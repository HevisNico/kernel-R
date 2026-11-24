"""The inverter gate measured INSIDE the layered network's deck: the network's own devices, at its own seed.

  python -m invinst.indeck OUTDIR --deck DECK.spice --seed S [--inverters n0,n1] [--config config.json]

DECK is the layered network's deck text, as the network runs it (stage D writes it: instrument.deck_text at the C5
overlay; flattened, tt_mm, no control block). For each inverter n<j>, the five runs of config.json are made in a copy of
that text in which only these lines change:
  - the inverter's five drive sources vkh/vki/vkj/vkr/vkb n<j> (the stand-alone deck's timing: slot at settle_s);
  - for a run without help, its help reference i.x<n>.ihref is set to 0 (as the stand-alone deck does);
  - for the static run (R5), an ideal source through 1 ohm onto x<n>.vq, added before .end.
Every other line, every other cell and inverter, stays as given (their drives stay at 'never'). The draw is
`setseed S` then `reset` in the control block, as sim.run does.

Identity: an op of the UNCHANGED deck at seed S gives the network's fingerprint of each inverter (sim.FINGER inside
x<n>). Every run's fingerprint must equal it within fingerprint_tol_V (the help diode excepted without help); if not,
same_sample is false and the gate's observation fails. The measured quantities are measure2's, restated in
`quantities` with the probe names prefixed; the gate is gate.gate, unchanged.

Writes OUTDIR/inverter_gate.json:
  {"kit_commit", "seed", "deck_sha256", "inverters": {"n0": {"K0", "K3", "measure_sha256", "why", "fingerprint",
   "same_sample", ...}}}
and OUTDIR/<n>/runs/<seed>/..., OUTDIR/<n>/gates/..., OUTDIR/SHA256SUMS. K0 and K3 follow campaign.first_failing
(an unmeasured StateBound fails); `why` lists the first failing clause of K0 and of K3 (empty when both hold).
"""
import argparse, hashlib, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import numpy as np

from . import sim
from .measure import _cols, integral, first_cross, comparator_flip, help_error, leak_fit, state_extent

PKG = Path(__file__).resolve().parents[1]
SCHEMA = "inverter-indeck/1"
NEVER = 1.0


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def names(inv):
    """The in-deck probe names of inverter `inv` (e.g. n0): fingerprint, then the saved vectors."""
    x = f"x{inv}"
    finger = [f"v({x}.ibm)"] + [n.replace("@m.", f"@m.{x}.") for n in sim.FINGER[1:]]
    saved = [f"v({x}.vq)", f"i(v.{x}.vah)", f"i(v.{x}.vaj)", f"v({x}.p)", f"v({x}.cmpm)"]
    return finger, saved


def swap_line(lines, start, new):
    k = [i for i, l in enumerate(lines) if l.startswith(start)]
    if len(k) != 1:
        raise ValueError(f"{start!r}: {len(k)} lines in the deck, expected 1")
    lines[k[0]] = new


def check_design(text, inv, c):
    """The deck's inverter is the configured cell: help and inhibit references, help mirror and level."""
    unit = c["cq_F"] * c["vunit_V"]
    m = re.search(rf"^i\.x{inv}\.ihref vdd x{inv}\.hg dc (\S+)$", text, re.M)
    j = re.search(rf"^b\.x{inv}\.bjref x{inv}\.jg 0 i = (\S+)\*v\(kj{inv}\)$", text, re.M)
    h = re.search(rf"^x{inv}\.xmh1 x{inv}\.hg x{inv}\.hg 0 0 sky130_fd_pr__nfet_01v8 w=(\S+) l=(\S+) ", text, re.M)
    lv = re.search(r"^\.param vfire=\{vr0 - (\S+)\*vunit\}", text, re.M)
    got = dict(H0=float(m.group(1)) * c["tu_s"] / unit, J0=float(j.group(1)) * c["tu_s"] / unit,
               help_w=float(h.group(1)), help_l=float(h.group(2)), level_x=float(lv.group(1)))
    want = dict(H0=c["H0"], J0=c["J0"], help_w=c["help_mirror"]["w"], help_l=c["help_mirror"]["l"], level_x=c["level_x"])
    bad = {k: (got[k], want[k]) for k in want if abs(got[k] - want[k]) > 1e-9 * max(1, abs(want[k]))}
    if bad:
        raise ValueError(f"{inv}: the deck's inverter differs from config.json: {bad}")


def run_deck(text, inv, c, r):
    """The deck of one run of inverter `inv`: the given text with only the listed lines changed."""
    tu, t0, e = c["tu_s"], c["settle_s"], c["edge_s"]
    s = lambda x: f"{t0 + x * tu:.12g}"
    w = lambda x: f"{x * tu - e:.12g}"
    lines = text.splitlines()
    swap_line(lines, f"vkh{inv} ", f"vkh{inv} kh{inv} 0 pulse(0 1.8 {s(c['h'])} {e} {e} {w(c['hl'])} 2)")
    swap_line(lines, f"vki{inv} ", f"vki{inv} ki{inv} 0 pulse(1.8 0 {s(0)} {e} {e} {w(c['tau'])} 2)")
    swap_line(lines, f"vkj{inv} ", f"vkj{inv} kj{inv} 0 pulse(0 1 {s(0) if r['present'] else NEVER} {e} {e} "
                                   f"{w(c['tau'])} 2)")
    at = s(c["D"]) if r["reset"] else NEVER
    swap_line(lines, f"vkr{inv} ", f"vkr{inv} kr{inv} 0 pulse(0 1.8 {at} {e} {e} {w(c['reset_len'])} 2)")
    swap_line(lines, f"vkb{inv} ", f"vkb{inv} kb{inv} 0 pulse(1.8 0 {at} {e} {e} {w(c['reset_len'])} 2)")
    if not r["help"]:
        swap_line(lines, f"i.x{inv}.ihref ", f"i.x{inv}.ihref vdd x{inv}.hg dc 0")
    if lines[-1] != ".end":
        raise ValueError("the deck does not end with .end")
    ramp = r.get("ramp")
    if ramp is not None:
        pwl = (f"0 {c['vr0_V']} {s(0)} {c['vr0_V']} {s(ramp['lead_tu'])} {ramp['v_hi']} "
               f"{s(ramp['lead_tu'] + ramp['ramp_tu'])} {ramp['v_lo']}")
        lines[-1:] = [f"vforce{inv} vfn{inv} 0 pwl({pwl})", f"rforce{inv} vfn{inv} x{inv}.vq 1", ".end"]
    return "\n".join(lines) + "\n"


def prepare(folder):
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    if not (folder / "pdk").exists():
        (folder / "pdk").symlink_to(sim.CIRCUIT / "pdk", target_is_directory=True)
    (folder / "blocks.spice").write_text((sim.CIRCUIT / "blocks.spice").read_text())
    (folder / ".spiceinit").write_text((sim.CIRCUIT / "spiceinit.txt").read_text())
    return folder


def ngspice(folder, deck, control, timeout):
    folder = prepare(folder)
    assert deck.endswith("\n.end\n")
    (folder / "input.spice").write_text(deck[: -len(".end\n")] + control + ".end\n")
    t0 = time.time()
    out = subprocess.run(["ngspice", "-b", "input.spice"], cwd=folder, capture_output=True, text=True, timeout=timeout)
    log = out.stdout + out.stderr
    (folder / "ngspice.log").write_text(log)
    finger = [l.split()[1:] for l in out.stdout.splitlines() if l.startswith("FINGER")]
    return out.returncode, log, [float(v) for v in finger[0]] if finger else None, time.time() - t0


def network_fingerprint(text, invs, seed, folder, timeout=3600):
    """The op-point fingerprint of each inverter in the UNCHANGED deck at `seed`."""
    probes = [p for inv in invs for p in names(inv)[0]]
    ctl = f".control\nsetseed {seed}\nreset\nop\necho FINGER {' '.join('$&' + p for p in probes)}\nquit\n.endc\n"
    rc, log, f, wall = ngspice(folder, text, ctl, timeout)
    if rc or f is None:
        raise RuntimeError("network op failed\n" + log[-3000:])
    k = len(sim.FINGER)
    return {inv: f[i * k:(i + 1) * k] for i, inv in enumerate(invs)}, wall


def run_one(folder, seed, deck, inv, tstop, maxstep, timeout=3600):
    finger, saved = names(inv)
    ctl = (f".control\nsetseed {seed}\nreset\nop\necho FINGER {' '.join('$&' + n for n in finger)}\n"
           f"set wr_singlescale\nset wr_vecnames\noption numdgt=12\ntran 1n {tstop:.12g} 0 {maxstep}\n"
           f"wrdata trace.txt {' '.join(saved)}\nquit\n.endc\n")
    rc, log, f, wall = ngspice(folder, deck, ctl, timeout)
    folder = Path(folder)
    if rc or not (folder / "trace.txt").exists() or "aborted" in log or "too small" in log:
        raise RuntimeError(f"{folder.name}: ngspice failed\n" + log[-3000:])
    data = np.loadtxt(folder / "trace.txt", skiprows=1)
    raw = dict(t=data[:, 0], vq=data[:, 1], ih=data[:, 2], ij=data[:, 3], p=data[:, 4], cmp=data[:, 5])
    rec = dict(files={n: sha(folder / n) for n in ("input.spice", "trace.txt", "ngspice.log")}, wall_s=wall,
               finger=f, points=int(len(data)))
    return raw, rec


def quantities(cfg, cols, root):
    """measure2.measure's quantities, restated from the runs' columns (the same code, line for line)."""
    c = cfg["cell"]
    r1, r2, r3, r4, r5 = (cols[n] for n in cfg["runs"])
    D, level = c["D"], c["level_x"]
    slot = lambda q: (q["u"] >= 0) & (q["u"] <= D)
    m = {}
    ramp = cfg["runs"]["R5_static"]["ramp"]
    t5 = comparator_flip(r5, ramp["lead_tu"] / 2)
    m["actual_level_x"] = float(np.interp(t5, r5["u"], r5["x"])) if t5 is not None else None
    m["delta"] = abs(m["actual_level_x"] - level) if t5 is not None else None
    m["static_ramp_slope"] = (ramp["v_hi"] - ramp["v_lo"]) / c["vunit_V"] / ramp["ramp_tu"]
    tc = first_cross(r1["u"], r1["x"], m["actual_level_x"], 0) if t5 is not None else None
    tf = comparator_flip(r1, 0)
    te = first_cross(r1["u"], r1["p"], 0.9, 0)
    m["contact_tu"] = tc
    m["emit_absent_tu"] = te
    m["comparator_delay_tu"] = tf - tc if (tf is not None and tc is not None) else None
    m["latch_delay_tu"] = te - tc if (te is not None and tc is not None) else None
    m["delta_dynamic"] = float(np.interp(tf, r1["u"], r1["x"])) - level if tf is not None else None
    m["x_max_absent"] = float(r1["x"][slot(r1)].max())
    m["etaJ"] = integral(r1, np.abs(r1["J"]), 0, c["h"] + c["hl"])
    m["etaJ_slot"] = integral(r1, np.abs(r1["J"]), 0, D)
    s2 = slot(r2)
    m["fired_present"] = bool((r2["p"][s2] > 0.9).any())
    m["x_max_present"] = float(r2["x"][s2].max())
    m["Q"] = integral(r2, np.maximum(r2["J"], 0), 0, c["tau"])
    m["etaM"] = integral(r2, np.maximum(-r2["J"], 0), 0, D)
    m["vq_max_present"] = float(r2["vq"][s2].max())
    m["etaH"] = max(help_error(r1, c), help_error(r2, c))
    m["help_negative_L1"] = max(integral(q, np.maximum(-q["H"], 0), 0, D) for q in (r1, r2))
    at = lambda q, x: float(np.interp(x, q["u"], q["x"]))
    m["x_slot_start"] = [at(r1, 0), at(r2, 0)]
    m["x_after_reset"] = [at(r1, D + c["reset_len"] + 0.05), at(r2, D + c["reset_len"] + 0.05)]
    m["eps0"] = max(abs(v) for v in m["x_slot_start"] + m["x_after_reset"])
    m["leak_above"] = leak_fit(r3, *cfg["runs"]["R3_leak_above"]["fit_tu"])
    m["leak_below"] = leak_fit(r4, *cfg["runs"]["R4_leak_below"]["fit_tu"])
    m["slot_duration_tu"] = D + c["reset_len"]
    m["state_extent"] = state_extent(cfg, root, (m["leak_above"]["rate"] + m["leak_below"]["rate"]) / 2)
    return m


def measure(cfg, text, inv, seed, net_finger, outdir, timeout=3600):
    t_start = time.time()
    c = cfg["cell"]
    root = Path(outdir) / str(seed)
    cols, recs = {}, {}
    for name, r in cfg["runs"].items():
        raw, recs[name] = run_one(root / name, seed, run_deck(text, inv, c, r), inv,
                                  c["settle_s"] + r["length_tu"] * c["tu_s"], r["maxstep"], timeout)
        cols[name] = _cols(c, raw)
    tol = cfg["fingerprint_tol_V"]
    same = all(rec["finger"] is not None for rec in recs.values()) and all(
        abs(a - b) <= tol for name, rec in recs.items() for j, (a, b) in enumerate(zip(rec["finger"], net_finger))
        if not (j == 3 and not cfg["runs"][name]["help"]))          # the help diode carries no current without help
    m = dict(same_sample=same, same_sample_reference="op of the unchanged network deck at this seed")
    m.update(quantities(cfg, cols, root))
    m["machine_s"] = {n: rec["wall_s"] for n, rec in recs.items()}
    m["machine_s_total"] = time.time() - t_start
    out = dict(seed=seed, inverter=inv, section="tt_mm (the deck's)", drawn=True, cell=c, measures=m,
               network_fingerprint=net_finger,
               runs={n: dict(files=rec["files"], finger=rec["finger"], points=rec["points"]) for n, rec in recs.items()})
    (root / "MEASURE.json").write_text(json.dumps(out, indent=1, sort_keys=True))
    return out


def one_job(args):
    """One inverter: measure in the deck, then gate (python -m invinst.indeck --job ...)."""
    from . import driver, gate
    cfg = driver.load_config(args.config)
    text = Path(args.deck).read_text()
    out = Path(args.outdir) / args.job
    nf = json.loads((Path(args.outdir) / "NETWORK_FINGERPRINT.json").read_text())["inverters"][args.job]
    meas = measure(cfg, text, args.job, args.seed, nf, out / "runs")
    gate.gate(cfg, meas, out / "gates", Path(args.outdir) / "lean_build")


def entry(out, inv, seed, status):
    from . import campaign
    gp = out / inv / "gates" / f"GATE_{seed}.json"
    mp = out / inv / "runs" / str(seed) / "MEASURE.json"
    g = json.loads(gp.read_text()) if (status == "ok" and gp.exists()) else None
    f0, f3 = campaign.first_failing(status, g, "K0"), campaign.first_failing(status, g, "K3")
    e = dict(K0=f0 is None, K3=f0 is None and f3 is None, why=[w for w in dict.fromkeys([f0, f3]) if w],
             first_failing_K0=f0, first_failing_K3=f3, status=status,
             measure_sha256=sha(mp) if mp.exists() else None)
    if g is not None:
        m = json.loads(mp.read_text())
        att = [a for a in g["attempts"] if a["passed"]]
        lean = out / inv / "gates" / att[0]["file"] if att else None
        e.update(same_sample=m["measures"]["same_sample"],
                 fingerprint=dict(names=names(inv)[0], network=m["network_fingerprint"],
                                  runs={n: r["finger"] for n, r in m["runs"].items()}),
                 gate_eligible_K0=g["eligible_K0"], gate_room_K3=g["room_K3"], kernel=g["kernel"],
                 margins=g["margins"], measures=g["measures"], state_bound=g["state_bound"],
                 files=dict(gate=str(gp.relative_to(out)), measure=str(mp.relative_to(out)),
                            lean=str(lean.relative_to(out)) if lean else None),
                 gate_sha256=sha(gp), lean_sha256=sha(lean) if lean else None,
                 machine_s=m["measures"]["machine_s_total"])
        assert not (e["K0"] and not g["eligible_K0"]) and not (e["K3"] and not g["room_K3"])
    return e


def run(deck, outdir, seed, invs=None, config=None):
    from . import campaign, driver
    out = Path(outdir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    deck = Path(deck).resolve()
    text = deck.read_text()
    cfg = driver.load_config(config)
    invs = invs or sorted(set(re.findall(r"^x(n\d+)\.xcmpm\.xm1 ", text, re.M)), key=lambda n: int(n[1:]))
    if not invs:
        raise ValueError("no inverter n<j> in the deck")
    for inv in invs:
        check_design(text, inv, cfg["cell"])
        names(inv)
    t0 = time.time()
    nf, op_s = network_fingerprint(text, invs, seed, out / "network_op")
    (out / "NETWORK_FINGERPRINT.json").write_text(json.dumps(dict(seed=seed, names={i: names(i)[0] for i in invs},
                                                                  inverters=nf), indent=1, sort_keys=True))
    driver.build_library(out / "lean_build")
    head = subprocess.run(["git", "-C", str(PKG), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "-C", str(PKG), "status", "--porcelain", "--", "."], capture_output=True,
                           text=True).stdout.strip()
    dcfg = cfg["driver"]

    def job(inv):
        cmd = [sys.executable, "-m", "invinst.indeck", str(out), "--deck", str(deck), "--seed", str(seed), "--job", inv]
        cmd += ["--config", str(Path(config).resolve())] if config else []
        s = time.time()
        try:
            p = subprocess.run(cmd, cwd=PKG, capture_output=True, text=True, timeout=dcfg["job_timeout_s"])
            status, log = ("ok" if p.returncode == 0 else "failed"), p.stdout + p.stderr
        except subprocess.TimeoutExpired as e:
            status, log = "timeout", str(e)
        (out / "status").mkdir(exist_ok=True)
        (out / "status" / f"{inv}.{status}").write_text(log[-5000:])
        return inv, status, time.time() - s

    with ThreadPoolExecutor(max_workers=dcfg["max_jobs"]) as ex:
        res = list(ex.map(job, invs))
    doc = dict(schema=SCHEMA, kit_commit=head, package_tree_clean=not dirty, seed=seed, deck=str(deck),
               deck_sha256=sha(deck), config_sha256=sha(Path(config or PKG / "config.json")),
               verdict_status="conditional on open_premises", open_premises=__import__("invinst.gate").gate.OPEN_PREMISES,
               rule="instance eligible at K0 iff every inverter's K0 holds; room at K3 iff every K3 holds",
               inverters={inv: entry(out, inv, seed, st) for inv, st, _ in res},
               job_wall_s={inv: w for inv, _, w in res}, network_op_s=op_s, wall_minutes=(time.time() - t0) / 60)
    doc["K0"] = all(e["K0"] for e in doc["inverters"].values())
    doc["K3"] = all(e["K3"] for e in doc["inverters"].values())
    (out / "inverter_gate.json").write_text(json.dumps(doc, indent=1, sort_keys=True))
    campaign.write_sums(out)
    return out / "inverter_gate.json"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    ap.add_argument("--deck", required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--inverters", help="comma-separated, default: every n<j> of the deck")
    ap.add_argument("--config")
    ap.add_argument("--job", help=argparse.SUPPRESS)
    a = ap.parse_args()
    if a.job:
        one_job(a)
        return
    p = run(a.deck, a.outdir, a.seed, a.inverters.split(",") if a.inverters else None, a.config)
    doc = json.loads(p.read_text())
    print(json.dumps(dict(seed=doc["seed"], K0=doc["K0"], K3=doc["K3"],
                          inverters={k: dict(K0=v["K0"], K3=v["K3"], why=v["why"], same_sample=v.get("same_sample"))
                                     for k, v in doc["inverters"].items()}, wall_minutes=doc["wall_minutes"]), indent=1))


if __name__ == "__main__":
    main()
