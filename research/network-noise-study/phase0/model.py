"""Phase 0, feasibility, no claim: the per-instance generator of a noise model drawn from the device models.

  model.py extract WORK OUT.json SECTION SEED|none CELLS NGSPICE PDK [STATE ...] [--per-cell]

With --per-cell (the method fixed for every instance), each cell is extracted in the deck of the instance with the
other cells taken out of the circuit but their mismatch draws kept (`isolate`), after a check that each cell's
operating point is the one of the full deck (`op_match`).

CELLS is a comma-separated list of cell names, the cells of the deck of the instance (for example a,b): the mismatch
sample of a seed belongs to the whole deck, so the extraction runs on that deck, with its seed (`setseed`, `reset`),
never on a cell taken alone. Every cell is frozen in the same state; each port or cell in turn is the output.

States (default: all five) and the output of each:
  hold    the stored voltage v(x<c>.vmem<p>), preset ended, no pulse (as in pilot.py)
  preset  the voltage across the integrating capacitor, v(x<c>.vmem<p>) - v(x<c>.x<p>.sum), preset switch closed:
          what the end of the preset freezes. The out-of-band part is reported, not modelled
  window  the first stage of the window comparator of the port, v(x<c>.x<p>.xcmps.o1), with the sensor node held by
          an ideal source, set by a DC sweep to where that comparator trips (the precharge cannot do it: below about
          0.65 V the discharge holds the sensor node at 0.4 V). The sensor's own noise is shorted here; it is not
          part of a decision point, and its sampled part is item V6
  fire    the first stage of the FIRE comparator of the cell, v(x<c>.xcmpm.o1), with the main charge held by an
          ideal source where the comparator trips (DC sweep)
  pulse   the main charge v(x<c>.vq), the port admitted and its mirror at the peak current of a pulse (173 nA), the
          charge held near 1.03 V through a noiseless 1 Mohm so that the cell does not protect itself

What every analysis deck changes, against the network deck: the bench resistors are noiseless; `vcm` gets `ac 1`, the
input that the noise command requires; and every internal node of a NAND stack gets a noiseless 1e-12 S to ground.
Phase 0 found that with both transistors of a stack off, such a node is held only by leakage, and the small-signal
matrix is then near singular below about 30 Hz (FEASIBILITY.md, section 3). In `hold`, `window`, `fire` and `pulse`
the preset switches are noiseless 1e14 ohm resistors.

For each state and output it keeps the devices that make 99 % of the output noise power over 10 Hz to 1.25 MHz and
writes their white density A and flicker coefficient B (S = A + B / f^ef), as in pilot.py.
"""
import json, re, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import pilot                                   # noqa: E402
from pilot import net, raw_ascii, seeded, vec, ALPHA, BENCH, BAND, COVER   # noqa: E402

STATES = ("hold", "preset", "window", "fire", "pulse")
# On some mismatch samples (7101, 7103) the operating point that the noise and AC analyses solve for themselves
# fails (gmin and source stepping) where `op` succeeds, and the analysis hangs; a .nodeset from `op` does not help.
# Tried and rejected: a shunt of 1e-13 S from every node (ngspice `rshunt`) lets the analysis finish, but the
# operating point it prints for 7101 is NaN and it changes the device transfers of the nominal cell. Not used.
RSHUNT = None
NODESET = True            # pass 2 of the per-cell method; the full-deck reference of V2c runs without it
TIMEOUT = None            # seconds per simulator call; the full-deck reference of V2c uses 1200


def spice(work, text, ngspice, pdk):
    """pilot.spice with the time limit TIMEOUT: a call that does not finish leaves no result (and a TIMEOUT file)."""
    import subprocess as sp
    try:
        return _spice(work, text, ngspice, pdk)
    except sp.TimeoutExpired:
        (work / "TIMEOUT").write_text(f"{TIMEOUT} s\n")
        return ""


def _spice(work, text, ngspice, pdk):
    import os, shutil, subprocess as sp
    work.mkdir(parents=True, exist_ok=False)
    (work / "pdk").symlink_to(Path(pdk).resolve(), target_is_directory=True)
    shutil.copyfile(pilot.CIRCUIT / "spiceinit.txt", work / ".spiceinit")
    (work / "deck.spice").write_text(text)
    env = dict(os.environ, SPICE_SCRIPTS=str(pilot.sim.SPINIT.parent))
    p = sp.run([ngspice, "-b", "deck.spice"], cwd=work, env=env, capture_output=True, text=True, timeout=TIMEOUT)
    (work / "log.txt").write_text(p.stdout + p.stderr)
    return p.stdout
STACK = re.compile(r"\.n[12]$")


def analysis_deck(section, cells, state, focus=None):
    """The frozen deck. `focus` is (cell, port) for `pulse`: the port that is admitted."""
    t = net.deck(cells=cells, section=section)
    if state != "preset":
        for c in cells:
            for p in net.PORTS:
                t = net.swap(t, f"s.x{c}.x{p}.srst x{c}.x{p}.sum x{c}.x{p}.drv x{c}.x{p}.rsti 0 swr",
                             f"r.hold{c}{p} x{c}.x{p}.sum x{c}.x{p}.drv 1e14 noisy=0")
    t = net.swap(t, "\nvcm vcm 0 {vcm}\n", "\nvcm vcm 0 {vcm} ac 1\n")
    # The protection latch of a cell is bistable at DC, and each analysis (op, noise, ac) solves its own operating
    # point: phase 0 saw `op` find the cell free and `noise` find it protected, in the same deck. Every frozen state
    # is a state of a free cell, so the latch is held there by ideal sources (noiseless).
    t = t.replace("\n.end\n", "\n" + "\n".join(f"vfp{c} x{c}.p 0 dc 0\nvfpb{c} x{c}.pb 0 dc 1.8" for c in cells) + "\n.end\n")
    if state == "window":                      # the sensor node is held where the comparator trips (see balance)
        c, p = focus
        t = t.replace("\n.end\n", f"\nvfrc x{c}.x{p}.vs 0 dc 0.6\n.end\n")
    if state == "fire":                        # the main charge is held where the FIRE comparator trips (see balance)
        c, _ = focus
        t = t.replace("\n.end\n", f"\nvfrcq x{c}.vq 0 dc 0.8\n.end\n")
    if state == "pulse":
        c, p = focus
        # at DC the mirror would pull the main charge below the FIRE level and the cell would protect itself:
        # the charge is held near 1.03 V through a noiseless 1 Mohm, so the admitted current flows and its noise
        # reaches v(vq)
        t = t.replace("\n.end\n", f"\nvhq hq{c} 0 dc 1.2\nr.hq{c} x{c}.vq hq{c} 1e6 noisy=0\n.end\n")
        t = net.swap(t, f"vks{c}{p} ks{c}{p} 0 pulse(0 1 {net.NEVER} 1n 1n {net.TU - 1e-9:.12g} 2)", f"vks{c}{p} ks{c}{p} 0 dc 1")
        t = net.swap(t, f"vts{c}{p} ts{c}{p} 0 dc {net.NEVER}", f"vts{c}{p} ts{c}{p} 0 dc 0")
    out, nodes = [], set()
    for line in t.splitlines():
        f = line.split()
        name = f[0] if f else ""
        if name.startswith("r.") and name.rsplit(".", 1)[-1] in BENCH:
            line += " noisy=0"
        if f and "sky130_fd_pr__" in line:
            nodes.update(n for n in f[1:5] if STACK.search(n))
        out.append(line)
    cond = [f"r.cond{k} {n} 0 1e12 noisy=0" for k, n in enumerate(sorted(nodes))]
    text = "\n".join(out) + "\n"
    return text.replace("\n.end\n", "\n" + "\n".join(cond + ([RSHUNT] if RSHUNT else [])) + "\n.end\n"), len(cond)


FOUR_TERMINAL = ("sky130_fd_pr__nfet_01v8", "sky130_fd_pr__pfet_01v8", "sky130_fd_pr__pfet_01v8_lvt")


def isolate(text, keep, cells):
    """The deck of the instance with every cell but `keep` taken out of the circuit, its mismatch draws kept: each
    transistor of another cell stays, in its place, with its four terminals on ground (so the PDK draws the same
    AGAUSS values in the same order, and `keep` gets exactly the mismatch it has in the full deck), and every other
    element of another cell is removed. Device noise is local, and the cells are joined only by the router outside
    the simulator and by ideal supplies."""
    others = [f"x{c}." for c in cells if c != keep]
    out = []
    for line in text.splitlines():
        f = line.split()
        if not f or not others:
            out.append(line)
            continue
        if any(f[0].startswith(o) for o in others) and "sky130_fd_pr__" in line:
            # only the three four-terminal transistors of the cell may be grounded this way: any other PDK device
            # (a resistor, a capacitor, a diode) has another number of terminals and would be corrupted
            assert f[5] in FOUR_TERMINAL, f"isolate: device type {f[5]} of {f[0]} is not a four-terminal transistor"
            out.append(" ".join([f[0], "0", "0", "0", "0"] + f[5:]))
        elif any(o in tok for tok in f[:6] for o in others) or any(f[0] in (f"vfp{c}", f"vfpb{c}") for c in cells if c != keep):
            continue
        else:
            out.append(line)
    return "\n".join(out) + "\n"


def op_match(work, section, seed, cells, ngspice, pdk, state="hold"):
    """The operating point of each cell in its isolated deck against the full deck: the largest difference over the
    nodes of the cell. The full deck's `op` converges where its noise analysis does not."""
    full, _ = analysis_deck(section, cells, state, focus=(cells[0], 1))
    ctl = lambda: "\n".join([".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + ["op", "write op.raw all", "quit", ".endc", ".end"]) + "\n"
    spice(work / "full", full.replace("\n.end\n", "\n") + ctl(), ngspice, pdk)
    ref = raw_ascii(work / "full" / "op.raw")
    res = {}
    for c in cells:
        spice(work / f"cell_{c}", isolate(full, c, cells).replace("\n.end\n", "\n") + ctl(), ngspice, pdk)
        r = raw_ascii(work / f"cell_{c}" / "op.raw")
        keys = [k for k in ref if k.startswith(f"v(x{c}.") and k in r and "#" not in k]
        d = max(abs(float(ref[k][0]) - float(r[k][0])) for k in keys)
        worst = max(keys, key=lambda k: abs(float(ref[k][0]) - float(r[k][0])))
        res[c] = dict(nodes=len(keys), max_abs_diff_V=d, worst_node=worst)
    return res


def devices(text):
    out = {}
    for line in text.splitlines():
        f = line.split()
        if not f:
            continue
        m = re.search(r"sky130_fd_pr__(\w+)", line)
        if m and f[0].startswith("x"):
            out[f[0]] = (f[1], f[3], m.group(1))
        elif f[0].startswith("r.") and "noisy=0" not in line:
            out[f[0][2:]] = (f[1], f[2], "res")
    return out


def outputs(state, cells):
    if state == "pulse":                       # one port per cell is admitted at a time; port 1 and port 2 in turn
        return [(c, p) for c in cells for p in net.PORTS]
    if state in ("hold", "preset", "window", "pulse"):
        return [(c, p) for c in cells for p in net.PORTS]
    return [(c, None) for c in cells]


def out_expr(state, c, p):
    return {"hold": f"v(x{c}.vmem{p})", "preset": f"v(x{c}.vmem{p},x{c}.x{p}.sum)", "window": f"v(x{c}.x{p}.xcmps.o1)",
            "fire": f"v(x{c}.xcmpm.o1)", "pulse": f"v(x{c}.vq)"}[state]


def balance(state, c, p):
    """Control lines that set the shared source where the comparator of (c, p) trips, before the noise analysis."""
    if state == "window":
        src, lo, hi, node = "vfrc", 0.54, 0.66, f"x{c}.x{p}.xcmps.o2"
    elif state == "fire":
        src, lo, hi, node = "vfrcq", 0.74, 0.86, f"x{c}.xcmpm.o2"
    else:
        return []
    return [f"dc {src} {lo} {hi} 0.0005", f"meas dc vtrip when v({node})=0.9", f"echo TRIP $&vtrip",
            f"alter {src} dc = $&vtrip"]


def one_output(work, text, devs, seed, state, c, p, ngspice, pdk):
    out = out_expr(state, c, p)
    # Pass 1: the operating point (after the trip sweep, if any), written out. Each later analysis solves its own
    # operating point from scratch, and on some mismatch samples that solve fails (gmin and source stepping) where
    # `op` succeeds: pass 2 gives it the solution of pass 1 as .nodeset.
    body = text.replace("\n.end\n", "\n")
    first = [".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + balance(state, c, p) + [
        "op", "write op.raw all", "quit", ".endc", ".end"]
    stdout = spice(work / "op", body + "\n".join(first) + "\n", ngspice, pdk)
    trip = next((float(l.split()[1]) for l in stdout.splitlines() if l.startswith("TRIP ")), None)
    if not (work / "op" / "op.raw").exists():
        return dict(state=state, cell=c, port=p, output=out, error="no operating point", trip=trip)
    op = raw_ascii(work / "op" / "op.raw")
    nodeset = [f".nodeset v({k[2:-1]})={float(v[0]):.15g}" for k, v in op.items()
               if k.startswith("v(") and "#" not in k and "," not in k]
    fixed = []
    if trip is not None:                       # the swept source stays where the comparator trips
        src = {"window": "vfrc", "fire": "vfrcq"}[state]
        fixed = [f"alter {src} dc = {trip:.15g}"]
    body = body + ("\n".join(nodeset) + "\n" if NODESET else "")
    pre = [".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + fixed + ["op"]
    spice(work / "noise", body + "\n".join(pre + [f"noise {out} vcm dec 20 1 1e8 1", "setplot noise1",
                                                "write noise.raw all", "quit", ".endc", ".end"]) + "\n", ngspice, pdk)
    if not (work / "noise" / "noise.raw").exists():
        return dict(state=state, cell=c, port=p, output=out, error="no noise result", trip=trip)
    r = raw_ascii(work / "noise" / "noise.raw")
    if "onoise_spectrum" not in r:
        return dict(state=state, cell=c, port=p, output=out, error="no noise plot", trip=trip)
    f = r["frequency"]
    band = (f >= BAND[0]) & (f <= BAND[1])
    integ = lambda s: float(np.trapezoid(s[band], f[band]))
    total = r["onoise_spectrum"] ** 2
    p_total = integ(total)
    share = {d: integ(r[vec(d, k)] ** 2) / p_total for d, (_, _, k) in devs.items() if vec(d, k) in r}
    keep, acc = [], 0.0
    for d in sorted(share, key=share.get, reverse=True):
        if acc >= COVER:
            break
        keep.append(d); acc += share[d]
    inj = [f"iinj{k} {devs[d][0]} {devs[d][1]} dc 0 ac 0" for k, d in enumerate(keep)]
    ctl = list(pre)
    for k in range(len(keep)):
        ctl += [f"alter @iinj{k}[acmag]=1", "ac dec 20 1 1e8", f"let h{k} = mag({out})", f"write h{k}.raw h{k}",
                f"alter @iinj{k}[acmag]=0"]
    spice(work / "ac", body + "\n".join(inj + ctl + ["quit", ".endc", ".end"]) + "\n", ngspice, pdk)
    kept = []
    for k, d in enumerate(keep):
        h = list(raw_ascii(work / "ac" / f"h{k}.raw").values())[1]
        a, b, kind = devs[d]
        key = vec(d, kind)
        if kind == "res":
            th, fl, alpha = r[key + "_thermal"] ** 2 / h ** 2, np.zeros_like(h), 1.0
        else:
            th, fl, alpha = r[key + ".id"] ** 2 / h ** 2, r[key + ".1overf"] ** 2 / h ** 2, ALPHA[kind]
        sel = band & (h > 1e-2 * h[band].max())
        A, B = float(np.median(th[sel])), float(np.median(fl[sel] * f[sel] ** alpha))
        spread = lambda y: float(np.percentile(y, 95) / max(np.percentile(y, 5), 1e-300))
        kept.append(dict(device=d, kind=kind, nodes=[a, b], share=share[d], alpha=alpha, white_A2_Hz=A, flicker_B=B,
                         spread_white=spread(th[sel]), spread_flicker=spread(fl[sel] * f[sel] ** alpha) if B > 0 else None))
    parts = {}
    for lo, hi in ((1, BAND[0]), BAND, (BAND[1], 1e8)):
        m = (f >= lo) & (f <= hi)
        parts[f"{lo:g}-{hi:g}"] = float(np.sqrt(np.trapezoid(total[m], f[m])))
    return dict(state=state, cell=c, port=p, output=out, trip=trip, rms_V=parts, covered=acc, kept=kept,
                top_share=max(share.values()) if share else None,
                onoise=dict(f=f[::4].tolist(), total=total[::4].tolist()))


def extract(work, out, section, seed, cells, ngspice, pdk, states, per_cell=False):
    res = dict(section=section, seed=seed, cells=cells, per_cell=per_cell, band_Hz=BAND, cover=COVER, outputs=[])
    if per_cell:
        res["op_match"] = op_match(work / "opmatch", section, seed, cells, ngspice, pdk)
        print("op match", res["op_match"], flush=True)
    for state in states:
        for c, p in outputs(state, cells):
            text, ncond = analysis_deck(section, cells, state, focus=(c, p))
            if per_cell:
                text = isolate(text, c, cells)
            devs = devices(text)
            r = one_output(work / f"{state}_{c}{p or ''}", text, devs, seed, state, c, p, ngspice, pdk)
            r["conditioned_nodes"] = ncond
            res["outputs"].append(r)
            ks = r.get("kept", [])
            print(state, c, p, r.get("error", ""), "trip", r.get("trip"), "rms", {k: round(v * 1e6, 1) for k, v in r.get("rms_V", {}).items()},
                  "kept", len(ks), [(x["device"], round(x["share"], 3), round(x["spread_white"], 3)) for x in ks[:4]], flush=True)
            Path(out).write_text(json.dumps(res, indent=1) + "\n")


if __name__ == "__main__":
    a = sys.argv[2:]
    if sys.argv[1] == "extract":
        per_cell = "--per-cell" in a
        if "--reference" in a:                 # the full-deck reference of V2c: no .nodeset, 1200 s per call
            NODESET, TIMEOUT = False, 1200
        a = [x for x in a if x not in ("--per-cell", "--reference")]
        extract(Path(a[0]), Path(a[1]), a[2], None if a[3] == "none" else int(a[3]), tuple(a[4].split(",")), a[5], a[6],
                a[7:] or list(STATES), per_cell)
