"""Analysis of the repetition campaign, by the rules of PREDICTION.md. No simulation is run.

  rep_analyze.py accel            solver and output options      -> ACCEL.md, campaign.json (klu, binary)
  rep_analyze.py step             step refinement                -> STEP.md, step.csv, campaign.json (tmax)
  rep_analyze.py preflight        truncation and noise replay    -> PREFLIGHT.md
  rep_analyze.py report [BASE]    run once, after the last slice -> trials.csv, ports.csv, REPORT.md

The gains of a read are computed by the functions of ../certification/cert_analyze.py, the comparison
with the current of the mirror by those of ../certification-unconditional/. BASE is the folder that
holds results/ and receives the files; it is this folder unless a dry run on synthetic data names another.
"""
import csv
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "certification-unconditional"))
import uncond_analyze as U
import uncond_amend1 as M

A, CERT = U.A, U.CERT
MANIFEST = json.loads((HERE / "manifest.json").read_text())
FROZEN = json.loads((HERE / "frozen.json").read_text())
KAPPA, D0, EPSK, MZ, MQ, MG = (FROZEN[k] for k in ("kappa", "d0", "eps_kappa", "MZ", "MQ", "MG"))
DATE_TOL = 0.001                     # resolution of a latch date in the step rule, in units
fm, DASH = A.fm, A.DASH


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(folder, name):
    """Rows, charges and metadata of a run, or None and the reason."""
    if (folder / f"{name}.failed").exists():
        return None, None, None, "run failed: " + (folder / f"{name}.failed").read_text().splitlines()[0]
    if not (folder / f"{name}.json").exists():
        return None, None, None, "run missing"
    meta = json.loads((folder / f"{name}.json").read_text())
    with (folder / f"{name}.csv").open(newline="") as fh:
        rows = [{k: float(v) for k, v in r.items()} for r in csv.DictReader(fh)]
    with (folder / f"{name}.charge.csv").open(newline="") as fh:
        charge = [{k: float(v) for k, v in r.items()} for r in csv.DictReader(fh)]
    if digest(folder / f"{name}.csv") != meta["csv_sha256"] or digest(folder / f"{name}.charge.csv") != meta["charge_sha256"]:
        return None, None, meta, "a file does not have the SHA-256 of its metadata"
    if len(rows) != meta["run"]["periods"] - 1 or len(charge) != len(rows) or any(int(c["pulse"]) != int(r["pulse"]) or int(c["port"]) != int(r["port"]) for c, r in zip(charge, rows)):
        return None, None, meta, "rows do not match the plan"
    if not all(math.isfinite(v) for r in rows + charge for v in r.values()):
        return None, None, meta, "a value is not finite"
    return rows, charge, meta, None


def eps3_stat(rows, charge, port, offsets=None):
    """eps3 of amendment 1 of the certification-unconditional campaign for the reads of a port given here.
    With offsets (D, DE) the two constants are those given; without, they are the means over the silent reads."""
    reads = [(r, math.log(c[f"w{port}"]), math.log(c[f"e{port}"])) for r, c in zip(rows, charge) if int(r["port"]) == port]
    silent = [(A.gain_silent(r), A.gain_early(r), gi, ge) for r, gi, ge in reads if r["fired"] != 1]
    if any(g is None or y is None for g, y, _, _ in silent):
        return None, "a silent read has no gain"
    if offsets is None:
        if not silent:
            return None, "no silent read"
        d, de = statistics.mean(g - gi for g, _, gi, _ in silent), statistics.mean(y - ge for _, y, _, ge in silent)
    else:
        d, de = offsets
    dev = [abs(g - gi - d) for g, _, gi, _ in silent] + [abs(y - ge - de) for _, y, _, ge in silent]
    left = 0
    for r, _, ge in reads:
        if r["fired"] == 1:
            if r["fire_latency"] < A.EARLY or A.gain_early(r) is None:
                left += 1
            else:
                dev.append(abs(A.gain_early(r) - ge - de))
    if not dev:
        return None, "no read with a gain"
    return dict(D=d, DE=de, eps3=max(dev) + MG, left_out=left), None


def save_campaign(**fields):
    path = HERE / "campaign.json"
    data = json.loads(path.read_text()) if path.exists() else {}
    data.update(fields)
    path.write_text(json.dumps(data, indent=1) + "\n")


# ---- solver and output options
def accel():
    folder = HERE / "results" / "accel"
    runs = {r["name"]: load(folder, r["name"]) for r in MANIFEST["stages"]["accel"]}
    reference = json.loads((CERT / "results" / "preflight" / "nom_train.json").read_text())["csv_sha256"]
    base = runs["a_base"][2]
    L = ["# Solver and output options", "", "Written by `rep_analyze.py accel`. Four runs of the nominal training without noise, at 200 ns, run at the same time on one machine.", "",
         "| Run | KLU | Binary output | Rows (SHA-256) | Charges (SHA-256) | Same as the base | Simulator, s | Reading, s | Total, s |", "|---|---|---|---|---|---|---|---|---|"]
    total, same = {}, {}
    for name, (rows, charge, meta, why) in runs.items():
        if rows is None:
            L.append(f"| `{name}` | | | {why} | | no | | | |")
            same[name] = False
            continue
        same[name] = base is not None and meta["csv_sha256"] == base["csv_sha256"] and meta["charge_sha256"] == base["charge_sha256"]
        total[name] = meta["simulator_seconds"] + meta["read_seconds"]
        L.append(f"| `{name}` | {'yes' if meta['options']['klu'] else 'no'} | {'yes' if meta['options']['binary'] else 'no'} | `{meta['csv_sha256'][:16]}` | `{meta['charge_sha256'][:16]}` | "
                 f"{'yes' if same[name] else '**no**'} | {meta['simulator_seconds']:.0f} | {meta['read_seconds']:.0f} | {total[name]:.0f} |")
    base_ok = base is not None and base["csv_sha256"] == reference
    binary = base_ok and same["a_bin"] and total["a_bin"] < total["a_base"]
    klu = base_ok and same["a_klu"] and total["a_klu"] < total["a_base"]
    if binary and klu and not (same["a_klu_bin"] and total["a_klu_bin"] < min(total["a_bin"], total["a_klu"])):
        klu = False                                  # the two together must also give the same rows and be the fastest
    L += ["", f"Rows of the base run against the nominal training of the certification campaign (`{reference[:16]}`): " + ("the same, byte for byte." if base_ok else "**different**; no option is adopted."),
          "", f"Rule of `PREDICTION.md`: an option is adopted only if its rows and charges are those of the base run byte for byte and its total time is lower. **Binary output: {'adopted' if binary else 'not adopted'}. KLU: {'adopted' if klu else 'not adopted'}.**"]
    (HERE / "ACCEL.md").write_text("\n".join(L) + "\n")
    save_campaign(klu=bool(klu), binary=bool(binary))
    print("\n".join(L))
    return 0 if base_ok else 1


# ---- step refinement
STEPS = ("400n", "200n", "100n", "50n")
PAIRS = (("400n", "200n"), ("200n", "100n"), ("100n", "50n"), ("200n", "50n"))


def step():
    folder = HERE / "results" / "step"
    cases = sorted({r["name"].rsplit("_", 1)[0] for r in MANIFEST["stages"]["step"]})
    out, problems, replay = [], [], []
    for case in cases:
        data = {s: load(folder, f"{case}_{s}") for s in STEPS}
        for s in STEPS:
            if data[s][0] is None:
                problems.append(f"`{case}_{s}`: {data[s][3]}")
        # the 200 ns run against the same run of the earlier campaigns
        seed, mode = case.split("_")[1], case.split("_")[2]
        ref = (CERT / "results" / "preflight" / f"nom_{mode}.json") if seed == "nom" else (CERT / "results" / "calibration" / f"{seed}_{mode}.json")
        if data["200n"][2] is not None:
            replay.append((case, data["200n"][2]["csv_sha256"] == json.loads(ref.read_text())["csv_sha256"]))
        ports = (1,) if mode == "leak" else (1, 2)
        stat = {}
        for s in STEPS:
            rows, charge, meta, _ = data[s]
            if rows is None:
                continue
            for port in ports:
                own, why = eps3_stat(rows, charge, port)
                stat[(s, port)] = own
                if own is None:
                    problems.append(f"`{case}_{s}` port {port}: {why}")
        for a, b in PAIRS:
            if data[a][0] is None or data[b][0] is None:
                continue
            ra, rb = data[a][0], data[b][0]
            for port in ports:
                pa, pb = [r for r in ra if int(r["port"]) == port], [r for r in rb if int(r["port"]) == port]
                row = dict(case=case, port=port, coarse=a, fine=b, reads=len(pa))
                out.append(row)
                row["same_fire"] = len(pa) == len(pb) and all(x["fired"] == y["fired"] for x, y in zip(pa, pb))
                row["same_guards"] = len(pa) == len(pb) and all(x[k] == y[k] for x, y in zip(pa, pb) for k in ("latch_rises", "steer_rises1", "steer_rises2"))
                row["same_count"] = A.count_of(pa) == A.count_of(pb)
                if not row["same_fire"]:
                    continue
                za, zb = [A.gain(r, KAPPA) for r in pa], [A.gain(r, KAPPA) for r in pb]
                if None in za or None in zb:
                    row["gain_evaluable"] = False
                else:
                    row["d_gain"] = max(abs(x - y) for x, y in zip(za, zb))
                row["d_date"] = max([abs(x["fire_latency"] - y["fire_latency"]) for x, y in zip(pa, pb) if x["fired"] == 1], default=0.0)
                sa, sb = stat.get((a, port)), stat.get((b, port))
                if sa and sb:
                    row.update(eps3_coarse=sa["eps3"], eps3_fine=sb["eps3"], d_eps3=abs(sa["eps3"] - sb["eps3"]), d_D=abs(sa["D"] - sb["D"]), d_DE=abs(sa["DE"] - sb["DE"]))
                    ref200 = stat.get(("200n", port))
                    if ref200:                       # the two constants frozen at their 200 ns values
                        fa, _ = eps3_stat(data[a][0], data[a][1], port, (ref200["D"], ref200["DE"]))
                        fb, _ = eps3_stat(data[b][0], data[b][1], port, (ref200["D"], ref200["DE"]))
                        if fa and fb:
                            row["d_eps3_frozen"] = abs(fa["eps3"] - fb["eps3"])
    fields = ["case", "port", "coarse", "fine", "reads", "same_fire", "same_count", "same_guards", "d_gain", "d_date", "eps3_coarse", "eps3_fine", "d_eps3", "d_eps3_frozen", "d_D", "d_DE"]
    with (HERE / "step.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n", extrasaction="ignore")
        w.writeheader()
        for r in out:
            w.writerow({k: ("" if r.get(k) is None else (format(r[k], ".12g") if isinstance(r[k], float) else r[k])) for k in fields})

    def ok(r, with_date):
        return (r["same_fire"] and r["same_count"] and r["same_guards"] and r.get("d_gain") is not None and r["d_gain"] <= MZ
                and r.get("d_eps3") is not None and r["d_eps3"] <= MG and r.get("d_eps3_frozen") is not None and r["d_eps3_frozen"] <= MG
                and (not with_date or r["d_date"] <= DATE_TOL))
    planned = len(cases) * 3 // 2                    # comparisons per pair of steps: 2 ports for a training, 1 for a leak scan
    complete = not problems and all(sum(1 for r in out if (r["coarse"], r["fine"]) == p) == planned for p in PAIRS)
    first = [r for r in out if (r["coarse"], r["fine"]) == ("400n", "200n")]
    adopt = complete and all(ok(r, True) for r in first)
    finer = [r for r in out if (r["coarse"], r["fine"]) != ("400n", "200n")]
    mg_holds = complete and all(r.get("d_eps3") is not None and r["d_eps3"] <= MG and r.get("d_eps3_frozen") is not None and r["d_eps3_frozen"] <= MG and r["same_fire"] for r in finer)
    big = lambda rows, k: max([r[k] for r in rows if r.get(k) is not None], default=None)
    L = ["# Step refinement", "", "Written by `rep_analyze.py step` under [`PREDICTION.md`](PREDICTION.md). One row per comparison: [`step.csv`](step.csv). "
         "Six cases without noise (nominal cell, calibration cells 5001 and 5002; training and leak scan), each at 400, 200, 100 and 50 ns.", "",
         "| Steps compared | Comparisons | Same FIRE of every read | Same counts | Same latch and steering counts | Largest change of a gain | Largest change of a latch date, units | Largest change of `eps3` | The same, constants frozen at 200 ns |", "|---|---|---|---|---|---|---|---|---|"]
    for p in PAIRS:
        rows = [r for r in out if (r["coarse"], r["fine"]) == p]
        L.append(f"| {p[0]} and {p[1]} | {len(rows)} | {sum(r['same_fire'] for r in rows)} | {sum(r['same_count'] for r in rows)} | {sum(r['same_guards'] for r in rows)} | "
                 f"{fm(big(rows, 'd_gain'), '.6f')} | {fm(big(rows, 'd_date'), '.6f')} | {fm(big(rows, 'd_eps3'), '.6f')} | {fm(big(rows, 'd_eps3_frozen'), '.6f')} |")
    L += ["", "The 200 ns runs against the same runs of the earlier campaigns, rows byte for byte: " + ", ".join(f"`{c}` {'same' if s else '**different**'}" for c, s in replay) + ".",
          "", "Runs or values not evaluable: " + ("; ".join(problems) if problems else "none") + ".", "",
          f"**Rule for the step of the campaign.** 400 ns is adopted only if, in every comparison of 400 ns with 200 ns, the FIRE of every read, the counts and the latch and steering counts are the same, "
          f"every gain moves by at most {MZ}, `eps3` by at most {MG} (constants refitted, and frozen), and every latch date by at most {DATE_TOL} unit. "
          f"Result: **{'400 ns is adopted' if adopt else '200 ns is kept'}.**", "",
          f"**Integration margin.** Between 200, 100 and 50 ns, `eps3` moves by at most {fm(big(finer, 'd_eps3'), '.6f')} (constants refitted) and {fm(big(finer, 'd_eps3_frozen'), '.6f')} (constants frozen at 200 ns), "
          f"against `MG` = {MG}: prediction R1 **{'holds' if mg_holds else 'fails'}**. This is the sensitivity to the step over three settings, not a bound on the error against the exact solution.",
          "", "| Case | Port | Steps | `eps3` coarse | `eps3` fine | Change | Change, constants frozen | Change of `D` | Change of `DE` | Largest change of a gain | Largest change of a latch date |", "|---|---|---|---|---|---|---|---|---|---|---|"]
    L += [f"| `{r['case']}` | {r['port']} | {r['coarse']} / {r['fine']} | {fm(r.get('eps3_coarse'), '.6f')} | {fm(r.get('eps3_fine'), '.6f')} | {fm(r.get('d_eps3'), '.6f')} | {fm(r.get('d_eps3_frozen'), '.6f')} | "
          f"{fm(r.get('d_D'), '.6f')} | {fm(r.get('d_DE'), '.6f')} | {fm(r.get('d_gain'), '.6f')} | {fm(r.get('d_date'), '.6f')} |" for r in out]
    (HERE / "STEP.md").write_text("\n".join(L) + "\n")
    save_campaign(tmax="400n" if adopt else "200n", step_rule_complete=bool(complete), R1_holds=bool(mg_holds))
    print("\n".join(L[:14]))
    return 0


# ---- truncation and noise replay
def preflight():
    folder = HERE / "results" / "preflight"
    campaign = json.loads((HERE / "campaign.json").read_text())
    runs = {r["name"]: load(folder, r["name"]) for r in MANIFEST["stages"]["preflight"]}
    full = HERE / "results" / "step" / f"s_nom_train_{campaign['tmax']}.csv"
    machine = next((m["machine"] for _, _, m, _ in runs.values() if m), "?")
    head = full.read_text().splitlines()[:6]
    trunc = (folder / "p_trunc.csv").read_text().splitlines() if runs["p_trunc"][0] is not None else None
    same_trunc = trunc == head
    a, b, c = (runs[n][2] for n in ("p_noise_a", "p_noise_b", "p_noise_c"))
    replay = bool(a and b) and a["csv_sha256"] == b["csv_sha256"] and a["charge_sha256"] == b["charge_sha256"] and a["noise_sha256"] == b["noise_sha256"] and a["trace_sha256"] == b["trace_sha256"]
    other = bool(a and c) and a["noise_sha256"] != c["noise_sha256"] and a["csv_sha256"] != c["csv_sha256"]
    L = [f"# Preflight of the repetitions, machine {machine}", "", f"Written by `rep_analyze.py preflight` on machine {machine}. Nominal cell, step {campaign['tmax']}.", "",
         "| Check | Result |", "|---|---|",
         f"| A training cut after five pulses, with the process id fixed, gives the first five rows of the complete training | {'yes, byte for byte' if same_trunc else '**no**'} |",
         f"| Two noisy runs with the same noise number give the same rows, charges, noise and trace | {'yes, byte for byte' if replay else '**no**'} |",
         f"| A noisy run with another noise number gives another noise and other rows | {'yes' if other else '**no**'} |",
         "", "| Run | Noise number | Rows (SHA-256) | Noise (SHA-256) |", "|---|---|---|---|"]
    L += [f"| `{n}` | {m['run']['noise_id']} | `{m['csv_sha256']}` | `{m['noise_sha256']}` |" if m else f"| `{n}` | | {why} | |" for n, (_, _, m, why) in runs.items()]
    name = "PREFLIGHT.md" if machine == "A" else f"PREFLIGHT_{machine}.md"
    (HERE / name).write_text("\n".join(L) + "\n")
    print("\n".join(L))
    return 0 if same_trunc and replay and other else 1


# ---- the repetitions
def upper_bound(errors, n, alpha=0.05):
    """One-sided Clopper-Pearson upper bound on a probability of error: the p with P[Binomial(n, p) <= errors] = alpha."""
    if errors >= n:
        return 1.0

    def tail(p):
        return sum(math.exp(math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * math.log(p) + (n - k) * math.log1p(-p)) for k in range(errors + 1))
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if mid <= 0.0 or tail(mid) > alpha:
            lo = mid
        else:
            hi = mid
    return hi


def trial(run, rows, charge, P):
    """The endpoints of one port in one repetition, from its reads 0 to m."""
    port, m = P["port"], P["m"]
    t = dict(cell=P["cell"], port=port, m=m, rep=run["rep"], machine=run["machine"], run=run["name"], evaluable=True, reason="")
    pairs = [(r, c) for r, c in zip(rows, charge) if int(r["port"]) == port][:m + 1]
    reads = [r for r, _ in pairs]
    fired = [r["fired"] == 1 for r in reads]
    first = next((i for i, f in enumerate(fired) if f), None)
    t.update(first_fire="" if first is None else first, count_agrees=first == m)
    other = 3 - port
    guards = []
    if any(not 0.1 <= r["c_pre"] <= 0.1001 for r in reads):
        guards.append("a rest state is outside the band")
    if any(r["latch_rises"] > 1 for r in reads):
        guards.append("the latch rises twice in a period")
    if any(r[f"steer_rises{port}"] != (0 if f else 1) or r[f"steer_rises{other}"] != 0 for r, f in zip(reads, fired)):
        guards.append("the steering switch does not follow the rule")
    z = [A.gain(r, KAPPA) for r in reads]
    if None in z:
        guards.append("a read has a FIRE earlier than 0.76, or no gain")
    t["guards_ok"] = not guards
    frozen, why = eps3_stat([r for r, _ in pairs], [c for _, c in pairs], port, (P["D0"], P["DE0"]))
    own, _ = eps3_stat([r for r, _ in pairs], [c for _, c in pairs], port)
    t.update(eps3_noisy=frozen["eps3"] if frozen else None, eps3_noisy_refit=own["eps3"] if own else None)
    t["residual_ok"] = bool(frozen) and not guards and frozen["eps3"] <= P["eps3_109"]
    t["certified"] = False
    if frozen is None or None in z:
        guards.append("eps3 not evaluable" if frozen is None else "")
    else:
        e = frozen["eps3"]
        r_of = lambda k: MZ + (EPSK if fired[k] else 0.0)
        dev = [z[k] - z[0] - k * D0 for k in range(m + 1)]
        a = P["a_s"] + abs(z[0] - P["start_gain"]) + MZ + (EPSK if fired[0] else 0.0) + e
        b_silent = max([0.0] + [dev[k] + r_of(k) + r_of(0) for k in range(m)]) + 2 * e
        b_fire = max(0.0, -dev[m] + r_of(m) + r_of(0)) + 2 * e
        ell = P["h3"] + max(r["noise_sup_V"] for r in reads) / 0.5 + MQ
        t.update(a=a, B_silent=b_silent, B_fire=b_fire, ell=ell, silence_room=D0 / 2 - a - b_silent - 20 / 17 * ell - 1 / 8000,
                 fire_room=D0 / 2 - a - b_fire - 20 / 17 * ell)
        if P["level0"] - ell < 0.95:
            guards.append("level0 - ell is below 19/20")
        if t["silence_room"] <= 0:
            guards.append("silence room")
        if t["fire_room"] < 0:
            guards.append("FIRE room")
        t["certified"] = not guards
    t["reason"] = "; ".join(g for g in guards if g)
    t["contradicted"] = t["certified"] and not t["count_agrees"]
    return t


def report(base):
    runs = MANIFEST["stages"]["repeat"]
    reps = sorted({r["rep"] for r in runs})
    done = [rep for rep in reps if (base / "results" / "repeat" / f"rep{rep:02d}" / "ARCHIVE.json").exists()]
    ports = {(p["seed"], p["port"]): p for p in FROZEN["ports"]}
    trials, failed, noise = [], [], {}
    for run in runs:
        if run["rep"] not in done:
            continue
        rows, charge, meta, why = load(base / "results" / "repeat" / f"rep{run['rep']:02d}", run["name"])
        if rows is None:
            failed.append(f"`{run['name']}`: {why}")
        else:
            noise.setdefault(meta["noise_sha256"], []).append(run["name"])
        for port, m in run["ports"]:
            P = ports[(run["seed"], port)]
            if rows is None:
                trials.append(dict(cell=P["cell"], port=port, m=m, rep=run["rep"], machine=run["machine"], run=run["name"], evaluable=False, reason=why,
                                   count_agrees=False, guards_ok=False, residual_ok=False, certified=False, contradicted=False))
            else:
                trials.append(trial(run, rows, charge, P))
    fields = ["cell", "port", "m", "rep", "machine", "run", "evaluable", "first_fire", "count_agrees", "guards_ok", "eps3_noisy", "eps3_noisy_refit", "residual_ok",
              "a", "B_silent", "B_fire", "ell", "silence_room", "fire_room", "certified", "contradicted", "reason"]

    def write(name, rows, cols):
        with (base / name).open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=cols, lineterminator="\n", extrasaction="ignore")
            w.writeheader()
            for r in rows:
                w.writerow({k: ("" if r.get(k) is None else (format(r[k], ".12g") if isinstance(r[k], float) else r[k])) for k in cols})
    write("trials.csv", trials, fields)
    family = len(ports)
    table = []
    for (seed, port), P in sorted(ports.items()):
        mine = [t for t in trials if t["cell"] == P["cell"] and t["port"] == port]
        n, wrong = len(mine), sum(not t["count_agrees"] for t in mine)
        eps = [t["eps3_noisy"] for t in mine if t.get("eps3_noisy") is not None]
        refit = [t["eps3_noisy_refit"] for t in mine if t.get("eps3_noisy_refit") is not None]
        table.append(dict(cell=P["cell"], port=port, m=P["m"], group="37" if P["status3_109"].startswith("certified") else "A1 only", trials=n, count_agrees=n - wrong, count_wrong=wrong,
                          error_upper_95=upper_bound(wrong, n) if n else None, error_upper_simultaneous=upper_bound(wrong, n, 0.05 / family) if n else None,
                          residual_ok=sum(t["residual_ok"] for t in mine), certified=sum(t["certified"] for t in mine), contradicted=sum(t["contradicted"] for t in mine),
                          eps3_109=P["eps3_109"], eps3_noisy_median=statistics.median(eps) if eps else None, eps3_noisy_max=max(eps) if eps else None,
                          eps3_refit_median=statistics.median(refit) if refit else None, eps3_refit_max=max(refit) if refit else None))
    write("ports.csv", table, ["cell", "port", "m", "group", "trials", "count_agrees", "count_wrong", "error_upper_95", "error_upper_simultaneous", "residual_ok", "certified", "contradicted",
                               "eps3_109", "eps3_noisy_median", "eps3_noisy_max", "eps3_refit_median", "eps3_refit_max"])

    # ---- report
    n, wrong = len(trials), sum(not t["count_agrees"] for t in trials)
    cert = [t for t in trials if t["certified"]]
    contra = [t for t in cert if t["contradicted"]]
    eps = [t["eps3_noisy"] for t in trials if t.get("eps3_noisy") is not None]
    refit = [t["eps3_noisy_refit"] for t in trials if t.get("eps3_noisy_refit") is not None]
    resid = sum(t["residual_ok"] for t in trials)
    worst = max((r["count_wrong"] for r in table), default=0)
    over = [r for r in table if r["trials"] and r["count_wrong"] / r["trials"] > 0.10]
    dup = {h: v for h, v in noise.items() if len(v) > 1}
    campaign = json.loads((HERE / "campaign.json").read_text())
    med = lambda v: statistics.median(v) if v else None
    planned = sum(len(r["ports"]) for r in runs)
    full = len(done) == len(reps)

    def verdict(holds, evaluable=True):
        return "not evaluable" if not evaluable else ("holds" if holds else "fails")
    V = [("R1", "between 200, 100 and 50 ns `eps3` moves by at most 0.0001", "see [`STEP.md`](STEP.md)", verdict(campaign.get("R1_holds", False), campaign.get("step_rule_complete", False))),
         ("R2", "no run fails", f"{len(failed)} of {sum(1 for r in runs if r['rep'] in done)} runs without a usable result", verdict(not failed, full)),
         ("R3", "the count is the predicted `m` in at least 97% of the trials", f"{n - wrong} of {n} ({100 * (n - wrong) / max(n, 1):.2f}%)", verdict(n > 0 and (n - wrong) / n >= 0.97, full)),
         ("R4", "no port has its count wrong in more than 10% of its repetitions", f"largest number of wrong counts for one port: {worst} of {table[0]['trials'] if table else 0}; ports above 10%: {len(over)}", verdict(not over, full)),
         ("R5", "the median `eps3` measured on the noisy runs is between 0.0005 and 0.003", f"{fm(med(eps))} over {len(eps)} trials", verdict(bool(eps) and 0.0005 <= med(eps) <= 0.003, full)),
         ("R6", "no repetition certified on its own measures has a wrong count", f"{len(contra)} of {len(cert)} certified trials", verdict(not contra, full and bool(cert))),
         ("R7", "the noise of every run is different", f"{len(noise)} different noises over {sum(len(v) for v in noise.values())} runs", verdict(not dup, full))]
    pooled = upper_bound(wrong, n) if n else None
    L = ["# Repetition campaign: report", "",
         "Written by `rep_analyze.py report` under [`PREDICTION.md`](PREDICTION.md) and [`AMENDMENT_1.md`](AMENDMENT_1.md). Step study: [`STEP.md`](STEP.md). Options: [`ACCEL.md`](ACCEL.md). "
         "One row per port and repetition: [`trials.csv`](trials.csv). One row per port: [`ports.csv`](ports.csv).", "",
         f"Repetitions analysed: {len(done)} of {len(reps)} ({', '.join(str(r) for r in done)}); {n} trials of {planned} planned. Step of the transient analysis: {campaign['tmax']}.", "",
         "## Summary", "",
         f"1. **Step.** {'400 ns was adopted by the rule written in advance' if campaign['tmax'] == '400n' else '200 ns was kept by the rule written in advance'}. Between 200, 100 and 50 ns the change of `eps3` "
         f"{'stays within' if campaign.get('R1_holds') else 'exceeds'} the integration margin `MG` = {MG} ([`STEP.md`](STEP.md)); this is a sensitivity to the step, not a bound on the error of the solver.",
         f"2. **Count.** The count is the predicted `m` in {n - wrong} of {n} trials ({len(ports)} ports, {len(done)} repetitions each, fresh noise each time). "
         f"One-sided 95% Clopper-Pearson upper bound on the probability of a wrong count, trials pooled: {fm(None if pooled is None else 100 * pooled, '.3f')}%. Pooling assumes interchangeable ports and independent trials.",
         f"3. **Per port.** The largest number of wrong counts for one port is {worst} of {table[0]['trials'] if table else 0}; {sum(1 for r in table if r['count_wrong'] == 0)} ports have none. "
         f"With no wrong count in 20 repetitions the bound for one port is {100 * upper_bound(0, 20):.1f}%, and {100 * upper_bound(0, 20, 0.05 / family):.1f}% simultaneously for the {family} ports.",
         f"4. **`eps3` on noisy runs.** With the two constants of each port frozen at their values without noise: median {fm(med(eps))}, largest {fm(max(eps) if eps else None)}; it is at most the `eps3` measured without noise "
         f"in {resid} of {n} trials. Refitted on each run: median {fm(med(refit))}, largest {fm(max(refit) if refit else None)}.",
         f"5. **Certified repetitions.** {len(cert)} of {n} trials satisfy rule A1 with every bound measured on the repetition itself, `eps3` included; the count is wrong in {len(contra)} of them. "
         "It stays a simulation; the gain of a read with a FIRE is checked by the current up to 0.75 unit only.", "",
         "## Predictions", "", "| | Prediction | Measured | Verdict |", "|---|---|---|---|"]
    L += [f"| {a} | {b} | {c} | {d} |" for a, b, c, d in V]
    L += ["", "## Failures", "",
          "- **F1, a repetition certified on its own measures with a wrong count:** " + (", ".join(f"`{t['run']}` port {t['port']}" for t in contra) if contra else "none") + ".",
          "- **F2, a port with a wrong count in more than 10% of its repetitions:** " + (", ".join(f"`{r['cell']}` port {r['port']} ({r['count_wrong']} of {r['trials']})" for r in over) if over else "none") + ".",
          "- **Runs without a usable result:** " + ("; ".join(failed) if failed else "none") + ".",
          "- **Runs that share a noise:** " + ("; ".join(", ".join(v) for v in dup.values()) if dup else "none") + ".",
          "", "## `eps3` on noisy runs, and repeatability, per port", "",
          "`37`: port certified by status 3 of the certification-unconditional campaign; `A1 only`: port that passes rule A1 only. Bounds are one-sided 95% Clopper-Pearson upper bounds on the probability of a wrong count.", "",
          "| Cell | Port | m | Group | Trials | Count = m | Wrong | Upper bound | Simultaneous | `eps3` without noise | `eps3` noisy, median | largest | refitted, median | largest | At most the noiseless `eps3` | Certified | Contradicted |",
          "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    L += [f"| `{r['cell']}` | {r['port']} | {r['m']} | {r['group']} | {r['trials']} | {r['count_agrees']} | {r['count_wrong']} | {fm(None if r['error_upper_95'] is None else 100 * r['error_upper_95'], '.1f')}% | "
          f"{fm(None if r['error_upper_simultaneous'] is None else 100 * r['error_upper_simultaneous'], '.1f')}% | {fm(r['eps3_109'])} | {fm(r['eps3_noisy_median'])} | {fm(r['eps3_noisy_max'])} | "
          f"{fm(r['eps3_refit_median'])} | {fm(r['eps3_refit_max'])} | {r['residual_ok']} | {r['certified']} | {r['contradicted']} |" for r in table]
    groups = {}
    for r in table:
        g = groups.setdefault(r["group"], [0, 0, 0])
        g[0] += r["trials"]
        g[1] += r["count_wrong"]
        g[2] += 1
    L += ["", "| Group | Ports | Trials | Wrong counts | Upper bound, pooled |", "|---|---|---|---|---|"]
    L += [f"| {k} | {v[2]} | {v[0]} | {v[1]} | {fm(100 * upper_bound(v[1], v[0]) if v[0] else None, '.3f')}% |" for k, v in sorted(groups.items())]
    by_machine = {}
    for t in trials:
        g = by_machine.setdefault(t["machine"], [0, 0])
        g[0] += 1
        g[1] += not t["count_agrees"]
    L += ["", "| Machine | Trials | Wrong counts |", "|---|---|---|"] + [f"| {k} | {v[0]} | {v[1]} |" for k, v in sorted(by_machine.items())]
    wrong_list = [t for t in trials if not t["count_agrees"]]
    L += ["", "## Trials with a wrong count", ""]
    if wrong_list:
        L += ["| Run | Port | m | First FIRE among the reads 0 to m | Certified on its own measures | Silence room | FIRE room | Reason |", "|---|---|---|---|---|---|---|---|"]
        L += [f"| `{t['run']}` | {t['port']} | {t['m']} | {t.get('first_fire', '') if t.get('first_fire', '') != '' else 'none'} | {'yes' if t['certified'] else 'no'} | {fm(t.get('silence_room'), '+.5f')} | {fm(t.get('fire_room'), '+.5f')} | {t['reason'] or DASH} |" for t in wrong_list]
    else:
        L.append("None.")
    archives = [json.loads((base / "results" / "repeat" / f"rep{rep:02d}" / "ARCHIVE.json").read_text()) for rep in done]
    L += ["", "## Traces", "",
          f"- Reduced traces: {sum(len(a['traces']) for a in archives)} traces in {len(archives)} archives of the private repository `HevisNico/kernel-R-circuit`, folder `09-repetition-traces/`. "
          "Each archive was read back from GitHub and its SHA-256 compared before the local traces were removed; the SHA-256 of each archive and of each trace is in `results/repeat/repNN/ARCHIVE.json`.",
          "- A reduced trace holds, for each read 0 to `m` of a port of rule A1, the solver points of its pulse and the signals that enter a measure: main charge, latch, noise of the threshold, steering, and the currents of the two mirrors with their noise.",
          "- A noisy run is replayed by its noise number: the process id seen by the simulator is fixed, the binary is not modified (`fakepid.c`, [`PREFLIGHT.md`](PREFLIGHT.md))."]
    (base / "REPORT.md").write_text("\n".join(L) + "\n")
    print("\n".join(L[:16 + len(V)]))
    return 0


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "report":
        sys.exit(report(Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else HERE))
    sys.exit({"accel": accel, "step": step, "preflight": preflight}[cmd]())
