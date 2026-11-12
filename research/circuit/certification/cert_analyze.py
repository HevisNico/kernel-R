"""Analysis of the certification campaign, by the rules of PREDICTION.md. No simulation is run.

  cert_analyze.py calibrate   stage 1: constants from the calibration cohort   -> calibration.json, CALIBRATION.md
  cert_analyze.py predict     stage 2: predicted need of each test port         -> predictions.csv, PREDICTED.md
  cert_analyze.py certify     stage 3: budget and status of each test port      -> ports.csv, REPORT.md

A value that cannot be computed is reported as not evaluable, with its reason. Nothing is substituted.
"""
import csv
import json
import math
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
import analyze
from cert_run import EXTRA, MODES

CS, CF = 400e-15, 30e-12
MZ, MQ = 0.0002, 0.0002
TARGET = 0.0026
EARLY = 0.76
DASH = "—"
MANIFEST = json.loads((HERE / "manifest.json").read_text())


def fm(x, spec=".5f"):
    return DASH if x is None else format(x, spec)


def load(stage, name):
    """Rows and metadata of a run, or None and the reason."""
    folder = HERE / "results" / stage
    if (folder / f"{name}.failed").exists():
        return None, None, "run failed: " + (folder / f"{name}.failed").read_text().splitlines()[0]
    if not (folder / f"{name}.json").exists():
        return None, None, "run missing"
    meta = json.loads((folder / f"{name}.json").read_text())
    if meta["run"]["mode"] == "ramp":
        return [], meta, None
    ports = MODES[meta["run"]["mode"]]["ports"]
    checked, why = analyze.read_run(str(folder / f"{name}.csv"), ports)
    if checked is None:
        return None, meta, "result rejected: " + why
    with (folder / f"{name}.csv").open(newline="") as fh:
        rows = [{k: float(v) for k, v in r.items()} for r in csv.DictReader(fh)]
    if any(not math.isfinite(r[k]) for r in rows for k in EXTRA):
        return None, meta, "result rejected: a value is not finite"
    return rows, meta, None


def gain_silent(r):
    x = r["q_peak"] - 0.1 - (r["c_pre"] - 0.1) * math.exp(-0.5)
    return math.log(x) if x > 0 else None


def gain_early(r):
    x = r["q_tc"] - 0.1 - (r["c_pre"] - 0.1) * math.exp(-0.375)
    return math.log(x) if x > 0 else None


def reads_of(rows, port):
    return [r for r in rows if int(r["port"]) == port]


def count_of(reads):
    return next((i for i, r in enumerate(reads) if r["fired"] == 1), len(reads))


def gain(r, kappa):
    """Gain of a read: from its peak if it is silent, from its early gain if it has a FIRE. None if it has none."""
    if r["fired"] != 1:
        return gain_silent(r)
    if r["fire_latency"] < EARLY:
        return None
    y = gain_early(r)
    return None if y is None else y + kappa


# ---- stage 1
def calibrate():
    C = dict(rule="PREDICTION.md, constants of stage 1", problems=[])
    kap, pairs_raw, slope_num, slope_den, per = [], [], 0.0, 0.0, {}
    for run in MANIFEST["stages"]["calibration"]:
        if run["mode"] != "train":
            continue
        rows, meta, why = load("calibration", run["name"])
        if rows is None:
            C["problems"].append(f"{run['name']}: {why}")
            continue
        for port in (1, 2):
            reads = reads_of(rows, port)
            k = count_of(reads)
            silent = [r for r in reads if r["fired"] != 1]
            for r in silent:
                g, y = gain_silent(r), gain_early(r)
                if g is None or y is None:
                    C["problems"].append(f"{run['name']} port {port}: a gain cannot be computed")
                else:
                    kap.append(g - y)
            before = [r for r in reads[:k]]
            gs, vs = [gain_silent(r) for r in before], [r[f"vbar{port}"] for r in before]
            if len(before) >= 2 and None not in gs:
                mg, mv = statistics.mean(gs), statistics.mean(vs)
                slope_num += sum((v - mv) * (g - mg) for v, g in zip(vs, gs))
                slope_den += sum((v - mv) ** 2 for v in vs)
            per[(run["name"], port)] = (reads, k)
    if not kap:
        C["problems"].append("no silent read in the cohort")
        C["status"] = "not evaluable"
        (HERE / "calibration.json").write_text(json.dumps(C, indent=2) + "\n")
        return C
    kappa = statistics.mean(kap)
    steps = []
    for (name, port), (reads, k) in per.items():
        last = min(k, len(reads) - 1)
        z = [gain(r, kappa) for r in reads[:last + 1]]
        for n in range(last):
            if z[n] is None or z[n + 1] is None:
                C["problems"].append(f"{name} port {port}: read {n} or {n + 1} has no gain")
            else:
                steps.append(z[n + 1] - z[n])
    C.update(kappa=kappa, kappa_reads=len(kap), eps_kappa_cohort=max(abs(x - kappa) for x in kap),
             d0=statistics.mean(steps) if steps else None, d0_pairs=len(steps),
             d0_sigma=statistics.stdev(steps) if len(steps) > 1 else None, d0_min=min(steps) if steps else None, d0_max=max(steps) if steps else None,
             s_per_V=-slope_num / slope_den if slope_den > 0 else None)
    # the firing level against the static level, from the leak scans
    scans = [("preflight", "nom_leak", "preflight", "nom_ramp")] + [
        ("calibration", r["name"], "calibration", r["name"].replace("_leak", "_ramp")) for r in MANIFEST["stages"]["calibration"] if r["mode"] == "leak"]
    mids, halves, detail = [], [], []
    for stage, name, rstage, rname in scans:
        rows, meta, why = load(stage, name)
        _, rmeta, rwhy = load(rstage, rname)
        if rows is None or rmeta is None:
            C["problems"].append(f"{name}: {why or rwhy}")
            continue
        k = count_of(rows)
        j = next((i for i in range(k + 1, len(rows)) if rows[i]["fired"] != 1), None)
        if k >= len(rows) or j is None:
            C["problems"].append(f"{name}: no silent read after the first FIRE")
            continue
        before = rows[j - 1]
        z = gain(before, kappa)
        if z is None:
            C["problems"].append(f"{name}: the read before the silent one has no gain")
            continue
        ps = rows[j]["q_peak"]
        pf = 0.1 + (before["c_pre"] - 0.1) * math.exp(-0.5) + math.exp(z)
        ls = rmeta["static_level"]
        mids.append((ps + pf) / 2 - ls)
        halves.append(abs(pf - ps) / 2)
        detail.append(dict(run=name, first_fire=k, silent_read=j, peak_silent=ps, peak_before=pf, static_level=ls, mid_minus_static=mids[-1], half_width=halves[-1]))
    C["leak_scans"] = detail
    if len(mids) == len(scans):
        mu = statistics.mean(mids)
        C.update(mu=mu, h_mu=max(abs(x - mu) for x in mids) + max(halves))
    else:
        C.update(mu=None, h_mu=None)
    C["status"] = "evaluated" if None not in (C["d0"], C["mu"], C["s_per_V"]) and not C["problems"] else "not evaluable"
    (HERE / "calibration.json").write_text(json.dumps(C, indent=2) + "\n")
    L = ["# Constants of stage 1", "", "Written by `cert_analyze.py calibrate` from the calibration cohort, under `PREDICTION.md`.", "",
         f"Status: **{C['status']}**." + (" Problems: " + "; ".join(C["problems"]) + "." if C["problems"] else ""), "",
         "| Constant | Value | From |", "|---|---|---|",
         f"| `kappa` | {fm(kappa)} | {len(kap)} silent reads; largest distance to it {C['eps_kappa_cohort']:.5f} |",
         f"| `d0` | {fm(C['d0'])} | {len(steps)} pairs of successive reads; sigma {fm(C['d0_sigma'])}, from {fm(C['d0_min'])} to {fm(C['d0_max'])} |",
         f"| `s` | {fm(C['s_per_V'], '.3f')} per V | slope of the gain against the stored voltage, silent reads before the first FIRE |",
         f"| `mu` | {fm(C['mu'])} | firing level minus static level, {len(mids)} of {len(scans)} leak scans |",
         f"| `h_mu` | {fm(C['h_mu'])} | spread of `mu` between cells plus the largest half-width of a scan |", "",
         "**Scope:** `h_mu` is the worst case on six cells (five calibration cells and the nominal cell), not a bound established for each test cell. "
         "Applying it to the 100 test cells assumes that the calibration covers their dynamic threshold offsets. "
         "The inferred gains also assume the scalar model's peak-to-gain correspondence; these simulations do not prove that correspondence.", "",
         "| Leak scan | First FIRE | Silent read | Peak of the silent read | Peak of the read before | Static level | Midpoint minus static | Half-width |", "|---|---|---|---|---|---|---|---|"]
    L += [f"| `{d['run']}` | {d['first_fire']} | {d['silent_read']} | {d['peak_silent']:.5f} | {d['peak_before']:.5f} | {d['static_level']:.5f} | {d['mid_minus_static']:+.5f} | {d['half_width']:.5f} |" for d in detail]
    (HERE / "CALIBRATION.md").write_text("\n".join(L) + "\n")
    print("\n".join(L))
    return C


# ---- stage 2
def predict():
    C = json.loads((HERE / "calibration.json").read_text())
    out = []
    for run in MANIFEST["stages"]["test"]:
        seed = run["seed"]
        _, ramp, rwhy = load("characterization", f"t{seed}_ramp")
        rows, _, why = load("characterization", f"t{seed}_read")
        for port in (1, 2):
            row = dict(cell=f"t{seed}", port=port, static_level=None, level0=None, start_gain=None, gap=None, m=None, a_s=None, reason="")
            out.append(row)
            if C["status"] != "evaluated":
                row["reason"] = "a constant of stage 1 is not evaluable"
            elif ramp is None or rows is None:
                row["reason"] = rwhy or why
            else:
                r = reads_of(rows, port)[0]
                g = gain(r, C["kappa"])
                if g is None:
                    row["reason"] = "the first read has no gain"
                    continue
                ls = ramp["static_level"]
                gap = math.log(ls + C["mu"] - 0.1) - g
                m = 0 if gap <= 0 else math.ceil(gap / C["d0"] - 1e-12)
                row.update(static_level=ls, level0=ls + C["mu"], start_gain=g, first_read_fires=int(r["fired"]), gap=gap, m=m,
                           a_s=abs(gap - (m - 0.5) * C["d0"]))
    fields = ["cell", "port", "static_level", "level0", "start_gain", "first_read_fires", "gap", "m", "a_s", "reason"]
    with (HERE / "predictions.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n")
        w.writeheader()
        for r in out:
            w.writerow({k: ("" if r.get(k) is None else (format(r[k], ".12g") if isinstance(r[k], float) else r[k])) for k in fields})
    ok = [r for r in out if r["m"] is not None]
    counts = {}
    for r in ok:
        counts[r["m"]] = counts.get(r["m"], 0) + 1
    levels = sorted({(r["cell"], r["static_level"]) for r in ok})
    L = ["# Predicted need of each test port", "", "Written by `cert_analyze.py predict` before the test runs, from stage 2 and the constants of stage 1.", "",
         f"- Ports with a prediction: {len(ok)} of {len(out)}." + ("" if len(ok) == len(out) else " Not evaluable: " + "; ".join(f"{r['cell']} port {r['port']} ({r['reason']})" for r in out if r["m"] is None) + "."),
         "- Ports per predicted need `m`: " + ", ".join(f"{k}: {counts[k]}" for k in sorted(counts)) + ".",
         f"- Static level of the cells: mean {fm(statistics.mean(v for _, v in levels) if levels else None)}, standard deviation {fm(statistics.stdev(v for _, v in levels) if len(levels) > 1 else None)}, "
         f"from {fm(min((v for _, v in levels), default=None))} to {fm(max((v for _, v in levels), default=None))}.",
         f"- Median `a_s`: {fm(statistics.median(r['a_s'] for r in ok) if ok else None)}; `d0/2` = {fm(C['d0'] / 2 if C.get('d0') else None)}.", "",
         "The table is `predictions.csv`."]
    (HERE / "PREDICTED.md").write_text("\n".join(L) + "\n")
    print("\n".join(L))


# ---- stage 3
def certify():
    C = json.loads((HERE / "calibration.json").read_text())
    with (HERE / "predictions.csv").open(newline="") as fh:
        pred = {(r["cell"], int(r["port"])): r for r in csv.DictReader(fh)}
    kappa, d0, s = C.get("kappa"), C.get("d0"), C.get("s_per_V")
    runs = {}
    for run in MANIFEST["stages"]["test"]:
        runs[f"t{run['seed']}"] = load("test", run["name"])
    eps = None
    if kappa is not None:
        dev = [abs(gain_silent(r) - gain_early(r) - kappa) for rows, _, _ in runs.values() if rows for r in rows
               if int(r["port"]) in (1, 2) and r["fired"] != 1 and gain_silent(r) is not None and gain_early(r) is not None]
        eps = max(dev) if dev else None
    out, E = [], dict(rest_outside=0, rest_total=0, latch_twice=0, steer_bad=0, periods=0)
    for cell, (rows, meta, why) in runs.items():
        if rows:
            for r in rows:
                E["rest_total"] += 1
                E["periods"] += 1
                E["rest_outside"] += not 0.1 <= r["c_pre"] <= 0.1001
                E["latch_twice"] += r["latch_rises"] > 1
                p = int(r["port"])
                on = [r["steer_rises1"], r["steer_rises2"]]
                if p in (1, 2):
                    E["steer_bad"] += (on[p - 1] != (0 if r["fired"] == 1 else 1)) or on[2 - p] != 0
                else:
                    E["steer_bad"] += any(x != (0 if r["fired"] == 1 else 1) for x in on)
        for port in (1, 2):
            P = pred.get((cell, port), {})
            row = dict(cell=cell, port=port, m=P.get("m", ""), status="not evaluable", reason="")
            out.append(row)
            if C["status"] != "evaluated" or eps is None:
                row["reason"] = "a constant is not evaluable"
                continue
            if rows is None:
                row["reason"] = why
                continue
            if not P or P["m"] == "":
                row["reason"] = "no prediction: " + (P.get("reason") or "missing")
                continue
            m, a_s, level0, g0s = int(P["m"]), float(P["a_s"]), float(P["level0"]), float(P["start_gain"])
            reads = reads_of(rows, port)
            k = count_of(reads)
            r_ = min(k, m, 9)
            part = reads[:r_ + 1]
            z = [gain(x, kappa) for x in part]
            row.update(count=k, r=r_, a_s=a_s, level0=level0)
            if None in z:
                row["reason"] = "a read has a FIRE earlier than 0.76, or no gain"
                continue
            fire_last = part[r_]["fired"] == 1
            a = a_s + abs(z[0] - g0s) + MZ + (eps if part[0]["fired"] == 1 else 0.0)
            dev = [abs(z[n] - z[0] - n * d0) for n in range(1, r_ + 1)]
            B = (max(dev) if dev else 0.0) + (eps if fire_last else 0.0) + 2 * MZ
            noise = max(x["noise_sup_V"] for x in part) / 0.5
            ell = C["h_mu"] + noise + MQ
            room = d0 / 2 - a - B - 20 / 17 * ell - 1 / 8000
            row.update(a=a, start_shift=abs(z[0] - g0s), B=B, B_at=(dev.index(max(dev)) + 1) if dev else 0, noise=noise, ell=ell, room=room,
                       half_d0=d0 / 2, level_term=20 / 17 * ell)
            # per write, reported only
            ks, sg, es, bd = [], [], [], []
            full = [gain(x, kappa) for x in reads[:min(k, 9) + 1]]
            for j in range(min(k, 9)):
                w = reads[j]
                if w["vs_entry"] < 0 or full[j] is None or full[j + 1] is None:
                    continue
                dvs = w["vs_entry"] - w["vs_exit"]
                dcap = (w["vmem_entry"] - w["sum_entry"]) - (w["vmem_exit"] - w["sum_exit"])
                ks.append(s / CF * abs(CF * dcap - CS * dvs))
                sg.append(abs(s * (CS / CF) * dvs - d0))
                es.append(abs(full[j + 1] - full[j] - s * dcap))
                bd.append(abs(full[j + 1] - full[j] - d0))
            if bd:
                row.update(k_eta=max(ks), sigma=max(sg), e=max(es), b_sum=max(x + y + w_ for x, y, w_ in zip(ks, sg, es)) + 2 * MZ, b_direct=max(bd) + 2 * MZ)
            why_out = []
            if any(not 0.1 <= x["c_pre"] <= 0.1001 for x in part):
                why_out.append("a rest state is outside the band")
            if any(x["latch_rises"] > 1 for x in part):
                why_out.append("the latch rises twice in a period")
            if any(x[f"steer_rises{port}"] != (0 if x["fired"] == 1 else 1) or x[f"steer_rises{3 - port}"] != 0 for x in part):
                why_out.append("the steering switch does not follow the rule")
            if level0 - ell < 0.95:
                why_out.append("level0 - ell is below 19/20")
            if room <= 0:
                terms = {"a": a, "B": B, "(20/17)*ell": 20 / 17 * ell}
                why_out.append(f"room is not positive; largest term {max(terms, key=terms.get)}")
            agrees = (k == m) if m <= 9 else (k >= 10)
            row["count_agrees"] = agrees
            if why_out:
                row.update(status="outside the certified domain", reason="; ".join(why_out))
            else:
                row.update(status="certified, count confirmed" if agrees else "certified, count contradicted")
    fields = ["cell", "port", "m", "count", "count_agrees", "status", "reason", "r", "half_d0", "a_s", "start_shift", "a", "B", "B_at", "noise", "ell", "level_term",
              "room", "level0", "k_eta", "sigma", "e", "b_sum", "b_direct"]
    with (HERE / "ports.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n")
        w.writeheader()
        for r in out:
            w.writerow({k: ("" if r.get(k) is None else (format(r[k], ".12g") if isinstance(r[k], float) else r[k])) for k in fields})

    # ---- report
    n = len(out)
    by = {}
    for r in out:
        by[r["status"]] = by.get(r["status"], 0) + 1
    ev = [r for r in out if "room" in r]
    cert = [r for r in out if r["status"].startswith("certified")]
    wrong = [r for r in cert if r["status"].endswith("contradicted")]
    agree = [r for r in out if r.get("count_agrees") is True]
    with_count = [r for r in out if "count_agrees" in r]
    bdir = sorted(r["b_direct"] for r in out if "b_direct" in r)
    bsum = sorted(r["b_sum"] for r in out if "b_sum" in r)
    failed = [c for c, (rows, _, why) in runs.items() if rows is None]
    levels = sorted({(r["cell"], float(pred[(r["cell"], r["port"])]["static_level"])) for r in out if pred.get((r["cell"], r["port"]), {}).get("static_level")})
    sd_level = statistics.stdev(v for _, v in levels) if len(levels) > 1 else None
    med = lambda v: statistics.median(v) if v else None
    share = lambda v, lim: sum(x <= lim for x in v) / len(v) if v else None

    def verdict(holds, evaluable=True):
        return "not evaluable" if not evaluable else ("holds" if holds else "fails")
    V = [("E1", "every rest state inside the band", f"{E['rest_total'] - E['rest_outside']} of {E['rest_total']} inside", verdict(E["rest_outside"] == 0, E["rest_total"] > 0 and not failed)),
         ("E2", "latch at most once per period, steering by the rule", f"{E['latch_twice']} periods with two rises, {E['steer_bad']} periods off the rule, of {E['periods']}",
          verdict(E["latch_twice"] == 0 and E["steer_bad"] == 0, E["periods"] > 0 and not failed)),
         ("E3", "count equals `m` on 85% to 98% of the ports", f"{len(agree)} of {len(with_count)} ports with a count and a prediction ({100 * len(agree) / max(len(with_count), 1):.1f}%)",
          verdict(0.85 <= len(agree) / n <= 0.98, len(with_count) == n)),
         ("E4", "20% to 60% of the ports certified", f"{len(cert)} of {n} ({100 * len(cert) / n:.1f}%)", verdict(0.20 <= len(cert) / n <= 0.60, len(ev) + by.get("not evaluable", 0) == n and not by.get("not evaluable"))),
         ("E5", "no certified port with its count contradicted", f"{len(wrong)} of {len(cert)} certified ports", verdict(not wrong, bool(cert) or not by.get("not evaluable"))),
         ("E6", "target missed: fewer than 25% of ports with `b_direct <= 0.0026`, median between 0.004 and 0.012",
          f"{fm(None if share(bdir, TARGET) is None else 100 * share(bdir, TARGET), '.1f')}% of {len(bdir)} ports, median {fm(med(bdir))}",
          verdict(bool(bdir) and share(bdir, TARGET) < 0.25 and 0.004 <= med(bdir) <= 0.012, bool(bdir))),
         ("E7", "standard deviation of the static level between 0.001 and 0.008", fm(sd_level), verdict(sd_level is not None and 0.001 <= sd_level <= 0.008, sd_level is not None)),
         ("E8", "no run fails", f"{len(failed)} of {len(runs)} test runs without a usable result" + (": " + ", ".join(failed[:8]) if failed else ""), verdict(not failed))]

    best = max(ev, key=lambda r: r["room"]) if ev else None
    terms = {}
    for r in ev:
        if r["room"] <= 0:
            t = max({"a": r["a"], "B": r["B"], "(20/17)*ell": r["level_term"]}.items(), key=lambda kv: kv[1])[0]
            terms[t] = terms.get(t, 0) + 1
    L = ["# Certification campaign: report", "",
         "Written by `cert_analyze.py certify` under [`PREDICTION.md`](PREDICTION.md). Constants: [`CALIBRATION.md`](CALIBRATION.md). "
         "Predicted needs: [`PREDICTED.md`](PREDICTED.md). One row per port: [`ports.csv`](ports.csv).", "",
         "## Summary", "",
         f"1. **Conditionally certified under the registered rule:** {len(cert)} ports of {n} pass its measured budgets and checks; the count is the predicted one on {len(cert) - len(wrong)} of them"
         + (f" and **contradicted on {len(wrong)}**" if wrong else "") + ".",
         f"2. **Not certified:** {by.get('outside the certified domain', 0)} ports outside the certified domain, {by.get('not evaluable', 0)} not evaluable. "
         + ("Largest term where the room is not positive: " + ", ".join(f"`{k}` on {v} ports" for k, v in sorted(terms.items(), key=lambda kv: -kv[1])) + "." if terms else ""),
         f"3. **Count:** the observed count equals the predicted `m` on {len(agree)} of {len(with_count)} ports, certified or not.",
         f"4. **Target `b <= {TARGET}` per write:** `b_direct` meets it on {fm(None if share(bdir, TARGET) is None else 100 * share(bdir, TARGET), '.1f')}% of the ports; its median is {fm(med(bdir))}, "
         f"{fm(None if med(bdir) is None else med(bdir) / TARGET, '.1f')} times the target. `b_sum` meets it on {fm(None if share(bsum, TARGET) is None else 100 * share(bsum, TARGET), '.1f')}%; median {fm(med(bsum))}.",
         "5. **Scope of certification:** it is conditional on the scalar model's peak-to-gain correspondence and on transferring `mu` to the test cells: "
         "`h_mu` is the worst case on six cells, not a bound established for each test cell. "
         "The comparator/uncut-peak correspondence within `ell` is supported by those six leak scans; "
         f"the gain of a read with a FIRE is read 0.25 unit before the end of its pulse, within `eps_kappa` = {fm(eps)}.", "",
         "## Predictions", "", "| | Prediction | Measured | Verdict |", "|---|---|---|---|"]
    L += [f"| {a} | {b} | {c} | {d} |" for a, b, c, d in V]
    L += ["", "## Hypotheses of the theorem and their bounds", "",
          "| Hypothesis | Bound | Source |", "|---|---|---|",
          f"| Start distance `a` | `a_s` from stage 2 (median {fm(med([r['a_s'] for r in ev]))}), plus the shift of the first read of the test run (median {fm(med([r['start_shift'] for r in ev]))}, largest {fm(max((r['start_shift'] for r in ev), default=None))}), plus {MZ} | ramp and first read of the cell without noise; first read of the test run |",
          f"| Cumulated gain `B` | median {fm(med([r['B'] for r in ev]))}, largest {fm(max((r['B'] for r in ev), default=None))} | gains of the reads of the test run; `d0` = {fm(d0)} from the cohort |",
          f"| Threshold `ell` | `h_mu` = {fm(C.get('h_mu'))}, plus the noise of the threshold in the reads (median {fm(med([r['noise'] for r in ev]))}, largest {fm(max((r['noise'] for r in ev), default=None))}), plus {MQ} | six leak scans; transfer of their bound to each test cell is assumed; noise source recorded in each read |",
          f"| `19/20 <= level` | smallest `level0 - ell`: {fm(min((r['level0'] - r['ell'] for r in ev), default=None))} | ramp of each cell |",
          f"| Rest band | {E['rest_total'] - E['rest_outside']} of {E['rest_total']} states inside `[0.1, 0.1001]` | 1 ps before each pulse of the test runs |",
          f"| One FIRE per read, one write per silent pulse, none with a FIRE | {E['latch_twice']} periods with two rises, {E['steer_bad']} off the steering rule, of {E['periods']} | latch and steering signals of the test runs |",
          f"| Gain of a read with a FIRE | within `eps_kappa` = {fm(eps)} of the early gain plus `kappa` = {fm(kappa)} | largest distance over the silent reads of the test runs |",
          f"| Per write, reported: `k*eta`, `sigma`, `e` | medians {fm(med([r['k_eta'] for r in out if 'k_eta' in r]))}, {fm(med([r['sigma'] for r in out if 'sigma' in r]))}, {fm(med([r['e'] for r in out if 'e' in r]))} | window endpoints of each write; slope `s` = {fm(s, '.3f')} per V |", ""]
    if best:
        L += [f"Port with the largest room: `{best['cell']}`, port {best['port']}: {best['room']:+.5f}, with `a` = {best['a']:.5f}, `B` = {best['B']:.5f}, `(20/17)*ell` = {best['level_term']:.5f}, against `d0/2` = {best['half_d0']:.5f}.", ""]
    L += ["## The 200 ports", "", "| Status | Ports |", "|---|---|"] + [f"| {k} | {v} |" for k, v in sorted(by.items(), key=lambda kv: -kv[1])]
    L += ["", "| Cell | Port | m | Count | Agrees | `a` | `B` | `(20/17)*ell` | Room | `b_direct` | Status | Reason |", "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in out:
        L.append(f"| `{r['cell']}` | {r['port']} | {r.get('m', '')} | {r.get('count', DASH)} | {DASH if 'count_agrees' not in r else ('yes' if r['count_agrees'] else 'no')} | {fm(r.get('a'))} | {fm(r.get('B'))} | "
                 f"{fm(r.get('level_term'))} | {fm(r.get('room'), '+.5f')} | {fm(r.get('b_direct'))} | {r['status']} | {r['reason'] or DASH} |")
    L += traces_section()
    (HERE / "REPORT.md").write_text("\n".join(L) + "\n")
    print("\n".join(L[:22 + len(V)]))


def traces_section():
    """What is kept of each run, and what a reader can check."""
    import hashlib
    import subprocess
    metas = [json.loads(p.read_text()) for stage in MANIFEST["stages"] for p in sorted((HERE / "results" / stage).glob("*.json"))]
    hashed = sum(1 for m in metas if m.get("trace_sha256"))
    noisy = sum(1 for m in metas if m["run"].get("noise"))
    now = hashlib.sha256((HERE / "cert_run.py").read_bytes()).hexdigest()
    p = subprocess.run(["git", "show", "5b9d75f:research/circuit/certification/cert_run.py"], capture_output=True, cwd=HERE)
    same = "not checked: the commit could not be read" if p.returncode else (
        "identical to the file of that commit" if hashlib.sha256(p.stdout).hexdigest() == now else "**different from the file of that commit**")
    return ["", "## Traces and reproduction", "",
            f"- **Extraction.** Every value of a run is extracted by `cert_run.py` when the run ends. The script was pushed in commit `5b9d75f`, before the first run. Its SHA-256 now is `{now}`: {same}.",
            "- **What is public.** For each run: one row per pulse with every quantity that enters a bound (`results/<stage>/<run>.csv`), and its metadata with the SHA-256 of the deck, of the binary, "
            "of the rows and of the compact trace (`results/<stage>/<run>.json`).",
            f"- **Traces.** The compact trace of a run holds the solver points around each pulse and each write window, as `PREDICTION.md` says. The traces are in the private repository "
            f"`HevisNico/kernel-R-circuit`, folder `07-certification-traces/`; {hashed} of the {len(metas)} runs with a result have the hash of their trace in their public metadata. "
            "That hash is the hash of the compact trace, not of the full solver output, which is not kept. Amendment 1 said that no trace would be kept; amendment 2 withdrew it before the runs of stages 2 and 3.",
            f"- **Reproduction.** Each run is made once. In the original campaign a run without noise replayed from its deck gave the same output byte for byte. The {noisy} runs with noise are not reproduced by their seed. "
            "Their extraction can be checked again only from the compact traces; their statistics can be reproduced by new runs, not their values."]


if __name__ == "__main__":
    {"calibrate": calibrate, "predict": predict, "certify": certify}[sys.argv[1]]()
