"""Campaign 5 (campaign 4's analyze.py at 093995b, adapted: the dates of the run in exact arithmetic, the rehearsal's
limits passed as a flag, no limits basis): the one analysis, after the last stage has ended on both machines. Run once.

  analyze.py OUT_DIR MEASURES_DIR_A MEASURES_DIR_B RUNS_DIR_A RUNS_DIR_B [EXTRACTIONS_DIR...]

Writes OUT_DIR/RESULTS.json and, for M8, OUT_DIR/M8.lean (the kernel checkers on the runs without noise of the
eligible instances under beta_0; each theorem asserts the Python mirror's verdict per checker, so that `check.sh
OUT_DIR/M8.lean` compiles only if the kernel agrees).

Order (PREDICTION.md, Rules of the analysis): (1) PREDICTED.json must be what predicted.py gives from the evidence of
the measures, or every claim is "not established"; (2) the regeneration check of the samples file of every noisy
run under the device model, before any word, output or score of a noisy run is read; (3) the claims, each with its
own verdict, and the declared comparisons. A run counts when the launcher recorded it complete and its own record
says that it reached its last date; any other is a missing run, never replaced.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "network-circuit"))
import c4                                               # noqa: E402
import measure                                          # noqa: E402
import net                                              # noqa: E402
import noisemodel                                       # noqa: E402
import plans4                                           # noqa: E402
import reads4                                           # noqa: E402
from c4 import dnf                                      # noqa: E402

TRUTH = lambda key: dict(a="A" in key and "B" in key, b="C" in key and "D" in key,
                         c=("A" in key and "B" in key) or ("C" in key and "D" in key))


import plan                                             # noqa: E402
import predicted as P                                   # noqa: E402

state_records, counts = P.state_records, P.counts


def rows_of(folder, needs, control):
    plan, slots = plans4.network(tuple(needs), control)
    ev = Path(folder) / "evidence"
    result = json.loads((ev / "result.json").read_text())
    tr = measure.Trace(ev / "trace.raw")
    return reads4.network_reads(tr, result, slots), result


def g_check(rows, noisy):
    """G on one run: every gated read moves no stored voltage by more than 0.01 mV (runs without noise) and raises
    no write and no write'."""
    bad = []
    for x in rows:
        for c, r in x["reads"].items():
            if not r["gated"]:
                continue
            for p, v in r["ports"].items():
                if v["writes"] or v["writes_prime"]:
                    bad.append(dict(slot=x["slot"], cell=c, port=p, writes=v["writes"], writes_prime=v["writes_prime"]))
                if not noisy and abs(v["move_mV"]) > c4.MOVE_BOUND_MV:
                    bad.append(dict(slot=x["slot"], cell=c, port=p, move_mV=v["move_mV"]))
    return bad


def h_check(rows, result):
    """H, observed and reported, never refuting: separation, late FIRE, routing, c's decoder, delivery. Campaign 5: the
    arithmetic on the instrument's dates is exact (each date at its exact binary value, the unit 1/50000 s), with
    campaign 4's tolerances kept as exact constants (1e-12 s for matching dates, 1e-9 unit for the bounds)."""
    F, ex = P.F, P.exact
    tol = F(1, 10 ** 9)
    key = lambda s: round(ex(s), 12)
    out = dict(min_separation_units={}, late_fires=0, arrivals_not_routed=0, skews_above_bound=0, c_fire_outside=0,
               undelivered=sum(1 for o in result["occurrences"] if not o["delivered"]), queued=len(result["still_queued_at_the_horizon"]))
    for c in c4.CELLS:
        d = sorted({key(o["date_s"]) for o in result["occurrences"] if o["delivered"] and o["cell"] == c})
        gaps = [(b - a) / TU_S for a, b in zip(d, d[1:]) if (b - a) / TU_S > 3]
        out["min_separation_units"][c] = float(min(gaps)) if gaps else None
    fires = {(f["cell"], key(f["date_s"])) for f in result["fires"]}
    for x in rows:
        for c, r in x["reads"].items():
            out["late_fires"] += r["late_fires"]
        r = x["reads"].get("c")
        if r:
            for a in r["arrivals"]:
                src = "a" if a["port"] == 1 else "b"
                ok = a["fire_date_s"] is not None and (src, key(a["fire_date_s"])) in fires and \
                    abs((ex(a["date_s"]) - ex(a["fire_date_s"])) / TU_S - F(3, 2)) <= F(1, 50) + tol
                out["arrivals_not_routed"] += not ok
            out["skews_above_bound"] += ex(r["skew_units"]) > F(11, 10) + tol
            if r["fire"] and r["fire_date_s"] < max(a["date_s"] for a in r["arrivals"]):
                out["c_fire_outside"] += 1
    return out


def word_claims(w, z, x):
    """L1, L2, T of one run without noise against the predictions of an eligible instance."""
    bad = []
    for port in ("a1", "a2", "b1", "b2", "c1", "c2"):
        want = z["words"][port[0] if port[0] != "c" else port]
        if w["words"][port] != want:
            bad.append(dict(port=port, word=w["words"][port], predicted=want))
    for key, want in z["tests"].items():
        got = w["tests"][key]
        for c in c4.CELLS:
            if got[c] != want[c]:
                bad.append(dict(pattern=key, cell=c, output=got[c], predicted=want[c]))
    return bad


def n_own(word, need):
    """N-own on one port-run: the word, without the slots where the port received no pulse, is need letters s
    followed only by F. None if the port received fewer than need pulses (the port-run does not count)."""
    w = word.replace("-", "")
    if len(w) < need:
        return None
    return w[:need] == "s" * need and set(w[need:]) <= {"F"}


def main(argv=None, here=HERE, predicted_path=None, rehearsal=False):
    argv = sys.argv[1:] if argv is None else argv
    print(c4.require_pinned())
    outdir, mA, mB, rA, rB = map(Path, argv[:5])
    extraction_dirs = [Path(x) for x in argv[5:]]
    raw = Path(predicted_path or here / "PREDICTED.json").read_text()
    predicted = json.loads(raw)
    before = plan.read_before_m(here / "BEFORE_M.md")
    res = dict(what="the one analysis of campaign 5; see analyze.py", interpreter=c4.interpreter(), missing=[], claims={}, comparisons={})
    recs = state_records(mA, mB, rA, rB)
    # (1) PREDICTED.json must be what the frozen prediction script gives from the evidence of the measures
    again, files = P.predictions(before, [mA, mB], extraction_dirs, rehearsal)
    same = json.dumps(again, indent=1, default=str) + "\n" == raw
    for path, text in files.items():
        same = same and (here.parent.parent / path).exists() and (here.parent.parent / path).read_text() == text
    res["predicted_is_reproduced"] = same
    # every run's own record against its collected files (record_is_the_waveform)
    import hashlib
    res["runs"] = {}
    for rid, rec in sorted(recs.items()):
        own = Path(rec["folder"]) / "record.json"
        if rec.get("status") != "complete" or not own.exists():
            res["runs"][rid] = dict(status=rec.get("status"), record_is_the_waveform=None)
            continue
        r = json.loads(own.read_text())
        base = Path(rec["folder"]) / ("evidence" if r["kind"] != "extract" else "")
        ok = all(hashlib.sha256((base / f).read_bytes()).hexdigest() == h for f, h in r["files"].items())
        res["runs"][rid] = dict(status=rec["status"], kind=r["kind"], wall_s=rec.get("wall_s"), record_is_the_waveform=ok)
    # (2) the regeneration check, before any word, output or score of a noisy run
    regen = dict(checked=0, dropped=[])
    import os
    import tempfile
    regen_dir = Path(tempfile.gettempdir()) / f"c4-regeneration-{os.getpid()}"     # never in the collected evidence; lowercase for ngspice
    noisy_ok = {}
    for r in predicted["network_runs"]:
        if r["noise"] == "none":
            continue
        rec = recs.get(r["id"])
        if not counts(rec):
            res["missing"].append(r["id"])
            continue
        own = json.loads((Path(rec["folder"]) / "record.json").read_text())
        if r["noise"] == "device":
            ex = json.loads((here.parent.parent / r["extraction"]["path"]).read_text())
            sha = noisemodel.regenerate_sha256(ex, c4.CELLS, own["noise"], regen_dir / r["id"].lower() / "nz")
            regen["checked"] += 1
            if sha != own["noise"]["samples_sha256"]:
                regen["dropped"].append(r["id"])
                continue
        noisy_ok[r["id"]] = rec
    regen["all_fail"] = bool(regen["checked"]) and len(regen["dropped"]) == regen["checked"]
    res["regeneration_check"] = regen
    outdir.mkdir(parents=True, exist_ok=True)
    if not same:
        res["claims"] = {k: "not established" for k in ("primary", "G", "N-out", "N-own", "N-word", "U", "S")}
        (outdir / "RESULTS.json").write_text(json.dumps(res, indent=1) + "\n")
        return res
    inst = {x["seed"]: x for x in predicted["instances"]}
    # (3) the claims
    primary, G, H, m2 = [], [], [], []
    quiet = {}
    for r in predicted["network_runs"]:
        if r["noise"] != "none" or r["control"] != "skew":
            continue
        rec = recs.get(r["id"])
        if not counts(rec):
            res["missing"].append(r["id"])
            continue
        rows, result = rows_of(rec["folder"], plan_needs(r), "skew")
        w = reads4.words(rows)
        quiet[r["seed"]] = (rows, w, rec)
        G += [dict(run=r["id"], **b) for b in g_check(rows, False)]
        H.append(dict(run=r["id"], **h_check(rows, result)))
        x = inst[r["seed"]]
        z = x.get("zero_error")
        if x.get("eligible"):
            primary += [dict(instance=r["seed"], **b) for b in word_claims(w, z, x)]
        elif z:
            m2.append(dict(instance=r["seed"], discrepancies=word_claims(w, z, x)))
    elig = [s for s, x in inst.items() if x.get("eligible")]
    counted = [s for s in elig if s in quiet]
    res["claims"]["primary"] = dict(instances=counted, discrepancies=primary,
                                    verdict="not established" if not counted else ("refuted" if primary else "held"))
    nout = {c: dict(output_runs=0, failures=[]) for c in c4.CELLS}
    nown = {p: dict(port_runs=0, not_counted=0, failures=[]) for p in ("a1", "a2", "b1", "b2", "c1", "c2")}
    nword = {p: dict(port_runs=0, failures=[]) for p in nown}
    m1, noisy_rows = [], {}
    for r in predicted["network_runs"]:
        if r["id"] not in noisy_ok:
            continue
        x = inst[r["seed"]]
        rows, result = rows_of(noisy_ok[r["id"]]["folder"], plan_needs(r), None)
        G += [dict(run=r["id"], **b) for b in g_check(rows, True)]
        w = reads4.words(rows)
        noisy_rows[r["id"]] = (rows, w, r)
        for c in c4.CELLS:
            ok = all(w["tests"][k][c] == TRUTH(k)[c] for k in w["tests"])
            if x["counts_N_out"][c]:
                nout[c]["output_runs"] += 1
                if not ok:
                    nout[c]["failures"].append(r["id"])
            else:
                m1.append(dict(run=r["id"], output=c, as_predicted=ok))
        n = x["needs"]
        for port, lp in x["learning_ports"].items():
            need = n[port[0]] if port[0] != "c" else n[port]
            want = x["zero_error"]["words"][port[0] if port[0] != "c" else port]
            if lp["own_room"]:
                v = n_own(w["words"][port], need)
                if v is None:
                    nown[port]["not_counted"] += 1
                else:
                    nown[port]["port_runs"] += 1
                    if not v:
                        nown[port]["failures"].append(r["id"])
            if lp["room_up_to"]:
                nword[port]["port_runs"] += 1
                if w["words"][port] != want:
                    nword[port]["failures"].append(r["id"])
    verdict = lambda runs, fails: "not established" if not runs else ("refuted" if fails else "held")
    res["claims"]["G"] = dict(failures=G, verdict="refuted" if G else "held")
    res["claims"]["N-out"] = {c: dict(v, verdict=verdict(v["output_runs"], v["failures"])) for c, v in nout.items()}
    tot = lambda d, k: sum(v[k] for v in d.values())
    res["claims"]["N-own"] = dict(ports=nown, verdict=verdict(tot(nown, "port_runs"), [f for v in nown.values() for f in v["failures"]]))
    res["claims"]["N-word"] = dict(ports=nword, verdict=verdict(tot(nword, "port_runs"), [f for v in nword.values() for f in v["failures"]]))
    if regen["all_fail"]:
        for k in ("N-out", "N-own", "N-word"):
            res["claims"][k] = "not established: every noisy run failed the regeneration check (a fault of the generator)"
    # controls
    ctl = [r for r in predicted["network_runs"] if r["control"] == "untrained"]
    U = None
    for r in ctl:
        rec = recs.get(r["id"])
        if counts(rec):
            rows, _ = rows_of(rec["folder"], plan_needs(r), "untrained")
            w = reads4.words(rows)
            U = [dict(pattern=k, cell=c) for k, v in w["tests"].items() for c in c4.CELLS if v[c]]
        else:
            res["missing"].append(r["id"])
    res["claims"]["U"] = dict(fires=U, verdict="not established" if U is None else ("refuted" if U else "held"))
    S = [dict(instance=s, pattern=k, cell=c) for s, (rows, w, _) in quiet.items() for k, v in w["skew"].items() for c in ("a", "b") if v[c]]
    res["claims"]["S"] = dict(fires=S, verdict="not established" if not quiet else ("refuted" if S else "held"))
    res["claims"]["H"] = H
    every = {f"{quiet_id(predicted, s)}": (rows, w) for s, (rows, w, _) in quiet.items()}
    every.update({k: (rows, w) for k, (rows, w, _) in noisy_rows.items()})
    m8, m8_lean = M8(inst, quiet, predicted)
    res["comparisons"] = dict(M1=m1, M2=m2, M3=M3(every), M4=M4(inst, quiet), M5={s: x.get("validation_residual_M5") for s, x in inst.items()},
                              M6=M6(every, noisy_rows), M7=M7(inst, noisy_rows, predicted["constants"]), M8=m8)
    (outdir / "RESULTS.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
    (outdir / "M8.lean").write_text(m8_lean)
    return res


def quiet_id(predicted, seed):
    return next(r["id"] for r in predicted["network_runs"] if r["seed"] == seed and r["scenario"] == "quiet")


# ------------------------------------------------------------------------------------- the declared comparisons

def M3(every):
    """Latencies of every FIRE (a, b: from the start of the read; c: from its first arrival) and the arrival skews on
    c, against the decision window (1.1 units), c's deadline (2.2 units) and the skew bound (1.1 units)."""
    out = {}
    for run, (rows, _) in every.items():
        lat = dict(a=[], b=[], c=[])
        skews = []
        for x in rows:
            for c, r in x["reads"].items():
                if r["fire"]:
                    lat[c].append(dict(slot=x["slot"], latency=r["latency"]))
                if c == "c":
                    skews.append(dict(slot=x["slot"], skew=r["skew_units"]))
        out[run] = dict(max_latency={c: max((v["latency"] for v in lat[c]), default=None) for c in lat},
                        latencies=lat, max_skew=max((v["skew"] for v in skews), default=None), skews=skews,
                        bounds=dict(window=c4.WINDOW, deadline_c=c4.DEADLINE_C, skew=c4.SKEW_C))
    return out


def M4(inst, quiet):
    """The nominal predictor (need 4 for each pair and line, the truth table) against the measured predictor and
    against the runs without noise: the letters and outputs where they differ."""
    nominal = dnf.zero_error(4, 4, 4, 4)
    out = {}
    for s, x in inst.items():
        if not x.get("measured") or not x.get("zero_error"):
            continue
        z = x["zero_error"]
        diff = lambda a, b: [dict(key=k, i=i, nominal=u, other=v) for k in a for i, (u, v) in enumerate(zip(a[k], b[k])) if u != v] + \
            [dict(key=k, length=(len(a[k]), len(b[k]))) for k in a if len(a[k]) != len(b[k])]
        row = dict(words_vs_measured=diff(nominal["words"], z["words"]),
                   tests_vs_measured=[dict(pattern=k, cell=c) for k in nominal["tests"] for c in c4.CELLS if nominal["tests"][k][c] != z["tests"][k][c]])
        if s in quiet:
            w = quiet[s][1]
            runw = dict(a=w["words"]["a1"], b=w["words"]["b1"], c1=w["words"]["c1"], c2=w["words"]["c2"])
            row["words_vs_run"] = diff(nominal["words"], runw)
            row["tests_vs_run"] = [dict(pattern=k, cell=c) for k in nominal["tests"] for c in c4.CELLS if nominal["tests"][k][c] != w["tests"][k][c]]
        out[str(s)] = row
    return out


def M6(every, noisy_rows):
    """Every write-signal crossing that is not a write' (narrower than 1 us), with its date in the cycle and its
    width; per port-run of the noisy runs, whether its word and its word' differ."""
    narrow = {}
    for run, (rows, _) in every.items():
        for x in rows:
            for c, r in x["reads"].items():
                for p, v in r["ports"].items():
                    for rise in v["rises"]:
                        if rise["width_s"] < c4.WRITE_PRIME_S:
                            narrow.setdefault(run, []).append(dict(slot=x["slot"], cell=c, port=p, date_in_cycle_s=rise["rise_s"] - r["start_s"],
                                                                   width_s=rise["width_s"]))
    differ = {}
    for run, (rows, w, _) in noisy_rows.items():
        wp = reads4.words(rows, prime=True)
        differ[run] = {p: dict(word=w["words"][p], word_prime=wp["words"][p]) for p in w["words"] if w["words"][p] != wp["words"][p]}
    return dict(narrow_crossings=narrow, word_and_word_prime_differ=differ)


def M7(inst, noisy_rows, const):
    """Per instance and learning port, over its noisy runs: the spread of the stored voltage at the end of its training
    (the mV before its first read after training: layer 2's first slot for a and b, the first test slot for c), and of
    the FIRE latency of its first F; against the model's sigma sqrt(w^2 + b^2 + n d^2) for the stored voltage. The
    model gives no latency spread; that one is reported alone."""
    import statistics
    by = {}
    for run, (rows, w, r) in noisy_rows.items():
        for c, ports, stage in (("a", (1, 2), "layer 2"), ("b", (1, 2), "layer 2"), ("c", (1, 2), "test")):
            x = next((x for x in rows if x["stage"] == stage and c in x["reads"]), None)
            first_f = {}
            for y in rows:
                rr = y["reads"].get(c)
                if rr and rr["fire"] and ((c != "c" and y["stage"] == "layer 1") or (c == "c" and y["stage"] == "layer 2")):
                    p = 1 if c != "c" else dnf.LINES[y["line"]][1]
                    for q in ((1, 2) if c != "c" else (p,)):
                        first_f.setdefault(q, rr["latency"])
            for p in ports:
                key = (r["seed"], f"{c}{p}")
                d = by.setdefault(key, dict(u_end_mV=[], first_F_latency=[]))
                if x:
                    d["u_end_mV"].append(x["reads"][c]["ports"][str(p)]["u_before_mV"])
                if p in first_f:
                    d["first_F_latency"].append(first_f[p])
    out = {}
    for (seed, port), d in sorted(by.items()):
        x = inst[seed]
        n = x["needs"][port[0]] if port[0] != "c" else x["needs"][port]
        sd = lambda v: statistics.pstdev(v) if len(v) > 1 else None
        out.setdefault(str(seed), {})[port] = dict(runs=len(d["u_end_mV"]), u_end_mV=d["u_end_mV"], u_end_spread_mV=sd(d["u_end_mV"]),
                                                   model_sigma_mV=(const["within_mV"] ** 2 + const["between_mV"] ** 2 + n * const["per_dose_mV"] ** 2) ** 0.5,
                                                   first_F_latency=d["first_F_latency"], first_F_latency_spread=sd(d["first_F_latency"]))
    return out


def M8(inst, quiet, predicted):
    """The kernel checkers on the runs without noise of the eligible instances, under beta_0, with the observation of
    the run (dates of the run's record; scores: the run's peak of q on the observed mask, for a read that fires the
    larger of its peak before the FIRE crossing and theta; the calibration scores of the predicted observation on the
    other submasks). Python mirror (cases.Mirror) per checker, and the Lean file asserting it. Also the declared
    assumption on c (PREDICTION.md, M8)."""
    import cases
    import gate4
    out, lean = {}, gate4.header("analyze.py, M8")
    for s, (rows, w, rec) in sorted(quiet.items()):
        x = inst[s]
        if not x.get("eligible"):
            continue
        o = run_observation(rows, x, Path(rec["folder"]))
        y = dict(x, observation=o)
        conds = cases.conditions(y, 0)
        v = cases.per_checker(conds)
        out[str(s)] = dict(per_checker=v, failing=[dict(checker=a, kind=b, where=c) for a, b, c, ok in conds if not ok],
                           note="for a firing read the score max(peak, theta) decides the FIRE bit by construction, and the guard stops the "
                                "charge near theta: the residual and threshold parts of the check on firing reads are nearly empty",
                           assumption_on_c=assumption_on_c(rows, x))
        tag = f"run_{s}"
        cn, tn = f"cascade_{tag}", f"trace_{tag}"
        lean += gate4.cascade_lean(cn, y, 0) + "\n" + gate4.trace_lean(tn, cn, o) + "\n"
        for th, stmt, c in ((f"valid_{tag}", f"checkCascadeValid {cn}", cases.VALID),
                            (f"separation_{tag}", f"checkTrainingSeparation {cn} left right {tn}.observations", cases.SEP),
                            (f"calibration_{tag}", f"checkCascadeCalibrationOneSided {cn} left right {tn}.observations {tn}.scoreAt", cases.CAL)):
            lean += f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem {th} : {stmt} = {'true' if v[c] else 'false'} := by decide +kernel\n\n"
    if not out:
        lean += "theorem no_eligible_instance : True := trivial\n\n"
    return out, lean + "end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4\n"


T0_S, TU_S = P.F(1, 10000), P.F(1, 50000)     # the calendar's origin (100 us) and the time unit (20 us), exactly


def units(date_s):
    """A date of the run in time units from the start of the calendar, as a rational rounded to 0.0001 unit, ties to
    even. Campaign 5: the date is taken at its exact binary value and the arithmetic is exact (campaign 4 subtracted
    100e-6 and divided by the float 20e-6 in binary floats)."""
    return P.q((P.exact(date_s) - T0_S) / TU_S)


def run_observation(rows, x, folder):
    """The observation of a run without noise in the serialized format of the predicted observation."""
    import measure
    tr = measure.Trace(folder / "evidence" / "trace.raw")
    result = json.loads((folder / "evidence" / "result.json").read_text())
    delivered = [o for o in result["occurrences"] if o["delivered"]]
    po = x["observation"]
    score = lambda r: P.zint(r["q_peak"]) if not r["fire"] else max(P.zint(r["q_peak_before_fire"]), P.THETA)
    INPUT_OF = {v: k for k, v in dnf.INPUTS.items()}

    def layer1(x_, c, own_target=False):
        """A read of a or b. Its input is every active external input of the slot (amendment 1, point 4), except in
        firstTrain, where it is the cell's target, as CascadeCalibrationOneSided checks it."""
        lo, hi = reads4.c4_at(x_["date"]) - 1e-9, reads4.c4_at(x_["date"] + dnf.SLOT) - 1e-9
        arr = {INPUT_OF[(o["cell"], o["port"])]: units(o["date_s"]) for o in delivered if lo <= o["date_s"] < hi and o["cell"] in ("a", "b")
               and (not own_target or o["cell"] == c)}
        arrivals = [None if k not in arr else str(arr[k]) for k in "ABCD"]
        r = x_["reads"].get(c)
        if r is None:   # the cell takes no pulse in this slot: its empty read on the slot's inputs (amendment 1, point 4)
            here = [o["date_s"] for o in delivered if lo <= o["date_s"] < hi and o["cell"] in ("a", "b")]
            start = min(here) if here else net.snap(reads4.c4_at(x_["date"]))     # a slot with no pulse: its snapped date
            fires = tr.crossings(f"v(x{c}.p)", lo, hi)
            peak = reads4.q_peak(tr, c, start, start + 3 * reads4.TU)
            value = P.zint(peak) if not fires else max(P.zint(reads4.q_peak(tr, c, start, fires[0])), P.THETA)
            return dict(start=str(units(start)), arrivals=arrivals, emissions=[str(units(f)) for f in fires], value=value)
        return dict(start=str(units(r["start_s"])), arrivals=arrivals, emissions=[str(units(f)) for f in r["slot_fires_s"]], value=score(r))

    def layer2(x_):
        r = x_["reads"].get("c")
        lo, hi = reads4.c4_at(x_["date"]) - 1e-9, reads4.c4_at(x_["date"] + dnf.SLOT) - 1e-9
        if r is None:
            start = net.snap(reads4.c4_at(x_["date"])) + 1.5 * reads4.TU      # no arrival: the slot's date plus 3/2, for the probe window
            fires = tr.crossings("v(xc.p)", lo, hi)
            return dict(start=str(units(net.snap(reads4.c4_at(x_["date"]))) + P.F(3, 2)), arrivals=[None, None], emissions=[str(units(f)) for f in fires],
                        value=P.zint(reads4.q_peak(tr, "c", start, start + 3 * reads4.TU)))
        arr = {a["port"]: units(a["date_s"]) for a in r["arrivals"]}
        return dict(start=str(units(r["start_s"])), arrivals=[str(arr[p]) if p in arr else None for p in (1, 2)],
                    emissions=[str(units(f)) for f in r["slot_fires_s"]], value=score(r))
    o = dict(firstTrain=[], teach=[], secondTrain=[], firstTest={}, secondTest={}, scores={})
    for x_ in rows:
        if x_["stage"] == "layer 1":
            o["firstTrain"].append([layer1(x_, c, own_target=True) for c in ("a", "b")])
        elif x_["stage"] == "layer 2":
            o["teach"].append([layer1(x_, c) for c in ("a", "b")])
            o["secondTrain"].append(layer2(x_))
        elif x_["stage"] == "test":
            k = "".join(sorted(x_["pattern"])) or "-"
            o["firstTest"][k] = [layer1(x_, c) for c in ("a", "b")]
            o["secondTest"][k] = layer2(x_)
            sc = dict(po["scores"][k])
            mask = "".join(str(p) for p, v in zip((1, 2), o["secondTest"][k]["arrivals"]) if v is not None) or "-"
            sc[mask] = o["secondTest"][k]["value"]
            o["scores"][k] = sc
    return o


def assumption_on_c(rows, x):
    """M8, the declared assumption on c: for n1 != n2, the run's FIRE latency of each line alone at test against the
    guard-on calibration latency of that line at stage n_j (kept in the instance's observation), and the run's peak q
    of the empty test read of c against the calibration at min(n1, n2) and max(n1, n2) (the predicted scores)."""
    n1, n2 = x["needs"]["c1"], x["needs"]["c2"]
    if n1 == n2:
        return None
    t = {("".join(sorted(y["pattern"])) or "-"): y for y in rows if y["stage"] == "test"}
    po = x["observation"]["secondTest"]
    lat = lambda k: (lambda r: r["latency"] if r and r["fire"] else None)(t[k]["reads"].get("c"))
    pred = lambda k: (float(P.exact(po[k]["emissions"][0]) - P.exact(po[k]["start"])) if po[k]["emissions"] else None)
    return dict(line_a_alone=dict(run=lat("AB"), calibration=pred("AB")), line_b_alone=dict(run=lat("CD"), calibration=pred("CD")),
                empty=dict(run_q_peak=None if t["-"]["reads"].get("c") is None else t["-"]["reads"]["c"]["q_peak"],
                           calibration_scores=x["observation"]["scores"]["-"]))


def plan_needs(r):
    return tuple(7 if v is None else v for v in r["needs"])


if __name__ == "__main__":
    main()
