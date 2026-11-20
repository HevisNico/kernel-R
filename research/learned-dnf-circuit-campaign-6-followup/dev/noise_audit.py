"""Noise audit of campaign 6, attempt c1: the pushed quiet and noisy network runs, read again. No simulation is run.

  noise_audit.py verify  EV_DIR OUT_DIR             reassembles split traces (PARTS.json) and checks every file against
                                                    COLLECTED.json and PARTS.json
  noise_audit.py reads   REPO EV_DIR OUT_DIR        the reads of every run, by the repository's own readers
                                                    (campaign 5's plans4.network and reads4.network_reads,
                                                    network-circuit's measure.Trace), written to OUT_DIR/reads/
  noise_audit.py analyze REPO EV_DIR OUT_DIR PREDICTED.json RESULTS.json
                                                    the noisy-minus-quiet differences and their summary
 noise_audit.py verify-m1 EV_DIR OUT_DIR           the same checks on the two folders of stage M1 (calibration decks)
  noise_audit.py m5 REPO EV_DIR OUT_DIR PREDICTED.json
                                                    b and w in mV by campaign 3's definition: the FIRE latencies of
                                                    `constants`, divided by the slope taken on the M1 guard-on decks
  noise_audit.py constants OUT_DIR                  the same reads cut as campaign 3 cut its noise: an offset per run and
                                                    a scatter within the run (from PER_READ.json, AUDIT.json and reads/)
  noise_audit.py windows PREDICTIONS_BATCH.json OUT_DIR
                                                    on the development batch's records only: the cells that would have
                                                    room for a given r

EV_DIR holds <stage>/<machine>/ as on the evidence branches (Q, N1, N2, N3; a, b). REPO is a checkout of
research/learned-dnf-circuit-campaign-6-impl at ecfcd1c1. Nothing is written inside REPO or EV_DIR except the
reassembled trace.raw files next to their parts (verify).

The audit measures noise. It recounts no claim of campaign 6 and applies no rule of room to its instances.
"""
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

STAGES = ("Q", "N1", "N2", "N3")
MACHINES = ("a", "b")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 22), b""):
            h.update(block)
    return h.hexdigest()


def stage_dirs(ev, stages=STAGES):
    return [(s, m, Path(ev) / s / m) for s in stages for m in MACHINES]


# --------------------------------------------------------------------------------------------------------- verify

def verify(ev, out, stages=STAGES, report_name="VERIFY.json"):
    report = dict(folders=[], files_checked=0, files_bad=[], parts_checked=0, parts_bad=[], reassembled=[],
                  not_in_collected=[])
    for s, m, d in stage_dirs(ev, stages):
        parts_file = d / "PARTS.json"
        split = json.loads(parts_file.read_text())["files"] if parts_file.exists() else {}
        for rel, spec in split.items():
            target = d / rel
            for p in spec["parts"]:
                f = d / p["path"]
                ok = f.exists() and f.stat().st_size == p["bytes"] and sha(f) == p["sha256"]
                report["parts_checked"] += 1
                if not ok:
                    report["parts_bad"].append(str(f))
            if not target.exists():
                with open(target, "wb") as w:
                    for p in spec["parts"]:
                        with open(d / p["path"], "rb") as r:
                            for block in iter(lambda: r.read(1 << 22), b""):
                                w.write(block)
            ok = target.stat().st_size == spec["bytes"] and sha(target) == spec["sha256"]
            report["reassembled"].append(dict(file=f"{s}/{m}/{rel}", bytes=spec["bytes"], sha256=spec["sha256"], ok=ok))
        collected = json.loads((d / "COLLECTED.json").read_text())
        listed = set()
        for x in collected["files"]:
            f = d / x["path"]
            listed.add(x["path"])
            ok = f.exists() and f.stat().st_size == x["bytes"] and sha(f) == x["sha256"]
            report["files_checked"] += 1
            if not ok:
                report["files_bad"].append(f"{s}/{m}/{x['path']}")
        runs = sorted(p.name for p in d.iterdir() if p.is_dir())
        for run in runs:                                    # the run's own record against its files
            rec = json.loads((d / run / "record.json").read_text())
            for name, h in rec["files"].items():
                report["files_checked"] += 1
                if sha(d / run / "evidence" / name) != h:
                    report["files_bad"].append(f"{s}/{m}/{run}/evidence/{name} (record.json)")
            for f in (d / run).rglob("*"):
                rel = str(f.relative_to(d))
                if f.is_file() and rel not in listed and ".part-" not in rel:
                    report["not_in_collected"].append(f"{s}/{m}/{rel}")
        report["folders"].append(dict(stage=s, machine=m, runs=runs, collected_files=len(collected["files"]),
                                      split_files=len(split)))
    Path(out).mkdir(parents=True, exist_ok=True)
    (Path(out) / report_name).write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: (v if not isinstance(v, list) else len(v)) for k, v in report.items()}))
    print("bad:", report["files_bad"], report["parts_bad"], [x for x in report["reassembled"] if not x["ok"]])
    return report


# ---------------------------------------------------------------------------------------------------------- reads

def repo_paths(repo):
    r = Path(repo) / "research"
    for p in (r / "learned-dnf-circuit-campaign-5", r / "network-circuit", r / "learned-dnf-circuit", r / "circuit"):
        sys.path.insert(0, str(p))


def runs_of(ev):
    out = []
    for s, m, d in stage_dirs(ev):
        for run in sorted(p for p in d.iterdir() if p.is_dir()):
            rec = json.loads((run / "record.json").read_text())
            out.append(dict(stage=s, machine=m, id=rec["id"], seed=rec["seed"], needs=rec["needs"], control=rec["control"],
                            noise=rec["noise"]["model"] if isinstance(rec.get("noise"), dict) else rec.get("noise"),
                            folder=str(run)))
    return out


def reads(repo, ev, out):
    repo_paths(repo)
    import measure
    import plans4
    import reads4
    od = Path(out) / "reads"
    od.mkdir(parents=True, exist_ok=True)
    index = []
    for r in runs_of(ev):
        plan, slots = plans4.network(tuple(r["needs"]), r["control"])
        evd = Path(r["folder"]) / "evidence"
        result = json.loads((evd / "result.json").read_text())
        tr = measure.Trace(evd / "trace.raw")
        rows = reads4.network_reads(tr, result, slots)
        w = reads4.words(rows)
        (od / f"{r['id']}.json").write_text(json.dumps(dict(run=r, rows=rows, words=w), indent=1) + "\n")
        index.append(dict(r, slots=len(rows), words=w["words"]))
        print(r["id"], r["control"], r["noise"], len(rows), w["words"], flush=True)
    (Path(out) / "RUNS.json").write_text(json.dumps(index, indent=1) + "\n")


# -------------------------------------------------------------------------------------------------------- analyze

def sd(xs):
    return statistics.pstdev(xs) if len(xs) > 1 else None


def rms(xs):
    return math.sqrt(sum(x * x for x in xs) / len(xs)) if xs else None


def summary(xs):
    xs = [x for x in xs if x is not None]
    if not xs:
        return dict(n=0)
    return dict(n=len(xs), mean=statistics.fmean(xs), sd=sd(xs), rms=rms(xs), max_abs=max(abs(x) for x in xs))


def analyze(repo, ev, out, predicted_path, results_path):
    out = Path(out)
    runs = json.loads((out / "RUNS.json").read_text())
    data = {r["id"]: json.loads((out / "reads" / f"{r['id']}.json").read_text()) for r in runs}
    predicted = json.loads(Path(predicted_path).read_text())
    results = json.loads(Path(results_path).read_text())
    from fractions import Fraction as F
    inst = {x["seed"]: x for x in predicted["instances"] if "needs" in x and x.get("needs")}
    const = predicted["constants"]
    sigma_model = lambda n: math.sqrt(const["within_mV"] ** 2 + const["between_mV"] ** 2 + n * const["per_dose_mV"] ** 2)

    # 0. the readers under this interpreter reproduce the pushed analysis: M7's u_end_mV, M3's latencies
    check = dict(M7_max_abs_diff_mV=0.0, M7_values=0, M3_max_abs_diff_units=0.0, M3_values=0)
    for seed_s, ports in results["comparisons"]["M7"].items():
        for port, v in ports.items():
            c, p = port[0], port[1]
            mine = []
            for n in (1, 2, 3):
                rows = data[f"{seed_s}-n{n}"]["rows"]
                stage = "layer 2" if c in "ab" else "test"
                x = next(x for x in rows if x["stage"] == stage and c in x["reads"])
                mine.append(x["reads"][c]["ports"][p]["u_before_mV"])
            for a, b in zip(mine, v["u_end_mV"]):
                check["M7_max_abs_diff_mV"] = max(check["M7_max_abs_diff_mV"], abs(a - b))
                check["M7_values"] += 1
    for run_id, v in results["comparisons"]["M3"].items():
        rows = {x["slot"]: x for x in data[run_id]["rows"]}
        for c, lst in v["latencies"].items():
            for e in lst:
                mine = rows[e["slot"]]["reads"][c]["latency"]
                check["M3_max_abs_diff_units"] = max(check["M3_max_abs_diff_units"], abs(mine - e["latency"]))
                check["M3_values"] += 1

    per_read, words_equal = [], {}
    ladders = {}
    for seed, x in sorted(inst.items()):
        quiet = data.get(f"{seed}-quiet")
        if quiet is None:
            continue
        D = {k: float(F(v)) for k, v in x["D_mV"].items()}                 # the measured mean dose of each port, mV
        need = x["needs"]
        qrows = {r["slot"]: r for r in quiet["rows"]}
        # the quiet run's own ladder: q_peak of the silent training reads, per read kind, by round
        lad = dict(a=[], b=[], c1=[], c2=[])
        for r in quiet["rows"]:
            if r["stage"] == "layer 1":
                for c in "ab":
                    rd = r["reads"][c]
                    lad[c].append(dict(fire=rd["fire"], q=rd["q_peak"], qbf=rd["q_peak_before_fire"],
                                       u=[rd["ports"][p]["u_before_mV"] for p in "12"]))
            elif r["stage"] == "layer 2":
                p = 1 if r["line"] == "a" else 2
                rd = r["reads"]["c"]
                lad[f"c{p}"].append(dict(fire=rd["fire"], q=rd["q_peak"], qbf=rd["q_peak_before_fire"], u=[rd["ports"][str(p)]["u_before_mV"]]))
        step = {}
        for k, rows_k in lad.items():
            silent = [e for e in rows_k if not e["fire"]]
            steps = [silent[i + 1]["q"] - silent[i]["q"] for i in range(len(silent) - 1)]
            du = [[silent[i]["u"][j] - silent[i + 1]["u"][j] for j in range(len(silent[i]["u"]))] for i in range(len(silent) - 1)]
            step[k] = dict(silent_reads=len(silent), q_of_silent=[e["q"] for e in silent], q_steps=steps,
                           last_q_step=steps[-1] if steps else None, u_moves_mV=du,
                           first_fire_qbf=next((e["qbf"] for e in rows_k if e["fire"]), None))
        ladders[seed] = step
        for n in (1, 2, 3):
            noisy = data.get(f"{seed}-n{n}")
            if noisy is None:
                continue
            words_equal[f"{seed}-n{n}"] = {k: noisy["words"]["words"][k] == quiet["words"]["words"][k][:len(noisy["words"]["words"][k])]
                                            for k in noisy["words"]["words"]}
            tests_equal = noisy["words"]["tests"] == quiet["words"]["tests"]
            words_equal[f"{seed}-n{n}"]["tests"] = tests_equal
            seen = dict(a=0, b=0, c1=0, c2=0)
            for r in noisy["rows"]:
                q = qrows.get(r["slot"])
                if q is None or q["stage"] != r["stage"] or q.get("pattern") != r.get("pattern") or q.get("line") != r.get("line"):
                    raise SystemExit(f"slot mismatch {seed}-n{n} slot {r['slot']}")
                for c, rd in r["reads"].items():
                    qd = q["reads"].get(c)
                    if qd is None:
                        continue
                    k = None                                         # the read's index among the training reads of its kind
                    if r["stage"] == "layer 1" and c in "ab":
                        k = seen[c]
                        seen[c] += 1
                    elif r["stage"] == "layer 2" and c == "c":
                        key = "c1" if r["line"] == "a" else "c2"
                        k = seen[key]
                        seen[key] += 1
                    if rd["fire"] != qd["fire"]:
                        per_read.append(dict(run=f"{seed}-n{n}", seed=seed, round=n, slot=r["slot"], stage=r["stage"], cell=c, fire_differs=True,
                                             fire_noisy=rd["fire"], fire_quiet=qd["fire"], k=k,
                                             q_peak_noisy=rd["q_peak"], q_peak_quiet=qd["q_peak"],
                                             q_before_fire_noisy=rd["q_peak_before_fire"], q_before_fire_quiet=qd["q_peak_before_fire"],
                                             du_mV={p: rd["ports"][p]["u_before_mV"] - qd["ports"][p]["u_before_mV"] for p in "12"}))
                        continue
                    e = dict(run=f"{seed}-n{n}", seed=seed, round=n, slot=r["slot"], stage=r["stage"], cell=c, fire=rd["fire"], gated=rd["gated"],
                             pattern=r.get("pattern"), line=r.get("line"), fire_differs=False, k=k,
                             dq_peak=rd["q_peak"] - qd["q_peak"],
                             dq_before_fire=(rd["q_peak_before_fire"] - qd["q_peak_before_fire"]) if rd["fire"] else None,
                             dlatency=(rd["latency"] - qd["latency"]) if rd["fire"] else None,
                             writes={p: (rd["ports"][p]["writes"], qd["ports"][p]["writes"]) for p in "12"},
                             du_mV={p: rd["ports"][p]["u_before_mV"] - qd["ports"][p]["u_before_mV"] for p in "12"},
                             dmove_mV={p: rd["ports"][p]["move_mV"] - qd["ports"][p]["move_mV"] for p in "12"},
                             move_quiet_mV={p: qd["ports"][p]["move_mV"] for p in "12"})
                    e["du_doses"] = {p: e["du_mV"][p] / D[f"{c}{p}"] for p in "12"}
                    if c == "c":
                        e["arrived"] = sorted({a["port"] for a in rd["arrivals"]})
                    per_read.append(e)

    ok = [e for e in per_read if not e["fire_differs"]]
    flips = [e for e in per_read if e["fire_differs"]]

    # 1. the stored voltage: noisy minus quiet, per port, in mV and in doses of that port
    stored = {}
    for seed in sorted(inst):
        for c in "abc":
            for p in "12":
                port = f"{c}{p}"
                mine = [e for e in ok if e["seed"] == seed and e["cell"] == c]
                if not mine:
                    continue
                D = float(F(inst[seed]["D_mV"][port]))
                by_run = {}
                for e in mine:
                    by_run.setdefault(e["run"], []).append(e["du_mV"][p])
                after = {}                                           # reads after the port's last write of the run
                for run, _ in by_run.items():
                    es = [e for e in mine if e["run"] == run]
                    last = max((e["slot"] for e in es if e["writes"][p][0] > 0), default=-1)
                    after[run] = [e["du_mV"][p] for e in es if e["slot"] > last]
                within = [v - statistics.fmean(vs) for vs in after.values() for v in vs]
                stored[f"{seed}-{port}"] = dict(
                    dose_mV=D, all_reads_mV=summary([v for vs in by_run.values() for v in vs]),
                    after_last_write=dict(run_means_mV={r: statistics.fmean(v) for r, v in after.items() if v},
                                          within_run_sd_mV=sd(within) if len(within) > 1 else None, n=len(within)),
                    model_sigma_mV=sigma_model(inst[seed]["needs"][c if c != "c" else f"c{p}"]))

    # 2. the dose moves: noisy minus quiet, on the reads where both runs write that port once
    doses = []
    for e in ok:
        for p in "12":
            if e["writes"][p] == (1, 1):
                doses.append(dict(run=e["run"], seed=e["seed"], cell=e["cell"], port=p, slot=e["slot"], dmove_mV=e["dmove_mV"][p],
                                  move_quiet_mV=e["move_quiet_mV"][p]))

    # 3. the FIRE level: q at the FIRE crossing, noisy minus quiet, on the reads that fire in both runs
    trip = {}
    for seed in sorted(inst):
        for c in "abc":
            es = [e for e in ok if e["seed"] == seed and e["cell"] == c and e["fire"]]
            if not es:
                continue
            kinds = {}
            for e in es:
                kind = "pair" if c in "ab" else ("both lines" if e["arrived"] == [1, 2] else f"line {e['arrived'][0]}")
                kinds.setdefault(kind, []).append(e)
            for kind, ks in kinds.items():
                by_run = {}
                for e in ks:
                    by_run.setdefault(e["run"], []).append(e["dq_before_fire"])
                within = [v - statistics.fmean(vs) for vs in by_run.values() for v in vs]
                key = dict(pair=c, **{"line 1": "c1", "line 2": "c2"}).get(kind)
                st = ladders[seed][key]["last_q_step"] if key else None
                trip[f"{seed}-{c}-{kind}"] = dict(
                    n=len(ks), all=summary([e["dq_before_fire"] for e in ks]), run_means={r: statistics.fmean(v) for r, v in by_run.items()},
                    within_run_sd=sd(within), latency=summary([e["dlatency"] for e in ks]),
                    last_silent_q_step_of_quiet_run=st,
                    in_steps=None if not st else dict(sd_all=sd([e["dq_before_fire"] for e in ks]) / st,
                                                      rms_all=rms([e["dq_before_fire"] for e in ks]) / st,
                                                      max_abs=max(abs(e["dq_before_fire"]) for e in ks) / st,
                                                      within_run_sd=(sd(within) or 0.0) / st))

    # 4. the score of silent reads: q_peak noisy minus quiet, on the training reads silent in both runs, in steps
    silent, silent_pooled, silent_rest = {}, dict(pair=[], line=[]), dict(pair=[], line=[])
    for seed in sorted(inst):
        for key, c in (("a", "a"), ("b", "b"), ("c1", "c"), ("c2", "c")):
            st = ladders[seed][key]["last_q_step"]
            if key in "ab":
                es = [e for e in ok if e["seed"] == seed and e["cell"] == c and e["stage"] == "layer 1" and not e["fire"]]
                dw = lambda e: -(e["du_doses"]["1"] + e["du_doses"]["2"]) / 2
            else:
                line = "a" if key == "c1" else "b"
                es = [e for e in ok if e["seed"] == seed and e["cell"] == "c" and e["stage"] == "layer 2" and e["line"] == line and not e["fire"]]
                dw = lambda e, p=key[1]: -e["du_doses"][p]
            if not es or not st:
                continue
            steps = ladders[seed][key]["q_steps"]
            local = lambda e: steps[e["k"]] if e["k"] < len(steps) else steps[-1]     # the quiet run's step from this stage to the next
            vals = [dict(dq=e["dq_peak"] / local(e), state=dw(e)) for e in es]
            silent[f"{seed}-{key}"] = dict(n=len(es), q_steps_of_quiet_run=steps,
                                           dq_in_steps=summary([v["dq"] for v in vals]),
                                           stored_voltage_in_steps=summary([v["state"] for v in vals]),
                                           dq_minus_stored_in_steps=summary([v["dq"] - v["state"] for v in vals]))
            silent_pooled["pair" if key in "ab" else "line"] += [v["dq"] for v in vals]
            silent_rest["pair" if key in "ab" else "line"] += [v["dq"] - v["state"] for v in vals]

    # 5. the margin of the firing reads at the trained state, in steps of the read's own training path:
    #    (move of the state toward FIRE, from the stored voltages) minus (move of the FIRE level, from q at the crossing)
    margin = {}
    pooled = dict(pair=[], line=[])
    for seed in sorted(inst):
        for key, c in (("a", "a"), ("b", "b"), ("c1", "c"), ("c2", "c")):
            st = ladders[seed][key]["last_q_step"]
            if not st:
                continue
            if key in "ab":
                es = [e for e in ok if e["seed"] == seed and e["cell"] == c and e["fire"]]
                dw = lambda e: -(e["du_doses"]["1"] + e["du_doses"]["2"]) / 2
            else:
                p = int(key[1])
                es = [e for e in ok if e["seed"] == seed and e["cell"] == "c" and e["fire"] and e["arrived"] == [p]]
                dw = lambda e, p=str(p): -e["du_doses"][p]
            if not es:
                continue
            vals = [dict(run=e["run"], slot=e["slot"], state=dw(e), level=e["dq_before_fire"] / st, margin=dw(e) - e["dq_before_fire"] / st) for e in es]
            by_run = {}
            for v in vals:
                by_run.setdefault(v["run"], []).append(v["margin"])
            margin[f"{seed}-{key}"] = dict(n=len(vals), state=summary([v["state"] for v in vals]), level=summary([v["level"] for v in vals]),
                                           margin=summary([v["margin"] for v in vals]),
                                           run_means={r: statistics.fmean(v) for r, v in by_run.items()})
            pooled["pair" if key in "ab" else "line"] += [v["margin"] for v in vals]

    pooled_all = pooled["pair"] + pooled["line"]
    level_pooled = dict(pair=[], line=[])
    for seed in sorted(inst):
        for key, c in (("a", "a"), ("b", "b"), ("c1", "c"), ("c2", "c")):
            st = ladders[seed][key]["last_q_step"]
            if key in "ab":
                es = [e for e in ok if e["seed"] == seed and e["cell"] == c and e["fire"]]
            else:
                es = [e for e in ok if e["seed"] == seed and e["cell"] == "c" and e["fire"] and e["arrived"] == [int(key[1])]]
            level_pooled["pair" if key in "ab" else "line"] += [e["dq_before_fire"] / st for e in es]

    # 6. the stored voltage before the first write of each port in each run, and after its last
    first, last_, gained = [], [], []
    for seed in sorted(inst):
        for c in "abc":
            for p in "12":
                for n in (1, 2, 3):
                    es = sorted((e for e in ok if e["run"] == f"{seed}-n{n}" and e["cell"] == c), key=lambda e: e["slot"])
                    if not es:
                        continue
                    D = float(F(inst[seed]["D_mV"][f"{c}{p}"]))
                    w = max((e["slot"] for e in es if e["writes"][p][0] > 0), default=-1)
                    after = [e["du_mV"][p] for e in es if e["slot"] > w]
                    if not after:
                        continue
                    first.append(es[0]["du_mV"][p])
                    last_.append(statistics.fmean(after))
                    gained.append(statistics.fmean(after) - es[0]["du_mV"][p])
    offsets = dict(port_runs=len(first), before_first_read_mV=summary(first), after_last_write_mV=summary(last_),
                   gained_during_training_mV=summary(gained), model=const)

    def combined(kind):
        s, l = silent_pooled[kind], level_pooled[kind]
        ss, sl = sd(s), sd(l)
        tot = math.sqrt(ss * ss + sl * sl)
        return dict(score_of_silent_training_reads=summary(s), score_beyond_stored_voltage=summary(silent_rest[kind]),
                    fire_level=summary(l), sigma_total_steps=tot, three_sigma_steps=3 * tot)
    combo = {k: combined(k) for k in ("pair", "line")}
    s_all, l_all = silent_pooled["pair"] + silent_pooled["line"], level_pooled["pair"] + level_pooled["line"]
    tot = math.sqrt(sd(s_all) ** 2 + sd(l_all) ** 2)
    combo["all"] = dict(score_of_silent_training_reads=summary(s_all), fire_level=summary(l_all), sigma_total_steps=tot, three_sigma_steps=3 * tot)
    # 7. a consistency check of the measured sigma: the number of FIRE bits expected to differ from the quiet run, if
    #    each read's margin (from the pushed prediction record, question_2: the crossing's place in its step) moved by
    #    an independent Gaussian of the measured sigma; against the number seen
    phi = lambda z: 0.5 * math.erfc(z / math.sqrt(2))
    expect = dict(reads=0, expected=0.0, by_kind=[])
    for seed, x in sorted(inst.items()):
        for key, c in (("a", "a"), ("b", "b"), ("c1", "c"), ("c2", "c")):
            sig = combo["pair" if key in "ab" else "line"]["sigma_total_steps"]
            below, above = float(F(x["question_2"][key]["below_stages"])), float(F(x["question_2"][key]["above_stages"]))
            n_need = x["needs"][key]
            if key in "ab":
                tr = [e for e in per_read if e["seed"] == seed and e["cell"] == c and e["stage"] == "layer 1"]
                fr = [e for e in per_read if e["seed"] == seed and e["cell"] == c and e["stage"] != "layer 1" and not e.get("fire_differs") and e["fire"]]
            else:
                line = "a" if key == "c1" else "b"
                tr = [e for e in per_read if e["seed"] == seed and e["cell"] == "c" and e["stage"] == "layer 2" and e.get("line", line) == line and e["k"] is not None
                      and (e.get("line") == line or e.get("fire_differs"))]
                fr = [e for e in per_read if e["seed"] == seed and e["cell"] == "c" and e["stage"] == "test" and not e.get("fire_differs") and e["fire"] and e["arrived"] == [int(key[1])]]
            ex = 0.0
            for e in tr:                                     # training reads: stage min(k, need) of the quiet word
                m = below + (n_need - 1 - e["k"]) if e["k"] < n_need else above
                ex += phi(m / sig)
            for e in fr:
                ex += phi(above / sig)
            expect["reads"] += len(tr) + len(fr)
            expect["expected"] += ex
            expect["by_kind"].append(dict(seed=seed, kind=key, below_steps=below, above_steps=above, reads=len(tr) + len(fr), expected=ex))
    expect["seen_first_differences"] = len({(e["run"], e["cell"]) for e in flips})
    # 8. the same two quantities among the noisy runs themselves, with no quiet run: per slot, the sample variance over the
    #    three noisy runs (when all three agree on the FIRE bit), pooled. If the quiet deck differed from the noisy ones by
    #    more than noise (another time step), 1. to 5. would be larger than this.
    among = dict(score=dict(pair=[], line=[]), level=dict(pair=[], line=[]))
    for seed in sorted(inst):
        three = [data.get(f"{seed}-n{n}") for n in (1, 2, 3)]
        if any(t is None for t in three):
            continue
        by_slot = [{r["slot"]: r for r in t["rows"]} for t in three]
        counters = dict(a=0, b=0, c1=0, c2=0)
        for slot in sorted(by_slot[0]):
            rows3 = [b.get(slot) for b in by_slot]
            r0 = rows3[0]
            for c in r0["reads"]:
                rds = [r["reads"].get(c) for r in rows3]
                key, k = None, None
                if r0["stage"] == "layer 1" and c in "ab":
                    key = c
                elif r0["stage"] == "layer 2" and c == "c":
                    key = "c1" if r0["line"] == "a" else "c2"
                if key:
                    k = counters[key]
                    counters[key] += 1
                if any(x is None for x in rds) or len({x["fire"] for x in rds}) != 1:
                    continue
                fire = rds[0]["fire"]
                if c == "c":
                    arrived = sorted({a["port"] for a in rds[0]["arrivals"]})
                    if len(arrived) != 1:
                        continue
                    key = key or f"c{arrived[0]}"
                else:
                    key = c
                kind = "pair" if key in "ab" else "line"
                steps = ladders[seed][key]["q_steps"]
                if fire:
                    among["level"][kind].append(statistics.variance([x["q_peak_before_fire"] / steps[-1] for x in rds]))
                elif k is not None:
                    st = steps[k] if k < len(steps) else steps[-1]
                    among["score"][kind].append(statistics.variance([x["q_peak"] / st for x in rds]))
    among_out = {}
    for what, d in among.items():
        for kind in ("pair", "line", "all"):
            v = d["pair"] + d["line"] if kind == "all" else d[kind]
            among_out[f"{what}, {kind}"] = dict(slots=len(v), pooled_sd_steps=math.sqrt(statistics.fmean(v)) if v else None)
    budget = {}
    for seed, x in sorted(inst.items()):
        g, b3 = x["guarded"]["dose"], x["budgets"]["K3"]
        budget[seed] = dict(a=b3["a"]["training"] / (2 * g["a"]), b=b3["b"]["training"] / (2 * g["b"]), c_line=b3["c"]["training"] / g["c"])
    out_data = dict(
        what="noise audit of campaign 6, attempt c1: noisy minus quiet, per read; it recounts no claim",
        reader_check=check,
        runs=[dict(id=r["id"], stage=r["stage"], machine=r["machine"], control=r["control"], noise=r["noise"], slots=r["slots"]) for r in runs],
        reads_compared=len(ok), fire_bit_differs=flips, words_equal_to_quiet=words_equal,
        constants=const, quiet_ladders=ladders,
        stored_voltage=stored,
        dose_moves=dict(n=len(doses), dmove_mV=summary([d["dmove_mV"] for d in doses]),
                        by_cell={c: summary([d["dmove_mV"] for d in doses if d["cell"] == c]) for c in "abc"},
                        quiet_move_mV=summary([d["move_quiet_mV"] for d in doses])),
        fire_level=trip, silent_scores=silent, firing_margin=margin,
        firing_margin_pooled={k: summary(v) for k, v in dict(pooled, all=pooled_all).items()},
        stored_voltage_offsets=offsets, combined_in_steps=combo, fire_bits_expected_to_differ=expect,
        among_the_noisy_runs=among_out,
        budget_K3_training_in_steps=budget)
    (out / "AUDIT.json").write_text(json.dumps(out_data, indent=1) + "\n")
    (out / "PER_READ.json").write_text(json.dumps(per_read, indent=1) + "\n")
    print(json.dumps(dict(reader_check=check, reads_compared=len(ok), fire_bit_differs=len(flips),
                          combined_in_steps=combo, stored_voltage_offsets=offsets, budget_K3_training_in_steps=budget, expect=expect,
                          dose_moves=out_data["dose_moves"]["dmove_mV"], flips=flips), indent=1))


def windows(batch_path, out):
    """On the development batch's records only (PREDICTIONS_BATCH.json): which cells would have room for a given r
    (3 sigma of one read, in steps of its own training path), from each crossing's place in its step (question_2).
    r = None uses each record's own K3 budgets, to check the formula against the record's room_at_K3."""
    from fractions import Fraction as F
    xs = [x for x in json.loads(Path(batch_path).read_text())["instances"] if "budgets" in x]
    res = {}
    for r in (None, 0.33, 0.25, 0.22, 0.20, 0.15):
        rows = []
        for x in xs:
            q, g, b3 = x["question_2"], x["guarded"]["dose"], x["budgets"]["K3"]
            row = dict(seed=x["seed"])
            for c in "ab":
                rr = b3[c]["training"] / (2 * g[c]) if r is None else r
                lo, hi = float(F(q[c]["below_stages"])), float(F(q[c]["above_stages"]))
                row[c] = lo > rr and hi >= rr
            for rule, k in (("c_today", 2), ("c_lever1", 1)):
                ok = True
                for p in "12":
                    tr = b3["c"]["training"] / g["c"] if r is None else r
                    te = b3["c"]["testing"] / g["c"] if r is None else 2 * r
                    lo, hi = float(F(q[f"c{p}"]["below_stages"])), float(F(q[f"c{p}"]["above_stages"]))
                    ok = ok and lo > tr and hi >= (te if k == 2 else tr)
                row[rule] = ok
            if r is None:
                row["record_room_at_K3"] = x["room_at_K3"]
            rows.append(row)
        res["record's own budgets" if r is None else f"r = {r}"] = dict(
            instances=len(rows), a=sum(x["a"] for x in rows), b=sum(x["b"] for x in rows), c_today=sum(x["c_today"] for x in rows),
            c_lever1=sum(x["c_lever1"] for x in rows), all_three_today=sum(x["a"] and x["b"] and x["c_today"] for x in rows),
            all_three_lever1=sum(x["a"] and x["b"] and x["c_lever1"] for x in rows), rows=rows)
    (Path(out) / "WINDOWS_BATCH.json").write_text(json.dumps(res, indent=1) + "\n")
    for k, v in res.items():
        print(k, {a: b for a, b in v.items() if a != "rows"})
    print([dict(seed=x["seed"], a=x["a"], b=x["b"], c=x["c_today"], rec=x["record_room_at_K3"]) for x in res["record's own budgets"]["rows"]])


def constants(out):
    """The audit's reads, cut as campaign 3 and phase 1 cut theirs (research/network-circuit/phase1/constants.py, and
    campaign 3's analyze.py, M5): per run, an offset (what the run adds to every read of a kind) and a scatter within
    the run. Two instruments: (1) this audit's own, in steps: the score of silent training reads and the FIRE level of
    firing reads, noisy minus quiet; (2) campaign 3's, the FIRE latency of the firing reads, in time units, with no
    conversion to mV: the slope of latency against stored voltage is not in the runs read here."""
    out = Path(out)
    per = json.loads((out / "PER_READ.json").read_text())
    audit = json.loads((out / "AUDIT.json").read_text())
    lad = audit["quiet_ladders"]
    runs = json.loads((out / "RUNS.json").read_text())
    data = {r["id"]: json.loads((out / "reads" / f"{r['id']}.json").read_text()) for r in runs}
    ok = [e for e in per if not e["fire_differs"]]

    def key_of(e):
        if e["cell"] in "ab":
            return e["cell"]
        if e["stage"] == "layer 2":
            return "c1" if e["line"] == "a" else "c2"
        return f"c{e['arrived'][0]}" if len(e.get("arrived", [])) == 1 else None

    def split(groups):
        """groups: {name: [values]}. Scatter within a group (pooled, n - 1), the root mean square of the group means,
        and that rms with the part due to the scatter within removed (mean of within^2 / n)."""
        gs = [v for v in groups.values() if len(v) >= 2]
        dof = sum(len(v) - 1 for v in gs)
        within2 = sum(sum((x - statistics.fmean(v)) ** 2 for x in v) for v in gs) / dof
        means2 = statistics.fmean(statistics.fmean(v) ** 2 for v in gs)
        corrected2 = means2 - statistics.fmean(within2 / len(v) for v in gs)
        return dict(groups=len(gs), values=sum(len(v) for v in gs), within_sd=math.sqrt(within2), rms_of_group_means=math.sqrt(means2),
                    between_corrected=math.sqrt(max(corrected2, 0.0)))

    res = {}
    for kind in ("pair", "line"):
        score, level = {}, {}
        for e in ok:
            key = key_of(e)
            if key is None or ("pair" if key in "ab" else "line") != kind:
                continue
            steps = lad[str(e["seed"])][key]["q_steps"]
            if e["stage"] in ("layer 1", "layer 2") and not e["fire"]:
                st = steps[e["k"]] if e["k"] < len(steps) else steps[-1]
                score.setdefault((e["run"], key), []).append(e["dq_peak"] / st)
            if e["fire"]:
                level.setdefault((e["run"], key), []).append(e["dq_before_fire"] / steps[-1])
        sc, lv = split(score), split(level)
        res[kind] = dict(score_of_silent_training_reads=sc, fire_level=lv,
                         run_offset_steps=math.sqrt(sc["between_corrected"] ** 2 + lv["between_corrected"] ** 2),
                         within_run_steps=math.sqrt(sc["within_sd"] ** 2 + lv["within_sd"] ** 2))
        res[kind]["total_steps"] = math.sqrt(res[kind]["run_offset_steps"] ** 2 + res[kind]["within_run_steps"] ** 2)

    # campaign 3's estimator on the FIRE latency, in time units
    lat = dict(pair=[], line=[])
    for r in runs:
        if r["noise"] != "injected":
            continue
        quiet = data[f"{r['seed']}-quiet"]
        def lats(d, key):
            v = []
            for x in d["rows"]:
                if key in "ab":
                    rd = x["reads"].get(key)
                    if rd and rd["fire"]:
                        v.append(rd["latency"])
                else:
                    rd = x["reads"].get("c")
                    if rd and rd["fire"] and sorted({a["port"] for a in rd["arrivals"]}) == [int(key[1])]:
                        v.append(rd["latency"])
            return v
        for key in ("a", "b", "c1", "c2"):
            if data[r["id"]]["words"]["words"][key if key.startswith("c") else key + "1"] != quiet["words"]["words"][key if key.startswith("c") else key + "1"][:len(data[r["id"]]["words"]["words"][key if key.startswith("c") else key + "1"])]:
                continue                                           # only runs that gave the word of the quiet run, as campaign 3
            n, q = lats(data[r["id"]], key), lats(quiet, key)
            if len(n) >= 3 and q:
                lat["pair" if key in "ab" else "line"].append(dict(run=r["id"], kind=key, fires=len(n), offset_units=statistics.median(q) - statistics.mean(n),
                                                                   within_sd_units=statistics.stdev(n), quiet_sd_units=statistics.stdev(q) if len(q) > 1 else None))
    for kind, rows in lat.items():
        res[kind]["fire_latency_as_campaign_3"] = dict(
            port_runs=len(rows), rms_of_run_offsets_units=rms([x["offset_units"] for x in rows]),
            rms_of_within_run_sd_units=rms([x["within_sd_units"] for x in rows]),
            rms_of_quiet_run_sd_units=rms([x["quiet_sd_units"] for x in rows if x["quiet_sd_units"] is not None]),
            rows=rows)
        d = res[kind]["fire_latency_as_campaign_3"]
        d["offset_over_within"] = d["rms_of_run_offsets_units"] / d["rms_of_within_run_sd_units"]
    res["campaign_3_M5"] = dict(run_offsets_mV=0.111, within_run_mV=0.094, offset_over_within=0.111 / 0.094, port_runs=38)
    res["mean_quiet_dose_mV"] = audit["dose_moves"]["quiet_move_mV"]["mean"]
    (out / "CONSTANTS_AS_CAMPAIGN_3.json").write_text(json.dumps(res, indent=1) + "\n")
    show = {k: {a: b for a, b in v.items() if a != "fire_latency_as_campaign_3"} for k, v in res.items() if k in ("pair", "line")}
    for k in ("pair", "line"):
        show[k]["latency"] = {a: b for a, b in res[k]["fire_latency_as_campaign_3"].items() if a != "rows"}
    print(json.dumps(show, indent=1))


def m5(repo, ev, out, predicted_path):
    """b and w in mV by campaign 3's definition (its analyze.py, M5; phase 1's constants.py), on the 12 noisy runs:
    per noisy run and kind of read, (median FIRE latency of the quiet run - mean FIRE latency of the noisy run) / slope
    and stdev(FIRE latencies of the noisy run) / slope, on runs that gave the quiet word, with at least 3 FIREs.
    The slope is phase 1's `secant`, copied below, on the firing reads of the kind in the instance's guard-on
    calibration deck of stage M1 (isolated reads, one per stage), at the trained state: the stored voltage of the
    deck's first firing stage. For a pair the stored voltage is the mean of its two ports, which move together."""
    repo_paths(repo)
    import measure
    import reads4
    out = Path(out)
    predicted = json.loads(Path(predicted_path).read_text())
    inst = {x["seed"]: x for x in predicted["instances"] if x.get("needs")}
    lat = json.loads((out / "CONSTANTS_AS_CAMPAIGN_3.json").read_text())

    def secant(points, u):                                   # research/network-circuit/phase1/constants.py, verbatim
        points = sorted(set(points))
        merged = []
        for p in points:
            if merged and p[0] - merged[-1][0][0] < 0.02:
                merged[-1].append(p)
            else:
                merged.append([p])
        points = [(statistics.mean(x[0] for x in g), statistics.mean(x[1] for x in g)) for g in merged]
        assert len(points) >= 2
        i = min(max(sum(1 for p in points if p[0] <= u), 1), len(points) - 1)
        (u0, l0), (u1, l1) = points[i - 1], points[i]
        return (l1 - l0) / (u1 - u0)

    KIND = dict(a=("a", "both", ("1", "2")), b=("b", "both", ("1", "2")), c1=("c", "port 1", ("1",)), c2=("c", "port 2", ("2",)))
    slopes = {}
    for seed in sorted(inst):
        d = next((Path(ev) / "M1" / m / f"{seed}-cal-on" for m in MACHINES if (Path(ev) / "M1" / m / f"{seed}-cal-on").exists()), None)
        rec = json.loads((d / "record.json").read_text())
        result = json.loads((d / "evidence" / "result.json").read_text())
        rows = reads4.calibration_reads(measure.Trace(d / "evidence" / "trace.raw"), result, rec["reads"])
        slopes[seed] = {}
        for key, (cell, read, ports) in KIND.items():
            mine = sorted((r for r in rows if r["cell"] == cell and r["read"] == read), key=lambda r: r["stage"])
            u = lambda r: statistics.fmean(r["ports"][p]["u_before_mV"] for p in ports)
            fired = [(u(r), r["latency"]) for r in mine if r["fire"]]
            first = next(r for r in mine if r["fire"])
            assert first["stage"] == inst[seed]["needs"][key], (seed, key, first["stage"])
            pts = sorted(fired, reverse=True)                 # from the trained state toward stronger states
            nxt = (pts[2][1] - pts[1][1]) / (pts[2][0] - pts[1][0]) if len(pts) >= 3 else None
            slopes[seed][key] = dict(need=first["stage"], trained_mV=u(first), latency_at_trained=first["latency"],
                                     firing_stages=[r["stage"] for r in mine if r["fire"]], latencies=[r["latency"] for r in mine if r["fire"]],
                                     u_mV=[u(r) for r in mine if r["fire"]],
                                     slope_per_mV=secant(fired, u(first)), slope_one_stage_further_per_mV=nxt)
    res = dict(slopes={str(k): v for k, v in slopes.items()})
    for kind in ("pair", "line"):
        rows = []
        for x in lat[kind]["fire_latency_as_campaign_3"]["rows"]:
            seed = int(x["run"].split("-")[0])
            sl = slopes[seed][x["kind"]]["slope_per_mV"]
            sl2 = slopes[seed][x["kind"]]["slope_one_stage_further_per_mV"]
            rows.append(dict(x, slope_per_mV=sl, offset_mV=x["offset_units"] / sl, within_sd_mV=x["within_sd_units"] / sl,
                             offset_mV_with_next_slope=None if not sl2 else x["offset_units"] / sl2,
                             within_sd_mV_with_next_slope=None if not sl2 else x["within_sd_units"] / sl2))
        res[kind] = dict(port_runs=len(rows), b_run_offsets_rms_mV=rms([r["offset_mV"] for r in rows]),
                         w_within_run_rms_mV=rms([r["within_sd_mV"] for r in rows]),
                         mean_offset_mV=statistics.fmean(r["offset_mV"] for r in rows),
                         sd_of_offsets_mV=sd([r["offset_mV"] for r in rows]),
                         b_with_next_slope_mV=rms([r["offset_mV_with_next_slope"] for r in rows if r["offset_mV_with_next_slope"] is not None]),
                         w_with_next_slope_mV=rms([r["within_sd_mV_with_next_slope"] for r in rows if r["within_sd_mV_with_next_slope"] is not None]),
                         rows=rows)
    allrows = res["pair"]["rows"] + res["line"]["rows"]
    res["all"] = dict(port_runs=len(allrows), b_run_offsets_rms_mV=rms([r["offset_mV"] for r in allrows]), w_within_run_rms_mV=rms([r["within_sd_mV"] for r in allrows]))
    # how much the slope depends on where it is taken: the secant above spans one whole dose on the strong side of the
    # trained state. A parabola through the first three firing stages gives the slope at the trained state itself:
    # 1.5 x (first secant) - 0.5 x (next secant), for equal doses. Reported beside, as a sensitivity, not as the definition.
    for kind in ("pair", "line"):
        rows = res[kind]["rows"]
        for r in rows:
            seed = int(r["run"].split("-")[0])
            s1, s2 = slopes[seed][r["kind"]]["slope_per_mV"], slopes[seed][r["kind"]]["slope_one_stage_further_per_mV"]
            r["slope_three_points_per_mV"] = 1.5 * s1 - 0.5 * s2
        res[kind]["b_three_point_slope_mV"] = rms([r["offset_units"] / r["slope_three_points_per_mV"] for r in rows])
        res[kind]["w_three_point_slope_mV"] = rms([r["within_sd_units"] / r["slope_three_points_per_mV"] for r in rows])
        res[kind]["mean_ratio_next_slope_over_slope"] = statistics.fmean(
            slopes[int(r["run"].split("-")[0])][r["kind"]]["slope_one_stage_further_per_mV"] / r["slope_per_mV"] for r in rows)
    # a test of these figures against the FIRE bits: if a read's margin moved by a Gaussian of sigma = sqrt(b^2 + w^2),
    # how many FIRE bits of the firing reads at the trained state would differ from the quiet run? (As section 4.8.)
    from fractions import Fraction as F
    phi = lambda z: 0.5 * math.erfc(z / math.sqrt(2))
    per = [e for e in json.loads((out / "PER_READ.json").read_text())]
    test = {}
    for label, bk, wk in (("secant", "b_run_offsets_rms_mV", "w_within_run_rms_mV"), ("three points", "b_three_point_slope_mV", "w_three_point_slope_mV")):
        total, n = 0.0, 0
        for seed, x in inst.items():
            for key in ("a", "b", "c1", "c2"):
                kind = "pair" if key in "ab" else "line"
                sig_mV = math.sqrt(res[kind][bk] ** 2 + res[kind][wk] ** 2)
                D = statistics.fmean(float(F(x["D_mV"][f"{key[0]}{p}"])) for p in (("1", "2") if key in "ab" else (key[1],)))
                above = float(F(x["question_2"][key]["above_stages"]))
                if key in "ab":
                    k = sum(1 for e in per if e["seed"] == seed and e["cell"] == key and not e.get("fire_differs") and e["fire"])
                else:
                    k = sum(1 for e in per if e["seed"] == seed and e["cell"] == "c" and not e.get("fire_differs") and e["fire"] and e.get("arrived") == [int(key[1])])
                total += k * phi(above / (sig_mV / D))
                n += k
        test[label] = dict(firing_reads=n, expected_to_differ=total, seen=0)
    res["fire_bits_of_firing_reads"] = test
    res["constants"] = predicted["constants"]
    (out / "M5_AS_CAMPAIGN_3.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: {a: b for a, b in v.items() if a != "rows"} for k, v in res.items() if k in ("pair", "line", "all", "fire_bits_of_firing_reads")}, indent=1))
    for seed, v in slopes.items():
        for key, x in v.items():
            print(seed, key, "need", x["need"], "stages", x["firing_stages"], "lat", [round(l, 4) for l in x["latencies"]], "slope", round(x["slope_per_mV"], 4),
                  "next", None if x["slope_one_stage_further_per_mV"] is None else round(x["slope_one_stage_further_per_mV"], 4))


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "verify":
        verify(a[1], a[2])
    elif a and a[0] == "verify-m1":
        verify(a[1], a[2], stages=("M1",), report_name="VERIFY_M1.json")
    elif a and a[0] == "m5":
        m5(a[1], a[2], a[3], a[4])
    elif a and a[0] == "reads":
        reads(a[1], a[2], a[3])
    elif a and a[0] == "analyze":
        analyze(a[1], a[2], a[3], a[4], a[5])
    elif a and a[0] == "windows":
        windows(a[1], a[2])
    elif a and a[0] == "constants":
        constants(a[1])
    else:
        raise SystemExit(__doc__)
