"""The analysis of the campaign, as PREDICTION.md fixes it. Run once, after both machines have ended.

  analyze.py EVIDENCE_A EVIDENCE_B OUT        -> OUT/RESULTS.json and OUT/REPORT.md  (OUT must not exist)

EVIDENCE_A and EVIDENCE_B are the evidence folders of the two machines, as the launcher left them or as
`collect` copied them: STATE.json, and one folder per run. Every measure is taken again from the
waveform of the run; the record that the run wrote is only compared with it. Nothing is simulated.
"""
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import plan
import run as R
from run import K, extract, sim

JOINT, SINGLE = (0.250, 0.280), (0.5, 1.0)
NEED = dict(M=40, O=5, R=5)             # fewer runs than this: the prediction is not established
QUIET_CONFIGS = ["tt27", "ss27", "ff27", "sf27", "fs27", "tt-40", "tt125", "mm2001", "mm2002"]


def binomial_tail(n, k, p):
    """P(X >= k) for X binomial(n, p)."""
    return sum(math.comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(k, n + 1))


def clopper_pearson(k, n, level=0.95):
    """Exact two-sided interval for k events in n trials; with k = 0 the upper end at one-sided `level` is 1 - (1-level)^(1/n)."""
    def solve(f, target):
        lo, hi = 0.0, 1.0
        for _ in range(200):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if f(mid) < target else (lo, mid)
        return (lo + hi) / 2
    alpha = 1 - level
    lower = 0.0 if k == 0 else solve(lambda p: binomial_tail(n, k, p), alpha / 2)
    upper = 1.0 if k == n else solve(lambda p: binomial_tail(n, k + 1, p), 1 - alpha / 2)
    return lower, upper


def one_sided_bound(n, level=0.95):
    return 1 - (1 - level) ** (1 / n)


def correct(name, x):
    lo, hi = JOINT if name == "joint" else SINGLE
    return x["fires"] == 1 and x["fire_latency"] is not None and lo <= x["fire_latency"] <= hi and x["writes1"] == 0 and x["writes2"] == 0


def measure(folder, planned):
    """Everything the predictions need from one run, from its waveform. Raises if the evidence is not that of the planned run."""
    r = json.loads((folder / "result.json").read_text())
    for key in ("id", "scenario", "config", "mode", "version", "seed"):
        assert r[key] == planned[key], (key, r[key], planned[key])
    assert r["noise"] == bool(planned["noise"]) and r["jump_S"] == planned["jump_S"] and r["jump_period"] == R.JUMP_PERIOD
    assert r["services_requested"] == planned["services"] and r["ended_at_the_last_slot_of_its_plan"] is True
    for name, digest in r["files"].items():
        assert sim.digest(folder / name) == digest, name
    v_service, bounds = R.bounds_of(r["config"], r["version"])
    assert r["v_service_V"] == v_service and r["bounds"] == [vars(b) for b in bounds]
    deck = sim.deck(section=r["section"], temperature=r["temperature_C"], noise=r["noise"], leak_S=R.G0, junction="areas")
    assert R.hashlib.sha256(deck.encode()).hexdigest() == r["deck_sha256"]
    written = (folder / "input.spice").read_text()
    library = next(l for l in written.splitlines() if l.startswith(".lib "))
    assert written.replace(library.split('"')[1], "pdk/models/sky130.lib.spice") == deck, "the deck of the run is not the deck of the preregistration"
    d = R.read_raw(folder / "trace.raw")
    rows = {k: R.slot_record(d, k) for k in range(2, r["last_slot"] + 1)}
    fingerprint = extract.noise_fingerprint(R.read_raw(folder / "head.raw"))
    assert fingerprint == r["noise_fingerprint"] == (folder / "noise.sha256").read_text().strip()
    reserve = lambda p, u: K.to_units(v_service[p] - u)
    marks = [e for e in r["events"] if e["phase"] in ("maintenance", "end")]
    reads = [e for e in r["events"] if e["phase"] == "read"]
    out = dict(id=r["id"], scenario=r["scenario"], config=r["config"], mode=r["mode"], noise=r["noise"], fingerprint=fingerprint,
               record_is_the_waveform=r["records"] == [rows[k] for k in sorted(rows)], entered=r["entered_at_slot"] is not None,
               preparation_cycles=[sum(e["action"][p] == K.MAINTENANCE for e in r["events"] if e["phase"] == "preparation") for p in (0, 1)],
               wall_s=r["wall_s"])
    # refusals, as the kernel answered them
    refused = [None, None]
    for e in marks[:-1]:
        for p in (0, 1):
            if e["kernel"][p] is not None and e["kernel"][p]["answer"] == K.REFUSE and refused[p] is None:
                refused[p] = e["period"]
    assert refused == r["refused_at_period"]
    out["refused_at_period"] = refused
    # services
    out["services"] = [dict(period=e["period"], read=e["read"], correct=correct(e["read"], rows[e["slot"]]), fires=rows[e["slot"]]["fires"],
                            latency=rows[e["slot"]]["fire_latency"], writes=[rows[e["slot"]]["writes1"], rows[e["slot"]]["writes2"]],
                            reserve_units=[reserve(p, rows[e["slot"]][f"u{p + 1}_pre_pulse"]) for p in (0, 1)]) for e in reads]
    # writes and FIRE outside reads
    read_slots = {e["slot"] for e in reads}
    commanded = {e["slot"]: e["action"] for e in r["events"] if e["phase"] in ("preparation", "maintenance")}
    out["writes_not_as_commanded"] = sum(rows[k][f"writes{p + 1}"] != (1 if action[p] == K.MAINTENANCE else 0)
                                         for k, action in commanded.items() if k in rows for p in (0, 1))
    out["fires_outside_reads"] = sum(x["fires"] for k, x in rows.items() if k not in read_slots)
    # the kernel's enclosure and its premises, on the reserves observed in the waveform
    observed = [[reserve(p, rows[e["slot"] - 1][f"u{p + 1}_obs"]) for p in (0, 1)] for e in marks]
    out["report_differs_from_waveform"] = sum(abs(e["report"][p] - observed[i][p]) > bounds[p].epsilon for i, e in enumerate(marks) for p in (0, 1))
    out["enclosure_broken"] = [dict(period=e["period"], port=p + 1) for i, e in enumerate(marks[:-1]) for p in (0, 1)
                               if e["kernel"][p] is not None and not e["kernel"][p]["lower"] <= observed[i][p] <= e["kernel"][p]["upper"]]
    premises = []
    for i, e in enumerate(marks[:-1]):
        for p in (0, 1):
            step, b = observed[i + 1][p] - observed[i][p], bounds[p]
            ok = b.Dmin - b.H <= step <= b.Dmax if e["action"][p] == K.MAINTENANCE else 0 <= -step <= b.H
            if not ok:
                premises.append(dict(period=e["period"], port=p + 1, action=e["action"][p], step_units=step))
    out["premises_broken"] = premises
    out["reads_outside_floor_and_capacity"] = [dict(period=s["period"], port=p + 1, reserve_units=s["reserve_units"][p]) for s in out["services"]
                                               for p in (0, 1) if not bounds[p].S <= s["reserve_units"][p] <= bounds[p].capacity]
    return out


def gather(folders, planned_runs=None):
    """Status of every planned run, and the measures of those that count."""
    states = {}
    for folder in folders:
        state = json.loads((folder / "STATE.json").read_text())
        assert state["machine"] not in states
        states[state["machine"]] = (folder, {r["id"]: r for r in state["records"]})
    assert set(states) == {"a", "b"}
    rows = []
    for planned in planned_runs or plan.runs():
        folder, records = states[planned["machine"]]
        record = records.get(planned["id"])
        row = dict(id=planned["id"], machine=planned["machine"], scenario=planned["scenario"], config=planned["config"],
                   status=record["status"] if record else "never started", counts=False, measures=None)
        if record and record["status"] == "complete":
            row["measures"] = measure(folder / planned["id"] / "evidence", planned)
            assert row["measures"]["fingerprint"] == record["noise_fingerprint"]
            row["counts"] = True
        rows.append(row)
    seen = {}                                               # rule 4: of several noisy runs with one fingerprint, the first in manifest order
    for row in rows:
        if row["counts"] and row["measures"]["noise"]:
            first = seen.setdefault(row["measures"]["fingerprint"], row["id"])
            if first != row["id"]:
                row.update(counts=False, status="duplicate noise of " + first)
    return rows


def verdict(holds, enough=True):
    return "not established" if not enough else "holds" if holds else "fails"


def evaluate(rows):
    counted = [r["measures"] for r in rows if r["counts"]]
    of = lambda scenario: [m for m in counted if m["scenario"] == scenario or (scenario == "main" and m["scenario"].startswith("main-"))]
    failed = lambda m, periods=None: [s for s in m["services"] if not s["correct"] and (periods is None or s["period"] in periods)]
    clean = lambda m: m["entered"] and m["refused_at_period"] == [None, None]
    out = {}

    def four(ms, prefix, enough):
        out[prefix + "1"] = dict(verdict=verdict(all(clean(m) for m in ms), enough), runs=len(ms), not_entered=[m["id"] for m in ms if not m["entered"]],
                                 refusals=[dict(run=m["id"], period=m["refused_at_period"]) for m in ms if m["refused_at_period"] != [None, None]])
        bad = [m["id"] for m in ms if failed(m) or len(m["services"]) != plan.SERVICES]
        out[prefix + "2"] = dict(verdict=verdict(not bad, enough), runs=len(ms), services=sum(len(m["services"]) for m in ms),
                                 failed_services=[dict(run=m["id"], **s) for m in ms for s in failed(m)], runs_with_a_failed_service=bad)
        out[prefix + "3"] = dict(verdict=verdict(all(m["writes_not_as_commanded"] == 0 and m["fires_outside_reads"] == 0 for m in ms), enough),
                                 writes_not_as_commanded=sum(m["writes_not_as_commanded"] for m in ms), fires_outside_reads=sum(m["fires_outside_reads"] for m in ms))
        out[prefix + "4"] = dict(verdict=verdict(all(not m["enclosure_broken"] for m in ms), enough),
                                 broken=[dict(run=m["id"], **x) for m in ms for x in m["enclosure_broken"]])
        return bad

    main = of("main")
    bad = four(main, "M", len(main) >= NEED["M"])
    if main:
        n, k = len(main), len(bad)
        out["M2"]["bound"] = (dict(statement="no run had a failed service", one_sided_95_upper_bound_on_the_fraction_of_runs=one_sided_bound(n)) if k == 0
                              else dict(statement=f"{k} of {n} runs had a failed service", two_sided_95_interval_of_the_fraction_of_runs=clopper_pearson(k, n)))
        out["M2"]["per_configuration"] = {c: dict(runs=sum(m["config"] == c for m in main), runs_with_a_failed_service=sum(m["config"] == c and m["id"] in bad for m in main))
                                          for c in plan.MAIN}
    quiet = of("quiet")
    per = {}
    for c in QUIET_CONFIGS:
        ms = [m for m in quiet if m["config"] == c]
        if not ms:
            per[c] = "not established"
            continue
        ok = all(clean(m) and not failed(m) and len(m["services"]) == plan.SERVICES and m["writes_not_as_commanded"] == 0 and m["fires_outside_reads"] == 0
                 and not m["enclosure_broken"] and not m["reads_outside_floor_and_capacity"] and not m["premises_broken"] for m in ms)
        per[c] = "holds" if ok else "fails"
    four(quiet, "Q", bool(quiet))
    out["Q5"] = dict(verdict=verdict(all(not m["reads_outside_floor_and_capacity"] for m in quiet), bool(quiet)),
                     outside=[dict(run=m["id"], **x) for m in quiet for x in m["reads_outside_floor_and_capacity"]])
    out["Q6"] = dict(verdict=verdict(all(not m["premises_broken"] for m in quiet), bool(quiet)), broken=[dict(run=m["id"], **x) for m in quiet for x in m["premises_broken"]])
    out["Q_per_configuration"] = per
    out["Q_on_the_nine_configurations"] = "fails" if "fails" in per.values() else "not established" if "not established" in per.values() else "holds"
    outside = of("outside")
    before = range(R.JUMP_PERIOD)
    o1 = lambda m: m["entered"] and all(x is None or x >= R.JUMP_PERIOD for x in m["refused_at_period"]) and not failed(m, before) and len(m["services"]) == plan.SERVICES
    out["O1"] = dict(verdict=verdict(all(o1(m) for m in outside), len(outside) >= NEED["O"]), runs=len(outside), failing=[m["id"] for m in outside if not o1(m)])
    out["O2"] = dict(verdict=verdict(all(m["refused_at_period"] == [R.JUMP_PERIOD + 1] * 2 for m in outside), len(outside) >= NEED["O"]),
                     refused_at_period={m["id"]: m["refused_at_period"] for m in outside},
                     reported_without_prediction={m["id"]: dict(failed_services_from_the_jump=[s["period"] for s in failed(m) if s["period"] >= R.JUMP_PERIOD]) for m in outside})
    alone = of("self")
    total, lost = sum(len(m["services"]) for m in alone), sum(len(failed(m)) for m in alone)
    out["R1"] = dict(verdict=verdict(all(failed(m) for m in alone), len(alone) >= NEED["R"]), runs=len(alone), failed_services={m["id"]: len(failed(m)) for m in alone})
    out["R2"] = dict(verdict=verdict(total > 0 and lost >= 0.05 * total, len(alone) >= NEED["R"]), failed=lost, services=total, fraction=lost / total if total else None)
    if out["M2"]["verdict"] == out["R1"]["verdict"] == out["R2"]["verdict"] == "holds":
        out["comparison"] = (f"Under the same jump, the supervised cell failed no service in {len(main)} runs, "
                             f"and the cell left to itself failed {lost} of {total} services.")
    else:
        out["comparison"] = "Not stated: M2, R1 and R2 do not all hold."
    out["records_that_differ_from_their_waveform"] = [m["id"] for m in counted if not m["record_is_the_waveform"]]
    out["reports_that_differ_from_the_waveform"] = sum(m["report_differs_from_waveform"] for m in counted)
    return out


def report(rows, results):
    lines = ["# SKY130 supervisor campaign: report", "",
             "Written by `analyze.py` under [`PREDICTION.md`](PREDICTION.md). Simulations of the two-port cell with junction areas; no layout, no silicon.", ""]
    names = [k for k in results if len(k) == 2 and k[0] in "MQOR"]
    count = lambda v: sum(results[k]["verdict"] == v for k in names)
    lines += [f"{count('holds')} predictions hold, {count('fails')} fail, {count('not established')} are not established, of {len(names)}.", "",
              "| | Verdict | Numbers |", "|---|---|---|"]
    for k in names:
        numbers = {a: b for a, b in results[k].items() if a != "verdict" and not isinstance(b, (list, dict))}
        lists = {a: len(b) for a, b in results[k].items() if isinstance(b, list)}
        lines.append(f"| {k} | {results[k]['verdict']} | " + ", ".join(f"{a}: {b}" for a, b in {**numbers, **lists}.items()) + " |")
    lines += ["", "Deterministic claim, per configuration: " + ", ".join(f"`{c}` {v}" for c, v in results["Q_per_configuration"].items())
              + f". On the nine configurations: {results['Q_on_the_nine_configurations']}.", ""]
    if "bound" in results["M2"]:
        lines += ["M2: " + json.dumps(results["M2"]["bound"]), ""]
    lines += ["Comparison: " + results["comparison"], "", "## Runs", "", "| Run | Status | Counts | Services | Failed | Refused at period | Wall time |", "|---|---|---|---|---|---|---|"]
    for r in rows:
        m = r["measures"]
        cells = [str(len(m["services"])), str(sum(not s["correct"] for s in m["services"])), str(m["refused_at_period"]), f"{m['wall_s']:.0f} s"] if m else ["", "", "", ""]
        lines.append(f"| `{r['id']}` | {r['status']} | {'yes' if r['counts'] else 'no'} | " + " | ".join(cells) + " |")
    missing = [r for r in rows if not r["counts"]]
    lines += ["", f"Runs that do not count: {len(missing)} of {len(rows)}." + ("" if not missing else " " + ", ".join(f"`{r['id']}` ({r['status']})" for r in missing)), "",
              "## Failed services", "", "| Run | Period | Read | FIRE | Latency | Writes |", "|---|---|---|---|---|---|"]
    for r in rows:
        if r["measures"]:
            for s in r["measures"]["services"]:
                if not s["correct"]:
                    lines.append(f"| `{r['id']}` | {s['period']} | {s['read']} | {s['fires']} | {s['latency']} | {s['writes']} |")
    return "\n".join(lines) + "\n"


def main():
    a, b, out = (Path(x).resolve() for x in sys.argv[1:4])
    assert not out.exists(), "one analysis: it does not overwrite"
    rows = gather([a, b])
    results = evaluate(rows)
    out.mkdir(parents=True)
    (out / "RESULTS.json").write_text(json.dumps(dict(predictions=results, runs=rows), indent=1) + "\n")
    (out / "REPORT.md").write_text(report(rows, results))
    print((out / "REPORT.md").read_text().split("## Runs")[0])


if __name__ == "__main__":
    main()
