"""Development only: what a batch of measures says, instance by instance, under campaign 6's frozen rule and under the
one-port rule for cell c's testing error. No simulation. It counts nothing for any campaign.

  batch2x_report.py REPO RUNS_DIR OUT_DIR        the batch of batch2x.py (seeds 8301 to 8310, RUNS_DIR/<seed>-<run>)

Per instance, as predict6.predict_batch does: not measured if its two decks did not both complete; otherwise the scans,
one-sided sets and both-lines check that completed are read, and predict6.predict_instance is called under
predict6_guard's wrapper (an instance on which campaign 5's predicted.instance raises is not eligible). Then the
one-port rule by t1_gate.one_port, unchanged. Reported per instance: its needs; whether it is eligible (K = 0) under
each rule; the room at K = 3 of a, b and c under each rule, with the reads that have none; each crossing's place in
its step (below = s* - (need - 1), above = need - s*) and the K = 3 budgets, in stages; and whether each crossing
sits in its window under the one-port rule (below > budget and above >= budget). The summary gives two counts:
k_elig, the instances eligible at K = 0 under the frozen rule (the count campaign 6's stopping rule uses), and k_all3,
the instances where a, b and c all have room at K = 3 under the one-port rule (what the batch is for).
It also writes each predicted instance's gate file under each rule with the frozen generator
(OUT_DIR/Gate_<seed>_frozen.lean, Gate_<seed>_oneport.lean).
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev2
import t1_gate

NEEDS = (("a", ("a", "pair")), ("b", ("b", "pair")), ("c1", ("c", "line1")), ("c2", ("c", "line2")))


def one_instance(seed, label, status, run_dir, out=None):
    """status: {run id: status} of this instance's runs; run_dir(tail) -> the folder of the run `<seed>-<tail>`."""
    import gate4
    import predict6
    import predict6_guard
    rec = lambda d: json.loads((Path(d) / "record.json").read_text())
    row = dict(seed=seed)
    if status.get(f"{seed}-cal-on") != "complete" or status.get(f"{seed}-cal-off") != "complete":
        row.update(measured=False, why="a calibration deck did not complete")
        return row
    on, off = run_dir("cal-on"), run_dir("cal-off")
    scans, ones = {}, {}
    for c, kind in predict6.CROSSINGS:
        if status.get(f"{seed}-scan-{c}-{kind}") == "complete":
            r = rec(run_dir(f"scan-{c}-{kind}"))
            scans[(c, kind)] = dict(r["result"], u0_V=r["u0_V"])
    for c in ("a", "b"):
        if status.get(f"{seed}-onesided-{c}") == "complete":
            r = rec(run_dir(f"onesided-{c}"))
            ones[c] = dict(r["result"], u0_V=r["u0_V"])
    bf = None
    if status.get(f"{seed}-bothfire-c") == "complete":
        r = rec(run_dir("bothfire-c"))
        bf = dict(r["result"], u0_V=r["u0_V"])
    with mock.patch.object(predict6.P, "instance", predict6_guard.guarded_instance):
        x = predict6.predict_instance(seed, label, status, on, off, scans, ones, bf)
    row.update(measured=bool(x.get("measured")), eligible_K0_frozen=bool(x.get("eligible")), question_1=x.get("question_1"),
               why=(x.get("why_not_measured") or x.get("why_not_eligible") or [None])[0], why_all=x.get("why_not_measured") or x.get("why_not_eligible") or [])
    if scans:
        row["crossings"] = {k: dict(s_star=float(F(scans[v]["s_star"])), half_bracket=scans[v].get("half_bracket"), consistent=bool(scans[v].get("consistent")))
                            for k, v in NEEDS if v in scans and scans[v].get("crossing")}
    if "budgets" not in x:
        return row
    t, dose, _ = predict6.table(on, off)
    w = predict6.deck_w(on, predict6.doses_V(dose))
    t2 = predict6.mapped(t, w, predict6.anchors({k: F(scans[k]["s_star"]) for k in predict6.CROSSINGS}))
    assert x["room"] == {K: predict6.P.room(t2, x["needs"], predict6.lay_of(x), x["budgets"][K]) for K in ("K0", "K3")}, (seed, "not the table predict_instance used")
    y, detail = t1_gate.one_port(x, t2)
    g = x["guarded"]["dose"]
    st = lambda v, c: float(F(v, g[c] if c == "c" else 2 * g[c]))
    budget = dict(a=st(x["budgets"]["K3"]["a"]["training"], "a"), b=st(x["budgets"]["K3"]["b"]["training"], "b"),
                  c1=st(x["budgets"]["K3"]["c"]["training"], "c"), c2=st(x["budgets"]["K3"]["c"]["training"], "c"))
    place = {}
    for k, v in NEEDS:
        s = F(scans[v]["s_star"])
        below, above = float(s - (math.ceil(s) - 1)), float(math.ceil(s) - s)
        place[k] = dict(s_star=float(s), need=math.ceil(s), below=below, above=above, budget_stages=budget[k], in_its_window=below > budget[k] and above >= budget[k])
    row.update(needs=x["needs"], doses_mV={k: float(F(v)) for k, v in x["D_mV"].items()}, crossings_in_their_steps=place,
               frozen=dict(eligible_K0=x["eligible"], verdicts=gate4.verdicts(x), room_at_K3=x["room_at_K3"], counts_N_out=x["counts_N_out"],
                           without_room_K3={c: v["without_room"] for c, v in x["room"]["K3"].items()}),
               one_port=dict(eligible_K0=y["eligible"], verdicts=gate4.verdicts(y), room_at_K3=y["room_at_K3"],
                             counts_N_out=dict(a=y["room_at_K3"]["a"], b=y["room_at_K3"]["b"], c=all(y["room_at_K3"].values())),
                             without_room_K3={c: v["without_room"] for c, v in y["room"]["K3"].items()}),
               budgets_stages_K3=dict(a=budget["a"], b=budget["b"], c_training=budget["c1"], c_testing_two_ports=st(x["budgets"]["K3"]["c"]["testing"], "c"),
                                      c_testing_one_port=st(y["budgets"]["K3"]["c"]["testing"], "c")),
               budgets_units=dict(frozen=x["budgets"], one_port_c_testing={K: y["budgets"][K]["c"]["testing"] for K in ("K0", "K3")}),
               one_port_detail=detail)
    if out is not None:
        for name, inst in (("frozen", x), ("oneport", y)):
            predict6.gate_file([inst], Path(out) / f"Gate_{seed}_{name}.lean")
    return row


def summary(rows):
    pred = [r for r in rows if "frozen" in r]
    seeds = lambda f: [r["seed"] for r in pred if f(r)]
    crossings = [v for r in pred for v in r["crossings_in_their_steps"].values()]
    return dict(
        k_elig=len(seeds(lambda r: r["frozen"]["verdicts"]["K0"])),                                  # eligible at K = 0, campaign 6's rule
        k_all3=len(seeds(lambda r: all(r["one_port"]["room_at_K3"].values()))),                      # a, b and c with room at K = 3, one-port rule
        instances=len(rows), measured=sum(bool(r.get("measured")) for r in rows), with_a_prediction=len(pred),
        eligible_K0=dict(frozen=seeds(lambda r: r["frozen"]["verdicts"]["K0"]), one_port=seeds(lambda r: r["one_port"]["verdicts"]["K0"])),
        room_at_K3=dict(a=seeds(lambda r: r["frozen"]["room_at_K3"]["a"]), b=seeds(lambda r: r["frozen"]["room_at_K3"]["b"]),
                        c_frozen=seeds(lambda r: r["frozen"]["room_at_K3"]["c"]), c_one_port=seeds(lambda r: r["one_port"]["room_at_K3"]["c"])),
        a_b_and_c_all_have_room_at_K3=dict(frozen=seeds(lambda r: all(r["frozen"]["room_at_K3"].values())), one_port=seeds(lambda r: all(r["one_port"]["room_at_K3"].values()))),
        crossings=dict(n=len(crossings), in_their_window=sum(v["in_its_window"] for v in crossings)),
        without_a_prediction={str(r["seed"]): r.get("why") for r in rows if "frozen" not in r})


def walls(runs):
    """Each run's status and wall time, and the mean wall time of the complete runs of each kind."""
    per, by = {}, {}
    for sub in ("W1", "W2", "W3"):
        p = Path(runs) / sub / "STATE.json"
        if not p.exists():
            continue
        for rid, v in json.loads(p.read_text())["runs"].items():
            tail = rid.split("-", 1)[1]
            kind = tail if tail.startswith("cal-") else "pair" if tail.endswith("-pair") else "line" if "-line" in tail else "bothfire" if tail.startswith("bothfire") else "onesided"
            per[rid] = dict(kind=kind, status=v["status"], wall_s=v.get("wall_s"), limit_s=v.get("limit_s"))
            if v["status"] == "complete":
                by.setdefault(kind, []).append(v["wall_s"])
    return dict(runs=per, mean_wall_s_of_complete_runs={k: sum(v) / len(v) for k, v in by.items()}, complete={k: len(v) for k, v in by.items()})


def statuses(runs):
    out = {}
    for sub in ("W1", "W2", "W3"):
        p = Path(runs) / sub / "STATE.json"
        if p.exists():
            out.update({k: v["status"] for k, v in json.loads(p.read_text())["runs"].items()})
    return out


if __name__ == "__main__":
    repo, runs, out = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
    dosedev2.repo_paths(repo)
    import batch2x
    out.mkdir(parents=True, exist_ok=True)
    status = statuses(runs)
    rows = [one_instance(s, "dev", {k: v for k, v in status.items() if k.startswith(f"{s}-")}, lambda tail, s=s: runs / f"{s}-{tail}", out) for s in batch2x.SEEDS]
    res = dict(what="development batch at twice the dose, reltol 1e-5: measures only; it counts nothing", parameters=batch2x.PARAMS,
               summary=summary(rows), instances=rows, wall_times=walls(runs))
    (out / "BATCH2X_REPORT.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
    print(json.dumps(res["summary"], indent=1))
