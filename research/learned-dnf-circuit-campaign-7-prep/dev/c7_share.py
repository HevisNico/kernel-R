"""Development only, for a design note: on the DEVELOPMENT batch of campaign 6 (seeds 7701 to 7710, development data
since their first run), which instances have room for c at K = 3 under the frozen rule and under the one-port rule.
No simulation. Campaign 6's counted instances (7801 to 7805) are not read.

  c7_share.py REPO BATCH_DIR PREDICTIONS_BATCH.json OUT_DIR

BATCH_DIR holds the batch's collected runs as its evidence branches do: BATCH_DIR/<machine>/<run id>/ and
BATCH_DIR/<machine>/RUNS.json. Per seed, in the batch's order and on its assigned machine:
1. as predict6.predict_batch: an instance whose two decks did not both complete is not measured; otherwise the scans,
   one-sided sets and both-lines check that completed are read, and predict6.predict_instance is called under
   predict6_guard's wrapper (an instance on which campaign 5's predicted.instance raises is not eligible);
2. guard: needs, budgets, eligible and room_at_K3 must equal the batch's own record (PREDICTIONS_BATCH.json), or stop;
3. the one-port rule, by t1_gate.one_port, unchanged: c's testing budget is the larger of the two lines' one-port
   budgets at their needs, plus H_c + S_c; c's test reads are judged again with it (the both-lines read keeps the
   two-port budget); a and b keep the frozen room.
It also writes, for every instance with a prediction, the gate file of each rule with the frozen generator
(OUT_DIR/Gate7_<seed>_frozen.lean, Gate7_<seed>_oneport.lean), to be checked by campaign 5's check.sh.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev2
import t1_gate


if __name__ == "__main__":
    repo, batch, record_path, out = sys.argv[1], Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4])
    dosedev2.repo_paths(repo)
    import batch6
    import gate4
    import predict6
    import predict6_guard
    out.mkdir(parents=True, exist_ok=True)
    record = {x["seed"]: x for x in json.loads(Path(record_path).read_text())["instances"]}
    status = {}
    for m in ("a", "b"):
        status.update({r["id"]: r["status"] for r in json.loads((batch / m / "RUNS.json").read_text())})
    rec = lambda d: json.loads((Path(d) / "record.json").read_text())
    res = []
    for seed in batch6.SEEDS:
        m = batch6.MACHINE_OF[seed]
        mine = {i: s for i, s in status.items() if i.startswith(f"{seed}-")}
        on, off = batch / m / f"{seed}-cal-on", batch / m / f"{seed}-cal-off"
        row = dict(seed=seed, machine=m)
        ref = record[seed]
        if mine.get(f"{seed}-cal-on") != "complete" or mine.get(f"{seed}-cal-off") != "complete":
            assert not ref.get("measured"), seed
            row.update(measured=False, why="a calibration deck did not complete")
            res.append(row)
            continue
        scans, ones = {}, {}
        for c, kind in predict6.CROSSINGS:
            i = f"{seed}-scan-{c}-{kind}"
            if mine.get(i) == "complete":
                r = rec(batch / m / i)
                scans[(c, kind)] = dict(r["result"], u0_V=r["u0_V"])
        for c in ("a", "b"):
            i = f"{seed}-onesided-{c}"
            if mine.get(i) == "complete":
                r = rec(batch / m / i)
                ones[c] = dict(r["result"], u0_V=r["u0_V"])
        bf = None
        if mine.get(f"{seed}-bothfire-c") == "complete":
            r = rec(batch / m / f"{seed}-bothfire-c")
            bf = dict(r["result"], u0_V=r["u0_V"])
        with mock.patch.object(predict6.P, "instance", predict6_guard.guarded_instance):
            x = predict6.predict_instance(seed, m, mine, on, off, scans, ones, bf)
        x = json.loads(json.dumps(x, default=str)) if False else x
        # guard: the batch's own record
        for k in ("measured", "eligible", "needs", "room_at_K3"):
            assert json.loads(json.dumps(x.get(k), default=str)) == ref.get(k), (seed, k, x.get(k), ref.get(k))
        if "budgets" in x:
            assert json.loads(json.dumps(x["budgets"], default=str)) == ref["budgets"], (seed, "budgets")
        row.update(measured=bool(x.get("measured")), eligible_K0_frozen=bool(x.get("eligible")), gate_K0_in_the_record=ref.get("gate_K0"),
                   why=(x.get("why_not_measured") or x.get("why_not_eligible") or [None])[0])
        if "budgets" not in x:
            res.append(row)
            continue
        t, dose, _ = predict6.table(on, off)
        w = predict6.deck_w(on, predict6.doses_V(dose))
        t2 = predict6.mapped(t, w, predict6.anchors({k: F(scans[k]["s_star"]) for k in predict6.CROSSINGS}))
        assert x["room"] == {K: predict6.P.room(t2, x["needs"], predict6.lay_of(x), x["budgets"][K]) for K in ("K0", "K3")}, (seed, "not the table predict_instance used")
        y, report = t1_gate.one_port(x, t2)
        g = x["guarded"]["dose"]
        st = lambda v, c: float(F(v, g[c] if c == "c" else 2 * g[c]))
        S = {k: F(scans[v]["s_star"]) for k, v in (("a", ("a", "pair")), ("b", ("b", "pair")), ("c1", ("c", "line1")), ("c2", ("c", "line2")))}
        import math
        margins = {k: dict(below=float(s - (math.ceil(s) - 1)), above=float(math.ceil(s) - s)) for k, s in S.items()}
        row.update(needs=x["needs"], Q=(x["Q1"], x["Q2"]),
                   frozen=dict(eligible_K0=x["eligible"], room_at_K3=x["room_at_K3"], counts_N_out=x["counts_N_out"], verdicts=gate4.verdicts(x),
                               c_without_room_K3=x["room"]["K3"]["c"]["without_room"], a_without_room_K3=x["room"]["K3"]["a"]["without_room"],
                               b_without_room_K3=x["room"]["K3"]["b"]["without_room"]),
                   one_port=dict(eligible_K0=y["eligible"], room_at_K3=y["room_at_K3"],
                                 counts_N_out=dict(a=y["room_at_K3"]["a"], b=y["room_at_K3"]["b"], c=all(y["room_at_K3"].values())),
                                 verdicts=gate4.verdicts(y), c_without_room_K3=y["room"]["K3"]["c"]["without_room"]),
                   budgets_stages=dict(a=st(x["budgets"]["K3"]["a"]["training"], "a"), b=st(x["budgets"]["K3"]["b"]["training"], "b"),
                                       c_training=st(x["budgets"]["K3"]["c"]["training"], "c"), c_testing_two_ports=st(x["budgets"]["K3"]["c"]["testing"], "c"),
                                       c_testing_one_port=st(y["budgets"]["K3"]["c"]["testing"], "c")),
                   budgets_units=dict(frozen=x["budgets"], one_port_c_testing={K: y["budgets"][K]["c"]["testing"] for K in ("K0", "K3")}),
                   margins_stages=margins, detail=report)
        for name, inst in (("frozen", x), ("oneport", y)):
            predict6.gate_file([inst], out / f"Gate7_{seed}_{name}.lean")
        res.append(row)
    with_pred = [r for r in res if "frozen" in r]
    summary = dict(
        instances=len(res), measured=sum(bool(r.get("measured")) for r in res), with_a_prediction=len(with_pred),
        eligible_K0_frozen=[r["seed"] for r in with_pred if r["frozen"]["verdicts"]["K0"]],
        eligible_K0_one_port=[r["seed"] for r in with_pred if r["one_port"]["verdicts"]["K0"]],
        c_room_K3_frozen=[r["seed"] for r in with_pred if r["frozen"]["room_at_K3"]["c"]],
        c_room_K3_one_port=[r["seed"] for r in with_pred if r["one_port"]["room_at_K3"]["c"]],
        counts_N_out_c_frozen=[r["seed"] for r in with_pred if r["frozen"]["counts_N_out"]["c"]],
        counts_N_out_c_one_port=[r["seed"] for r in with_pred if r["one_port"]["counts_N_out"]["c"]],
        a_room_K3=[r["seed"] for r in with_pred if r["frozen"]["room_at_K3"]["a"]], b_room_K3=[r["seed"] for r in with_pred if r["frozen"]["room_at_K3"]["b"]],
        all_three_K3_frozen=[r["seed"] for r in with_pred if all(r["frozen"]["room_at_K3"].values())],
        all_three_K3_one_port=[r["seed"] for r in with_pred if all(r["one_port"]["room_at_K3"].values())])
    (out / "C7_SHARE.json").write_text(json.dumps(dict(summary=summary, instances=res), indent=1, default=str) + "\n")
    print(json.dumps(summary, indent=1))
    for r in res:
        if "frozen" not in r:
            print(r["seed"], "no prediction:", r.get("why"))
            continue
        print(r["seed"], "needs", r["needs"], "| frozen K0", r["frozen"]["verdicts"]["K0"], "K3 rooms", r["frozen"]["room_at_K3"], "| one-port K0", r["one_port"]["verdicts"]["K0"], "c K3",
              r["one_port"]["room_at_K3"]["c"], r["one_port"]["c_without_room_K3"], "| stages", {k: round(v, 3) for k, v in r["budgets_stages"].items()},
              "| c margins", {k: (round(v["below"], 3), round(v["above"], 3)) for k, v in r["margins_stages"].items() if k.startswith("c")})
