"""Development only. A5: POST-HOC and EXPLORATORY. This is NOT campaign 6's frozen rule and not a claim.

  post_d_a5.py REPO CONFIG.json POST_D.json OUT.json

The same five cases as A4 of post_d.py (the nominal cell at 1x and 2x; decision 5's constants, the constants read at
each dose, and at 2x the same with a measure term of 0.030 mV), with ONE change to the rule: for cell c, the reads
with one line or none (test line p alone, test empty, the guarded empty mask) are judged with the ONE-port budget
at that line's need, instead of the two-port testing budget. The both-lines read keeps the two-port budget.
The empty reads have no line: they take the larger of the two lines' one-port budgets.

How: nothing frozen is edited. The instance is predicted by the frozen functions exactly as in A4
(post_d.frozen_prediction's path: predict6.table, deck_w, measure_instance, predicted.instance, predict6.augmented).
The one-port testing budget is predicted.read_budget(eps_c, [s_cp], [n_p], K, const) + H_c + S_c: the frozen function
that the frozen rule already uses for c's training budget. Then c's test reads are judged again by a copy of
predicted.room's lines 320 to 328 in which `te` is the one-port budget for the reads named above; everything else in
the room (a, b, c's teaching reads, the rails) is the frozen predicted.room's own output.

Also given, per case: the budgets in stages; the width of the part of a step where a line's crossing can sit and
leave room, 1 - tr - te, under the frozen rule and under A5; and whether the both-lines read, with its two-port
budget, limits c: the frozen check `pair >= max(z1, z2) + te`, and 2 x need - (s1 + s2) against te in stages.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev2
import post_d


def case(label, cfg, sets, ref):
    import c4
    import predict6
    P = predict6.P
    THETA = P.THETA
    rec = lambda d: json.loads((Path(d) / "record.json").read_text())
    scans = {}
    for name, d in cfg["scans"].items():
        c, kind = name.split("-")
        r = rec(d)
        scans[(c, kind)] = dict(r["result"], u0_V=r["u0_V"])
    ones = {c: dict(rec(d)["result"], u0_V=rec(d)["u0_V"]) for c, d in cfg["onesided"].items()}
    bf = dict(rec(cfg["bothfire"])["result"], u0_V=rec(cfg["bothfire"])["u0_V"])
    on, off = cfg["cal_on"], cfg["cal_off"]
    t, dose, bad = predict6.table(on, off)
    D = predict6.doses_V(dose)
    w = predict6.deck_w(on, D)
    statuses = {f"{label}-{k}": "complete" for k in ["cal-on", "cal-off", "bothfire-c", *[f"scan-{n}" for n in cfg["scans"]], *[f"onesided-{c}" for c in ones]]}
    why, data = predict6.measure_instance(label, statuses, t, dose, bad, scans, ones, predict6.deck_u0(on), bf, w)
    assert not why, why
    t2 = data["t2"]
    S = {k: F(scans[v]["s_star"]) for k, v in post_d.KEY_OF_SCAN.items()}
    out = {}
    for name, (const, term_mV) in sets.items():
        H = dict(data["H"])
        if term_mV is not None:                              # as post_d.frozen_prediction
            an = dict(d=data["anchors"]["d"], d_c=data["anchors"]["d_c"])
            H30 = dict(a=math.ceil(F(str(term_mV)) / min(D[("a", 1)], D[("a", 2)]) * 2 * an["d"]), b=math.ceil(F(str(term_mV)) / min(D[("b", 1)], D[("b", 2)]) * 2 * an["d"]),
                       c=max(math.ceil(F(str(term_mV)) / D[("c", p)] * an["d_c"]) for p in (1, 2)))
            H = {c: max(H[c], H30[c]) for c in H}
        raw = P.instance(label, t2, dose, [], const)
        x = predict6.augmented(raw, H, data["S"], t2)
        assert x["room_at_K3"] == ref[name]["room_at_K3"] and x["budgets"]["K3"]["c"]["testing"] == round(ref[name]["cells"]["c"]["K3"]["testing_stages"] * x["guarded"]["dose"]["c"]), \
            "not the case A4 computed"
        n = x["needs"]
        n1, n2 = n["c1"], n["c2"]
        lay = predict6.lay_of(x)
        L = lay("c")
        g = x["guarded"]["dose"]["c"]
        res = dict(constants=const, measure_term_mV=term_mV, needs=n, frozen_room_at_K3=x["room_at_K3"])
        for K, kind in (("K0", 0), ("K3", 3)):
            tr, te2 = x["budgets"][K]["c"]["training"], x["budgets"][K]["c"]["testing"]
            te1 = {p: P.read_budget(raw["epsilon"]["c"], [raw["sensitivity"][f"c{p}"]], [nn], kind, const) + H["c"] + data["S"]["c"] for p, nn in ((1, n1), (2, n2))}
            te0 = max(te1.values())
            frozen = x["room"][K]["c"]["reads"]
            rr = {k: v for k, v in frozen.items() if k.startswith("teaching") or k.startswith("guarded gain")}       # unchanged reads
            hi, lo = max(n1, n2), min(n1, n2)
            # a copy of predicted.room, lines 320 to 328, with te -> te0 (empty reads), te1[p] (one line), te2 (both lines)
            rr[f"test empty stage {hi}, silent"] = L["help"]["c"] + te0 < THETA and abs(t2[("c", hi, "empty")]["Z"] - L["help"]["c"]) <= te0
            z = {}
            for p, nn in ((1, n1), (2, n2)):
                z[p] = t2[("c", nn, f"port {p}")]["Z"]
                rr[f"test line {p} alone stage {nn}, FIRE"] = z[p] - te1[p] >= THETA and z[p] >= P.G(L, "c", nn, (p,)) - te1[p]
            pair = min(t2[("c", lo, "both")]["Z"], t2[("c", lo, P.SKEWED)]["Z"])
            rr[f"test both lines stage {lo}, FIRE"] = rr[f"test line 1 alone stage {n1}, FIRE"] and rr[f"test line 2 alone stage {n2}, FIRE"] and pair >= max(z[1], z[2]) + te2
            rr["guarded empty mask silent (Disjunctions.check)"] = L["help"]["c"] + te0 < THETA
            assert set(rr) == set(frozen), (sorted(rr), sorted(frozen))
            st = lambda v: float(F(v, g))
            margins = {p: dict(below=float(S[f"c{p}"] - (math.ceil(S[f"c{p}"]) - 1)), above=float(math.ceil(S[f"c{p}"]) - S[f"c{p}"])) for p in (1, 2)}
            res[K] = dict(
                c_reads_frozen=frozen, c_reads_A5=rr, c_all_frozen=all(frozen.values()), c_all_A5=all(rr.values()),
                c_without_room_frozen=[k for k, v in frozen.items() if not v], c_without_room_A5=[k for k, v in rr.items() if not v],
                a_all=x["room"][K]["a"]["all"], b_all=x["room"][K]["b"]["all"],
                a_reads=x["room"][K]["a"]["reads"], b_reads=x["room"][K]["b"]["reads"],
                budgets_stages=dict(c_training=st(tr), c_testing_two_ports_frozen=st(te2), c_testing_one_port_A5={str(p): st(v) for p, v in te1.items()},
                                    a=float(F(x["budgets"][K]["a"]["training"], 2 * x["guarded"]["dose"]["a"])), b=float(F(x["budgets"][K]["b"]["training"], 2 * x["guarded"]["dose"]["b"]))),
                width_of_the_part_of_a_step_with_room=dict(frozen=1 - st(tr) - st(te2), A5={str(p): 1 - st(tr) - st(te1[p]) for p in (1, 2)}),
                slack_stages=dict(frozen={str(p): dict(below_minus_training=margins[p]["below"] - st(tr), above_minus_testing=margins[p]["above"] - st(te2)) for p in (1, 2)},
                                  A5={str(p): dict(below_minus_training=margins[p]["below"] - st(tr), above_minus_testing=margins[p]["above"] - st(te1[p])) for p in (1, 2)}),
                both_lines_read=dict(two_port_budget_stages=st(te2), frozen_check_pair_minus_largest_single_stages=st(pair - max(z[1], z[2])),
                                     frozen_check_slack_stages=st(pair - max(z[1], z[2]) - te2), pair_minus_threshold_stages=st(pair - THETA),
                                     two_needs_minus_s1_plus_s2_stages=float(2 * lo - (S["c1"] + S["c2"])) if n1 == n2 else None,
                                     needs_minus_crossings_stages=float(n1 + n2 - (S["c1"] + S["c2"])),
                                     limits_c=not (pair >= max(z[1], z[2]) + te2)))
        out[name] = res
    return out


if __name__ == "__main__":
    repo, config, post_path, dest = sys.argv[1:5]
    dosedev2.repo_paths(repo)
    import c4
    cfg = json.loads(Path(config).read_text())["doses"]
    post = json.loads(Path(post_path).read_text())["A4_frozen_budget"]
    measured = post["constants_read_at_each_dose"]
    res = dict(what="A5: post-hoc and exploratory; not campaign 6's frozen rule; one change: c's reads with one line or none are judged with the one-port budget")
    for l in ("1x", "2x"):
        sets = {"decision 5's constants": (dict(c4.DECISION5), None), "the constants read at this dose": (measured[l], None)}
        if l == "2x":
            sets["the constants read at this dose, measure term 0.030 mV"] = (measured[l], "0.030")
        res[l] = case(l, cfg[l], sets, post[l]["sets"])
    Path(dest).write_text(json.dumps(res, indent=1, default=str) + "\n")
    f = lambda v: round(v, 4) if isinstance(v, float) else v
    for l in ("1x", "2x"):
        for name, x in res[l].items():
            k = x["K3"]
            print(l, "|", name)
            print("   K3 room: a", k["a_all"], "b", k["b_all"], "c frozen", k["c_all_frozen"], "c A5", k["c_all_A5"], "| without room, frozen:", k["c_without_room_frozen"], "| A5:", k["c_without_room_A5"])
            print("   budgets", {a: (f(b) if not isinstance(b, dict) else {p: f(q) for p, q in b.items()}) for a, b in k["budgets_stages"].items()})
            print("   width", f(k["width_of_the_part_of_a_step_with_room"]["frozen"]), {p: f(q) for p, q in k["width_of_the_part_of_a_step_with_room"]["A5"].items()})
            print("   slack A5", {p: {a: f(b) for a, b in q.items()} for p, q in k["slack_stages"]["A5"].items()})
            print("   both lines", {a: f(b) for a, b in k["both_lines_read"].items()})
            print("   K0 room: c frozen", x["K0"]["c_all_frozen"], "c A5", x["K0"]["c_all_A5"])
