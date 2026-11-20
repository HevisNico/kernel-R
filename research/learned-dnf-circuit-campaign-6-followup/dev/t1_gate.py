"""Development only, EXPLORATORY: campaign 6's gate file for the nominal cell at each dose, written by the frozen
generator (campaign 5's gate4.py through campaign 6's predict6.gate_file), once as frozen and once with ONE change:
c's testingError is the one-port budget of DOSE_REPORT.md 5.5. Not campaign 6's rule and not a claim.

  t1_gate.py REPO CONFIG.json OUT_DIR

CONFIG.json is post_d.py's (POST_D_CONFIG.json). No simulation and no Lean here: this only writes the Lean files and
GATE_INPUT.json. The files are then checked by campaign 5's check.sh, as campaign 6's predict6.gate_each does.

Per dose (1x: the rehearsal r3's none-a; 2x: step B's runs):
1. x = predict6.predict_instance(...), the frozen prediction with decision 5's constants, unchanged.
2. "frozen": predict6.gate_file([x], OUT_DIR/Gate6_<dose>_frozen.lean). The control: the frozen budgets and the
   frozen verdicts (gate4.verdicts reads x["eligible"] and x["room_at_K3"]).
3. "oneport": a copy of x in which, for K = 0 and K = 3,
     budgets[K]["c"]["testing"] = max over the two lines of
         predicted.read_budget(eps_c, [s_cp], [n_p], K, decision 5) + H_c + S_c
   (one number, because the Lean structure has one testingError per cell), and the verdict fields are set to what
   the Python then says: c's room is judged again by a copy of predicted.room's lines 320 to 328 with that number
   for the reads with one line or none, and the frozen two-port budget kept for the both-lines read (as section
   5.5; Lean puts no budget on that read); a and b keep the frozen room. eligible = every cell has room at K = 0;
   room_at_K3 likewise. Nothing else of x is touched: the guarded tuple, the needs, the observation, the training
   errors and a's and b's testing errors are the frozen ones.
   predict6.gate_file([that copy], OUT_DIR/Gate6_<dose>_oneport.lean).
gate4 writes `checks ... = true` where the verdict it is given is true and `= false` elsewhere, so each file
compiles only if Lean agrees with the verdict written in GATE_INPUT.json.
"""
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev2


def instance(label, cfg):
    """The frozen prediction of the nominal cell at one dose: predict6.predict_instance on its measures."""
    import predict6
    rec = lambda d: json.loads((Path(d) / "record.json").read_text())
    scans = {}
    for name, d in cfg["scans"].items():
        c, kind = name.split("-")
        r = rec(d)
        scans[(c, kind)] = dict(r["result"], u0_V=r["u0_V"])
    ones = {c: dict(rec(d)["result"], u0_V=rec(d)["u0_V"]) for c, d in cfg["onesided"].items()}
    bf = dict(rec(cfg["bothfire"])["result"], u0_V=rec(cfg["bothfire"])["u0_V"])
    statuses = {f"{label}-{k}": "complete" for k in ["cal-on", "cal-off", "bothfire-c", *[f"scan-{n}" for n in cfg["scans"]], *[f"onesided-{c}" for c in ones]]}
    x = predict6.predict_instance(label, "dev", statuses, cfg["cal_on"], cfg["cal_off"], scans, ones, bf)
    assert x.get("measured") and "observation" in x, x.get("why_not_measured")
    # the mapped table that predict_instance used and does not return: the same three frozen calls as measure_instance
    t, dose, _ = predict6.table(cfg["cal_on"], cfg["cal_off"])
    w = predict6.deck_w(cfg["cal_on"], predict6.doses_V(dose))
    an = predict6.anchors({k: F(scans[k]["s_star"]) for k in predict6.CROSSINGS})
    return x, predict6.mapped(t, w, an)


def one_port(x, t2):
    """The copy of x with c's testingError replaced by the one-port budget, and the Python verdicts that go with it."""
    import c4
    import predict6
    P = predict6.P
    y = copy.deepcopy(x)
    n1, n2 = x["needs"]["c1"], x["needs"]["c2"]
    L = predict6.lay_of(x)("c")
    H, S = x["errors_added"]["c"]["H"], x["errors_added"]["c"]["S"]
    report = {}
    for K, kind in (("K0", 0), ("K3", 3)):
        te2 = x["budgets"][K]["c"]["testing"]
        te1 = max(P.read_budget(x["epsilon"]["c"], [x["sensitivity"][f"c{p}"]], [nn], kind, c4.DECISION5) + H + S for p, nn in ((1, n1), (2, n2)))
        y["budgets"][K]["c"]["testing"] = te1
        frozen = x["room"][K]["c"]["reads"]
        rr = {k: v for k, v in frozen.items() if k.startswith("teaching") or k.startswith("guarded gain")}
        hi, lo = max(n1, n2), min(n1, n2)
        # a copy of predicted.room, lines 320 to 328: te -> te1 for the reads with one line or none, te2 kept for both lines
        rr[f"test empty stage {hi}, silent"] = L["help"]["c"] + te1 < P.THETA and abs(t2[("c", hi, "empty")]["Z"] - L["help"]["c"]) <= te1
        z = {}
        for p, nn in ((1, n1), (2, n2)):
            z[p] = t2[("c", nn, f"port {p}")]["Z"]
            rr[f"test line {p} alone stage {nn}, FIRE"] = z[p] - te1 >= P.THETA and z[p] >= P.G(L, "c", nn, (p,)) - te1
        pair = min(t2[("c", lo, "both")]["Z"], t2[("c", lo, P.SKEWED)]["Z"])
        rr[f"test both lines stage {lo}, FIRE"] = rr[f"test line 1 alone stage {n1}, FIRE"] and rr[f"test line 2 alone stage {n2}, FIRE"] and pair >= max(z[1], z[2]) + te2
        rr["guarded empty mask silent (Disjunctions.check)"] = L["help"]["c"] + te1 < P.THETA
        assert set(rr) == set(frozen)
        y["room"][K]["c"] = dict(reads=rr, all=all(rr.values()), without_room=[k for k, v in rr.items() if not v])
        report[K] = dict(c_testing_two_ports=te2, c_testing_one_port=te1, c_training=x["budgets"][K]["c"]["training"],
                         c_room_frozen=x["room"][K]["c"]["all"], c_room_one_port=y["room"][K]["c"]["all"], c_without_room_one_port=y["room"][K]["c"]["without_room"])
    y["eligible"] = all(v["all"] for v in y["room"]["K0"].values())
    y["room_at_K3"] = {c: v["all"] for c, v in y["room"]["K3"].items()}
    return y, report


if __name__ == "__main__":
    repo, config, out = sys.argv[1], sys.argv[2], Path(sys.argv[3])
    dosedev2.repo_paths(repo)
    import gate4
    import predict6
    out.mkdir(parents=True, exist_ok=True)
    cfg = json.loads(Path(config).read_text())["doses"]
    res = {}
    for label in ("1x", "2x"):
        x, t2 = instance(label, cfg[label])
        assert x["room"] == {K: predict6.P.room(t2, x["needs"], predict6.lay_of(x), x["budgets"][K]) for K in ("K0", "K3")}, "not the table predict_instance used"
        y, report = one_port(x, t2)
        for name, inst in (("frozen", x), ("oneport", y)):
            predict6.gate_file([inst], out / f"Gate6_{label}_{name}.lean")
        res[label] = dict(needs=x["needs"], budgets_frozen=x["budgets"], budgets_one_port=y["budgets"], one_port=report,
                          verdict_written_frozen=gate4.verdicts(x), verdict_written_one_port=gate4.verdicts(y),
                          eligible_frozen=x["eligible"], room_at_K3_frozen=x["room_at_K3"], eligible_one_port=y["eligible"], room_at_K3_one_port=y["room_at_K3"],
                          timing_ok=gate4.timing_ok(x["observation"], x["Q1"], x["Q2"]))
    (out / "GATE_INPUT.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
    print(json.dumps(res, indent=1, default=str))
