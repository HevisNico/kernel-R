"""Campaign 5, diagnostic of the gap in P2's interval (coordinator's review 2, B2), before PREDICTION.md is pushed.

  diag5.py OUT.json OUT_DIAG.lean OUT_DIAG_TARGETS.lean

The case P0 of cases5.py with the score of a's pair read at stage 4 set to 102 338, 102 339, 102 340, 102 341 and
102 342 in turn. For each: the frozen prediction (predicted.py, unchanged), its eligibility and reasons, the guarded
tuple of layer 1 as exact rationals before rounding and after, epsilon and the per-cell budgets, and every condition of
the checker mirror (cases.Mirror, unchanged) that fails under beta_0. Then the Lean gate (gate4.lean_file, unchanged)
and the per-checker targets, in the form of cases.lean_targets, for these five variants.
"""
from fractions import Fraction as F
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import predicted as P                                   # noqa: E402
import gate4                                            # noqa: E402
import cases as C4                                      # noqa: E402
import cases5                                           # noqa: E402

KEY = ("a", 4, "both")
SCORES = (102338, 102339, 102340, 102341, 102342)


def exact_layer1(t, Q1):
    """The exact rational least-squares solution of layer 1's guarded fit before rounding: the rows of
    predicted.guarded, rebuilt here, solved by predicted.solve (both unchanged)."""
    cells, reads = P.LAYER1, P.GUARDED_READS_1
    names = [f"h_{c}" for c in cells] + [f"g_{c}{p}" for c in cells for p in (1, 2)] + ["d"]
    rows, rhs = [], []
    for c in cells:
        for k in range(Q1 + 1):
            for r in reads:
                row = [0.0] * len(names)
                row[names.index(f"h_{c}")] = 1
                for q in P.ports(r):
                    row[names.index(f"g_{c}{q}")] = 1
                    row[-1] += k
                rows.append(row)
                rhs.append(t[(c, k, r)]["Z"])
    return {n: (str(v), float(v), round(v)) for n, v in zip(names, P.solve(rows, rhs))}


def main():
    print(c4.require_pinned())
    t0, dose = cases5.base()
    out, cases = [], []
    for s in SCORES:
        t = copy.deepcopy(t0)
        t[KEY]["Z"] = s
        C4.fire_bits(t, KEY)
        x = P.instance(None, t, dose, [], c4.DECISION5)
        conds = C4.conditions(x, 0)
        fails = [dict(checker=ch, kind=k, where=w) for ch, k, w, ok in conds if not ok]
        margins = {}
        m = C4.Mirror(x, 0)
        for a in ("a", "b"):
            nd = m.need(a)
            margins[a] = dict(need=nd, training=m.tr[a], testing=m.te[a],
                              early_silence_stage3=dict(score=m.score(a, 3, C4.TARGET[a]), room=P.THETA - (m.score(a, 3, C4.TARGET[a]) + m.tr[a])),
                              stop_stage4=dict(score=m.score(a, nd, C4.TARGET[a]), room=m.score(a, nd, C4.TARGET[a]) - (P.THETA + m.tr[a])))
        row = dict(exact_layer1=exact_layer1(t, x["Q1"]), score=s, eligible=x.get("eligible"), why_not_eligible=x.get("why_not_eligible"), guarded=x["guarded"],
                   epsilon=x.get("epsilon"), budgets_K0=x["budgets"]["K0"], mirror_K0=C4.per_checker(conds), failing_K0=fails,
                   margins=margins, gate=gate4.verdicts(x))
        out.append(row)
        cases.append(dict(x, tag=f"Z{s}", change=f"pair of a at stage 4: Z = {s}"))
        print(json.dumps(dict(score=s, eligible=row["eligible"], exact_layer1=row["exact_layer1"], help=x["guarded"]["help"], gain=x["guarded"]["gain"], dose=x["guarded"]["dose"],
                              budgets_a=x["budgets"]["K0"]["a"], budgets_b=x["budgets"]["K0"]["b"], margins=margins, failing=fails), default=str))
    Path(sys.argv[1]).write_text(json.dumps(out, indent=1, default=str) + "\n")
    verdicts = {(x["tag"], K): C4.per_checker(C4.conditions(x, K)) for x in cases for K in (0, 3)}
    Path(sys.argv[2]).write_text(gate4.lean_file(cases, "diagnostic of P2's interval, campaign 5"))
    full = C4.lean_targets(cases + [dict(cases[0], tag="P4")], verdicts | {("P4", 0): verdicts[(cases[0]["tag"], 0)], ("P4", 3): verdicts[(cases[0]["tag"], 3)]},
                           Path(sys.argv[2]).stem)
    keep = full.split("/-! P4 (amendment 2")[0]
    keep = "\n".join(l for l in keep.split("\n") if "_P4_" not in l) + "\nend LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4\n"
    Path(sys.argv[3]).write_text(keep)


if __name__ == "__main__":
    main()
