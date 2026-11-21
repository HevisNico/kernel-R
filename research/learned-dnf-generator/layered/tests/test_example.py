"""Test (a) of the layered generator (LAYERED_GENERATOR_DESIGN.md 4): the repository's own example, as a spec.

LayeredMonotoneExample.lean (main, `circuit`, `train`, `test`, lines 34-133) is transcribed here as a spec: the same
cells (`canonical`), wiring, stimuli of the active groups, clock, dates, scores and emissions. So are the five
rejection fixtures of LayeredMonotoneCheckerExamples.lean:18-42 and 55-68. The test requires:

1. the mirror: the four checkers true on the example (as the file's accepted_* theorems, :47-53), and each fixture
   false on the checker its `example` names;
2. a Lean file asserting the mirror's per-checker values for all six (written to OUT.lean), to be compiled by
   gencheck_layered.sh: it compiles only if Lean agrees.

  python -I tests/test_example.py OUT.lean
"""
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import lemit  # noqa: E402
import lmirror  # noqa: E402
import lspec  # noqa: E402

S = lambda x: str(F(x))
CLOCK = dict(skew="0", deadline="1", duration="2")              # Example.clock, :34


def canonical(gate):
    """LayeredMonotoneCharacterization.lean:42-51."""
    return dict(initialGain=[0, 0], help=4 if gate == "on" else 0, threshold=6 if gate == "both" else 2,
                trainError=1, testError=1, dose=4, maxWrites=1, rail=5)


TERM = [{0, 1}, {2, 3}]                                         # Example.term, :40-41
SRC = [[0, 1], [2, 3]]                                          # Example.source, :43-44


def slot(start, x, value, fires):                               # Example.slot, :62-63
    start = F(start)
    return dict(start=S(start), arrivals=[S(start) if b else None for b in x], emissions=[S(start + 1)] if fires else [], value=value)



def scores(f):
    """The four reference scores of a score function on Pattern 2, in maskIndex order (port 0 most significant)."""
    return [f((False, False)), f((False, True)), f((True, False)), f((True, True))]


AND = lambda y: 4 * y[0] + 4 * y[1]                             # :95-96
COPY = lambda y: 4 if y[0] else 0                               # :98
OR = lambda y: (6 if y[1] else 4) if y[0] else (4 if y[1] else 0)   # :100-101


def first_mask(x, i):
    return (SRC[i][0] in x, SRC[i][1] in x)


def term_fires(x, i):
    m = first_mask(x, i)
    return m[0] and m[1]


def arrivals(t, x):
    return [S(t) if j in x else None for j in range(4)]


def first_replay(t, x):                                         # :103-105
    return dict(arrivals=arrivals(t, x),
                layers=[[dict(read=slot(t, first_mask(x, i), AND(first_mask(x, i)), term_fires(x, i)), scores=scores(AND)) for i in (0, 1)]])


def copy_replay(t, x):                                          # :107-110
    rt = first_replay(t, x)
    rt["layers"].append([dict(read=slot(F(t) + 1, (term_fires(x, i), False), COPY((term_fires(x, i), False)), term_fires(x, i)),
                              scores=scores(COPY)) for i in (0, 1)])
    return rt


def replay(t, x):                                               # :112-115
    rt = copy_replay(t, x)
    tf = (term_fires(x, 0), term_fires(x, 1))
    rt["layers"].append([dict(read=slot(F(t) + 2, tf, OR(tf), tf[0] or tf[1]), scores=scores(OR))])
    return rt


def mask_of(w):
    return {j for j in range(4) if w >> (3 - j) & 1}


def example():
    n1 = [dict(name=f"and{i}", gate="both", source=SRC[i], delay=["0", "0"], stimulus=[sorted(TERM[i]), None], **canonical("both")) for i in (0, 1)]
    n2 = [dict(name=f"copy{i}", gate="copy", source=[i, None], delay=["0", "0"], stimulus=[[0, 1, 2, 3], None], **canonical("copy")) for i in (0, 1)]
    n3 = [dict(name="or", gate="either", source=[0, 1], delay=["0", "0"], stimulus=[sorted(TERM[0]), sorted(TERM[1])], **canonical("either"))]
    full = {0, 1, 2, 3}
    t1 = [[[dict(replay=dict(arrivals=arrivals(20 * i + 10 * r, TERM[i]), layers=[]),
                 read=slot(20 * i + 10 * r, (True, True), 0 if r == 0 else 8, r != 0)) for r in (0, 1)]] for i in (0, 1)]   # :123-125
    t2 = [[[dict(replay=first_replay(40 + 20 * i + 10 * r, full),
                 read=slot(40 + 20 * i + 10 * r + 1, (True, False), 0 if r == 0 else 4, r != 0)) for r in (0, 1)]] for i in (0, 1)]   # :127-129
    t3 = [[[dict(replay=copy_replay(80 + 20 * g + 10 * r, TERM[g]),
                 read=slot(80 + 20 * g + 10 * r + 2, (g == 0, g == 1), 0 if r == 0 else 4, r != 0)) for r in (0, 1)] for g in (0, 1)]]  # :131-133
    return dict(tag="Ex", M=4, layers=[dict(timing=CLOCK, nodes=n1), dict(timing=CLOCK, nodes=n2), dict(timing=CLOCK, nodes=n3)],
                training=[t1, t2, t3], tests=[replay(120, mask_of(w)) for w in range(16)],
                function="(x 0 && x 1) || (x 2 && x 3)",
                lean=dict(namespace="LearnedCoincidence.Layered.Generated", source="LayeredMonotoneExample, transcribed"))


def expected(x):
    return (0 in x and 1 in x) or (2 in x and 3 in x)


def edit_final(raw, tag, choose, value, edit):                  # CheckerExamples.editFinal, :10-16
    d = copy.deepcopy(raw)
    d["tag"] = tag
    for w, rt in enumerate(d["tests"]):
        if choose(mask_of(w)):
            c = rt["layers"][2][0]
            c["read"]["value"] = value
            c["scores"] = [edit(y, s) for y, s in zip([(False, False), (False, True), (True, False), (True, True)], c["scores"])]
    return d


def fixtures(ex):
    out = {}
    sep = copy.deepcopy(ex)
    sep["tag"] = "ExReplay0"
    sep["tests"] = [replay(0, mask_of(w)) for w in range(16)]                       # :55, Example.replay 0
    out["ExReplay0"] = (sep, "checkLayeredSeparation")
    out["ExSilent"] = (edit_final(ex, "ExSilent", lambda x: not expected(x), -2, lambda y, s: s), "checkLayeredReadCalibration")   # :18-19
    out["ExAnchor"] = (edit_final(ex, "ExAnchor", lambda x: 0 in x and 1 in x and not (2 in x and 3 in x), 2,
                                  lambda y, s: 2 if y[0] and not y[1] else s), "checkLayeredReadCalibration")                    # :21-23
    out["ExSubmask"] = (edit_final(ex, "ExSubmask", lambda x: x == {0, 1, 2, 3}, 3,
                                   lambda y, s: 3 if y[0] and y[1] else s), "checkLayeredReadCalibration")                       # :25-27
    low = copy.deepcopy(ex)
    low["tag"] = "ExLower"
    low["training"][2][0][0][0]["replay"]["layers"][0][1]["read"]["value"] = -2     # :31-42: OR lesson g=0, r=0, AND cell 1
    out["ExLower"] = (low, "checkLayeredTrainingCalibration")
    return out


def main():
    out_lean = Path(sys.argv[1])
    ex = example()
    s = lspec.load(ex)
    conj, pc, fails = lmirror.verdicts(s)
    bad = 0
    print(f"Ex: mirror {pc}; failing {fails[:5]}")
    if not conj:
        bad += 1
        print("  FAIL: the example must pass all four checkers (CheckerExamples accepted_*, :47-53)")
    pred_ok = all(lmirror.predict(s, mask_of(w))[0] == expected(mask_of(w)) for w in range(16))
    print(f"Ex: mirror predict equals (A and B) or (C and D) on the cube: {pred_ok}")
    bad += not pred_ok
    specs, pcs, report = [s], {"Ex": pc}, [dict(tag="Ex", per_checker=pc, failing=[])]
    for tag, (raw, checker) in fixtures(ex).items():
        sf = lspec.load(raw)
        c, p, f = lmirror.verdicts(sf)
        kinds = sorted({(ch, k) for ch, k, _ in f})
        ok = p[checker] is False
        bad += not ok
        print(f"{tag}: mirror {p}; expected {checker} = false: {'yes' if ok else 'NO'}; failing kinds {kinds}")
        specs.append(sf)
        pcs[tag] = p
        report.append(dict(tag=tag, per_checker=p, expected_false=checker, failing_kinds=kinds))
    out_lean.write_text(lemit.lean_file(specs, pcs, "LayeredMonotoneExample and the five fixtures of LayeredMonotoneCheckerExamples"))
    (out_lean.with_suffix(".json")).write_text(json.dumps(report, indent=1) + "\n")
    print(f"test (a), mirror part: {'passed' if not bad else 'FAILED'}; Lean file written: {out_lean}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
