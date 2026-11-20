"""The legacy adapter (GENERATOR_DESIGN.md 3.6): a gate4 instance dict (campaign 5's PREDICTED.json and CASES.json,
campaign 6's PREDICTED.json) as a generator spec of shape Cascade 2 1 4, the function (A and B) or (C and D).

The frozen campaign-5 modules are imported as libraries from a campaign-5 directory given by the caller (C5_DIR,
default: the checkout's research/learned-dnf-circuit-campaign-5). Nothing of them is copied or edited:
`gate4.verdicts` gives the external verdict, `predicted` the constants THETA, RAIL and the slot timings.
"""
import importlib
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent

GATE4_NAMESPACE = "LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4"
LETTERS = "ABCD"


def frozen(c5_dir=None):
    """(gate4, predicted) imported from the frozen campaign-5 directory."""
    d = Path(c5_dir) if c5_dir else HERE.parent / "learned-dnf-circuit-campaign-5"
    if str(d) not in sys.path:
        sys.path.insert(0, str(d))
    return importlib.import_module("gate4"), importlib.import_module("predicted")


def key_of(word):
    """gate4.key_of: the letters of a mask index (A the most significant bit)."""
    return "".join(x for i, x in enumerate(LETTERS) if word & (8 >> i)) or "-"


def spec_of(x, source, c5_dir=None, budgets=("K0", "K3")):
    """A raw spec (spec.load input) from a gate4 instance dict x, with gate4's tag x['tag'] and its verdicts."""
    gate4, P = frozen(c5_dir)
    g, h, d = x["guarded"]["gain"], x["guarded"]["help"], x["guarded"]["dose"]
    o = x["observation"]
    b = {K: dict(first=dict(training=[x["budgets"][K][c]["training"] for c in "ab"], testing=[x["budgets"][K][c]["testing"] for c in "ab"]),
                 second=dict(training=[x["budgets"][K]["c"]["training"]], testing=[x["budgets"][K]["c"]["testing"]])) for K in budgets}
    v = gate4.verdicts(x)
    rd = lambda c: dict(start=c["start"], arrivals=list(c["arrivals"]), emissions=list(c["emissions"]), value=c["value"])
    t = lambda q: {k: str(v) for k, v in q.items()}
    return dict(
        tag=x["tag"], shape=dict(A=2, B=1, M=4), inputs=list(LETTERS),
        first=dict(cells=["a", "b"], terms=[[0, 1], [2, 3]],
                   initialGain=[[g["a1"], g["a2"], 0, 0], [0, 0, g["b1"], g["b2"]]],
                   help=[h["a"], h["b"]], threshold=[P.THETA, P.THETA], dose=d["a"], maxWrites=x["Q1"], rail=P.RAIL),
        second=dict(cells=["c"], lines=[[0, 1]], alwaysFire=[False], initialGain=[[g["c1"], g["c2"]]],
                    help=[h["c"]], threshold=[P.THETA], dose=d["c"], maxWrites=x["Q2"], rail=P.RAIL),
        delay=[["3/2", "3/2"]], heldOut=[],
        timing=dict(left=t(dict(skew=P.SKEW_A, deadline=P.DEADLINE_A, duration=P.DURATION_A)),
                    right=t(dict(skew=P.SKEW_C, deadline=P.DEADLINE_C, duration=P.DURATION_C))),
        budgets=b,
        observation=dict(
            firstTrain=[[rd(c) for c in row] for row in o["firstTrain"]],
            teach=[[rd(c) for c in row] for row in o["teach"]],
            secondTrain=[rd(c) for c in o["secondTrain"]],
            firstTest=[[rd(c) for c in o["firstTest"][key_of(w)]] for w in range(16)],
            secondTest=[[rd(o["secondTest"][key_of(w)])] for w in range(16)],
            scores=[[[o["scores"][key_of(w)][m] for m in ("-", "2", "1", "12")]] for w in range(16)]),
        verdicts={K: v[K] for K in budgets},
        lean=dict(style="gate4", namespace=GATE4_NAMESPACE, source=source, derive=True))


def lean_file(xs, source, c5_dir=None):
    """The gate4 file of instances xs (dicts with a tag), written by the generator from their specs."""
    import emit
    import spec
    specs = [spec.load(spec_of(x, source, c5_dir)) for x in xs]
    verdicts = {(s["tag"], K): s["verdicts"][K] for s in specs for K in s["budgets"]}
    return emit.lean_file(specs, verdicts, source)
