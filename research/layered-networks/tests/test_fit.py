"""Tests of fit.py without a simulator: python3 -B tests/test_fit.py"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE))
import fit  # noqa: E402
import spec as specmod  # noqa: E402

THETA = fit.THETA


def test_solve_exact():
    rows = [[1, 0, 0], [1, 1, 0], [1, 1, 1], [1, 0, 1]]
    x = [F(3), F(2), F(5)]
    rhs = [sum(a * b for a, b in zip(r, x)) for r in rows]
    assert fit.solve(rows, rhs) == x


def test_read_budget_known_values():
    # K0: eps + ceil(0.030 * sum s); K3 one port: least m with m^2 >= 9 s^2 (w^2 + b^2 + n d^2)
    assert fit.read_budget(10, [F(10000)], [0], 0) == 10 + 300
    s, n = F(10000), 4
    X = 9 * s * s * (F("0.094") ** 2 + F("0.111") ** 2 + n * F("0.009") ** 2)
    m = fit.read_budget(0, [s], [n], 3)
    assert m * m >= X and (m - 1) ** 2 < X


def copy_cell(**kw):
    p = dict(gate="copy", help=0, gain={1: 60000, 2: 0}, dose=11000, threshold=THETA, maxWrites=5, rail=10 * THETA,
             trainError=300, testError=300)
    p.update(kw)
    return p


def test_cell_valid_copy_and_stop():
    p = copy_cell()
    assert fit.stop(p, 0) == 4                    # 60000 + 4 * 11000 = 104000 >= THETA, 93000 < THETA
    ok, clauses = fit.cell_valid(p)
    assert ok, [c for c in clauses if c[1] <= 0]
    ok3, clauses3 = fit.cell_valid(copy_cell(trainError=5000, testError=5000))
    failing = [n for n, v in clauses3 if v <= 0]
    assert not ok3 and failing == ["g0: stop margin", "anchor (1,)"], failing    # 104000 < THETA + 5000
    assert dict(clauses3)["g0: early silence k=3"] == THETA - (93000 + 5000)


def test_cell_valid_both_needs_silent_singles():
    p = dict(gate="both", help=0, gain={1: 20000, 2: 20000}, dose=8000, threshold=THETA, maxWrites=6, rail=10 * THETA,
             trainError=200, testError=200)
    st = fit.stop(p, 0)                           # 40000 + 16000 k >= THETA at k = 4
    assert st == 4
    ok, clauses = fit.cell_valid(p)
    assert ok, [c for c in clauses if c[1] <= 0]
    assert dict(clauses)["silent mask (1,)"] == THETA - (20000 + 8000 * 4 + 200)


def test_dev_records_reproduce():
    """The committed dev records give the committed verdicts."""
    for name in ("not1", "andor3"):
        out = HERE / "dev" / f"cal_{name}"
        if not (out / "fit.json").exists():
            continue
        s = specmod.load(HERE / "specs" / f"{name}.json")
        r = fit.js(fit.instance_fit(s, json.loads((out / "record.json").read_text())))
        assert json.loads(json.dumps(r)) == json.loads((out / "fit.json").read_text())


if __name__ == "__main__":
    n = 0
    for name, f in list(globals().items()):
        if name.startswith("test_") and callable(f):
            f()
            n += 1
            print("ok", name)
    print(n, "tests passed")
