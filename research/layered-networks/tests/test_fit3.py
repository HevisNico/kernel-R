"""Tests of fit3.py on the committed 9803 stage-D record (no simulation). Run: python3 -B tests/test_fit3.py"""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import fit  # noqa: E402
import fit3  # noqa: E402
import records2  # noqa: E402
import scores  # noqa: E402
import spec  # noqa: E402
import stage_d  # noqa: E402


def fit_cell(rule, c, layer, idx):
    s = spec.load(HERE / "specs/xor3.json")
    rec = records2.load(HERE / "dev/stage_d_xor3")
    v = stage_d.cell_view(rec, c, layer)
    with fit3.rule(rule):
        return fit.cell_fit(s, v, scores.readout(s, v), c, layer, idx)


def test_either_one_port():
    mx, op = fit_cell("max", "c2_0", 2, 0), fit_cell("one-port", "c2_0", 2, 0)
    assert mx["budgets"]["K3"]["testError"] == 6550 and mx["verdicts"]["K3"]["min_slack"]["anchor (2,)"] == -364
    assert op["budgets"]["K3"]["testError"] == 3371 == op["budgets"]["K3"]["trainError"]
    assert op["verdicts"]["K3"]["ok"] and op["testError_rule"] == "one-port"
    assert op["budgets"]["K3"]["trainError"] == mx["budgets"]["K3"]["trainError"]       # training unchanged
    assert fit.cell_fit is fit3._cell_fit and fit.read_budget is fit3._read_budget     # restored


def test_other_gates_unchanged():
    for c, layer, idx in (("c1_0", 1, 0), ("c3_0", 3, 0)):
        assert fit_cell("max", c, layer, idx)["budgets"] == fit_cell("one-port", c, layer, idx)["budgets"]


if __name__ == "__main__":
    test_either_one_port()
    test_other_gates_unchanged()
    print("2 tests passed")
