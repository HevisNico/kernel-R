"""The either cell's testError under the one-port rule (DECISIONS_3.md, 2026-11-24). Development only.

fit.py is pushed and kept as it is. Its either-cell testError is the max rule: the larger of the one-port rule
(max_p read_budget(eps, [s_p], [n_p], K)) and the two-port both-lines budget read_budget(eps, [s_1, s_2], [n_1, n_2],
K). Under `rule("one-port")` the both-lines term is dropped, for either cells only: while fit.cell_fit runs on an
either cell, fit.read_budget returns 0 for a two-port call (sens of length 2). In cell_fit an either cell makes exactly
one such call, the both-lines term, so testError = max_p one-port + H + H_drift + H_D4; its trainError and every
other gate's budgets are unchanged. `rule("max")` is fit.py as pushed.

  with fit3.rule("one-port"): ...      fit.cell_fit, fit.instance_fit and everything that calls them (stage_d.predict,
                                       leancal, leancal2) use the one-port rule inside the block
"""
import contextlib
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fit as fitmod  # noqa: E402

RULES = ("one-port", "max")
_cell_fit, _read_budget = fitmod.cell_fit, fitmod.read_budget


def _one_port_cell_fit(s, rec, readout, c, layer, idx):
    if s["layers"][layer - 1][idx]["gate"] != "either":
        return _cell_fit(s, rec, readout, c, layer, idx)

    def rb(eps, sens, writes, K):
        return 0 if len(sens) == 2 else _read_budget(eps, sens, writes, K)
    fitmod.read_budget = rb
    try:
        out = _cell_fit(s, rec, readout, c, layer, idx)
    finally:
        fitmod.read_budget = _read_budget
    if out.get("measured"):
        out["testError_rule"] = "one-port"
    return out


@contextlib.contextmanager
def rule(name):
    assert name in RULES, name
    if name == "max":
        yield
        return
    fitmod.cell_fit = _one_port_cell_fit
    try:
        yield
    finally:
        fitmod.cell_fit = _cell_fit
