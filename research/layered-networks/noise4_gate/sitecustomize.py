"""Loaded by every Python process started with this folder first on PYTHONPATH (indeck_noise4.py sets it).

When LAYERED_K3_BUDGET names a budget file (research/layered-networks/noise4_budget.json) and LAYERED_KIT_PKG the
kit's package folder (research/circuit/inverter/instances), the kit's invinst.gate.allowance is replaced, in this
process, by one that returns K0's allowance unchanged and, at K3, the budget's `allowance_K3` (delta, eta as exact
fractions). The kit's files are not modified; this changes only which allowance its unchanged gate receives.
Any other process is untouched (the variables are unset).
"""
import os

_budget = os.environ.get("LAYERED_K3_BUDGET")
_pkg = os.environ.get("LAYERED_KIT_PKG")
if _budget and _pkg:
    import json
    import sys
    from fractions import Fraction as F
    if _pkg not in sys.path:
        sys.path.insert(0, _pkg)
    import invinst.gate as _gate
    _b = json.loads(open(_budget).read())
    _orig = _gate.allowance

    def allowance(cfg, K):
        if K == 0:
            return _orig(cfg, 0)
        assert K == cfg["gate"]["K3_sigmas"] == _b["K3_sigmas"], (K, cfg["gate"]["K3_sigmas"], _b["K3_sigmas"])
        return dict(delta=F(_b["allowance_K3"]["delta"]), eta=F(_b["allowance_K3"]["eta"]))
    _gate.allowance = allowance
