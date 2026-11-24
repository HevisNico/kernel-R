"""Tests of yield_lot.py (no simulation). Run: python3 -B tests/test_yield_lot.py"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import yield_lot as Y  # noqa: E402


def fake(k0, k3, n):
    return dict(eligible_K0=dict(k=k0, n=n, rate=k0 / n, wilson90=Y.wilson(k0, n)),
                room_K3=dict(k=k3, n=n, rate=k3 / n, wilson90=Y.wilson(k3, n)))


def test_wilson():
    lo, hi = Y.wilson(21, 24)
    assert 0.72 < lo < 0.74 and 0.94 < hi < 0.96
    assert Y.wilson(0, 24)[0] == 0.0 and Y.wilson(24, 24)[1] == 1.0


def test_size_rule():
    y = dict(NOT1=fake(8, 6, 8), ANDOR3=fake(21, 6, 24), XOR3=fake(21, 6, 24))
    r = Y.size(y, 280, 12)
    assert r["sizes"]["NOT1"]["N"] == 60 and r["total_core_h"] <= 280 and r["declared_in_advance"] == []
    for g in ("ANDOR3", "XOR3"):
        n = r["sizes"][g]["N"]
        assert n * y[g]["room_K3"]["wilson90"][0] >= 5 and n * y[g]["eligible_K0"]["wilson90"][0] >= 20
    r8 = Y.size(y, 176, 8)
    assert r8["total_core_h"] <= 176 and r8["sizes"]["NOT1"]["N"] == 40
    y2 = dict(NOT1=fake(8, 6, 8), ANDOR3=fake(20, 2, 24), XOR3=fake(18, 0, 24))
    r2 = Y.size(y2, 280, 12)
    assert r2["sizes"]["XOR3"]["N"] == r2["requirements"]["XOR3"]["N0"]        # k3 = 0: sized for K0 only
    assert r2["sizes"]["ANDOR3"]["N"] == r2["requirements"]["ANDOR3"]["N0"]    # N3 > 80: sized for K0 only
    assert len(r2["declared_in_advance"]) == 2
    assert Y.canon(Y.size(y2, 280, 12)) == Y.canon(r2)


def test_plans_cover_every_seed_once():
    ps, summ = Y.plans(dict(overlay="config_inverter_c5.json"), 12)
    got = sorted((g, s) for p in ps for g, v in p["groups"].items() for s in v["seeds"])
    assert got == sorted((g, s) for g, v in Y.SEEDS.items() for s in v) and len(got) == 56
    assert all(p["steps_until"] == "D" and "seal_push" not in p for p in ps)


if __name__ == "__main__":
    test_wilson()
    test_size_rule()
    test_plans_cover_every_seed_once()
    print("3 tests passed")
