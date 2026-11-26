"""Tests of draw_seeds.py and plan_split.py (no simulation). Run: python3 -B tests/test_draw_split.py"""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import draw_seeds as DS  # noqa: E402
import plan_split as PS  # noqa: E402


def excl(seeds):
    s = sorted(set(seeds))
    return dict(seeds=s, count=len(s), seeds_sha256=hashlib.sha256(DS.canon(s)).hexdigest())


def test_numbers_and_ranges():
    assert DS.numbers("seeds 8301–8303 and 9801") == {8301, 8302, 8303, 9801}
    assert DS.numbers("setseed 98031") == {98031}
    assert DS.numbers("seed 1000-9000") == {1000, 9000}           # a range wider than 2000 is not expanded
    assert DS.numbers("version 1.2345") == set()


def test_draw_deterministic_and_excluding():
    ex = excl(list(range(10000, 60000)) + [700001])
    a = DS.draw("beacon-abc", "123", ex)
    b = DS.draw("beacon-abc", "123", ex)
    assert DS.canon(a) == DS.canon(b)
    seeds = [s for v in a["groups"].values() for s in v]
    assert [len(v) for v in a["groups"].values()] == [60, 49, 49] and len(set(seeds)) == 158
    assert all(60000 <= s < 100000 for s in seeds) and 70000 not in seeds    # 10*70000+1 = 700001 is excluded
    assert DS.draw("beacon-abd", "123", ex)["groups"] != a["groups"]
    bad = dict(ex, seeds=ex["seeds"][:-1])
    try:
        DS.draw("x", "1", bad)
        raise AssertionError("an altered list was accepted")
    except AssertionError as e:
        assert "altered" in str(e)


def test_split():
    d = DS.draw("beacon-abc", "123", excl([]))
    t = dict(overlay="config_inverter_c5.json", seal_push=dict(remote="r", dry=False))
    for m in (8, 12):
        plans, summ = PS.split(d, t, m)
        assert len(plans) == m
        got = sorted((g, s) for p in plans for g, v in p["groups"].items() for s in v["seeds"])
        assert got == sorted((g, s) for g, v in d["groups"].items() for s in v)                  # each once
        assert sorted(g for p in plans for g in p["U_groups"]) == sorted(d["groups"])             # U once per group
        for p_i, p in enumerate(plans):
            assert p["seal_push"]["branch"] == f"evidence/combined-seals-K{p_i + 1:02d}"
            for x in p["remote_duplicates"]:
                assert x["seed"] not in p["groups"].get(x["group"], {}).get("seeds", [])         # on another machine
        aud = sorted(s for p in plans for v in p["groups"].values() for s in v["d4_audit"])
        assert aud == sorted(s for v in d["groups"].values() for s in v[5::6])                     # every 6th
        assert summ["max_core_h"] <= 1.25 * summ["total_core_h"] / m + 1.5                        # balanced
        assert DS.canon(PS.split(d, t, m)[1]) == DS.canon(summ)
    for m in (7, 13):
        try:
            PS.split(d, t, m)
            raise AssertionError("m outside 8..12 accepted")
        except AssertionError as e:
            assert "8 to 12" in str(e)


if __name__ == "__main__":
    test_numbers_and_ranges()
    test_draw_deterministic_and_excluding()
    test_split()
    print("3 tests passed")
