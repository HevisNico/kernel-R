"""Tests of campaign_run5.py and plan_split2.py (no simulation). Run: python3 -B tests/test_campaign_run5.py"""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run5 as C5  # noqa: E402
import draw_seeds as DS  # noqa: E402
import plan_split2 as PS2  # noqa: E402

PLAN = dict(groups=dict(NOT1=dict(spec="specs/not1.json", seeds=[9801])), seal_push=dict(remote="x", branch="b"))


def folder(d, inst, verdict=None):
    f = Path(d) / inst / "N0"
    f.mkdir(parents=True)
    (f / "trace.raw").write_text("raw")
    (f / "trace.digest.json").write_text("{}")
    if verdict:
        (f / "comparison.json").write_text(json.dumps(dict(verdict=verdict)))
    return f


def test_raw_kept_unless_agrees():
    with tempfile.TemporaryDirectory() as d:
        C5.STATE["keep"] = {"NOT1_9802"}
        cases = [("NOT1_9801", "agrees", False), ("NOT1_9803", "refuted", True), ("NOT1_9804", "observed only (no prediction)", True),
                 ("NOT1_9805", None, True), ("NOT1_9802", "agrees", True), ("DUP_NOT1_9801", "agrees", True), ("DUPX_NOT1_9806", None, True)]
        for inst, v, kept in cases:
            f = folder(d, inst, v)
            C5.drop_raw(f)
            assert (f / "trace.raw").exists() == kept, (inst, v)


def test_disk_guard_holds_without_status():
    with tempfile.TemporaryDirectory() as d:
        C5.STATE.update(root=Path(d), guard_gb=1e9, held=[])
        i = C5.Instance(d, "NOT1", "specs/not1.json", 9801, PLAN)
        assert not i.step("deck", [C5.CR.PY, "-c", "pass"], [], "deck")
        assert "deck" not in i.status["steps"] and C5.STATE["held"][0]["step"] == "deck"
        C5.STATE.update(guard_gb=0.0)
        assert i.step("deck", [C5.CR.PY, "-c", "pass"], [], "deck")


def test_stage_n_refused_without_pushed_seal():
    with tempfile.TemporaryDirectory() as d:
        C5.STATE.update(root=Path(d), guard_gb=0.0, held=[])
        i = C5.Instance(d, "NOT1", "specs/not1.json", 9801, dict(PLAN, noise_tree=d))
        assert not i.round(0) and i.status["steps"]["N0"]["status"] == "refused"
        j = C5.Instance(Path(d) / "b", "NOT1", "specs/not1.json", 9801, dict(PLAN, noise_tree=d))
        (j.dir / "seal_push.json").write_text(json.dumps(dict(pushed="dry", commit="a" * 40)))
        assert not j.round(0) and j.status["steps"]["N0"]["status"] == "refused"       # dry not allowed by default
        (Path(d) / "research" / "layered-networks").mkdir(parents=True)
        k = C5.Instance(Path(d) / "c", "NOT1", "specs/not1.json", 9801, dict(PLAN, noise_tree=d))
        (k.dir / "seal_push.json").write_text(json.dumps(dict(pushed=True, commit="b" * 40, branch="br")))
        k.round(0)                                                  # N0 then fails (no tree), but only after SEAL_LOG.json
        assert json.loads((k.dir / "N0" / "SEAL_LOG.json").read_text())["commit"] == "b" * 40
        assert k.status["steps"]["N0"]["status"] != "refused"


def test_split2_keep_raw():
    ex = dict(seeds=[], count=0, seeds_sha256=DS.hashlib.sha256(DS.canon([])).hexdigest())
    dr = DS.draw("b", "1", ex)
    plans, _ = PS2.split(dr, dict(seal_push=dict(remote="r")), 12)
    keep = sorted(x for p in plans for x in p["keep_raw"])
    assert keep == sorted(f"{t}_{dr['groups'][g][0]}" for g, t in (("NOT1", "NOT1"), ("ANDOR3", "ANDOR3"), ("XOR3", "XOR3")))
    assert all(p["disk_guard_gb"] == 20 and p["allow_dry_seal"] is False for p in plans)


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
