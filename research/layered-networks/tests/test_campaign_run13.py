"""Tests of campaign_run13.py's template check (no simulation). python -B tests/test_campaign_run13.py

A plan from plan_split2.py on TEMPLATE_CAMPAIGN.json passes. Refused: a missing stagen, stagen controls2, a wrong
rule, allow_dry_seal true, and also save_ref_round, steps_until, a tree path, k3_budget, a short commit, a wrong
branch, keep_raw outside the plan, a rehearsal template that differs beyond seal_push.remote, a changed pinned
template. A refused launch writes nothing.
"""
import copy
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run13 as C13  # noqa: E402
import plan_split2 as PS2  # noqa: E402

DRAW = {"format": "layered-draw/1", "groups": {"NOT1": [6212, 6213, 6217, 6218, 6219, 6220], "XOR3": [7001, 7002]}}


def base():
    t, _ = C13.load_template()
    plans, _ = PS2.split(DRAW, t, 8)
    return t, next(p for p in plans if p["groups"])


def refused(plan, t, word):
    bad = C13.check_plan(plan, t)
    assert any(word in b for b in bad), (word, bad)
    return bad


def test_pinned_template():
    t, tc = C13.load_template()
    assert tc["template_sha256"] == C13.TEMPLATE_SHA256 and not tc["rehearsal"]
    for k in ("save_ref_round", "steps_until", "kit_tree", "noise_tree", "k3_budget", "keep_raw"):
        assert k not in t
    assert t["stagen"] == "controls4" and t["rounds"] == 3 and t["testError_rule"] == "one-port" and t["allow_dry_seal"] is False


def test_split_plan_passes():
    t, p = base()
    assert C13.check_plan(p, t) == [], C13.check_plan(p, t)


def test_the_four_refusals():
    t, p = base()
    q = copy.deepcopy(p); del q["stagen"]; print(" missing stagen:", refused(q, t, "missing key stagen"))
    q = dict(p, stagen="controls2"); print(" stagen controls2:", refused(q, t, "stagen is 'controls2'"))
    q = dict(p, testError_rule="two-port"); print(" wrong rule:", refused(q, t, "testError_rule is 'two-port'"))
    q = dict(p, allow_dry_seal=True); print(" allow_dry_seal true:", refused(q, t, "allow_dry_seal is True"))


def test_other_refusals():
    t, p = base()
    for k, v in (("save_ref_round", 1), ("steps_until", "D"), ("kit_tree", "/x"), ("noise_tree", "/x"), ("k3_budget", "/x")):
        refused(dict(p, **{k: v}), t, f"key {k} is not allowed")
    refused(dict(p, rounds=0), t, "rounds is 0")
    refused(dict(p, kit_commit="d599300"), t, "kit_commit")
    refused(dict(p, seal_push=dict(p["seal_push"], dry=True)), t, "seal_push")
    refused(dict(p, seal_push=dict(p["seal_push"], branch="main")), t, "seal_push.branch")
    refused(dict(p, keep_raw=["NOT1_1"]), t, "keep_raw")
    q = copy.deepcopy(p); del q["keep_raw"]; refused(q, t, "missing per-machine key keep_raw")
    try:
        C13.resolve_trees(dict(p, kit_commit="d599300d"), t, trees=[])
        raise AssertionError("a short commit was accepted")
    except C13.Refused as e:
        assert "full commit hash" in str(e)
    try:
        C13.resolve_trees(p, t, trees=[])
        raise AssertionError("a missing worktree was accepted")
    except C13.Refused as e:
        assert "no clean worktree" in str(e)


def test_rehearsal_template():
    t, _ = C13.load_template()
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "T.json"
        f.write_text(json.dumps(dict(t, seal_push=dict(t["seal_push"], remote="/local/seallog.git"))))
        r, tc = C13.load_template(f)
        assert tc["rehearsal"] and r["seal_push"]["remote"] == "/local/seallog.git"
        for bad in (dict(t, rounds=0), dict(t, allow_dry_seal=True), dict(t, seal_push=dict(t["seal_push"], dry=True))):
            f.write_text(json.dumps(bad))
            try:
                C13.load_template(f)
                raise AssertionError("a template differing beyond seal_push.remote was accepted")
            except C13.Refused as e:
                assert "beyond seal_push.remote" in str(e)


def test_changed_pinned_template_refused():
    saved = C13.TEMPLATE_SHA256
    C13.TEMPLATE_SHA256 = "0" * 64
    try:
        C13.load_template()
        raise AssertionError("a changed template was accepted")
    except C13.Refused as e:
        assert "not the pinned" in str(e)
    finally:
        C13.TEMPLATE_SHA256 = saved


def test_refused_launch_writes_nothing():
    t, p = base()
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "PLAN.json"
        f.write_text(json.dumps(dict(p, stagen="controls2")))
        root = Path(d) / "out"
        try:
            C13.cmd_launch(str(f), str(root))
            raise AssertionError("launched")
        except C13.Refused as e:
            assert "stagen" in str(e)
        assert not root.exists()


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
