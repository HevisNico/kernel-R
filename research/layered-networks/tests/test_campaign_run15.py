"""Tests of campaign_run15.py and plan_split3.py (no simulation). python -B tests/test_campaign_run15.py

- Template 3 passes on plan_split3 plans; plans from plan_split2 are refused (no home_branch), and so are a manual
  seal_log, a home_branch equal to the machine's own, and the older templates.
- The wait: with no branch, then a branch without the line, it polls until the limit and returns None; once the
  home's SEALS.txt has the line, it returns the branch tip. The clock is simulated (no real sleep).
- A duplicate at the limit is not completed, with the reason, and nothing runs.
- launch refuses below disk_launch_gb (30) before writing anything.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run15 as C15  # noqa: E402
import plan_split2 as PS2  # noqa: E402
import plan_split3 as PS3  # noqa: E402

DRAW = {"format": "layered-draw/1", "groups": {"NOT1": [6212, 6213, 6217, 6218, 6219, 6220], "XOR3": [7001], "ANDOR3": [7101]}}


def test_template_3_and_refusals():
    t, tc = C15.load_template()
    assert tc["template_sha256"] == C15.TEMPLATE_SHA256 and t["disk_launch_gb"] == 30 and t["disk_guard_gb"] == 20
    assert t["duplicate_wait"] == {"interval_s": 60, "limit_s": 21600} and t["stage_d_script"] == "stage_d6.py"
    plans = PS3.split(DRAW, t, 8)[0]
    for p in plans:
        bad = C15.C13.check_plan(p, t) + C15.check_duplicates(p)
        assert bad == [], bad
    dups = [x for p in plans for x in p["remote_duplicates"]]
    assert len(dups) == 3 and all(x["home_branch"].startswith("evidence/combined-seals-K") for x in dups)
    p2 = next(p for p in PS2.split(DRAW, t, 8)[0] if p["remote_duplicates"])
    print(" plan_split2 plan:", C15.check_duplicates(p2)[:1])
    assert any("no home_branch" in b for b in C15.check_duplicates(p2))
    p = next(p for p in plans if p["remote_duplicates"])
    q = copy.deepcopy(p); q["remote_duplicates"][0]["seal_log"] = ["0" * 40, "x"]
    assert any("seal_log is not allowed" in b for b in C15.check_duplicates(q))
    q = copy.deepcopy(p); q["remote_duplicates"][0]["home_branch"] = q["seal_push"]["branch"]
    assert any("own branch" in b for b in C15.check_duplicates(q))
    for old in ("TEMPLATE_CAMPAIGN.json", "TEMPLATE_CAMPAIGN_2.json"):
        try:
            C15.load_template(HERE / old)
            raise AssertionError(f"{old} accepted")
        except C15.Refused as e:
            assert "beyond seal_push.remote" in str(e)


def git(*a, cwd=None):
    return subprocess.run(["git", *a], cwd=cwd, capture_output=True, text=True, check=True).stdout.strip()


def test_wait_for_seal():
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        remote = d / "log.git"
        git("init", "-q", "--bare", str(remote))
        clock = dict(t=0.0)
        events = {}

        def sleep(s):
            clock["t"] += s
            for at, f in list(events.items()):
                if clock["t"] >= at:
                    f()
                    events.pop(at)
        C15.WAIT.update(sleep=sleep, now=lambda: clock["t"])
        br = "evidence/combined-seals-K01"
        assert C15.wait_for_seal(remote, br, "NOT1_1", 60, 300, d / "w0.json") is None     # no branch at all
        w0 = json.loads((d / "w0.json").read_text())
        assert not w0["found"] and len(w0["attempts"]) == 6, w0          # t = 0, 60, ..., 300

        work = d / "work"
        git("init", "-q", str(work))
        for k, v in (("user.name", "t"), ("user.email", "t@t")):
            git("config", k, v, cwd=work)

        def push(lines):
            (work / "SEALS.txt").write_text("".join(f"{x} {'a' * 64}\n" for x in lines))
            git("add", "SEALS.txt", cwd=work)
            git("commit", "-q", "-m", "s", cwd=work)
            git("push", "-q", str(remote), f"HEAD:refs/heads/{br}", cwd=work)
        push(["NOT1_2"])                                   # the branch exists, without the line
        clock["t"] = 0.0
        events[200.0] = lambda: push(["NOT1_2", "NOT1_1"])  # the home pushes during the wait
        tip = C15.wait_for_seal(remote, br, "NOT1_1", 60, 3600, d / "w1.json")
        w1 = json.loads((d / "w1.json").read_text())
        print(" waited:", w1["waited_s"], "s,", len(w1["attempts"]), "attempts, found", w1["found"])
        assert tip == git("rev-parse", "HEAD", cwd=work) and w1["found"] and w1["attempts"][0]["found"] is False

        plan = dict(seal_push=dict(remote=str(remote)), duplicate_wait=dict(interval_s=60, limit_s=120))
        x = dict(group="NOT1", spec="specs/not1.json", seed=999, home_branch=br, home_instance="NOT1_999")
        clock["t"] = 0.0
        r = C15.remote_duplicate(d / "root", x, plan)
        print(" at the limit:", r)
        assert r["ok"] is False and r["not_completed"] and "within 120 s" in r["why"]
        assert not (d / "root" / "DUPX_NOT1_999" / "N0").exists()
        C15.WAIT.update(sleep=__import__("time").sleep, now=__import__("time").time)


def test_launch_disk_refused():
    t, _ = C15.load_template()
    p = next(p for p in PS3.split(DRAW, t, 8)[0] if p["groups"])
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "PLAN.json"
        f.write_text(json.dumps(p))
        saved_check, saved_free = C15.check, C15.free_gb
        C15.check = lambda path, tpl=None: (json.loads(Path(path).read_text()), b"", {}, {})   # trees are not needed here
        C15.free_gb = lambda path: 12.5
        try:
            C15.cmd_launch(str(f), str(Path(d) / "out"))
            raise AssertionError("launched")
        except C15.Refused as e:
            print(" ", e)
            assert "30 GB needed" in str(e)
        finally:
            C15.check, C15.free_gb = saved_check, saved_free
        assert not (Path(d) / "out").exists()


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
