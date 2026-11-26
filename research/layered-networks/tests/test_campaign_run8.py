"""Test of campaign_run8.py: `campaign_run.py verify` passes after a run (no simulation).
Run: python3 -B tests/test_campaign_run8.py

campaign_run2.cmd_run is replaced by a fake that writes OUTROOT exactly as its tail does (RESULT.json, then the
top-level SHA256SUMS). campaign_run3/4/5's real post-writes then run on it. With campaign_run7 alone, verify reports
RESULT.json broken (the defect); with campaign_run8 it prints "verified".
"""
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run3 as C3  # noqa: E402
import campaign_run7 as C7  # noqa: E402
import campaign_run8 as C8  # noqa: E402


def fake_c2_run(plan_path, root, *rest):
    root = Path(root)
    inst = root / "NOT1_9801"
    (inst / "D").mkdir(parents=True, exist_ok=True)
    (inst / "D" / "prediction.json").write_text("{}\n")
    (inst / "SHA256SUMS").write_text(f"{CR.sha(inst / 'D' / 'prediction.json')}  D/prediction.json\n")
    (root / "PLAN.json").write_text(Path(plan_path).read_text())
    (root / "trees.json").write_text("{}\n")
    (root / "RESULT.json").write_text(json.dumps(dict(instances=[]), indent=1, sort_keys=True) + "\n")
    files = sorted(root.glob("*/SHA256SUMS")) + [root / "RESULT.json", root / "PLAN.json", root / "trees.json"]
    (root / "SHA256SUMS").write_text("".join(f"{CR.sha(p)}  {p.relative_to(root)}\n" for p in files))
    (root / "DONE").write_text("x\n")
    return True


def verify(root):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        ok = CR.cmd_verify(root)
    return ok, out.getvalue().strip()


def run(driver, d):
    plan = Path(d) / "plan.json"
    plan.write_text(json.dumps(dict(groups=dict(NOT1=dict(spec="specs/not1.json", seeds=[9801])), steps_until="D",
                                    noise_tree=str(d), kit_tree=str(d))))
    root = Path(d) / "out"
    saved = C2.cmd_run, C3.set_env
    C2.cmd_run, C3.set_env = fake_c2_run, (lambda plan, root: "0" * 64)
    try:
        assert driver.cmd_run(plan, root)
    finally:
        C2.cmd_run, C3.set_env = saved
    return root


def test_run7_defect_and_run8_fix():
    with tempfile.TemporaryDirectory() as d:
        root = run(C7, d)
        ok, msg = verify(root)
        assert not ok and msg == f"BROKEN: {root / 'RESULT.json'}", msg           # the defect, and only it
        r = json.loads((root / "RESULT.json").read_text())
        assert {"core_budget", "remote_duplicates", "stopped_for_disk"} <= set(r)
    with tempfile.TemporaryDirectory() as d:
        root = run(C8, d)
        ok, msg = verify(root)
        assert ok and msg == "verified", msg
        pre = (root / "SHA256SUMS.pre_post_writes").read_text().splitlines()
        post = (root / "SHA256SUMS").read_text().splitlines()
        assert [x for x in pre if x not in post] == [x for x in pre if x.endswith("  RESULT.json")]
        assert [x.split("  ")[1] for x in pre] == [x.split("  ")[1] for x in post]


def test_rehash_finished_root():
    with tempfile.TemporaryDirectory() as d:
        root = run(C7, d)
        assert not verify(root)[0]
        assert C8.rewrite_top_sums(root) and verify(root)[0]
        first = (root / "SHA256SUMS.pre_post_writes").read_bytes()
        assert C8.rewrite_top_sums(root) and (root / "SHA256SUMS.pre_post_writes").read_bytes() == first   # kept


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
