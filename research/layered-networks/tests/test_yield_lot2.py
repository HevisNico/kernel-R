"""Tests of yield_lot2.py's integrity check (no simulation). Run: python3 -B tests/test_yield_lot2.py"""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import yield_lot2 as Y2  # noqa: E402


def make_root(d, post=dict(core_budget=dict(cores=4, peak_in_use=4))):
    root = Path(d) / "out"
    inst = root / "NOT1_6223"
    (inst / "D").mkdir(parents=True)
    (inst / "D" / "prediction.json").write_text("{}\n")
    (inst / "SHA256SUMS").write_text(f"{Y2.sha(inst / 'D' / 'prediction.json')}  D/prediction.json\n")
    (root / "PLAN.json").write_text("{}\n")
    res = dict(instances=[], controls={})
    (root / "RESULT.json").write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    files = [inst / "SHA256SUMS", root / "RESULT.json", root / "PLAN.json"]
    (root / "SHA256SUMS").write_text("".join(f"{Y2.sha(p)}  {p.relative_to(root)}\n" for p in files))
    (root / "RESULT.json").write_text(json.dumps(dict(res, **post), indent=1, sort_keys=True) + "\n")   # the post-write
    return root


def test_known_defect_accepted_only_as_such():
    with tempfile.TemporaryDirectory() as d:
        r = Y2.check_root(make_root(d))
        assert r["ok"] and r["known_defect"]["keys_removed"] == ["core_budget"]
    with tempfile.TemporaryDirectory() as d:
        r = Y2.check_root(make_root(d, post={}))
        assert r["ok"] and r["known_defect"] is None
    with tempfile.TemporaryDirectory() as d:
        r = Y2.check_root(make_root(d, post=dict(core_budget=1, instances=["x"])))     # another change: refused
        assert not r["ok"] and r["top_level"] == [dict(file="RESULT.json", why="hash differs")]


def test_per_instance_failures():
    with tempfile.TemporaryDirectory() as d:
        root = make_root(d)
        (root / "NOT1_6223" / "D" / "prediction.json").write_text("{\"x\": 1}\n")
        r = Y2.check_root(root)
        assert not r["ok"] and r["per_instance"][0]["failed"] == [dict(file="D/prediction.json", why="hash differs")]
        (root / "NOT1_6223" / "D" / "prediction.json").unlink()
        assert Y2.check_root(root)["per_instance"][0]["failed"][0]["why"] == "missing"


def add_line(root, inst, line):
    with open(inst / "SHA256SUMS", "a") as f:
        f.write(line)
    top = root / "SHA256SUMS"
    top.write_text("".join(f"{Y2.sha(inst / 'SHA256SUMS')}  {inst.name}/SHA256SUMS\n" if l.endswith(f"{inst.name}/SHA256SUMS") else l + "\n"
                           for l in top.read_text().splitlines()))


def test_pushed_copy_inv_absent():
    with tempfile.TemporaryDirectory() as d:
        root = make_root(d)
        inst = root / "NOT1_6223"
        add_line(root, inst, "0" * 64 + "  inv/n0/runs/6223/MEASURE.json\n")
        assert not Y2.check_root(root)["ok"]                                   # no VERIFY.txt: missing is a failure
        (root / "VERIFY.txt").write_text("BROKEN: /root/x/out/RESULT.json\n")
        r = Y2.check_root(root)
        assert r["ok"] and r["absent_from_copy"] == 1
        add_line(root, inst, "0" * 64 + "  D/missing.json\n")                            # outside inv/: still a failure
        assert not Y2.check_root(root)["ok"]
        (root / "VERIFY.txt").write_text("BROKEN: /root/x/out/RESULT.json, /root/x/out/NOT1_6223/D/record.json\n")
        assert not Y2.machine_verified(root)


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
