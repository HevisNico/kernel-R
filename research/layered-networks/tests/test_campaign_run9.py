"""Tests of campaign_run9.py and ref_extract.py (no simulation). Run: python3 -B tests/test_campaign_run9.py

- The end is held: DONE and INVENTORY_END do not exist while the remote duplicate runs, they exist after it, verify
  prints "verified", and the top-level SHA256SUMS covers DUPX_<inst>/SHA256SUMS.
- The remote duplicate is compared against the original's seal, checked against the seal log; a seal_dir whose
  SHA256SUMS is not the logged one gives no comparison.json.
- The save_ref round's vectors are extracted before its trace.raw is deleted.
"""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import numpy as np

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run3 as C3  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import ref_extract  # noqa: E402
import seal as sealmod  # noqa: E402
import stage_d  # noqa: E402

SEEN = {}


def fake_c2_run(plan_path, root, *rest):
    root = Path(root)
    inst = root / "XOR3_9803"
    (inst / "D").mkdir(parents=True, exist_ok=True)
    (inst / "D" / "prediction.json").write_text("{}\n")
    (inst / "SHA256SUMS").write_text(f"{CR.sha(inst / 'D' / 'prediction.json')}  D/prediction.json\n")
    (root / "PLAN.json").write_text(Path(plan_path).read_text())
    (root / "trees.json").write_text("{}\n")
    (root / "RESULT.json").write_text(json.dumps(dict(instances=[]), indent=1, sort_keys=True) + "\n")
    files = sorted(root.glob("*/SHA256SUMS")) + [root / "RESULT.json", root / "PLAN.json", root / "trees.json"]
    (root / "SHA256SUMS").write_text("".join(f"{CR.sha(p)}  {p.relative_to(root)}\n" for p in files))
    (root / "INVENTORY_END").write_text(C2.inventory())          # campaign_run2's own order
    (root / "DONE").write_text("x\n")
    return True


def fake_c4_dup(root, x, plan):
    d = Path(root) / f"DUPX_XOR3_{x['seed']}"
    (d / "N0").mkdir(parents=True, exist_ok=True)
    SEEN["done_during_dup"] = (Path(root) / "DONE").exists() or (Path(root) / "INVENTORY_END").exists()
    (d / "N0" / "noisy_record.json").write_text("{}\n")
    (d / "N0" / "input.spice").write_text("* deck\n")
    res = dict(instance=f"XOR3_{x['seed']}", ok=True)
    (d / "duplicate_here.json").write_text(json.dumps(res) + "\n")
    C3.BUDGET.acquire(1)
    C3.BUDGET.release(1)
    return res


def fake_compare_argv(seal, sp, out, n):
    return [CR.PY, "-c", f"import json; open({str(Path(out) / 'comparison.json')!r},'w').write(json.dumps(dict(verdict='agrees')))"]


def make_seal_and_log(d, inst="XOR3_9803"):
    d = Path(d)
    pdir = d / "inst"
    pdir.mkdir()
    pred = dict(format=stage_d.FORMAT, tag="XOR3", seed=9803, status="done", eligible_K0=True, room_K3=True,
                inverter_gate=dict(source="assumed"), applies=dict(noiseless=True, noisy=True), prediction={})
    (pdir / "prediction.json").write_bytes(stage_d.canon(pred))
    sealmod.seal(d / "seal", pdir)
    bare = d / "log.git"
    subprocess.run(["git", "init", "-q", "--bare", str(bare)], check=True)
    w = d / "w"
    subprocess.run(["git", "init", "-q", str(w)], check=True)
    (w / "SEALS.txt").write_text(f"{inst} {CR.sha(d / 'seal' / 'SHA256SUMS')} 2026-11-25T00:00:00Z\n")
    g = lambda *a: subprocess.run(["git", "-C", str(w), "-c", "user.name=t", "-c", "user.email=t@t", *a],
                                  check=True, capture_output=True, text=True)
    g("add", "SEALS.txt")
    g("commit", "-q", "-m", "seal")
    g("push", "-q", str(bare), "HEAD:refs/heads/evidence/combined-seals-K01")
    return d / "seal", bare, g("rev-parse", "HEAD").stdout.strip()


def run9(d, seal_dir, bare, commit):
    plan = Path(d) / "plan.json"
    plan.write_text(json.dumps(dict(groups={}, steps_until="D", noise_tree=str(d), kit_tree=str(d),
                                    seal_push=dict(remote=str(bare), branch="evidence/combined-seals-K02"),
                                    remote_duplicates=[dict(spec="specs/xor3.json", seed=9803, group="XOR3",
                                                            seal_dir=str(seal_dir),
                                                            seal_log=[commit, "evidence/combined-seals-K01"])])))
    root = Path(d) / "out"
    saved = C2.cmd_run, C3.set_env, C9._c4_remote_duplicate, CR.compare_argv
    C2.cmd_run, C9._c4_remote_duplicate, CR.compare_argv = fake_c2_run, fake_c4_dup, fake_compare_argv
    orig_set_env = C9.set_env
    C9.set_env = lambda plan_, root_: "0" * 64
    try:
        assert C9.cmd_run(plan, root)
    finally:
        C2.cmd_run, C3.set_env, C9._c4_remote_duplicate, CR.compare_argv = saved
        C9.set_env = orig_set_env
    return root


def verify(root):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        ok = CR.cmd_verify(root)
    return ok, out.getvalue().strip()


def test_end_held_and_dupx_compared():
    with tempfile.TemporaryDirectory() as d:
        seal_dir, bare, commit = make_seal_and_log(d)
        root = run9(d, seal_dir, bare, commit)
        assert SEEN["done_during_dup"] is False
        assert (root / "DONE").exists() and (root / "INVENTORY_END").exists()
        ok, msg = verify(root)
        assert ok and msg == "verified", msg
        top = (root / "SHA256SUMS").read_text()
        assert "DUPX_XOR3_9803/SHA256SUMS" in top and "DUPX_XOR3_9803/duplicate_here.json" in top
        dsums = (root / "DUPX_XOR3_9803" / "SHA256SUMS").read_text()
        assert "N0/comparison.json" in dsums and "seal/SHA256SUMS" in dsums and "seal_check.json" in dsums
        chk = json.loads((root / "DUPX_XOR3_9803" / "seal_check.json").read_text())
        assert chk["ok"] and chk["verdict"] == "agrees"
        r = json.loads((root / "RESULT.json").read_text())
        assert r["core_budget"]["peak_in_use"] >= 1 and r["end_held_until_every_job"]


def test_wrong_seal_gives_no_comparison():
    with tempfile.TemporaryDirectory() as d:
        seal_dir, bare, commit = make_seal_and_log(d)
        other = Path(d) / "inst2"
        other.mkdir()
        p = json.loads((Path(d) / "inst" / "prediction.json").read_text())
        p["room_K3"] = False
        (other / "prediction.json").write_bytes(stage_d.canon(p))
        sealmod.seal(Path(d) / "seal2", other)                  # a valid seal, but not the logged one
        root = run9(d, Path(d) / "seal2", bare, commit)
        chk = json.loads((root / "DUPX_XOR3_9803" / "seal_check.json").read_text())
        assert not chk["ok"] and "is not seal_dir's" in chk["why"]
        assert not (root / "DUPX_XOR3_9803" / "N0" / "comparison.json").exists()
        assert verify(root)[0]


def write_raw(path, names, data):
    head = ["Title: t", "Date: x", "Plotname: Transient Analysis", "Flags: real", f"No. Variables: {len(names)}",
            f"No. Points: {len(data)}", "Variables:"] + [f"\t{i}\t{n}\tvoltage" for i, n in enumerate(names)]
    Path(path).write_bytes(("\n".join(head) + "\nBinary:\n").encode() + np.asarray(data, "<f8").tobytes())


def test_ref_extract_and_drop():
    with tempfile.TemporaryDirectory() as d:
        rnd = Path(d) / "XOR3_9803" / "N1"
        rnd.mkdir(parents=True)
        names = ["time", "v(a)", "v(xn0.vrefm)", "v(xn0.vrefmn)", "v(xn0.nzm)", "v(nzhn0)", "v(nzjn0)", "v(b)"]
        data = np.arange(5 * len(names), dtype=float).reshape(5, len(names))
        write_raw(rnd / "trace.raw", names, data)
        (rnd / "noisy_record.json").write_text(json.dumps(dict(saved_ref=["xn0.vrefm"], slots=[dict(inv=[{}])])))
        (rnd / "comparison.json").write_text(json.dumps(dict(verdict="agrees")))
        (rnd / "trace.digest.json").write_text(json.dumps(dict(file="trace.raw", size=1)))
        C9.PLAN.clear()
        C9.PLAN.update(save_ref_round=1)
        C9.C5.STATE.update(keep=set())
        C9.drop_raw(rnd)
        assert not (rnd / "trace.raw").exists()                       # deleted by campaign_run5's rule, after the extract
        meta = json.loads((rnd / "ref" / "ref.json").read_text())
        assert meta["vectors"] == names[:1] + names[2:7] and meta["points"] == 5
        got = ref_extract.header(rnd / "ref" / "trace.raw")
        arr = np.frombuffer((rnd / "ref" / "trace.raw").read_bytes()[got[4]:], "<f8").reshape(5, 6)
        assert (arr == data[:, [0, 2, 3, 4, 5, 6]]).all()             # the original columns, bit for bit
        assert json.loads((rnd / "ref_extract.json").read_text())["ok"]


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
