"""Tests of sealpush2.py and campaign_run10.py (no simulation). Run: python3 -B tests/test_campaign_run10.py

A local bare repository stands in for GitHub: machine A pushes the line and the seal folder in one commit, and
machine B fetches the branch by name and compares against that folder.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run3 as C3  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import campaign_run10 as C10  # noqa: E402
import seal as sealmod  # noqa: E402
import sealpush2  # noqa: E402
import stage_d  # noqa: E402
import test_campaign_run9 as T9  # noqa: E402

BR = "evidence/combined-seals-K01"


def make_seal(d, name, seed, room=True):
    p = Path(d) / f"inst_{name}"
    p.mkdir()
    pred = dict(format=stage_d.FORMAT, tag="XOR3", seed=seed, status="done", eligible_K0=True, room_K3=room,
                inverter_gate=dict(source="assumed"), applies=dict(noiseless=True, noisy=room), prediction={})
    (p / "prediction.json").write_bytes(stage_d.canon(pred))
    sealmod.seal(Path(d) / f"seal_{name}", p)
    return Path(d) / f"seal_{name}"


def bare(d):
    b = Path(d) / "log.git"
    subprocess.run(["git", "init", "-q", "--bare", str(b)], check=True)
    hook = b / "hooks" / "pre-receive"
    hook.write_text("#!/bin/sh\nz=0000000000000000000000000000000000000000\nwhile read o n r; do\n"
                    "[ \"$n\" = \"$z\" ] && exit 1\n[ \"$o\" != \"$z\" ] && ! git merge-base --is-ancestor \"$o\" \"$n\" && exit 1\n"
                    "done\nexit 0\n")
    hook.chmod(0o755)
    return b


def test_push_two_seals_fetch_and_refusals():
    with tempfile.TemporaryDirectory() as d:
        b, w = bare(d), Path(d) / "work"
        s1, s2 = make_seal(d, "a", 9803), make_seal(d, "b", 9806)
        assert sealpush2.push(b, BR, "XOR3_9803", s1, w, Path(d) / "p1.json")
        assert sealpush2.push(b, BR, "XOR3_9806", s2, w, Path(d) / "p2.json")
        r1, r2 = (json.loads((Path(d) / f).read_text()) for f in ("p1.json", "p2.json"))
        assert r2["previous"] == r1["commit"] and r1["seal_folder"]["files"] == 3
        # the second commit only adds seals/XOR3_9806/ and appends SEALS.txt
        st = subprocess.run(["git", "-C", str(b), "diff", "--name-status", r1["commit"], r2["commit"]],
                            capture_output=True, text=True).stdout.split("\n")
        assert sorted(x.split("\t")[0] for x in st if x) == ["A", "A", "A", "M"]
        assert not sealpush2.push(b, BR, "XOR3_9803", s1, w, Path(d) / "p3.json")        # a second seal: refused
        assert "already on" in json.loads((Path(d) / "p3.json").read_text())["why"]
        ok, why = sealpush2.fetch(b, BR, r1["commit"], "XOR3_9803", Path(d) / "got")
        assert ok and sealmod.verify(Path(d) / "got", quiet=True)
        assert (Path(d) / "got" / "SHA256SUMS").read_bytes() == (s1 / "SHA256SUMS").read_bytes()
        assert sealpush2.fetch(b, BR, r1["commit"], "XOR3_9806", Path(d) / "no")[0] is False   # not yet at r1
        assert sealpush2.fetch(b, BR, "0" * 40, "XOR3_9803", Path(d) / "no2")[0] is False


def test_machine_b_fetches_and_compares():
    with tempfile.TemporaryDirectory() as d:
        b, w = bare(d), Path(d) / "work"
        s1 = make_seal(d, "a", 9803)
        assert sealpush2.push(b, BR, "XOR3_9803", s1, w, Path(d) / "p1.json")
        commit = json.loads((Path(d) / "p1.json").read_text())["commit"]
        plan = Path(d) / "plan.json"
        plan.write_text(json.dumps(dict(groups={}, steps_until="D", noise_tree=str(d), kit_tree=str(d),
                                        seal_push=dict(remote=str(b), branch="evidence/combined-seals-K02"),
                                        remote_duplicates=[dict(spec="specs/xor3.json", seed=9803, group="XOR3",
                                                                seal_log=[commit, BR])])))
        saved = C2.cmd_run, C9._c4_remote_duplicate, CR.compare_argv, C9.set_env
        C2.cmd_run, C9._c4_remote_duplicate, CR.compare_argv = T9.fake_c2_run, T9.fake_c4_dup, T9.fake_compare_argv
        C9.set_env = lambda plan_, root_: "0" * 64
        try:
            assert C10.cmd_run(plan, Path(d) / "out")
        finally:
            C2.cmd_run, C9._c4_remote_duplicate, CR.compare_argv, C9.set_env = saved
        dx = Path(d) / "out" / "DUPX_XOR3_9803"
        assert json.loads((dx / "seal_fetch.json").read_text())["ok"]
        chk = json.loads((dx / "seal_check.json").read_text())
        assert chk["ok"] and chk["verdict"] == "agrees"
        assert (dx / "seal" / "SHA256SUMS").read_bytes() == (s1 / "SHA256SUMS").read_bytes()
        assert T9.verify(Path(d) / "out")[0]


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
