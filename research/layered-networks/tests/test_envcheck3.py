"""Tests of envcheck_layered3.py and campaign_run11.set_env (no simulation).
Run with the pinned environment on PATH (numpy 2.3.5, ngspice, the PDK, Lean 4.35.0 under elan):
python -B tests/test_envcheck3.py

- Under elan, the real toolchain binary is found and pinned, and the proxy is recorded outside `static`.
- A PATH with only the toolchain's bin/ (a tarball install) gives the same static part.
- A fake `lean` 4.35.0 on PATH is refused, and campaign_run11.set_env refuses to write ENV.json.
"""
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run11 as C11  # noqa: E402
import envcheck_layered3 as E3  # noqa: E402


def with_path(path, f):
    old = os.environ["PATH"]
    os.environ["PATH"] = path
    try:
        return f()
    finally:
        os.environ["PATH"] = old


def test_real_binary_and_same_static():
    r = E3.lean_resolution()
    assert r["sha256"] == E3.LEAN_SHA256 and r["version"] == "4.35.0", r
    if not shutil.which("elan"):
        return
    assert r["proxy"] and r["proxy"]["sha256"] != E3.LEAN_SHA256      # elan's proxy is not the binary
    tool_bin = str(Path(r["path"]).parent)
    rest = ":".join(p for p in os.environ["PATH"].split(":") if ".elan/bin" not in p)
    t = with_path(f"{tool_bin}:{rest}", E3.lean_resolution)
    assert t["sha256"] == E3.LEAN_SHA256 and t["proxy"] is None
    a = E3.env()
    b = with_path(f"{tool_bin}:{rest}", E3.env)
    assert a["static_sha256"] == b["static_sha256"] and a["lean_proxy"] and b["lean_proxy"] is None


def test_fake_lean_refused():
    with tempfile.TemporaryDirectory() as d:
        fake = Path(d) / "bin"
        fake.mkdir()
        (fake / "lean").write_text('#!/bin/sh\necho "Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit x, Release)"\n')
        (fake / "lean").chmod(0o755)
        rest = ":".join(p for p in os.environ["PATH"].split(":") if ".elan" not in p)
        c = with_path(f"{fake}:{rest}", E3.checks)
        assert c["lean"]["ok"] and not c["lean_binary"]["ok"]          # the version alone would have passed
        try:
            with_path(f"{fake}:{rest}", lambda: C11.set_env({}, Path(d) / "out"))
            raise AssertionError("a wrong lean binary was accepted")
        except SystemExit as e:
            assert "lean_binary" in str(e)
        assert not (Path(d) / "out" / "ENV.json").exists()


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
