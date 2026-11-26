"""Tests of analyze10.regenerate (no simulation; Lean 4.35.0 on PATH).
python -B tests/test_analyze10.py ROOT INSTANCE        e.g. a campaign_run14 root and one of its stage_d6 instances

- the sealed stage_d6 prediction regenerates byte-identical, the kernel field included;
- refused: stage_d6 named without a kernel field; a kernel field without stage_d6 named; a changed kernel field
  (regenerated, then not identical); and with analyze3's old script order, the defect D1 is reproduced.
"""
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import analyze3 as A3  # noqa: E402
import analyze10 as A10  # noqa: E402
import campaign_run14 as C14  # noqa: E402
import seal as sealmod  # noqa: E402

ROOT, INST = (Path(sys.argv[1]), sys.argv[2]) if len(sys.argv) > 2 else (None, None)


def with_seal(d, edit):
    f = next(p for p in (d / "seal").glob("*.json") if p.name != "MANIFEST.json")
    p = json.loads(f.read_bytes())
    edit(p)
    f.write_bytes(sealmod.canon(p))


def test_regenerate_rule():
    if ROOT is None:
        print(" skipped (no root given)")
        return
    plan = json.loads((ROOT / "PLAN.json").read_text())
    status = json.loads((ROOT / INST / "status.json").read_text())
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        build, _ = C14.build_kernel(t)
        os.environ["LAYERED_KERNEL_BUILD"] = str(build)
        A3.SCRIPTS, A3.regenerate = A10.SCRIPTS, A10.regenerate
        ok, why = A10.regenerate(ROOT, INST, plan, status)
        print(" sealed:", ok, why)
        assert ok, why

        def case(edit, want):
            r = t / "root"
            if r.exists():
                shutil.rmtree(r)
            (r / INST).mkdir(parents=True)
            for sub in ("seal", "D", "inv"):
                if (ROOT / INST / sub).exists():
                    shutil.copytree(ROOT / INST / sub, r / INST / sub, symlinks=True,
                                    ignore=shutil.ignore_patterns("lean_build", "kernel"))   # links kept as links
            with_seal(r / INST, edit)
            ok, why = A10.regenerate(r, INST, plan, status)
            print(" ", want, "->", ok, why)
            assert not ok and want in why, (want, why)

        case(lambda p: p.pop("kernel"), "no kernel field")
        case(lambda p: p["code"].pop("stage_d6.py"), "does not name stage_d6.py")
        case(lambda p: p["kernel"].update(theorems=p["kernel"]["theorems"] + 1), "differs from the seal in ['kernel']")
        A3.SCRIPTS = ("stage_d5.py", "stage_d4.py", "stage_d3.py")                # analyze3's order: D1 again
        ok, why = A3.regenerate.__wrapped__(ROOT, INST, plan, status) if hasattr(A3.regenerate, "__wrapped__") else \
            A10._regenerate(ROOT, INST, plan, status)
        print(" old order:", ok, why)
        assert not ok and "kernel" in why


if __name__ == "__main__":
    os.environ.setdefault("LAYERED_ENV_SHA256", "")
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
