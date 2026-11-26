"""Tests of campaign_run16.py (no simulation). python -B tests/test_campaign_run16.py NOT1_ROUND_DIR
NOT1_ROUND_DIR: a NOT1 stage-N round with trace.raw, noisy_record.json and trace.digest.json (e.g. a kept N0).

- Template 4: 40 GB at launch, guard 20; templates 1–3 refused.
- The forced low-disk condition: the guard threshold is set above the free space.
  - A comparison step C1 runs, and is logged in GUARD_EXEMPT.json.
  - After it, the round's raw is deleted (the extract written first), and the freed bytes are measured.
  - A new N step (N2) is held: it does not run, gets no status entry, and is listed as held.
  - A step named like a comparison but not of kind C, and stage D, stay guarded.
"""
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run5 as C5  # noqa: E402
import campaign_run10 as C10  # noqa: E402
import campaign_run14 as C14  # noqa: E402
import campaign_run16 as C16  # noqa: E402

SRC = Path(sys.argv[1]) if len(sys.argv) > 1 else None


def test_template_4():
    t, tc = C16.load_template()
    assert tc["template_sha256"] == C16.TEMPLATE_SHA256 and t["disk_launch_gb"] == 40 and t["disk_guard_gb"] == 20
    for old in ("TEMPLATE_CAMPAIGN.json", "TEMPLATE_CAMPAIGN_2.json", "TEMPLATE_CAMPAIGN_3.json"):
        try:
            C16.load_template(HERE / old)
            raise AssertionError(f"{old} accepted")
        except C16.Refused as e:
            assert "beyond seal_push.remote" in str(e)


def test_forced_low_disk():
    if SRC is None:
        print(" skipped (no round given)")
        return
    with tempfile.TemporaryDirectory() as d:
        root = Path(d) / "root"
        plan = dict(groups=dict(NOT1=dict(spec="specs/not1.json", seeds=[1])))
        inst = C10.Instance(root, "NOT1", "specs/not1.json", 1, plan)
        n1 = inst.dir / "N1"
        n1.mkdir(parents=True)
        for f in ("trace.raw", "noisy_record.json", "trace.digest.json"):
            shutil.copyfile(SRC / f, n1 / f)
        free = shutil.disk_usage(root).free / 1e9
        C5.STATE.update(root=root, guard_gb=free + 1000.0, held=[], keep=set())   # the guard far above the free space
        saved = C5.Instance.step
        C5.Instance.step = C16.step
        try:
            comp = n1 / "comparison.json"
            argv = [CR.PY, "-c", f"import json; open({str(comp)!r}, 'w').write(json.dumps(dict(verdict='agrees')))"]
            ok_c = inst.step("C1", argv, ["N1/comparison.json"], "C")
            raw = (n1 / "trace.raw").stat().st_size
            before = shutil.disk_usage(root).free
            C14.drop_raw(n1)                                       # what the chain does after an agreeing comparison
            after = shutil.disk_usage(root).free
            ok_n = inst.step("N2", [CR.PY, "-c", "open('ran', 'w')"], ["N2/noisy_record.json"], "N")
            ok_x = inst.step("C2", [CR.PY, "-c", "pass"], [], "N")           # named C2 but not of kind C: guarded
            ok_d = inst.step("D", [CR.PY, "-c", "pass"], [], "D")
        finally:
            C5.Instance.step = saved
        st = json.loads((inst.dir / "status.json").read_text())["steps"]
        ex = json.loads((root / "GUARD_EXEMPT.json").read_text())
        print(" C1:", ok_c, st["C1"]["status"], "| raw", raw, "bytes deleted:", not (n1 / "trace.raw").exists(),
              "freed net", after - before, "| extract:", (n1 / "extract" / "extract.json").exists())
        print(" held:", [h["step"] for h in C5.STATE["held"]], "| exempt log:", [(e["step"], e["free_gb"] < e["guard_gb"]) for e in ex])
        assert ok_c and st["C1"]["status"] == "done" and [e["step"] for e in ex] == ["C1"]
        assert not (n1 / "trace.raw").exists() and (n1 / "extract" / "extract.json").exists()
        ext = sum(f.stat().st_size for f in (n1 / "extract").iterdir())
        assert after - before >= raw - ext - 1_000_000, (after - before, raw, ext)   # net of the extract written first
        assert not ok_n and "N2" not in st and not (Path(CR.HERE) / "ran").exists()
        assert not ok_x and "C2" not in st and not ok_d and "D" not in st
        assert [h["step"] for h in C5.STATE["held"]] == ["N2", "C2", "D"]
        C5.STATE.update(root=None, guard_gb=20.0, held=[], keep=set())


if __name__ == "__main__":
    os.environ.setdefault("LAYERED_ENV_SHA256", "test")
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
