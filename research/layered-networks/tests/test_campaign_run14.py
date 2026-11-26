"""Tests of campaign_run14.py, stage_d6.py and trace_extract.py (no simulation; Lean 4.35.0 on PATH).
python -B tests/test_campaign_run14.py [NOT1_ROUND_DIR] [STAGE_D_DIR]

- The pinned template 2 passes on a plan_split2 plan; the old template and its plans are refused; the four refusals.
- A changed kernel source is refused before any build.
- stage_d6: the kernel agrees on a sealed stage-D record; with a mirror made wrong on one clause, the kernel rejects
  that clause, the step fails and the clause is in prediction.json's kernel.disagreements.
- drop_raw: the extract is written before the raw is deleted; keep_raw keeps N0 only; a failed extract keeps the raw.
The two optional arguments are a NOT1 stage-N round with trace.raw, noisy_record.json and comparison.json "agrees",
and a NOT1 instance folder with D/record.json, D/overlay_d.json, D/prediction.json and inv/inverter_gate.json.
"""
import copy
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run5 as C5  # noqa: E402
import campaign_run14 as C14  # noqa: E402
import fit as fitmod  # noqa: E402
import plan_split2 as PS2  # noqa: E402
import stage_d6  # noqa: E402

DRAW = {"format": "layered-draw/1", "groups": {"NOT1": [6212, 6213, 6217, 6218, 6219, 6220], "XOR3": [7001], "ANDOR3": [7101]}}
ARGS = sys.argv[1:]


def plans(t):
    return PS2.split(DRAW, t, 8)[0]


def test_template_2_and_old_refused():
    t, tc = C14.load_template()
    assert tc["template_sha256"] == C14.TEMPLATE_SHA256 and t["stage_d_script"] == "stage_d6.py"
    assert "kernel" in t and "trace_extract" in t
    for p in plans(t):
        assert C14.C13.check_plan(p, t) == [], C14.C13.check_plan(p, t)
    try:
        C14.load_template(HERE / "TEMPLATE_CAMPAIGN.json")
        raise AssertionError("the old template was accepted")
    except C14.Refused as e:
        assert "beyond seal_push.remote" in str(e), e
    old, _ = C14.C13.load_template()
    bad = C14.C13.check_plan(next(p for p in plans(old) if p["groups"]), t)
    print(" a plan from the old template:", bad)
    assert any("stage_d_script" in b for b in bad) and any("missing key kernel" in b for b in bad)
    assert any("missing key trace_extract" in b for b in bad)
    p = next(p for p in plans(t) if p["groups"])
    q = copy.deepcopy(p); del q["stagen"]
    for r, w in ((q, "missing key stagen"), (dict(p, stagen="controls2"), "stagen is"),
                 (dict(p, testError_rule="two-port"), "testError_rule is"), (dict(p, allow_dry_seal=True), "allow_dry_seal is")):
        assert any(w in b for b in C14.C13.check_plan(r, t)), w


def test_changed_kernel_source_refused():
    saved = dict(C14.KERNEL_SOURCES)
    C14.KERNEL_SOURCES["LayeredMonotoneTarget.lean"] = "0" * 64
    try:
        with tempfile.TemporaryDirectory() as d:
            C14.build_kernel(d)
            raise AssertionError("a changed source was accepted")
    except C14.Refused as e:
        assert "LayeredMonotoneTarget.lean" in str(e)
        assert not (Path(d) / "kernel_build").exists()
    finally:
        C14.KERNEL_SOURCES.clear()
        C14.KERNEL_SOURCES.update(saved)


def test_stage_d6_kernel_and_disagreement():
    if len(ARGS) < 2:
        print(" skipped (no stage-D folder given)")
        return
    inst = Path(ARGS[1])
    with tempfile.TemporaryDirectory() as d:
        build, meta = C14.build_kernel(d)
        print(" library built in", meta["seconds"], "s")
        for wrong in (False, True):
            out = Path(d) / f"D{int(wrong)}"
            out.mkdir()
            for n in ("record.json", "overlay_d.json"):
                shutil.copyfile(inst / "D" / n, out / n)
            argv = ["predict", str(HERE / "specs/not1.json"), str(out), f"inverters={inst / 'inv' / 'inverter_gate.json'}",
                    "rule=one-port", f"kernel_build={build}"]
            saved = fitmod.cell_valid
            if wrong:                                   # the mirror wrong on the dose clause: it says false
                def cv(p):
                    v, cl = saved(p)
                    cl = [(n, (0 if n == "dose > 0" else s)) for n, s in cl]
                    return all(s > 0 for _, s in cl), cl
                fitmod.cell_valid = cv
            try:
                ok = stage_d6.main(argv)
            finally:
                fitmod.cell_valid = saved
            k = json.loads((out / "prediction.json").read_text())["kernel"]
            if not wrong:
                sealed = json.loads((inst / "D" / "prediction.json").read_text())
                new = json.loads((out / "prediction.json").read_text())
                assert ok and k["agrees"] and new["eligible_K0"] == sealed["eligible_K0"] and new["room_K3"] == sealed["room_K3"]
            else:
                print(" wrong mirror:", k["disagreements"])
                assert not ok and not k["agrees"]
                assert {x["clause"] for x in k["disagreements"]} >= {"dose > 0", "cellValid"}


def test_drop_raw_extract_and_keep_raw():
    if not ARGS:
        print(" skipped (no round given)")
        return
    src = Path(ARGS[0])
    with tempfile.TemporaryDirectory() as d:
        for inst, keep in (("NOT1_1", True), ("NOT1_2", False)):
            for n in ("N0", "N1"):
                f = Path(d) / inst / n
                f.mkdir(parents=True)
                for x in ("trace.raw", "noisy_record.json", "comparison.json", "trace.digest.json"):
                    if (src / x).exists():
                        shutil.copyfile(src / x, f / x)
        C5.STATE["keep"] = {"NOT1_1"}
        for inst in ("NOT1_1", "NOT1_2"):
            for n in ("N0", "N1"):
                C14.drop_raw(Path(d) / inst / n)
        have = {f"{i}/{n}": (Path(d, i, n, "trace.raw").exists(), Path(d, i, n, "extract", "extract.json").exists())
                for i in ("NOT1_1", "NOT1_2") for n in ("N0", "N1")}
        print(" (raw kept, extract written):", have)
        assert have == {"NOT1_1/N0": (True, True), "NOT1_1/N1": (False, True), "NOT1_2/N0": (False, True),
                        "NOT1_2/N1": (False, True)}
        f = Path(d) / "NOT1_3" / "N1"                   # a vector missing: the record names a cell the trace lacks
        f.mkdir(parents=True)
        shutil.copyfile(src / "trace.raw", f / "trace.raw")
        shutil.copyfile(src / "comparison.json", f / "comparison.json")
        rec = json.loads((src / "noisy_record.json").read_text())
        rec["slots"][0]["reads"].append(dict(layer=9, index=9))
        (f / "noisy_record.json").write_text(json.dumps(rec))
        C14.drop_raw(f)
        assert (f / "trace.raw").exists() and (f / "extract_failed.json").exists()
        assert "xc9_9" in json.loads((f / "extract_failed.json").read_text())["why"]
        C5.STATE["keep"] = set()


if __name__ == "__main__":
    os.environ.setdefault("LAYERED_ENV_SHA256", "test")
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
