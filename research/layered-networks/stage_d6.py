"""stage_d5.py with the Lean kernel as the last word on the R cells' Cell.Valid (the owner's decision, relayed
2026-11-26). Development only. stage_d5.py and the earlier stages are kept as they are.

  stage_d6.py run | predict | deck | seal | verify ...     as stage_d5.py; run and predict add the kernel check

**After predict** (stage_d5's prediction.json is written), leancell.py checks D/prediction.json with the kernel:
- every measured cell, at K0 and K3, as a Lean `Cell` literal;
- one `decide +kernel` theorem per clause of fit.cell_valid (the Python mirror of Cell.Valid, LayeredMonotoneTarget.lean),
  stating the mirror's value;
- `Cell.stop`, and `Checker.cellValid` = the mirror's valid (sound and complete for Cell.Valid).

**The kernel is the last word.** A theorem the kernel rejects is a kernel–mirror disagreement. Then:
- the step fails (exit 1), so the instance is not completed at stage D: no seal, no stage N;
- the disagreements (cell, level, clause) are in prediction.json `kernel.disagreements`.

When the kernel accepts every theorem, the mirror's verdicts are the kernel's, and prediction.json gets `kernel`
(deterministic: no path, no time, so the seal stays byte-reproducible):
- `agrees` true and the number of theorems;
- per cell and level, the kernel's Cell.Valid and the mirror's valid beside it;
- the sha256 of leancell.py and of the Lean sources the library is built from.

**The calibration clauses** (TrainingCalibration / ReadCalibration: residuals, decoder, firing-slot submasks and
anchors), the trained-word check and the inverter gate's own mirror stay on the Python mirror; the kernel does not
check them here.

**The library** (LayeredMonotoneCheckerProofs and its imports) is built once per machine by campaign_run14 into
OUTROOT/kernel_build, given here in the environment variable LAYERED_KERNEL_BUILD (or `kernel_build=DIR` by hand).
Without it, run and predict refuse.

The logs, the .lean file and leancell's LEANCELL.json (with times and paths) are in D/kernel/.
"""
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import stage_d  # noqa: E402
import stage_d3  # noqa: E402
import stage_d5  # noqa: E402,F401  (sets stage_d3.stamp to stage_d5's)
import leancell  # noqa: E402

LEAN_DIR = HERE.parent / "learned-coincidence"
CLOSURE = ["Target", "TwoLayerTarget", "MonotoneTarget", "MonotoneSupport", "MonotoneOneSidedTarget",
           "LayeredMonotoneTarget", "MonotonePremiseTargets", "LayeredMonotoneCheckerTargets", "MonotonePremiseSoundness",
           "MonotonePremiseCompletenessTargets", "MonotonePremiseCompleteness", "LayeredMonotoneCheckerProofs"]
STATE = dict(build=None, ok=True)
_stamp5 = stage_d3.stamp


def sources():
    return {f"{m}.lean": stage_d.sha256_file(LEAN_DIR / f"{m}.lean") for m in CLOSURE}


def kernel_check(out, build):
    """leancell on OUT/prediction.json: the kernel section of the prediction (deterministic) and whether it agrees."""
    out = Path(out)
    kd = out / "kernel"
    kd.mkdir(exist_ok=True)
    (kd / "MANIFEST.json").write_text(json.dumps([dict(label="prediction", prediction=str(out / "prediction.json"))]))
    leancell.main(kd, build, kd / "MANIFEST.json")
    r = json.loads((kd / "LEANCELL.json").read_text())["runs"][0]
    pred = json.loads((out / "prediction.json").read_text())
    verdicts = []
    for c in pred.get("cells", []):
        if not c.get("measured"):
            continue
        for K in ("K0", "K3"):
            _, valid, _, _ = leancell.mirror(c["lean_cell"][K])
            bad = [d for d in r["disagreements"] if d["cell"] == c["cell"] and d["level"] == K]
            kv = (not valid) if any(d["clause"] == "cellValid" for d in bad) else valid
            verdicts.append(dict(cell=c["cell"], level=K, kernel_cell_valid=kv, mirror_cell_valid=valid))
    agrees = bool(r["kernel_agrees_everywhere"] and r["sealed_failing_equals_mirror"] and not r["unplaced_error_lines"])
    return agrees, dict(checker="leancell.py (decide +kernel, clause by clause)", agrees=agrees, theorems=r["theorems"],
                        lean_rc=r["lean_rc"], disagreements=r["disagreements"],
                        unplaced_error_lines=r["unplaced_error_lines"],
                        sealed_failing_equals_mirror=r["sealed_failing_equals_mirror"], cell_valid=verdicts,
                        last_word="kernel (Cell.Valid); calibration clauses, trained word and inverter gate: mirror",
                        leancell_sha256=stage_d.sha256_file(HERE / "leancell.py"), lean_sources_sha256=sources())


def stamp(out, rule):
    p = _stamp5(out, rule)
    agrees, k = kernel_check(out, STATE["build"])
    p = json.loads((Path(out) / "prediction.json").read_bytes())
    p["kernel"] = k
    p["code"]["stage_d6.py"] = stage_d.sha256_file(HERE / "stage_d6.py")
    p["code"]["leancell.py"] = k["leancell_sha256"]
    (Path(out) / "prediction.json").write_bytes(stage_d.canon(p))
    STATE["ok"] = agrees
    print(json.dumps(dict(kernel_agrees=agrees, theorems=k["theorems"], disagreements=k["disagreements"])))
    return p


def main(argv):
    cmd = (argv or ["help"])[0]
    if cmd in ("run", "predict"):
        kb = next((x.split("=", 1)[1] for x in argv if x.startswith("kernel_build=")), None)
        argv = [x for x in argv if not x.startswith("kernel_build=")]
        STATE["build"] = kb or os.environ.get("LAYERED_KERNEL_BUILD")
        if not STATE["build"] or not (Path(STATE["build"]) / "LayeredMonotoneCheckerProofs.olean").exists():
            raise SystemExit("refused: no kernel library (LAYERED_KERNEL_BUILD or kernel_build=DIR, built by campaign_run14)")
        stage_d3.stamp = stamp
        try:
            ok = stage_d3.main(argv)
        finally:
            stage_d3.stamp = _stamp5
        return bool(ok) and STATE["ok"]
    return stage_d3.main(argv)


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1:]) else 1)
