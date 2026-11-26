"""analyze9.py, verifying stage_d6 seals (defect D1 of the final dry run, fixed by the owner's decision, 2026-11-26).
Development only. analyze9.py and the earlier analyses are kept as they are.

**The defect.** analyze3.regenerate re-derives each sealed prediction from its stage-D record with the stage-D script
the prediction names in `code`, taking the first of (stage_d5.py, stage_d4.py, stage_d3.py). A stage_d6 prediction
names stage_d5.py too (stage_d6 runs stage_d5's stamp), so the regeneration ran stage_d5. Its prediction has no
`kernel` field, so every stage_d6 seal read not_sealed.

**The rule here.** A prediction names its stage-D script in `code`; stage_d6.py names itself there.
- **The script is the latest stage_d<N>.py the prediction names:** stage_d6.py, else stage_d5.py, stage_d4.py or
  stage_d3.py, in that order.
- **The kernel field must agree with that name.** A prediction naming stage_d6.py must carry `kernel`, and one carrying
  `kernel` must name stage_d6.py. Otherwise the seal is refused (not_sealed), with the reason.
- **The regeneration with stage_d6** runs its kernel check, on the kernel library built here from the pinned Lean
  sources: campaign_run14.build_kernel into OUTDIR/kernel_build, refused if a source differs from KERNEL_SOURCES.
- **The regenerated prediction must equal the sealed bytes, the kernel field included.**

Everything else is analyze9's. RESULTS.json gets the format layered-campaign-results/10, analyze10_sha256 and
`stage_d_script_rule`. The kernel build's time stays in OUTDIR/kernel_build/KERNEL_BUILD.json, outside RESULTS.json,
so two runs are byte-identical.

  analyze10.py OUTDIR ROOT [ROOT ...] [times=...] [thresholds=thresholds.json] [controls=DIR]
"""
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402
import analyze3 as A3  # noqa: E402
import analyze9 as A9  # noqa: E402
import campaign_run14 as C14  # noqa: E402

FORMAT = "layered-campaign-results/10"
SCRIPTS = ("stage_d6.py", "stage_d5.py", "stage_d4.py", "stage_d3.py")
RULE = ("the stage-D script is the latest stage_d<N>.py the sealed prediction names in `code` (stage_d6.py names "
        "itself); a prediction naming stage_d6.py must carry `kernel` and one carrying `kernel` must name stage_d6.py; "
        "the regeneration (with stage_d6, on the kernel library built from the pinned Lean sources) must equal the "
        "sealed bytes, the kernel field included")
_regenerate = A3.regenerate


def regenerate(root, name, plan, status):
    d = Path(root) / name
    seal_file = next((p for p in (d / "seal").glob("*.json") if p.name != "MANIFEST.json"), None)
    if seal_file is not None:
        pred = json.loads(seal_file.read_bytes())
        names6, kernel = "stage_d6.py" in pred.get("code", {}), "kernel" in pred
        if names6 and not kernel:
            return False, "the sealed prediction names stage_d6.py but has no kernel field"
        if kernel and not names6:
            return False, "the sealed prediction has a kernel field but does not name stage_d6.py"
    return _regenerate(root, name, plan, status)


def main(outdir, *args):
    out = Path(outdir)
    out.mkdir(parents=True, exist_ok=True)
    build, _ = C14.build_kernel(out)
    saved = A3.SCRIPTS, A3.regenerate, os.environ.get("LAYERED_KERNEL_BUILD")
    A3.SCRIPTS, A3.regenerate = SCRIPTS, regenerate
    os.environ["LAYERED_KERNEL_BUILD"] = str(build)
    try:
        A9.main(outdir, *args)
    finally:
        A3.SCRIPTS, A3.regenerate = saved[0], saved[1]
        if saved[2] is None:
            os.environ.pop("LAYERED_KERNEL_BUILD", None)
        else:
            os.environ["LAYERED_KERNEL_BUILD"] = saved[2]
    res = json.loads((out / "RESULTS.json").read_text())
    res.update(format=FORMAT, analyze10_sha256=A.sha(__file__), stage_d_script_rule=RULE,
               kernel_sources_sha256=C14.KERNEL_SOURCES)
    (out / "RESULTS.json").write_bytes(A.canon(res))
    (out / "SHA256SUMS").write_text(f"{A.sha(out / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=A.sha(out / "RESULTS.json"), seal_defects=len(res.get("seal_defects", [])))))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
