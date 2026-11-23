"""Build and audit training through the inverters, then require rejection of weakened versions.

The modules they import are compiled once into a temporary directory, as check.sh does.
Each negative control mutates a copy of a new module in a second temporary directory; no
repository file is modified. Run with the pinned Lean on PATH: python3 -B check_inverter_training.py
"""
from pathlib import Path
import os, subprocess, tempfile

ROOT = Path(__file__).resolve().parent
BASE = ["Target", "Recognition", "TwoLayerTarget", "MonotoneTarget", "MonotoneSupport",
        "MonotoneRecognition", "MonotoneCharacterization", "TwoRailsTarget", "TwoRails",
        "MonotoneOneSidedTarget", "MonotoneOneSidedRecognition", "MonotonePremiseTargets",
        "MonotonePremiseCompletenessTargets", "MonotonePremiseSoundness",
        "InverterTarget", "Inverters", "InverterWitness"]
NEW = ["TwoRailsExplicit", "InverterTraining", "InverterTrainingWitness"]
AUDIT = "InverterTrainingAudit"


def lean(args, lean_path, cwd):
    env = dict(os.environ, LEAN_PATH=str(lean_path))
    return subprocess.run(["lean", "-DwarningAsError=true", *map(str, args)], cwd=cwd, env=env,
                          capture_output=True, text=True, timeout=1800)


def build_new(sources, base, cwd):
    out = Path(tempfile.mkdtemp())
    path = f"{out}:{base}"
    for module in NEW:
        result = lean(["--root=" + str(cwd), "-o", out / f"{module}.olean", sources[module]], path, cwd)
        if result.returncode:
            return result
    return lean([sources[AUDIT]], path, cwd)


def main():
    base = Path(tempfile.mkdtemp())
    for module in BASE:
        result = lean(["-o", base / f"{module}.olean", f"{module}.lean"], base, ROOT)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
    originals = {m: (ROOT / f"{m}.lean").read_text() for m in NEW + [AUDIT]}

    def sources_with(mutations=()):
        work = Path(tempfile.mkdtemp())
        texts = dict(originals)
        for module, text in mutations:
            texts[module] = text
        paths = {}
        for name, body in texts.items():
            (work / f"{name}.lean").write_text(body)
            paths[name] = work / f"{name}.lean"
        return paths, work

    paths, work = sources_with()
    ok = build_new(paths, base, work)
    if ok.returncode or "Inverter training audit passed" not in ok.stdout:
        raise RuntimeError(ok.stdout + ok.stderr)
    print(ok.stdout.splitlines()[0], flush=True)

    def mutate(module, old, new, count=1):
        body = originals[module]
        if body.count(old) != count:
            raise RuntimeError(f"Update the mutation for {module}: {old!r}")
        return module, body.replace(old, new)

    controls = [
        ("project axiom", [("InverterTraining", originals["InverterTraining"] +
                            "\naxiom InverterTrainingNegativeAxiom : False\n")], "Unexpected inverter-training axiom"),
        ("admitted proof", [("InverterTraining", originals["InverterTraining"] +
                             "\ntheorem InverterTrainingNegativeAdmitted : False := by sorry\n")], "sorry"),
        ("training reads not required to show the rails of the target",
         [mutate("InverterTraining", "rails (fun j => (external j).isSome) = p.first.target a) ∧",
                 "True) ∧")], "error"),
        ("inverter slot longer than the first-layer slot",
         [mutate("InverterTraining", "(fits : s.duration ≤ firstTiming.duration)",
                 "(fits : firstTiming.duration ≤ s.duration)", count=2)], "error"),
        ("witness: training on the present input, whose rails are not the target",
         [mutate("InverterTrainingWitness", "frontReadAt (10 * r.val) absent (r.val ≠ 0)",
                 "frontReadAt (10 * r.val) present (r.val ≠ 0)")], "error"),
        ("witness: an inverter pulse later than emitLate",
         [mutate("InverterTrainingWitness", "[s + 5 / 8]", "[s + 7 / 8]")], "error"),
    ]
    for label, mutations, marker in controls:
        paths, work = sources_with(mutations)
        result = build_new(paths, base, work)
        output = result.stdout + result.stderr
        if result.returncode == 0 or marker not in output:
            raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-4000:]}")
        first = next((l for l in output.splitlines() if "error" in l), "")
        print(f"Rejected: {label}\n  {first[:300]}", flush=True)
    print("All inverter-training controls rejected; repository sources untouched.", flush=True)


if __name__ == "__main__":
    main()
