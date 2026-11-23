"""Build and audit the layered-composition modules, then require rejection of weakened versions.

The modules they import (those of check.sh, plus InverterTarget and Inverters) are compiled
once into a temporary directory. Each negative control mutates a copy of one new module in
a second temporary directory. No repository file is modified.
Run from anywhere with the pinned Lean on PATH: python3 -B check_layered_composition.py
"""
from pathlib import Path
import os, subprocess, tempfile, time

ROOT = Path(__file__).resolve().parent
BASE = ["Target", "Recognition", "TwoLayerTarget", "MonotoneTarget", "MonotoneSupport",
        "MonotoneRecognition", "MonotoneCharacterization", "TwoRailsTarget", "TwoRails",
        "MonotoneOneSidedTarget", "MonotoneOneSidedRecognition", "MonotonePremiseTargets",
        "MonotonePremiseCompletenessTargets", "MonotonePremiseSoundness", "MonotonePremiseCompleteness",
        "LayeredMonotoneTarget", "LayeredMonotoneRecognition", "LayeredMonotoneCharacterization",
        "LayeredMonotoneExample", "LayeredMonotoneCheckerTargets", "LayeredMonotoneCheckerProofs",
        "InverterTarget", "Inverters"]
NEW = ["LayeredCompositionTarget", "LayeredRecognitionAt", "LayeredChain",
       "LayeredTrainingChainTarget", "LayeredTrainingChain", "LayeredChainChecks",
       "LayeredChainExamples", "LayeredInverterTarget", "LayeredInverters", "LayeredWitnessSupport",
       "LayeredWitnessAndOr", "LayeredWitnessNot", "LayeredWitnessXor"]
AUDIT = "LayeredCompositionAudit"


def lean(args, lean_path, cwd):
    env = dict(os.environ, LEAN_PATH=str(lean_path))
    return subprocess.run(["lean", "-DwarningAsError=true", *map(str, args)], cwd=cwd, env=env,
                          capture_output=True, text=True, timeout=1800)


def build_new(sources, base, cwd, times=None):
    """Compile the new modules from `sources` on top of `base`; return the failing result or the audit run."""
    out = Path(tempfile.mkdtemp())
    path = f"{out}:{base}"
    for module in NEW:
        start = time.monotonic()
        result = lean(["--root=" + str(cwd), "-o", out / f"{module}.olean", sources[module]], path, cwd)
        if times is not None:
            times[module] = time.monotonic() - start
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

    def sources_with(module=None, text=None):
        work = Path(tempfile.mkdtemp())
        paths = {}
        for name, body in originals.items():
            target = work / f"{name}.lean"
            target.write_text(text if name == module else body)
            paths[name] = target
        return paths, work

    paths, work = sources_with()
    times = {}
    ok = build_new(paths, base, work, times)
    if ok.returncode or "Layered composition audit passed" not in ok.stdout:
        raise RuntimeError(ok.stdout + ok.stderr)
    print(ok.stdout.splitlines()[0], flush=True)
    for module in NEW:
        print(f"  {module}: {times[module]:.1f} s", flush=True)

    def mutate(module, old, new, count=1):
        body = originals[module]
        if body.count(old) != count:
            raise RuntimeError(f"Update the mutation for {module}: {old!r}")
        return body.replace(old, new)

    controls = [
        ("project axiom", "LayeredChain",
         originals["LayeredChain"] + "\naxiom LayeredNegativeAxiom : False\n",
         "Unexpected layered-composition axiom"),
        ("admitted proof", "LayeredChain",
         originals["LayeredChain"] + "\ntheorem LayeredNegativeAdmitted : False := by sorry\n", "sorry"),
        ("chain without the downstream skew inequality", "LayeredCompositionTarget",
         mutate("LayeredCompositionTarget",
                "      s L + f L + (nodes i).delay a ≤ s (L + 1) + timing.skew\n\ndef checkChainDates",
                "      True\n\ndef checkChainDates"), "error"),
        ("chain without the downstream start inequality", "LayeredCompositionTarget",
         mutate("LayeredCompositionTarget",
                "    ∀ i a src, (nodes i).source a = some src →\n      s (L + 1) ≤ s L + e L + (nodes i).delay a ∧",
                "    ∀ i a src, (nodes i).source a = some src →\n      True ∧"), "error"),
        ("latency without its lower bound", "LayeredCompositionTarget",
         mutate("LayeredCompositionTarget", "∀ t ∈ r.emissions, r.start + lmin ≤ t ∧ t ≤ r.start + lmax",
                "∀ t ∈ r.emissions, r.start + lmin - lmin ≤ t ∧ t ≤ r.start + lmax"), "error"),
        ("lesson chain without the addressed cell's skew inequality", "LayeredTrainingChainTarget",
         mutate("LayeredTrainingChainTarget", "          s L + f L + (nodes i).delay a ≤ s (L + 1) + timing.skew",
                "          True"), "error"),
        ("direct rails not delayed", "LayeredInverterTarget",
         mutate("LayeredInverterTarget", "inputTrace c test = frontArrival t.emitEarly external inv",
                "inputTrace c test = frontArrival 0 external inv"), "error"),
        ("deadline-only chain claimed to accept main's example", "LayeredChainExamples",
         mutate("LayeredChainExamples", "      Example.circuit = false := by decide +kernel",
                "      Example.circuit = true := by decide +kernel"), "error"),
        ("witness: an inverter that fires on its input", "LayeredWitnessSupport",
         mutate("LayeredWitnessSupport", "if y j then [] else [T0 + 5 / 8]", "if y j then [T0 + 5 / 8] else []"),
         "error"),
        ("witness: front width below the inverter spread", "LayeredWitnessXor",
         mutate("LayeredWitnessXor", "def w : Rat := 1 / 4", "def w : Rat := 1 / 8"), "error"),
        ("witness: a wire delay that misses the next read window", "LayeredWitnessXor",
         mutate("LayeredWitnessXor", "def outNode : Node 4 1 := ⟨canonical .copy, fun a => if a = 0 then some 0 else none, fun _ => 0,",
                "def outNode : Node 4 1 := ⟨canonical .copy, fun a => if a = 0 then some 0 else none, fun _ => 1,"),
         "error"),
        ("witness: a latency bound below the emission date", "LayeredWitnessXor",
         mutate("LayeredWitnessXor", "def lmax : Nat → Rat := fun _ => 1", "def lmax : Nat → Rat := fun _ => 1 / 2"),
         "error"),
        ("witness: a cascade reading the direct rail, which cannot answer NOT", "LayeredWitnessNot",
         mutate("LayeredWitnessNot", "fun a => if a = 0 then some 1 else none", "fun a => if a = 0 then some 0 else none"),
         "error"),
        ("witness: a claimed function other than XOR", "LayeredWitnessXor",
         mutate("LayeredWitnessXor", "(y 0 != y 1)", "(y 0 || y 1)", count=2), "error"),
    ]
    for label, module, text, marker in controls:
        paths, work = sources_with(module, text)
        result = build_new(paths, base, work)
        output = result.stdout + result.stderr
        if result.returncode == 0 or marker not in output:
            raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-4000:]}")
        first = next((l for l in output.splitlines() if "error" in l), "")
        print(f"Rejected: {label}\n  {first[:300]}", flush=True)
    print(f"All {len(controls)} layered-composition controls rejected; repository sources untouched.", flush=True)


if __name__ == "__main__":
    main()
