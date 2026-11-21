"""Build and audit the inverter modules, then require rejection of weakened versions.

The existing modules they import are compiled once into a temporary directory, as
check.sh does. Each negative control mutates a copy of an inverter module in a
second temporary directory; no repository file is modified.
Run from anywhere with the pinned Lean on PATH: python3 -B check_inverters.py
"""
from pathlib import Path
import os, shutil, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
BASE = ["Target", "Recognition", "TwoLayerTarget", "MonotoneTarget", "MonotoneSupport",
        "MonotoneRecognition", "MonotoneCharacterization", "TwoRailsTarget", "TwoRails",
        "MonotoneOneSidedTarget", "MonotoneOneSidedRecognition"]
NEW = ["InverterTarget", "Inverters"]


def lean(args, lean_path, cwd):
    env = dict(os.environ, LEAN_PATH=str(lean_path))
    return subprocess.run(["lean", "-DwarningAsError=true", *map(str, args)], cwd=cwd, env=env,
                          capture_output=True, text=True, timeout=1800)


def build_new(sources, base, cwd):
    """Compile the inverter modules from `sources` on top of `base`; return the failing result or the audit run."""
    out = Path(tempfile.mkdtemp())
    path = f"{out}:{base}"
    for module in NEW:
        result = lean(["--root=" + str(cwd), "-o", out / f"{module}.olean", sources[module]], path, cwd)
        if result.returncode:
            return result
    return lean([sources["InverterAudit"]], path, cwd)


def main():
    base = Path(tempfile.mkdtemp())
    for module in BASE:
        result = lean(["-o", base / f"{module}.olean", f"{module}.lean"], base, ROOT)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
    originals = {m: (ROOT / f"{m}.lean").read_text() for m in NEW + ["InverterAudit"]}

    def sources_with(module=None, text=None):
        work = Path(tempfile.mkdtemp())
        paths = {}
        for name, body in originals.items():
            target = work / f"{name}.lean"
            target.write_text(text if name == module else body)
            paths[name] = target
        return paths, work

    paths, work = sources_with()
    ok = build_new(paths, base, work)
    if ok.returncode or "Inverter audit passed" not in ok.stdout:
        raise RuntimeError(ok.stdout + ok.stderr)
    print(ok.stdout.splitlines()[0], flush=True)

    def mutate(module, old, new, count=1):
        body = originals[module]
        if body.count(old) != count:
            raise RuntimeError(f"Update the mutation for {module}: {old!r}")
        return body.replace(old, new)

    controls = [
        ("project axiom", "Inverters", originals["Inverters"] + "\naxiom InverterNegativeAxiom : False\n",
         "Unexpected inverter axiom"),
        ("admitted proof", "Inverters",
         originals["Inverters"] + "\ntheorem InverterNegativeAdmitted : False := by sorry\n", "sorry"),
        ("spread of the inverter pulses not bounded by the read window", "InverterTarget",
         mutate("InverterTarget", "t.emitLate - t.emitEarly ≤ firstTiming.skew →",
                "t.window ≤ firstTiming.skew →"), "error"),
        ("direct rails not delayed", "InverterTarget",
         mutate("InverterTarget", "read.arrival = frontArrival t.emitEarly external inv",
                "read.arrival = frontArrival 0 external inv"), "error"),
        ("first-layer read starting with the inputs, not with the delayed rails", "InverterTarget",
         mutate("InverterTarget", "read.start = start + t.emitEarly ∧", "read.start = start ∧"), "error"),
        ("a cell that fires on its input instead of on its absence", "InverterTarget",
         mutate("InverterTarget", "r.fired = !r.input 0", "r.fired = r.input 0"), "error"),
    ]
    for label, module, text, marker in controls:
        paths, work = sources_with(module, text)
        result = build_new(paths, base, work)
        output = result.stdout + result.stderr
        if result.returncode == 0 or marker not in output:
            raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-4000:]}")
        first = next((l for l in output.splitlines() if "error" in l), "")
        print(f"Rejected: {label}\n  {first[:300]}", flush=True)
    print("All inverter controls rejected; repository sources untouched.", flush=True)


if __name__ == "__main__":
    main()
