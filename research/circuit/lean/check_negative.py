"""Check the axiom boundary and reject unjustifiably tighter error budgets.

Run after `lake build`. Sources are temporarily mutated, then restored in a
finally block and rebuilt. Do not run concurrently with edits or Lean builds
in this checkout. No circuit data or netlist is modified.
"""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
TIMING = ROOT / "CircuitTiming.lean"
NEED = ROOT / "CircuitNeed.lean"
VARIABLE = ROOT.parents[1] / "recursive-learning/native/Search/VariableNeedTolerance.lean"
WIDE = ROOT.parents[1] / "recursive-learning/native/Training/WideDoseRead.lean"


def build():
    return subprocess.run(
        ["lake", "build", "CircuitAudit"], cwd=ROOT,
        capture_output=True, text=True, timeout=180,
    )


def require_success(result):
    if result.returncode:
        raise RuntimeError((result.stdout + result.stderr)[-6000:])


def main():
    require_success(build())
    original = TIMING.read_text()
    bound = "|root - nominal| ≤ (ε + δ) / speed"
    if original.count(bound) != 2:
        raise RuntimeError("Update the latency mutation for the current theorem statements")
    originals = {p: p.read_text() for p in (TIMING, VARIABLE, WIDE, NEED)}
    dose_room = "a + m * b + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2"
    if originals[VARIABLE].count(dose_room) != 2:
        raise RuntimeError("Update the variable-dose mutation for the current statements")
    controls = [
        ("project axiom", TIMING, original + "\naxiom CircuitNegativeAxiom : False\n",
         "Unexpected project axiom"),
        ("admitted proof", TIMING, original + "\ntheorem CircuitNegativeAdmitted : False := by sorry\n",
         "sorryAx"),
        ("omitted threshold-error budget", TIMING,
         original.replace(bound, "|root - nominal| ≤ ε / speed", 1),
         "error: CircuitTiming.lean"),
        ("omitted dose accumulation factor", VARIABLE,
         originals[VARIABLE].replace(dose_room, "a + b + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2", 1),
         "error: Search/VariableNeedTolerance.lean"),
        ("omitted sensor-dose uncertainty", NEED,
         originals[NEED].replace("m * (k * η + σ + e)", "m * (k * η + e)", 1),
         "error: CircuitNeed.lean"),
        ("old pair window with dose 0.06", WIDE,
         originals[WIDE].replace("59 / 250", "239 / 1000").replace("59 / 500", "239 / 2000"),
         "error: Training/WideDoseRead.lean"),
    ]
    try:
        for label, path, mutated, marker in controls:
            path.write_text(mutated)
            result = build()
            output = result.stdout + result.stderr
            if result.returncode == 0 or marker not in output:
                raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-6000:]}")
            print(f"Rejected: {label}", flush=True)
            path.write_text(originals[path])
    finally:
        for path, contents in originals.items():
            path.write_text(contents)
        require_success(build())
        print("Original sources restored; build and axiom audit pass", flush=True)


if __name__ == "__main__":
    main()
