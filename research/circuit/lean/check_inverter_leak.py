"""Build and audit the leak-asymmetry modules, then require rejection of weakened versions.

Run from this directory with the pinned Lean on PATH, after `lake build CircuitInverterExamples`:
    python3 -B check_inverter_leak.py
Each control mutates a copy of `CircuitInverterLeak.lean` in a temporary directory and
compiles it with the package's own environment (`lake env`). No repository file is modified.
"""
from pathlib import Path
import subprocess, tempfile

ROOT = Path(__file__).resolve().parent
NEW = ["CircuitInverterLeak", "CircuitInverterLeakExamples"]
AUDIT = "CircuitInverterLeakAudit"


def lean(args, out):
    cmd = 'LEAN_PATH="%s:$LEAN_PATH" lean %s' % (out, " ".join(map(str, args)))
    return subprocess.run(["lake", "env", "sh", "-c", cmd], cwd=ROOT, capture_output=True, text=True,
                          timeout=1800)


def build(texts):
    work, out = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp())
    for name, body in texts.items():
        (work / f"{name}.lean").write_text(body)
    for module in NEW:
        result = lean([f"--root={work}", "-o", out / f"{module}.olean", work / f"{module}.lean"], out)
        if result.returncode:
            return result
    return lean([work / f"{AUDIT}.lean"], out)


def main():
    originals = {m: (ROOT / f"{m}.lean").read_text() for m in NEW + [AUDIT]}
    ok = build(originals)
    if ok.returncode or "Leak audit passed" not in ok.stdout:
        raise RuntimeError(ok.stdout + ok.stderr)
    print(ok.stdout.splitlines()[0], flush=True)

    def mutate(old, new, count=1):
        body = originals["CircuitInverterLeak"]
        if body.count(old) != count:
            raise RuntimeError(f"Update the mutation: {old!r}")
        return dict(originals, CircuitInverterLeak=body.replace(old, new))

    leak = originals["CircuitInverterLeak"]
    controls = [
        ("project axiom", dict(originals, CircuitInverterLeak=leak + "\naxiom LeakNegativeAxiom : False\n"),
         "Unexpected leak axiom"),
        ("admitted proof", dict(originals, CircuitInverterLeak=leak +
                                "\ntheorem LeakNegativeAdmitted : False := by sorry\n"), "sorry"),
        ("silence margin without alpha * L",
         mutate("reference t + (ε₀ + ηH + ηm) + δ + α * L < level + Real.exp (-(a' + α) * D) * Q",
                "reference t + (ε₀ + ηH + ηm) + δ < level + Real.exp (-(a' + α) * D) * Q"), "error"),
        ("firing margin without alpha * L",
         mutate("(after : level + (ε₀ + (ηH + ηJ)) + δ + α * L < reference deadline)",
                "(after : level + (ε₀ + (ηH + ηJ)) + δ < reference deadline)"), "error"),
        ("inhibitory charge discounted at the reference leak, not the worst leak",
         mutate("level + Real.exp (-(a' + α) * D) * Q)", "level + Real.exp (-a' * D) * Q)"), "error"),
        ("silence without the bound on the leak gap",
         mutate("(leak : 0 ≤ a) (leak' : 0 ≤ a') (gap : |a - a'| ≤ α) (order : 0 ≤ τ ∧ τ ≤ D)",
                "(leak : 0 ≤ a) (leak' : 0 ≤ a') (order : 0 ≤ τ ∧ τ ≤ D)"), "error"),
    ]
    for label, texts, marker in controls:
        result = build(texts)
        output = result.stdout + result.stderr
        if result.returncode == 0 or marker not in output:
            raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-4000:]}")
        first = next((l for l in output.splitlines() if "error" in l), "")
        print(f"Rejected: {label}\n  {first[:300]}", flush=True)
    print("All leak controls rejected; repository sources untouched.", flush=True)


if __name__ == "__main__":
    main()
