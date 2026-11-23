"""Build and audit the varying-leak modules, then require rejection of weakened versions.

Run from this directory with the pinned Lean on PATH, after `lake build CircuitInverterExamples`:
    python3 -B check_inverter_varying.py
Each control mutates a copy of `CircuitInverterVaryingLeak.lean` in a temporary directory and
compiles it with the package's own environment (`lake env`). No repository file is modified.
"""
from pathlib import Path
import subprocess, tempfile

ROOT = Path(__file__).resolve().parent
NEW = ["CircuitInverterVaryingLeak", "CircuitInverterVaryingLeakExamples"]
AUDIT = "CircuitInverterVaryingLeakAudit"


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
    if ok.returncode or "Varying-leak audit passed" not in ok.stdout:
        raise RuntimeError(ok.stdout + ok.stderr)
    print(ok.stdout.splitlines()[0], flush=True)

    def mutate(old, new, count=1):
        body = originals["CircuitInverterVaryingLeak"]
        if body.count(old) != count:
            raise RuntimeError(f"Update the mutation: {old!r}")
        return dict(originals, CircuitInverterVaryingLeak=body.replace(old, new))

    leak = originals["CircuitInverterVaryingLeak"]
    controls = [
        ("project axiom", dict(originals, CircuitInverterVaryingLeak=leak + "\naxiom VaryingNegativeAxiom : False\n"),
         "Unexpected varying-leak axiom"),
        ("admitted proof", dict(originals, CircuitInverterVaryingLeak=leak +
                                "\ntheorem VaryingNegativeAdmitted : False := by sorry\n"), "sorry"),
        ("silence margins without alpha * X * D",
         mutate("(ε₀ + (ηH + α * X * D) + ηm)", "(ε₀ + ηH + ηm)", count=2), "error"),
        ("firing margins without alpha * X * deadline",
         mutate("(ε₀ + ((ηH + α * X * deadline) + ηJ))", "(ε₀ + (ηH + ηJ))", count=2), "error"),
        ("drift bound without the state bound X",
         mutate("≤ α * X * D := by", "≤ α * D := by"), "error"),
    ]
    for label, texts, marker in controls:
        result = build(texts)
        output = result.stdout + result.stderr
        if result.returncode == 0 or marker not in output:
            raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-4000:]}")
        first = next((l for l in output.splitlines() if "error" in l), "")
        print(f"Rejected: {label}\n  {first[:300]}", flush=True)
    print("All varying-leak controls rejected; repository sources untouched.", flush=True)


if __name__ == "__main__":
    main()
