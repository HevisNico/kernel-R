"""Build and audit the bridge pieces (box reference, exp bounds), then require rejection of weakened versions.

Run from this directory with the pinned Lean on PATH, after `lake build CircuitInverterExamples`:
    python3 -B check_inverter_bridge_pieces.py
Each control mutates a copy of one of the two modules in a temporary directory and
compiles it with the package's own environment (`lake env`). No repository file is modified.
"""
from pathlib import Path
import subprocess, tempfile

ROOT = Path(__file__).resolve().parent
NEW = ["CircuitInverterBoxReference", "CircuitInverterExpBounds"]
AUDIT = "CircuitInverterBridgeAudit"


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
    if ok.returncode or "Bridge pieces audit passed" not in ok.stdout:
        raise RuntimeError(ok.stdout + ok.stderr)
    print(ok.stdout.splitlines()[0], flush=True)

    def mutate(module, old, new, count=1):
        body = originals[module]
        if body.count(old) != count:
            raise RuntimeError(f"Update the mutation: {old!r}")
        return dict(originals, **{module: body.replace(old, new)})

    box = originals["CircuitInverterBoxReference"]
    controls = [
        ("project axiom", dict(originals, CircuitInverterBoxReference=box + "\naxiom BridgeNegativeAxiom : False\n"),
         "Unexpected bridge axiom"),
        ("admitted proof", dict(originals, CircuitInverterBoxReference=box +
                                "\ntheorem BridgeNegativeAdmitted : False := by sorry\n"), "sorry"),
        ("closed form with half the window response",
         mutate("CircuitInverterBoxReference", "  else if t ≤ h + ℓ then c / a * (1 - Real.exp (-a * (t - h)))",
                "  else if t ≤ h + ℓ then c / a * (1 - Real.exp (-a * (t - h))) / 2"), "error"),
        ("peak bound at half the true peak",
         mutate("CircuitInverterBoxReference", "    boxClosed a c h ℓ t ≤ c / a * (1 - Real.exp (-a * ℓ)) := by",
                "    boxClosed a c h ℓ t ≤ c / a * (1 - Real.exp (-a * ℓ)) / 2 := by"), "error"),
        ("exp lower bound without the remainder",
         mutate("CircuitInverterExpBounds", "def expNegLower (q : ℚ) (n : ℕ) : ℚ := expNegTaylor q n - expNegRemainder q n",
                "def expNegLower (q : ℚ) (n : ℕ) : ℚ := expNegTaylor q n + expNegRemainder q n"), "error"),
    ]
    for label, texts, marker in controls:
        result = build(texts)
        output = result.stdout + result.stderr
        if result.returncode == 0 or marker not in output:
            raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-4000:]}")
        first = next((l for l in output.splitlines() if "error" in l), "")
        print(f"Rejected: {label}\n  {first[:300]}", flush=True)
    print("All bridge-piece controls rejected; repository sources untouched.", flush=True)


if __name__ == "__main__":
    main()
