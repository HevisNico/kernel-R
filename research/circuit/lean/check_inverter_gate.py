"""Build and audit the gate bridge (Taylor bounds, assembly, seed 9901), then require rejection of weakened versions.

Run from this directory with the pinned Lean on PATH, after `lake build CircuitInverterExamples`:
    python3 -B check_inverter_gate.py
Each control mutates a copy of one of the two modules in a temporary directory and
compiles it with the package's own environment (`lake env`). No repository file is modified.
"""
from pathlib import Path
import subprocess, tempfile

ROOT = Path(__file__).resolve().parent
NEW = ["CircuitInverterVaryingLeak", "CircuitInverterBoxReference", "CircuitInverterTaylor",
       "CircuitInverterGateBridge", "CircuitInverterGate9901"]
AUDIT = "CircuitInverterGateAudit"


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
    if ok.returncode or "Gate bridge audit passed" not in ok.stdout:
        raise RuntimeError(ok.stdout + ok.stderr)
    print(ok.stdout.splitlines()[0], flush=True)

    def mutate(module, old, new, count=1):
        body = originals[module]
        if body.count(old) != count:
            raise RuntimeError(f"Update the mutation: {old!r}")
        return dict(originals, **{module: body.replace(old, new)})

    bridge = originals["CircuitInverterGateBridge"]
    controls = [
        ("project axiom", dict(originals, CircuitInverterGateBridge=bridge + "\naxiom GateNegativeAxiom : False\n"),
         "Unexpected gate axiom"),
        ("admitted proof", dict(originals, CircuitInverterGateBridge=bridge +
                                "\ntheorem GateNegativeAdmitted : False := by sorry\n"), "sorry"),
        ("degree-6 sum claimed as a lower bound",
         mutate("CircuitInverterTaylor", "theorem expNegSum_six_le {x : ℝ} (hx : 0 ≤ x) : expNegSum 6 x ≤ Real.exp (-x) := by",
                "theorem expNegSum_six_le {x : ℝ} (hx : 0 ≤ x) : expNegSum 7 x ≤ Real.exp (-x) := by"), "error"),
        ("state bound twice the gate's H0 * hl",
         mutate("CircuitInverterGateBridge", "|actual u| ≤ (d.H0 : ℝ) * d.hl)",
                "|actual u| ≤ 2 * ((d.H0 : ℝ) * d.hl))", count=2), "error"),
        ("seed 9901 with a threshold error of 0.1",
         mutate("CircuitInverterGate9901", "4767 / 1000000, 1299 / 500000, 401 / 1000000,",
                "4767 / 1000000, 1299 / 500000, 100000 / 1000000,"), "error"),
    ]
    for label, texts, marker in controls:
        result = build(texts)
        output = result.stdout + result.stderr
        if result.returncode == 0 or marker not in output:
            raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-4000:]}")
        first = next((l for l in output.splitlines() if "error" in l), "")
        print(f"Rejected: {label}\n  {first[:300]}", flush=True)
    print("All gate-bridge controls rejected; repository sources untouched.", flush=True)


if __name__ == "__main__":
    main()
