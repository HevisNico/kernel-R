"""Check the single-source gate: the definitions compile with plain `lean` (no Mathlib),
the bridge and seed 9901 build on them, the audit passes, and weakened versions are rejected.

Run from this directory with the pinned Lean on PATH, after `lake build CircuitInverterExamples`
and with the oleans of CircuitInverterVaryingLeak, CircuitInverterBoxReference,
CircuitInverterTaylor and CircuitInverterGateBridge built (e.g. by check_inverter_gate.py's
modules being in the lakefile):
    python3 -B check_inverter_gate_single.py
Each control mutates a copy in a temporary directory. No repository file is modified.
"""
from pathlib import Path
import os, subprocess, tempfile

ROOT = Path(__file__).resolve().parent
ENGINE = ["CircuitInverterVaryingLeak", "CircuitInverterBoxReference", "CircuitInverterTaylor",
          "CircuitInverterGateBridge"]
NEW = ["CircuitInverterGate", "CircuitInverterGateProof", "CircuitInverterGateInstance9901"]
AUDIT = "CircuitInverterGateProofAudit"


def lean(args, out):
    cmd = 'LEAN_PATH="%s:$LEAN_PATH" lean %s' % (out, " ".join(map(str, args)))
    return subprocess.run(["lake", "env", "sh", "-c", cmd], cwd=ROOT, capture_output=True, text=True,
                          timeout=1800)


def core_only(body):
    work = Path(tempfile.mkdtemp())
    (work / "CircuitInverterGate.lean").write_text(body)
    env = {k: v for k, v in os.environ.items() if k != "LEAN_PATH"}
    return subprocess.run(["lean", "-DwarningAsError=true", str(work / "CircuitInverterGate.lean")],
                          cwd=work, env=env, capture_output=True, text=True, timeout=600)


def build(texts, out):
    work, own = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp())
    for name, body in texts.items():
        (work / f"{name}.lean").write_text(body)
    for module in NEW:
        result = lean([f"--root={work}", "-o", own / f"{module}.olean", work / f"{module}.lean"], f"{own}:{out}")
        if result.returncode:
            return result
    return lean([work / f"{AUDIT}.lean"], f"{own}:{out}")


def main():
    originals = {m: (ROOT / f"{m}.lean").read_text() for m in ENGINE + NEW + [AUDIT]}
    core = core_only(originals["CircuitInverterGate"])
    if core.returncode:
        raise RuntimeError("Gate definitions need more than core Lean:\n" + core.stdout + core.stderr)
    print("Core-only compile of CircuitInverterGate: OK", flush=True)
    rejected = core_only("import Mathlib.Tactic\n" + originals["CircuitInverterGate"])
    if rejected.returncode == 0:
        raise RuntimeError("Core-only check did not reject a Mathlib import")
    print("Rejected: Mathlib import in the core-only module", flush=True)

    out = Path(tempfile.mkdtemp())
    for module in ENGINE:
        result = lean(["-o", out / f"{module}.olean", ROOT / f"{module}.lean"], out)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
    ok = build(originals, out)
    if ok.returncode or "Single-source gate audit passed" not in ok.stdout:
        raise RuntimeError(ok.stdout + ok.stderr)
    print(ok.stdout.splitlines()[0], flush=True)

    def mutate(module, old, new):
        body = originals[module]
        if body.count(old) != 1:
            raise RuntimeError(f"Update the mutation: {old!r}")
        return dict(originals, **{module: body.replace(old, new)})

    proof = originals["CircuitInverterGateProof"]
    controls = [
        ("project axiom", dict(originals, CircuitInverterGateProof=proof + "\naxiom GateNegativeAxiom : False\n"),
         "Unexpected gate axiom"),
        ("admitted proof", dict(originals, CircuitInverterGateProof=proof +
                                "\ntheorem GateNegativeAdmitted : False := by sorry\n"), "sorry"),
        ("StateBound dropped from H0 * hl",
         mutate("CircuitInverterGate", "0 ≤ xAbsent ∧ xAbsent ≤ d.H0 * d.hl", "0 ≤ xAbsent"), "error"),
        ("seed 9901 xAbsent above H0 * hl (1.389 > 1.35)",
         mutate("CircuitInverterGateInstance9901", "def xAbsent : Rat := 23779 / 20000",
                "def xAbsent : Rat := 27779 / 20000"), "error"),
        ("seed 9901 with a threshold error of 0.1",
         mutate("CircuitInverterGateInstance9901", "4767 / 1000000, 1299 / 500000, 401 / 1000000,",
                "4767 / 1000000, 1299 / 500000, 100000 / 1000000,"), "error"),
    ]
    for label, texts, marker in controls:
        result = build(texts, out)
        output = result.stdout + result.stderr
        if result.returncode == 0 or marker not in output:
            raise RuntimeError(f"Negative control did not fail as intended: {label}\n{output[-4000:]}")
        first = next((l for l in output.splitlines() if "error" in l), "")
        print(f"Rejected: {label}\n  {first[:300]}", flush=True)
    print("All single-source gate controls rejected; repository sources untouched.", flush=True)


if __name__ == "__main__":
    main()
