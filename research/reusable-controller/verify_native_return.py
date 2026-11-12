"""Check the native read-to-rest sub-obligation; this does not close M2.

Build the native dependencies once, then compile semantic mutations into
isolated temporary import directories. Original sources/oleans are not changed.
Run with the pinned Lean toolchain: python verify_native_return.py --report PATH.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
NATIVE = HERE.parent / "recursive-learning" / "native"
FILES = ["Teaching/SelectorRead.lean", "Teaching/SelectorReturn.lean",
         "Teaching/SelectorReturnAudit.lean"]


def command(args, folder, env=None, timeout=180):
    p = subprocess.run(args, cwd=folder, env=env, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError("Mutation anchor is not unique: " + old)
    return text.replace(old, new, 1)


def hashes():
    paths = [NATIVE / f for f in FILES] + [Path(__file__).resolve(), NATIVE / "lean-toolchain"]
    return {os.path.relpath(p, HERE): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    located = shutil.which(args.lake)
    if not located:
        parser.error("lake not found")
    lake = str(Path(located).absolute())
    code, version = command([lake, "env", "lean", "--version"], NATIVE)
    if code or "version 4.35.0" not in version:
        raise RuntimeError("Wrong Lean toolchain: " + version)
    code, output = command([lake, "build", "Teaching.SelectorReturnAudit"], NATIVE, timeout=3600)
    if code or "Selector-return audit passed:" not in output:
        raise RuntimeError("Positive build/audit failed:\n" + output)
    audit = next(line for line in output.splitlines() if "Selector-return audit passed:" in line)
    print(audit, flush=True)
    code, search_path = command([lake, "env", "printenv", "LEAN_PATH"], NATIVE)
    if code:
        raise RuntimeError("Cannot read native import path: " + search_path)
    search_path = os.pathsep.join(str((NATIVE / p).resolve()) for p in search_path.strip().split(os.pathsep))
    code, lean = command([lake, "env", "which", "lean"], NATIVE)
    if code:
        raise RuntimeError("Cannot locate native Lean executable")
    lean = lean.strip()
    original = {f: (NATIVE / f).read_text() for f in FILES}
    before = hashes()
    target = FILES[1]
    mutations = [
        ("allow_zero_slow_recovery", target,
         "(slow : s.main 0 = .slow) (above : 1 / 10 < s.x 0 .q) (positive : 0 < s.x 0 .b)",
         "(slow : s.main 0 = .slow) (above : 1 / 10 < s.x 0 .q) (positive : 0 ≤ s.x 0 .b)", None),
        ("invent_prepared_charge", target,
         "  charge : final.x 0 .q = 1 / 10", "  charge : final.x 0 .q = 13 / 20", None),
        ("alter_retained_gain", target,
         "  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)",
         "  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p) + 1", None),
        ("reset_sensor_residues", FILES[0],
         "  auxiliaryRest : ∀ p, RestBand (final.x 0 (.m p))",
         "  auxiliaryRest : ∀ p, final.x 0 (.m p) = 1 / 40", None),
        ("unused_project_axiom", target, "\nend RecursiveLearning.Native\n",
         "\nend RecursiveLearning.Native\naxiom unusedSelectorReturnAxiom : True\n", "Unexpected project axiom"),
        ("admitted_physical_return", target,
         "PhysicalInvariant θ run.tail.final := run.execution.physical_invariant box initial",
         "PhysicalInvariant θ run.tail.final := by sorry", "Unexpected axiom sorryAx"),
    ]
    results = []
    for name, changed, old, new, marker in mutations:
        with tempfile.TemporaryDirectory(prefix="selector-return-") as td:
            folder = Path(td)
            # Lean resolves an import prefix as a unit. Keep a private copy of
            # the compiled Teaching prefix so no missing import can masquerade
            # as rejection and mutant output cannot overwrite original oleans.
            shutil.copytree(NATIVE / ".lake/build/lib/lean/Teaching", folder / "Teaching")
            for file, content in original.items():
                p = folder / file
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(replace_once(content, old, new) if file == changed else content)
            env = dict(os.environ, LEAN_PATH=str(folder) + os.pathsep + search_path)
            # Only the changed module is compiled. Its imports are the already
            # checked originals; the audit imports this mutant olean first.
            code, log = command([lean, "-o", changed.removesuffix(".lean") + ".olean", changed], folder, env)
            if marker:
                if code:
                    raise RuntimeError(name + ": mutant must compile before the audit:\n" + log)
                code, log = command([lean, FILES[2]], folder, env)
                rejected = code != 0 and marker in log
            else:
                rejected = code != 0 and bool(re.search(re.escape(changed) + r":\d+:\d+: error:", log))
            malformed = any(s in log.lower() for s in
                            ("unexpected token", "unknown module", "unknown identifier", "unexpected identifier",
                             "object file", "does not exist", "failed to load"))
            if not rejected or malformed:
                raise RuntimeError(name + ": not rejected by intended semantic check:\n" + log)
            results.append({"mutation": name, "rejected": True, "check": marker or changed})
            print(name + ": rejected", flush=True)
    if hashes() != before:
        raise RuntimeError("Original sources changed")
    report = {"lean": version.strip(), "scope": "read-to-rest only; M2 remains open",
              "positive_build": True, "axiom_audit": audit, "negative_controls": results,
              "source_sha256": before}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print("All six native controls rejected; original sources unchanged.", flush=True)


if __name__ == "__main__":
    main()
