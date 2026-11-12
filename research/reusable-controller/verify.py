"""Build, audit, and reject semantic mutations in isolated temporary copies.

Run from any directory: python verify.py [--lake /path/to/lake].
Requires the pinned Lean toolchain, Python's standard library, and the sibling
recursive-learning package. It never modifies the original Lean sources.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent


def source_hashes():
    paths = sorted(HERE.rglob("*.lean"))
    paths = [p for p in paths if ".lake" not in p.relative_to(HERE).parts]
    paths += [HERE / "lakefile.toml", HERE / "lean-toolchain", HERE / "verify.py",
              HERE.parent / "recursive-learning/RecursiveLearning/Model.lean"]
    return {str(p.relative_to(HERE)) if p.is_relative_to(HERE) else
            "../recursive-learning/RecursiveLearning/Model.lean":
            hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def build(lake, folder):
    result = subprocess.run([lake, "build"], cwd=folder, capture_output=True,
                            text=True, timeout=180)
    return result.returncode, result.stdout + result.stderr


def replace_once(folder, file, old, new):
    path = folder / file
    text = path.read_text()
    if text.count(old) != 1:
        raise RuntimeError(f"mutation anchor not unique: {file}: {old}")
    path.write_text(text.replace(old, new, 1))


def admit_ready(folder):
    path = folder / "ReusableController/Proofs.lean"
    text = path.read_text()
    start = text.index("theorem round_ready")
    body = text.index(" := by", start)
    end = text.index("\ntheorem round_accounting", body)
    path.write_text(text[:body] + " := by\n  sorry\n" + text[end:])


def add_axiom(folder):
    path = folder / "ReusableController/Model.lean"
    path.write_text(path.read_text() + "\naxiom unusedControllerAxiom : True\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    located = shutil.which(args.lake)
    if located is None:
        parser.error("lake not found; install the version in lean-toolchain")
    lake = str(Path(located).absolute())
    original_hashes = source_hashes()
    tool = subprocess.run([lake, "env", "lean", "--version"], cwd=HERE,
                          capture_output=True, text=True, check=True)
    if "version 4.35.0" not in tool.stdout:
        raise RuntimeError("wrong Lean toolchain: " + tool.stdout)
    code, output = build(lake, HERE)
    if code or "Audit passed:" not in output:
        raise RuntimeError("positive build/audit failed:\n" + output)
    print("Positive build and axiom audit passed", flush=True)

    model = "ReusableController/Model.lean"
    mutations = [
        ("accept_failed_trial", lambda d: replace_once(d, model,
            "if (lesson.train need).retained then", "if true then"), "Proofs.lean"),
        ("stop_progress_on_rejection", lambda d: replace_once(d, model,
            "else block tested axis", "else tested"), "Proofs.lean"),
        ("omit_validation_cost", lambda d: replace_once(d, model,
            "s.trialPulses + lesson.cost", "s.trialPulses"), "Proofs.lean"),
        ("wrong_commit_credit", lambda d: replace_once(d, model,
            "| .preparation => { s with lesson := trial, accepted := s.accepted + 1 }",
            "| .preparation => { s with lesson := trial, accepted := s.accepted + 2 }"),
            "Proofs.lean"),
        ("unused_project_axiom", add_axiom, "Unexpected project axiom"),
        ("admitted_round_ready", admit_ready, "Unexpected axiom sorryAx"),
    ]
    results = []
    for name, mutate, marker in mutations:
        # Keep the sibling path dependency pointing to the real, unmodified package.
        with tempfile.TemporaryDirectory(prefix=".controller-negative-", dir=HERE.parent) as td:
            folder = Path(td)
            shutil.copytree(HERE, folder, dirs_exist_ok=True,
                            ignore=shutil.ignore_patterns(".lake", "__pycache__", "validation.json"))
            mutate(folder)
            code, log = build(lake, folder)
            diagnostic = re.search(r"error: ReusableController/Proofs\.lean:\d+:\d+:", log)
            rejected = code != 0 and (bool(diagnostic) if marker == "Proofs.lean" else marker in log)
            malformed = any(x in log for x in ("unexpected token", "unknown module prefix",
                                               "unknown identifier", "unexpected identifier"))
            if not rejected or malformed:
                raise RuntimeError(f"{name}: not rejected by its intended check:\n{log}")
            results.append({"mutation": name, "rejected": True, "check": marker})
            print(name + ": rejected", flush=True)
    if source_hashes() != original_hashes:
        raise RuntimeError("original sources changed during validation")
    report = {"lean": tool.stdout.strip(), "positive_build": True,
              "axiom_audit": True, "negative_controls": results,
              "source_sha256": original_hashes}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print("All six negative controls rejected; original sources unchanged", flush=True)


if __name__ == "__main__":
    main()
