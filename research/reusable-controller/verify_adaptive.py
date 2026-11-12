"""Check adaptive contracts and reject semantic mutations in isolated copies.

Uses the same pinned, Mathlib-free toolchain and axiom audit as verify.py.
Every negative control must fail its designated theorem/audit; malformed
syntax, missing imports and unknown identifiers are never accepted as proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

import verify

HERE = Path(__file__).resolve().parent


def source_hashes():
    result = verify.source_hashes()
    result["verify_adaptive.py"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def admit_robustness(folder):
    path = folder / "ReusableController/Selection.lean"
    text = path.read_text()
    start = text.index("theorem robust_cost_nondegradation")
    body = text.index(" := by", start)
    end = text.index("\ntheorem selectStep_live", body)
    path.write_text(text[:body] + " := by\n  sorry\n" + text[end:])


def unused_axiom(folder):
    path = folder / "ReusableController/NoisySearch.lean"
    path.write_text(path.read_text() + "\naxiom unusedAdaptiveAxiom : True\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    located = shutil.which(args.lake)
    if located is None:
        parser.error("lake not found; install lean-toolchain")
    lake = str(Path(located).absolute())
    original = source_hashes()
    tool = subprocess.run([lake, "env", "lean", "--version"], cwd=HERE,
                          capture_output=True, text=True, check=True)
    if "version 4.35.0" not in tool.stdout:
        raise RuntimeError("wrong Lean toolchain: " + tool.stdout)
    code, log = verify.build(lake, HERE)
    if code or "Audit passed:" not in log:
        raise RuntimeError("positive build/audit failed:\n" + log)
    print("Positive adaptive build and axiom audit passed", flush=True)
    search = "ReusableController/NoisySearch.lean"
    selection = "ReusableController/Selection.lean"

    def mutation(file, old, new):
        return lambda folder: verify.replace_once(folder, file, old, new)

    controls = [
        ("margin_tau_allows_regression", mutation(selection,
            "new + 2 * (tau : Int) ≤ old ∧ new < old",
            "new + (tau : Int) ≤ old ∧ new < old"), "Selection.lean"),
        ("zero_error_ties_destroy_strict_potential", mutation(selection,
            "new + 2 * (tau : Int) ≤ old ∧ new < old",
            "new + 2 * (tau : Int) ≤ old ∧ new ≤ old"), "Selection.lean"),
        ("ambiguous_failure_falsely_blocks", mutation(search,
            "| .unknown => tested", "| .unknown => block tested axis"), "NoisySearch.lean"),
        ("ambiguous_trial_is_free", mutation(search,
            "| .unknown => tested", "| .unknown => tried"), "NoisySearch.lean"),
        ("uncertified_success_is_committed", mutation(search,
            "if (tau : Int) ≤ reading then .pass",
            "if 0 ≤ reading then .pass"), "NoisySearch.lean"),
        ("adoption_erases_live_memory", mutation(selection,
            "score := report p, adoptions := s.adoptions + 1 }",
            "score := report p, adoptions := s.adoptions + 1, live := initial s.live.lesson }"),
            "Selection.lean"),
        ("baseline_validation_is_free", mutation(selection,
            "⟨seed, report seed, pending, charge seed, 1, 0, live⟩",
            "⟨seed, report seed, pending, 0, 1, 0, live⟩"), "AdaptiveExamples.lean"),
        ("candidate_validation_is_free", mutation(selection,
            "spent := s.spent + charge p", "spent := s.spent"), "Selection.lean"),
        ("candidate_queue_not_consumed", mutation(selection,
            "pending := ps, spent :=", "pending := s.pending, spent :="), "Selection.lean"),
        ("unused_adaptive_axiom", unused_axiom, "Unexpected project axiom"),
        ("admitted_robustness", admit_robustness, "Unexpected axiom sorryAx"),
    ]
    results = []
    for name, mutate, marker in controls:
        with tempfile.TemporaryDirectory(prefix=".adaptive-negative-", dir=HERE.parent) as td:
            folder = Path(td)
            shutil.copytree(HERE, folder, dirs_exist_ok=True, ignore=shutil.ignore_patterns(
                ".lake", "__pycache__", "validation.json", "adaptive-validation.json"))
            mutate(folder)
            code, log = verify.build(lake, folder)
            diagnostic = re.search(r"error: ReusableController/" + re.escape(marker) + r":\d+:\d+:", log)
            rejected = code != 0 and (bool(diagnostic) if marker.endswith(".lean") else marker in log)
            malformed = any(x in log for x in ("unexpected token", "unknown module prefix",
                                               "unknown identifier", "unexpected identifier"))
            if not rejected or malformed:
                raise RuntimeError(f"{name}: not rejected by its intended check:\n{log}")
            results.append({"mutation": name, "rejected": True, "check": marker})
            print(name + ": rejected", flush=True)
    if source_hashes() != original:
        raise RuntimeError("original sources changed during validation")
    report = {"lean": tool.stdout.strip(), "positive_build": True, "axiom_audit": True,
              "negative_controls": results, "source_sha256": original}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"All {len(results)} adaptive negative controls rejected; original sources unchanged", flush=True)


if __name__ == "__main__":
    main()
