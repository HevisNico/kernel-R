"""Reject semantic weakenings of the Lean proof and Python eligibility rules."""

from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise AssertionError(f"expected one mutation site: {old}")
    return source.replace(old, new, 1)


def lean_mutations():
    source = (HERE / "RestTolerance/Need.lean").read_text()
    mutations = (
        ("omit upper rest cost", " + silenceCost hi < d₀ / 2)", " < d₀ / 2)",
         "have under : z k <", "theorem needAlong_of_cumulative_rest_tolerance"),
        ("omit lower rest cost", " + fireCost lo ≤ d₀ / 2)", " ≤ d₀ / 2)",
         "have enough : Real.log", "theorem needAlong_of_cumulative_rest_tolerance"),
        ("widen the cap without raising the coefficient",
         "hi ≤ 1 / 20", "hi ≤ 1 / 10",
         "nlinarith [mul_nonneg hiPos", "theorem fire_log_gap"),
    )
    with TemporaryDirectory() as directory:
        path = Path(directory) / "Mutation.lean"
        for label, old, new, location, next_theorem in mutations:
            prefix = source.split(next_theorem, 1)[0]
            mutated = replace_once(prefix, old, new) + "end RecursiveLearning.Native.RestTolerance\n"
            path.write_text(mutated)
            line = next(i for i, text in enumerate(mutated.splitlines(), 1) if location in text)
            result = subprocess.run(
                ["lake", "env", "lean", str(path)], cwd=HERE, capture_output=True, text=True,
            )
            output = result.stdout + result.stderr
            errors = re.findall(r":(\d+):\d+: error: ([^\n]+)", output)
            if result.returncode == 0 or not errors or any(
                int(number) != line or not message.startswith(("linarith", "Tactic `linarith`"))
                for number, message in errors
            ):
                raise AssertionError(f"{label}: expected the proof inequality to fail\n{output}")
            print(f"Rejected Lean mutation: {label}")


def python_mutations():
    mutations = (
        ("status3_delta.py", "max(budget.silence_cost, budget.fire_cost)", "0",
         "test_rest_budget_omission_would_admit_ports_on_both_sides"),
        ("rule_a1_delta.py", " - budget.silence_cost", "",
         "test_rest_budget_omission_would_admit_ports_on_both_sides"),
        ("rule_a1_delta.py", " - budget.fire_cost", "",
         "test_rest_budget_omission_would_admit_ports_on_both_sides"),
        ("evidence.py", "hi > Fraction(1, 20)", "hi > Fraction(1, 10)",
         "test_malformed_or_incomplete_evidence_fails"),
    )
    files = ("evidence.py", "status3_delta.py", "rule_a1_delta.py", "test_certification.py")
    for filename, old, new, test in mutations:
        with TemporaryDirectory() as directory:
            for name in files:
                source = (HERE / name).read_text()
                (Path(directory) / name).write_text(
                    replace_once(source, old, new) if name == filename else source
                )
            result = subprocess.run(
                ["python", "-B", "-m", "unittest", f"test_certification.CertificationTest.{test}"],
                cwd=directory, capture_output=True, text=True,
            )
            if result.returncode != 1 or "AssertionError:" not in result.stderr or "ERROR:" in result.stderr:
                raise AssertionError(f"{filename}: expected an assertion failure\n{result.stderr}")
            print(f"Rejected Python mutation: {filename}, {old}")


if __name__ == "__main__":
    lean_mutations()
    python_mutations()
