"""Run paired semantic controls against the compiled milestone models."""

from pathlib import Path
import subprocess
import sys


def lean(directory: Path, source: str) -> subprocess.CompletedProcess[str]:
    path = directory / "Mutation.lean"
    path.write_text(source, encoding="utf-8")
    return subprocess.run(
        ["lean", str(path)], cwd=directory, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )


def paired(directory: Path, label: str, positive: str, mutation: str) -> None:
    result = lean(directory, positive)
    if result.returncode:
        raise RuntimeError(f"{label} positive control failed:\n{result.stdout}")

    result = lean(directory, mutation)
    errors = [line for line in result.stdout.splitlines() if "error:" in line]
    if not result.returncode or len(errors) != 1 or "proved that the proposition" not in errors[0]:
        raise RuntimeError(f"{label} mutation did not fail at its assertion:\n{result.stdout}")
    if "is false" not in result.stdout:
        raise RuntimeError(f"{label} mutation did not reduce to a false proposition:\n{result.stdout}")
    print(f"{label}: positive control passed, mutation falsified")


def main() -> None:
    directory = Path(sys.argv[1]).resolve()
    header = """import Counterexample
open NetworkStability.ChipFiring NetworkStability.Control
"""
    # A fixed point of a finite execution budget would be terminal if the
    # non-strict row and column checks sufficed. Critical passes both checks.
    paired(
        directory, "non-strict margin",
        header + "example : (compute subcritical 2 4 (start subcritical)).work 0 < 2 := by decide\n",
        header + "example : (compute critical 1 2 (start critical)).work 0 < 1 := by decide\n",
    )
    one_way = """def selected : Model 2 where
  initial := oneWay.initial
  spill j i := FACTOR * oneWay.spill j i
example : (fire selected 2 (start selected) 0).work 1 = 3 := by decide
"""
    paired(
        directory, "duplicate spill",
        header + one_way.replace("FACTOR", "1"),
        header + one_way.replace("FACTOR", "2"),
    )
    feedback = """import GuardedFeedback
open NetworkStability.GuardedFeedback
example : episode 0 0 0 EQUALITY episode 1 0 0 := by decide
"""
    paired(
        directory, "false read invariance",
        feedback.replace("EQUALITY", "≠"),
        feedback.replace("EQUALITY", "="),
    )


if __name__ == "__main__":
    main()
