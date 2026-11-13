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


    calendar = """import RoutedCalendarExamples
open NetworkStability.RoutedCalendar
"""
    # At the positive error limit, the original silent slot stays silent.
    # Moving its port score to the boundary makes the same error trigger FIRE.
    edge = """example :
  (run 2 (fun _ => 1) (start 1) [⟨0, OFFSET, []⟩]).fires = [false] := by decide
"""
    paired(
        directory, "silence margin at threshold",
        calendar + edge.replace("OFFSET", "-2"),
        calendar + edge.replace("OFFSET", "-1"),
    )
    # Remove only the B-to-A contact. The acknowledgement must then fail.
    ack = """example :
  (run 2 (fun _ => 0) (start 2)
    [⟨0, 3, []⟩, ⟨1, -3, [⟨0, 6⟩]⟩, ⟨0, -5, CONTACTS⟩]).fires =
    [true, true, true] := by decide
"""
    paired(
        directory, "drop reciprocal acknowledgement",
        calendar + ack.replace("CONTACTS", "[⟨1, 6⟩]"),
        calendar + ack.replace("CONTACTS", "[]"),
    )


    feedback = """import FeedbackExamples
open NetworkStability.AutonomousFeedback
"""
    pending = """example :
  (run MODEL 1 (fun _ => 0) 4 (start 1 [SEED])).pending = [] := by decide
"""
    paired(
        directory, "zero-decrease self-loop",
        feedback + pending.replace("MODEL", "(Ring.model 0 (fun _ => true))").replace("SEED", "0"),
        feedback + pending.replace("MODEL", "loop").replace("SEED", "()"),
    )
    and_task = """example :
  (3, true) ∈ (run (Ring.model 2 BITS) 1 (fun _ => 0) 6 (start 3 [0])).log := by decide
"""
    paired(
        directory, "ring acknowledgement with a false input",
        feedback + and_task.replace("BITS", "(fun _ => true)"),
        feedback + and_task.replace("BITS", "(fun i => i != 1)"),
    )


    orders = """import ScheduleCounterexample
open NetworkStability.AutonomousFeedback NetworkStability.AutonomousFeedback.ScheduleCounterexample
example : stored 2 (fun _ => 1) warmFirst 1 REL stored 2 (fun _ => 1) readFirst 1 := by decide
"""
    paired(
        directory, "false schedule independence",
        orders.replace("REL", "≠"),
        orders.replace("REL", "="),
    )
    traffic = """import PerpetualExamples
open NetworkStability.AutonomousFeedback
example :
  (run (RecirculatingRing.model 2) 1 (fun _ => 0) 12 (start 3 [none, some 0])).pending
    REL [] := by decide
"""
    paired(
        directory, "false queue drainage under local reserve",
        traffic.replace("REL", "≠"),
        traffic.replace("REL", "="),
    )


    room = """import ScheduleExamples
open NetworkStability.AutonomousFeedback.Schedule
example : decide (0 ≤ (-2 : Int) + 1 + ERROR) = false := by decide
"""
    paired(
        directory, "interleaving margin exhausted",
        room.replace("ERROR", "0"),
        room.replace("ERROR", "1"),
    )


if __name__ == "__main__":
    main()
