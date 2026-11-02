#!/usr/bin/env python3
"""Paired Lean controls for irregular, memory-preserving continuations."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = """import KernelR
open KernelR.Hybrid
noncomputable section
"""
IRREGULAR_SCHEDULE = """example : FutureSchedule (15/2) where
  time := fun k => 10 + (15/2 : ℝ) * (k : ℝ) + (k : ℝ)^2
  separated := by
    intro k
    dsimp
    push_cast
    nlinarith
"""


def pair(label, template, good, bad):
    if "@v@" not in template or good == bad:
        raise ValueError("invalid paired control")
    return label, template.replace("@v@", good), template.replace("@v@", bad)


def cases():
    prefix = """example {n θ route active reference cell port ε}
    (law : @PulseContract n θ route active reference cell port)
    (hb : PhysicalBox θ ε) (schedule : FutureSchedule law.duration)
    (initial : Snapshot n) (hi : LearnedDomain θ active reference initial)
    (hfirst : initial.time ≤ schedule.time 0) (k : ℕ) {u : Snapshot n}
    (run : Execution θ route
      (withFuture initial (sourceQueue cell port schedule.time k)) u)
    (hc : CompleteThrough run (law.readyStates schedule initial hi hfirst k).val.time)
"""
    high = """example {θ ε s p first later terminal}
    (c : IsolatedHighContinuation θ s p first later terminal)
    (hb : PhysicalBox θ ε) (hs : IsolatedHighRest θ p s) {u}
    (run : Execution θ (fun _ _ => []) (isolatedHighSource s p first later) u)
    (hc : CompleteThrough run terminal)
"""
    terminal = """example {n θ bornCells K sigma centre delay T}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (i : Fin (n+1))
"""
    runtime_terminal = """example {n θ bornCells K sigma centre delay T ε u}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε)
    (run : Execution θ c.router (familyPreparationBornSource bornCells K) u)
    (hc : CompleteThrough run T) (i : Fin (n+1))
"""
    connected = """example {θ s delay first later terminal}
    (c : TwoCellHighContinuation θ s delay first later terminal)
"""
    return [
        pair("irregular settled prefixes retain exact actual response dates", prefix + """
    (i : Fin n) : run.emissionTimes i =
      (List.range k).map (fun j => schedule.time j + law.latency i@v@) := by
  exact (law.every_complete_prefix hb schedule initial hi hfirst k run hc).2.2 i
""", "", "+1"),
        pair("every complete prefix retains its reference recovery", prefix + """
    (i : Fin n) : u.x i .b = reference.x i .b@v@ := by
  exact ((law.every_complete_prefix hb schedule initial hi hfirst k run hc).2.1.2 i).1
""", "", "+1"),
        pair("every complete prefix retains every port memory", prefix + """
    (i : Fin n) (p : Port) : u.x i (.z p) = reference.x i (.z p)@v@ := by
  exact ((law.every_complete_prefix hb schedule initial hi hfirst k run hc).2.1.2 i).2 p
""", "", "+1"),
        pair("settled complete prefixes return to exact main rest", prefix + """
    (i : Fin n) : u.x i .q = @v@ := by
  exact (law.every_complete_prefix hb schedule initial hi hfirst k run hc).2.1.1.charge i
""", "1/10", "1/4"),
        pair("sensor residues are bounded rather than reset", prefix + """
    (i : Fin n) (p : Port) : |u.x i (.m p)-1/40| ≤ @v@ := by
  exact (law.every_complete_prefix hb schedule initial hi hfirst k run hc).2.1.1.sensor i p
""", "1/100000", "0"),
        pair("source prefixes have exactly one emission per served input", prefix + """
    (i : Fin n) : (run.emissionTimes i).length = @v@ := by
  rw [(law.every_complete_prefix hb schedule initial hi hfirst k run hc).2.2 i]
  simp
""", "k", "k+1"),
        pair("prefix comparison requires completion at the same actual horizon",
             prefix.replace("(law.readyStates schedule initial hi hfirst k).val.time)",
                            "((law.readyStates schedule initial hi hfirst k).val.time@v@))") + """
    : LearnedDomain θ active reference u := by
  exact (law.every_complete_prefix hb schedule initial hi hfirst k run hc).2.1
""", "", "+1"),
        pair("isolated high trains derive rather than prescribe their output dates", high + """
    : run.emissionTimes 0 = (first :: later).map
      (fun t => t + highRestLatency (Real.exp (s.x 0 (.z p)))@v@) := by
  exact (c.every_complete_execution hb hs run hc).2
""", "", "+1"),
        pair("high train universality preserves the same physical endpoint", high + """
    : u.x 0 .energy = c.final.x 0 .energy@v@ := by
  have h := (c.every_complete_execution hb hs run hc).1
  exact congrFun (congrFun h.values.symm 0) .energy
""", "", "+1"),
        pair("high train reuse retains all original port gains", high + """
    (q : Port) : u.x 0 (.z q) = s.x 0 (.z q)@v@ := by
  have h := (c.every_complete_execution hb hs run hc).1
  rw [←h.values]
  exact c.gains 0 q
""", "", "+1"),
        pair("every declared high input is consumed by an actual arrival", high + """
    : c.execution.deliveries = (@v@).map
      (fun t => (⟨0,p,t⟩ : Delivery 1)) := by
  exact c.deliveries
""", "first :: later", "later"),
        pair("the actual chain endpoint reaches the separate high recovery band", terminal + """
    : @v@ ≤ (c.final.autonomousView i).x 0 .b := by
  exact (c.terminal_high_rest i).recovery.1
""", "37999/100000", "1"),
        pair("terminal projection has no hidden pending traffic", terminal + """
    : (c.final.autonomousView i).pending = @v@ := by
  exact (c.terminal_high_rest i).pending
""", "[]", "[⟨0,0,T+1⟩]"),
        pair("every complete original chain endpoint reaches the reusable high section",
             runtime_terminal + """
    : (u.autonomousView i).x 0 .q = @v@ := by
  exact (c.terminal_high_rest_of_complete_execution hb run hc i).charge
""", "1/10", "1/4"),
        pair("high-section closure belongs to every complete continuation", high + """
    : @v@ ≤ u.x 0 .b := by
  exact (c.every_complete_high_rest hb hs run hc).recovery.1
""", "37999/100000", "1"),
        pair("the connected root calendar includes the actual fixed wire delay", connected + """
    : c.execution.emissionTimes 0 = (first::later).map
      (fun t => t + (highRestLatency (Real.exp (s.x 1 (.z 0))) @v@ +
        highRestLatency (Real.exp (s.x 0 (.z 2))))) := by
  simpa only [twoCellHighLatency,ite_true] using c.calendar 0
""", "+ delay", "- delay"),
        pair("the connected leaf responds without a fictitious extra hop", connected + """
    : c.execution.emissionTimes 1 = (first::later).map
      (fun t => t + highRestLatency (Real.exp (s.x 1 (.z 0)))@v@) := by
  simpa only [twoCellHighLatency,show (1 : Fin 2) ≠ 0 by decide,ite_false] using c.calendar 1
""", "", "+delay"),
        pair("connected reuse preserves each cell's own port memory", connected + """
    (i : Fin 2) (p : Port) : c.final.x i (.z p)=s.x i (.z p)@v@ := by
  exact c.gains i p
""", "", "+1"),
        pair("new external connected sources target the leaf only", """
example (s : Snapshot 2) (first : ℝ) (later : List ℝ) :
    (twoCellHighSource s first later).pending =
      (first::later).map (fun t => (⟨@v@,t⟩ : Delivery 2)) ++ s.pending := by
  rfl
""", "1,0", "0,2"),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix="generalized-continuations-", dir=ROOT) as tmp:
        path = Path(tmp) / "Check.lean"
        command = lean_check_command(tmp)

        def check(source, expected, label):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
            if (result.returncode == 0) != expected:
                raise SystemExit(f"{label}: unexpected result:\n{result.stdout}")
            if not expected and "error:" not in result.stdout:
                raise SystemExit(f"{label}: refusal lacked a Lean diagnostic:\n{result.stdout}")

        check(IRREGULAR_SCHEDULE + "\n".join(good for _, good, _ in controls),
              True, "irregular schedule and all positive controls")
        for label, _, bad in controls:
            check(bad, False, label)
            print(f"{label}: valid conclusion accepted; altered claim rejected.", flush=True)
    print(f"{len(controls)} paired generalized continuation controls passed.", flush=True)


if __name__ == "__main__":
    main()
