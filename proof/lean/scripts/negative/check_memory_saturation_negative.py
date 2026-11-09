#!/usr/bin/env python3
"""Paired controls for actual capped ERROR transfers and section counts.

These checks protect the declared interfaces; rejection is not itself a
counterexample proof. Every altered statement is paired with a valid one.
Infrastructure failures cannot satisfy an expected semantic rejection.
"""
from pathlib import Path
import os
import signal
import subprocess
import tempfile
from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
MODULE = "KernelR.HybridCrossingMemorySaturation"
PREFIX = f"import {MODULE}\nopen KernelR.Hybrid\n"

TRANSFER = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (available : {exposure})
    (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = min (Real.log ((θ i).cap p))
      (s.x i (.z p) + ({factor} : ℝ) * (s.x i (.m p) - u.x i (.m p))) := by
  exact e.error_capped_transfer hb i p available initial
"""
COUNT = """example {{n θ ε route s u i p}} (e : @Execution n θ route s u)
    (cover : CappedErrorSectionCover i p e)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = {rhs} := by
  exact cover.gain_eq hb initial
"""
CEILING = """example {{n θ ε route s u i p}} (e : @Execution n θ route s u)
    (cover : CappedErrorSectionCover i p e)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) ↔
      gainSaturationCount θ s i p {offset} ≤ cover.count := by
  exact cover.saturated_iff_count hb initial
"""
PERMANENCE = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (initial : s.x i (.z p) {relation} Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) := by
  exact e.gain_stays_at_cap hb i p initial
"""
COMPATIBILITY = """example {{n θ route s u i p}} (e : @Execution n θ route s u)
    (cover : ErrorSectionCover i p e) :
    cover.toCapped.count = cover.count {offset} := by
  exact cover.toCapped_count
"""
CLIPPING = """example : min (1 : ℝ) (9/10 + 3/5) = {value} := by norm_num
"""
WEAK = """example {{n θ ε route s u}} (e : @WeakExecution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (available : e.ErrorAvailable i p)
    (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = min (Real.log ((θ i).cap p))
      (s.x i (.z p) + ({factor} : ℝ) * (s.x i (.m p) - u.x i (.m p))) := by
  exact e.error_capped_transfer hb i p available initial
"""
CROSSING = """example {{n θ ε route s u}} (run : @CrossingExecution n θ route s u)
    (i : Fin n) (p : Port)
    (cover : WeakCappedErrorSectionCover i p run.execution)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) ↔
      gainSaturationCount θ s i p {offset} ≤ cover.count := by
  exact run.memory_saturated_iff_count i p cover hb initial
"""
CROSSING_CAP = """example {{n θ ε route s u}} (run : @CrossingExecution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (initial : s.x i (.z p) {relation} Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) := by
  exact run.gain_stays_at_cap hb i p initial
"""
WITNESS = """example {{n}} (θ : Fin n → Parameters) (route : Router n)
    {{T : ℝ}} (hT : 0 < T) :
    ∃ run : CrossingExecution θ route (saturatedResting θ 0) (saturatedResting θ T),
      PhysicalInvariant θ (saturatedResting θ 0) ∧ CrossingCompleteThrough run T ∧
        ∀ i p, (saturatedResting θ T).x i (.z p) = Real.log ((θ i).cap p) {offset} := by
  exact saturated_resting_crossing_complete_exists θ route hT
"""
def main():
    capped="min (Real.log ((θ i).cap p)) (s.x i (.z p) + (3/5 : ℝ) * cover.count)"
    uncapped="s.x i (.z p) + (3/5 : ℝ) * cover.count"
    wrongfactor="min (Real.log ((θ i).cap p)) (s.x i (.z p) + (2/5 : ℝ) * cover.count)"
    cases=[
        ("clipped transfer retains the factor eight",
         TRANSFER.format(exposure="e.ErrorAvailable i p",factor="8"),
         TRANSFER.format(exposure="e.ErrorAvailable i p",factor="7")),
        ("mechanical exposure cannot be replaced by the ERROR mode alone",
         TRANSFER.format(exposure="e.ErrorAvailable i p",factor="8"),
         TRANSFER.format(exposure="e.AuxFlows i p .error",factor="8")),
        ("whole-trace count retains the three-fifths dose",
         COUNT.format(rhs=capped),COUNT.format(rhs=wrongfactor)),
        ("the automatic cap cannot be dropped from the counted result",
         COUNT.format(rhs=capped),COUNT.format(rhs=uncapped)),
        ("the ceiling threshold is not shifted by one",
         CEILING.format(offset=""),CEILING.format(offset="+ 1")),
        ("cap permanence requires initial cap attainment",
         PERMANENCE.format(relation="="),PERMANENCE.format(relation="≤")),
        ("old exposed covers retain their actual counts",
         COMPATIBILITY.format(offset=""),COMPATIBILITY.format(offset="+ 1")),
        ("last-section clipping does not overshoot the cap",
         CLIPPING.format(value="1"),CLIPPING.format(value="3/2")),
        ("weak-flow transfer retains the same physical dose",
         WEAK.format(factor="8"),WEAK.format(factor="7")),
        ("upward-crossing section count has the same ceiling",
         CROSSING.format(offset=""),CROSSING.format(offset="+ 1")),
        ("upward-crossing permanence requires attained cap",
         CROSSING_CAP.format(relation="="),CROSSING_CAP.format(relation="≤")),
        ("positive-duration saturated witness has no invented gain increase",
         WITNESS.format(offset=""),WITNESS.format(offset="+ 1")),
    ]
    infrastructure=("unknown identifier","unknown constant","unknown module prefix",
                    "unexpected token","invalid import","object file","failed to open",
                    "file not found","does not exist")
    with tempfile.TemporaryDirectory(prefix="memory-saturation-controls-",dir=ROOT) as tmp:
        path=Path(tmp)/"Check.lean"
        command=lean_check_command(tmp,root_module=MODULE)
        for name,good,bad in cases:
            for expected,source in [(True,good),(False,bad)]:
                path.write_text(PREFIX+source)
                with subprocess.Popen([*command,str(path)],cwd=ROOT,text=True,
                    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                    start_new_session=True) as process:
                    try:
                        output,_=process.communicate(timeout=120)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid,signal.SIGKILL)
                        output,_=process.communicate()
                        raise SystemExit(f"{name}: control timed out; no semantic result accepted.\n{output}")
                    code=process.returncode
                if (code==0)!=expected:
                    raise SystemExit(f"{name}: unexpected result:\n{output}")
                if not expected:
                    low=output.lower()
                    if "error:" not in low or any(x in low for x in infrastructure):
                        raise SystemExit(f"{name}: not a valid semantic rejection:\n{output}")
            print(f"{name}: valid statement accepted; altered statement rejected.",flush=True)
    print(f"All {len(cases)} paired memory-saturation controls passed.",flush=True)
if __name__=="__main__":
    main()
