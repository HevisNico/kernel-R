import KernelR.Cadence
import KernelR.Protocol

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.CadenceRecorded.Cadence010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open KernelR.Cadence

def bTeaching : List RecordedStep := [
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩]

theorem bTeaching_counters : checkSteps 3 0 bTeaching = true := by decide
theorem bTeaching_counts : bTeaching.length = 16 ∧ emissions bTeaching = 16 ∧
    errors bTeaching = 0 ∧ marks bTeaching = 0 := by decide

def cTeaching : List RecordedStep := [
  ⟨.weakError, 1, 0⟩,
  ⟨.fire, 1, 0⟩,
  ⟨.markOnly, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩,
  ⟨.fire, 1, 1⟩]

theorem cTeaching_counters : checkSteps 0 0 cTeaching = true := by decide
theorem cTeaching_counts : cTeaching.length = 16 ∧ emissions cTeaching = 14 ∧
    errors cTeaching = 1 ∧ marks cTeaching = 1 := by decide

def cFast : List RecordedStep := [
  ⟨.weakError, 1, 0⟩,
  ⟨.weakError, 2, 0⟩,
  ⟨.weakError, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.markOnly, 3, 1⟩,
  ⟨.fire, 3, 1⟩,
  ⟨.markThenError, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩]

theorem cFast_counters : checkSteps 0 0 cFast = true := by decide
theorem cFast_counts : cFast.length = 25 ∧ emissions cFast = 20 ∧
    errors cFast = 4 ∧ marks cFast = 2 := by decide

def bFast : List RecordedStep := [
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.markOnly, 3, 1⟩,
  ⟨.fire, 3, 1⟩,
  ⟨.markThenError, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩]

theorem bFast_counters : checkSteps 3 0 bFast = true := by decide
theorem bFast_counts : bFast.length = 20 ∧ emissions bFast = 18 ∧
    errors bFast = 1 ∧ marks bFast = 2 := by decide

def aFast : List RecordedStep := [
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.fire, 3, 0⟩,
  ⟨.markOnly, 3, 1⟩,
  ⟨.fire, 3, 1⟩,
  ⟨.markThenError, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩,
  ⟨.fire, 4, 2⟩]

theorem aFast_counters : checkSteps 3 0 aFast = true := by decide
theorem aFast_counts : aFast.length = 18 ∧ emissions aFast = 16 ∧
    errors aFast = 1 ∧ marks aFast = 2 := by decide

theorem routed_input_counts : bFast.length = emissions cFast ∧
    aFast.length = emissions bFast ∧ cTeaching.length = emissions bTeaching := by decide
theorem all_input_cases : bTeaching.length + cTeaching.length + cFast.length +
    bFast.length + aFast.length = 95 := by decide
theorem total_emissions_through_789_9 :
    KernelR.fireCount (KernelR.aWarmup ++ KernelR.aTeaching ++ KernelR.feedbackWord 13) +
      emissions aFast = 54 ∧
    KernelR.fireCount (KernelR.bWarmup ++ KernelR.feedbackWord 16) +
      emissions bTeaching + emissions bFast = 61 ∧
    emissions cTeaching + emissions cFast = 34 := by decide

end KernelR.CadenceRecorded.Cadence010
