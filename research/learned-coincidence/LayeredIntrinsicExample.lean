import LayeredIntrinsic
import LayeredChainExamples

/-! The intrinsic-delay chain on the repository's three-layer example. Every read
emits exactly one unit after the later of its start and its arrivals, so
`dmin = dmax = 1`. Each skew is 0, so `λmax = skew + dmax = 1`. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)

/-- A sound checker: the reference date is searched among the read start and the arrivals. -/
def checkIntrinsicDelay (dmin dmax : Rat) (r : ReadObservation 2) : Bool :=
  r.emissions.all fun t =>
    (r.start :: (List.finRange 2).filterMap r.arrival).any fun ref =>
      decide (r.start ≤ ref) &&
      (List.finRange 2).all (fun j => match r.arrival j with
        | none => true
        | some v => decide (v ≤ ref)) &&
      decide (ref + dmin ≤ t ∧ t ≤ ref + dmax)

def checkIntrinsicDelays (dmin dmax : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Bool
  | .input, _ => true
  | .layer (L := L) lower _ _, r =>
    checkIntrinsicDelays dmin dmax lower r.1 &&
      (List.finRange N).all fun i => checkIntrinsicDelay (dmin (L + 1)) (dmax (L + 1)) (r.2.1 i)

private theorem all_fin {n : Nat} {P : Fin n → Bool} :
    (List.finRange n).all P = true ↔ ∀ i, P i = true := by
  simp [List.all_eq_true]

theorem intrinsic_delay_checker_sound {dmin dmax : Rat} {r : ReadObservation 2}
    (h : checkIntrinsicDelay dmin dmax r = true) : IntrinsicDelay dmin dmax r := by
  intro t mem
  obtain ⟨ref, candidate, ok⟩ := List.any_eq_true.mp (List.all_eq_true.mp h t mem)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨after, arrivals⟩, lo, hi⟩ := ok
  refine ⟨ref, ?_, after, fun j v arrived => ?_, lo, hi⟩
  · rcases List.mem_cons.mp candidate with same | other
    · exact Or.inl same
    · obtain ⟨j, _, arrived⟩ := List.mem_filterMap.mp other
      exact Or.inr ⟨j, arrived⟩
  · have port := all_fin.mp arrivals j
    rw [arrived] at port
    exact of_decide_eq_true port

theorem intrinsic_delays_checker_sound {dmin dmax : Nat → Rat} {c : Cascade M L N} {r : ReadTrace c}
    (h : checkIntrinsicDelays dmin dmax c r = true) : IntrinsicDelays dmin dmax c r := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    simp only [checkIntrinsicDelays, Bool.and_eq_true] at h
    exact ⟨ih h.1, fun i => intrinsic_delay_checker_sound (all_fin.mp h.2 i)⟩

namespace ChainExample

open MonotoneDNF.PremiseCheck (patterns)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem intrinsic_accepted :
    checkChainDates start (latencyLow fun _ => 1)
      (latencyHigh 0 fun ℓ => layerSkew Example.circuit ℓ + 1) Example.circuit = true := by
  decide +kernel

private theorem intrinsic_traces :
    ((patterns 4).all fun x => checkIntrinsicDelays (fun _ => 1) (fun _ => 1) Example.circuit
      (Example.test x)) = true := by decide +kernel

private theorem every (x : Pattern 4) {P : Pattern 4 → Bool} (h : (patterns 4).all P = true) :
    P x = true := List.all_eq_true.mp h x (MonotoneDNF.patterns_complete x)

/-- The example from intrinsic delays: the windows and the decisions, with no latency assumed. -/
theorem example_from_intrinsic (x : Pattern 4) :
    ArrivalWindows Example.circuit (Example.test x) ∧
    observed Example.circuit (Example.test x) = Example.circuit.predict x := by
  have valid := layered_valid_checker_sound 4 3 1 _ (by decide +kernel : checkLayeredValid Example.circuit = true)
  have training := layered_training_calibration_checker_sound 4 3 1 _ _
    (by decide +kernel : checkLayeredTrainingCalibration Example.circuit Example.train = true)
  have reads := (read_calibration_iff Example.circuit Example.train x (Example.test x)).mp
    (layered_read_calibration_checker_sound 4 3 1 _ _ _
      (by decide +kernel : checkLayeredReadCalibration Example.circuit Example.train Example.test = true) x)
  have scheduled : checkScheduled start Example.circuit (Example.test x) = true :=
    every x (by decide +kernel : ((patterns 4).all fun x => checkScheduled start Example.circuit (Example.test x)) = true)
  have external : checkExternalWindow (start 0) 0 Example.circuit (Example.test x) = true :=
    every x (by decide +kernel : ((patterns 4).all fun x =>
      checkExternalWindow (start 0) 0 Example.circuit (Example.test x)) = true)
  exact layered_recognition_from_intrinsic valid training
    (chain_dates_checker_sound 4 3 1 _ _ _ _ intrinsic_accepted) reads.1 reads.2.1
    (scheduled_checker_sound scheduled) (external_window_checker_sound external)
    (intrinsic_delays_checker_sound (every x intrinsic_traces))

end ChainExample

end LearnedCoincidence.Layered
