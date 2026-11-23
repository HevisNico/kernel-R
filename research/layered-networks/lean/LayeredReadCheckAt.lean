import LayeredMonotoneCheckerProofs

/-! The read-calibration checker at ONE external pattern, with a public soundness proof.

`checkLayeredReadCalibration` checks every line pattern; behind inverters only the rails of the input patterns
occur, so a measured test trace exists only there. `Checker.oneRead` checks one pattern; its soundness lemma in
`LayeredMonotoneCheckerProofs.lean` (`one_read_iff`) is private. This file proves it again, publicly, with the same
steps. No existing file is changed. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (patterns checkThresholdRead)

private theorem at_all_ports {f : Fin N → Bool} :
    (List.finRange N).all f = true ↔ ∀ i, f i = true := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies]

private theorem at_all_filter {xs : List α} {f g : α → Bool} :
    (xs.filter f).all g = true ↔ ∀ x ∈ xs, f x = true → g x = true := by
  simp only [List.all_eq_true, List.mem_filter, and_imp]

private theorem at_all_filtered_patterns {f g : Pattern M → Bool} :
    ((patterns M).filter f).all g = true ↔ ∀ x, f x = true → g x = true :=
  at_all_filter.trans ⟨fun h x => h x (MonotoneDNF.patterns_complete x), fun h x _ => h x⟩

private theorem at_mask_eq_iff {x y : Pattern M} : Checker.maskEq x y = true ↔ x = y := by
  simp only [Checker.maskEq, at_all_ports, beq_iff_eq]
  exact ⟨funext, fun h a => congrFun h a⟩

private theorem at_routed_iff {d : Node M N} {incoming : Fin N → Option Rat} {r : ReadObservation 2} :
    Checker.routed d incoming r = true ↔ Routed d incoming r := by
  simp only [Checker.routed, Routed, at_all_ports, decide_eq_true_eq]

private theorem at_threshold_iff {level : Nat} {t : SlotTiming} {r : ReadObservation 2} :
    checkThresholdRead level t r = true ↔ MonotoneDNF.ThresholdRead level t r :=
  ⟨MonotoneDNF.threshold_read_sound, MonotoneDNF.check_threshold_read_complete⟩

private theorem at_additive_iff {p : Cell} {w : Writes} {budget : Nat} {t : SlotTiming}
    {r : ReadObservation 2} :
    Checker.additiveSlot p w budget t r = true ↔ AdditiveSlot p w budget t r := by
  simp only [Checker.additiveSlot, AdditiveSlot, admissible, Bool.and_eq_true, at_threshold_iff,
    decide_eq_true_eq]

private theorem at_firing_iff {p : Cell} {w : Writes} {t : SlotTiming} {r : ReadObservation 2}
    {scoreAt : Pattern 2 → Int} :
    Checker.firingSlot p w t r scoreAt = true ↔ FiringSlot p w t r scoreAt := by
  simp only [Checker.firingSlot, FiringSlot, Bool.and_eq_true, and_assoc, at_threshold_iff,
    at_all_filtered_patterns, and_imp, decide_eq_true_eq]
  simp only [at_all_filter, decide_eq_true_eq]

private theorem at_slot_iff (p : Cell) (w : Writes) (t : SlotTiming) (r : ReadObservation 2)
    (scores : Pattern 2 → Int) :
    (if p.gate.eval r.input then Checker.firingSlot p w t r scores
      else Checker.additiveSlot p w p.testError t r) = true ↔
    (if p.gate.eval r.input then FiringSlot p w t r scores
      else AdditiveSlot p w p.testError t r) := by
  cases p.gate.eval r.input <;> simp [at_additive_iff, at_firing_iff]

/-- `Checker.oneRead` decides `ReadCalibration` at one external pattern. -/
theorem one_read_checker_iff (c : Cascade M L N) (train : TrainingTrace c) (x : Pattern M) (r : ReadTrace c) :
    Checker.oneRead c train x r = true ↔ ReadCalibration c train x r := by
  induction c with
  | input => exact at_mask_eq_iff
  | layer lower t nodes ih =>
    simp only [Checker.oneRead, ReadCalibration, Bool.and_eq_true, ih, at_all_ports, at_routed_iff, at_slot_iff]

theorem one_read_checker_sound {c : Cascade M L N} {train : TrainingTrace c} {x : Pattern M} {r : ReadTrace c}
    (h : Checker.oneRead c train x r = true) : ReadCalibration c train x r :=
  (one_read_checker_iff c train x r).mp h

end LearnedCoincidence.Layered
