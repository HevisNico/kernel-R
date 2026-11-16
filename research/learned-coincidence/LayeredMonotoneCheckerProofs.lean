import LayeredMonotoneCheckerTargets
import MonotonePremiseSoundness
import MonotonePremiseCompleteness

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (patterns checkThresholdRead)

private theorem all_ports {f : Fin N → Bool} :
    (List.finRange N).all f = true ↔ ∀ i, f i = true := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies]

private theorem all_range {f : Nat → Bool} {n : Nat} :
    (List.range n).all f = true ↔ ∀ k, k < n → f k = true := by
  simp only [List.all_eq_true, List.mem_range]

private theorem all_patterns {f : Pattern M → Bool} :
    (patterns M).all f = true ↔ ∀ x, f x = true :=
  ⟨fun h x => List.all_eq_true.mp h x (MonotoneDNF.patterns_complete x),
    fun h => List.all_eq_true.mpr fun x _ => h x⟩

private theorem all_filter {xs : List α} {f g : α → Bool} :
    (xs.filter f).all g = true ↔ ∀ x ∈ xs, f x = true → g x = true := by
  simp only [List.all_eq_true, List.mem_filter, and_imp]

private theorem all_filtered_patterns {f g : Pattern M → Bool} :
    ((patterns M).filter f).all g = true ↔ ∀ x, f x = true → g x = true :=
  all_filter.trans ⟨fun h x => h x (MonotoneDNF.patterns_complete x), fun h x _ => h x⟩

private theorem all_groups {p : Cell} {f : Fin 2 → Bool} :
    (Checker.activeGroups p).all f = true ↔ ∀ g, g.val < p.gate.groups → f g = true := by
  simp only [Checker.activeGroups, all_filter, List.mem_finRange, true_implies, decide_eq_true_eq]

private theorem timing_iff {t : SlotTiming} : Checker.timing t = true ↔ t.Valid := by
  simp only [Checker.timing, decide_eq_true_eq, SlotTiming.Valid]

private theorem mask_eq_iff {x y : Pattern M} : Checker.maskEq x y = true ↔ x = y := by
  simp only [Checker.maskEq, all_ports, beq_iff_eq]
  exact ⟨funext, fun h a => congrFun h a⟩

private theorem cell_valid_iff (p : Cell) : Checker.cellValid p = true ↔ p.Valid := by
  simp only [Checker.cellValid, Cell.Valid, Bool.and_eq_true, and_assoc, all_groups, all_range,
    all_ports, all_filtered_patterns, Bool.not_eq_true', decide_eq_true_eq]
  simp only [List.all_eq_true, decide_eq_true_eq]

private theorem node_valid_iff (d : Node M N) (predict : Pattern M → Pattern N) :
    Checker.nodeValid d predict = true ↔ d.Valid predict := by
  simp only [Checker.nodeValid, Node.Valid, Bool.and_eq_true, and_assoc, cell_valid_iff,
    all_ports, all_groups, mask_eq_iff, decide_eq_true_eq]

private theorem batch_before_iff (a b : List Window) :
    Checker.batchBefore a b = true ↔ BatchBefore a b := by
  simp only [Checker.batchBefore, BatchBefore, List.all_eq_true, decide_eq_true_eq]

private theorem ordered_batches_iff (batches : List (List Window)) :
    Checker.orderedBatches batches = true ↔ batches.Pairwise BatchBefore := by
  induction batches with
  | nil => simp [Checker.orderedBatches]
  | cons batch rest ih =>
    simp only [Checker.orderedBatches, Bool.and_eq_true, List.all_eq_true, batch_before_iff,
      ih, List.pairwise_cons]

private theorem valid_iff (c : Cascade M L N) : checkLayeredValid c = true ↔ c.Valid := by
  induction c with
  | input => simp [checkLayeredValid, Cascade.Valid]
  | layer lower t nodes ih =>
    simp only [checkLayeredValid, Cascade.Valid, Bool.and_eq_true, and_assoc, ih, timing_iff,
      all_ports, node_valid_iff]

private theorem separation_iff (c : Cascade M L N) (train : TrainingTrace c)
    (test : Pattern M → ReadTrace c) :
    checkLayeredSeparation c train test = true ↔ TrainingSeparation c train test := by
  simp only [checkLayeredSeparation, TrainingSeparation, Bool.and_eq_true, ordered_batches_iff,
    Checker.externalSeparation, all_patterns]
  simp only [List.all_eq_true, batch_before_iff]

private theorem routed_iff {d : Node M N} {incoming : Fin N → Option Rat} {r : ReadObservation 2} :
    Checker.routed d incoming r = true ↔ Routed d incoming r := by
  simp only [Checker.routed, Routed, all_ports, decide_eq_true_eq]

private theorem threshold_iff {level : Nat} {t : SlotTiming} {r : ReadObservation 2} :
    checkThresholdRead level t r = true ↔ MonotoneDNF.ThresholdRead level t r :=
  ⟨MonotoneDNF.threshold_read_sound, MonotoneDNF.check_threshold_read_complete⟩

private theorem additive_iff {p : Cell} {w : Writes} {budget : Nat} {t : SlotTiming}
    {r : ReadObservation 2} :
    Checker.additiveSlot p w budget t r = true ↔ AdditiveSlot p w budget t r := by
  simp only [Checker.additiveSlot, AdditiveSlot, admissible, Bool.and_eq_true, threshold_iff,
    decide_eq_true_eq]

private theorem firing_iff {p : Cell} {w : Writes} {t : SlotTiming} {r : ReadObservation 2}
    {scoreAt : Pattern 2 → Int} :
    Checker.firingSlot p w t r scoreAt = true ↔ FiringSlot p w t r scoreAt := by
  simp only [Checker.firingSlot, FiringSlot, Bool.and_eq_true, and_assoc, threshold_iff,
    all_filtered_patterns, and_imp, decide_eq_true_eq]
  simp only [all_filter, decide_eq_true_eq]

private theorem slot_iff (p : Cell) (w : Writes) (t : SlotTiming) (r : ReadObservation 2)
    (scores : Pattern 2 → Int) :
    (if p.gate.eval r.input then Checker.firingSlot p w t r scores
      else Checker.additiveSlot p w p.testError t r) = true ↔
    (if p.gate.eval r.input then FiringSlot p w t r scores
      else AdditiveSlot p w p.testError t r) := by
  cases p.gate.eval r.input <;> simp [additive_iff, firing_iff]

private theorem one_read_iff (c : Cascade M L N) (train : TrainingTrace c)
    (x : Pattern M) (r : ReadTrace c) :
    Checker.oneRead c train x r = true ↔ ReadCalibration c train x r := by
  induction c with
  | input => exact mask_eq_iff
  | layer lower t nodes ih =>
    simp only [Checker.oneRead, ReadCalibration, Bool.and_eq_true, ih, all_ports, routed_iff, slot_iff]

private theorem training_iff (c : Cascade M L N) (train : TrainingTrace c) :
    checkLayeredTrainingCalibration c train = true ↔ TrainingCalibration c train := by
  induction c with
  | input => simp [checkLayeredTrainingCalibration, TrainingCalibration]
  | layer lower t nodes ih =>
    simp only [checkLayeredTrainingCalibration, TrainingCalibration, Bool.and_eq_true, and_assoc,
      ih, all_ports, all_groups, all_range, one_read_iff, routed_iff, additive_iff]
    simp only [Nat.lt_succ_iff]

private theorem readings_iff (c : Cascade M L N) (train : TrainingTrace c)
    (test : Pattern M → ReadTrace c) :
    checkLayeredReadCalibration c train test = true ↔ ∀ x, ReadCalibration c train x (test x) := by
  simp only [checkLayeredReadCalibration, all_patterns, one_read_iff]

theorem layered_valid_checker_sound : LayeredValidCheckerSound :=
  fun _ _ _ c => (valid_iff c).mp

theorem layered_valid_checker_complete : LayeredValidCheckerComplete :=
  fun _ _ _ c => (valid_iff c).mpr

theorem layered_separation_checker_sound : LayeredSeparationCheckerSound :=
  fun _ _ _ c train test => (separation_iff c train test).mp

theorem layered_separation_checker_complete : LayeredSeparationCheckerComplete :=
  fun _ _ _ c train test => (separation_iff c train test).mpr

theorem layered_training_calibration_checker_sound : LayeredTrainingCalibrationCheckerSound :=
  fun _ _ _ c train => (training_iff c train).mp

theorem layered_training_calibration_checker_complete : LayeredTrainingCalibrationCheckerComplete :=
  fun _ _ _ c train => (training_iff c train).mpr

theorem layered_read_calibration_checker_sound : LayeredReadCalibrationCheckerSound :=
  fun _ _ _ c train test => (readings_iff c train test).mp

theorem layered_read_calibration_checker_complete : LayeredReadCalibrationCheckerComplete :=
  fun _ _ _ c train test => (readings_iff c train test).mpr

end LearnedCoincidence.Layered
