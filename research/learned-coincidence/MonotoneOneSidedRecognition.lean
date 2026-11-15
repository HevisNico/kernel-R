import MonotoneOneSidedTarget
import MonotoneRecognition

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (ReadObservation SlotTiming)

private theorem firing_mask_fires {p : Disjunctions B A} (check : p.check = true)
    (i : Fin B) {timing : SlotTiming} {r : ReadObservation A} {scoreAt : Pattern A → Int}
    (active : (p.alwaysFire i ||
      (List.finRange A).any (fun a => p.lines i a && r.input a)) = true)
    (read : FiringMaskRead p (expectedWrites p) i timing r scoreAt) :
    r.fired = true := by
  obtain ⟨decoder, measured, monotone, anchor⟩ := read
  have reaches : ∃ y, contains r.input y = true ∧ (p.threshold i : Int) ≤ scoreAt y := by
    cases mode : p.alwaysFire i with
    | true =>
      rw [ite_eq_left mode] at anchor
      refine ⟨fun _ => false, contains_iff.mpr (by simp), ?_⟩
      have margin := constant_margin check i mode
      omega
    | false =>
      rw [ite_eq_right (by simp [mode])] at anchor
      simp only [mode, Bool.false_or] at active
      obtain ⟨a, _, on⟩ := List.any_eq_true.mp active
      obtain ⟨selected, arrived⟩ := Bool.and_eq_true_iff.mp on
      have lower := anchor a selected arrived
      rw [show expectedWrites p i a = lineNeed p i a by simp [expectedWrites, selected]] at lower
      have margin := (line_certificate check i a selected).2.2.2
      refine ⟨singleton a, contains_iff.mpr ?_, by omega⟩
      intro b on
      obtain rfl : b = a := of_decide_eq_true on
      exact arrived
  obtain ⟨y, submask, fires⟩ := reaches
  rw [decoder.2.2.2, ← measured]
  exact decide_eq_true (Int.le_trans fires (monotone y submask fires))

/-- At test, a firing reference suffices for every mask that contains it. -/
theorem two_layer_monotone_recognition_one_sided : TwoLayerMonotoneRecognitionOneSided := by
  intro A B M p valid left right o scores _separation calibration
  have training := monotone_training valid calibration.1
  refine ⟨training, ?_⟩
  simp only [Cascade.Valid, Cascade.check, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨firstCheck, secondCheck⟩, _⟩, _⟩, _⟩ := valid
  intro x i
  obtain ⟨route, read⟩ := calibration.2.2 x i
  have input := second_test_input firstCheck training.1 (calibration.2.1 x) route
  have sameCounts : lessonCounts p o (lessons p).length = expectedWrites p.second :=
    funext fun j => funext (training.2.2.2 j)
  rw [sameCounts] at read
  change (if p.second.alwaysFire i ||
      (List.finRange A).any (fun a => p.second.lines i a && (o.secondTest x i).input a) then
    _ else _) at read
  have observedOutput :
      (p.second.alwaysFire i ||
        (List.finRange A).any (fun a => p.second.lines i a && (o.secondTest x i).input a)) =
        output p i x :=
    congrArg (fun mask : Pattern A =>
      p.second.alwaysFire i || (List.finRange A).any (fun a => p.second.lines i a && mask a)) input
  rw [← observedOutput]
  cases active : (p.second.alwaysFire i ||
      (List.finRange A).any (fun a => p.second.lines i a && (o.secondTest x i).input a)) with
  | false =>
    rw [ite_eq_right (by simp [active])] at read
    have margin := second_margin p.second secondCheck i (o.secondTest x i).input
    rw [active] at margin
    exact read_of_margin read margin
  | true =>
    rw [ite_eq_left active] at read
    exact firing_mask_fires secondCheck i active read

end LearnedCoincidence.MonotoneDNF
