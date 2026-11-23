import InverterTarget
import MonotoneOneSidedRecognition
import TwoRails

/-! Inverters in front of the monotone cascade. The front end makes the rails of
the input pattern from the inverters' late pulses and the delayed direct pulses,
inside one read window. A per-pattern form of the one-sided recognition theorem
then gives the predicted answer, and `every_function_on_two_rails` makes it any
Boolean function. -/

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch settledCount)

/-- The front end puts the rails of the input pattern on the 2 M lines. -/
theorem front_end_input {M : Nat} {t : InverterTiming} {start : Rat}
    {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    {read : ReadObservation (M + M)} (front : FrontEnd t start external inv read) :
    read.input = rails (fun j => (external j).isSome) := by
  obtain ⟨cells, _, arrivals⟩ := front
  funext j
  simp only [ReadObservation.input, arrivals, frontArrival, rails]
  by_cases h : j.val < M
  · simp [h]
  · simp only [h, dite_false]
    obtain ⟨_, heard, law⟩ := cells ⟨j.val - M, by omega⟩
    obtain ⟨_, _, _, decision⟩ := law
    simp only [ReadObservation.fired, ReadObservation.input, heard] at decision
    cases e : (inv ⟨j.val - M, by omega⟩).emissions with
    | nil => simp_all
    | cons _ _ => simp_all

/-- With the direct rails delayed by `emitEarly`, every pulse of the front end
falls within one read window of width `max window (emitLate - emitEarly)`. -/
theorem front_end_window {M : Nat} {t : InverterTiming} {start skew : Rat}
    {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    {read : ReadObservation (M + M)} (front : FrontEnd t start external inv read)
    (windowFits : t.window ≤ skew) (spreadFits : t.emitLate - t.emitEarly ≤ skew) :
    ∀ j v, read.arrival j = some v → read.start ≤ v ∧ v ≤ read.start + skew := by
  obtain ⟨cells, readStart, arrivals⟩ := front
  intro j v arrived
  rw [arrivals] at arrived
  rw [readStart]
  simp only [frontArrival] at arrived
  by_cases h : j.val < M
  · simp only [h, dite_true] at arrived
    obtain ⟨u, heard, shifted⟩ := Option.map_eq_some_iff.mp arrived
    obtain ⟨cellStart, cellHeard, law⟩ := cells ⟨j.val, h⟩
    obtain ⟨_, window, _, _⟩ := law
    rw [cellHeard, cellStart] at window
    obtain ⟨lo, hi⟩ := window u heard
    subst shifted
    constructor <;> grind
  · simp only [h, dite_false] at arrived
    obtain ⟨cellStart, _, law⟩ := cells ⟨j.val - M, by omega⟩
    obtain ⟨_, _, emission, _⟩ := law
    rw [cellStart] at emission
    cases e : (inv ⟨j.val - M, by omega⟩).emissions with
    | nil => simp [e] at arrived
    | cons first rest =>
      rw [e] at arrived emission
      cases rest with
      | nil =>
        simp only [List.head?_cons, Option.some.injEq] at arrived
        subst arrived
        obtain ⟨lo, hi⟩ := emission
        constructor <;> grind
      | cons _ _ => exact emission.elim

/-- The front end and the remaining clauses give the calibrated read that the
cascade's first layer needs, at the rails of the input pattern. -/
theorem front_end_calibrated {M N : Nat} {p : Parameters N (M + M)} {a : Fin N} {writes budget : Nat}
    {t : InverterTiming} {timing : SlotTiming} {start : Rat} {y : Pattern M}
    {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    {read : ReadObservation (M + M)}
    (realised : ∀ j, (external j).isSome = y j)
    (front : FrontEnd t start external inv read)
    (rest : ReadAfterFront p a writes (rails y) budget timing read)
    (windowFits : t.window ≤ timing.skew) (spreadFits : t.emitLate - t.emitEarly ≤ timing.skew) :
    CalibratedAdditiveRead p a writes (rails y) budget timing read := by
  have input : read.input = rails y := by
    rw [front_end_input front]
    exact congrArg rails (funext realised)
  obtain ⟨valid, emission, decoder, residual⟩ := rest
  exact ⟨valid, input, front_end_window front windowFits spreadFits, emission, decoder, residual⟩

/- Copied from `MonotoneOneSidedRecognition.lean`, where it is private. -/
private theorem firing_mask_fires' {p : Disjunctions B A} (check : p.check = true)
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

/-- The one-sided recognition theorem at a single test pattern: the training
calibration and the test reads at `x` alone determine the decisions at `x`. -/
theorem one_sided_recognition_at {p : Cascade A B M} (valid : p.Valid)
    {firstTiming secondTiming : SlotTiming} {o : Observations A B M}
    {scores : Pattern M → Fin B → Pattern A → Int} {x : Pattern M}
    (training : CascadeTrainingCalibration p firstTiming secondTiming o)
    (firstReads : ∀ a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a) x
      (p.first.testingError a) firstTiming (o.firstTest x a))
    (secondReads : ∀ i, SecondTestRead p secondTiming o scores x i) :
    ∀ i, (o.secondTest x i).fired = output p i x := by
  have certificate := monotone_training valid training
  simp only [Cascade.Valid, Cascade.check, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨firstCheck, secondCheck⟩, _⟩, _⟩, _⟩ := valid
  intro i
  obtain ⟨route, read⟩ := secondReads i
  have input := second_test_input firstCheck certificate.1 firstReads route
  have sameCounts : lessonCounts p o (lessons p).length = expectedWrites p.second :=
    funext fun j => funext (certificate.2.2.2 j)
  simp only [] at read
  rw [sameCounts] at read
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
    exact firing_mask_fires' secondCheck i active read

/-- For ANY admissible cascade on 2 M lines: read through the inverter front end,
its decision at the input pattern `y` is its predicted answer on the rails of `y`.
This is the composition for a given cascade; the existence of a cascade for each
function comes from `every_function_on_two_rails`. -/
theorem inverters_compute {p : Cascade A B (M + M)} (valid : p.Valid)
    {t : InverterTiming} {firstTiming secondTiming : SlotTiming}
    {o : Observations A B (M + M)} {scores : Pattern (M + M) → Fin B → Pattern A → Int}
    (windowFits : t.window ≤ firstTiming.skew) (spreadFits : t.emitLate - t.emitEarly ≤ firstTiming.skew)
    (training : CascadeTrainingCalibration p firstTiming secondTiming o)
    {y : Pattern M} {start : Rat} {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    (realised : ∀ j, (external j).isSome = y j)
    (front : InverterFrontRead p t firstTiming o y start external inv)
    (second : ∀ k, SecondTestRead p secondTiming o scores (rails y) k) :
    ∀ i, (o.secondTest (rails y) i).fired = output p i (rails y) := by
  have firstReads : ∀ a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a)
      (rails y) (p.first.testingError a) firstTiming (o.firstTest (rails y) a) := fun a =>
    front_end_calibrated realised (front a).1 (front a).2 windowFits spreadFits
  exact one_sided_recognition_at valid training firstReads second

/-- Inverters in front of an admissible cascade compute every Boolean function. -/
theorem every_function_with_inverters : EveryFunctionWithInverters := by
  intro M f
  obtain ⟨A, B, p, i, valid, same⟩ := every_function_on_two_rails M f
  refine ⟨A, B, p, i, valid, ?_⟩
  intro t firstTiming secondTiming o scores windowFits spreadFits training y start external inv
    realised front second
  rw [inverters_compute valid windowFits spreadFits training realised front second i, same y]

end LearnedCoincidence.MonotoneDNF
