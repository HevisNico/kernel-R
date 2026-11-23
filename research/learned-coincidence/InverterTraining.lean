import Inverters
import TwoRailsExplicit

/-! Training through the inverters. The cascade's training and teaching reads of
the first layer are produced by the same front end as its test reads, so that the
network only ever sees `M` input lines. The inverters are fixed and untrained;
only the cascade learns. -/

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch observedCount
  settledCount)

/-- The training calibration of the cascade, with every first-layer read of
training and teaching produced by the front end at the rails of some input
pattern equal to the read's target. The second-layer reads are as before. -/
def InverterTrainingCalibration (p : Cascade A B (M + M)) (t : InverterTiming)
    (firstTiming secondTiming : SlotTiming) (o : Observations A B (M + M)) : Prop :=
  (∀ r, r ≤ p.first.maxWrites → ∀ a,
    (∃ start external inv, FrontEnd t start external inv (o.firstTrain r a) ∧
      rails (fun j => (external j).isSome) = p.first.target a) ∧
    ReadAfterFront p.first a (observedCount o.firstTrain a r) (p.first.target a)
      (p.first.trainingError a) firstTiming (o.firstTrain r a)) ∧
  (∀ n L, (lessons p)[n]? = some L →
    (∀ a, (∃ start external inv, FrontEnd t start external inv (o.teach n a) ∧
        rails (fun j => (external j).isSome) = p.first.target L.line) ∧
      ReadAfterFront p.first a (settledCount p.first o.firstTrain a) (p.first.target L.line)
        (p.first.testingError a) firstTiming (o.teach n a)) ∧
    RoutedBatch (p.delay L.cell) (o.teach n) (o.secondTrain n) ∧
    CalibratedAdditiveRead (readView p.second (lessonCounts p o n)) L.cell 0 (o.secondTrain n).input
      (p.second.trainingError L.cell) secondTiming (o.secondTrain n))

/-- A front-end read whose rails are a target gives the calibrated read at that target. -/
theorem front_end_at_target {N : Nat} {p : Parameters N (M + M)} {a : Fin N} {writes budget : Nat}
    {t : InverterTiming} {timing : SlotTiming} {target : Pattern (M + M)}
    {read : ReadObservation (M + M)}
    (front : ∃ start external inv, FrontEnd t start external inv read ∧
      rails (fun j => (external j).isSome) = target)
    (rest : ReadAfterFront p a writes target budget timing read)
    (windowFits : t.window ≤ timing.skew) (spreadFits : t.emitLate - t.emitEarly ≤ timing.skew) :
    CalibratedAdditiveRead p a writes target budget timing read := by
  obtain ⟨start, external, inv, produced, atTarget⟩ := front
  rw [← atTarget] at rest ⊢
  exact front_end_calibrated (fun _ => rfl) produced rest windowFits spreadFits

/-- (b) Training through the front end supplies the training calibration of the cascade. -/
theorem training_through_front_end {p : Cascade A B (M + M)} {t : InverterTiming}
    {firstTiming secondTiming : SlotTiming} {o : Observations A B (M + M)}
    (windowFits : t.window ≤ firstTiming.skew) (spreadFits : t.emitLate - t.emitEarly ≤ firstTiming.skew)
    (training : InverterTrainingCalibration p t firstTiming secondTiming o) :
    CascadeTrainingCalibration p firstTiming secondTiming o := by
  refine ⟨fun r bound a => ?_, fun n L atIndex => ?_⟩
  · obtain ⟨front, rest⟩ := training.1 r bound a
    exact front_end_at_target front rest windowFits spreadFits
  · obtain ⟨teaching, route, second⟩ := training.2 n L atIndex
    refine ⟨fun a => ?_, route, second⟩
    obtain ⟨front, rest⟩ := teaching a
    exact front_end_at_target front rest windowFits spreadFits

/-- An inverter slot: its dates and its whole duration, reset included. -/
structure InverterSlot where
  timing : InverterTiming
  duration : Rat

def InverterSlot.Valid (s : InverterSlot) : Prop :=
  s.timing.Valid ∧ s.timing.emitLate < s.duration

/-- (c) If two first-layer reads fed by front ends are separated by the
first-layer slot duration, and the inverter slot fits in it, the two inverter
slots do not overlap: the first ends before the second starts. -/
theorem front_end_slots_disjoint {M : Nat} {s : InverterSlot} {firstTiming : SlotTiming}
    {start₁ start₂ : Rat} {external₁ external₂ : Fin M → Option Rat}
    {inv₁ inv₂ : Fin M → ReadObservation 1} {read₁ read₂ : ReadObservation (M + M)}
    (front₁ : FrontEnd s.timing start₁ external₁ inv₁ read₁)
    (front₂ : FrontEnd s.timing start₂ external₂ inv₂ read₂)
    (separated : read₁.start + firstTiming.duration ≤ read₂.start)
    (fits : s.duration ≤ firstTiming.duration) :
    start₁ + s.duration ≤ start₂ := by
  have h₁ := front₁.2.1
  have h₂ := front₂.2.1
  grind

/-- (c) Applied to consecutive training rounds, as `TrainingSeparation` orders them. -/
theorem training_inverter_slots_disjoint {p : Cascade A B (M + M)} {s : InverterSlot}
    {firstTiming secondTiming : SlotTiming} {o : Observations A B (M + M)}
    (separation : TrainingSeparation p firstTiming secondTiming o)
    (fits : s.duration ≤ firstTiming.duration)
    {r : Nat} (round : r < p.first.maxWrites) (a b : Fin A)
    {start₁ start₂ : Rat} {external₁ external₂ : Fin M → Option Rat}
    {inv₁ inv₂ : Fin M → ReadObservation 1}
    (front₁ : FrontEnd s.timing start₁ external₁ inv₁ (o.firstTrain r a))
    (front₂ : FrontEnd s.timing start₂ external₂ inv₂ (o.firstTrain (r + 1) b)) :
    start₁ + s.duration ≤ start₂ :=
  front_end_slots_disjoint front₁ front₂ (separation.1 r round a b) fits

/-- The composition with training, for a given cascade: trained and tested
through the inverters, it answers its predicted answer on the rails. -/
theorem trained_inverters_compute {p : Cascade A B (M + M)} (valid : p.Valid)
    {t : InverterTiming} {firstTiming secondTiming : SlotTiming}
    {o : Observations A B (M + M)} {scores : Pattern (M + M) → Fin B → Pattern A → Int}
    (windowFits : t.window ≤ firstTiming.skew) (spreadFits : t.emitLate - t.emitEarly ≤ firstTiming.skew)
    (training : InverterTrainingCalibration p t firstTiming secondTiming o)
    {y : Pattern M} {start : Rat} {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    (realised : ∀ j, (external j).isSome = y j)
    (front : InverterFrontRead p t firstTiming o y start external inv)
    (second : ∀ k, SecondTestRead p secondTiming o scores (rails y) k) :
    ∀ i, (o.secondTest (rails y) i).fired = output p i (rails y) :=
  inverters_compute valid windowFits spreadFits
    (training_through_front_end windowFits spreadFits training) realised front second

/-- Frozen target: every Boolean function of `M` inputs is computed by an
admissible cascade on `2 M` lines that is trained and tested through `M`
inverters. Every first-layer target is the rails of an input pattern, so the front
end can produce every training stimulus. -/
def EveryFunctionTrainedThroughInverters : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool),
    ∃ (A B : Nat) (p : Cascade A B (M + M)) (i : Fin B), p.Valid ∧
      (∀ a, ∃ x, f x = true ∧ p.first.target a = rails x) ∧
      ∀ (t : InverterTiming) (firstTiming secondTiming : SlotTiming)
        (o : Observations A B (M + M)) (scores : Pattern (M + M) → Fin B → Pattern A → Int),
        t.window ≤ firstTiming.skew → t.emitLate - t.emitEarly ≤ firstTiming.skew →
        InverterTrainingCalibration p t firstTiming secondTiming o →
        ∀ (y : Pattern M) (start : Rat) (external : Fin M → Option Rat)
          (inv : Fin M → ReadObservation 1),
          (∀ j, (external j).isSome = y j) →
          InverterFrontRead p t firstTiming o y start external inv →
          (∀ k, SecondTestRead p secondTiming o scores (rails y) k) →
          (o.secondTest (rails y) i).fired = f y

theorem every_function_trained_through_inverters : EveryFunctionTrainedThroughInverters := by
  intro M f
  obtain ⟨A, B, p, i, valid, same, targets⟩ := RailsExplicit.every_function_on_two_rails_explicit M f
  refine ⟨A, B, p, i, valid, targets, ?_⟩
  intro t firstTiming secondTiming o scores windowFits spreadFits training y start external inv
    realised front second
  rw [trained_inverters_compute valid windowFits spreadFits training realised front second i, same y]

end LearnedCoincidence.MonotoneDNF
