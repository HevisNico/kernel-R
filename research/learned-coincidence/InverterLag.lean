import InverterSchedule

/-! Direct-rail delay tolerance. `FrontEnd` delays the direct rails by exactly
`emitEarly`. Here the delay `lag` of a read may be anywhere in
`[emitEarly, emitEarly + ε]`; the read still starts at `start + emitEarly`. The
price is one more checkable date inequality, `window + ε ≤ skew`: the direct
pulses then still fall in the first layer's read window. -/

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch observedCount
  settledCount)

/-- A front-end read whose direct rails are delayed by `lag ∈ [emitEarly, emitEarly + ε]`. -/
def FrontEndLag {M : Nat} (t : InverterTiming) (ε lag : Rat) (start : Rat)
    (external : Fin M → Option Rat) (inv : Fin M → ReadObservation 1)
    (read : ReadObservation (M + M)) : Prop :=
  t.emitEarly ≤ lag ∧ lag ≤ t.emitEarly + ε ∧
  (∀ j, (inv j).start = start ∧ (inv j).arrival 0 = external j ∧ InverterRead t (inv j)) ∧
  read.start = start + t.emitEarly ∧
  read.arrival = frontArrival lag external inv

/-- The exact front end is the case `lag = emitEarly`, for any `ε ≥ 0`. -/
theorem front_end_is_lag {M : Nat} {t : InverterTiming} {ε start : Rat}
    {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    {read : ReadObservation (M + M)} (nonneg : 0 ≤ ε) (front : FrontEnd t start external inv read) :
    FrontEndLag t ε t.emitEarly start external inv read :=
  ⟨Rat.le_refl, by grind, front⟩

/-- The delay does not change which lines are active: the rails of the input. -/
theorem front_end_lag_input {M : Nat} {t : InverterTiming} {ε lag start : Rat}
    {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    {read : ReadObservation (M + M)} (front : FrontEndLag t ε lag start external inv read) :
    read.input = rails (fun j => (external j).isSome) := by
  obtain ⟨_, _, cells, _, arrivals⟩ := front
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

/-- With `window + ε ≤ skew`, every pulse falls in one read window. -/
theorem front_end_lag_window {M : Nat} {t : InverterTiming} {ε lag start skew : Rat}
    {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    {read : ReadObservation (M + M)} (front : FrontEndLag t ε lag start external inv read)
    (windowFits : t.window + ε ≤ skew) (spreadFits : t.emitLate - t.emitEarly ≤ skew) :
    ∀ j v, read.arrival j = some v → read.start ≤ v ∧ v ≤ read.start + skew := by
  obtain ⟨lagLow, lagHigh, cells, readStart, arrivals⟩ := front
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

/-- The delayed front end and the remaining clauses give the calibrated read. -/
theorem front_end_lag_calibrated {M N : Nat} {p : Parameters N (M + M)} {a : Fin N}
    {writes budget : Nat} {t : InverterTiming} {timing : SlotTiming} {ε lag start : Rat}
    {target : Pattern (M + M)} {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    {read : ReadObservation (M + M)}
    (front : FrontEndLag t ε lag start external inv read)
    (atTarget : rails (fun j => (external j).isSome) = target)
    (rest : ReadAfterFront p a writes target budget timing read)
    (windowFits : t.window + ε ≤ timing.skew) (spreadFits : t.emitLate - t.emitEarly ≤ timing.skew) :
    CalibratedAdditiveRead p a writes target budget timing read := by
  have input : read.input = target := (front_end_lag_input front).trans atTarget
  obtain ⟨valid, emission, decoder, residual⟩ := rest
  exact ⟨valid, input, front_end_lag_window front windowFits spreadFits, emission, decoder, residual⟩

/-- The test premise with delayed direct rails, at the input pattern `y`. -/
def InverterFrontReadLag (p : Cascade A B (M + M)) (t : InverterTiming) (ε lag : Rat)
    (firstTiming : SlotTiming) (o : Observations A B (M + M)) (y : Pattern M) (start : Rat)
    (external : Fin M → Option Rat) (inv : Fin M → ReadObservation 1) : Prop :=
  ∀ a, FrontEndLag t ε lag start external inv (o.firstTest (rails y) a) ∧
    ReadAfterFront p.first a (settledCount p.first o.firstTrain a) (rails y)
      (p.first.testingError a) firstTiming (o.firstTest (rails y) a)

/-- Training on a fixed schedule, with a delay per training read and per lesson. -/
def ScheduledInverterTrainingLag (p : Cascade A B (M + M)) (t : InverterTiming) (ε : Rat)
    (firstTiming secondTiming : SlotTiming) (o : Observations A B (M + M))
    (s : InverterSchedule A M) (trainLag teachLag : Nat → Fin A → Rat) : Prop :=
  (∀ r, r ≤ p.first.maxWrites → ∀ a,
    FrontEndLag t ε (trainLag r a) (s.trainStart r a) (s.trainExternal r a) (s.trainInv r a)
      (o.firstTrain r a) ∧
    rails (fun j => (s.trainExternal r a j).isSome) = p.first.target a ∧
    ReadAfterFront p.first a (observedCount o.firstTrain a r) (p.first.target a)
      (p.first.trainingError a) firstTiming (o.firstTrain r a)) ∧
  (∀ n L, (lessons p)[n]? = some L →
    (∀ a, FrontEndLag t ε (teachLag n a) (s.teachStart n a) (s.teachExternal n a) (s.teachInv n a)
        (o.teach n a) ∧
      rails (fun j => (s.teachExternal n a j).isSome) = p.first.target L.line ∧
      ReadAfterFront p.first a (settledCount p.first o.firstTrain a) (p.first.target L.line)
        (p.first.testingError a) firstTiming (o.teach n a)) ∧
    RoutedBatch (p.delay L.cell) (o.teach n) (o.secondTrain n) ∧
    CalibratedAdditiveRead (readView p.second (lessonCounts p o n)) L.cell 0 (o.secondTrain n).input
      (p.second.trainingError L.cell) secondTiming (o.secondTrain n))

theorem scheduled_training_lag_calibration {p : Cascade A B (M + M)} {t : InverterTiming} {ε : Rat}
    {firstTiming secondTiming : SlotTiming} {o : Observations A B (M + M)} {s : InverterSchedule A M}
    {trainLag teachLag : Nat → Fin A → Rat}
    (windowFits : t.window + ε ≤ firstTiming.skew) (spreadFits : t.emitLate - t.emitEarly ≤ firstTiming.skew)
    (scheduled : ScheduledInverterTrainingLag p t ε firstTiming secondTiming o s trainLag teachLag) :
    CascadeTrainingCalibration p firstTiming secondTiming o := by
  refine ⟨fun r bound a => ?_, fun n L atIndex => ?_⟩
  · obtain ⟨front, atTarget, rest⟩ := scheduled.1 r bound a
    exact front_end_lag_calibrated front atTarget rest windowFits spreadFits
  · obtain ⟨teaching, route, second⟩ := scheduled.2 n L atIndex
    refine ⟨fun a => ?_, route, second⟩
    obtain ⟨front, atTarget, rest⟩ := teaching a
    exact front_end_lag_calibrated front atTarget rest windowFits spreadFits

/-- The test composition with delayed direct rails, for a given cascade. -/
theorem inverters_compute_lag {p : Cascade A B (M + M)} (valid : p.Valid)
    {t : InverterTiming} {ε lag : Rat} {firstTiming secondTiming : SlotTiming}
    {o : Observations A B (M + M)} {scores : Pattern (M + M) → Fin B → Pattern A → Int}
    (windowFits : t.window + ε ≤ firstTiming.skew) (spreadFits : t.emitLate - t.emitEarly ≤ firstTiming.skew)
    (training : CascadeTrainingCalibration p firstTiming secondTiming o)
    {y : Pattern M} {start : Rat} {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    (realised : ∀ j, (external j).isSome = y j)
    (front : InverterFrontReadLag p t ε lag firstTiming o y start external inv)
    (second : ∀ k, SecondTestRead p secondTiming o scores (rails y) k) :
    ∀ i, (o.secondTest (rails y) i).fired = output p i (rails y) := by
  have firstReads : ∀ a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a)
      (rails y) (p.first.testingError a) firstTiming (o.firstTest (rails y) a) := fun a =>
    front_end_lag_calibrated (front a).1 (congrArg rails (funext realised)) (front a).2
      windowFits spreadFits
  exact one_sided_recognition_at valid training firstReads second

/-- Training on a fixed schedule and testing, both with delayed direct rails. -/
theorem scheduled_inverters_compute_lag {p : Cascade A B (M + M)} (valid : p.Valid)
    {t : InverterTiming} {ε lag : Rat} {firstTiming secondTiming : SlotTiming}
    {o : Observations A B (M + M)} {scores : Pattern (M + M) → Fin B → Pattern A → Int}
    {s : InverterSchedule A M} {trainLag teachLag : Nat → Fin A → Rat}
    (windowFits : t.window + ε ≤ firstTiming.skew) (spreadFits : t.emitLate - t.emitEarly ≤ firstTiming.skew)
    (training : ScheduledInverterTrainingLag p t ε firstTiming secondTiming o s trainLag teachLag)
    {y : Pattern M} {start : Rat} {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    (realised : ∀ j, (external j).isSome = y j)
    (front : InverterFrontReadLag p t ε lag firstTiming o y start external inv)
    (second : ∀ k, SecondTestRead p secondTiming o scores (rails y) k) :
    ∀ i, (o.secondTest (rails y) i).fired = output p i (rails y) :=
  inverters_compute_lag valid windowFits spreadFits
    (scheduled_training_lag_calibration windowFits spreadFits training) realised front second

/-- Frozen target: every Boolean function is computed by a cascade trained on a
fixed inverter schedule and tested through the inverters, with every direct-rail
delay anywhere in `[emitEarly, emitEarly + ε]` and `window + ε ≤ skew`. -/
def EveryFunctionWithDelayTolerance : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool),
    ∃ (A B : Nat) (p : Cascade A B (M + M)) (i : Fin B), p.Valid ∧
      (∀ a, ∃ x, f x = true ∧ p.first.target a = rails x) ∧
      ∀ (t : InverterTiming) (ε lag : Rat) (firstTiming secondTiming : SlotTiming)
        (o : Observations A B (M + M)) (scores : Pattern (M + M) → Fin B → Pattern A → Int)
        (s : InverterSchedule A M) (trainLag teachLag : Nat → Fin A → Rat),
        t.window + ε ≤ firstTiming.skew → t.emitLate - t.emitEarly ≤ firstTiming.skew →
        ScheduledInverterTrainingLag p t ε firstTiming secondTiming o s trainLag teachLag →
        ∀ (y : Pattern M) (start : Rat) (external : Fin M → Option Rat)
          (inv : Fin M → ReadObservation 1),
          (∀ j, (external j).isSome = y j) →
          InverterFrontReadLag p t ε lag firstTiming o y start external inv →
          (∀ k, SecondTestRead p secondTiming o scores (rails y) k) →
          (o.secondTest (rails y) i).fired = f y

theorem every_function_with_delay_tolerance : EveryFunctionWithDelayTolerance := by
  intro M f
  obtain ⟨A, B, p, i, valid, same, targets⟩ := RailsExplicit.every_function_on_two_rails_explicit M f
  refine ⟨A, B, p, i, valid, targets, ?_⟩
  intro t ε lag firstTiming secondTiming o scores s trainLag teachLag windowFits spreadFits training
    y start external inv realised front second
  rw [scheduled_inverters_compute_lag valid windowFits spreadFits training realised front second i,
    same y]

end LearnedCoincidence.MonotoneDNF
