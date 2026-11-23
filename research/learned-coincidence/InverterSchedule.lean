import InverterTraining

/-! Training through the inverters on a schedule fixed in advance.

`InverterTrainingCalibration` asks, for each training and teaching read, that
SOME start, input pulses and inverter observations produce it through the front
end. Those witnesses may be chosen after the fact: given a read whose dates fit
the front-end pattern, inverter observations can be written down to match it. The
existential therefore constrains the DATES of the reads (direct pulses within the
input window after the read start, complement pulses strictly after it and within
the inverters' spread, each complement pulse the late emission of an inverter
whose input was absent). It does not tie the reads to an inverter schedule given
beforehand.

Here the schedule is a parameter: for every training round, lesson and cell it
names the slot start, the input pulses and the inverter observations, and the
premise is that THESE produce the reads. Said plainly, as a statement of logic,
`∀ s, P s → C` is equivalent to `(∃ s, P s) → C`, so the scheduled theorem is not
logically stronger. What it changes is the interface: a checker or an experiment
is handed one schedule, fixed before the run, and verifies the premise for it,
instead of searching for witnesses. -/

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch observedCount
  settledCount)

/-- What the front end forces on any read it produces: every complement-rail pulse
arrives STRICTLY after the read starts (the inverter decides only after its window).
`CalibratedAdditiveRead` allows a pulse at the read start itself. -/
theorem front_end_complement_late {M : Nat} {t : InverterTiming} {start : Rat}
    {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    {read : ReadObservation (M + M)} (front : FrontEnd t start external inv read)
    (j : Fin (M + M)) (complement : ¬ j.val < M) {v : Rat} (arrived : read.arrival j = some v) :
    read.start < v := by
  obtain ⟨cells, readStart, arrivals⟩ := front
  rw [arrivals] at arrived
  rw [readStart]
  simp only [frontArrival, complement, dite_false] at arrived
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
      exact emission.1
    | cons _ _ => exact emission.elim

/-- Hence the existential form is not a restatement of the old premise: a read
with a complement pulse at its start meets the arrival clause of
`CalibratedAdditiveRead` but is produced by no front end. -/
theorem directly_driven_not_front_end {M : Nat} {t : InverterTiming}
    {read : ReadObservation (M + M)} (j : Fin (M + M)) (complement : ¬ j.val < M)
    (atStart : read.arrival j = some read.start) :
    ¬ ∃ start external inv, FrontEnd t start external inv read := by
  rintro ⟨start, external, inv, front⟩
  have late := front_end_complement_late front j complement atStart
  exact Rat.lt_irrefl late

/-- The inverter schedule of training: slot starts, input pulses and inverter
observations for every training round and cell, and every lesson and cell. -/
structure InverterSchedule (A M : Nat) where
  trainStart : Nat → Fin A → Rat
  trainExternal : Nat → Fin A → Fin M → Option Rat
  trainInv : Nat → Fin A → Fin M → ReadObservation 1
  teachStart : Nat → Fin A → Rat
  teachExternal : Nat → Fin A → Fin M → Option Rat
  teachInv : Nat → Fin A → Fin M → ReadObservation 1

/-- The training calibration, with every first-layer read of training and teaching
produced through the front end by the GIVEN schedule. -/
def ScheduledInverterTraining (p : Cascade A B (M + M)) (t : InverterTiming)
    (firstTiming secondTiming : SlotTiming) (o : Observations A B (M + M))
    (s : InverterSchedule A M) : Prop :=
  (∀ r, r ≤ p.first.maxWrites → ∀ a,
    FrontEnd t (s.trainStart r a) (s.trainExternal r a) (s.trainInv r a) (o.firstTrain r a) ∧
    rails (fun j => (s.trainExternal r a j).isSome) = p.first.target a ∧
    ReadAfterFront p.first a (observedCount o.firstTrain a r) (p.first.target a)
      (p.first.trainingError a) firstTiming (o.firstTrain r a)) ∧
  (∀ n L, (lessons p)[n]? = some L →
    (∀ a, FrontEnd t (s.teachStart n a) (s.teachExternal n a) (s.teachInv n a) (o.teach n a) ∧
      rails (fun j => (s.teachExternal n a j).isSome) = p.first.target L.line ∧
      ReadAfterFront p.first a (settledCount p.first o.firstTrain a) (p.first.target L.line)
        (p.first.testingError a) firstTiming (o.teach n a)) ∧
    RoutedBatch (p.delay L.cell) (o.teach n) (o.secondTrain n) ∧
    CalibratedAdditiveRead (readView p.second (lessonCounts p o n)) L.cell 0 (o.secondTrain n).input
      (p.second.trainingError L.cell) secondTiming (o.secondTrain n))

/-- A fixed schedule supplies the existential form. -/
theorem scheduled_training_calibration {p : Cascade A B (M + M)} {t : InverterTiming}
    {firstTiming secondTiming : SlotTiming} {o : Observations A B (M + M)} {s : InverterSchedule A M}
    (scheduled : ScheduledInverterTraining p t firstTiming secondTiming o s) :
    InverterTrainingCalibration p t firstTiming secondTiming o := by
  refine ⟨fun r bound a => ?_, fun n L atIndex => ?_⟩
  · obtain ⟨front, atTarget, rest⟩ := scheduled.1 r bound a
    exact ⟨⟨_, _, _, front, atTarget⟩, rest⟩
  · obtain ⟨teaching, route, second⟩ := scheduled.2 n L atIndex
    refine ⟨fun a => ?_, route, second⟩
    obtain ⟨front, atTarget, rest⟩ := teaching a
    exact ⟨⟨_, _, _, front, atTarget⟩, rest⟩

/-- The composition with training on a fixed schedule, for a given cascade. -/
theorem scheduled_inverters_compute {p : Cascade A B (M + M)} (valid : p.Valid)
    {t : InverterTiming} {firstTiming secondTiming : SlotTiming}
    {o : Observations A B (M + M)} {scores : Pattern (M + M) → Fin B → Pattern A → Int}
    {s : InverterSchedule A M}
    (windowFits : t.window ≤ firstTiming.skew) (spreadFits : t.emitLate - t.emitEarly ≤ firstTiming.skew)
    (training : ScheduledInverterTraining p t firstTiming secondTiming o s)
    {y : Pattern M} {start : Rat} {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1}
    (realised : ∀ j, (external j).isSome = y j)
    (front : InverterFrontRead p t firstTiming o y start external inv)
    (second : ∀ k, SecondTestRead p secondTiming o scores (rails y) k) :
    ∀ i, (o.secondTest (rails y) i).fired = output p i (rails y) :=
  trained_inverters_compute valid windowFits spreadFits (scheduled_training_calibration training)
    realised front second

/-- Frozen target: every Boolean function is computed by a cascade trained on a
fixed inverter schedule and tested through the inverters. -/
def EveryFunctionTrainedOnSchedule : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool),
    ∃ (A B : Nat) (p : Cascade A B (M + M)) (i : Fin B), p.Valid ∧
      (∀ a, ∃ x, f x = true ∧ p.first.target a = rails x) ∧
      ∀ (t : InverterTiming) (firstTiming secondTiming : SlotTiming)
        (o : Observations A B (M + M)) (scores : Pattern (M + M) → Fin B → Pattern A → Int)
        (s : InverterSchedule A M),
        t.window ≤ firstTiming.skew → t.emitLate - t.emitEarly ≤ firstTiming.skew →
        ScheduledInverterTraining p t firstTiming secondTiming o s →
        ∀ (y : Pattern M) (start : Rat) (external : Fin M → Option Rat)
          (inv : Fin M → ReadObservation 1),
          (∀ j, (external j).isSome = y j) →
          InverterFrontRead p t firstTiming o y start external inv →
          (∀ k, SecondTestRead p secondTiming o scores (rails y) k) →
          (o.secondTest (rails y) i).fired = f y

theorem every_function_trained_on_schedule : EveryFunctionTrainedOnSchedule := by
  intro M f
  obtain ⟨A, B, p, i, valid, targets, rest⟩ := every_function_trained_through_inverters M f
  refine ⟨A, B, p, i, valid, targets, ?_⟩
  intro t firstTiming secondTiming o scores s windowFits spreadFits training
  exact rest t firstTiming secondTiming o scores windowFits spreadFits
    (scheduled_training_calibration training)

end LearnedCoincidence.MonotoneDNF
