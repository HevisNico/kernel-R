import MonotoneRecognition

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch settledCount)

/-- The same dates, emission window and threshold decoder as the additive
interface, for a slot whose input is its actual arrival mask. -/
def ThresholdRead (level : Nat) (timing : SlotTiming) (r : ReadObservation A) : Prop :=
  timing.Valid ∧
  (∀ a t, r.arrival a = some t → r.start ≤ t ∧ t ≤ r.start + timing.skew) ∧
  (match r.emissions with
    | [] => True
    | [t] =>
      r.start ≤ t ∧ t ≤ r.start + timing.deadline ∧
      ∀ a v, r.arrival a = some v → v ≤ t
    | _ => False) ∧
  r.fired = decide ((level : Int) ≤ r.measuredScore)

/-- Compare the score to every observed firing submask of the same cell at
the settled checkpoint. This includes the final singleton lessons. Inclusion
allows equality, so a singleton test is also compared to its training reference.
Two firing test slots with the same mask must therefore report the same score. -/
def FiringSubmaskOrder (p : Cascade A B M) (o : Observations A B M)
    (i : Fin B) (r : ReadObservation A) : Prop :=
  (∀ n L, (lessons p)[n]? = some L → L.cell = i →
    lessonCounts p o n = lessonCounts p o (lessons p).length →
    contains r.input (o.secondTrain n).input = true → (o.secondTrain n).fired = true →
    (o.secondTrain n).measuredScore ≤ r.measuredScore) ∧
  ∀ x, contains r.input (o.secondTest x i).input = true → (o.secondTest x i).fired = true →
    (o.secondTest x i).measuredScore ≤ r.measuredScore

/-- Whether the arrival mask contains a line selected for training. -/
def hasTrainedLine (p : Disjunctions B A) (i : Fin B) (x : Pattern A) : Bool :=
  (List.finRange A).any fun a => p.lines i a && x a

/-- Retain additive calibration for the entire first layer and for all
training. On downstream tests, apply the score order precisely when a
selected line arrived. All other masks use the symmetric residual, including
fixed-bias cells, which have no trained lines. -/
def CascadeCalibrationOneSided (p : Cascade A B M) (left right : SlotTiming)
    (o : Observations A B M) : Prop :=
  TrainingCalibration p left right o ∧
  (∀ x a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a) x
    (p.first.testingError a) left (o.firstTest x a)) ∧
  ∀ x i, RoutedBatch (p.delay i) (o.firstTest x) (o.secondTest x i) ∧
    if hasTrainedLine p.second i (o.secondTest x i).input then
      ThresholdRead (p.second.threshold i) right (o.secondTest x i) ∧
        FiringSubmaskOrder p o i (o.secondTest x i)
    else
      CalibratedAdditiveRead (readView p.second (lessonCounts p o (lessons p).length)) i 0
        (o.secondTest x i).input (p.second.testingError i) right (o.secondTest x i)

/-- The same training and prediction conclusions as the symmetric target,
with firing submask order in place of an additive fit on active OR reads. -/
def TwoLayerMonotoneRecognitionOneSided : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M), p.Valid →
    ∀ (left right : SlotTiming) (o : Observations A B M),
      TrainingSeparation p left right o →
      CascadeCalibrationOneSided p left right o →
      TrainingConclusion p o ∧ ∀ x i, (o.secondTest x i).fired = output p i x

private theorem fire_of_submask {p : Cascade A B M} (valid : p.Valid)
    {o : Observations A B M} {left right : SlotTiming}
    (calibration : TrainingCalibration p left right o) (training : TrainingConclusion p o)
    {i : Fin B} {r : ReadObservation A}
    (threshold : ThresholdRead (p.second.threshold i) right r)
    (ordered : FiringSubmaskOrder p o i r)
    (present : hasTrainedLine p.second i r.input = true) : r.fired = true := by
  obtain ⟨a, _, on⟩ := List.any_eq_true.mp present
  have ⟨selected, arrived⟩ := Bool.and_eq_true_iff.mp on
  obtain ⟨n, lesson, settled, mask, fire, scoreAtLine⟩ :=
    settled_singleton_lesson valid calibration training i a selected
  have included : contains r.input (o.secondTrain n).input = true := by
    rw [mask]
    exact contains_iff.mpr fun b hb => (of_decide_eq_true hb : b = a) ▸ arrived
  have lower := ordered.1 n ⟨i, a⟩ lesson rfl settled included fire
  exact threshold.2.2.2.trans (decide_eq_true (Int.le_trans scoreAtLine lower))

/-- Singleton training supplies a firing anchor at the same memory
checkpoint, so the one-sided condition cannot hold vacuously on active reads. -/
theorem two_layer_monotone_recognition_one_sided : TwoLayerMonotoneRecognitionOneSided := by
  intro A B M p valid left right o _separation calibration
  have training := guarded_training valid calibration.1
  refine ⟨training, ?_⟩
  intro x i
  obtain ⟨route, read⟩ := calibration.2.2 x i
  have input := guarded_test_input valid training x i (calibration.2.1 x) route
  have prediction : output p i x =
      (p.second.alwaysFire i || hasTrainedLine p.second i (o.secondTest x i).input) := by
    rw [input]
    rfl
  rw [prediction]
  cases present : hasTrainedLine p.second i (o.secondTest x i).input with
  | false =>
    rw [ite_eq_right (by simp [present])] at read
    have decision := guarded_additive_test valid training x i read
    change (o.secondTest x i).fired =
      (p.second.alwaysFire i || hasTrainedLine p.second i (o.secondTest x i).input) at decision
    rw [present] at decision
    exact decision
  | true =>
    rw [ite_eq_left present] at read
    rw [Bool.or_true]
    exact fire_of_submask valid calibration.1 training read.1 read.2 present

end LearnedCoincidence.MonotoneDNF
