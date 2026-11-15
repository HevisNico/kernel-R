import MonotoneSupport

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch
  settledCount)

/-- The dated threshold decoder, with no assumption about an additive score. -/
def ThresholdRead (level : Nat) (timing : SlotTiming) (r : ReadObservation A) : Prop :=
  timing.Valid ∧
  (∀ j t, r.arrival j = some t → r.start ≤ t ∧ t ≤ r.start + timing.skew) ∧
  (match r.emissions with
    | [] => True
    | [t] =>
      r.start ≤ t ∧ t ≤ r.start + timing.deadline ∧
      ∀ j v, r.arrival j = some v → v ≤ t
    | _ => False) ∧
  r.fired = decide ((level : Int) ≤ r.measuredScore)

/-- Scores refer to the same settled checkpoint and read conditions, with
only the input mask varied. The observed mask cannot lose score relative
to a submask that reaches threshold. The singleton references need only
a lower bound. A constant-true cell uses the empty mask as its reference. -/
def FiringMaskRead (p : Disjunctions B A) (w : Counts B A) (i : Fin B)
    (timing : SlotTiming) (r : ReadObservation A) (scoreAt : Pattern A → Int) : Prop :=
  ThresholdRead (p.threshold i) timing r ∧
  scoreAt r.input = r.measuredScore ∧
  (∀ y, contains r.input y = true → (p.threshold i : Int) ≤ scoreAt y →
    scoreAt y ≤ scoreAt r.input) ∧
  if p.alwaysFire i then
    (p.help i : Int) - p.testingError i ≤ scoreAt (fun _ => false)
  else
    ∀ a, p.lines i a = true → r.input a = true →
      (lineScore p i a (w i a) : Int) - p.testingError i ≤ scoreAt (singleton a)

/-- Layer one and the teaching prefix keep additive calibration. At test,
the layer-two silent masks keep the two-sided residual. Firing masks use
the dated decoder and the one-sided score comparison. -/
def CascadeCalibrationOneSided (p : Cascade A B M) (firstTiming secondTiming : SlotTiming)
    (o : Observations A B M) (scores : Pattern M → Fin B → Pattern A → Int) : Prop :=
  CascadeTrainingCalibration p firstTiming secondTiming o ∧
  (∀ x a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a) x
    (p.first.testingError a) firstTiming (o.firstTest x a)) ∧
  ∀ x i, RoutedBatch (p.delay i) (o.firstTest x) (o.secondTest x i) ∧
    let r := o.secondTest x i
    let w := lessonCounts p o (lessons p).length
    if p.second.alwaysFire i || (List.finRange A).any (fun a => p.second.lines i a && r.input a) then
      FiringMaskRead p.second w i secondTiming r (scores x i)
    else
      CalibratedAdditiveRead (readView p.second w) i 0 r.input
        (p.second.testingError i) secondTiming r

/-- Frozen trace target for saturated layer-two reads of firing masks. -/
def TwoLayerMonotoneRecognitionOneSided : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M), p.Valid →
    ∀ (firstTiming secondTiming : SlotTiming) (o : Observations A B M)
      (scores : Pattern M → Fin B → Pattern A → Int),
      TrainingSeparation p firstTiming secondTiming o →
      CascadeCalibrationOneSided p firstTiming secondTiming o scores →
      CascadeTrainingCertificate p o ∧
      ∀ x i, (o.secondTest x i).fired = output p i x

end LearnedCoincidence.MonotoneDNF
