import MonotonePremiseTargets

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming)

/-- Frozen converse for the parameter checker. -/
def CascadeValidCheckerComplete : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M), p.Valid → checkCascadeValid p = true

/-- Frozen converse for the calendar checker. -/
def TrainingSeparationCheckerComplete : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M) (left right : SlotTiming) (o : Observations A B M),
    TrainingSeparation p left right o → checkTrainingSeparation p left right o = true

/-- Frozen converse for the calibration checker. -/
def CascadeCalibrationOneSidedCheckerComplete : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M) (left right : SlotTiming) (o : Observations A B M)
    (scores : Pattern M → Fin B → Pattern A → Int),
    CascadeCalibrationOneSided p left right o scores →
      checkCascadeCalibrationOneSided p left right o scores = true

end LearnedCoincidence.MonotoneDNF
