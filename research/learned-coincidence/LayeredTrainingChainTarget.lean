import LayeredCompositionTarget

/-! The timing chain for the training lessons: definitions and the frozen target only.
A lesson is addressed to cell `i` of layer `ℓ + 1`, group `g` and round `r`. It replays the
lower layers and then reads the addressed cell. `σ (ℓ + 1) i g r k` is the read start of
layer `k` in that lesson, where `k ≤ ℓ + 1` and layer 0 is the external stimulus. The pulse
windows `e`, `f` are shared by all lessons, as in the test chain. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)

abbrev LessonClock := Nat → Nat → Nat → Nat → Nat → Rat

/-- `TrainingCalibration` without any arrival window. -/
def TrainingReads : (c : Cascade M L N) → TrainingTrace c → Prop
  | .input, _ => True
  | .layer lower timing nodes, train =>
    TrainingReads lower train.1 ∧
    ∀ i (g : Fin 2), g.val < (nodes i).cell.gate.groups →
      ∀ r, r ≤ (nodes i).cell.maxWrites →
        let d := nodes i
        let replay := train.2.1 i g r
        let reads := train.2.2 i
        (fun j => (inputTrace lower replay j).isSome) = d.stimulus g ∧
        LayerReads lower train.1 replay ∧
        Routed d (pulseDates lower replay) (reads g r) ∧
        AdditiveDecoded d.cell (d.cell.writesBefore reads g r) d.cell.trainError timing (reads g r)

/-- The lesson reads start on the lesson clock. -/
def TrainingScheduled (σ : LessonClock) : (c : Cascade M L N) → TrainingTrace c → Prop
  | .input, _ => True
  | .layer (L := L) lower _ nodes, train =>
    TrainingScheduled σ lower train.1 ∧
    ∀ i (g : Fin 2), g.val < (nodes i).cell.gate.groups →
      ∀ r, r ≤ (nodes i).cell.maxWrites →
        Scheduled (σ (L + 1) i.val g.val r) lower (train.2.1 i g r) ∧
        (train.2.2 i g r).start = σ (L + 1) i.val g.val r (L + 1)

/-- The lower pulses of each lesson lie in the shared windows. -/
def TrainingPulses (σ : LessonClock) (e f : Nat → Rat) : (c : Cascade M L N) → TrainingTrace c → Prop
  | .input, _ => True
  | .layer (L := L) lower _ nodes, train =>
    TrainingPulses σ e f lower train.1 ∧
    ∀ i (g : Fin 2), g.val < (nodes i).cell.gate.groups →
      ∀ r, r ≤ (nodes i).cell.maxWrites →
        PulseWindows (σ (L + 1) i.val g.val r) e f lower (train.2.1 i g r)

/-- The chain inequalities of every lesson, on constants only: those of its replay of the
lower layers, and those of the addressed cell. -/
def TrainingChainDates (σ : LessonClock) (e f : Nat → Rat) : (c : Cascade M L N) → Prop
  | .input => True
  | .layer (L := L) lower timing nodes =>
    TrainingChainDates σ e f lower ∧
    ∀ i (g : Fin 2), g.val < (nodes i).cell.gate.groups →
      ∀ r, r ≤ (nodes i).cell.maxWrites →
        let s := σ (L + 1) i.val g.val r
        ChainDates s e f lower ∧
        ∀ a src, (nodes i).source a = some src →
          s (L + 1) ≤ s L + e L + (nodes i).delay a ∧
          s L + f L + (nodes i).delay a ≤ s (L + 1) + timing.skew

/-- Frozen target. The training calibration, with its windows derived. -/
def TrainingCalibrationChained : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (train : TrainingTrace c) (σ : LessonClock) (e f : Nat → Rat),
    TrainingChainDates σ e f c → TrainingReads c train → TrainingScheduled σ c train →
    TrainingPulses σ e f c train → TrainingCalibration c train

end LearnedCoincidence.Layered
