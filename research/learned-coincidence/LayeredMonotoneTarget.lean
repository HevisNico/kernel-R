import MonotoneOneSidedTarget

/-! A layered circuit with fixed wires between consecutive layers. A lesson
replays the trained earlier layers read-only and writes only at its addressed cell. -/
namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF (ThresholdRead MonotoneFunction)

def emptyMask : Pattern 2 := fun _ => false
def fullMask : Pattern 2 := fun _ => true

inductive Gate where
  | off | on | copy | both | either
  deriving DecidableEq

def Gate.eval : Gate → Pattern 2 → Bool
  | .off, _ => false
  | .on, _ => true
  | .copy, x => x 0
  | .both, x => x 0 && x 1
  | .either, x => x 0 || x 1

/-- The nullary gates are the constant cases of OR and AND. A unary gate
copies its first port and can carry a signal across a layer. -/
def Gate.uses : Gate → Fin 2 → Bool
  | .off, _ | .on, _ => false
  | .copy, a => decide (a = 0)
  | .both, _ | .either, _ => true

def Gate.groups : Gate → Nat
  | .off | .on => 0
  | .copy | .both => 1
  | .either => 2

def Gate.groupMask : Gate → Fin 2 → Pattern 2
  | .copy, _ => MonotoneDNF.singleton 0
  | .both, _ => fullMask
  | .either, g => MonotoneDNF.singleton g
  | _, _ => emptyMask

/-- Minimal firing references. Only these references require testing margin. -/
def Gate.anchors : Gate → List (Pattern 2)
  | .off => []
  | .on => [emptyMask]
  | .copy => [MonotoneDNF.singleton 0]
  | .both => [fullMask]
  | .either => [MonotoneDNF.singleton 0, MonotoneDNF.singleton 1]

structure Cell where
  gate : Gate
  initialGain : Fin 2 → Nat
  help : Nat
  threshold : Nat
  trainError : Nat
  testError : Nat
  dose : Nat
  maxWrites : Nat
  rail : Nat

abbrev Writes := Fin 2 → Nat
abbrev CellTrain := Fin 2 → Nat → ReadObservation 2

def Cell.gain (p : Cell) (w : Writes) (a : Fin 2) : Nat :=
  p.initialGain a + p.dose * w a

def Cell.score (p : Cell) (w : Writes) (x : Pattern 2) : Nat :=
  p.help + (if x 0 then p.gain w 0 else 0) + (if x 1 then p.gain w 1 else 0)

def Cell.groupWrites (p : Cell) (g : Fin 2) (k : Nat) : Writes :=
  fun a => if p.gate.groupMask g a then k else 0

def Cell.groupScore (p : Cell) (g : Fin 2) (k : Nat) : Nat :=
  p.score (p.groupWrites g k) (p.gate.groupMask g)

def Cell.stop (p : Cell) (g : Fin 2) : Nat :=
  ((List.range (p.maxWrites + 1)).find? fun k => decide (p.threshold ≤ p.groupScore g k)).getD
    (p.maxWrites + 1)

def Cell.expectedWrites (p : Cell) (a : Fin 2) : Nat :=
  (if 0 < p.gate.groups then p.groupWrites 0 (p.stop 0) a else 0) +
  (if 1 < p.gate.groups then p.groupWrites 1 (p.stop 1) a else 0)

def Cell.Valid (p : Cell) : Prop :=
  0 < p.dose ∧
  (∀ g : Fin 2, g.val < p.gate.groups →
    (0 < p.stop g ∧ p.stop g ≤ p.maxWrites) ∧
    (∀ k, k < p.stop g → p.groupScore g k + p.trainError < p.threshold) ∧
    p.threshold + p.trainError ≤ p.groupScore g (p.stop g)) ∧
  (∀ a, p.gain p.expectedWrites a < p.rail) ∧
  (∀ x, p.gate.eval x = false → p.score p.expectedWrites x + p.testError < p.threshold) ∧
  (∀ y ∈ p.gate.anchors, p.threshold + p.testError ≤ p.score p.expectedWrites y)

/-- Count a write only on an observed arrival and an observed silence. -/
def groupObserved (train : CellTrain) (g : Fin 2) (a : Fin 2) : Nat → Nat
  | 0 => 0
  | r + 1 => groupObserved train g a r +
    if !(train g r).fired && (train g r).input a then 1 else 0

def Cell.writesBefore (p : Cell) (train : CellTrain) (g : Fin 2) (r : Nat) (a : Fin 2) : Nat :=
  (if g = 0 then 0 else groupObserved train 0 a (p.maxWrites + 1)) + groupObserved train g a r

def Cell.settledWrites (p : Cell) (train : CellTrain) (a : Fin 2) : Nat :=
  (if 0 < p.gate.groups then groupObserved train 0 a (p.maxWrites + 1) else 0) +
  (if 1 < p.gate.groups then groupObserved train 1 a (p.maxWrites + 1) else 0)

def Cell.Trained (p : Cell) (train : CellTrain) : Prop :=
  (∀ g : Fin 2, g.val < p.gate.groups → ∀ r, r ≤ p.maxWrites →
    (train g r).input = p.gate.groupMask g ∧ (train g r).fired = decide (p.stop g ≤ r)) ∧
  (∀ g : Fin 2, g.val < p.gate.groups → ∀ r, r ≤ p.maxWrites + 1 → ∀ a,
    groupObserved train g a r = p.groupWrites g (min r (p.stop g)) a ∧
    p.writesBefore train g r a ≤ p.expectedWrites a ∧
    p.gain (p.writesBefore train g r) a < p.rail) ∧
  (∀ a, p.settledWrites train a = p.expectedWrites a)

structure Node (M N : Nat) where
  cell : Cell
  source : Fin 2 → Option (Fin N)
  delay : Fin 2 → Rat
  stimulus : Fin 2 → Pattern M

def Node.inputs (d : Node M N) (x : Pattern N) : Pattern 2 :=
  fun a => ((d.source a).map x).getD false

def Node.Valid (d : Node M N) (predict : Pattern M → Pattern N) : Prop :=
  d.cell.Valid ∧
  (∀ a, (d.source a).isSome = d.cell.gate.uses a ∧ 0 ≤ d.delay a) ∧
  ∀ g : Fin 2, g.val < d.cell.gate.groups →
    d.inputs (predict (d.stimulus g)) = d.cell.gate.groupMask g

/-- Indexed by the number of layers and the width of the last layer. -/
inductive Cascade (M : Nat) : Nat → Nat → Type
  | input : Cascade M 0 M
  | layer : Cascade M L N → SlotTiming → (Fin B → Node M N) → Cascade M (L + 1) B

def Cascade.predict : Cascade M L N → Pattern M → Pattern N
  | .input, x => x
  | .layer lower _ nodes, x =>
    fun i => (nodes i).cell.gate.eval ((nodes i).inputs (lower.predict x))

def Cascade.Valid : Cascade M L N → Prop
  | .input => True
  | .layer lower timing nodes =>
    lower.Valid ∧ timing.Valid ∧ ∀ i, (nodes i).Valid lower.predict

/-- Each replay records external arrivals, full emission lists at each
cell, and reference scores at the same settled checkpoint and read conditions. -/
def ReadTrace : Cascade M L N → Type
  | .input => Fin M → Option Rat
  | .layer lower _ _ =>
    ReadTrace lower × (Fin N → ReadObservation 2) × (Fin N → Pattern 2 → Int)

def TrainingTrace : Cascade M L N → Type
  | .input => Unit
  | .layer lower _ _ =>
    TrainingTrace lower × (Fin N → Fin 2 → Nat → ReadTrace lower) × (Fin N → CellTrain)

def pulseDates : (c : Cascade M L N) → ReadTrace c → Fin N → Option Rat
  | .input, r => r
  | .layer _ _ _, r => fun i => (r.2.1 i).emissions.head?

def observed : (c : Cascade M L N) → ReadTrace c → Pattern N
  | .input, r => fun i => (r i).isSome
  | .layer _ _ _, r => fun i => (r.2.1 i).fired

def Routed (d : Node M N) (incoming : Fin N → Option Rat) (r : ReadObservation 2) : Prop :=
  ∀ a, r.arrival a = ((d.source a).bind incoming).map (fun t => t + d.delay a)

/-- An exact dated decoder and a two-sided residual for the observed mask. -/
def AdditiveSlot (p : Cell) (w : Writes) (budget : Nat) (timing : SlotTiming)
    (r : ReadObservation 2) : Prop :=
  ThresholdRead p.threshold timing r ∧
  admissible budget (r.measuredScore - (p.score w r.input : Int))

/-- The observed score dominates each firing submask. Each contained minimal
firing reference needs only a lower bound. -/
def FiringSlot (p : Cell) (w : Writes) (timing : SlotTiming)
    (r : ReadObservation 2) (scoreAt : Pattern 2 → Int) : Prop :=
  ThresholdRead p.threshold timing r ∧
  scoreAt r.input = r.measuredScore ∧
  (∀ y, contains r.input y = true → (p.threshold : Int) ≤ scoreAt y →
    scoreAt y ≤ scoreAt r.input) ∧
  ∀ y ∈ p.gate.anchors, contains r.input y = true →
    (p.score w y : Int) - p.testError ≤ scoreAt y

def ReadCalibration : (c : Cascade M L N) → TrainingTrace c → Pattern M → ReadTrace c → Prop
  | .input, _, x, r => (fun i => (r i).isSome) = x
  | .layer lower timing nodes, train, x, r =>
    ReadCalibration lower train.1 x r.1 ∧
    ∀ i,
      let d := nodes i
      let read := r.2.1 i
      let w := d.cell.settledWrites (train.2.2 i)
      Routed d (pulseDates lower r.1) read ∧
      if d.cell.gate.eval read.input then
        FiringSlot d.cell w timing read (r.2.2 i)
      else
        AdditiveSlot d.cell w d.cell.testError timing read

def TrainingCalibration : (c : Cascade M L N) → TrainingTrace c → Prop
  | .input, _ => True
  | .layer lower timing nodes, train =>
    TrainingCalibration lower train.1 ∧
    ∀ i (g : Fin 2), g.val < (nodes i).cell.gate.groups →
      ∀ r, r ≤ (nodes i).cell.maxWrites →
        let d := nodes i
        let replay := train.2.1 i g r
        let reads := train.2.2 i
        ReadCalibration lower train.1 (d.stimulus g) replay ∧
        Routed d (pulseDates lower replay) (reads g r) ∧
        AdditiveSlot d.cell (d.cell.writesBefore reads g r) d.cell.trainError timing (reads g r)

abbrev Window := Rat × Rat

def readWindows : (c : Cascade M L N) → ReadTrace c → List Window
  | .input, r => (List.finRange M).filterMap fun i => (r i).map (fun t => (t, t))
  | .layer lower timing _, r =>
    readWindows lower r.1 ++ (List.finRange N).map (fun i =>
      let t := (r.2.1 i).start
      (t, t + timing.duration))

/-- Batches are ordered by layer, cell, group and training round. Within
a batch, dated routing governs the earlier-layer replay and the addressed read. -/
def trainingBatches : (c : Cascade M L N) → TrainingTrace c → List (List Window)
  | .input, _ => []
  | .layer lower timing nodes, train =>
    trainingBatches lower train.1 ++
    (List.finRange N).flatMap fun i =>
      ((List.finRange 2).filter fun g => decide (g.val < (nodes i).cell.gate.groups)).flatMap fun g =>
        (List.range ((nodes i).cell.maxWrites + 1)).map fun r =>
          let start := (train.2.2 i g r).start
          readWindows lower (train.2.1 i g r) ++ [(start, start + timing.duration)]

def BatchBefore (first second : List Window) : Prop :=
  ∀ a ∈ first, ∀ b ∈ second, a.2 ≤ b.1

/-- Replays of separate test patterns are independent at the same trained checkpoint. -/
def TrainingSeparation (c : Cascade M L N) (train : TrainingTrace c)
    (test : Pattern M → ReadTrace c) : Prop :=
  (trainingBatches c train).Pairwise BatchBefore ∧
  ∀ x batch, batch ∈ trainingBatches c train → BatchBefore batch (readWindows c (test x))

def Cascade.Trained : (c : Cascade M L N) → TrainingTrace c → Prop
  | .input, _ => True
  | .layer lower _ nodes, train =>
    lower.Trained train.1 ∧ ∀ i, (nodes i).cell.Trained (train.2.2 i)

/-- Frozen recognition target for an arbitrary number of finite layers. -/
def LayeredMonotoneRecognitionOneSided : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N), c.Valid →
    ∀ (train : TrainingTrace c) (test : Pattern M → ReadTrace c),
      TrainingSeparation c train test →
      TrainingCalibration c train →
      (∀ x, ReadCalibration c train x (test x)) →
      c.Trained train ∧ ∀ x, observed c (test x) = c.predict x

/-- Frozen expressive characterization of admissible binary cascades. -/
def LayeredMonotoneCharacterization : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool), MonotoneFunction f ↔
    ∃ (L N : Nat) (c : Cascade M L N) (i : Fin N), c.Valid ∧ ∀ x, c.predict x i = f x

end LearnedCoincidence.Layered
