import LayeredMonotoneTarget
import MonotonePremiseTargets

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (patterns checkThresholdRead)

namespace Checker

def timing (t : SlotTiming) : Bool :=
  decide (0 ≤ t.skew ∧ 0 < t.deadline ∧ t.skew ≤ t.deadline ∧ t.deadline < t.duration)

def maskEq (x y : Pattern M) : Bool :=
  (List.finRange M).all fun a => x a == y a

def activeGroups (p : Cell) : List (Fin 2) :=
  (List.finRange 2).filter fun g => decide (g.val < p.gate.groups)

def cellValid (p : Cell) : Bool :=
  decide (0 < p.dose) &&
  ((activeGroups p).all fun g =>
    let stop := p.stop g
    decide (0 < stop ∧ stop ≤ p.maxWrites) &&
    ((List.range stop).all fun k => decide (p.groupScore g k + p.trainError < p.threshold)) &&
    decide (p.threshold + p.trainError ≤ p.groupScore g stop)) &&
  ((List.finRange 2).all fun a => decide (p.gain p.expectedWrites a < p.rail)) &&
  (((patterns 2).filter fun x => !p.gate.eval x).all fun x =>
    decide (p.score p.expectedWrites x + p.testError < p.threshold)) &&
  (p.gate.anchors.all fun y => decide (p.threshold + p.testError ≤ p.score p.expectedWrites y))

def nodeValid (d : Node M N) (predict : Pattern M → Pattern N) : Bool :=
  cellValid d.cell &&
  ((List.finRange 2).all fun a =>
    decide ((d.source a).isSome = d.cell.gate.uses a ∧ 0 ≤ d.delay a)) &&
  ((activeGroups d.cell).all fun g => maskEq (d.inputs (predict (d.stimulus g))) (d.cell.gate.groupMask g))

def batchBefore (earlier later : List Window) : Bool :=
  earlier.all fun a => later.all fun b => decide (a.2 ≤ b.1)

def orderedBatches : List (List Window) → Bool
  | [] => true
  | batch :: rest => rest.all (batchBefore batch) && orderedBatches rest

def externalSeparation (c : Cascade M L N) (batches : List (List Window))
    (test : Pattern M → ReadTrace c) : Bool :=
  (patterns M).all fun x => batches.all fun batch => batchBefore batch (readWindows c (test x))

def routed (d : Node M N) (incoming : Fin N → Option Rat) (r : ReadObservation 2) : Bool :=
  (List.finRange 2).all fun a =>
    decide (r.arrival a = ((d.source a).bind incoming).map (fun t => t + d.delay a))

def additiveSlot (p : Cell) (w : Writes) (budget : Nat) (t : SlotTiming)
    (r : ReadObservation 2) : Bool :=
  checkThresholdRead p.threshold t r &&
  (let residual := r.measuredScore - (p.score w r.input : Int)
   decide (-(budget : Int) ≤ residual ∧ residual ≤ budget))

def firingSlot (p : Cell) (w : Writes) (t : SlotTiming)
    (r : ReadObservation 2) (scoreAt : Pattern 2 → Int) : Bool :=
  let measured := scoreAt r.input
  let firingSubmasks := (patterns 2).filter fun y =>
    contains r.input y && decide ((p.threshold : Int) ≤ scoreAt y)
  let anchors := p.gate.anchors.filter fun y => contains r.input y
  checkThresholdRead p.threshold t r &&
  decide (measured = r.measuredScore) &&
  (firingSubmasks.all fun y => decide (scoreAt y ≤ measured)) &&
  (anchors.all fun y => decide ((p.score w y : Int) - p.testError ≤ scoreAt y))

def oneRead : (c : Cascade M L N) → TrainingTrace c → Pattern M → ReadTrace c → Bool
  | .input, _, x, r => maskEq (fun i => (r i).isSome) x
  | .layer lower t nodes, train, x, r =>
    oneRead lower train.1 x r.1 &&
    ((List.finRange N).all fun i =>
      let d := nodes i
      let read := r.2.1 i
      let w := d.cell.settledWrites (train.2.2 i)
      routed d (pulseDates lower r.1) read &&
      if d.cell.gate.eval read.input then firingSlot d.cell w t read (r.2.2 i)
      else additiveSlot d.cell w d.cell.testError t read)

end Checker

def checkLayeredValid : Cascade M L N → Bool
  | .input => true
  | .layer lower t nodes =>
    checkLayeredValid lower && Checker.timing t &&
    ((List.finRange N).all fun i => Checker.nodeValid (nodes i) lower.predict)

def checkLayeredSeparation (c : Cascade M L N) (train : TrainingTrace c)
    (test : Pattern M → ReadTrace c) : Bool :=
  let batches := trainingBatches c train
  Checker.orderedBatches batches && Checker.externalSeparation c batches test

def checkLayeredTrainingCalibration : (c : Cascade M L N) → TrainingTrace c → Bool
  | .input, _ => true
  | .layer lower t nodes, train =>
    checkLayeredTrainingCalibration lower train.1 &&
    ((List.finRange N).all fun i =>
      let d := nodes i
      let reads := train.2.2 i
      (Checker.activeGroups d.cell).all fun g =>
        (List.range (d.cell.maxWrites + 1)).all fun r =>
          let replay := train.2.1 i g r
          Checker.oneRead lower train.1 (d.stimulus g) replay &&
          Checker.routed d (pulseDates lower replay) (reads g r) &&
          Checker.additiveSlot d.cell (d.cell.writesBefore reads g r) d.cell.trainError t (reads g r))

def checkLayeredReadCalibration (c : Cascade M L N) (train : TrainingTrace c)
    (test : Pattern M → ReadTrace c) : Bool :=
  (patterns M).all fun x => Checker.oneRead c train x (test x)

def LayeredValidCheckerSound : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N), checkLayeredValid c = true → c.Valid

def LayeredValidCheckerComplete : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N), c.Valid → checkLayeredValid c = true

def LayeredSeparationCheckerSound : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (train : TrainingTrace c) (test : Pattern M → ReadTrace c),
    checkLayeredSeparation c train test = true → TrainingSeparation c train test

def LayeredSeparationCheckerComplete : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (train : TrainingTrace c) (test : Pattern M → ReadTrace c),
    TrainingSeparation c train test → checkLayeredSeparation c train test = true

def LayeredTrainingCalibrationCheckerSound : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (train : TrainingTrace c),
    checkLayeredTrainingCalibration c train = true → TrainingCalibration c train

def LayeredTrainingCalibrationCheckerComplete : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (train : TrainingTrace c),
    TrainingCalibration c train → checkLayeredTrainingCalibration c train = true

def LayeredReadCalibrationCheckerSound : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (train : TrainingTrace c) (test : Pattern M → ReadTrace c),
    checkLayeredReadCalibration c train test = true → ∀ x, ReadCalibration c train x (test x)

def LayeredReadCalibrationCheckerComplete : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (train : TrainingTrace c) (test : Pattern M → ReadTrace c),
    (∀ x, ReadCalibration c train x (test x)) → checkLayeredReadCalibration c train test = true

end LearnedCoincidence.Layered
