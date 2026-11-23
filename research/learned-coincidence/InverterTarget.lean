import MonotoneOneSidedTarget
import TwoRailsTarget

/-! The abstract inverter and its composition with the monotone cascade. An
inverter has one input line. It fires, late, exactly when its input is absent.
M inverters in front of a cascade on 2 M lines supply the complement rails; the
direct rails are delayed so that both kinds of pulse fall within one read window.
This file holds definitions and the frozen target only. -/

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch settledCount)

/-- Dates of one inverter slot, relative to its start. The input may arrive in
`[start, start + window]`. An emission, if any, falls in
`(start + emitEarly, start + emitLate]`. -/
structure InverterTiming where
  window : Rat
  emitEarly : Rat
  emitLate : Rat

/-- The inverter decides only after its input window: `window ≤ emitEarly`. -/
def InverterTiming.Valid (t : InverterTiming) : Prop :=
  0 ≤ t.window ∧ t.window ≤ t.emitEarly ∧ t.emitEarly < t.emitLate

/-- The projected inverter law, on one input line: the input arrives within the
window, there is at most one emission, it is late, and the cell fires exactly when
its input is absent. -/
def InverterRead (t : InverterTiming) (r : ReadObservation 1) : Prop :=
  t.Valid ∧
  (∀ v, r.arrival 0 = some v → r.start ≤ v ∧ v ≤ r.start + t.window) ∧
  (match r.emissions with
    | [] => True
    | [e] => r.start + t.emitEarly < e ∧ e ≤ r.start + t.emitLate
    | _ => False) ∧
  r.fired = !r.input 0

/-- The 2 M lines made from M external arrivals: line `j` is input `j` delayed by
`lag`; line `M + j` is the emission of inverter `j`. -/
def frontArrival {M : Nat} (lag : Rat) (external : Fin M → Option Rat)
    (inv : Fin M → ReadObservation 1) : Fin (M + M) → Option Rat := fun j =>
  if h : j.val < M then (external ⟨j.val, h⟩).map (· + lag)
  else (inv ⟨j.val - M, by omega⟩).emissions.head?

/-- One first-layer read fed by the front end. Inverter `j` hears input `j` from
`start`; the direct rails are delayed by `emitEarly`, and the read starts then. -/
def FrontEnd {M : Nat} (t : InverterTiming) (start : Rat) (external : Fin M → Option Rat)
    (inv : Fin M → ReadObservation 1) (read : ReadObservation (M + M)) : Prop :=
  (∀ j, (inv j).start = start ∧ (inv j).arrival 0 = external j ∧ InverterRead t (inv j)) ∧
  read.start = start + t.emitEarly ∧
  read.arrival = frontArrival t.emitEarly external inv

/-- The clauses of `CalibratedAdditiveRead` other than the input mask and the
arrival window, which the front end supplies. -/
def ReadAfterFront (p : Parameters N M) (i : Fin N) (writes : Nat) (x : Pattern M)
    (budget : Nat) (timing : SlotTiming) (r : ReadObservation M) : Prop :=
  timing.Valid ∧
  (match r.emissions with
    | [] => True
    | [t] =>
      r.start ≤ t ∧ t ≤ r.start + timing.deadline ∧
      ∀ j v, r.arrival j = some v → v ≤ t
    | _ => False) ∧
  r.fired = decide ((p.threshold i : Int) ≤ r.measuredScore) ∧
  admissible budget (r.measuredScore - (score p i writes x : Int))

/-- The second-layer test premise of `CascadeCalibrationOneSided`, at one
pattern `x` and one output `i`. -/
def SecondTestRead (p : Cascade A B M) (secondTiming : SlotTiming) (o : Observations A B M)
    (scores : Pattern M → Fin B → Pattern A → Int) (x : Pattern M) (i : Fin B) : Prop :=
  RoutedBatch (p.delay i) (o.firstTest x) (o.secondTest x i) ∧
    let r := o.secondTest x i
    let w := lessonCounts p o (lessons p).length
    if p.second.alwaysFire i || (List.finRange A).any (fun a => p.second.lines i a && r.input a) then
      FiringMaskRead p.second w i secondTiming r (scores x i)
    else
      CalibratedAdditiveRead (readView p.second w) i 0 r.input
        (p.second.testingError i) secondTiming r

/-- The first-layer test premise for the input pattern `y`, read through the
inverter front end: every first-layer read of the replay at `rails y` is
produced by the front end and meets the remaining calibrated clauses. -/
def InverterFrontRead (p : Cascade A B (M + M)) (t : InverterTiming) (firstTiming : SlotTiming)
    (o : Observations A B (M + M)) (y : Pattern M) (start : Rat)
    (external : Fin M → Option Rat) (inv : Fin M → ReadObservation 1) : Prop :=
  ∀ a, FrontEnd t start external inv (o.firstTest (rails y) a) ∧
    ReadAfterFront p.first a (settledCount p.first o.firstTrain a) (rails y)
      (p.first.testingError a) firstTiming (o.firstTest (rails y) a)

/-- Frozen target. For every Boolean function `f` of `M` inputs there is an
admissible cascade on `2 M` lines whose output, read through `M` inverters and
`M` delayed direct rails, is `f`. The premises are the training calibration of
the cascade, the front-end law at the tested input pattern, the second-layer read
at that pattern, and two checkable date inequalities. -/
def EveryFunctionWithInverters : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool),
    ∃ (A B : Nat) (p : Cascade A B (M + M)) (i : Fin B), p.Valid ∧
      ∀ (t : InverterTiming) (firstTiming secondTiming : SlotTiming)
        (o : Observations A B (M + M)) (scores : Pattern (M + M) → Fin B → Pattern A → Int),
        t.window ≤ firstTiming.skew → t.emitLate - t.emitEarly ≤ firstTiming.skew →
        CascadeTrainingCalibration p firstTiming secondTiming o →
        ∀ (y : Pattern M) (start : Rat) (external : Fin M → Option Rat)
          (inv : Fin M → ReadObservation 1),
          (∀ j, (external j).isSome = y j) →
          InverterFrontRead p t firstTiming o y start external inv →
          (∀ k, SecondTestRead p secondTiming o scores (rails y) k) →
          (o.secondTest (rails y) i).fired = f y

end LearnedCoincidence.MonotoneDNF
