import LayeredCompositionTarget
import InverterTarget

/-! Inverters in front of the layered cascade: definitions and frozen targets only.
`M` inverters and `M` direct rails, delayed by `emitEarly`, feed a layered cascade on `2 M`
lines. The front end is that of `InverterTarget.lean`, unchanged. Here it supplies the
external level of the layered read trace. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF (InverterTiming InverterRead frontArrival rails)

/-- The front end of one test read. Every inverter starts at `start`, hears its input and
obeys the inverter law. The cascade's external arrivals are the delayed direct rails and
the inverter pulses. -/
def LayeredFront (t : InverterTiming) (start : Rat) (external : Fin M → Option Rat)
    (inv : Fin M → ReadObservation 1) (c : Cascade (M + M) L N) (test : ReadTrace c) : Prop :=
  (∀ j, (inv j).start = start ∧ (inv j).arrival 0 = external j ∧ InverterRead t (inv j)) ∧
  inputTrace c test = frontArrival t.emitEarly external inv

/-- Frozen target: for ANY admissible layered cascade on `2 M` lines, read through the
front end at `y`, the decisions are the cascade's prediction on the rails of `y`. The
cascade's own reads keep their assumed arrival windows. -/
def LayeredInvertersCompute : Prop :=
  ∀ (M L N : Nat) (c : Cascade (M + M) L N), c.Valid →
    ∀ (train : TrainingTrace c), TrainingCalibration c train →
      ∀ (t : InverterTiming) (start : Rat) (external : Fin M → Option Rat)
        (inv : Fin M → ReadObservation 1) (y : Pattern M) (test : ReadTrace c),
        (∀ j, (external j).isSome = y j) → LayeredFront t start external inv c test →
        LayerReads c train test → ArrivalWindows c test →
        observed c test = c.predict (rails y)

/-- Frozen chained target. The front end is layer 0 of the chain: it starts at
`s 0 = start + emitEarly` and has width `w`, which bounds both the inverter input window
and the inverter emission spread. No arrival window is assumed. -/
def LayeredInvertersChained : Prop :=
  ∀ (M L N : Nat) (c : Cascade (M + M) L N), c.Valid →
    ∀ (train : TrainingTrace c), TrainingCalibration c train →
      ∀ (t : InverterTiming) (start : Rat) (external : Fin M → Option Rat)
        (inv : Fin M → ReadObservation 1) (y : Pattern M) (test : ReadTrace c)
        (s lmin lmax : Nat → Rat) (w : Rat),
        s 0 = start + t.emitEarly → t.window ≤ w → t.emitLate - t.emitEarly ≤ w →
        ChainDates s (latencyLow lmin) (latencyHigh w lmax) c →
        (∀ j, (external j).isSome = y j) → LayeredFront t start external inv c test →
        LayerReads c train test → Scheduled s c test → Latencies lmin lmax c test →
        ArrivalWindows c test ∧ observed c test = c.predict (rails y)

/-- Frozen target: every Boolean function is computed by some admissible layered cascade
read through the inverter front end. -/
def EveryFunctionLayeredWithInverters : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool),
    ∃ (L N : Nat) (c : Cascade (M + M) L N) (i : Fin N), c.Valid ∧
      ∀ (train : TrainingTrace c), TrainingCalibration c train →
        ∀ (t : InverterTiming) (start : Rat) (external : Fin M → Option Rat)
          (inv : Fin M → ReadObservation 1) (y : Pattern M) (test : ReadTrace c),
          (∀ j, (external j).isSome = y j) → LayeredFront t start external inv c test →
          LayerReads c train test → ArrivalWindows c test →
          observed c test i = f y

end LearnedCoincidence.Layered
