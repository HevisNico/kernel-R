import LayeredInverters
import LayeredChainChecks

/-! Support for the witnesses.

- `simulate` and `simTrain` build test and training traces from the additive model. Every
  read starts on its schedule and emits one unit after its start exactly when the model
  fires. Its measured score is the model score at the predicted writes.
- These are trace constructors only. Every premise is then checked on the resulting traces
  by the repository's checkers and by the chain checkers, all reduced by the kernel. The
  constructors carry no proof obligation.
- `checkLayeredFront` is a sound checker for the inverter front end. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF (InverterTiming InverterRead frontArrival)

/-- External pulses at date `t` on the lines of `x`. -/
def externalAt (t : Rat) (x : Pattern M) : Fin M → Option Rat := fun j => if x j then some t else none

/-- Layer 0 at `T`, layer `k ≥ 1` at `T + (k - 1)`. -/
def stepSchedule (T : Rat) : Nat → Rat := fun k => if k = 0 then T else T + ((k - 1 : Nat) : Rat)

def routedArrivals (d : Node M N) (pulses : Fin N → Option Rat) : Fin 2 → Option Rat :=
  fun a => ((d.source a).bind pulses).map (· + d.delay a)

def simulate (s : Nat → Rat) : (c : Cascade M L N) → (Fin M → Option Rat) → ReadTrace c
  | .input, ext => ext
  | .layer (L := L) lower _ nodes, ext =>
    let low := simulate s lower ext
    ⟨low, fun i =>
      let d := nodes i
      let arr := routedArrivals d (pulseDates lower low)
      let x : Pattern 2 := fun a => (arr a).isSome
      ⟨s (L + 1), arr, if d.cell.gate.eval x then [s (L + 1) + 1] else [],
        (d.cell.score d.cell.expectedWrites x : Int)⟩,
     fun i y => ((nodes i).cell.score (nodes i).cell.expectedWrites y : Int)⟩

/-- The writes before round `r` of group `g` predicted by the guarded model. -/
def predictedWrites (p : Cell) (g : Fin 2) (r : Nat) : Writes := fun a =>
  (if g = 0 then 0 else p.groupWrites 0 (p.stop 0) a) + p.groupWrites g (min r (p.stop g)) a

/-- A lesson base date, increasing in (layer, cell, group, round). -/
def lessonBase (ℓ i g r : Nat) : Rat := ((1000 * ℓ + 100 * i + 30 * g + 5 * r : Nat) : Rat)

def witnessClock : LessonClock := fun ℓ i g r => stepSchedule (lessonBase ℓ i g r)

def simTrain : (c : Cascade M L N) → TrainingTrace c
  | .input => ()
  | .layer (L := L) lower _ nodes =>
    ⟨simTrain lower,
     fun i g r =>
      let s := witnessClock (L + 1) i.val g.val r
      simulate s lower (externalAt (s 0) ((nodes i).stimulus g)),
     fun i g r =>
      let d := nodes i
      let s := witnessClock (L + 1) i.val g.val r
      let replay := simulate s lower (externalAt (s 0) (d.stimulus g))
      let arr := routedArrivals d (pulseDates lower replay)
      let x : Pattern 2 := fun a => (arr a).isSome
      let score : Nat := d.cell.score (predictedWrites d.cell g r) x
      ⟨s (L + 1), arr, if decide (d.cell.threshold ≤ score) then [s (L + 1) + 1] else [],
        (score : Int)⟩⟩

def checkInverterRead (t : InverterTiming) (r : ReadObservation 1) : Bool :=
  decide (0 ≤ t.window ∧ t.window ≤ t.emitEarly ∧ t.emitEarly < t.emitLate) &&
  (match r.arrival 0 with
    | none => true
    | some v => decide (r.start ≤ v ∧ v ≤ r.start + t.window)) &&
  (match r.emissions with
    | [] => true
    | [e] => decide (r.start + t.emitEarly < e ∧ e ≤ r.start + t.emitLate)
    | _ => false) &&
  (r.fired == !r.input 0)

def checkLayeredFront (t : InverterTiming) (start : Rat) (external : Fin M → Option Rat)
    (inv : Fin M → ReadObservation 1) (c : Cascade (M + M) L N) (test : ReadTrace c) : Bool :=
  ((List.finRange M).all fun j =>
    decide ((inv j).start = start) && decide ((inv j).arrival 0 = external j) &&
      checkInverterRead t (inv j)) &&
  (List.finRange (M + M)).all fun j => decide (inputTrace c test j = frontArrival t.emitEarly external inv j)

private theorem all_fin {n : Nat} {P : Fin n → Bool} :
    (List.finRange n).all P = true ↔ ∀ i, P i = true := by
  simp [List.all_eq_true]

theorem inverter_read_checker_sound {t : InverterTiming} {r : ReadObservation 1}
    (h : checkInverterRead t r = true) : InverterRead t r := by
  simp only [checkInverterRead, Bool.and_eq_true] at h
  obtain ⟨⟨⟨valid, window⟩, emission⟩, decision⟩ := h
  refine ⟨(of_decide_eq_true valid : 0 ≤ t.window ∧ t.window ≤ t.emitEarly ∧ t.emitEarly < t.emitLate), fun v arrived => ?_, ?_, ?_⟩
  · rw [arrived] at window
    exact of_decide_eq_true window
  · match e : r.emissions, emission with
    | [], _ => trivial
    | [u], ok => exact of_decide_eq_true (by simpa [e] using ok)
    | _ :: _ :: _, bad => simp at bad
  · simpa using decision

theorem layered_front_checker_sound {t : InverterTiming} {start : Rat}
    {external : Fin M → Option Rat} {inv : Fin M → ReadObservation 1} {c : Cascade (M + M) L N}
    {test : ReadTrace c} (h : checkLayeredFront t start external inv c test = true) :
    LayeredFront t start external inv c test := by
  simp only [checkLayeredFront, Bool.and_eq_true] at h
  refine ⟨fun j => ?_, funext fun j => of_decide_eq_true (all_fin.mp h.2 j)⟩
  have cell := all_fin.mp h.1 j
  simp only [Bool.and_eq_true] at cell
  exact ⟨of_decide_eq_true cell.1.1, of_decide_eq_true cell.1.2, inverter_read_checker_sound cell.2⟩

/-- The inverter of the witnesses: input window 1/4, emission in (1/2, 3/4]. -/
def witnessInverter : InverterTiming := ⟨1 / 4, 1 / 2, 3 / 4⟩

/-- External pulses at `T0`. The inverters start at `T0` and fire at `T0 + 5/8` when their
input is absent. -/
def T0 : Rat := 10000

def frontExternal (y : Pattern M) : Fin M → Option Rat := externalAt T0 y

def frontInverters (y : Pattern M) : Fin M → ReadObservation 1 := fun j =>
  ⟨T0, fun _ => frontExternal y j, if y j then [] else [T0 + 5 / 8], 0⟩

/-- The line arrivals of the front end for any line pattern: direct rails at
`T0 + 1/2` and complement rails at `T0 + 5/8`. On the rails of `y` this is the front end. -/
def lineArrivals (x : Pattern (M + M)) : Fin (M + M) → Option Rat := fun j =>
  if x j then some (if j.val < M then T0 + 1 / 2 else T0 + 5 / 8) else none

end LearnedCoincidence.Layered
