import LayeredMonotoneExample
import LayeredMonotoneCheckerTargets

namespace LearnedCoincidence.Layered.CheckerBench

open MonotoneDNF (singleton)

/-- A reproducible trace family for measuring kernel work separately by checker. -/
structure Fixture (M L : Nat) where
  circuit : Cascade M L 1
  train : TrainingTrace circuit
  replay : Rat → Pattern M → ReadTrace circuit
  nextBatch : Nat
  signal : Pattern M → Bool

def Fixture.test (f : Fixture M L) (x : Pattern M) : ReadTrace f.circuit :=
  f.replay f.nextBatch x

private def copyNode (port : Fin N) : Node M N :=
  ⟨canonical .copy, fun a => if a = 0 then some port else none, fun _ => 0, fun _ _ => true⟩

private def copyRead (start : Rat) (fire : Bool) :=
  Example.slot start (fun a => decide (a = 0) && fire) (if fire then 4 else 0) fire

private def copyTrainingRead (start : Rat) (round : Nat) :=
  Example.slot start (singleton 0) (if round = 0 then 0 else 4) (decide (round ≠ 0))

private def copyScores (_ : Fin 1) (x : Pattern 2) : Int := if x 0 then 4 else 0

private def Fixture.appendCopy (f : Fixture M L) : Fixture M (L + 1) where
  circuit := .layer f.circuit Example.clock fun _ => copyNode 0
  train :=
    ⟨f.train, fun _ _ r => f.replay (f.nextBatch + 20 * r : Nat) (fun _ => true),
      fun _ _ r => copyTrainingRead ((f.nextBatch + 20 * r : Nat) + (L : Rat)) r⟩
  replay := fun t x => ⟨f.replay t x, fun _ => copyRead (t + (L : Rat)) (f.signal x), copyScores⟩
  nextBatch := f.nextBatch + 40
  signal := f.signal

/-- At depth three, the saturated regression fixture. Additional layers are
trained copies of the last signal, so depths five and seven still use four inputs. -/
def depth : (extra : Nat) → Fixture 4 (3 + extra)
  | 0 =>
    ⟨Example.circuit, Example.train, Example.replay, 120,
      fun x => (x 0 && x 1) || (x 2 && x 3)⟩
  | extra + 1 => (depth extra).appendCopy

private def copySeed (extra : Nat) : Fixture (extra + 1) 1 where
  circuit := .layer .input Example.clock fun _ => copyNode 0
  train :=
    ⟨(), fun _ _ r _ => some (20 * r : Nat),
      fun _ _ r => copyTrainingRead (20 * r : Nat) r⟩
  replay := fun t x =>
    ⟨fun i => if x i then some t else none, fun _ => copyRead t (x 0), copyScores⟩
  nextBatch := 40
  signal := fun x => x 0

/-- Three trained copies with extra physically present but unconnected inputs.
This isolates external cube growth at a fixed depth and downstream width. -/
def width (extra : Nat) : Fixture (extra + 1) 3 :=
  ((copySeed extra).appendCopy).appendCopy

end LearnedCoincidence.Layered.CheckerBench
