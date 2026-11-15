import Target

/-! Design target for a two-layer cascade. The calibration hypotheses refer
to complete, dated read observations. The memory conclusion is guarded. -/
namespace LearnedCoincidence.TwoLayer

structure Cascade (A B M : Nat) where
  first : Parameters A M
  second : Parameters B A
  delay : Fin B → Fin A → Rat
  heldOut : List (Pattern M)

/-- The smallest external pattern that contains every selected target. -/
def source (p : Cascade A B M) (i : Fin B) : Pattern M :=
  fun j => (List.finRange A).any fun a => p.second.target i a && p.first.target a j

def Cascade.reachable (p : Cascade A B M) : Bool :=
  (List.finRange B).all fun i => (List.finRange A).all fun a =>
    predicted p.first (source p i) a == p.second.target i a

private def same (x y : Pattern M) : Bool := contains x y && contains y x

def Cascade.check (p : Cascade A B M) : Bool :=
  p.first.check && p.second.check && p.reachable &&
    (List.finRange B).all (fun i => (List.finRange A).all fun a => decide (0 ≤ p.delay i a)) &&
    !p.heldOut.isEmpty &&
    p.heldOut.all (fun x => (List.finRange A).all (fun a => !same x (p.first.target a)) &&
      (List.finRange B).all fun i => !same x (source p i))

def Cascade.Valid (p : Cascade A B M) : Prop := p.check = true

instance (p : Cascade A B M) : Decidable p.Valid :=
  inferInstanceAs (Decidable (p.check = true))

structure SlotTiming where
  skew : Rat
  deadline : Rat
  duration : Rat

def SlotTiming.Valid (t : SlotTiming) : Prop :=
  0 ≤ t.skew ∧ 0 < t.deadline ∧ t.skew ≤ t.deadline ∧ t.deadline < t.duration

/-- Extracted from one complete slot. The score is reported in the fixed
integer calibration units of the guarded threshold. -/
structure ReadObservation (M : Nat) where
  start : Rat
  arrival : Fin M → Option Rat
  emissions : List Rat
  measuredScore : Int

def ReadObservation.input (r : ReadObservation M) : Pattern M := fun j => (r.arrival j).isSome

def ReadObservation.fired (r : ReadObservation M) : Bool := !r.emissions.isEmpty

/-- A dated, additive read interface. Emissions cover the *whole* slot.
The decoder and residual refer to the same independently calibrated score.
The error bound is uniform over the specified readings of this cell. -/
def CalibratedAdditiveRead (p : Parameters N M) (i : Fin N) (writes : Nat) (x : Pattern M)
    (budget : Nat) (timing : SlotTiming) (r : ReadObservation M) : Prop :=
  timing.Valid ∧
  r.input = x ∧
  (∀ j t, r.arrival j = some t → r.start ≤ t ∧ t ≤ r.start + timing.skew) ∧
  (match r.emissions with
    | [] => True
    | [t] =>
      r.start ≤ t ∧ t ≤ r.start + timing.deadline ∧
      ∀ j v, r.arrival j = some v → v ≤ t
    | _ => False) ∧
  r.fired = decide ((p.threshold i : Int) ≤ r.measuredScore) ∧
  admissible budget (r.measuredScore - (score p i writes x : Int))

/-- Every arrival is the actual upstream FIRE shifted by its fixed wire delay.
An upstream silence leaves the downstream port inactive. -/
def RoutedBatch (delay : Fin A → Rat) (left : Fin A → ReadObservation M)
    (right : ReadObservation A) : Prop :=
  ∀ a, right.arrival a = ((left a).emissions.head?).map (fun t => t + delay a)

structure Observations (A B M : Nat) where
  firstTrain : Nat → Fin A → ReadObservation M
  /-- Teaching the second layer uses the first layer in read-only mode. -/
  teach : Nat → Fin B → Fin A → ReadObservation M
  secondTrain : Nat → Fin B → ReadObservation A
  firstTest : Pattern M → Fin A → ReadObservation M
  secondTest : Pattern M → Fin B → ReadObservation A

/-- The guarded memory reconstructed from the observed FIREs. -/
def observedCount (trace : Nat → Fin N → ReadObservation M) (i : Fin N) : Nat → Nat
  | 0 => 0
  | r + 1 =>
    if (trace r i).fired then observedCount trace i r else observedCount trace i r + 1

def settledCount (p : Parameters N M) (trace : Nat → Fin N → ReadObservation M) (i : Fin N) : Nat :=
  observedCount trace i (p.maxWrites + 1)

private def teachingEndsBefore (left right : SlotTiming) (o : Observations A B M)
    (r : Nat) (i : Fin B) (time : Rat) : Prop :=
  (∀ a, (o.teach r i a).start + left.duration ≤ time) ∧
  (o.secondTrain r i).start + right.duration ≤ time

/-- Training uses `Q+1` slots in each layer. The second layer's selected
cells are taught in lexicographic order by round and cell. Tests may each
start from the same completed training checkpoint. -/
def TrainingSeparation (p : Cascade A B M) (left right : SlotTiming)
    (o : Observations A B M) : Prop :=
  (∀ r, r < p.first.maxWrites → ∀ a b,
    (o.firstTrain r a).start + left.duration ≤ (o.firstTrain (r + 1) b).start) ∧
  (∀ r, r ≤ p.second.maxWrites → ∀ i a,
    (∀ b, (o.firstTrain p.first.maxWrites b).start + left.duration ≤ (o.teach r i a).start) ∧
    (o.firstTrain p.first.maxWrites a).start + left.duration ≤ (o.secondTrain r i).start) ∧
  (∀ r s, r ≤ p.second.maxWrites → s ≤ p.second.maxWrites → ∀ i j : Fin B,
    r * B + i.val < s * B + j.val →
    (∀ a, teachingEndsBefore left right o r i (o.teach s j a).start) ∧
    teachingEndsBefore left right o r i (o.secondTrain s j).start) ∧
  ∀ x r, r ≤ p.second.maxWrites → ∀ i,
    (∀ a, teachingEndsBefore left right o r i (o.firstTest x a).start) ∧
    ∀ j, teachingEndsBefore left right o r i (o.secondTest x j).start

/-- The bridge premise applies to each reading in its mode and at the
guarded state reconstructed from the emitted word. -/
def CascadeCalibration (p : Cascade A B M) (firstTiming secondTiming : SlotTiming)
    (o : Observations A B M) : Prop :=
  (∀ r, r ≤ p.first.maxWrites → ∀ a, CalibratedAdditiveRead p.first a (observedCount o.firstTrain a r) (p.first.target a)
    (p.first.trainingError a) firstTiming (o.firstTrain r a)) ∧
  (∀ r, r ≤ p.second.maxWrites → ∀ i a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a) (source p i)
    (p.first.testingError a) firstTiming (o.teach r i a)) ∧
  (∀ r, r ≤ p.second.maxWrites → ∀ i, RoutedBatch (p.delay i) (o.teach r i) (o.secondTrain r i) ∧
    CalibratedAdditiveRead p.second i (observedCount o.secondTrain i r) (o.secondTrain r i).input
      (p.second.trainingError i) secondTiming (o.secondTrain r i)) ∧
  (∀ x a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a) x
    (p.first.testingError a) firstTiming (o.firstTest x a)) ∧
  (∀ x i, RoutedBatch (p.delay i) (o.firstTest x) (o.secondTest x i) ∧
    CalibratedAdditiveRead p.second i (settledCount p.second o.secondTrain i) (o.secondTest x i).input
      (p.second.testingError i) secondTiming (o.secondTest x i))

def LearningCertificate (p : Parameters N M) (trace : Nat → Fin N → ReadObservation M) : Prop :=
  (∀ r, r ≤ p.maxWrites + 1 → ∀ i, observedCount trace i r = min r (need p i)) ∧
  (∀ r, r ≤ p.maxWrites → ∀ i, (trace r i).fired = decide (need p i ≤ r)) ∧
  ∀ r, r ≤ p.maxWrites + 1 → ∀ i j, portWrites p i j (observedCount trace i r) ≤ p.maxWrites ∧
    gain p i (observedCount trace i r) j < p.rail

/-- The frozen two-layer target. Calibration is an explicit premise, and
routing is checked from observed dates rather than supplied masks. -/
def TwoLayerCoincidenceRecognition : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M), p.Valid →
    ∀ (firstTiming secondTiming : SlotTiming) (o : Observations A B M),
      TrainingSeparation p firstTiming secondTiming o →
      CascadeCalibration p firstTiming secondTiming o →
      LearningCertificate p.first o.firstTrain ∧
      (∀ r, r ≤ p.second.maxWrites → ∀ i, (o.secondTrain r i).input = p.second.target i) ∧
      LearningCertificate p.second o.secondTrain ∧
      ∀ x i, (o.secondTest x i).fired = contains x (source p i)

private def firstPilot : Parameters 3 4 where
  target i := if i = 0 then pattern [0, 1] else if i = 1 then pattern [0, 2] else pattern [0, 3]
  tests := [pattern [0], pattern [1], pattern [2], pattern [3], pattern [1, 2], pattern [0, 1, 2, 3]]
  initialGain := fun _ _ => 0
  help := fun _ => 0
  threshold := fun _ => 6
  trainingError := fun _ => 1
  testingError := fun _ => 1
  dose := 4
  maxWrites := 1
  rail := 5

private def secondPilot : Parameters 2 3 where
  target i := if i = 0 then pattern [0, 1] else pattern [1, 2]
  tests := [pattern [0], pattern [1], pattern [2], pattern [0, 2], pattern [0, 1, 2]]
  initialGain := fun _ _ => 0
  help := fun _ => 0
  threshold := fun _ => 6
  trainingError := fun _ => 1
  testingError := fun _ => 1
  dose := 4
  maxWrites := 1
  rail := 5

private def pilot : Cascade 3 2 4 :=
  ⟨firstPilot, secondPilot, fun _ _ => 0,
    [pattern [0], pattern [1, 2], pattern [0, 1, 3], pattern [0, 1, 2, 3]]⟩

example : pilot.Valid ∧
    (List.finRange 2).map (fun i => contains (pattern [0, 1, 2, 3]) (source pilot i)) =
      [true, true] := by decide +kernel

/-- With the triangle of first-layer targets, the union needed to fire
the first two detectors fires the third too. -/
example : ({pilot with first := {pilot.first with
    target := fun i => if i = 0 then pattern [0, 1] else if i = 1 then pattern [1, 2]
      else pattern [0, 2] }}).reachable = false := by decide +kernel

end LearnedCoincidence.TwoLayer
