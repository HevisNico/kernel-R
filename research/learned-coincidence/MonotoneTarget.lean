import TwoLayerTarget

/-! Phase 0 for monotone DNF. The first layer trains nonempty conjunctions.
The second trains one upstream line at a time from the actual arrivals. -/
namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch
  observedCount settledCount LearningCertificate)

structure Disjunctions (B A : Nat) where
  lines : Fin B → Pattern A
  alwaysFire : Fin B → Bool
  initialGain : Fin B → Fin A → Nat
  help : Fin B → Nat
  threshold : Fin B → Nat
  trainingError : Fin B → Nat
  testingError : Fin B → Nat
  dose : Nat
  maxWrites : Nat
  rail : Nat

abbrev Counts (B A : Nat) := Fin B → Fin A → Nat

def lineGain (p : Disjunctions B A) (i : Fin B) (a : Fin A) (k : Nat) : Nat :=
  p.initialGain i a + p.dose * k

def singleton (a : Fin A) : Pattern A := fun b => decide (b = a)

def lineScore (p : Disjunctions B A) (i : Fin B) (a : Fin A) (k : Nat) : Nat :=
  p.help i + lineGain p i a k

def lineNeed (p : Disjunctions B A) (i : Fin B) (a : Fin A) : Nat :=
  ((List.range (p.maxWrites + 1)).find? fun k =>
    decide (p.threshold i ≤ lineScore p i a k)).getD (p.maxWrites + 1)

/-- Every inactive training line has zero writes in the predicted state. -/
def expectedWrites (p : Disjunctions B A) (i : Fin B) (a : Fin A) : Nat :=
  if p.lines i a then lineNeed p i a else 0

/-- A read-only view at the actual port counts. The calibrated score uses
this view at index zero, so it reuses the existing additive bridge. -/
def readView (p : Disjunctions B A) (writes : Counts B A) : Parameters B A where
  target := p.lines
  tests := []
  initialGain := fun i a => lineGain p i a (writes i a)
  help := p.help
  threshold := p.threshold
  trainingError := p.trainingError
  testingError := p.testingError
  dose := p.dose
  maxWrites := p.maxWrites
  rail := p.rail

private def lineCheck (p : Disjunctions B A) (i : Fin B) (a : Fin A) : Bool :=
  let k := lineNeed p i a
  decide (0 < k ∧ k ≤ p.maxWrites) &&
    (List.range k).all (fun n => robustSilence (p.threshold i) (p.trainingError i) (lineScore p i a n)) &&
    robustFire (p.threshold i) (p.trainingError i) (lineScore p i a k) &&
    robustFire (p.threshold i) (p.testingError i) (lineScore p i a k)

def Disjunctions.check (p : Disjunctions B A) : Bool :=
  decide (0 < p.dose) && (List.finRange B).all fun i =>
    (List.finRange A).all (fun a => decide (lineGain p i a (expectedWrites p i a) < p.rail)) &&
    if p.alwaysFire i then
      !(List.finRange A).any (p.lines i) && robustFire (p.threshold i) (p.testingError i) (p.help i)
    else
      (List.finRange A).all (fun a => !p.lines i a || lineCheck p i a) &&
      robustSilence (p.threshold i) (p.testingError i)
        (score (readView p (expectedWrites p)) i 0 (fun a => !p.lines i a))

structure Cascade (A B M : Nat) where
  first : Parameters A M
  second : Disjunctions B A
  delay : Fin B → Fin A → Rat
  heldOut : List (Pattern M)

/-- Unary conjunctions are needed for universality. The original joint-only
checker stays unchanged. The held-out suite belongs to the cascade. -/
def checkConjunctions (p : Parameters A M) : Bool :=
  decide (0 < p.dose) &&
    (List.finRange A).all (fun a => decide (0 < card (p.target a))) &&
    p.earlySilence && p.stops && p.belowRail && p.positiveMargin && p.negativeMargin

/-- The line's own target is the smallest external pattern that can fire it.
Demand silence of every other upstream cell on that pattern. -/
def Cascade.reachable (p : Cascade A B M) : Bool :=
  (List.finRange A).all fun a =>
    !(List.finRange B).any (fun i => p.second.lines i a) ||
    (List.finRange A).all fun b => predicted p.first (p.first.target a) b == singleton a b

def Cascade.check (p : Cascade A B M) : Bool :=
  checkConjunctions p.first && p.second.check && p.reachable &&
    (List.finRange B).all (fun i => (List.finRange A).all fun a => decide (0 ≤ p.delay i a)) &&
    p.heldOut.all (fun x => (List.finRange A).all fun a =>
      !(contains x (p.first.target a) && contains (p.first.target a) x))

def Cascade.Valid (p : Cascade A B M) : Prop := p.check = true

instance (p : Cascade A B M) : Decidable p.Valid :=
  inferInstanceAs (Decidable (p.check = true))

def output (p : Cascade A B M) (i : Fin B) (x : Pattern M) : Bool :=
  p.second.alwaysFire i ||
  (List.finRange A).any fun a => p.second.lines i a && predicted p.first x a

structure Lesson (A B : Nat) where
  cell : Fin B
  line : Fin A

/-- For each round, serialize the selected (cell, line) pairs. This
schedule specifies external stimuli; it does not create downstream pulses. -/
def lessons (p : Cascade A B M) : List (Lesson A B) :=
  (List.range (p.second.maxWrites + 1)).flatMap fun _ =>
    (List.finRange B).flatMap fun i =>
      ((List.finRange A).filter (p.second.lines i)).map fun a => ⟨i, a⟩

structure Observations (A B M : Nat) where
  firstTrain : Nat → Fin A → ReadObservation M
  teach : Nat → Fin A → ReadObservation M
  secondTrain : Nat → ReadObservation A
  firstTest : Pattern M → Fin A → ReadObservation M
  secondTest : Pattern M → Fin B → ReadObservation A

/-- Model the actual update: only at the addressed learner, on silence,
and only at ports that really arrived. -/
def advance (writes : Counts B A) (i : Fin B) (r : ReadObservation A) : Counts B A :=
  fun j a => writes j a + if j = i ∧ r.fired = false ∧ r.input a = true then 1 else 0

def lessonCounts (p : Cascade A B M) (o : Observations A B M) : Nat → Counts B A
  | 0 => fun _ _ => 0
  | n + 1 => match (lessons p)[n]? with
    | none => lessonCounts p o n
    | some L => advance (lessonCounts p o n) L.cell (o.secondTrain n)

def attempts (p : Cascade A B M) (n : Nat) (i : Fin B) (a : Fin A) : Nat :=
  (((lessons p).take n).filter fun L => decide (L.cell = i ∧ L.line = a)).length

private def endsBefore (firstTiming secondTiming : SlotTiming) (o : Observations A B M)
    (n : Nat) (time : Rat) : Prop :=
  (∀ a, (o.teach n a).start + firstTiming.duration ≤ time) ∧
    (o.secondTrain n).start + secondTiming.duration ≤ time

/-- Separate slots through settlement. Tests can replay the completed
checkpoint independently for each external pattern. -/
def TrainingSeparation (p : Cascade A B M) (firstTiming secondTiming : SlotTiming)
    (o : Observations A B M) : Prop :=
  (∀ r, r < p.first.maxWrites → ∀ a b,
    (o.firstTrain r a).start + firstTiming.duration ≤ (o.firstTrain (r + 1) b).start) ∧
  (∀ n, n < (lessons p).length → ∀ a,
    (∀ b, (o.firstTrain p.first.maxWrites a).start + firstTiming.duration ≤ (o.teach n b).start) ∧
    (o.firstTrain p.first.maxWrites a).start + firstTiming.duration ≤ (o.secondTrain n).start) ∧
  (∀ n s, n < s → s < (lessons p).length →
    (∀ a, endsBefore firstTiming secondTiming o n (o.teach s a).start) ∧
    endsBefore firstTiming secondTiming o n (o.secondTrain s).start) ∧
  (∀ x a, (∀ b, (o.firstTrain p.first.maxWrites a).start + firstTiming.duration ≤ (o.firstTest x b).start) ∧
    ∀ i, (o.firstTrain p.first.maxWrites a).start + firstTiming.duration ≤ (o.secondTest x i).start) ∧
  ∀ x n, n < (lessons p).length →
    (∀ a, endsBefore firstTiming secondTiming o n (o.firstTest x a).start) ∧
    ∀ i, endsBefore firstTiming secondTiming o n (o.secondTest x i).start

/-- The existing threshold, skew and residual premise applies at the
memory reconstructed from actual decisions and arrivals in each slot. -/
def CascadeCalibration (p : Cascade A B M) (firstTiming secondTiming : SlotTiming)
    (o : Observations A B M) : Prop :=
  (∀ r, r ≤ p.first.maxWrites → ∀ a,
    CalibratedAdditiveRead p.first a (observedCount o.firstTrain a r) (p.first.target a)
      (p.first.trainingError a) firstTiming (o.firstTrain r a)) ∧
  (∀ n L, (lessons p)[n]? = some L →
    (∀ a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a) (p.first.target L.line)
      (p.first.testingError a) firstTiming (o.teach n a)) ∧
    RoutedBatch (p.delay L.cell) (o.teach n) (o.secondTrain n) ∧
    CalibratedAdditiveRead (readView p.second (lessonCounts p o n)) L.cell 0 (o.secondTrain n).input
      (p.second.trainingError L.cell) secondTiming (o.secondTrain n)) ∧
  (∀ x a, CalibratedAdditiveRead p.first a (settledCount p.first o.firstTrain a) x
    (p.first.testingError a) firstTiming (o.firstTest x a)) ∧
  ∀ x i, RoutedBatch (p.delay i) (o.firstTest x) (o.secondTest x i) ∧
    CalibratedAdditiveRead (readView p.second (lessonCounts p o (lessons p).length)) i 0
      (o.secondTest x i).input (p.second.testingError i) secondTiming (o.secondTest x i)

/-- Frozen trace target. Its conclusions describe guarded memory, given
complete observations satisfying the calibrated additive interface. -/
def TwoLayerMonotoneRecognition : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M), p.Valid →
    ∀ (firstTiming secondTiming : SlotTiming) (o : Observations A B M),
      TrainingSeparation p firstTiming secondTiming o →
      CascadeCalibration p firstTiming secondTiming o →
      LearningCertificate p.first o.firstTrain ∧
      (∀ n L, (lessons p)[n]? = some L →
        (o.secondTrain n).input = singleton L.line ∧
        (o.secondTrain n).fired =
          decide (lineNeed p.second L.cell L.line ≤ attempts p n L.cell L.line)) ∧
      (∀ n, n ≤ (lessons p).length → ∀ i a,
        lessonCounts p o n i a = min (attempts p n i a) (expectedWrites p.second i a) ∧
        lessonCounts p o n i a ≤ p.second.maxWrites ∧
        lineGain p.second i a (lessonCounts p o n i a) < p.second.rail) ∧
      (∀ i a, lessonCounts p o (lessons p).length i a = expectedWrites p.second i a) ∧
      ∀ x i, (o.secondTest x i).fired = output p i x

def MonotoneFunction (f : Pattern M → Bool) : Prop :=
  ∀ x y, contains y x = true → f x = true → f y = true

/-- Expressive completeness of the admissible guarded parameter class. -/
def MonotoneCharacterization : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool), MonotoneFunction f ↔
    ∃ (A B : Nat) (p : Cascade A B M) (i : Fin B), p.Valid ∧ ∀ x, output p i x = f x

private def cube (M : Nat) : List (Pattern M) :=
  (List.range (2 ^ M)).map fun word j => word.testBit j.val

private def fromTerms (terms : Fin A → Pattern M) : Cascade A 1 M where
  first := {
    target := terms, tests := [], initialGain := fun _ _ => 0, help := fun _ => 0
    threshold := fun a => 4 * card (terms a) - 2
    trainingError := fun _ => 1, testingError := fun _ => 1, dose := 4, maxWrites := 1, rail := 5
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false
    initialGain := fun _ _ => 0, help := fun _ => 0, threshold := fun _ => 2
    trainingError := fun _ => 1, testingError := fun _ => 1, dose := 4, maxWrites := 1, rail := 5
  }
  delay := fun _ _ => 0
  heldOut := (cube M).filter fun x => (List.finRange A).all fun a =>
    !(contains x (terms a) && contains (terms a) x)

private def majority3 : Cascade 3 1 3 :=
  fromTerms fun a => if a = 0 then pattern [0, 1] else if a = 1 then pattern [0, 2] else pattern [1, 2]

private def twoOfFour : Cascade 6 1 4 :=
  fromTerms fun a =>
    if a = 0 then pattern [0, 1] else if a = 1 then pattern [0, 2] else if a = 2 then pattern [0, 3]
    else if a = 3 then pattern [1, 2] else if a = 4 then pattern [1, 3] else pattern [2, 3]

private def eitherPair : Cascade 2 1 4 :=
  fromTerms fun a => if a = 0 then pattern [0, 1] else pattern [2, 3]

example : majority3.Valid ∧
    ((cube 3).all fun x => output majority3 0 x == decide (2 ≤ card x)) = true := by decide +kernel

example : twoOfFour.Valid ∧
    ((cube 4).all fun x => output twoOfFour 0 x == decide (2 ≤ card x)) = true := by decide +kernel

example : eitherPair.Valid ∧
    ((cube 4).all fun x => output eitherPair 0 x == ((x 0 && x 1) || (x 2 && x 3))) = true := by
  decide +kernel

private def unary : Cascade 1 1 1 := fromTerms fun _ => pattern [0]
private def constFalse (M : Nat) : Cascade 0 1 M := fromTerms Fin.elim0
private def constTrue (M : Nat) : Cascade 0 1 M :=
  { constFalse M with second := { (constFalse M).second with
      alwaysFire := fun _ => true, help := fun _ => 3 } }

example : unary.Valid ∧
    ((cube 1).all fun x => output unary 0 x == x 0) = true := by decide +kernel

example : (constFalse 0).Valid ∧ (constTrue 0).Valid ∧
    output (constFalse 0) 0 (pattern []) = false ∧
    output (constTrue 0) 0 (pattern []) = true := by decide +kernel

example : (constFalse 3).Valid ∧ (constTrue 3).Valid ∧
    ((cube 3).all fun x => !output (constFalse 3) 0 x && output (constTrue 3) 0 x) = true := by
  decide +kernel

/-- A comparable upstream target prevents isolation of its strict superset. -/
example : (fromTerms (A := 2) (M := 2) fun a =>
    if a = 0 then pattern [0] else pattern [0, 1]).reachable = false := by decide +kernel

private def xorInput (x : Pattern 2) : Bool := x 0 != x 1

/-- XOR switches off when a bit is added. This finite witness violates
the monotonicity clause in the characterization target. -/
example : contains (pattern [0, 1] : Pattern 2) (pattern [0]) = true ∧
    xorInput (pattern [0]) = true ∧ xorInput (pattern [0, 1]) = false := by decide +kernel

end LearnedCoincidence.MonotoneDNF
