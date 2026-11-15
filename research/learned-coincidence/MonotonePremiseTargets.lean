import MonotoneOneSidedTarget

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch
  observedCount settledCount)

namespace PremiseCheck

/-- Enumerate the whole Boolean cube, including the single empty mask at size zero. -/
def patterns : (M : Nat) → List (Pattern M)
  | 0 => [Fin.elim0]
  | M + 1 => (patterns M).flatMap fun x => [Fin.cases false x, Fin.cases true x]

/-- The first port is the most significant bit in a tabulated test pattern. -/
def maskIndex : {M : Nat} → Pattern M → Fin (2 ^ M)
  | 0, _ => 0
  | M + 1, x =>
    let tail := maskIndex (fun j => x j.succ)
    ⟨(if x 0 then 2 ^ M else 0) + tail.val, by
      have bound := tail.isLt
      rw [Nat.pow_succ]
      split <;> omega⟩

/-- Dates are exact rationals. Scores use the integer units of the frozen read
interface. For rational calibration data, use a common positive denominator
to express all scores and score parameters in the same integer units. -/
def datedRead (start : Rat) (arrivals : Vector (Option Rat) M)
    (emissions : List Rat) (value : Int) : ReadObservation M :=
  ⟨start, arrivals.get, emissions, value⟩

abbrev Table (rows cols : Nat) (α : Type) := Vector (Vector α cols) rows

/-- Indexed rows for every training round, lesson, and external mask. The sizes
ensure that lookup in a checked slot never uses a missing row. Mask columns
and rows use the index defined by `maskIndex`. -/
structure TraceTables (p : Cascade A B M) where
  firstTrain : Table (p.first.maxWrites + 1) A (ReadObservation M)
  teach : Table (lessons p).length A (ReadObservation M)
  secondTrain : Vector (ReadObservation A) (lessons p).length
  firstTest : Table (2 ^ M) A (ReadObservation M)
  secondTest : Table (2 ^ M) B (ReadObservation A)
  scores : Table (2 ^ M) B (Vector Int (2 ^ A))

private def emptyRead : ReadObservation M := ⟨0, fun _ => none, [], 0⟩

def TraceTables.observations {p : Cascade A B M} (t : TraceTables p) : Observations A B M where
  firstTrain r a := if h : r < p.first.maxWrites + 1 then
    (t.firstTrain.get ⟨r, h⟩).get a else emptyRead
  teach n a := if h : n < (lessons p).length then (t.teach.get ⟨n, h⟩).get a else emptyRead
  secondTrain n := if h : n < (lessons p).length then t.secondTrain.get ⟨n, h⟩ else emptyRead
  firstTest x a := (t.firstTest.get (maskIndex x)).get a
  secondTest x i := (t.secondTest.get (maskIndex x)).get i

def TraceTables.scoreAt {p : Cascade A B M} (t : TraceTables p)
    (x : Pattern M) (i : Fin B) (y : Pattern A) : Int :=
  ((t.scores.get (maskIndex x)).get i).get (maskIndex y)

def checkEndsBefore (firstTiming secondTiming : SlotTiming) (o : Observations A B M)
    (n : Nat) (time : Rat) : Bool :=
  (List.finRange A).all (fun a => decide ((o.teach n a).start + firstTiming.duration ≤ time)) &&
  decide ((o.secondTrain n).start + secondTiming.duration ≤ time)

def checkArrivals (r : ReadObservation M) (ok : Rat → Bool) : Bool :=
  (List.finRange M).all fun j => (r.arrival j).all ok

def checkEmissions (timing : SlotTiming) (r : ReadObservation M) : Bool :=
  match r.emissions with
  | [] => true
  | [t] => decide (r.start ≤ t ∧ t ≤ r.start + timing.deadline) &&
      checkArrivals r (fun v => decide (v ≤ t))
  | _ => false

def checkThresholdRead (level : Nat) (timing : SlotTiming) (r : ReadObservation M) : Bool :=
  decide (0 ≤ timing.skew ∧ 0 < timing.deadline ∧
    timing.skew ≤ timing.deadline ∧ timing.deadline < timing.duration) &&
  checkArrivals r (fun t => decide (r.start ≤ t ∧ t ≤ r.start + timing.skew)) &&
  checkEmissions timing r &&
  (r.fired == decide ((level : Int) ≤ r.measuredScore))

def checkAdditiveRead (p : Parameters N M) (i : Fin N) (writes : Nat) (x : Pattern M)
    (budget : Nat) (timing : SlotTiming) (r : ReadObservation M) : Bool :=
  checkThresholdRead (p.threshold i) timing r &&
  (List.finRange M).all (fun j => r.input j == x j) &&
  (let residual := r.measuredScore - (score p i writes x : Int)
  decide (-(budget : Int) ≤ residual ∧ residual ≤ budget))

def checkRoute (delay : Fin A → Rat) (left : Fin A → ReadObservation M)
    (right : ReadObservation A) : Bool :=
  (List.finRange A).all fun a => decide
    (right.arrival a = ((left a).emissions.head?).map (fun t => t + delay a))

def checkFiringMask (p : Disjunctions B A) (writes : Counts B A) (i : Fin B)
    (timing : SlotTiming) (r : ReadObservation A) (scoreAt : Pattern A → Int) : Bool :=
  checkThresholdRead (p.threshold i) timing r &&
  decide (scoreAt r.input = r.measuredScore) &&
  (patterns A).all (fun y =>
    if contains r.input y && decide ((p.threshold i : Int) ≤ scoreAt y) then
      decide (scoreAt y ≤ scoreAt r.input)
    else true) &&
  (if p.alwaysFire i then
    decide ((p.help i : Int) - p.testingError i ≤ scoreAt (fun _ => false))
  else
    (List.finRange A).all fun a =>
      if p.lines i a && r.input a then
        decide ((lineScore p i a (writes i a) : Int) - p.testingError i ≤ scoreAt (singleton a))
      else true)

end PremiseCheck

open PremiseCheck

/-- The frozen validity predicate already has an executable Boolean checker. -/
def checkCascadeValid (p : Cascade A B M) : Bool := p.check

def checkTrainingSeparation (p : Cascade A B M) (left right : SlotTiming)
    (o : Observations A B M) : Bool :=
  let rounds := List.range p.first.maxWrites
  let schedule := List.range (lessons p).length
  let first := List.finRange A
  let second := List.finRange B
  let tests := patterns M
  (rounds.all fun r => first.all fun a => first.all fun b =>
    decide ((o.firstTrain r a).start + left.duration ≤ (o.firstTrain (r + 1) b).start)) &&
  (schedule.all fun n => first.all fun a =>
    (first.all fun b =>
      decide ((o.firstTrain p.first.maxWrites a).start + left.duration ≤ (o.teach n b).start)) &&
    decide ((o.firstTrain p.first.maxWrites a).start + left.duration ≤ (o.secondTrain n).start)) &&
  (schedule.all fun n => schedule.all fun s => if n < s then
    (first.all fun a => checkEndsBefore left right o n (o.teach s a).start) &&
    checkEndsBefore left right o n (o.secondTrain s).start
    else true) &&
  (tests.all fun x => first.all fun a =>
    (first.all fun b =>
      decide ((o.firstTrain p.first.maxWrites a).start + left.duration ≤ (o.firstTest x b).start)) &&
    (second.all fun i =>
      decide ((o.firstTrain p.first.maxWrites a).start + left.duration ≤ (o.secondTest x i).start))) &&
  (tests.all fun x => schedule.all fun n =>
    (first.all fun a => checkEndsBefore left right o n (o.firstTest x a).start) &&
    (second.all fun i => checkEndsBefore left right o n (o.secondTest x i).start))

def checkCascadeCalibrationOneSided (p : Cascade A B M) (left right : SlotTiming)
    (o : Observations A B M) (scores : Pattern M → Fin B → Pattern A → Int) : Bool :=
  let schedule := lessons p
  let first := List.finRange A
  let second := List.finRange B
  let tests := patterns M
  let settled := settledCount p.first o.firstTrain
  let writes := lessonCounts p o schedule.length
  (List.range (p.first.maxWrites + 1) |>.all fun r => first.all fun a =>
    checkAdditiveRead p.first a (observedCount o.firstTrain a r) (p.first.target a)
      (p.first.trainingError a) left (o.firstTrain r a)) &&
  ((List.range schedule.length).all fun n =>
    match schedule[n]? with
    | none => false
    | some L =>
      (first.all fun a => checkAdditiveRead p.first a (settled a) (p.first.target L.line)
        (p.first.testingError a) left (o.teach n a)) &&
      checkRoute (p.delay L.cell) (o.teach n) (o.secondTrain n) &&
      checkAdditiveRead (readView p.second (lessonCounts p o n)) L.cell 0 (o.secondTrain n).input
        (p.second.trainingError L.cell) right (o.secondTrain n)) &&
  (tests.all fun x => first.all fun a =>
    checkAdditiveRead p.first a (settled a) x (p.first.testingError a) left (o.firstTest x a)) &&
  (tests.all fun x => second.all fun i =>
    let r := o.secondTest x i
    checkRoute (p.delay i) (o.firstTest x) r &&
    if p.second.alwaysFire i || first.any (fun a => p.second.lines i a && r.input a) then
      checkFiringMask p.second writes i right r (scores x i)
    else
      checkAdditiveRead (readView p.second writes) i 0 r.input (p.second.testingError i) right r)

/-- Frozen soundness target for the parameter checker. -/
def CascadeValidCheckerSound : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M), checkCascadeValid p = true → p.Valid

/-- Frozen soundness target for the calendar checker. -/
def TrainingSeparationCheckerSound : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M) (left right : SlotTiming) (o : Observations A B M),
    checkTrainingSeparation p left right o = true → TrainingSeparation p left right o

/-- Frozen soundness target for the calibration checker. -/
def CascadeCalibrationOneSidedCheckerSound : Prop :=
  ∀ (A B M : Nat) (p : Cascade A B M) (left right : SlotTiming) (o : Observations A B M)
    (scores : Pattern M → Fin B → Pattern A → Int),
    checkCascadeCalibrationOneSided p left right o scores = true →
      CascadeCalibrationOneSided p left right o scores

end LearnedCoincidence.MonotoneDNF
