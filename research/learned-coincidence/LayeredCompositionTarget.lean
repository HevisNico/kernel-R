import LayeredMonotoneTarget

/-! Layered composition: definitions and frozen targets only.

1. `LayeredRecognitionAt`: the per-pattern form of `LayeredMonotoneRecognitionOneSided`.
   A read calibration at one external pattern `x` determines the decisions at `x`.
2. The timing chain. `ReadCalibration` assumes, read by read, that every arrival lies in
   `[start, start + skew]`. Here that arrival window is removed from each read
   (`LayerReads`) and derived instead (`ArrivalWindows`). The inputs are:
   - the read start of each layer (`Scheduled`);
   - a window for each layer's pulses (`PulseWindows`);
   - date inequalities between layers on the fixed constants alone (`ChainDates`).
   Those inequalities can be checked before a run (`checkChainDates`).
3. The latency form. Each layer-`ℓ` cell emits between `λmin ℓ` and `λmax ℓ` after its
   read start (`CellLatency`). The form measured from the last arrival
   (`CellLatencyFromLastArrival`) implies it. The external pulses lie in `[s 0, s 0 + w]`. The pulse windows then
   follow, with `e = latencyLow λmin` and `f = latencyHigh w λmax`, so the whole schedule
   is predicted from per-cell constants. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)

/-- The external arrivals recorded by a read trace. -/
def inputTrace : (c : Cascade M L N) → ReadTrace c → Fin M → Option Rat
  | .input, r => r
  | .layer lower _ _, r => inputTrace lower r.1

/-- Frozen per-pattern target. -/
def LayeredRecognitionAt : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N), c.Valid →
    ∀ (train : TrainingTrace c), TrainingCalibration c train →
      ∀ (x : Pattern M) (test : ReadTrace c), ReadCalibration c train x test →
        c.Trained train ∧ observed c test = c.predict x

/-- `ThresholdRead` without its arrival-window clause. -/
def DecodedRead (level : Nat) (timing : SlotTiming) (r : ReadObservation 2) : Prop :=
  timing.Valid ∧
  (match r.emissions with
    | [] => True
    | [t] =>
      r.start ≤ t ∧ t ≤ r.start + timing.deadline ∧
      ∀ j v, r.arrival j = some v → v ≤ t
    | _ => False) ∧
  r.fired = decide ((level : Int) ≤ r.measuredScore)

/-- The arrival-window clause of `ThresholdRead`. -/
def InWindow (timing : SlotTiming) (r : ReadObservation 2) : Prop :=
  ∀ j t, r.arrival j = some t → r.start ≤ t ∧ t ≤ r.start + timing.skew

def AdditiveDecoded (p : Cell) (w : Writes) (budget : Nat) (timing : SlotTiming)
    (r : ReadObservation 2) : Prop :=
  DecodedRead p.threshold timing r ∧
  admissible budget (r.measuredScore - (p.score w r.input : Int))

def FiringDecoded (p : Cell) (w : Writes) (timing : SlotTiming)
    (r : ReadObservation 2) (scoreAt : Pattern 2 → Int) : Prop :=
  DecodedRead p.threshold timing r ∧
  scoreAt r.input = r.measuredScore ∧
  (∀ y, contains r.input y = true → (p.threshold : Int) ≤ scoreAt y →
    scoreAt y ≤ scoreAt r.input) ∧
  ∀ y ∈ p.gate.anchors, contains r.input y = true →
    (p.score w y : Int) - p.testError ≤ scoreAt y

/-- `ReadCalibration` without the external-mask clause and without any arrival window. -/
def LayerReads : (c : Cascade M L N) → TrainingTrace c → ReadTrace c → Prop
  | .input, _, _ => True
  | .layer lower timing nodes, train, r =>
    LayerReads lower train.1 r.1 ∧
    ∀ i,
      let d := nodes i
      let read := r.2.1 i
      let w := d.cell.settledWrites (train.2.2 i)
      Routed d (pulseDates lower r.1) read ∧
      if d.cell.gate.eval read.input then
        FiringDecoded d.cell w timing read (r.2.2 i)
      else
        AdditiveDecoded d.cell w d.cell.testError timing read

/-- Every read of every layer receives its arrivals within its own window. -/
def ArrivalWindows : (c : Cascade M L N) → ReadTrace c → Prop
  | .input, _ => True
  | .layer lower timing _, r => ArrivalWindows lower r.1 ∧ ∀ i, InWindow timing (r.2.1 i)

/-- Layer `ℓ ≥ 1` reads all start at `s ℓ`. Layer 0 is the external input. -/
def Scheduled (s : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Prop
  | .input, _ => True
  | .layer (L := L) lower _ _, r => Scheduled s lower r.1 ∧ ∀ i, (r.2.1 i).start = s (L + 1)

/-- Every pulse of layer `ℓ` lies in `[s ℓ + e ℓ, s ℓ + f ℓ]`. Only the first emission
of a read is routed, so only that pulse is constrained. -/
def PulseWindows (s e f : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Prop
  | .input, r => ∀ j t, r j = some t → s 0 + e 0 ≤ t ∧ t ≤ s 0 + f 0
  | .layer (L := L) lower _ _, r =>
    PulseWindows s e f lower r.1 ∧
    ∀ i t, (r.2.1 i).emissions.head? = some t →
      s (L + 1) + e (L + 1) ≤ t ∧ t ≤ s (L + 1) + f (L + 1)

/-- The chain inequalities. For each wired port of a layer `ℓ + 1` cell, with wire delay
`δ`: `s (ℓ+1) ≤ s ℓ + e ℓ + δ` and `s ℓ + f ℓ + δ ≤ s (ℓ+1) + skew (ℓ+1)`. They involve
constants only. -/
def ChainDates (s e f : Nat → Rat) : (c : Cascade M L N) → Prop
  | .input => True
  | .layer (L := L) lower timing nodes =>
    ChainDates s e f lower ∧
    ∀ i a src, (nodes i).source a = some src →
      s (L + 1) ≤ s L + e L + (nodes i).delay a ∧
      s L + f L + (nodes i).delay a ≤ s (L + 1) + timing.skew

def checkChainDates (s e f : Nat → Rat) : (c : Cascade M L N) → Bool
  | .input => true
  | .layer (L := L) lower timing nodes =>
    checkChainDates s e f lower &&
    (List.finRange N).all fun i => (List.finRange 2).all fun a =>
      match (nodes i).source a with
      | none => true
      | some _ =>
        decide (s (L + 1) ≤ s L + e L + (nodes i).delay a) &&
        decide (s L + f L + (nodes i).delay a ≤ s (L + 1) + timing.skew)

def ChainDatesCheckerSound : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (s e f : Nat → Rat),
    checkChainDates s e f c = true → ChainDates s e f c

def ChainDatesCheckerComplete : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N) (s e f : Nat → Rat),
    ChainDates s e f c → checkChainDates s e f c = true

/-- Frozen general form. The declared pulse windows and the chain inequalities give every
arrival window. The calibration at `x` without windows then gives the decisions at `x`. -/
def LayeredRecognitionChained : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N), c.Valid →
    ∀ (train : TrainingTrace c), TrainingCalibration c train →
      ∀ (s e f : Nat → Rat), ChainDates s e f c →
        ∀ (x : Pattern M) (test : ReadTrace c),
          (fun j => (inputTrace c test j).isSome) = x →
          LayerReads c train test → Scheduled s c test → PulseWindows s e f c test →
          ArrivalWindows c test ∧ observed c test = c.predict x

/-- The latency law of one cell read: every emission lies in
`[start + lmin, start + lmax]`. This is the premise the chain uses. -/
def CellLatency (lmin lmax : Rat) (r : ReadObservation 2) : Prop :=
  ∀ t ∈ r.emissions, r.start + lmin ≤ t ∧ t ≤ r.start + lmax

/-- The per-cell form measured from the last arrival: every emission is at least `lmin`
after the later of the read start and each arrival, and at most `lmax` after the read
start. It implies `CellLatency` (`cell_latency_of_last_arrival`). -/
def CellLatencyFromLastArrival (lmin lmax : Rat) (r : ReadObservation 2) : Prop :=
  ∀ t ∈ r.emissions,
    r.start + lmin ≤ t ∧ (∀ j v, r.arrival j = some v → v + lmin ≤ t) ∧ t ≤ r.start + lmax

def Latencies (lmin lmax : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Prop
  | .input, _ => True
  | .layer (L := L) lower _ _, r =>
    Latencies lmin lmax lower r.1 ∧ ∀ i, CellLatency (lmin (L + 1)) (lmax (L + 1)) (r.2.1 i)

/-- The external pulses lie in `[s0, s0 + w]`. -/
def ExternalWindow (s0 w : Rat) (c : Cascade M L N) (r : ReadTrace c) : Prop :=
  ∀ j t, inputTrace c r j = some t → s0 ≤ t ∧ t ≤ s0 + w

/-- The pulse window offsets derived from the latencies: layer 0 is the external window. -/
def latencyLow (lmin : Nat → Rat) : Nat → Rat
  | 0 => 0
  | ℓ + 1 => lmin (ℓ + 1)

def latencyHigh (w : Rat) (lmax : Nat → Rat) : Nat → Rat
  | 0 => w
  | ℓ + 1 => lmax (ℓ + 1)

/-- Frozen latency form. The whole calendar follows from `s`, `w` and the per-cell
latencies. The output pulses are predicted to lie in their layer's window. -/
def LayeredRecognitionFromLatency : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N), c.Valid →
    ∀ (train : TrainingTrace c), TrainingCalibration c train →
      ∀ (s lmin lmax : Nat → Rat) (w : Rat),
        ChainDates s (latencyLow lmin) (latencyHigh w lmax) c →
        ∀ (x : Pattern M) (test : ReadTrace c),
          (fun j => (inputTrace c test j).isSome) = x →
          LayerReads c train test → Scheduled s c test →
          ExternalWindow (s 0) w c test → Latencies lmin lmax c test →
          ArrivalWindows c test ∧ observed c test = c.predict x ∧
          ∀ i t, pulseDates c test i = some t →
            s L + latencyLow lmin L ≤ t ∧ t ≤ s L + latencyHigh w lmax L

/-- The deadline of each layer, by layer number. -/
def layerDeadline : (c : Cascade M L N) → Nat → Rat
  | .input => fun _ => 0
  | .layer (L := L) lower timing _ => fun ℓ => if ℓ = L + 1 then timing.deadline else layerDeadline lower ℓ

/-- Frozen deadline-only form: `e = 0` and `f = deadline` above the input. -/
def LayeredRecognitionFromDeadlines : Prop :=
  ∀ (M L N : Nat) (c : Cascade M L N), c.Valid →
    ∀ (train : TrainingTrace c), TrainingCalibration c train →
      ∀ (s : Nat → Rat) (w : Rat),
        ChainDates s (latencyLow fun _ => 0) (latencyHigh w (layerDeadline c)) c →
        ∀ (x : Pattern M) (test : ReadTrace c),
          (fun j => (inputTrace c test j).isSome) = x →
          LayerReads c train test → Scheduled s c test → ExternalWindow (s 0) w c test →
          ArrivalWindows c test ∧ observed c test = c.predict x

end LearnedCoincidence.Layered
