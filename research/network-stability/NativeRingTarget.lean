import DatedNetwork
import NativeAdmissions
import KernelR.HybridUniversalExecution

/-! The frozen statement for the single-token native ring in NATIVE_RING_PHASE0.md. -/

namespace NetworkStability.NativeRing

open KernelR.Hybrid
open PhaseAdmission
open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

/-- The topology, preparation, and launch are fixed by the protocol.
Membership only depends on these rational parameters and the number of cells. -/
structure Parameters (N : Nat) where
  delay : Fin N → ℚ
  forwardAmplitude : Fin N → ℚ
  returnAmplitude : ℚ

def WeakAmplitude (a : ℚ) : Prop := 9 / 10 ≤ a ∧ a ≤ 1

def StrongAmplitude (a : ℚ) : Prop := 9 / 5 ≤ a ∧ a ≤ 2

instance (a : ℚ) : Decidable (WeakAmplitude a) :=
  inferInstanceAs (Decidable (9 / 10 ≤ a ∧ a ≤ 1))

instance (a : ℚ) : Decidable (StrongAmplitude a) :=
  inferInstanceAs (Decidable (9 / 5 ≤ a ∧ a ≤ 2))

def Parameters.Valid (p : Parameters N) : Prop :=
  2 ≤ N ∧ WeakAmplitude p.returnAmplitude ∧
    ∀ i, (8 ≤ p.delay i ∧ p.delay i ≤ 9) ∧
      (if i.val = 0 then StrongAmplitude (p.forwardAmplitude i)
       else WeakAmplitude (p.forwardAmplitude i) ∨ StrongAmplitude (p.forwardAmplitude i))

instance (p : Parameters N) : Decidable p.Valid := by
  unfold Parameters.Valid
  infer_instance

def Parameters.check (p : Parameters N) : Bool := decide p.Valid

abbrev Input (N : Nat) := Fin N ⊕ Unit

abbrev Probe (N : Nat) := Occurrence ℝ (Input N)

abbrev Row (N : Nat) := Transaction ℝ (Input N)

abbrev State (N : Nat) := Config (3 * N) (Probe N)

def root (size : 2 ≤ N) : Fin N := ⟨0, by omega⟩

def inputCell (size : 2 ≤ N) : Input N → Fin N
  | .inl i => i
  | .inr _ => root size

def inputPort : Input N → Port
  | .inl _ => 0
  | .inr _ => 2

def successor (i : Fin N) : Input N :=
  if next : i.val + 1 < N then .inl ⟨i.val + 1, next⟩ else .inr ()

def toDelivery (size : 2 ≤ N) (p : Probe N) : Delivery N :=
  ⟨inputCell size p.input, inputPort p.input, p.due⟩

def seed (size : 2 ≤ N) : List (Probe N) :=
  [⟨1, .inl (root size)⟩]

noncomputable def router (p : Parameters N) (size : 2 ≤ N) : Router N := by
  classical
  exact fun i fire =>
    if i = root size ∧ ¬ (1 ≤ fire ∧ fire < 2) then []
    else [toDelivery size ⟨fire + p.delay i, successor i⟩]

noncomputable def nativeParameters (N : Nat) : Fin N → KernelR.Hybrid.Parameters :=
  fun _ => KernelR.FutureControls.parameters 0

def Parameters.amplitude (p : Parameters N) (size : 2 ≤ N) (i : Fin N) (port : Port) : ℚ :=
  if port = 0 then p.forwardAmplitude i
  else if i = root size ∧ port = 2 then p.returnAmplitude
  else 1

noncomputable def prepared (p : Parameters N) (size : 2 ≤ N) : Snapshot N where
  time := 0
  x i c := match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z port => Real.log (p.amplitude size i port)
    | .b => 9 / 50
    | .energy => 50
  main _ := .ready
  aux _ _ := .ready
  raw _ _ := none
  pending := (seed size).map (toDelivery size)

/-- Scalar first crossing at the prepared charge. The calendar is computed
from parameters; an execution will have to realize this exact clock. -/
noncomputable def latency (p : Parameters N) (i : Fin N) : ℝ :=
  if StrongAmplitude (p.forwardAmplitude i) then
    sInf {t : ℝ | 0 ≤ t ∧ t ≤ 9 / 10 ∧ readyPulse (1 / 10) (p.forwardAmplitude i) 0 t = 1}
  else 1 / 2

noncomputable def calendar (p : Parameters N) (size : 2 ≤ N) : Calendar N ℝ (Input N) where
  cell := inputCell size
  secondPort input := match input with
    | .inl _ => false
    | .inr _ => true
  phase _ _ := .ready
  bias input _ := match input with
    | .inl i => if StrongAmplitude (p.forwardAmplitude i) then 2 else -2
    | .inr _ => -2
  recoveryWeight _ _ := 0
  learn _ _ := true
  mark _ _ _ := false
  route probe := match probe.input with
    | .inl i => [⟨probe.due + latency p i + p.delay i, successor i⟩]
    | .inr _ => []

def occurrenceRank (p : Probe N) : Nat :=
  match p.input with
  | .inl i => N + 1 - i.val
  | .inr _ => 1

abbrev Q : Nat := 1
abbrev d : Nat := 4
abbrev B : Nat := 0
abbrev rail : Nat := 5
abbrev W : Nat := 2
abbrev eta₀ : Nat := 1

def horizon (N : Nat) : ℝ := 10 * ((N : ℝ) + 1)

def nativeCoordinate : Coordinate → Coord
  | .port0 => .z 0
  | .port1 => .z 2
  | .recovery => .b

noncomputable def unitDose : Coordinate → ℝ
  | .port0 | .port1 => 3 / 5
  | .recovery => 1 / 10

/-- A comparison at a settled cut includes the physical queue and the
unused native port. The recovery coordinate remains at its prepared value. -/
def Matches (p : Parameters N) (size : 2 ≤ N) (s : Snapshot N) (a : State N) : Prop :=
  s.pending.Perm (a.pending.map (toDelivery size)) ∧
    ∀ i, s.x i (.z 1) = (prepared p size).x i (.z 1) ∧
      a.writes (Address.mk i .recovery).encode = 0 ∧
      ∀ c, s.x i (nativeCoordinate c) = (prepared p size).x i (nativeCoordinate c) +
        unitDose c * a.writes (Address.mk i c).encode

/-- Rail safety for snapshots and all intermediate points of every flow. -/
def BelowRail (x : Values N) : Prop :=
  (∀ i port, x i (.z port) < Real.log ((nativeParameters N i).cap port)) ∧
    ∀ i, x i .b < 11 / 10

/-- Align each guarded row with a segment of the same native execution.
The successor queue and write counts live at the settled cut, after any
native FIRE or dose, rather than at the earlier intake clock. -/
inductive NativeRows (p : Parameters N) (size : 2 ≤ N) :
    {s u : Snapshot N} → Execution (nativeParameters N) (router p size) s u →
      State N → List (Row N) → State N → Prop where
  | done {s u} (idle : Execution (nativeParameters N) (router p size) s u) (a : State N)
      (noDelivery : idle.deliveries = [])
      (noFire : idle.ledger.emissions = [])
      (start : Matches p size s a) (finish : Matches p size u a) :
      NativeRows p size idle a [] a
  | step {s admitted settled u} {a next out : State N} {tx : Row N} {rows : List (Row N)}
      (intake : Execution (nativeParameters N) (router p size) s admitted)
      (pulse : Execution (nativeParameters N) (router p size) admitted settled)
      (suffix : Execution (nativeParameters N) (router p size) settled u)
      (arrival : NativeReciprocal.nativeAdmissions intake = [⟨toDelivery size tx.probe, .ready⟩])
      (clock : admitted.time = tx.probe.due)
      (raw : admitted.raw (inputCell size tx.probe.input) (inputPort tx.probe.input) =
        some tx.probe.due)
      (noEarlyFire : intake.ledger.emissions = [])
      (noDelivery : pulse.deliveries = [])
      (fire : pulse.ledger.emissions =
        tx.fireDate.toList.map (fun t => (inputCell size tx.probe.input, t)))
      (route : tx.children.map (toDelivery size) =
        tx.fireDate.toList.flatMap (router p size (inputCell size tx.probe.input)))
      (fireClock : ∀ t ∈ tx.fireDate,
        tx.probe.due + 3 / 10 < t ∧ t < tx.probe.due + 9 / 10)
      (settledClock : settled.time = tx.probe.due + 15 / 2)
      (ready : ∀ i, PreparedSection settled i)
      (inactive : ∀ i port, settled.raw i port = none)
      (margin : tx.lo = -1 ∧ tx.hi = 1)
      (start : Matches p size s a) (finish : Matches p size settled next)
      (replay : TransactionReplay (calendar p size) d (· ≤ ·) a [tx] next)
      (later : NativeRows p size suffix next rows out) :
      NativeRows p size (intake.append (pulse.append suffix)) a (tx :: rows) out

/-- The coordinate recording the result is the first weak relay, or the
root's return port when all relays transmit. -/
def resultInput (p : Parameters N) : Input N :=
  match (List.finRange N).find? (fun i => decide (WeakAmplitude (p.forwardAmplitude i))) with
  | some i => .inl i
  | none => .inr ()

def resultAddress (p : Parameters N) (size : 2 ≤ N) : Address N :=
  let input := resultInput p
  ⟨inputCell size input, match input with | .inl _ => .port0 | .inr _ => .port1⟩

/-- Target for a fixed checked parameter tuple. The same compiler is used
for the native witness, the abstract replay, and every comparison trace. -/
def Refines (p : Parameters N) (size : 2 ≤ N) : Prop :=
  let C := calendar p size
  let start := MarkFeedback.initial N (seed size)
  Nonempty (MarkFeedback.Reserve Q C.model (seed size)) ∧
  (∃ rank : MarkFeedback.Rank W eta₀ C.model (seed size), rank.weight = occurrenceRank) ∧
  Causal C ∧ TieAdmissible C d start ∧
  ∃ (last : Snapshot N)
    (run : Execution (nativeParameters N) (router p size) (prepared p size) last)
    (rows : List (Row N)) (out : State N),
    CompleteThrough run (horizon N) ∧
    NativeRows p size run start rows out ∧
    TransactionReplay C d (· ≤ ·) start rows out ∧
    rows.map (fun tx => toDelivery size tx.probe) = run.deliveries ∧
    Transaction.fires (inputCell size) rows = run.ledger.emissions ∧
    last.pending = [] ∧ out.pending = [] ∧ rows.length ≤ N + 1 ∧
    Matches p size last out ∧
    run.AllStates (fun s => BelowRail s.x) ∧
    run.AllFlows (fun {s u} flow => ∀ t ∈ Set.Icc s.time u.time, BelowRail (flow.path t)) ∧
    SafeMemory Q d B rail (fun _ => 0) out ∧
    (∀ i, out.writes i = if i = (resultAddress p size).encode then 1 else 0) ∧
    (∀ other word, Trace C d (· ≤ ·) start word other →
      List.IsPrefix word (Transaction.word rows) ∧ word.length ≤ N + 1 ∧
        (other.pending = [] → word = Transaction.word rows ∧ other.writes = out.writes) ∧
        ∃ suffix, Trace C d (· ≤ ·) other suffix out ∧ word ++ suffix = Transaction.word rows) ∧
    (∀ (other : Snapshot N)
      (comparison : Execution (nativeParameters N) (router p size) (prepared p size) other),
      CompleteThrough comparison (horizon N) →
        last.ObservationalEq other ∧ run.ledger.emissions.Perm comparison.ledger.emissions)

/-- Frozen theorem statement for the final milestone. -/
def NativeRingRefinement : Prop :=
  ∀ (N : Nat) (p : Parameters N), p.Valid → ∀ size : 2 ≤ N, Refines p size

end NetworkStability.NativeRing
