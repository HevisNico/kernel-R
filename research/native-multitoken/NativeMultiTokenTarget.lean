import DatedNetwork
import NativeAdmissions
import KernelR.FutureControls
import KernelR.HybridUniversalExecution
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic

/-! Frozen design target for the native multi-token training ring. -/
namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid PhaseAdmission
open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

structure Parameters (N : Nat) where
  amplitude : Fin N → ℚ
  gap1 : ℚ
  gap2 : ℚ
  successor : Fin N → Fin N
  delay : Fin N → ℚ

/-- Fixed outward enclosures, interpreted as rational constants in the checker. -/
def expThreeFifthsBounds : ℚ × ℚ := (1822 / 1000, 1823 / 1000)
def expSixFifthsBounds : ℚ × ℚ := (3320 / 1000, 3321 / 1000)

def auxDeadline : ℚ := 419 / 300

def G (p : Parameters N) : Prop :=
  ∀ i, 9 / 5 ≤ expSixFifthsBounds.1 * p.amplitude i ∧
    expSixFifthsBounds.2 * p.amplitude i ≤ 2

def T1 (p : Parameters N) : Prop :=
  8 ≤ p.gap1 ∧ 8 ≤ p.gap2

def R1 (p : Parameters N) : Prop :=
  (∀ i j, p.successor i = p.successor j → i = j) ∧
    ∀ i j, ∃ k : Fin N, (p.successor^[k.val]) i = j

def T2 (p : Parameters N) : Prop :=
  ∀ i, 3 / 10 + p.delay i > 9 / 10 + 1

def T3 (p : Parameters N) : Prop :=
  ∀ i, 9 / 50 * (p.delay i + 3 / 5 - 1) + 7 / 25 * auxDeadline < 9 / 10

def Parameters.Valid (p : Parameters N) : Prop :=
  2 ≤ N ∧ G p ∧ T1 p ∧ R1 p ∧ T2 p ∧ T3 p

instance (p : Parameters N) : Decidable p.Valid := by
  unfold Parameters.Valid G T1 R1 T2 T3
  infer_instance

def Parameters.check (p : Parameters N) : Bool := decide p.Valid

def family (N : Nat) : Parameters N where
  amplitude _ := 3 / 5
  gap1 := 8
  gap2 := 8
  successor i := ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  delay _ := 5 / 2

example : (family 2).check = true ∧ (family 3).check = true := by decide +kernel

inductive Stage
  | first | second | launch | receipt
  deriving DecidableEq, BEq

abbrev Input (N : Nat) := Fin N × Stage
abbrev Probe (N : Nat) := Occurrence ℝ (Input N)
abbrev Row (N : Nat) := Transaction ℝ (Input N)
abbrev State (N : Nat) := Config (3 * N) (Probe N)

def inputCell (input : Input N) : Fin N := input.1

def inputPort (input : Input N) : Port :=
  if input.2 = .receipt then 2 else 0

def toDelivery (probe : Probe N) : Delivery N :=
  ⟨inputCell probe.input, inputPort probe.input, probe.due⟩

def firstDate : ℝ := 1
noncomputable def secondDate (p : Parameters N) : ℝ := firstDate + p.gap1
noncomputable def launchDate (p : Parameters N) : ℝ := secondDate p + p.gap2
noncomputable def horizon (p : Parameters N) : ℝ := launchDate p + 10

noncomputable def seed (p : Parameters N) : List (Probe N) :=
  (List.finRange N).map (fun i => ⟨firstDate, (i, .first)⟩) ++
  (List.finRange N).map (fun i => ⟨secondDate p, (i, .second)⟩) ++
  (List.finRange N).map (fun i => ⟨launchDate p, (i, .launch)⟩)

noncomputable def nativeParameters (N : Nat) : Fin N → KernelR.Hybrid.Parameters :=
  fun _ => KernelR.FutureControls.parameters 0

noncomputable def prepared (p : Parameters N) : Snapshot N where
  time := 0
  x i c := match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z port => if port = 0 then Real.log (p.amplitude i : ℝ) else 0
    | .b => 9 / 50
    | .energy => 50
  main _ := .ready
  aux _ _ := .ready
  raw _ _ := none
  pending := (seed p).map toDelivery

noncomputable def router (p : Parameters N) : Router N := by
  classical
  exact fun i fire =>
    if launchDate p + 3 / 10 ≤ fire ∧ fire ≤ launchDate p + 9 / 10 then
      [⟨p.successor i, 2, fire + p.delay i⟩]
    else []

noncomputable def afterSilent (charge amplitude gap : ℝ) : ℝ :=
  1 / 10 + (readyPulse charge amplitude 0 1 - 1 / 10) * Real.exp (-(gap - 1) / 2)

noncomputable def launchCharge (p : Parameters N) (i : Fin N) : ℝ :=
  afterSilent (afterSilent (1 / 10) (p.amplitude i) p.gap1)
    ((p.amplitude i : ℝ) * Real.exp (3 / 5)) p.gap2

noncomputable def launchAmplitude (p : Parameters N) (i : Fin N) : ℝ :=
  (p.amplitude i : ℝ) * Real.exp (6 / 5)

noncomputable def latency (p : Parameters N) (i : Fin N) : ℝ :=
  sInf {t : ℝ | 3 / 10 < t ∧ t < 9 / 10 ∧
    readyPulse (launchCharge p i) (launchAmplitude p i) 0 t = 1}

noncomputable def calendar (p : Parameters N) : Calendar N ℝ (Input N) where
  cell := inputCell
  secondPort input := input.2 == .receipt
  phase input _ := if input.2 = .receipt then .slow else .ready
  bias input _ := if input.2 = .receipt then -2 else -6
  recoveryWeight _ _ := 0
  learn _ phase := match phase with
    | .ready => true
    | .slow => false
  mark input phase fire := match phase with
    | .ready => false
    | .slow => (input.2 == .receipt) && !fire
  route probe := if probe.input.2 = .launch then
    [⟨probe.due + latency p probe.input.1 + p.delay probe.input.1,
      (p.successor probe.input.1, .receipt)⟩]
    else []

def occurrenceRank (probe : Probe N) : Nat :=
  if probe.input.2 = .launch then 2 else 1

abbrev Q : Nat := 3
abbrev d : Nat := 4
abbrev B : Nat := 0
abbrev rail : Nat := 13
abbrev W : Nat := 4
abbrev eta₀ : Nat := 1

def nativeCoordinate : Coordinate → Coord
  | .port0 => .z 0
  | .port1 => .z 2
  | .recovery => .b

noncomputable def unitDose : Coordinate → ℝ
  | .port0 | .port1 => 3 / 5
  | .recovery => 1 / 10

def BelowRail (x : Values N) : Prop :=
  (∀ i port, x i (.z port) < Real.log ((nativeParameters N i).cap port)) ∧
    ∀ i, x i .b < 11 / 10

def SettledMemory (p : Parameters N) (s : Snapshot N) (state : State N) : Prop :=
  ∀ i, s.x i (.z 1) = (prepared p).x i (.z 1) ∧
    ∀ c, s.x i (nativeCoordinate c) =
      (prepared p).x i (nativeCoordinate c) + unitDose c * state.writes (Address.mk i c).encode

def targetDecision (input : Input N) : Bool := input.2 == .launch

def rowAdmission (row : Row N) : NativeReciprocal.Admission N :=
  ⟨toDelivery row.probe, if row.probe.input.2 = .receipt then .slow else .ready⟩

def RowMatches (p : Parameters N) (row : Row N) : Prop :=
  let probe := row.probe
  row.lo = -1 ∧ row.hi = 1 ∧ row.decision = targetDecision probe.input ∧
  row.fireDate = (if probe.input.2 = .launch then
      some (probe.due + latency p probe.input.1) else none) ∧
  row.children.map toDelivery = row.fireDate.toList.flatMap (router p probe.input.1)

/-- Each local pulse has a dose ledger on a segment cut out of the same
global witness. The segment can contain activity at other cells. -/
def RowDose (p : Parameters N) {last : Snapshot N}
    (run : Execution (nativeParameters N) (router p) (prepared p) last) (row : Row N) : Prop :=
  let i := row.probe.input.1
  let stage := row.probe.input.2
  ∃ (before admitted finished : Snapshot N)
    (head : Execution (nativeParameters N) (router p) (prepared p) before)
    (arrival : Jump (router p) before admitted)
    (body : Execution (nativeParameters N) (router p) admitted finished)
    (tail : Execution (nativeParameters N) (router p) finished last),
    run = head.append (.cons (.jump arrival) (body.append tail)) ∧
    NativeReciprocal.jumpAdmissions arrival = [rowAdmission row] ∧
    before.time = row.probe.due ∧ finished.time = row.probe.due + auxDeadline ∧
    (∀ token ∈ body.deliveries, token.cell ≠ i) ∧
    body.emissionTimes i = row.fireDate.toList ∧
    (∀ port, body.ledger.error i port =
      if port = 0 ∧ (stage = .first ∨ stage = .second) then 3 / 5 else 0) ∧
    (∀ port, body.ledger.mark i port =
      if port = 2 ∧ stage = .receipt then 1 / 10 else 0) ∧
    body.ledger.recovery i = (if stage = .receipt then 1 / 10 else 0) ∧
    (stage = .receipt → body.AllStates (fun s => s.main i = .slow)) ∧
    (∀ port, finished.raw i port = none ∧ finished.aux i port = .ready)

/-- A guarded launch enqueues before the native FIRE. Count only the
children of consumed launch rows whose FIRE is absent from the native
prefix emissions. -/
noncomputable def unissued (rows : List (Row N)) (fires : List (Fin N × ℝ)) :
    List (Delivery N) := by
  classical
  exact rows.flatMap fun row =>
    match row.fireDate with
    | none => []
    | some time =>
      if (row.probe.input.1, time) ∈ fires then [] else row.children.map toDelivery

def prefixCorrespondence (p : Parameters N) {last : Snapshot N}
    (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (rows : List (Row N)) (out : State N) : Prop :=
  ∀ (cut : Snapshot N)
    (head : Execution (nativeParameters N) (router p) (prepared p) cut)
    (tail : Execution (nativeParameters N) (router p) cut last),
    run = head.append tail →
    let consumed := rows.take head.deliveries.length
    ∃ mid : State N,
      NativeReciprocal.nativeAdmissions head = consumed.map rowAdmission ∧
      TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) consumed mid ∧
      TransactionReplay (calendar p) d (· ≤ ·) mid (rows.drop head.deliveries.length) out ∧
      (mid.pending.map toDelivery).Perm (cut.pending ++ unissued consumed head.ledger.emissions) ∧
      (head.ledger.emissions.length < N → ∀ row ∈ consumed, row.probe.input.2 ≠ .receipt) ∧
      ((cut.time = firstDate + 15 / 2 ∨ cut.time = secondDate p + 15 / 2) →
        SettledMemory p cut mid)

/-- Target for a single tuple. Membership and the compiler are independent
of the witness quantified here. -/
def Refines (p : Parameters N) : Prop :=
  let C := calendar p
  let start := MarkFeedback.initial N (seed p)
  Nonempty (MarkFeedback.Reserve Q C.model (seed p)) ∧
  (∃ rank : MarkFeedback.Rank W eta₀ C.model (seed p), rank.weight = occurrenceRank) ∧
  Causal C ∧ TieAdmissible C d start ∧
  (∀ i, 3 / 10 < latency p i ∧ latency p i < 9 / 10 ∧
    readyPulse (launchCharge p i) (launchAmplitude p i) 0 (latency p i) = 1 ∧
    ∀ t, 0 ≤ t → t < latency p i → readyPulse (launchCharge p i) (launchAmplitude p i) 0 t < 1) ∧
  ∃ (last : Snapshot N)
    (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (rows : List (Row N)) (out : State N),
    CompleteThrough run (horizon p) ∧ run.ContactsTransversal ∧
    TransactionReplay C d (· ≤ ·) start rows out ∧
    rows.length = 4 * N ∧ rows.map rowAdmission = NativeReciprocal.nativeAdmissions run ∧
    (Transaction.fires inputCell rows).Perm run.ledger.emissions ∧
    run.ledger.emissions.Perm ((List.finRange N).map (fun i => (i, launchDate p + latency p i))) ∧
    (∀ row ∈ rows, RowMatches p row ∧ RowDose p run row) ∧
    (∀ i, run.ledger.error i 0 = 2 * unitDose .port0 ∧
      run.ledger.error i 1 = 0 ∧ run.ledger.error i 2 = 0 ∧
      run.ledger.mark i 0 = 0 ∧ run.ledger.mark i 1 = 0 ∧
      run.ledger.mark i 2 = unitDose .recovery) ∧
    prefixCorrespondence p run rows out ∧
    (∀ t ∈ [firstDate + 15 / 2, secondDate p + 15 / 2], ∃ (cut : Snapshot N)
      (head : Execution (nativeParameters N) (router p) (prepared p) cut)
      (tail : Execution (nativeParameters N) (router p) cut last),
      run = head.append tail ∧ cut.time = t ∧
      (∀ i, cut.main i = .ready ∧ ∀ port, cut.raw i port = none ∧ cut.aux i port = .ready)) ∧
    (∃ (cut : Snapshot N) (head : Execution (nativeParameters N) (router p) (prepared p) cut)
      (tail : Execution (nativeParameters N) (router p) cut last),
      run = head.append tail ∧ head.ledger.emissions.length = N ∧
      cut.pending.Perm (rows.flatMap (fun row => row.children.map toDelivery))) ∧
    last.pending = [] ∧ out.pending = [] ∧ SettledMemory p last out ∧
    run.AllStates (fun s => BelowRail s.x) ∧
    run.AllFlows (fun {s u} flow => ∀ t ∈ Set.Icc s.time u.time, BelowRail (flow.path t)) ∧
    SafeMemory Q d B rail (fun _ => 0) out ∧
    (∀ i c, out.writes (Address.mk i c).encode =
      match c with | .port0 => 2 | .port1 => 0 | .recovery => 1) ∧
    (∀ other word, Trace C d (· ≤ ·) start word other →
      word.length ≤ 4 * N ∧
      (∀ entry ∈ word, entry.2 = targetDecision entry.1.input) ∧
      (other.pending = [] → word.Perm (Transaction.word rows) ∧ other.writes = out.writes) ∧
      ∃ terminal suffix, Trace C d (· ≤ ·) other suffix terminal ∧ terminal.pending = [] ∧
        (word ++ suffix).Perm (Transaction.word rows) ∧ terminal.writes = out.writes) ∧
    (∀ (other : Snapshot N)
      (comparison : Execution (nativeParameters N) (router p) (prepared p) other),
      CompleteThrough comparison (horizon p) →
        last.ObservationalEq other ∧ run.ledger.emissions.Perm comparison.ledger.emissions)

/-- Frozen target for the implementation phase. -/
def NativeMultiTokenRefinement : Prop :=
  ∀ (N : Nat) (p : Parameters N), p.check = true → Refines p

end NetworkStability.NativeMultiToken
