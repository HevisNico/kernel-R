import MarkFeedback

namespace NetworkStability.PhaseAdmission

open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address)

inductive Phase
  | ready
  | slow
  deriving DecidableEq

/-- A dated occurrence carries a calendar key and a physical input. The same
input can be admitted in different phases on different dates. -/
structure Occurrence (Date Input : Type) where
  due : Date
  input : Input
  deriving DecidableEq

structure Calendar (N : Nat) (Date Input : Type) where
  cell : Input → Fin N
  secondPort : Input → Bool
  phase : Input → Date → Phase
  bias : Input → Phase → Int
  recoveryWeight : Input → Phase → Int
  learn : Input → Phase → Bool
  mark : Input → Phase → Bool → Bool
  route : Occurrence Date Input → List (Occurrence Date Input)

/-- The phase belongs to the occurrence. Selecting another occurrence first
can change the stored counts, but cannot change this phase. -/
def Calendar.model (C : Calendar N Date Input) : MarkFeedback.Model N (Occurrence Date Input) where
  cell p := C.cell p.input
  secondPort p := C.secondPort p.input
  bias p := C.bias p.input (C.phase p.input p.due)
  recoveryWeight p := C.recoveryWeight p.input (C.phase p.input p.due)
  learn p := C.learn p.input (C.phase p.input p.due)
  mark p := C.mark p.input (C.phase p.input p.due)
  route := C.route

/-- Calendar order for a selected set of pending occurrences. A supplied
order comparison admits ties. The abstract transition still consumes one
occurrence and appends its descendants, irrespective of list presentation. -/
def Earliest (le : Date → Date → Prop) (p : Occurrence Date Input)
    (rest : List (Occurrence Date Input)) : Prop :=
  ∀ q ∈ rest, le p.due q.due

/-- An admission trace checks the date, exact occurrence multiplicity, read
margin and selected branch at every step, and records the full decision word. -/
inductive Trace (C : Calendar N Date Input) (d : Nat) (le : Date → Date → Prop) :
    Config (3 * N) (Occurrence Date Input) → List (Occurrence Date Input × Bool) →
      Config (3 * N) (Occurrence Date Input) → Prop where
  | nil (s) : Trace C d le s [] s
  | cons {s u} (p : Occurrence Date Input) (rest : List (Occurrence Date Input))
      (available : s.pending.Perm (p :: rest)) (earliest : Earliest le p rest)
      (lo hi error : Int) (within : lo ≤ error ∧ error ≤ hi)
      (room : RoutedCalendar.HasRoom (MarkFeedback.score C.model d s p) lo hi)
      {word} (tail : Trace C d le (MarkFeedback.process C.model d s p rest error) word u) :
      Trace C d le s ((p, MarkFeedback.read C.model d s p error) :: word) u

theorem Trace.certified {C : Calendar N Date Input} {d le s word u}
    (trace : Trace C d le s word u) : MarkFeedback.CertifiedPath C.model d s u := by
  induction trace with
  | nil => exact .nil _
  | cons p rest available _ lo hi error within room _ ih =>
    exact .cons p rest available lo hi error within room ih


/-- Zero-error dated execution with the full decision word. -/
inductive NominalTrace (C : Calendar N Date Input) (d : Nat) (le : Date → Date → Prop) :
    Config (3 * N) (Occurrence Date Input) → List (Occurrence Date Input × Bool) →
      Config (3 * N) (Occurrence Date Input) → Prop where
  | nil (s) : NominalTrace C d le s [] s
  | cons {s u} (p : Occurrence Date Input) (rest : List (Occurrence Date Input))
      (available : s.pending.Perm (p :: rest)) (earliest : Earliest le p rest)
      {word} (tail : NominalTrace C d le (MarkFeedback.process C.model d s p rest 0) word u) :
      NominalTrace C d le s ((p, MarkFeedback.read C.model d s p 0) :: word) u

/-- Certified errors leave both the decision word and the final state
unchanged when replayed with the same dated choices and zero errors. -/
theorem Trace.zero_error_replay {C : Calendar N Date Input} {d le s word u}
    (trace : Trace C d le s word u) : NominalTrace C d le s word u := by
  induction trace with
  | nil => exact .nil _
  | cons p rest available earliest lo hi error within room _ ih =>
    have decision : MarkFeedback.read C.model d _ p error = MarkFeedback.read C.model d _ p 0 :=
      MarkFeedback.read_eq_of_room _ lo hi error within room
    simpa only [decision] using
      (NominalTrace.cons p rest available earliest (by
        simpa only [MarkFeedback.process, decision] using ih))

/-- The rank bounds even a finite prefix under earliest-date scheduling. -/
theorem Trace.rank_bound {C : Calendar N Date Input} {W eta d le seed s word u}
    (rank : MarkFeedback.Rank W eta C.model seed) (trace : Trace C d le s word u) :
    word.length + AutonomousFeedback.mass rank.weight u.pending ≤
      AutonomousFeedback.mass rank.weight s.pending := by
  induction trace with
  | nil => simp
  | cons p rest available _ _ _ error _ _ _ ih =>
    have progress := MarkFeedback.process_rank C.model d W eta rank _ p rest available error
    have positive := rank.positive
    simp only [List.length_cons]
    omega

/-- At a tie, both orders remain earliest after either step if issued
children are no earlier than their parent. The physical commutation
condition still checks the two write footprints. -/
theorem tied_occurrences_commute (C : Calendar N Date Input) (d : Nat)
    (le : Date → Date → Prop) (trans : ∀ {a b c}, le a b → le b c → le a c)
    (causal : ∀ p q, q ∈ C.route p → le p.due q.due)
    (s : Config (3 * N) (Occurrence Date Input)) (p q : Occurrence Date Input)
    (rest : List (Occurrence Date Input)) (available : s.pending.Perm (p :: q :: rest))
    (pDue : Earliest le p (q :: rest)) (qDue : Earliest le q (p :: rest))
    (ne : p ≠ q) (room : MarkFeedback.Exclusive C.model s ∨ MarkFeedback.Separated C.model d s) :
    let a := MarkFeedback.process C.model d s p (q :: rest) 0
    let b := MarkFeedback.process C.model d s q (p :: rest) 0
    let pa := rest ++ MarkFeedback.emitted C.model p (MarkFeedback.read C.model d s p 0)
    let qb := rest ++ MarkFeedback.emitted C.model q (MarkFeedback.read C.model d s q 0)
    Earliest le q pa ∧ Earliest le p qb ∧
      AutonomousFeedback.Schedule.Equivalent
        (MarkFeedback.process C.model d a q pa 0)
        (MarkFeedback.process C.model d b p qb 0) := by
  dsimp only
  have remains (older newer : Occurrence Date Input)
      (first : Earliest le newer (older :: rest)) (fire : Bool) :
      Earliest le newer (rest ++ MarkFeedback.emitted C.model older fire) := by
    intro x mem
    rcases List.mem_append.mp mem with tail | child
    · exact first x (List.mem_cons_of_mem _ tail)
    · cases fire
      · simp [MarkFeedback.emitted] at child
      · exact trans (first older (by simp))
          (causal older x (by simpa [MarkFeedback.emitted, Calendar.model] using child))
  refine ⟨remains p q qDue _, remains q p pDue _, ?_⟩
  apply MarkFeedback.two_occurrences_commute
  · exact MarkFeedback.read_stable C.model d s room available ne
  · exact MarkFeedback.read_stable C.model d s room
      (available.trans (List.Perm.swap _ _ _)) ne.symm

/-- A sufficient causal condition for calendar order along a trace. Every
descendant becomes due no earlier than the probe that issued it. -/
theorem Trace.chronological {C : Calendar N Date Input} {d le s word u}
    (causal : ∀ p q, q ∈ C.route p → le p.due q.due)
    (trace : Trace C d le s word u) (trans : ∀ {a b c}, le a b → le b c → le a c) :
    word.Pairwise (fun a b => le a.1.due b.1.due) := by
  have ordered {s word u} (trace : Trace C d le s word u) :
      word.Pairwise (fun a b => le a.1.due b.1.due) ∧
      ∀ a, (∀ p ∈ s.pending, le a p.due) → ∀ q ∈ word, le a q.1.due := by
    induction trace with
    | nil => exact ⟨.nil, by simp⟩
    | @cons current last p rest available earliest lo hi error within room decisions tail ih =>
      let fire := MarkFeedback.read C.model d current p error
      have next : ∀ q ∈ rest ++ MarkFeedback.emitted C.model p fire, le p.due q.due := by
        intro q mem
        rcases List.mem_append.mp mem with inRest | issued
        · exact earliest q inRest
        · cases hf : fire with
          | false => simp [MarkFeedback.emitted, hf] at issued
          | true => exact causal p q (by simpa [MarkFeedback.emitted, hf, Calendar.model] using issued)
      refine ⟨List.pairwise_cons.mpr ⟨ih.2 p.due next, ih.1⟩, ?_⟩
      intro a lower q mem
      have before := lower p (available.mem_iff.mpr (by simp))
      rcases List.mem_cons.mp mem with rfl | inTail
      · exact before
      · exact trans before (ih.2 p.due next q inTail)
  exact (ordered trace).1

/-- Memory safety and common terminal counts for dated admissions follow
from the same footprint certificate and diamond as the MARK model. The
diamond must hold on the whole reachable MARK system, including alternative
orders. No time spacing is needed to keep a fixed calendar phase unchanged. -/
theorem network_memory (Q d B rail W eta : Nat) {N : Nat} {Date Input : Type}
    (C : Calendar N Date Input) (seed : List (Occurrence Date Input))
    (cert : MarkFeedback.Reserve Q C.model seed)
    (base : Fin (3 * N) → Nat) (initialBound : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (diamond : MarkFeedback.Admissible C.model d (MarkFeedback.initial N seed))
    (le : Date → Date → Prop) (lo hi : Nat → Int) :
    (∀ s word, Trace C d le (MarkFeedback.initial N seed) word s → SafeMemory Q d B rail base s) ∧
    (∀ error n, SafeMemory Q d B rail base (MarkFeedback.fifo C.model d error (MarkFeedback.initial N seed) n)) ∧
    (∀ s word, Trace C d le (MarkFeedback.initial N seed) word s → ∀ i : Fin N,
      s.writes (Address.mk i .port0).encode + s.writes (Address.mk i .port1).encode +
        s.writes (Address.mk i .recovery).encode ≤ 3 * Q) ∧
    (∀ error, ∃ counts, MarkFeedback.Stabilizes (MarkFeedback.fifo C.model d error (MarkFeedback.initial N seed)) counts) ∧
    (∀ error n, (∀ k, lo k ≤ error k ∧ error k ≤ hi k) →
      MarkFeedback.NominalMargins C.model d lo hi (MarkFeedback.initial N seed) n →
      MarkFeedback.fifo C.model d error (MarkFeedback.initial N seed) n =
        MarkFeedback.fifo C.model d (fun _ => 0) (MarkFeedback.initial N seed) n) ∧
    (∀ state : Nat → Config (3 * N) (Occurrence Date Input), state 0 = MarkFeedback.initial N seed →
      (∀ n, ∃ word, Trace C d le (state n) word (state (n + 1))) →
      ∃ counts, MarkFeedback.Stabilizes state counts) ∧
    MarkFeedback.WriteFair C.model d (MarkFeedback.fifo C.model d (fun _ => 0) (MarkFeedback.initial N seed)) ∧
    (∀ state : Nat → Config (3 * N) (Occurrence Date Input), state 0 = MarkFeedback.initial N seed →
      (∀ n, ∃ word, Trace C d le (state n) word (state (n + 1))) →
      MarkFeedback.WriteFair C.model d state → ∃ counts, MarkFeedback.Stabilizes state counts ∧
        MarkFeedback.Stabilizes (MarkFeedback.fifo C.model d (fun _ => 0) (MarkFeedback.initial N seed)) counts) ∧
    (MarkFeedback.Rank W eta C.model seed →
      (∀ error, (MarkFeedback.fifo C.model d error (MarkFeedback.initial N seed) (W * N)).pending = []) ∧
      ∀ a b wordA wordB, Trace C d le (MarkFeedback.initial N seed) wordA a →
        Trace C d le (MarkFeedback.initial N seed) wordB b →
        a.pending = [] → b.pending = [] → a.writes = b.writes) := by
  obtain ⟨safe, fifoSafe, cellBound, freezes, margins, sampled, fair, limits, terminal⟩ :=
    MarkFeedback.network_memory Q d B rail W eta C.model seed cert base initialBound headroom diamond lo hi
  refine ⟨fun s _ h => safe s h.certified, fifoSafe, fun s _ h => cellBound s h.certified,
    freezes, margins, ?_, fair, ?_, ?_⟩
  · intro state start steps
    exact sampled state start (fun n => by obtain ⟨_, h⟩ := steps n; exact h.certified)
  · intro state start steps fairState
    exact limits state start (fun n => by obtain ⟨_, h⟩ := steps n; exact h.certified) fairState
  · intro rank
    obtain ⟨drains, unique⟩ := terminal rank
    exact ⟨drains, fun _ _ _ _ a b => unique _ _ a.certified b.certified⟩

/-- The admission phase is stable in a time window if it misses every
phase boundary. This uses a half-open convention at the reopening date. -/
def afterReopen (le : Date → Date → Prop) [DecidableRel le] (reopen due : Date) : Phase :=
  if le reopen due then .ready else .slow

theorem phase_window {le : Date → Date → Prop} [DecidableRel le] {lower upper reopen : Date}
    (trans : ∀ {a b c}, le a b → le b c → le a c)
    (room : le reopen lower ∨ ¬ le reopen upper) :
    ∃ phase, ∀ t, le lower t → le t upper → afterReopen le reopen t = phase := by
  rcases room with ready | busy
  · exact ⟨.ready, fun _ lo _ => ite_eq_left (trans ready lo)⟩
  · exact ⟨.slow, fun _ _ hi => ite_eq_right (fun reopened => busy (trans reopened hi))⟩


/- A timed mode transition may race a read. The scheduler is allowed to
choose either pending occurrence when it has the same date as the other. -/
namespace ReopenRace

inductive Action
  | reopen
  | probe
  deriving DecidableEq

def time (probeTime : Nat) : Action → Nat
  | .reopen => 1
  | .probe => probeTime

structure State where
  pending : List Action
  phase : Phase
  recovery : Nat

def initial : State := ⟨[.reopen, .probe], .slow, 0⟩

def process (s : State) (event : Action) (rest : List Action) : State :=
  match event with
  | .reopen => ⟨rest, .ready, s.recovery⟩
  | .probe => ⟨rest, s.phase, s.recovery + if s.phase = .slow then 1 else 0⟩

inductive Move (probeTime : Nat) : State → State → Prop where
  | select (s : State) (p : Action) (rest : List Action)
      (pending : s.pending.Perm (p :: rest))
      (due : ∀ q ∈ rest, time probeTime p ≤ time probeTime q) :
      Move probeTime s (process s p rest)

inductive Path (probeTime : Nat) : State → State → Prop where
  | nil (s) : Path probeTime s s
  | cons {s t u} : Move probeTime s t → Path probeTime t u → Path probeTime s u

theorem move_shortens {probeTime : Nat} {s t : State} (step : Move probeTime s t) :
    t.pending.length + 1 = s.pending.length := by
  cases step with
  | select p rest pending due =>
    have size := pending.length_eq
    cases p <;> simpa [process, Nat.add_comm] using size.symm

/-- Reopening and a protected probe due at the same date give two legal
terminal orders. The unit write budget and finite queue hold in both. -/
theorem coincident_reopening_different_memory :
    ∃ a b, Path 1 initial a ∧ Path 1 initial b ∧
      a.pending = [] ∧ b.pending = [] ∧ a.recovery = 0 ∧ b.recovery = 1 := by
  let a := process (process initial .reopen [.probe]) .probe []
  let b := process (process initial .probe [.reopen]) .reopen []
  refine ⟨a, b, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact .cons (.select initial .reopen [.probe] (List.Perm.refl _) (by simp [time]))
      (.cons (.select _ .probe [] (List.Perm.refl _) (by simp)) (.nil _))
  · exact .cons (.select initial .probe [.reopen] (List.Perm.swap _ _ _) (by simp [time]))
      (.cons (.select _ .reopen [] (List.Perm.refl _) (by simp)) (.nil _))

theorem strict_gap_forces_same_first_action {probeTime : Nat} (gap : probeTime ≠ 1)
    {a b : State} (left : Move probeTime initial a) (right : Move probeTime initial b) :
    a.phase = b.phase ∧ a.recovery = b.recovery := by
  cases left with
  | select p rest pending due =>
    cases right with
    | select q other available due' =>
      have singleton {x : Action} {tail : List Action} (perm : tail.Perm [x]) : tail = [x] := by
        have len := perm.length_eq
        cases tail with
        | nil => simp at len
        | cons z zs =>
          cases zs with
          | nil =>
            have mem := perm.mem_iff.mp (show z ∈ [z] by simp)
            simpa using mem
          | cons _ _ => simp at len
      have line (x : Action) (tail : List Action) (perm : initial.pending.Perm (x :: tail)) :
          (x = .reopen ∧ tail = [.probe]) ∨ (x = .probe ∧ tail = [.reopen]) := by
        cases x with
        | reopen =>
          exact Or.inl ⟨rfl, singleton perm.cons_inv.symm⟩
        | probe =>
          exact Or.inr ⟨rfl, singleton ((List.Perm.swap _ _ _).trans perm).cons_inv.symm⟩
      rcases line p rest pending with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases line q other available with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · have h := due .probe (by simp)
        have h' := due' .reopen (by simp)
        exact (gap (Nat.le_antisymm h' h)).elim
      · have h := due .reopen (by simp)
        have h' := due' .probe (by simp)
        exact (gap (Nat.le_antisymm h h')).elim
      · exact ⟨rfl, rfl⟩

end ReopenRace
end NetworkStability.PhaseAdmission
