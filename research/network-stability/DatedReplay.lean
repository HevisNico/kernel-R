import PhaseAdmission

namespace NetworkStability.PhaseAdmission

open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address)

theorem Trace.append {C : Calendar N Date Input} {d le s t u left right}
    (first : Trace C d le s left t) (last : Trace C d le t right u) :
    Trace C d le s (left ++ right) u := by
  induction first with
  | nil => exact last
  | cons p rest available earliest lo hi error within room _ ih =>
    exact .cons p rest available earliest lo hi error within room (ih last)

/-- Data for replaying an already certified transaction. The native clock
for FIRE is retained separately from the admission clock. -/
structure Transaction (Date Input : Type) where
  probe : Occurrence Date Input
  fireDate : Option Date
  children : List (Occurrence Date Input)
  lo : Int
  hi : Int

def Transaction.decision (tx : Transaction Date Input) : Bool := tx.fireDate.isSome

def Transaction.word (rows : List (Transaction Date Input)) :
    List (Occurrence Date Input × Bool) :=
  rows.map fun tx => (tx.probe, tx.decision)

def Transaction.fires (cell : Input → Fin N) (rows : List (Transaction Date Input)) :
    List (Fin N × Date) :=
  rows.filterMap fun tx => tx.fireDate.map (fun t => (cell tx.probe.input, t))

/-- A transaction certificate checks the actual remainder of the queue,
the logged children, the margin, and the normalized per-coordinate dose. -/
inductive TransactionReplay (C : Calendar N Date Input) (d : Nat) (le : Date → Date → Prop) :
    Config (3 * N) (Occurrence Date Input) → List (Transaction Date Input) →
      Config (3 * N) (Occurrence Date Input) → Prop where
  | nil (s) : TransactionReplay C d le s [] s
  | cons {s next u : Config (3 * N) (Occurrence Date Input)}
      (tx : Transaction Date Input) (rest : List (Occurrence Date Input))
      (selected : s.pending.Perm (tx.probe :: rest)) (earliest : Earliest le tx.probe rest)
      (interval : tx.lo ≤ 0 ∧ 0 ≤ tx.hi)
      (room : RoutedCalendar.HasRoom (MarkFeedback.score C.model d s tx.probe) tx.lo tx.hi)
      (decision : MarkFeedback.read C.model d s tx.probe 0 = tx.decision)
      (children : MarkFeedback.emitted C.model tx.probe tx.decision = tx.children)
      (queue : next.pending = rest ++ tx.children)
      (dose : ∀ i, next.writes i = s.writes i + MarkFeedback.footprint C.model tx.probe tx.decision i)
      {rows} (tail : TransactionReplay C d le next rows u) :
      TransactionReplay C d le s (tx :: rows) u

theorem TransactionReplay.trace {C : Calendar N Date Input} {d le s rows u}
    (replay : TransactionReplay C d le s rows u) :
    Trace C d le s (Transaction.word rows) u := by
  induction replay with
  | nil => exact .nil _
  | @cons s next u tx rest selected earliest interval room decision children queue dose rows tail ih =>
    have successor : MarkFeedback.process C.model d s tx.probe rest 0 = next := by
      cases next
      simp only [MarkFeedback.process, decision, children]
      congr 1
      · exact queue.symm
      · exact funext (fun i => (dose i).symm)
    have clean := Trace.cons tx.probe rest selected earliest tx.lo tx.hi 0 interval room
      (show Trace C d le (MarkFeedback.process C.model d s tx.probe rest 0) _ u from successor.symm ▸ ih)
    simpa only [Transaction.word, List.map_cons, decision] using clean

theorem TransactionReplay.append {C : Calendar N Date Input} {d le s t u left right}
    (first : TransactionReplay C d le s left t) (last : TransactionReplay C d le t right u) :
    TransactionReplay C d le s (left ++ right) u := by
  induction first with
  | nil => exact last
  | cons tx rest selected earliest interval room decision children queue dose _ ih =>
    exact .cons tx rest selected earliest interval room decision children queue dose (ih last)

/-- The explicit horizon queue may contain future work. This gives strict
headroom and the nominal error replay for the segment up to the cut. The
terminal uniqueness premise remains an empty abstract queue. -/
theorem replay_network_memory (Q d B rail W eta : Nat) {N : Nat} {Date Input : Type}
    (C : Calendar N Date Input) (seed : List (Occurrence Date Input))
    (reserve : MarkFeedback.Reserve Q C.model seed)
    (base : Fin (3 * N) → Nat) (initialBound : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (diamond : MarkFeedback.Admissible C.model d (MarkFeedback.initial N seed))
    (le : Date → Date → Prop) {u rows}
    (replay : TransactionReplay C d le (MarkFeedback.initial N seed) rows u) :
    SafeMemory Q d B rail base u ∧
      NominalTrace C d le (MarkFeedback.initial N seed) (Transaction.word rows) u ∧
      ∀ i : Fin N, u.writes (Address.mk i .port0).encode + u.writes (Address.mk i .port1).encode +
        u.writes (Address.mk i .recovery).encode ≤ 3 * Q := by
  obtain ⟨safe, _, cell, _, _, _, _, _, _⟩ := network_memory Q d B rail W eta C seed reserve base
    initialBound headroom diamond le (fun _ => 0) (fun _ => 0)
  exact ⟨safe _ _ replay.trace, replay.trace.zero_error_replay, cell _ _ replay.trace⟩

/-- Retain every occurrence at or before the comparison horizon. -/
noncomputable def horizonCut {Date Input : Type} {N : Nat} (le : Date → Date → Prop)
    (horizon : Date) (s : Config (3 * N) (Occurrence Date Input)) :
    Config (3 * N) (Occurrence Date Input) :=
  ⟨s.pending.filter (fun p => @decide (le p.due horizon) (Classical.propDecidable _)), s.writes⟩

theorem horizonCut_empty {Date Input : Type} {N : Nat} {le : Date → Date → Prop}
    {horizon : Date} {s : Config (3 * N) (Occurrence Date Input)}
    (future : ∀ p ∈ s.pending, ¬ le p.due horizon) :
    (horizonCut le horizon s).pending = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p mem
  rcases List.mem_filter.mp mem with ⟨queued, inside⟩
  exact future p queued (of_decide_eq_true inside)

/-- Truncation is applied to the initial queue and to every batch of
children. It keeps the read law and its write footprint. -/
noncomputable def Calendar.through (C : Calendar N Date Input) (le : Date → Date → Prop)
    (horizon : Date) : Calendar N Date Input :=
  { C with route := fun p => (C.route p).filter (
      fun q => @decide (le q.due horizon) (Classical.propDecidable _)) }

/-- Every step inside a horizon survives queue clipping with the same
decision word and writes. No assumption about the number of later
occurrences is needed. -/
theorem Trace.through {C : Calendar N Date Input} {d le s word u} (horizon : Date)
    (replay : Trace C d le s word u) (within : ∀ row ∈ word, le row.1.due horizon) :
    Trace (C.through le horizon) d le (horizonCut le horizon s) word (horizonCut le horizon u) := by
  classical
  let keep : Occurrence Date Input → Bool := fun p => decide (le p.due horizon)
  induction replay with
  | nil => exact .nil _
  | @cons s u p rest selected earliest lo hi error errorWithin room word tail ih =>
    have kept : keep p = true := decide_eq_true (within (p, MarkFeedback.read C.model d s p error) (List.mem_cons_self ..))
    have queue : (horizonCut le horizon s).pending.Perm (p :: rest.filter keep) := by
      simpa only [horizonCut, List.filter_cons, kept, ite_true] using selected.filter keep
    have first : Earliest le p (rest.filter keep) := fun q h => earliest q ((List.mem_filter.mp h).1)
    have score : MarkFeedback.score (C.through le horizon).model d (horizonCut le horizon s) p =
        MarkFeedback.score C.model d s p := rfl
    have fire : MarkFeedback.read (C.through le horizon).model d (horizonCut le horizon s) p error =
        MarkFeedback.read C.model d s p error := by rw [MarkFeedback.read, score]; rfl
    have next : MarkFeedback.process (C.through le horizon).model d (horizonCut le horizon s) p
        (rest.filter keep) error = horizonCut le horizon (MarkFeedback.process C.model d s p rest error) := by
      unfold MarkFeedback.process
      rw [fire]
      cases MarkFeedback.read C.model d s p error <;>
        simp only [MarkFeedback.emitted, Bool.false_eq_true, ite_false, ite_true, horizonCut,
          Calendar.through, Calendar.model, List.filter_append, List.filter_nil] <;> rfl
    have step := Trace.cons p (rest.filter keep) queue first lo hi error errorWithin
      (show RoutedCalendar.HasRoom (MarkFeedback.score (C.through le horizon).model d
        (horizonCut le horizon s) p) lo hi by rw [score]; exact room)
      (next.symm ▸ ih (fun row mem => within row (List.mem_cons_of_mem _ mem)))
    simpa only [fire] using step

/-- Once the horizon is cleared, terminal uniqueness applies to the
clipped certificate. It compares memories while preserving the actual
future queues in the unprojected executions. -/
theorem through_terminal_unique (W eta d : Nat) {N : Nat} {Date Input : Type}
    (C : Calendar N Date Input) (le : Date → Date → Prop) (horizon : Date)
    (seed : List (Occurrence Date Input))
    (rank : MarkFeedback.Rank W eta (C.through le horizon).model
      (horizonCut le horizon (MarkFeedback.initial N seed)).pending)
    (diamond : MarkFeedback.Admissible (C.through le horizon).model d
      (horizonCut le horizon (MarkFeedback.initial N seed)))
    {a b wa wb} (left : Trace C d le (MarkFeedback.initial N seed) wa a)
    (right : Trace C d le (MarkFeedback.initial N seed) wb b)
    (leftDates : ∀ row ∈ wa, le row.1.due horizon) (rightDates : ∀ row ∈ wb, le row.1.due horizon)
    (leftClear : ∀ p ∈ a.pending, ¬ le p.due horizon) (rightClear : ∀ p ∈ b.pending, ¬ le p.due horizon) :
    a.writes = b.writes := by
  exact MarkFeedback.terminal_unique W eta d (C.through le horizon).model _
    (a := horizonCut le horizon a) (b := horizonCut le horizon b)
    rank diamond (MarkFeedback.certified_projects (left.through horizon leftDates).certified)
    (MarkFeedback.certified_projects (right.through horizon rightDates).certified)
    (horizonCut_empty leftClear) (horizonCut_empty rightClear)

end NetworkStability.PhaseAdmission
