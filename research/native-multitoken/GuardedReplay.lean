import NativeMultiTokenMilestone

namespace NetworkStability.NativeMultiToken

open PhaseAdmission
open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

private theorem zero_room (score : Int) : RoutedCalendar.HasRoom score 0 0 := by
  by_cases h : 0 ≤ score
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inl ⟨by omega, by omega⟩

private theorem next_probe {queue : List (Probe N)} (nonempty : queue ≠ []) :
    ∃ probe rest, queue.Perm (probe :: rest) ∧ Earliest (· ≤ ·) probe rest := by
  classical
  have existsMin {l : List (Probe N)} (h : l ≠ []) :
      ∃ x ∈ l, ∀ y ∈ l, x.due ≤ y.due := by
    induction l with
    | nil => exact (h rfl).elim
    | cons x xs ih =>
      by_cases empty : xs = []
      · subst xs; exact ⟨x, by simp, by intro y mem; rcases List.mem_singleton.mp mem with rfl; exact le_rfl⟩
      · obtain ⟨first, member, best⟩ := ih empty
        by_cases earlier : x.due ≤ first.due
        · refine ⟨x, by simp, fun y mem => ?_⟩
          rcases List.mem_cons.mp mem with rfl | rest
          · exact le_rfl
          · exact earlier.trans (best y rest)
        · refine ⟨first, List.mem_cons_of_mem _ member, fun y mem => ?_⟩
          rcases List.mem_cons.mp mem with rfl | rest
          · exact le_of_not_ge earlier
          · exact best y rest
  obtain ⟨x, member, best⟩ := existsMin nonempty
  obtain ⟨front, tail, split⟩ := List.append_of_mem member
  refine ⟨x, front ++ tail, split ▸ List.perm_middle, ?_⟩
  intro y mem
  apply best y
  rw [split]
  exact List.mem_append.mp mem |>.elim
    (fun h => List.mem_append_left _ h) (fun h => List.mem_append_right _ (List.mem_cons_of_mem _ h))

/-- Extend any guarded configuration to a drained zero-error trace using
the same rank. This is independent of the native construction. -/
theorem guarded_drain {p : Parameters N}
    (rank : MarkFeedback.Rank W eta₀ (calendar p).model (seed p))
    (s : State N) : ∃ out word, Trace (calendar p) d (· ≤ ·) s word out ∧ out.pending = [] := by
  classical
  let mass := AutonomousFeedback.mass rank.weight
  suffices loop : ∀ k (s : State N), mass s.pending = k →
      ∃ out word, Trace (calendar p) d (· ≤ ·) s word out ∧ out.pending = [] from
    loop _ s rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s size
    by_cases done : s.pending = []
    · exact ⟨s, [], .nil s, done⟩
    · obtain ⟨probe, rest, selected, earliest⟩ := next_probe done
      let next := MarkFeedback.process (calendar p).model d s probe rest 0
      have decreases : mass next.pending < k := by
        have step := MarkFeedback.process_rank (calendar p).model d W eta₀ rank s probe rest selected 0
        change mass next.pending + 1 ≤ mass s.pending at step
        omega
      obtain ⟨out, word, trace, finished⟩ := ih _ decreases next rfl
      exact ⟨out, _, .cons probe rest selected earliest 0 0 0 (by decide)
        (zero_room _) trace, finished⟩

/-- Count writes through an ordered list of native transaction rows. -/
def writesAfter (C : Calendar N ℝ (Input N)) (rows : List (Row N))
    (before : Fin (3 * N) → Nat) : Fin (3 * N) → Nat :=
  rows.foldl (fun counts tx i =>
    counts i + MarkFeedback.footprint C.model tx.probe tx.decision i) before

/-- Check the guards against the counters at each boundary. The queue
induction can then change the order of pending occurrences freely. -/
def RowGuards (C : Calendar N ℝ (Input N)) (d : Nat) :
    List (Row N) → (Fin (3 * N) → Nat) → Prop
  | [], _ => True
  | tx :: rows, counts =>
    (tx.lo ≤ 0 ∧ 0 ≤ tx.hi) ∧
    RoutedCalendar.HasRoom (MarkFeedback.score C.model d ⟨[], counts⟩ tx.probe) tx.lo tx.hi ∧
    MarkFeedback.read C.model d ⟨[], counts⟩ tx.probe 0 = tx.decision ∧
    MarkFeedback.emitted C.model tx.probe tx.decision = tx.children ∧
    RowGuards C d rows (fun i =>
      counts i + MarkFeedback.footprint C.model tx.probe tx.decision i)

set_option maxHeartbeats 650000 in
theorem replay_from_token_budget (C : Calendar N ℝ (Input N)) (d : Nat)
    (rows : List (Row N)) (s : State N) (future : List (Probe N))
    (guards : RowGuards C d rows s.writes)
    (chronology : rows.Pairwise (fun a b => a.probe.due ≤ b.probe.due))
    (causal : ∀ tx ∈ rows, ∀ q ∈ tx.children, tx.probe.due < q.due)
    (later : ∀ tx ∈ rows, ∀ q ∈ future, tx.probe.due ≤ q.due)
    (balance : (s.pending ++ rows.flatMap Transaction.children).Perm
      (rows.map Transaction.probe ++ future)) :
    ∃ out, TransactionReplay C d (· ≤ ·) s rows out ∧
      out.pending.Perm future ∧ out.writes = writesAfter C rows s.writes := by
  induction rows generalizing s with
  | nil =>
    exact ⟨s, TransactionReplay.nil (C := C) (d := d) (le := (· ≤ ·)) s, by simpa using balance, rfl⟩
  | cons tx rows ih =>
    rcases List.pairwise_cons.mp chronology with ⟨first, ordered⟩
    have present : tx.probe ∈ s.pending := by
      have member := balance.mem_iff.mpr (show tx.probe ∈ (tx :: rows).map Transaction.probe ++ future by simp)
      rcases List.mem_append.mp member with h | children
      · exact h
      · obtain ⟨parent, occurs, child⟩ := List.mem_flatMap.mp children
        have bound : tx.probe.due ≤ parent.probe.due := by
          rcases List.mem_cons.mp occurs with rfl | tail
          · rfl
          · exact first parent tail
        exact (lt_irrefl _ (bound.trans_lt (causal parent occurs _ child))).elim
    classical
    let rest := s.pending.erase tx.probe
    have selected : s.pending.Perm (tx.probe :: rest) := List.perm_cons_erase present
    have earliest : Earliest (· ≤ ·) tx.probe rest := by
      intro q queued
      have mem := selected.mem_iff.mpr (List.mem_cons_of_mem _ queued)
      rcases List.mem_append.mp (balance.mem_iff.mp (List.mem_append_left _ mem)) with admitted | stays
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp admitted
        rcases List.mem_cons.mp ha with rfl | other
        · rfl
        · exact first a other
      · exact later tx (by simp) q stays
    rcases guards with ⟨interval, room, decision, issued, tailGuards⟩
    let next : State N :=
      ⟨rest ++ tx.children, fun i => s.writes i + MarkFeedback.footprint C.model tx.probe tx.decision i⟩
    have nextBalance : (next.pending ++ rows.flatMap Transaction.children).Perm
        (rows.map Transaction.probe ++ future) := by
      have aligned := (selected.append_right ((tx :: rows).flatMap Transaction.children)).symm.trans balance
      simpa only [List.cons_append, List.flatMap_cons, List.map_cons, List.perm_cons, List.append_assoc, next] using aligned
    obtain ⟨out, tail, queued, counts⟩ := ih next tailGuards ordered
      (fun x hx => causal x (List.mem_cons_of_mem _ hx))
      (fun x hx => later x (List.mem_cons_of_mem _ hx)) nextBalance
    have run : TransactionReplay C d (· ≤ ·) s (tx :: rows) out :=
      TransactionReplay.cons (s := s) (next := next) tx rest selected earliest interval room decision
        issued rfl (fun _ => rfl) tail
    exact ⟨out, run, queued, counts⟩

end NetworkStability.NativeMultiToken
