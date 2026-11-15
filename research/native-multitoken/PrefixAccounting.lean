import NativeMultiTokenTarget
import KernelR.HybridInputBalance

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid PhaseAdmission
open scoped List

/-- The native queue accounts for each admission and each child of an
actual FIRE, including when a prefix stops between same-date jumps. -/
theorem native_prefix_balance {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) :
    (u.pending ++ run.deliveries).Perm
      (s.pending ++ run.ledger.emissions.flatMap (fun e => route e.1 e.2)) := by
  apply Multiset.coe_eq_coe.mp
  simpa only [← Multiset.coe_add] using run.token_balance

/-- An abstract replay queues a row's children when the row is admitted. -/
theorem guarded_prefix_balance {p : Parameters N} {s u : State N} {rows : List (Row N)}
    (replay : TransactionReplay (calendar p) d (· ≤ ·) s rows u) :
    ((u.pending.map toDelivery) ++ rows.map (fun r => toDelivery r.probe)).Perm
      ((s.pending.map toDelivery) ++ rows.flatMap (fun r => r.children.map toDelivery)) := by
  induction replay with
  | nil s => simp
  | @cons s next u tx rest selected earliest interval room decision children queue dose rows tail ih =>
    have head : (next.pending.map toDelivery ++ [toDelivery tx.probe]).Perm
        (s.pending.map toDelivery ++ tx.children.map toDelivery) := by
      rw [queue, List.map_append]
      calc
        _ ~ rest.map toDelivery ++ toDelivery tx.probe :: tx.children.map toDelivery := by
          rw [List.append_assoc]
          exact (List.perm_append_singleton _ _).append_left _
        _ ~ (toDelivery tx.probe :: rest.map toDelivery) ++ tx.children.map toDelivery := by
          exact List.perm_middle
        _ ~ _ := (selected.map toDelivery).symm.append_right _
    change ((u.pending.map toDelivery) ++ toDelivery tx.probe :: rows.map (fun r => toDelivery r.probe)).Perm
      ((s.pending.map toDelivery) ++ (tx.children.map toDelivery ++ rows.flatMap fun r => r.children.map toDelivery))
    calc
      _ ~ (u.pending.map toDelivery ++ rows.map (fun r => toDelivery r.probe)) ++ [toDelivery tx.probe] := by
        rw [List.append_assoc]
        exact (List.perm_append_singleton _ _).symm.append_left _
      _ ~ (next.pending.map toDelivery ++ rows.flatMap (fun r => r.children.map toDelivery)) ++ [toDelivery tx.probe] :=
        ih.append_right _
      _ ~ (next.pending.map toDelivery ++ [toDelivery tx.probe]) ++ rows.flatMap (fun r => r.children.map toDelivery) := by
        simp only [List.append_assoc]
        exact List.perm_append_comm.append_left _
      _ ~ _ := by
        rw [← List.append_assoc]
        exact head.append_right _

/-- Cancel the consumed tokens from both ledgers. The only difference is
the list of children that were queued abstractly but have yet to FIRE. -/
theorem prefix_unissued_balance {p : Parameters N} {u : Snapshot N}
    (head : Execution (nativeParameters N) (router p) (prepared p) u)
    {rows : List (Row N)} {mid : State N}
    (replay : TransactionReplay (calendar p) d (· ≤ ·)
      (MarkFeedback.initial N (seed p)) rows mid)
    (intake : rows.map (fun r => toDelivery r.probe) = head.deliveries)
    (children : (rows.flatMap (fun r => r.children.map toDelivery)).Perm
      (head.ledger.emissions.flatMap (fun e => router p e.1 e.2) ++ unissued rows head.ledger.emissions)) :
    (mid.pending.map toDelivery).Perm (u.pending ++ unissued rows head.ledger.emissions) := by
  have real := native_prefix_balance head
  have abstract := guarded_prefix_balance replay
  rw [intake] at abstract
  have credit := children.append_left ((seed p).map toDelivery)
  have total : (mid.pending.map toDelivery ++ head.deliveries).Perm
      ((u.pending ++ head.deliveries) ++ unissued rows head.ledger.emissions) := by
    apply abstract.trans
    have step := real.symm.append_right (unissued rows head.ledger.emissions)
    exact credit.trans (by simpa only [prepared, List.append_assoc] using step)
  apply (List.perm_append_right_iff head.deliveries).mp
  refine total.trans ?_
  simp only [List.append_assoc]
  exact List.perm_append_comm.append_left _

private theorem replay_take_drop {p : Parameters N} {s u : State N} {rows : List (Row N)}
    (replay : TransactionReplay (calendar p) d (· ≤ ·) s rows u) (n : Nat) :
    ∃ mid : State N,
      TransactionReplay (calendar p) d (· ≤ ·) s (rows.take n) mid ∧
      TransactionReplay (calendar p) d (· ≤ ·) mid (rows.drop n) u := by
  induction replay generalizing n with
  | nil s => exact ⟨s, by simp; exact .nil s, by simp; exact .nil s⟩
  | @cons s next u tx rest select first interval room decision children queue dose rows tail ih =>
    cases n with
    | zero => exact ⟨s, .nil s, .cons tx rest select first interval room decision children queue dose tail⟩
    | succ n =>
      obtain ⟨mid, head, suffix⟩ := ih n
      exact ⟨mid, .cons tx rest select first interval room decision children queue dose head, suffix⟩

private theorem admissions_append {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u v : Snapshot N} (head : Execution θ route s u) (tail : Execution θ route u v) :
    NativeReciprocal.nativeAdmissions (head.append tail) =
      NativeReciprocal.nativeAdmissions head ++ NativeReciprocal.nativeAdmissions tail := by
  induction head with
  | nil => rfl
  | cons move rest ih =>
    simp only [Execution.append, NativeReciprocal.nativeAdmissions, ih, List.append_assoc]

/-- Given the dated event and settled-cut certificates, replay and physical
queue conservation prove the frozen prefix correspondence at every cut of
the actual execution. The cut can be between two jumps at the same date. -/
theorem prefix_correspondence_of_cuts {p : Parameters N} {last : Snapshot N}
    (run : Execution (nativeParameters N) (router p) (prepared p) last)
    {rows : List (Row N)} {out : State N}
    (replay : TransactionReplay (calendar p) d (· ≤ ·)
      (MarkFeedback.initial N (seed p)) rows out)
    (admitted : rows.map rowAdmission = NativeReciprocal.nativeAdmissions run)
    (cuts : ∀ (cut : Snapshot N)
      (head : Execution (nativeParameters N) (router p) (prepared p) cut)
      (tail : Execution (nativeParameters N) (router p) cut last),
      run = head.append tail →
      let consumed := rows.take head.deliveries.length
      (consumed.flatMap (fun row => row.children.map toDelivery)).Perm
        (head.ledger.emissions.flatMap (fun e => router p e.1 e.2) ++
          unissued consumed head.ledger.emissions) ∧
      (head.ledger.emissions.length < N → ∀ row ∈ consumed, row.probe.input.2 ≠ .receipt) ∧
      (∀ mid, TransactionReplay (calendar p) d (· ≤ ·)
        (MarkFeedback.initial N (seed p)) consumed mid →
        (cut.time = firstDate + 15 / 2 ∨ cut.time = secondDate p + 15 / 2) →
          SettledMemory p cut mid)) :
    prefixCorrespondence p run rows out := by
  intro cut head tail split
  let consumed := rows.take head.deliveries.length
  have length : (NativeReciprocal.nativeAdmissions head).length = head.deliveries.length := by
    have h := congrArg List.length (NativeReciprocal.admissions_deliveries head)
    simpa only [List.length_map] using h
  have matching : NativeReciprocal.nativeAdmissions head = consumed.map rowAdmission := by
    dsimp only [consumed]
    rw [List.map_take, admitted, split, admissions_append, ← length, List.take_left]
  have intake : consumed.map (fun r => toDelivery r.probe) = head.deliveries := by
    rw [← NativeReciprocal.admissions_deliveries head, matching, List.map_map]
    rfl
  obtain ⟨mid, first, rest⟩ := replay_take_drop replay head.deliveries.length
  obtain ⟨children, noReceipt, settled⟩ := cuts cut head tail split
  exact ⟨mid, matching, first, rest, prefix_unissued_balance head first intake children,
    noReceipt, settled mid first⟩

/-- A consumed receipt is later than the entire FIRE wave. Therefore the
native prefix already contains the complete ordered FIRE word. -/
theorem prefix_fires_before_receipt {p : Parameters N} {cut last : Snapshot N}
    (head : Execution (nativeParameters N) (router p) (prepared p) cut)
    (tail : Execution (nativeParameters N) (router p) cut last)
    {rows : List (Row N)} (clock : ℝ)
    (admitted : rows.map rowAdmission = NativeReciprocal.nativeAdmissions (head.append tail))
    (early : ∀ fire ∈ (head.append tail).ledger.emissions, fire.2 ≤ clock)
    (late : ∀ row ∈ rows, row.probe.input.2 = .receipt → clock < row.probe.due)
    (row : Row N) (mem : row ∈ rows.take head.deliveries.length)
    (receipt : row.probe.input.2 = .receipt) :
    head.ledger.emissions = (head.append tail).ledger.emissions := by
  have count : (NativeReciprocal.nativeAdmissions head).length = head.deliveries.length := by
    simpa only [List.length_map] using congrArg List.length (NativeReciprocal.admissions_deliveries head)
  have prefixWord : (rows.take head.deliveries.length).map rowAdmission = NativeReciprocal.nativeAdmissions head := by
    rw [List.map_take, admitted, admissions_append, ← count, List.take_left]
  have token : toDelivery row.probe ∈ head.deliveries := by
    rw [← NativeReciprocal.admissions_deliveries head, ← prefixWord, List.map_map]
    exact List.mem_map.mpr ⟨row, mem, rfl⟩
  have after : clock < cut.time :=
    (late row (List.mem_of_mem_take mem) receipt).trans_le (head.delivery_time_bounds _ token).2
  have drained : tail.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event member
    have before := early event (by rw [Execution.emissions_append]; exact List.mem_append_right _ member)
    exact (not_lt_of_ge ((tail.emission_time_bounds _ member).1.trans before)) after
  rw [Execution.emissions_append, drained, List.append_nil]

theorem planned_children_word {p : Parameters N} {rows : List (Row N)}
    (matching : ∀ r ∈ rows, RowMatches p r) :
    rows.flatMap (fun r => r.children.map toDelivery) =
      (Transaction.fires inputCell rows).flatMap (fun e => router p e.1 e.2) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have children := (matching row List.mem_cons_self).2.2.2.2
    have restExact := ih (fun row mem => matching row (List.mem_cons_of_mem _ mem))
    cases date : row.fireDate with
    | none => simp [Transaction.fires, children, date]; exact restExact
    | some time => simp [Transaction.fires, children, inputCell, date]; exact restExact

/-- The child of every matched launch belongs to the issued or unissued
part according to whether the launch FIRE is in the native prefix. -/
theorem issued_unissued_partition {p : Parameters N} {rows : List (Row N)}
    (matching : ∀ r ∈ rows, RowMatches p r)
    (fires : List (Fin N × ℝ))
    (uniqueFires : fires.Nodup) (uniqueRows : (Transaction.fires inputCell rows).Nodup)
    (seen : ∀ e ∈ fires, e ∈ Transaction.fires inputCell rows) :
    (rows.flatMap (fun row => row.children.map toDelivery)).Perm
      (fires.flatMap (fun e => router p e.1 e.2) ++ unissued rows fires) := by
  classical
  let planned := Transaction.fires inputCell rows
  let issue := fun e : Fin N × ℝ => router p e.1 e.2
  let fired := fun e : Fin N × ℝ => decide (e ∈ fires)
  have plannedExact : rows.flatMap (fun r => r.children.map toDelivery) = planned.flatMap issue :=
    planned_children_word matching
  have unissuedExact : unissued rows fires = (planned.filter (fun e => !fired e)).flatMap issue := by
    dsimp only [planned]
    clear uniqueFires uniqueRows seen plannedExact
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      have good := matching row (List.mem_cons_self)
      have children := good.2.2.2.2
      have restExact := ih (fun row mem => matching row (List.mem_cons_of_mem _ mem))
      cases date : row.fireDate with
      | none => simp [unissued, Transaction.fires, date]; exact restExact
      | some time =>
        by_cases mem : (row.probe.input.1, time) ∈ fires <;>
          (simp [unissued, Transaction.fires, issue, fired, inputCell, children, date, mem]; exact restExact)
  have issuedExact : (planned.filter fired).Perm fires := by
    apply (List.perm_ext_iff_of_nodup (uniqueRows.filter _) uniqueFires).mpr
    intro e
    change e ∈ planned.filter fired ↔ e ∈ fires
    rw [List.mem_filter]
    simp only [fired, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨seen e h, h⟩⟩
  rw [plannedExact, unissuedExact]
  have partition := (List.filter_append_perm fired planned).symm.flatMap_right issue
  rw [List.flatMap_append] at partition
  exact partition.trans ((issuedExact.flatMap_right issue).append_right _)

end NetworkStability.NativeMultiToken
