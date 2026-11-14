import NativeMultiTokenTarget

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid PhaseAdmission
open scoped List

/-- The native queue accounts for each admission and each child of an
actual FIRE, including when a prefix stops between same-date jumps. -/
theorem native_prefix_balance {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) :
    (u.pending ++ run.deliveries).Perm
      (s.pending ++ run.ledger.emissions.flatMap (fun e => route e.1 e.2)) := by
  induction run with
  | nil => simp [Execution.deliveries, Execution.ledger, Ledger.zero]
  | @cons source cut target step rest ih =>
    have head : (cut.pending ++ step.deliveries).Perm
        (source.pending ++ step.ledger.emissions.flatMap (fun e => route e.1 e.2)) := by
      cases step with
      | flow f =>
        simp [Move.deliveries, Move.ledger, Flow.ledger, f.queue_fixed]
      | jump j =>
        cases j with
        | arrive d before after queue due free =>
          change ((before ++ after) ++ [d]).Perm (_ ++ [])
          rw [List.append_nil, queue]
          simp only [List.append_assoc]
          exact (List.perm_append_singleton d after).append_left before
        | fire i mode guard => simp [Move.deliveries, Jump.deliveries, Move.ledger, Jump.ledger]
        | _ => simp [Move.deliveries, Jump.deliveries, Move.ledger, Jump.ledger, Ledger.zero,
            setMain, setAux, setRaw]
    change (_ ++ (step.deliveries ++ rest.deliveries)).Perm
      (_ ++ (step.ledger.emissions ++ rest.ledger.emissions).flatMap (fun e => route e.1 e.2))
    rw [List.flatMap_append]
    calc
      _ ~ (_ ++ rest.deliveries) ++ step.deliveries := by
        rw [List.append_assoc]
        exact (List.perm_append_comm (l₁ := step.deliveries) (l₂ := rest.deliveries)).append_left _
      _ ~ (_ ++ rest.ledger.emissions.flatMap (fun e => route e.1 e.2)) ++ step.deliveries :=
        ih.append_right _
      _ ~ (_ ++ step.deliveries) ++ rest.ledger.emissions.flatMap (fun e => route e.1 e.2) := by
        simp only [List.append_assoc]
        exact (List.perm_append_comm (l₁ := rest.ledger.emissions.flatMap (fun e => route e.1 e.2))
          (l₂ := step.deliveries)).append_left _
      _ ~ _ := by
        rw [← List.append_assoc]
        exact head.append_right _

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
  have matches : NativeReciprocal.nativeAdmissions head = consumed.map rowAdmission := by
    dsimp only [consumed]
    rw [List.map_take, admitted, split, admissions_append, ← length, List.take_left]
  have intake : consumed.map (fun r => toDelivery r.probe) = head.deliveries := by
    rw [← NativeReciprocal.admissions_deliveries head, matches, List.map_map]
    rfl
  obtain ⟨mid, first, rest⟩ := replay_take_drop replay head.deliveries.length
  obtain ⟨children, noReceipt, settled⟩ := cuts cut head tail split
  exact ⟨mid, matches, first, rest, prefix_unissued_balance head first intake children,
    noReceipt, settled mid first⟩

/-- The child of every matched launch belongs to the issued or unissued
part according to whether the launch FIRE is in the native prefix. -/
theorem issued_unissued_partition {p : Parameters N} {rows : List (Row N)}
    (matches : ∀ r ∈ rows, RowMatches p r)
    (fires : List (Fin N × ℝ))
    (uniqueFires : fires.Nodup) (uniqueRows : (Transaction.fires inputCell rows).Nodup)
    (seen : ∀ e ∈ fires, e ∈ Transaction.fires inputCell rows) :
    (rows.flatMap (fun row => row.children.map toDelivery)).Perm
      (fires.flatMap (fun e => router p e.1 e.2) ++ unissued rows fires) := by
  classical
  let planned := Transaction.fires inputCell rows
  let issue := fun e : Fin N × ℝ => router p e.1 e.2
  let fired := fun e : Fin N × ℝ => decide (e ∈ fires)
  have plannedExact : rows.flatMap (fun r => r.children.map toDelivery) = planned.flatMap issue := by
    dsimp only [planned]
    clear uniqueFires uniqueRows seen
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      have good := matches row (List.mem_cons_self)
      have children := good.2.2.2.2
      have restExact := ih (fun row mem => matches row (List.mem_cons_of_mem _ mem))
      cases date : row.fireDate with
      | none => simp [Transaction.fires, issue, children, date, ← restExact]
      | some time => simp [Transaction.fires, issue, children, inputCell, date, ← restExact]
  have unissuedExact : unissued rows fires = (planned.filter (fun e => !fired e)).flatMap issue := by
    dsimp only [planned]
    clear uniqueFires uniqueRows seen
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      have good := matches row (List.mem_cons_self)
      have children := good.2.2.2.2
      have restExact := ih (fun row mem => matches row (List.mem_cons_of_mem _ mem))
      cases date : row.fireDate with
      | none => simp [unissued, Transaction.fires, date, ← restExact]
      | some time =>
        by_cases mem : (row.probe.input.1, time) ∈ fires <;>
          simp [unissued, Transaction.fires, issue, fired, inputCell, children, date, mem, ← restExact]
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
