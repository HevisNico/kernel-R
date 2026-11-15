import GuardedExternalRows

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid PhaseAdmission
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

private theorem admissions_append {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u v : Snapshot N} (head : Execution θ route s u) (tail : Execution θ route u v) :
    NativeReciprocal.nativeAdmissions (head.append tail) =
      NativeReciprocal.nativeAdmissions head ++ NativeReciprocal.nativeAdmissions tail := by
  induction head with
  | nil => rfl
  | cons move rest ih => simp only [Execution.append, NativeReciprocal.nativeAdmissions, ih, List.append_assoc]

private theorem early_row_mem_prefix {p : Parameters N} {cut last : Snapshot N}
    (head : Execution (nativeParameters N) (router p) (prepared p) cut)
    (tail : Execution (nativeParameters N) (router p) cut last)
    {rows : List (Row N)}
    (admitted : rows.map rowAdmission = NativeReciprocal.nativeAdmissions (head.append tail))
    (r : Row N) (mem : r ∈ rows) (early : r.probe.due < cut.time) :
    r ∈ rows.take head.deliveries.length := by
  have length : (NativeReciprocal.nativeAdmissions head).length = head.deliveries.length := by
    simpa only [List.length_map] using congrArg List.length (NativeReciprocal.admissions_deliveries head)
  have tailWord : (rows.drop head.deliveries.length).map rowAdmission = NativeReciprocal.nativeAdmissions tail := by
    rw [List.map_drop, admitted, admissions_append, ← length, List.drop_left]
  rw [← List.take_append_drop head.deliveries.length rows] at mem
  rcases List.mem_append.mp mem with first | after
  · exact first
  · have inTail : toDelivery r.probe ∈ tail.deliveries := by
      rw [← NativeReciprocal.admissions_deliveries, ← tailWord, List.map_map]
      exact List.mem_map.mpr ⟨r, after, rfl⟩
    exact (not_le_of_gt early (tail.delivery_time_bounds _ inTail).1).elim

private theorem fires_append (rows rest : List (Row N)) :
    Transaction.fires inputCell (rows ++ rest) =
      Transaction.fires inputCell rows ++ Transaction.fires inputCell rest := List.filterMap_append

private theorem external_fires (p : Parameters N) :
    Transaction.fires inputCell ((List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)) =
    (List.finRange N).map (fun i => (i, launchDate p + latency p i)) := by
  simp [Transaction.fires, externalRow, inputCell]

private theorem receipt_fires {p : Parameters N} (rows : List (Row N))
    (receipt : ∀ r ∈ rows, r.probe.input.2 = .receipt ∧ RowMatches p r) :
    Transaction.fires inputCell rows = [] := by
  unfold Transaction.fires
  apply List.filterMap_eq_nil_iff.mpr
  intro r mem
  have tag := (receipt r mem).1
  have date := (receipt r mem).2.2.2.2.1
  simp [tag] at date
  simp [date]

theorem scheduled_row_fires {p : Parameters N} (receipts : List (Row N))
    (receipt : ∀ r ∈ receipts, ∃ source, r = receiptRow p source) :
    Transaction.fires inputCell (((List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)) ++ receipts) =
      (List.finRange N).map (fun i => (i, launchDate p + latency p i)) := by
  rw [fires_append, external_fires, receipt_fires, List.append_nil]
  intro row mem
  obtain ⟨i, rfl⟩ := receipt row mem
  exact ⟨rfl, receipt_row_matches p i⟩

/-- The native prefix has issued precisely the children of the consumed
rows whose FIRE occurs in that prefix. A receipt cannot occur before the
complete FIRE wave, including for prefixes that end between tied jumps. -/
theorem prefix_launch_and_receipt_accounting {p : Parameters N} (accepted : p.check = true)
    {cut last : Snapshot N}
    (head : Execution (nativeParameters N) (router p) (prepared p) cut)
    (tail : Execution (nativeParameters N) (router p) cut last)
    (receipts : List (Row N))
    (receipt : ∀ r ∈ receipts, ∃ source, r = receiptRow p source)
    (matching : ∀ r ∈ ((List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)) ++ receipts, RowMatches p r)
    (admitted : (((List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)) ++ receipts).map rowAdmission =
        NativeReciprocal.nativeAdmissions (head.append tail))
    (fired : (head.append tail).ledger.emissions.Perm
      ((List.finRange N).map (fun i => (i, launchDate p + latency p i)))) :
    let rows := ((List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)) ++ receipts
    let consumed := rows.take head.deliveries.length
    (consumed.flatMap (fun row => row.children.map toDelivery)).Perm
      (head.ledger.emissions.flatMap (fun e => router p e.1 e.2) ++ unissued consumed head.ledger.emissions) ∧
    (head.ledger.emissions.length < N → ∀ row ∈ consumed, row.probe.input.2 ≠ .receipt) := by
  intro rows consumed
  have dates (e : Fin N × ℝ) (mem : e ∈ (head.append tail).ledger.emissions) :
      e.2 = launchDate p + latency p e.1 := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (fired.mem_iff.mp mem)
    rfl
  have firedLength : (head.append tail).ledger.emissions.length = N := by
    simpa only [List.length_map, List.length_finRange] using fired.length_eq
  have wholeUnique : (Transaction.fires inputCell rows).Nodup := by
    dsimp only [rows]
    rw [scheduled_row_fires receipts receipt]
    exact (List.nodup_finRange N).map (fun _ _ same => congrArg Prod.fst same)
  have prefixUnique : head.ledger.emissions.Nodup := by
    have all := fired.nodup_iff.mpr ((List.nodup_finRange N).map (fun _ _ same => congrArg Prod.fst same))
    rw [Execution.emissions_append] at all
    exact all.sublist (List.sublist_append_left _ _)
  have observed (e : Fin N × ℝ) (mem : e ∈ head.ledger.emissions) :
      e ∈ Transaction.fires inputCell consumed := by
    have clock := dates e (by rw [Execution.emissions_append]; exact List.mem_append_left _ mem)
    have rMem : externalRow p (launchDate p) .launch e.1 ∈ rows :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange e.1)))
    have cutoff := (head.emission_time_bounds e mem).2
    rw [clock] at cutoff
    have early : (externalRow p (launchDate p) .launch e.1).probe.due < cut.time := by
      change launchDate p < cut.time
      linarith [(scalar_latency accepted e.1).1]
    have retained := early_row_mem_prefix head tail admitted _ rMem early
    apply List.mem_filterMap.mpr
    refine ⟨_, retained, ?_⟩
    simp [externalRow, inputCell]
    exact Prod.ext rfl clock.symm
  have taken : (Transaction.fires inputCell consumed).Nodup :=
    wholeUnique.sublist ((List.take_sublist _ _).filterMap _)
  refine ⟨issued_unissued_partition (fun r mem => matching r (List.mem_of_mem_take mem))
    _ prefixUnique taken observed, ?_⟩
  intro short row seen tag
  have late (r : Row N) (mem : r ∈ rows) (stage : r.probe.input.2 = .receipt) :
      launchDate p + 19 / 10 < r.probe.due := by
    simp only [rows, List.mem_append] at mem
    rcases mem with (((first | second) | launch) | rMem)
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp first
      cases stage
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp second
      cases stage
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp launch
      cases stage
    · obtain ⟨source, rfl⟩ := receipt r rMem
      exact receipt_after_fast_cut accepted source
  have early (e : Fin N × ℝ) (mem : e ∈ (head.append tail).ledger.emissions) :
      e.2 ≤ launchDate p + 19 / 10 := by
    rw [dates e mem]
    linarith [(scalar_latency accepted e.1).2.1]
  have same := prefix_fires_before_receipt head tail (launchDate p + 19 / 10) admitted early late row seen tag
  exact (not_lt_of_ge ((congrArg List.length same).trans firedLength).ge short)

private theorem equal_clock_observations {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) (clock : s.time = u.time)
    (noDue : ∀ token ∈ run.deliveries, token.due ≠ u.time) :
    s.x = u.x ∧ run.deliveries = [] := by
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | @cons s cut u move tail ih =>
    cases move with
    | flow flow => exact False.elim (by linarith [flow.positive, tail.time_monotone])
    | jump jump =>
      have after := ih (jump.time_unchanged.trans clock)
        (fun token mem => noDue token (List.mem_append_right _ mem))
      have none : jump.deliveries = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro token mem
        have appears : token ∈ (Execution.cons (.jump jump) tail).deliveries := List.mem_append_left _ mem
        exact noDue token appears ((le_antisymm
          ((Execution.cons (.jump jump) tail).delivery_time_bounds token appears).2
          (clock ▸ ((Execution.cons (.jump jump) tail).delivery_time_bounds token appears).1)))
      exact ⟨jump.physical_continuous.symm.trans after.1, by
        change jump.deliveries ++ tail.deliveries = []
        rw [none, after.2]; rfl⟩

/-- Two factorizations of the same trace at an equal clock have the same
memory and delivery word when no input is due at that clock. -/
theorem same_clock_prefix_observations {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s a b u : Snapshot N} (left : Execution θ route s a) (right : Execution θ route s b)
    (leftTail : Execution θ route a u) (rightTail : Execution θ route b u)
    (shape : left.append leftTail = right.append rightTail) (clock : a.time = b.time)
    (noDue : ∀ token ∈ (left.append leftTail).deliveries, token.due ≠ a.time) :
    a.x = b.x ∧ left.deliveries = right.deliveries := by
  induction left generalizing u b with
  | nil =>
    have h := equal_clock_observations right clock (fun token mem => by
      have ne := noDue token (by rw [shape, Execution.deliveries_append]; exact List.mem_append_left _ mem)
      rwa [← clock])
    exact ⟨h.1, h.2.symm⟩
  | @cons s cut a first left ih =>
    cases right with
    | nil =>
      have h := equal_clock_observations (.cons first left) clock.symm (fun token mem =>
        noDue token (by rw [Execution.deliveries_append]; exact List.mem_append_left _ mem))
      exact ⟨h.1.symm, h.2⟩
    | @cons _ cut' _ second right =>
      change Execution.cons first (left.append leftTail) = Execution.cons second (right.append rightTail) at shape
      injection shape with _ sameState _ sameMove sameTail
      subst cut'
      have eqMove := eq_of_heq sameMove
      subst second
      obtain ⟨values, admitted⟩ := ih right leftTail rightTail (eq_of_heq sameTail) clock
        (fun token mem => noDue token (List.mem_append_right _ mem))
      exact ⟨values, congrArg (fun rest => first.deliveries ++ rest) admitted⟩

private theorem settled_reference {p : Parameters N} (accepted : p.check = true)
    {last cut reference : Snapshot N}
    (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (head : Execution (nativeParameters N) (router p) (prepared p) cut)
    (tail : Execution (nativeParameters N) (router p) cut last)
    (split : run = head.append tail)
    (referenceRun : Execution (nativeParameters N) (router p) (prepared p) reference)
    (silent : referenceRun.ledger.emissions = []) (complete : CompleteThrough referenceRun cut.time)
    (available : HasExecutionCut run cut.time)
    (noDue : ∀ token ∈ run.deliveries, token.due ≠ cut.time) :
    cut.x = reference.x ∧ head.deliveries.length = referenceRun.deliveries.length := by
  obtain ⟨settled, knownHead, knownTail, knownComplete, other⟩ := available
  have same := same_clock_prefix_observations head knownHead tail knownTail
    (split.symm.trans other) knownComplete.1.symm (by rw [← split]; exact noDue)
  have observed := knownHead.observational_unique referenceRun (native_box N) (prepared_physical accepted)
    knownComplete complete
  have noFires : knownHead.ledger.emissions = [] := by
    have word := observed.2
    rw [silent] at word
    exact word.eq_nil
  have knownBalance := (native_prefix_balance knownHead).length_eq
  have refBalance := (native_prefix_balance referenceRun).length_eq
  simp only [noFires, silent, List.flatMap_nil, List.append_nil, List.length_append] at knownBalance refBalance
  have queue := observed.1.pending.length_eq
  refine ⟨same.1.trans observed.1.values, ?_⟩
  rw [same.2]
  omega

private theorem training_memory_from_counts {p : Parameters N} (cut : Snapshot N) (mid : State N) (k : Nat)
    (gain : ∀ i q, cut.x i (.z q) = (prepared p).x i (.z q) + if q = 0 then (3 / 5 : ℝ) * k else 0)
    (recovery : ∀ i, cut.x i .b = (prepared p).x i .b)
    (counts : ∀ i c, mid.writes (Address.mk i c).encode = if c = .port0 then k else 0) :
    SettledMemory p cut mid := by
  intro i
  refine ⟨?_, ?_⟩
  · rw [gain]
    norm_num
  · intro c
    rw [counts]
    cases c
    · simp only [nativeCoordinate, unitDose, ite_true]
      exact (gain i 0).trans (by simp)
    · simpa [nativeCoordinate, unitDose] using gain i 2
    · simp [nativeCoordinate, unitDose, recovery]

private theorem training_settled_cut {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) history.last)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date)
    (receipts : List (Row N)) (receipt : ∀ r ∈ receipts, ∃ source, r = receiptRow p source)
    (admitted : (((List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)) ++ receipts).map rowAdmission =
        NativeReciprocal.nativeAdmissions run) :
    let rows := ((List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)) ++ receipts
    ∀ {cut : Snapshot N} (head : Execution (nativeParameters N) (router p) (prepared p) cut)
      (tail : Execution (nativeParameters N) (router p) cut history.last),
      run = head.append tail → ∀ mid,
      TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p))
        (rows.take head.deliveries.length) mid →
      (cut.time = firstDate + 15 / 2 ∨ cut.time = secondDate p + 15 / 2) → SettledMemory p cut mid := by
  intro rows cut head tail split mid replay date
  have gaps := (of_decide_eq_true accepted : p.Valid).2.2.1
  have firstGap : (8 : ℝ) ≤ p.gap1 := by exact_mod_cast gaps.1
  have secondGap : (8 : ℝ) ≤ p.gap2 := by exact_mod_cast gaps.2
  have order1 : firstDate + 15 / 2 < secondDate p := by unfold secondDate; linarith
  have order2 : secondDate p + 15 / 2 < launchDate p := by unfold launchDate; linarith
  have noDue (token : Delivery N) (mem : token ∈ run.deliveries) : token.due ≠ cut.time := by
    rw [← NativeReciprocal.admissions_deliveries, ← admitted, List.map_map] at mem
    obtain ⟨row, member, rfl⟩ := List.mem_map.mp mem
    change row.probe.due ≠ cut.time
    simp only [List.mem_append] at member
    rcases member with (((first | second) | launch) | routed)
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp first
      change firstDate ≠ cut.time
      rcases date with eq | eq <;> linarith
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp second
      change secondDate p ≠ cut.time
      rcases date with eq | eq <;> linarith
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp launch
      change launchDate p ≠ cut.time
      rcases date with eq | eq <;> linarith
    · obtain ⟨src, rfl⟩ := receipt row routed
      change receiptDate p src ≠ cut.time
      have later := receipt_after_fast_cut accepted src
      rcases date with eq | eq <;> linarith
  have oneComplete : CompleteThrough
      (history.start.append (history.first.intake.append history.first.wave)) (firstDate + 15 / 2) := by
    rw [← history.firstDate]
    exact history.first.settledComplete
  have twoComplete : CompleteThrough
      (history.start.append (history.first.intake.append (history.first.wave.append
        (history.first.quiet.append (history.second.intake.append history.second.wave)))))
      (secondDate p + 15 / 2) := by
    have done := history.second.settledComplete
    refine ⟨done.1.trans (congrArg (fun t => t + 15 / 2) history.first.date), done.2.1, ?_⟩
    intro token mem
    exact (congrArg (fun t => t + 15 / 2) history.first.date) ▸ done.2.2 token mem
  have writes := replay_writes replay
  rcases date with first | second
  · let reference := history.start.append (history.first.intake.append history.first.wave)
    have silent : reference.ledger.emissions = [] := by
      simp only [reference, Execution.emissions_append, history.startSilent, history.first.noFires.1,
        history.first.noFires.2.1, List.nil_append]
    obtain ⟨values, consumed⟩ := settled_reference accepted run head tail split reference silent
      (first.symm ▸ oneComplete) (cuts _ (by rw [first]; simp [exactCutDates])) noDue
    have size : reference.deliveries.length = N := by
      simp only [reference, Execution.deliveries_append, history.startNoArrivals, history.first.intakeWord,
        history.first.noArrivals.1, waveTokens, List.nil_append, List.append_nil, List.length_map, List.length_finRange]
    have prefixEq : rows.take head.deliveries.length = (List.finRange N).map (externalRow p firstDate .first) := by
      let trained := (List.finRange N).map (externalRow p firstDate .first)
      have splitRows : rows = trained ++ ((List.finRange N).map (externalRow p (secondDate p) .second) ++
          ((List.finRange N).map (externalRow p (launchDate p) .launch) ++ receipts)) := by
        simp only [rows, trained, List.append_assoc]
      have trainedLength : trained.length = N := by simp [trained]
      rw [consumed.trans (size.trans trainedLength.symm), splitRows, List.take_left]
    apply training_memory_from_counts cut mid 1
    · intro i q
      rw [values, history.first.settledGains, history.startGain]
      norm_num
    · intro i
      rw [values, history.first.settledRecovery, history.startRecovery]
    · intro i c
      rw [writes, prefixEq]
      exact (guarded_training_counts p).1 i c
  · let reference := history.start.append (history.first.intake.append (history.first.wave.append
      (history.first.quiet.append (history.second.intake.append history.second.wave))))
    have silent : reference.ledger.emissions = [] := by
      simp only [reference, Execution.emissions_append, history.startSilent, history.first.noFires.1,
        history.first.noFires.2.1, history.first.noFires.2.2, history.second.noFires.1, history.second.noFires.2.1,
        List.nil_append]
    obtain ⟨values, consumed⟩ := settled_reference accepted run head tail split reference silent
      (second.symm ▸ twoComplete) (cuts _ (by rw [second]; simp [exactCutDates])) noDue
    have size : reference.deliveries.length = N + N := by
      simp only [reference, Execution.deliveries_append, history.startNoArrivals, history.first.intakeWord,
        history.first.noArrivals.1, history.first.noArrivals.2, history.second.intakeWord, history.second.noArrivals.1,
        waveTokens, List.nil_append, List.append_nil, List.length_append, List.length_map, List.length_finRange]
    let trained := (List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second)
    have prefixEq : rows.take head.deliveries.length = trained := by
      have splitRows : rows = trained ++ ((List.finRange N).map (externalRow p (launchDate p) .launch) ++ receipts) := by
        simp only [rows, trained, List.append_assoc]
      have trainedLength : trained.length = N + N := by simp [trained]
      rw [consumed.trans (size.trans trainedLength.symm), splitRows, List.take_left]
    apply training_memory_from_counts cut mid 2
    · intro i q
      rw [values, history.second.settledGains, history.first.gains, history.startGain]
      by_cases selected : q = 0
      · simp [selected]
        ring
      · simp [selected]
    · intro i
      rw [values, history.second.settledRecovery, history.first.recovery, history.startRecovery]
    · intro i c
      rw [writes, prefixEq]
      exact (guarded_training_counts p).2 i c

/-- All append boundaries of the exact execution have the frozen guarded
prefix, the unissued-children ledger, and the two settled memory cuts. -/
theorem exact_prefix_correspondence {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) history.last)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date)
    (receipts : List (Row N)) (receipt : ∀ r ∈ receipts, ∃ source, r = receiptRow p source)
    (out : State N) :
    let rows := ((List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)) ++ receipts
    TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) rows out →
    rows.map rowAdmission = NativeReciprocal.nativeAdmissions run →
    run.ledger.emissions.Perm ((List.finRange N).map (fun i => (i, launchDate p + latency p i))) →
    prefixCorrespondence p run rows out := by
  intro rows replay admitted fired
  have matching (row : Row N) (mem : row ∈ rows) : RowMatches p row := by
    simp only [rows, List.mem_append] at mem
    rcases mem with (((first | second) | launch) | child)
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp first
      exact (external_row_matches accepted i).1
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp second
      exact (external_row_matches accepted i).2.1
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp launch
      exact (external_row_matches accepted i).2.2
    · obtain ⟨source, rfl⟩ := receipt row child
      exact receipt_row_matches p source
  apply prefix_correspondence_of_cuts run replay admitted
  intro cut head tail split
  have accounting := prefix_launch_and_receipt_accounting accepted head tail receipts receipt matching
    (split ▸ admitted) (split ▸ fired)
  exact ⟨accounting.1, accounting.2,
    training_settled_cut accepted history run cuts receipts receipt admitted head tail split⟩

/-- The exact native witness and its guarded replay agree at every prefix,
including either choice of cut between same-clock jumps. -/
theorem native_with_prefix_correspondence {p : Parameters N} (accepted : p.check = true) :
    ∃ (last : Snapshot N) (run : Execution (nativeParameters N) (router p) (prepared p) last)
      (rows : List (Row N)) (out : State N),
      CompleteThrough run (horizon p) ∧
      TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) rows out ∧
      rows.map rowAdmission = NativeReciprocal.nativeAdmissions run ∧ prefixCorrespondence p run rows out := by
  obtain ⟨history, run, complete, _, cuts, _, admitted, fires, _⟩ := native_exact_execution accepted
  obtain ⟨receipts, out, replay, word, _, _, _, receipt, _⟩ :=
    exact_guarded_replay accepted history run cuts admitted fires
  exact ⟨history.last, run, _, out, complete, replay, word,
    exact_prefix_correspondence accepted history run cuts receipts receipt out replay word
      (native_fires_frozen history run fires)⟩

end NetworkStability.NativeMultiToken
