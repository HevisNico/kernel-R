import GuardedReceiptRows

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid PhaseAdmission
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate address_encode_injective)

noncomputable def externalRow (p : Parameters N) (date : ℝ) (stage : Stage) (i : Fin N) : Row N :=
  ⟨⟨date, (i, stage)⟩, if stage = .launch then some (date + latency p i) else none,
    if stage = .launch then [⟨date + latency p i + p.delay i, (p.successor i, .receipt)⟩] else [], -1, 1⟩

private theorem external_rows_fold (p : Parameters N) (date : ℝ) (stage : Stage) (start : Nat)
    (external : stage ≠ .receipt) (readScore : if stage = .launch then start = 2 else start ≤ 1)
    (cells : List (Fin N)) (unique : cells.Nodup) (counts : Fin (3 * N) → Nat)
    (unread : ∀ i ∈ cells, counts (Address.mk i .port0).encode = start) :
    let rows := cells.map (externalRow p date stage)
    RowGuards (calendar p) d rows counts ∧
    ∀ i c, writesAfter (calendar p) rows counts (Address.mk i c).encode =
      counts (Address.mk i c).encode + if i ∈ cells ∧ c = .port0 ∧ stage ≠ .launch then 1 else 0 := by
  induction cells generalizing counts with
  | nil => simp [writesAfter, RowGuards]
  | cons i cells ih =>
    let tx := externalRow p date stage i
    have distinct := List.nodup_cons.mp unique
    have beqReceipt : (stage == Stage.receipt) = false := by
      cases stage <;> first | rfl | exact (external rfl).elim
    have footprint (a : Fin (3 * N)) : MarkFeedback.footprint (calendar p).model tx.probe tx.decision a =
        if a = (Address.mk i .port0).encode ∧ stage ≠ .launch then 1 else 0 := by
      by_cases launches : stage = .launch <;>
        simp [MarkFeedback.footprint, MarkFeedback.gain, tx, externalRow, Calendar.model, calendar,
          inputCell, external, beqReceipt, Transaction.decision, launches, and_comm]
    let next (a : Fin (3 * N)) := counts a + MarkFeedback.footprint (calendar p).model tx.probe tx.decision a
    have coordinate (j : Fin N) (c : Coordinate) :
        (Address.mk j c).encode = (Address.mk i .port0).encode ↔ j = i ∧ c = .port0 := by
      constructor
      · intro eq
        have same := address_encode_injective _ _ eq
        exact ⟨congrArg Address.cell same, congrArg Address.coordinate same⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    have unreadNext (j : Fin N) (mem : j ∈ cells) : next (Address.mk j .port0).encode = start := by
      have unequal : j ≠ i := fun eq => distinct.1 (eq ▸ mem)
      simp [next, footprint, coordinate, unequal, unread j (List.mem_cons_of_mem _ mem)]
    obtain ⟨tail, dose⟩ := ih distinct.2 next unreadNext
    have score : MarkFeedback.score (calendar p).model d ⟨[], counts⟩ tx.probe = -6 + 4 * (start : ℤ) := by
      simp [MarkFeedback.score, MarkFeedback.gain, tx, externalRow, Calendar.model, calendar,
        inputCell, external, beqReceipt, unread i List.mem_cons_self]
    refine ⟨⟨by norm_num [tx, externalRow], ?_, ?_, ?_, tail⟩, ?_⟩
    · change RoutedCalendar.HasRoom (MarkFeedback.score (calendar p).model d ⟨[], counts⟩ tx.probe) (-1) 1
      rw [score]
      by_cases fire : stage = .launch
      · have two : start = 2 := by simpa [fire] using readScore
        subst start
        exact Or.inr ⟨by decide, by decide⟩
      · have weak : start ≤ 1 := by simpa [fire] using readScore
        exact Or.inl ⟨by omega, by omega⟩
    · change MarkFeedback.read (calendar p).model d ⟨[], counts⟩ tx.probe 0 = tx.decision
      by_cases fire : stage = .launch
      · have two : start = 2 := by simpa [fire] using readScore
        subst start
        rw [MarkFeedback.read, score]
        norm_num [tx, externalRow, Transaction.decision, fire]
      · have weak : start ≤ 1 := by simpa [fire] using readScore
        have negative : ¬(0 ≤ -6 + 4 * (start : ℤ)) := by omega
        rw [MarkFeedback.read, score]
        simp [tx, externalRow, Transaction.decision, fire, negative]
    · change MarkFeedback.emitted (calendar p).model tx.probe tx.decision = tx.children
      by_cases fire : stage = .launch <;>
        simp [MarkFeedback.emitted, tx, externalRow, Transaction.decision, calendar, Calendar.model, fire]
    · intro j c
      change writesAfter (calendar p) (cells.map (externalRow p date stage)) next (Address.mk j c).encode = _
      rw [dose]
      dsimp only [next]
      rw [footprint]
      simp only [coordinate, List.mem_cons]
      by_cases eq : j = i
      · subst j
        simp [distinct.1]
      · simp [eq]

/-- A same-date weak or launch batch of distinct cells, with the remaining
queue kept up to permutation and with transport of every guarded count. -/
theorem guarded_external_wave {p : Parameters N} (accepted : p.check = true)
    (cells : List (Fin N)) (unique : cells.Nodup) (date : ℝ) (stage : Stage) (count : Nat)
    (external : stage ≠ .receipt) (readScore : if stage = .launch then count = 2 else count ≤ 1)
    (s : State N) (future : List (Probe N))
    (queue : s.pending.Perm ((cells.map (fun i => (externalRow p date stage i).probe)) ++ future))
    (later : ∀ probe ∈ future, date ≤ probe.due)
    (unread : ∀ i ∈ cells, s.writes (Address.mk i .port0).encode = count) :
    let rows := cells.map (externalRow p date stage)
    ∃ out, TransactionReplay (calendar p) d (· ≤ ·) s rows out ∧
      out.pending.Perm (future ++ rows.flatMap Transaction.children) ∧
      ∀ i c, out.writes (Address.mk i c).encode =
        s.writes (Address.mk i c).encode + if i ∈ cells ∧ c = .port0 ∧ stage ≠ .launch then 1 else 0 := by
  intro rows
  have childFuture (tx : Row N) (mem : tx ∈ rows) (probe : Probe N) (child : probe ∈ tx.children) :
      date < probe.due := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
    by_cases fire : stage = .launch
    · simp only [externalRow, ite_eq_left fire, List.mem_singleton] at child
      subst probe
      have delay := (of_decide_eq_true accepted : p.Valid).2.2.2.2.1 i
      have positive : (0 : ℚ) < p.delay i := by linarith
      have positiveReal : (0 : ℝ) < (p.delay i : ℝ) := by exact_mod_cast positive
      change date < date + latency p i + (p.delay i : ℝ)
      linarith [(scalar_latency accepted i).1]
    · simp [externalRow, fire] at child
  have tailFuture (probe : Probe N) (mem : probe ∈ future ++ rows.flatMap Transaction.children) :
      date ≤ probe.due := by
    rcases List.mem_append.mp mem with initial | children
    · exact later probe initial
    · obtain ⟨tx, txMem, child⟩ := List.mem_flatMap.mp children
      exact (childFuture tx txMem probe child).le
  have chronology : rows.Pairwise (fun a b => a.probe.due ≤ b.probe.due) := by
    apply List.pairwise_map.mpr
    exact List.pairwise_of_forall (fun i j => le_rfl)
  have guards := external_rows_fold p date stage count external readScore cells unique s.writes unread
  have balance : (s.pending ++ rows.flatMap Transaction.children).Perm
      (rows.map Transaction.probe ++ (future ++ rows.flatMap Transaction.children)) := by
    rw [← List.append_assoc, List.map_map]
    exact queue.append_right _
  have dateOf (tx : Row N) (mem : tx ∈ rows) : tx.probe.due = date := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
    rfl
  obtain ⟨out, replay, pending, counts⟩ := replay_from_token_budget (calendar p) d rows s _
    guards.1 chronology (fun tx mem probe child => (dateOf tx mem).symm ▸ childFuture tx mem probe child)
    (fun tx mem probe queued => (dateOf tx mem).symm ▸ tailFuture probe queued) balance
  exact ⟨out, replay, pending, fun i c => (congrFun counts _).trans (guards.2 i c)⟩

private theorem external_children (p : Parameters N) (date : ℝ) (stage : Stage)
    (cells : List (Fin N)) :
    (cells.map (externalRow p date stage)).flatMap Transaction.children =
      if stage = .launch then cells.map (fun i => ⟨date + latency p i + p.delay i,
        (p.successor i, .receipt)⟩) else [] := by
  induction cells with
  | nil => by_cases fire : stage = .launch <;> simp [fire]
  | cons i cells ih =>
    simp only [List.map_cons, List.flatMap_cons, ih]
    by_cases fire : stage = .launch <;> simp [externalRow, fire]

/-- Guarded counts at the two training boundaries, independent of the
queue presentation chosen by the replay. -/
theorem guarded_training_counts (p : Parameters N) :
    let first := (List.finRange N).map (externalRow p firstDate .first)
    let second := (List.finRange N).map (externalRow p (secondDate p) .second)
    let counts := (MarkFeedback.initial N (seed p)).writes
    (∀ i c, writesAfter (calendar p) first counts (Address.mk i c).encode =
      if c = .port0 then 1 else 0) ∧
    (∀ i c, writesAfter (calendar p) (first ++ second) counts (Address.mk i c).encode =
      if c = .port0 then 2 else 0) := by
  intro first second counts
  have one := (external_rows_fold p firstDate .first 0 (by decide) (by decide)
    (List.finRange N) (List.nodup_finRange N) counts (fun _ _ => rfl)).2
  have firstCounts (i : Fin N) (c : Coordinate) :
      writesAfter (calendar p) first counts (Address.mk i c).encode = if c = .port0 then 1 else 0 := by
    simpa [counts, MarkFeedback.initial, List.mem_finRange] using one i c
  have two := (external_rows_fold p (secondDate p) .second 1 (by decide) (by decide)
    (List.finRange N) (List.nodup_finRange N) (writesAfter (calendar p) first counts)
    (fun i _ => by rw [firstCounts]; rfl)).2
  refine ⟨firstCounts, ?_⟩
  intro i c
  rw [writesAfter_append, two, firstCounts]
  by_cases chosen : c = .port0 <;> simp [chosen, List.mem_finRange]

/-- Replay both training batches and the launch batch from the seed.
The remaining guarded queue is exactly the set of routed receipts. -/
theorem guarded_through_launch {p : Parameters N} (accepted : p.check = true) :
    let rows := (List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)
    ∃ start, TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) rows start ∧
      start.pending.Perm ((List.finRange N).map (fun i => (receiptRow p i).probe)) ∧
      ∀ i c, start.writes (Address.mk i c).encode = if c = .port0 then 2 else 0 := by
  let cells := List.finRange N
  let second := cells.map (fun i => (externalRow p (secondDate p) .second i).probe)
  let launch := cells.map (fun i => (externalRow p (launchDate p) .launch i).probe)
  have gaps := (of_decide_eq_true accepted : p.Valid).2.2.1
  have firstGap : (8 : ℝ) ≤ p.gap1 := by exact_mod_cast gaps.1
  have secondGap : (8 : ℝ) ≤ p.gap2 := by exact_mod_cast gaps.2
  have firstBefore : firstDate ≤ secondDate p := by unfold secondDate; linarith
  have secondBefore : secondDate p ≤ launchDate p := by unfold launchDate; linarith
  have launchFuture (probe : Probe N) (mem : probe ∈ launch) : secondDate p ≤ probe.due := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
    exact secondBefore
  have initialFuture (probe : Probe N) (mem : probe ∈ second ++ launch) : firstDate ≤ probe.due := by
    rcases List.mem_append.mp mem with earlier | later
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp earlier
      exact firstBefore
    · exact firstBefore.trans (launchFuture probe later)
  have seedQueue : (seed p).Perm ((cells.map (fun i => (externalRow p firstDate .first i).probe)) ++
      (second ++ launch)) := by
    rw [← List.append_assoc]
    rfl
  obtain ⟨afterFirst, firstReplay, firstPending, firstCounts⟩ :=
    guarded_external_wave accepted cells (List.nodup_finRange N) firstDate .first 0 (by decide) (by decide)
      (MarkFeedback.initial N (seed p)) (second ++ launch) seedQueue initialFuture (fun _ _ => rfl)
  have firstQueue : afterFirst.pending.Perm (second ++ launch) := by
    simpa [external_children] using firstPending
  have firstWrite (i : Fin N) (c : Coordinate) :
      afterFirst.writes (Address.mk i c).encode = if c = .port0 then 1 else 0 := by
    simpa [MarkFeedback.initial, show i ∈ cells from List.mem_finRange i] using firstCounts i c
  obtain ⟨afterSecond, secondReplay, secondPending, secondCounts⟩ :=
    guarded_external_wave accepted cells (List.nodup_finRange N) (secondDate p) .second 1 (by decide) (by decide)
      afterFirst launch firstQueue launchFuture (fun i _ => by rw [firstWrite]; rfl)
  have secondQueue : afterSecond.pending.Perm (launch ++ []) := by
    simpa [external_children] using secondPending
  have secondWrite (i : Fin N) (c : Coordinate) :
      afterSecond.writes (Address.mk i c).encode = if c = .port0 then 2 else 0 := by
    rw [secondCounts, firstWrite]
    by_cases selected : c = .port0 <;> simp [selected, show i ∈ cells from List.mem_finRange i]
  obtain ⟨out, launchReplay, launchPending, launchCounts⟩ :=
    guarded_external_wave accepted cells (List.nodup_finRange N) (launchDate p) .launch 2 (by decide) (by decide)
      afterSecond [] secondQueue (by simp) (fun i _ => by rw [secondWrite]; rfl)
  refine ⟨out, (firstReplay.append secondReplay).append launchReplay, ?_, ?_⟩
  · rw [external_children] at launchPending
    exact launchPending
  · intro i c
    rw [launchCounts, secondWrite]
    simp

private theorem admissions_append {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u v : Snapshot N} (head : Execution θ route s u) (tail : Execution θ route u v) :
    NativeReciprocal.nativeAdmissions (head.append tail) =
      NativeReciprocal.nativeAdmissions head ++ NativeReciprocal.nativeAdmissions tail := by
  induction head with
  | nil => rfl
  | cons move rest ih =>
    simp only [Execution.append, NativeReciprocal.nativeAdmissions, ih, List.append_assoc]

private theorem admissions_empty {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) (quiet : run.deliveries = []) :
    NativeReciprocal.nativeAdmissions run = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry mem
  have hd := List.mem_map_of_mem (f := NativeReciprocal.Admission.token) mem
  rw [NativeReciprocal.admissions_deliveries run, quiet] at hd
  cases hd

private theorem ready_after_silence {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) (silent : run.ledger.emissions = [])
    (ready : ∀ i, s.main i = .ready) (i : Fin N) : u.main i = .ready := by
  exact run.allStates_final (run.ready_states_of_no_emissions i (ready i) (by simp [Execution.emissionTimes, silent]))

private theorem external_admissions {p : Parameters N} {s u : Snapshot N}
    (run : Execution (nativeParameters N) (router p) s u) (date : ℝ) (stage : Stage)
    (external : stage ≠ .receipt) (silent : run.ledger.emissions = []) (ready : ∀ i, s.main i = .ready)
    (word : run.deliveries = waveTokens date (fun _ => 0) (List.finRange N)) :
    NativeReciprocal.nativeAdmissions run = ((List.finRange N).map (externalRow p date stage)).map rowAdmission := by
  let label (token : Delivery N) : NativeReciprocal.Admission N := ⟨token, .ready⟩
  have mode (entry : NativeReciprocal.Admission N) (mem : entry ∈ NativeReciprocal.nativeAdmissions run) :
      entry = label entry.token := by
    obtain ⟨before, _, head, arrival, tail, shape, _, observed, _⟩ := NativeReciprocal.admission_cut run entry mem
    have headSilent : head.ledger.emissions = [] := by
      have both := silent
      rw [shape, Execution.emissions_append] at both
      exact (List.append_eq_nil_iff.mp both).1
    rw [ready_after_silence head headSilent ready] at observed
    cases entry with
    | mk token phase => exact congrArg (NativeReciprocal.Admission.mk token) observed.symm
  calc
    _ = (NativeReciprocal.nativeAdmissions run).map id := (List.map_id _).symm
    _ = (NativeReciprocal.nativeAdmissions run).map (fun entry => label entry.token) := List.map_congr_left mode
    _ = run.deliveries.map label := by rw [← NativeReciprocal.admissions_deliveries, List.map_map]; all_goals rfl
    _ = _ := by
      rw [word]
      simp only [waveTokens, List.map_map, Function.comp_def]
      congr 1
      funext i
      simp [rowAdmission, externalRow, toDelivery, inputCell, inputPort, external, label]

private theorem through_wire_admissions {p : Parameters N} (h : NativeHistory p) :
    let rows := (List.finRange N).map (externalRow p firstDate .first) ++
      (List.finRange N).map (externalRow p (secondDate p) .second) ++
      (List.finRange N).map (externalRow p (launchDate p) .launch)
    NativeReciprocal.nativeAdmissions h.throughWire = rows.map rowAdmission := by
  have cleanStart := admissions_empty h.start h.startNoArrivals
  have first := external_admissions h.first.intake firstDate .first (by decide) h.first.noFires.1
    (ready_after_silence h.start h.startSilent (fun _ => rfl)) (by rw [h.first.intakeWord,h.firstDate])
  have second := external_admissions h.second.intake (secondDate p) .second (by decide) h.second.noFires.1
    (fun i => (h.first.ready i).ready) (by rw [h.second.intakeWord,h.first.date])
  have launch := external_admissions h.launchIntake (launchDate p) .launch (by decide) h.launchSilent
    (fun i => (h.second.ready i).ready) h.launchInputs
  simp only [NativeHistory.throughWire, admissions_append, List.map_append, cleanStart, first, second, launch,
    admissions_empty h.first.wave h.first.noArrivals.1, admissions_empty h.first.quiet h.first.noArrivals.2,
    admissions_empty h.second.wave h.second.noArrivals.1, admissions_empty h.second.quiet h.second.noArrivals.2,
    admissions_empty h.launch h.launchNoArrivals, List.nil_append, List.append_nil, List.append_assoc]

/-- Replay every guarded transaction against the admission word of the
exact native witness. The receipt suffix follows the witness's own order. -/
theorem exact_guarded_replay {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) history.last)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date)
    (admitted : NativeReciprocal.nativeAdmissions run = NativeReciprocal.nativeAdmissions history.run)
    (fires : run.ledger.emissions = history.run.ledger.emissions) :
    ∃ (receipts : List (Row N)) (out : State N),
      let external := (List.finRange N).map (externalRow p firstDate .first) ++
        (List.finRange N).map (externalRow p (secondDate p) .second) ++
        (List.finRange N).map (externalRow p (launchDate p) .launch)
      let rows := external ++ receipts
      TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) rows out ∧
      rows.map rowAdmission = NativeReciprocal.nativeAdmissions run ∧
      rows.length = 4 * N ∧ out.pending = [] ∧
      (∀ row ∈ receipts, row.probe.input.2 = .receipt ∧ RowMatches p row ∧ RowDose p run row) ∧
      (∀ row ∈ receipts, ∃ source, row = receiptRow p source) ∧
      ∀ i c, out.writes (Address.mk i c).encode =
        match c with | .port0 => 2 | .port1 => 0 | .recovery => 1 := by
  obtain ⟨wire, head, tail, _, split, wired, _, _, delivered⟩ := native_exact_wire_cut accepted history run cuts fires
  obtain ⟨start, replay, pending, counts⟩ := guarded_through_launch accepted
  have receiptQueue : (start.pending.map toDelivery).Perm tail.deliveries := by
    have mapped := pending.map toDelivery
    rw [List.map_map] at mapped
    exact mapped.trans delivered.symm
  have receiptOnly (probe : Probe N) (mem : probe ∈ start.pending) : probe.input.2 = .receipt := by
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp (pending.mem_iff.mp mem)
    rfl
  obtain ⟨receipts, out, receiptReplay, drained, receiptWord, physical, kinds, dose⟩ :=
    exact_receipt_replay accepted head tail wired delivered run split cuts start receiptQueue receiptOnly
      (fun i => by rw [counts]; rfl)
  let external := (List.finRange N).map (externalRow p firstDate .first) ++
    (List.finRange N).map (externalRow p (secondDate p) .second) ++
    (List.finRange N).map (externalRow p (launchDate p) .launch)
  have official := through_wire_admissions history
  have lastLength : (NativeReciprocal.nativeAdmissions tail).length =
      (NativeReciprocal.nativeAdmissions history.receipts).length := by
    have h1 := congrArg List.length (NativeReciprocal.admissions_deliveries tail)
    have h2 := congrArg List.length (NativeReciprocal.admissions_deliveries history.receipts)
    simp only [List.length_map] at h1 h2
    exact h1.trans (delivered.length_eq.trans (history.wireSection.queue.length_eq.symm.trans
      (history.receiptInputs.length_eq.trans h2.symm)))
  have headWord : NativeReciprocal.nativeAdmissions head = external.map rowAdmission := by
    have same := admitted
    rw [split, NativeHistory.run, admissions_append, admissions_append] at same
    exact (List.append_inj_left' same lastLength).trans official
  refine ⟨receipts, out, replay.append receiptReplay, ?_, ?_, drained, ?_, kinds, ?_⟩
  · rw [split, List.map_append, admissions_append, receiptWord, headWord]
  · have receiptLength := congrArg List.length receiptWord
    have wordLength := congrArg List.length (NativeReciprocal.admissions_deliveries tail)
    have tailLength := delivered.length_eq
    simp only [List.length_map, List.length_finRange] at receiptLength wordLength tailLength
    change (external ++ receipts).length = 4 * N
    rw [List.length_append, receiptLength, wordLength, tailLength]
    simp only [external, List.length_append, List.length_map, List.length_finRange]
    omega
  · intro row mem
    refine ⟨?_, physical row mem⟩
    obtain ⟨source, rfl⟩ := kinds row mem
    rfl
  · intro i c
    rw [dose, counts]
    cases c <;> rfl

/-- The rows from the three external batches satisfy the frozen clock and
routing specification. Physical dose certification is a separate fact. -/
theorem external_row_matches {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    RowMatches p (externalRow p firstDate .first i) ∧
    RowMatches p (externalRow p (secondDate p) .second i) ∧
    RowMatches p (externalRow p (launchDate p) .launch i) := by
  have first : (Stage.first == Stage.launch) = false := rfl
  have second : (Stage.second == Stage.launch) = false := rfl
  have launch : (Stage.launch == Stage.launch) = true := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp [RowMatches, externalRow, Transaction.decision, targetDecision, first]
  · simp [RowMatches, externalRow, Transaction.decision, targetDecision, second]
  · simp [RowMatches, externalRow, Transaction.decision, targetDecision, launch,
      router_launch accepted i, toDelivery, inputCell, inputPort]

/-- The actual native FIRE multiset names every cell at its scalar root. -/
theorem native_fires_frozen {p : Parameters N} (history : NativeHistory p)
    {last : Snapshot N} (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (fires : run.ledger.emissions = history.run.ledger.emissions) :
    run.ledger.emissions.Perm ((List.finRange N).map (fun i => (i, launchDate p + latency p i))) := by
  rw [fires, history.emissions]
  let emit (i : Fin N) := (i, launchDate p + latency p i)
  have word : (history.launch.ledger.emissions.map Prod.fst).map emit = history.launch.ledger.emissions := by
    rw [List.map_map]
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro event mem
    have clock : event.2 ∈ history.launch.emissionTimes event.1 := List.mem_map_of_mem
      (List.mem_filter.mpr ⟨mem, by simp⟩)
    rw [history.fires, List.mem_singleton] at clock
    exact Prod.ext rfl clock.symm
  exact word ▸ (emission_cell_perm history.fires).map emit

/-- Identify the final native memory with the guarded write counts. -/
theorem settled_replay_memory {p : Parameters N} (history : NativeHistory p) (out : State N)
    (writes : ∀ i c, out.writes (Address.mk i c).encode =
      match c with | .port0 => 2 | .port1 => 0 | .recovery => 1) :
    SettledMemory p history.last out := by
  intro i
  refine ⟨?_, ?_⟩
  · rw [history.endpointGain]
    norm_num
  · intro c
    rw [writes]
    cases c
    · simp only [nativeCoordinate, unitDose, Nat.cast_ofNat]
      rw [history.endpointGain, ite_eq_left rfl]
      ring
    · simp only [nativeCoordinate, unitDose, Nat.cast_zero, mul_zero, add_zero]
      rw [history.endpointGain]
      norm_num
    · rw [show nativeCoordinate .recovery = Coord.b from rfl, history.endpointRecovery]
      norm_num [prepared, unitDose]

/-- The frozen native witness and the complete guarded replay agree on
the admission word, the receipt doses, and all terminal memory counts. -/
theorem native_with_exact_guarded_replay {p : Parameters N} (accepted : p.check = true) :
    ∃ (last : Snapshot N) (run : Execution (nativeParameters N) (router p) (prepared p) last)
      (rows : List (Row N)) (out : State N),
      CompleteThrough run (horizon p) ∧ last.pending = [] ∧ out.pending = [] ∧
      TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) rows out ∧
      rows.length = 4 * N ∧ rows.map rowAdmission = NativeReciprocal.nativeAdmissions run ∧
      (∀ row ∈ rows, RowMatches p row ∧ (row.probe.input.2 = .receipt → RowDose p run row)) ∧
      run.ledger.emissions.Perm ((List.finRange N).map (fun i => (i, launchDate p + latency p i))) ∧
      SettledMemory p last out ∧
      (∀ i c, out.writes (Address.mk i c).encode =
        match c with | .port0 => 2 | .port1 => 0 | .recovery => 1) := by
  obtain ⟨history, run, complete, drained, cuts, _, admitted, fires, _⟩ := native_exact_execution accepted
  obtain ⟨receipts, out, replay, word, length, outDrained, physical, _, writes⟩ :=
    exact_guarded_replay accepted history run cuts admitted fires
  refine ⟨history.last, run, _, out, complete, drained, outDrained, replay, length, word, ?_,
    native_fires_frozen history run fires, settled_replay_memory history out writes, writes⟩
  intro row mem
  simp only [List.mem_append] at mem
  rcases mem with ((first | second) | launch) | receipt
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp first
    exact ⟨(external_row_matches accepted i).1, fun impossible => by cases impossible⟩
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp second
    exact ⟨(external_row_matches accepted i).2.1, fun impossible => by cases impossible⟩
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp launch
    exact ⟨(external_row_matches accepted i).2.2, fun impossible => by cases impossible⟩
  · exact ⟨(physical row receipt).2.1, fun _ => (physical row receipt).2.2⟩

end NetworkStability.NativeMultiToken
