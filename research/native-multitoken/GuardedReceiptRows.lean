import GuardedReplay
import NativeReceiptRows

/-! The guarded counterpart of the receipt suffix. -/
namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid PhaseAdmission
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate address_encode_injective)

private theorem receipt_footprint (p : Parameters N) (source : Fin N) (a : Fin (3 * N)) :
    MarkFeedback.footprint (calendar p).model (receiptRow p source).probe false a =
      if a = (Address.mk (p.successor source) .recovery).encode then 1 else 0 := by
  have tag : (Stage.receipt == Stage.receipt) = true := rfl
  simp [MarkFeedback.footprint, MarkFeedback.recovery, receiptRow, calendar, Calendar.model, inputCell, tag]

private theorem receipt_preserves_second (p : Parameters N) (source i : Fin N) :
    MarkFeedback.footprint (calendar p).model (receiptRow p source).probe false
      (Address.mk i .port1).encode = 0 := by
  rw [receipt_footprint]
  apply ite_eq_right
  intro eq
  have different := congrArg Address.coordinate (address_encode_injective _ _ eq)
  cases different

private theorem row_guards_for_receipts (p : Parameters N) (sources : List (Fin N))
    (counts : Fin (3 * N) → Nat) (zero : ∀ i, counts (Address.mk i .port1).encode = 0) :
    RowGuards (calendar p) d (sources.map (receiptRow p)) counts := by
  induction sources generalizing counts with
  | nil => trivial
  | cons source rest ih =>
    let tx := receiptRow p source
    have score : MarkFeedback.score (calendar p).model d ⟨[], counts⟩ tx.probe = -2 := by
      have tag : (Stage.receipt == Stage.receipt) = true := rfl
      simp [MarkFeedback.score, MarkFeedback.gain, tx, receiptRow, calendar, Calendar.model, inputCell, tag, zero]
    refine ⟨by norm_num [tx, receiptRow], ?_, ?_, ?_, ?_⟩
    · change RoutedCalendar.HasRoom (MarkFeedback.score (calendar p).model d ⟨[], counts⟩ tx.probe) (-1) 1
      rw [score]
      exact Or.inl ⟨by decide, by decide⟩
    · change MarkFeedback.read (calendar p).model d ⟨[], counts⟩ tx.probe 0 = false
      norm_num [MarkFeedback.read, score]
    · rfl
    · apply ih
      intro i
      change counts (Address.mk i .port1).encode +
        MarkFeedback.footprint (calendar p).model tx.probe false (Address.mk i .port1).encode = 0
      rw [zero i, receipt_preserves_second]

private theorem written_receipt_counts (p : Parameters N) (sources : List (Fin N))
    (counts : Fin (3 * N) → Nat) (i : Fin N) (c : Coordinate) :
    writesAfter (calendar p) (sources.map (receiptRow p)) counts (Address.mk i c).encode =
      counts (Address.mk i c).encode +
        if c = .recovery then sources.countP (fun source => p.successor source = i) else 0 := by
  induction sources generalizing counts with
  | nil => cases c <;> simp [writesAfter]
  | cons source rest ih =>
    let next (a : Fin (3 * N)) := counts a + MarkFeedback.footprint (calendar p).model
      (receiptRow p source).probe false a
    change writesAfter (calendar p) (rest.map (receiptRow p)) next (Address.mk i c).encode = _
    rw [ih next]
    dsimp only [next]
    rw [receipt_footprint]
    have address : (Address.mk i c).encode = (Address.mk (p.successor source) .recovery).encode ↔
        p.successor source = i ∧ c = .recovery := by
      constructor
      · intro eq
        have same := address_encode_injective _ _ eq
        exact ⟨(congrArg Address.cell same).symm, congrArg Address.coordinate same⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [address]
    by_cases h : p.successor source = i <;> cases c <;>
      simp [h]
    all_goals omega

/-- A drained receipt suffix. The supplied order need only be chronological,
so the native ordering of equally dated independent receipts is admissible. -/
theorem guarded_receipt_replay {p : Parameters N} (accepted : p.check = true)
    (sources : List (Fin N)) (occurrences : sources.Perm (List.finRange N))
    (ordered : sources.Pairwise (fun a b => receiptDate p a ≤ receiptDate p b))
    (start : State N) (queue : start.pending.Perm (sources.map (fun i => (receiptRow p i).probe)))
    (zeroSecond : ∀ i, start.writes (Address.mk i .port1).encode = 0) :
    ∃ out, TransactionReplay (calendar p) d (· ≤ ·) start (sources.map (receiptRow p)) out ∧
      out.pending = [] ∧ ∀ i c,
        out.writes (Address.mk i c).encode =
          start.writes (Address.mk i c).encode + if c = .recovery then 1 else 0 := by
  have children : ∀ tx ∈ sources.map (receiptRow p), tx.children = [] := by
    intro tx mem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp mem
    rfl
  have balance : (start.pending ++ (sources.map (receiptRow p)).flatMap Transaction.children).Perm
      ((sources.map (receiptRow p)).map Transaction.probe ++ []) := by
    rw [List.flatMap_eq_nil_iff.mpr children, List.append_nil, List.append_nil, List.map_map]
    exact queue
  obtain ⟨out, replay, drained, counts⟩ := replay_from_token_budget (calendar p) d
    (sources.map (receiptRow p)) start [] (row_guards_for_receipts p sources start.writes zeroSecond)
    (List.pairwise_map.mpr ordered) (fun tx mem child present => by rw [children tx mem] at present; cases present)
    (by simp) balance
  refine ⟨out, replay, drained.eq_nil, ?_⟩
  intro i c
  rw [counts, written_receipt_counts]
  have selects (source : Fin N) : p.successor source = i ↔ source = sourceOf accepted i := by
    constructor
    · intro same
      rw [← same, sourceOf_successor]
    · rintro rfl
      exact sourceOf_receives accepted i
  have pred : (fun source : Fin N => decide (p.successor source = i)) =
      (fun source => source == sourceOf accepted i) := by
    funext source
    simp only [Bool.beq_eq_decide_eq, selects]
  have once : sources.countP (fun source => p.successor source = i) = 1 := by
    rw [pred, ← List.count_eq_countP, occurrences.count_eq]
    exact List.count_eq_one_of_mem (List.nodup_finRange N) (List.mem_finRange _)
  rw [once]

/-- Replay the receipts in their actual native delivery order. Accounting
for the guarded queue is required only up to permutation of physical tokens. -/
theorem guarded_replay_in_native_receipt_order {p : Parameters N} (accepted : p.check = true)
    {wire last : Snapshot N} (tail : Execution (nativeParameters N) (router p) wire last)
    (delivered : tail.deliveries.Perm ((List.finRange N).map (receiptToken p)))
    (start : State N) (queue : (start.pending.map toDelivery).Perm tail.deliveries)
    (receiptOnly : ∀ probe ∈ start.pending, probe.input.2 = .receipt)
    (zeroSecond : ∀ i, start.writes (Address.mk i .port1).encode = 0) :
    ∃ (rows : List (Row N)) (out : State N),
      TransactionReplay (calendar p) d (· ≤ ·) start rows out ∧ out.pending = [] ∧
      rows.map (fun row => toDelivery row.probe) = tail.deliveries ∧
      (∀ row ∈ rows, ∃ source, row = receiptRow p source) ∧
      ∀ i c, out.writes (Address.mk i c).encode =
        start.writes (Address.mk i c).encode + if c = .recovery then 1 else 0 := by
  let source (token : Delivery N) := sourceOf accepted token.cell
  let ordered := tail.deliveries.map source
  have lookup (i : Fin N) : source (receiptToken p i) = i := sourceOf_successor accepted i
  have allSources : ordered.Perm (List.finRange N) := by
    simpa only [List.map_map, Function.comp_def, lookup, List.map_id'] using delivered.map source
  have original (token : Delivery N) (mem : token ∈ tail.deliveries) :
      receiptToken p (source token) = token := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (delivered.mem_iff.mp mem)
    change receiptToken p (sourceOf accepted (p.successor i)) = receiptToken p i
    rw [sourceOf_successor]
  have deliveryWord : ordered.map (receiptToken p) = tail.deliveries := by
    rw [show ordered = tail.deliveries.map source from rfl, List.map_map]
    change tail.deliveries.map (fun token => receiptToken p (source token)) = tail.deliveries
    exact (List.map_congr_left (g := id) original).trans (List.map_id _)
  have chronology : ordered.Pairwise (fun a b => receiptDate p a ≤ receiptDate p b) := by
    apply List.pairwise_map.mpr
    refine tail.deliveries_chronological.imp_of_mem ?_
    intro a b ha hb early
    change (receiptToken p (source a)).due ≤ (receiptToken p (source b)).due
    rwa [original a ha, original b hb]
  let decode (token : Delivery N) : Probe N := ⟨token.due, (token.cell, .receipt)⟩
  have decodedStart : (start.pending.map toDelivery).map decode = start.pending := by
    rw [List.map_map]
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro probe mem
    obtain ⟨date, i, stage⟩ := probe
    have tag := receiptOnly _ mem
    change stage = .receipt at tag
    subst stage
    rfl
  have decodedTail : tail.deliveries.map decode = ordered.map (fun i => (receiptRow p i).probe) := by
    rw [← deliveryWord, List.map_map]
    all_goals rfl
  have queueExact := queue.map decode
  rw [decodedStart, decodedTail] at queueExact
  obtain ⟨out, replay, drained, counts⟩ :=
    guarded_receipt_replay accepted ordered allSources chronology start queueExact zeroSecond
  refine ⟨ordered.map (receiptRow p), out, replay, drained, ?_, ?_, counts⟩
  · rw [List.map_map]
    exact deliveryWord
  · intro row mem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
    exact ⟨i, rfl⟩

/-- The guarded receipt suffix has the exact native admission word, and its
rows carry the frozen physical dose certificate on the full execution. -/
theorem exact_receipt_replay {p : Parameters N} (accepted : p.check = true)
    {wire last : Snapshot N}
    (launchHead : Execution (nativeParameters N) (router p) (prepared p) wire)
    (receiptTail : Execution (nativeParameters N) (router p) wire last)
    (wireSection : WireSection p wire)
    (delivered : receiptTail.deliveries.Perm ((List.finRange N).map (receiptToken p)))
    (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (split : run = launchHead.append receiptTail)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date)
    (start : State N) (queue : (start.pending.map toDelivery).Perm receiptTail.deliveries)
    (receiptOnly : ∀ probe ∈ start.pending, probe.input.2 = .receipt)
    (zeroSecond : ∀ i, start.writes (Address.mk i .port1).encode = 0) :
    ∃ (rows : List (Row N)) (out : State N),
      TransactionReplay (calendar p) d (· ≤ ·) start rows out ∧ out.pending = [] ∧
      rows.map rowAdmission = NativeReciprocal.nativeAdmissions receiptTail ∧
      (∀ row ∈ rows, RowMatches p row ∧ RowDose p run row) ∧
      ∀ i c, out.writes (Address.mk i c).encode =
        start.writes (Address.mk i c).encode + if c = .recovery then 1 else 0 := by
  have physical := receipt_row_doses_in_tail accepted launchHead receiptTail wireSection delivered run split cuts
  obtain ⟨rows, out, replay, drained, word, kinds, counts⟩ :=
    guarded_replay_in_native_receipt_order accepted receiptTail delivered start queue receiptOnly zeroSecond
  have injective : Function.Injective (receiptToken p) := fun a b eq =>
    (of_decide_eq_true accepted : p.Valid).2.2.2.1.1 a b (congrArg Delivery.cell eq)
  have unique : ((NativeReciprocal.nativeAdmissions receiptTail).map NativeReciprocal.Admission.token).Nodup := by
    rw [NativeReciprocal.admissions_deliveries]
    exact delivered.nodup_iff.mpr ((List.nodup_finRange N).map injective)
  let label (token : Delivery N) : NativeReciprocal.Admission N := ⟨token, .slow⟩
  have labels : NativeReciprocal.nativeAdmissions receiptTail = receiptTail.deliveries.map label := by
    calc
      _ = (NativeReciprocal.nativeAdmissions receiptTail).map id := (List.map_id _).symm
      _ = (NativeReciprocal.nativeAdmissions receiptTail).map (fun entry => label entry.token) := by
        apply List.map_congr_left
        intro entry mem
        have seen : entry.token ∈ receiptTail.deliveries := by
          rw [← NativeReciprocal.admissions_deliveries]
          exact List.mem_map_of_mem mem
        obtain ⟨source, _, same⟩ := List.mem_map.mp (delivered.mem_iff.mp seen)
        calc
          entry = rowAdmission (receiptRow p source) :=
            List.inj_on_of_nodup_map unique mem (physical source).2 same.symm
          _ = label entry.token := by
            change label (receiptToken p source) = label entry.token
            rw [same]
      _ = _ := by
        rw [← NativeReciprocal.admissions_deliveries, List.map_map]
        all_goals rfl
  refine ⟨rows, out, replay, drained, ?_, ?_, counts⟩
  · rw [labels, ← word, List.map_map]
    apply List.map_congr_left
    intro row mem
    obtain ⟨source, rfl⟩ := kinds row mem
    rfl
  · intro row mem
    obtain ⟨source, rfl⟩ := kinds row mem
    exact ⟨receipt_row_matches p source, (physical source).1⟩

end NetworkStability.NativeMultiToken
