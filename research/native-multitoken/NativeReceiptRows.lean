import ExactNativeExecution
import ReceiptWindow

/-! The receipt rows of the frozen refinement, cut from one native execution. -/
namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid

noncomputable def receiptRow (p : Parameters N) (source : Fin N) : Row N :=
  ⟨⟨receiptDate p source, (p.successor source, .receipt)⟩, none, [], -1, 1⟩

theorem receipt_row_matches (p : Parameters N) (source : Fin N) : RowMatches p (receiptRow p source) := by
  have tag : (Stage.receipt == Stage.launch) = false := rfl
  simp [RowMatches, receiptRow, PhaseAdmission.Transaction.decision, targetDecision, tag]

private theorem wire_section_complete {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p) : CompleteThrough history.throughWire (launchDate p + 19 / 10) := by
  have wire := history.wireSection
  have future (token : Delivery N) (present : token ∈ history.wireCut.pending) :
      history.wireCut.time < token.due := by
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp (wire.queue.mem_iff.mp present)
    rw [history.wireDate]
    exact receipt_after_fast_cut accepted source
  have guards : BeforeGuards history.wireCut history.wireCut.x := by
    constructor
    · intro i
      rw [wire.slow]
      let source := sourceOf accepted i
      have target : p.successor source = i := sourceOf_receives accepted i
      have charge := wire.charge source
      rw [target] at charge
      rw [charge]
      change 1 / 10 < _
      rw [neg_mul]
      apply quarter_above_reopen
      have earlier := receipt_after_fast_cut accepted source
      rw [← history.wireDate] at earlier
      linarith [(receipt_timing accepted source).2.1]
    · intro i q
      rw [(wire.aux i q).1]
      linarith [(wire.aux i q).2.2]
  exact ⟨history.wireDate, guards.no_jump (fun i q origin raw => by rw [wire.raw i q] at raw; contradiction)
    future, fun token mem => history.wireDate ▸ future token mem⟩

private theorem wire_section_transport {p : Parameters N} {s t : Snapshot N}
    (same : s.ObservationalEq t) (wire : WireSection p t) : WireSection p s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, same.pending.trans wire.queue⟩
  · intro i; rw [same.main]; exact wire.slow i
  · intro i; rw [same.values, same.time]; exact wire.charge i
  · intro i; rw [same.values]; exact wire.recovery i
  · intro i q; rw [same.aux, same.values]; exact wire.aux i q
  · intro i q; rw [same.raw]; exact wire.raw i q

/-- A selected cell's pre-admission SLOW wait carries its exact charge to
its own receipt, even when other cells have already taken their MARK dose. -/
private theorem wait_for_receipt {p : Parameters N} (accepted : p.check = true)
    {s u : Snapshot N} (wire : WireSection p s) (wait : Execution (nativeParameters N) (router p) s u)
    (source : Fin N) (clock : u.time = receiptDate p source)
    (isolated : ∀ q, NoArrivalAt wait (p.successor source) q) :
    u.main (p.successor source) = .slow ∧
    u.x (p.successor source) .q = (1 / 4) * Real.exp (-(9 / 50) * (u.time - receiverFastEnd p source)) ∧
    u.x (p.successor source) .b = 9 / 50 ∧
    (∀ q, u.aux (p.successor source) q = .ready ∧ RestBand (u.x (p.successor source) (.m q))) ∧
    (∀ q, u.raw (p.successor source) q = none) := by
  let i := p.successor source
  have noMark (q : Port) : wait.ledger.mark i q = 0 := by
    have still := wait.aux_ready_without_input_band i q (wire.aux i q).1 (wire.aux i q).2.2
      (wire.raw i q) (isolated q)
    exact wait.mark_zero_aux i q .ready (by decide) (wait.allStates_aux_flows i q .ready still)
  have cold : u.x i .b = s.x i .b := by
    rw [wait.recovery_balance i, wait.recovery_sum_marks i]
    simp [noMark]
  have constant := (wait.recovery_constant_of_end (native_box N) i cold).2
  have flows : wait.AllFlows (fun {v w} f => ∀ t ∈ Set.Icc v.time w.time,
      f.path t i .b = 9 / 50) := by
    simpa only [wire.recovery i] using constant
  have budget : (9 / 50) * (s.time - receiverFastEnd p source) +
      (9 / 50) * (u.time - s.time) < 9 / 10 := by
    rw [clock]
    have h := (receipt_timing accepted source).2.1
    linarith
  have slow := slow_through_budget wait i (receiverFastEnd p source) (wire.slow i) (wire.charge source)
    (9 / 50) (by norm_num) budget
    (wait.allFlows_mono (fun _ h t ht => (h t ht).le) flows)
  have gainClock := wait.slow_solution i (wait.allStates_main_flows i .slow slow)
  have charge : s.x i .q = (1 / 4) * Real.exp (-(9 / 50) * (s.time - receiverFastEnd p source)) :=
    wire.charge source
  rw [wait.accumulatedRecovery_of_constant i (9 / 50) flows, charge, mul_assoc] at gainClock
  rw [← neg_mul, attenuation_split] at gainClock
  exact ⟨wait.allStates_final slow, gainClock, cold.trans (wire.recovery i),
    fun q => (wait.aux_no_input_rest_band i q (wire.aux i q).1 (wire.aux i q).2
      (wire.raw i q) (isolated q)).1,
    fun q => (wait.raw_absent_of_no_arrival i q (wire.raw i q) (isolated q)).1⟩

private theorem receipt_jump_fields {route : Router N} {before after : Snapshot N}
    (jump : Jump route before after) (token : Delivery N) (paid : jump.deliveries = [token])
    (inactive : ∀ q, before.raw token.cell q = none) :
    after.main = before.main ∧ after.aux = before.aux ∧
    after.raw token.cell token.port = some after.time ∧
    (∀ q, q ≠ token.port → after.raw token.cell q = none) := by
  cases jump with
  | arrive actual =>
    have eq : actual = token := (List.cons.inj paid).1
    subst token
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp [setRaw]
    · intro q different
      simp [setRaw, different, inactive]
  | _ => simp [Jump.deliveries] at paid

/-- Recover the common wire cut in the exact witness. Every FIRE is in
its head and the suffix consumes exactly the queued routed children. -/
theorem native_exact_wire_cut {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) history.last)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date)
    (fires : run.ledger.emissions = history.run.ledger.emissions) :
    ∃ (wire : Snapshot N)
      (head : Execution (nativeParameters N) (router p) (prepared p) wire)
      (tail : Execution (nativeParameters N) (router p) wire history.last),
      CompleteThrough head (launchDate p + 19 / 10) ∧ run = head.append tail ∧
      WireSection p wire ∧ head.ledger.emissions.length = N ∧
      tail.ledger.emissions = [] ∧ tail.deliveries.Perm ((List.finRange N).map (receiptToken p)) := by
  classical
  have past := wire_section_complete accepted history
  obtain ⟨wire, launchHead, receiptTail, complete, split⟩ := cuts (launchDate p + 19 / 10)
    (by simp [exactCutDates])
  have sameWire := (launchHead.observational_unique history.throughWire (native_box N)
    (prepared_physical accepted) complete past).1
  have wires := wire_section_transport sameWire history.wireSection
  have noFires : receiptTail.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event present
    have nativeEvent : event ∈ run.ledger.emissions := by
      rw [split, Execution.emissions_append]
      exact List.mem_append_right _ present
    rw [fires, history.emissions] at nativeEvent
    have clock : event.2 = launchDate p + latency p event.1 := by
      have mem : event.2 ∈ history.launch.emissionTimes event.1 := List.mem_map_of_mem
        (List.mem_filter.mpr ⟨nativeEvent, by simp⟩)
      simpa only [history.fires, List.mem_singleton] using mem
    have later := (receiptTail.emission_time_bounds event present).1
    rw [complete.1, clock] at later
    linarith [(scalar_latency accepted event.1).2.1]
  have inputs : receiptTail.deliveries.Perm ((List.finRange N).map (receiptToken p)) := by
    have balance := native_prefix_balance receiptTail
    rw [history.finalQueue, noFires] at balance
    exact (by simpa only [List.nil_append, List.flatMap_nil, List.append_nil] using balance :
      receiptTail.deliveries.Perm wire.pending).trans wires.queue
  have length : history.launch.ledger.emissions.length = N := by
    simpa only [List.length_map, List.length_finRange] using (emission_cell_perm history.fires).length_eq
  have headFires : (launchHead.ledger.emissions).length = N := by
    have word : run.ledger.emissions = launchHead.ledger.emissions := by
      rw [split, Execution.emissions_append, noFires, List.append_nil]
    exact (congrArg List.length (word.symm.trans (fires.trans history.emissions))).trans length
  exact ⟨wire, launchHead, receiptTail, complete, split, wires, headFires, noFires, inputs⟩

/-- Every routed receipt has exactly the frozen `RowDose` on a segment of
this exact witness, including coincident receipts on different cells. -/
theorem receipt_row_doses_in_tail {p : Parameters N} (accepted : p.check = true)
    {wire last : Snapshot N}
    (launchHead : Execution (nativeParameters N) (router p) (prepared p) wire)
    (receiptTail : Execution (nativeParameters N) (router p) wire last)
    (wires : WireSection p wire)
    (inputs : receiptTail.deliveries.Perm ((List.finRange N).map (receiptToken p)))
    (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (split : run = launchHead.append receiptTail)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date) :
    ∀ source, RowDose p run (receiptRow p source) ∧
      rowAdmission (receiptRow p source) ∈ NativeReciprocal.nativeAdmissions receiptTail := by
  classical
  have injective : Function.Injective (receiptToken p) := by
    intro a b equal
    exact (of_decide_eq_true accepted : p.Valid).2.2.2.1.1 a b (congrArg Delivery.cell equal)
  have unique := inputs.nodup_iff.mpr ((List.nodup_finRange N).map injective)
  intro source
  let token := receiptToken p source
  let i := p.successor source
  have seenToken : token ∈ receiptTail.deliveries :=
    inputs.mem_iff.mpr (List.mem_map_of_mem (List.mem_finRange source))
  rw [← NativeReciprocal.admissions_deliveries receiptTail] at seenToken
  obtain ⟨admission, seen, tokenEq⟩ := List.mem_map.mp seenToken
  obtain ⟨before, admitted, wait, arrival, remaining, receiptSplit, delivered, observedMode, arrivalDate⟩ :=
    NativeReciprocal.admission_cut receiptTail admission seen
  rw [tokenEq] at delivered arrivalDate
  have receiptClock : before.time = receiptDate p source := arrivalDate
  have fromWire : receiptTail.deliveries = wait.deliveries ++ token :: remaining.deliveries := by
    rw [receiptSplit, Execution.deliveries_append]
    change wait.deliveries ++ (arrival.deliveries ++ remaining.deliveries) = _
    simp only [delivered, List.cons_append, List.nil_append]
  have tokenAbsent : token ∉ wait.deliveries ++ remaining.deliveries := by
    rw [fromWire] at unique
    have moved : (wait.deliveries ++ token :: remaining.deliveries).Perm
        (token :: (wait.deliveries ++ remaining.deliveries)) := List.perm_middle
    exact (List.nodup_cons.mp (moved.nodup_iff.mp unique)).1
  have exclusive (d : Delivery N) (mem : d ∈ wait.deliveries ++ remaining.deliveries) : d.cell ≠ i := by
    intro cell
    have intake : d ∈ receiptTail.deliveries := by
      rw [fromWire]
      rcases List.mem_append.mp mem with before | after
      · exact List.mem_append_left _ before
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
    obtain ⟨other, _, rfl⟩ := List.mem_map.mp (inputs.mem_iff.mp intake)
    have same : other = source := (of_decide_eq_true accepted : p.Valid).2.2.2.1.1 other source cell
    exact tokenAbsent (by simpa only [same] using mem)
  obtain ⟨mode, charge, cold, aux, dry⟩ := wait_for_receipt accepted wires wait source receiptClock
    (fun _ d mem => Or.inl (exclusive d (List.mem_append_left _ mem)))
  obtain ⟨mainSame, auxSame, active, inactive⟩ := receipt_jump_fields arrival token delivered dry
  let head := launchHead.append wait
  let throughIntake := head.append (.cons (.jump arrival) (.nil _))
  have nativeShape : run = throughIntake.append remaining := by
    simp only [split, receiptSplit, throughIntake, head, Execution.append_assoc, Execution.append]
  have admittedClock : admitted.time = receiptDate p source := arrival.time_unchanged.trans receiptClock
  have deadline : HasExecutionCut run (receiptDate p source + (auxDeadline : ℝ)) :=
    cuts _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange source)))
  have later : admitted.time < receiptDate p source + (auxDeadline : ℝ) := by
    rw [admittedClock]; norm_num [auxDeadline]
  obtain ⟨endState, body, tail, endComplete, bodySplit⟩ :=
    HasExecutionCut.after_prefix throughIntake remaining later (nativeShape ▸ deadline)
  have isolated (d : Delivery N) (mem : d ∈ body.deliveries) : d.cell ≠ i := by
    apply exclusive d
    apply List.mem_append_right
    rw [bodySplit, Execution.deliveries_append]
    exact List.mem_append_left _ mem
  have validStart : RawValid (prepared p) := by intro _ _ _ h; cases h
  have window := receipt_window_doses body i 2 (native_box N)
    (throughIntake.physical_invariant (native_box N) (prepared_physical accepted))
    (throughIntake.raw_valid validStart) (receiverFastEnd p source)
    (by rw [mainSame]; exact mode)
    (by rw [arrival.physical_continuous, arrival.time_unchanged]; exact charge)
    (by rw [arrival.physical_continuous]; exact cold)
    (by rw [admittedClock]; exact endComplete.1)
    (by rw [admittedClock]; simpa [auxDeadline] using (receipt_timing accepted source).2.1)
    (fun q => by rw [auxSame, arrival.physical_continuous]; exact aux q)
    active inactive (fun _ d mem => Or.inl (isolated d mem))
  have shape : run = head.append (.cons (.jump arrival) (body.append tail)) := by
    simp only [nativeShape, bodySplit, throughIntake, Execution.append_assoc, Execution.append]
  have actual : NativeReciprocal.jumpAdmissions arrival = [rowAdmission (receiptRow p source)] :=
    jump_admission_of_delivery arrival _ delivered mode
  have modeExpected : admission.mode = .slow := by
    rw [← observedMode, tokenEq]
    exact mode
  have admissionExpected : admission = rowAdmission (receiptRow p source) := by
    cases admission with
    | mk actual mode =>
      exact congrArg₂ NativeReciprocal.Admission.mk tokenEq modeExpected
  refine ⟨?_, admissionExpected ▸ seen⟩
  refine ⟨before, admitted, endState, head, arrival, body, tail, shape, actual, receiptClock,
    endComplete.1, isolated, window.noFire, ?_, ?_, ?_, fun _ => window.slow, window.settled⟩
  · simpa [receiptRow] using window.error
  · simpa [receiptRow] using window.mark
  · simpa [receiptRow] using window.recovery

theorem receipt_row_doses {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) history.last)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date)
    (fires : run.ledger.emissions = history.run.ledger.emissions) :
    ∀ source, RowDose p run (receiptRow p source) := by
  obtain ⟨wire, launchHead, receiptTail, _, split, wires, _, _, inputs⟩ :=
    native_exact_wire_cut accepted history run cuts fires
  exact fun source => (receipt_row_doses_in_tail accepted launchHead receiptTail wires inputs run split cuts source).1

theorem native_exact_receipt_rows {p : Parameters N} (accepted : p.check = true) :
    ∃ (last : Snapshot N) (run : Execution (nativeParameters N) (router p) (prepared p) last),
      CompleteThrough run (horizon p) ∧ last.pending = [] ∧
      (∀ date ∈ exactCutDates p, HasExecutionCut run date) ∧
      ∀ source, RowMatches p (receiptRow p source) ∧ RowDose p run (receiptRow p source) := by
  obtain ⟨history, run, complete, drained, cuts, _, _, fires, _⟩ := native_exact_execution accepted
  exact ⟨history.last, run, complete, drained, cuts,
    fun source => ⟨receipt_row_matches p source, receipt_row_doses accepted history run cuts fires source⟩⟩

end NetworkStability.NativeMultiToken
