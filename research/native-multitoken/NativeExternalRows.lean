import ExactPrefixCorrespondence
import GuardedTraceWords
import KernelR.HybridInactiveSectionCovers

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid PhaseAdmission
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

/-- The three external pulses are bracketed by the initial and settled cuts. -/
inductive ExternalWave
  | first | second | launch

def ExternalWave.tag : ExternalWave → Stage
  | .first => .first
  | .second => .second
  | .launch => .launch

noncomputable def ExternalWave.start (p : Parameters N) : ExternalWave → ℝ
  | .first => 0
  | .second => firstDate + 15 / 2
  | .launch => secondDate p + 15 / 2

noncomputable def ExternalWave.intake (p : Parameters N) : ExternalWave → ℝ
  | .first => firstDate
  | .second => secondDate p
  | .launch => launchDate p

private theorem external_deliveries {p : Parameters N} (accepted : p.check = true)
    {last : Snapshot N} (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (fires : run.ledger.emissions.Perm ((List.finRange N).map (fun i => (i, launchDate p + latency p i))))
    (token : Delivery N) (seen : token ∈ run.deliveries) :
    (token.port = 0 ∧ (token.due = firstDate ∨ token.due = secondDate p ∨ token.due = launchDate p)) ∨
      ∃ i, token = receiptToken p i := by
  have queue := (native_prefix_balance run).mem_iff.mp (List.mem_append_right _ seen)
  rcases List.mem_append.mp queue with initial | child
  · change token ∈ (seed p).map toDelivery at initial
    obtain ⟨probe, source, rfl⟩ := List.mem_map.mp initial
    simp only [seed, List.mem_append] at source
    rcases source with (first | second) | launch
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp first
      exact Or.inl ⟨rfl, Or.inl rfl⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp second
      exact Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp launch
      exact Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩
  · obtain ⟨event, fire, routed⟩ := List.mem_flatMap.mp child
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (fires.mem_iff.mp fire)
    rw [router_launch accepted] at routed
    exact Or.inr ⟨i, List.mem_singleton.mp routed⟩

private theorem external_interval_token {p : Parameters N} (accepted : p.check = true)
    {last : Snapshot N} (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (fires : run.ledger.emissions.Perm ((List.finRange N).map (fun i => (i, launchDate p + latency p i))))
    (wave : ExternalWave) (token : Delivery N) (mem : token ∈ run.deliveries)
    (lower : wave.start p ≤ token.due) (upper : token.due ≤ wave.intake p + (auxDeadline : ℝ)) :
    token.port = 0 ∧ token.due = wave.intake p := by
  have gaps := (of_decide_eq_true accepted : p.Valid).2.2.1
  have g1 : (8 : ℝ) ≤ p.gap1 := by exact_mod_cast gaps.1
  have g2 : (8 : ℝ) ≤ p.gap2 := by exact_mod_cast gaps.2
  have d1 : firstDate + 15 / 2 < secondDate p := by unfold secondDate; linarith
  have d2 : secondDate p + 15 / 2 < launchDate p := by unfold launchDate; linarith
  have short : (auxDeadline : ℝ) < 19 / 10 := by norm_num [auxDeadline]
  rcases external_deliveries accepted run fires token mem with ⟨port, first | second | launch⟩ | ⟨i, rfl⟩
  · cases wave <;> simp only [ExternalWave.start, ExternalWave.intake] at lower upper ⊢
    · exact ⟨port, first⟩
    · exfalso; linarith
    · exfalso; linarith
  · cases wave <;> simp only [ExternalWave.start, ExternalWave.intake] at lower upper ⊢
    · exfalso; linarith
    · exact ⟨port, second⟩
    · exfalso; linarith
  · cases wave <;> simp only [ExternalWave.start, ExternalWave.intake] at lower upper ⊢
    · exfalso; linarith
    · exfalso; linarith
    · exact ⟨port, launch⟩
  · have later := receipt_after_fast_cut accepted i
    change receiptDate p i ≤ wave.intake p + (auxDeadline : ℝ) at upper
    cases wave <;> simp only [ExternalWave.intake] at upper <;> exfalso <;> linarith

private theorem native_delivery_nodup {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) : run.deliveries.Nodup := by
  exact (NativeReciprocal.actual_raw_windows_disjoint run).imp (fun {_ _} gap same => by
    subst_vars
    have impossible := gap rfl rfl
    linarith)

/-- A single cell's external slice contains its labelled raw intake and
no further same-cell inputs, even if other cells are admitted at that clock. -/
theorem external_pulse_window {p : Parameters N} (accepted : p.check = true)
    {base last : Snapshot N} (prefixRun : Execution (nativeParameters N) (router p) (prepared p) base)
    (suffix : Execution (nativeParameters N) (router p) base last)
    (wave : ExternalWave) (i : Fin N) (start : base.time = wave.start p)
    (beforeIntake : base.time < wave.intake p)
    (seen : rowAdmission (externalRow p (wave.intake p) wave.tag i) ∈
      NativeReciprocal.nativeAdmissions suffix)
    (fires : (prefixRun.append suffix).ledger.emissions.Perm
      ((List.finRange N).map (fun i => (i, launchDate p + latency p i))))
    (deadline : HasExecutionCut (prefixRun.append suffix) (wave.intake p + (auxDeadline : ℝ))) :
    ∃ (before admitted finished : Snapshot N)
      (wait : Execution (nativeParameters N) (router p) base before)
      (jump : Jump (router p) before admitted)
      (body : Execution (nativeParameters N) (router p) admitted finished)
      (tail : Execution (nativeParameters N) (router p) finished last),
      suffix = wait.append (.cons (.jump jump) (body.append tail)) ∧
      jump.deliveries = [⟨i, 0, wave.intake p⟩] ∧
      before.time = wave.intake p ∧ finished.time = wave.intake p + (auxDeadline : ℝ) ∧
      (∀ token ∈ wait.deliveries, token.cell ≠ i) ∧ (∀ token ∈ body.deliveries, token.cell ≠ i) := by
  let row := externalRow p (wave.intake p) wave.tag i
  let token : Delivery N := ⟨i, 0, wave.intake p⟩
  have identified : (rowAdmission row).token = token := by cases wave <;> rfl
  obtain ⟨before, admitted, wait, jump, rest, split, paid, _, clock⟩ := NativeReciprocal.admission_cut suffix _ seen
  rw [identified] at paid clock
  have exactClock : before.time = wave.intake p := clock
  let through := (prefixRun.append wait).append (.cons (.jump jump) (.nil _))
  have reaches : prefixRun.append suffix = through.append rest := by
    simp only [split, through, Execution.append_assoc, Execution.append]
  have positive : (0 : ℝ) < auxDeadline := by norm_num [auxDeadline]
  have after := HasExecutionCut.after_prefix through rest (by
    rw [jump.time_unchanged, exactClock]; linarith) (reaches ▸ deadline)
  obtain ⟨finished, body, tail, complete, done⟩ := after
  have finalSplit : suffix = wait.append (.cons (.jump jump) (body.append tail)) := by rw [split, done]
  have word : suffix.deliveries = wait.deliveries ++ token :: (body.deliveries ++ tail.deliveries) := by
    rw [finalSplit, Execution.deliveries_append]
    change wait.deliveries ++ (jump.deliveries ++ (body.append tail).deliveries) = _
    rw [Execution.deliveries_append]
    simp only [paid, List.cons_append, List.nil_append]
  have unique := native_delivery_nodup suffix
  rw [word] at unique
  have tokenAbsent : token ∉ wait.deliveries ++ (body.deliveries ++ tail.deliveries) := by
    apply (List.nodup_cons.mp (List.perm_middle.nodup_iff.mp unique)).1
  have isolated (d : Delivery N) (member : d ∈ wait.deliveries ++ body.deliveries)
      (lower : base.time ≤ d.due) (upper : d.due ≤ finished.time) : d.cell ≠ i := by
    intro same
    have occurs : d ∈ suffix.deliveries := by
      rw [word]
      rcases List.mem_append.mp member with early | late
      · exact List.mem_append_left _ early
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ late))
    have fields := external_interval_token accepted (prefixRun.append suffix) fires wave d
      (by rw [Execution.deliveries_append]; exact List.mem_append_right _ occurs)
      (start ▸ lower) (complete.1 ▸ upper)
    have eq : d = token := by cases d; simp_all only [token]
    apply tokenAbsent
    rw [← eq]
    exact (List.sublist_append_left _ _).append_left _ |>.subset member
  refine ⟨before, admitted, finished, wait, jump, body, tail, finalSplit, paid, exactClock,
    complete.1, ?_, ?_⟩
  · intro d mem
    have bounds := wait.delivery_time_bounds d mem
    exact isolated d (List.mem_append_left _ mem) bounds.1
      (bounds.2.trans (by rw [exactClock, complete.1]; linarith))
  · intro d mem
    have bounds := body.delivery_time_bounds d mem
    exact isolated d (List.mem_append_right _ mem)
      (beforeIntake.le.trans (by simpa only [jump.time_unchanged, exactClock] using bounds.1)) bounds.2

/-- Exact local weak dose on the frozen auxiliary window, which can
include jumps and flows at other cells. -/
theorem training_window_doses {θ : Fin N → KernelR.Hybrid.Parameters}
    {route : Router N} {s u : Snapshot N} {ε : ℝ} (body : Execution θ route s u) (i : Fin N) (port : Port)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (ready : s.main i = .ready) (charge : s.x i .q ≤ 7 / 50)
    (gain : s.x i (.z port) ≤ Real.log (6 / 5) + 1 / 1000)
    (date : u.time = s.time + (auxDeadline : ℝ))
    (aux : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (active : s.raw i port = some s.time) (inactive : ∀ q, q ≠ port → s.raw i q = none)
    (isolated : ∀ q, NoArrivalAt body i q) :
    body.emissionTimes i = [] ∧
    (∀ q, body.ledger.error i q = if q = port then 3 / 5 else 0) ∧
    (∀ q, body.ledger.mark i q = 0) ∧ body.ledger.recovery i = 0 ∧
    (∀ q, u.raw i q = none ∧ u.aux i q = .ready) := by
  have deadline : s.time + 419 / 300 ≤ u.time := by rw [date]; norm_num [auxDeadline]
  obtain ⟨stays, silent⟩ := body.nominal_silent_input box physical.region i port ready charge gain
    (aux port).1 active (aux port).2 inactive isolated deadline
  obtain ⟨cycle⟩ := body.sensor_cycle box physical.region i port (aux port).1 active (aux port).2 deadline
  have margin := box.fast_nominal_headroom i port
  have headroom : s.x i (.z port) + 3 / 5 < Real.log ((θ i).cap port) := by linarith
  have selected := cycle.total_error_of_invariant box physical valid stays headroom active (isolated port)
  have other (q : Port) (ne : q ≠ port) := body.aux_no_input_rest_band i q (aux q).1 (aux q).2 (inactive q ne) (isolated q)
  have noMark (q : Port) : body.ledger.mark i q = 0 :=
    body.mark_zero_ready i q (body.allStates_main_flows i .ready stays)
  have dry := body.raw_expired_states i s.time valid (fun q => by
    by_cases same : q = port
    · subst q; exact Or.inr active
    · exact Or.inl (inactive q same)) isolated
  have expired : s.time + 1 < u.time := by rw [date]; norm_num [auxDeadline]
  refine ⟨silent, ?_, noMark, ?_, ?_⟩
  · intro q
    by_cases same : q = port
    · subst q; simpa using selected.1
    · have balance := body.gain_balance i q
      rw [(other q same).2] at balance
      simp [same]
      linarith
  · rw [body.recovery_sum_marks i]
    simp [noMark]
  · intro q
    refine ⟨body.allStates_final dry expired q, ?_⟩
    by_cases same : q = port
    · subst q; exact (cycle.final_rest valid active (isolated port)).1
    · exact (other q same).1.1

private theorem admission_fields {route : Router N} {before after : Snapshot N}
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

private theorem quiet_before_external {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {base before : Snapshot N} (wait : Execution θ route base before) (i : Fin N)
    (ready : ReadyCoordinates base i) (raw : ∀ q, base.raw i q = none)
    (isolated : ∀ token ∈ wait.deliveries, token.cell ≠ i) :
    ReadyCoordinates before i ∧ (∀ q, before.raw i q = none) ∧
      (∀ q, before.x i (.z q) = base.x i (.z q)) := by
  have noInput (q : Port) : NoArrivalAt wait i q := fun d mem => Or.inl (isolated d mem)
  have still := wait.ready_without_input_band i ready.ready ready.charge.2 raw noInput
  have flows := wait.allStates_main_flows i .ready still
  have dry (q : Port) := wait.raw_absent_of_no_arrival i q (raw q) (noInput q)
  have beforeCharge := wait.ready_no_current_solution i flows (fun q => (dry q).2)
  have cap := decay_upper (show base.x i .q - 1 / 10 ≤ (1 / 25 : ℝ) by linarith [ready.charge.2])
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) (sub_nonneg.mpr wait.time_monotone)
  have sensor (q : Port) := wait.aux_no_input_rest_band i q (ready.auxiliary q).1
    (ready.auxiliary q).2 (raw q) (noInput q)
  exact ⟨⟨wait.allStates_final still, ⟨wait.ready_charge_lower i flows ready.charge.1, by linarith⟩,
      fun q => (sensor q).1⟩, fun q => (dry q).1, fun q => (sensor q).2⟩

/-- Certification of an external weak row, starting from an actual quiet
anchor cut before that wave. -/
theorem training_row_from_anchor {p : Parameters N} (accepted : p.check = true)
    {base last : Snapshot N} (prefixRun : Execution (nativeParameters N) (router p) (prepared p) base)
    (suffix : Execution (nativeParameters N) (router p) base last)
    (wave : ExternalWave) (training : wave ≠ .launch) (i : Fin N)
    (anchor : base.time = wave.start p) (beforeIntake : base.time < wave.intake p)
    (ready : ReadyCoordinates base i) (raw : ∀ q, base.raw i q = none)
    (gain : base.x i (.z 0) ≤ Real.log (6 / 5) + 1 / 1000)
    (seen : rowAdmission (externalRow p (wave.intake p) wave.tag i) ∈
      NativeReciprocal.nativeAdmissions suffix)
    (fires : (prefixRun.append suffix).ledger.emissions.Perm
      ((List.finRange N).map (fun i => (i, launchDate p + latency p i))))
    (deadline : HasExecutionCut (prefixRun.append suffix) (wave.intake p + (auxDeadline : ℝ))) :
    RowDose p (prefixRun.append suffix) (externalRow p (wave.intake p) wave.tag i) := by
  obtain ⟨before, admitted, finished, wait, jump, body, tail, split, paid, intakeClock, finishClock,
    noWaitInput, noBodyInput⟩ := external_pulse_window accepted prefixRun suffix wave i anchor beforeIntake
      seen fires deadline
  let token : Delivery N := ⟨i, 0, wave.intake p⟩
  have rawPaid : jump.deliveries = [token] := paid
  obtain ⟨beforeReady, beforeRaw, beforeGain⟩ := quiet_before_external wait i ready raw noWaitInput
  obtain ⟨sameMain, sameAux, active, inactive⟩ := admission_fields jump token rawPaid beforeRaw
  let head := prefixRun.append wait
  let through := head.append (.cons (.jump jump) (.nil _))
  have rawValid : RawValid admitted := through.raw_valid (by intro _ _ _ h; cases h)
  have physical := through.physical_invariant (native_box N) (prepared_physical accepted)
  have rest : ∀ q, admitted.aux i q = .ready ∧ RestBand (admitted.x i (.m q)) := by
    intro q
    rw [sameAux, jump.physical_continuous]
    exact beforeReady.auxiliary q
  have doses := training_window_doses body i 0 (native_box N) physical rawValid
    (by rw [sameMain]; exact beforeReady.ready)
    (by rw [jump.physical_continuous]; exact beforeReady.charge.2)
    (by rw [jump.physical_continuous, beforeGain]; exact gain)
    (by rw [jump.time_unchanged, intakeClock]; exact finishClock)
    rest active inactive (fun _ d mem => Or.inl (noBodyInput d mem))
  have exactRun : prefixRun.append suffix = head.append (.cons (.jump jump) (body.append tail)) := by
    rw [split, Execution.append_assoc]
  have label : NativeReciprocal.jumpAdmissions jump =
      [rowAdmission (externalRow p (wave.intake p) wave.tag i)] := by
    apply jump_admission_of_delivery
    · cases wave <;> exact paid
    · cases wave <;> exact beforeReady.ready
  have weakTag : wave.tag = .first ∨ wave.tag = .second := by
    cases wave with
    | first => exact Or.inl rfl
    | second => exact Or.inr rfl
    | launch => exact (training rfl).elim
  refine ⟨before, admitted, finished, head, jump, body, tail, exactRun, label,
    intakeClock, finishClock, noBodyInput, ?_, ?_, ?_, ?_, ?_, doses.2.2.2.2⟩
  · rcases weakTag with tag | tag <;> simpa [externalRow, tag] using doses.1
  · intro q
    change body.ledger.error i q = if q = 0 ∧ (wave.tag = .first ∨ wave.tag = .second) then 3 / 5 else 0
    simpa [weakTag] using doses.2.1 q
  · intro q
    change body.ledger.mark i q = if q = 2 ∧ wave.tag = .receipt then 1 / 10 else 0
    rcases weakTag with tag | tag <;> simpa [tag] using doses.2.2.1 q
  · change body.ledger.recovery i = if wave.tag = .receipt then 1 / 10 else 0
    rcases weakTag with tag | tag <;> simpa [tag] using doses.2.2.2.1
  · intro bad
    change wave.tag = .receipt at bad
    rcases weakTag with tag | tag <;> rw [tag] at bad <;> cases bad

private theorem admissions_append {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u v : Snapshot N} (head : Execution θ route s u) (tail : Execution θ route u v) :
    NativeReciprocal.nativeAdmissions (head.append tail) =
      NativeReciprocal.nativeAdmissions head ++ NativeReciprocal.nativeAdmissions tail := by
  induction head with
  | nil => rfl
  | cons move rest ih => simp only [Execution.append, NativeReciprocal.nativeAdmissions, ih, List.append_assoc]

private theorem input_after_anchor {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u v : Snapshot N} (head : Execution θ route s u) (tail : Execution θ route u v)
    (a : NativeReciprocal.Admission N) (member : a ∈ NativeReciprocal.nativeAdmissions (head.append tail))
    (after : u.time < a.token.due) : a ∈ NativeReciprocal.nativeAdmissions tail := by
  rw [admissions_append] at member
  rcases List.mem_append.mp member with early | later
  · have delivered : a.token ∈ head.deliveries := by
      rw [← NativeReciprocal.admissions_deliveries]
      exact List.mem_map_of_mem early
    exact (not_lt_of_ge (head.delivery_time_bounds _ delivered).2 after).elim
  · exact later

private theorem first_settled_reference {p : Parameters N} (accepted : p.check = true)
    (h : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) h.last)
    (cuts : ∀ t ∈ exactCutDates p, HasExecutionCut run t) :
    ∃ (anchor : Snapshot N) (prefixRun : Execution (nativeParameters N) (router p) (prepared p) anchor)
      (suffix : Execution (nativeParameters N) (router p) anchor h.last),
      run = prefixRun.append suffix ∧ anchor.time = firstDate + 15 / 2 ∧
      anchor.ObservationalEq h.first.settled := by
  let reference := h.start.append (h.first.intake.append h.first.wave)
  have complete : CompleteThrough reference (firstDate + 15 / 2) := by
    rw [← h.firstDate]
    exact h.first.settledComplete
  obtain ⟨anchor, prefixRun, suffix, done, split⟩ := cuts (firstDate + 15 / 2) (by simp [exactCutDates])
  exact ⟨anchor, prefixRun, suffix, split, done.1,
    (prefixRun.observational_unique reference (native_box N) (prepared_physical accepted) done complete).1⟩

/-- Both training waves have the frozen per-row dose on the same exact run. -/
theorem exact_training_row_doses {p : Parameters N} (accepted : p.check = true)
    (h : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) h.last)
    (cuts : ∀ t ∈ exactCutDates p, HasExecutionCut run t)
    (fires : run.ledger.emissions.Perm ((List.finRange N).map (fun i => (i, launchDate p + latency p i))))
    (seenFirst : ∀ i, rowAdmission (externalRow p firstDate .first i) ∈ NativeReciprocal.nativeAdmissions run)
    (seenSecond : ∀ i, rowAdmission (externalRow p (secondDate p) .second i) ∈ NativeReciprocal.nativeAdmissions run) :
    ∀ i, RowDose p run (externalRow p firstDate .first i) ∧
      RowDose p run (externalRow p (secondDate p) .second i) := by
  obtain ⟨anchor, prefixRun, suffix, split, readyDate, observed⟩ := first_settled_reference accepted h run cuts
  have gap : (8 : ℝ) ≤ p.gap1 := by exact_mod_cast (of_decide_eq_true accepted : p.Valid).2.2.1.1
  have beforeSecond : anchor.time < secondDate p := by rw [readyDate]; unfold secondDate; linarith
  intro i
  refine ⟨?_, ?_⟩
  · have ready : ReadyCoordinates (prepared p) i := by
      refine ⟨rfl, ?_, fun _ => ⟨rfl, ?_⟩⟩ <;> norm_num [prepared, RestBand]
    exact training_row_from_anchor accepted (.nil _) run .first (by intro h; cases h) i rfl
      (by norm_num [prepared, ExternalWave.intake, firstDate]) ready (fun _ => rfl) (native_training_headroom accepted h i).1
      (seenFirst i) fires (cuts _ (by simp [exactCutDates, ExternalWave.intake]))
  · have ready : ReadyCoordinates anchor i := by
      have ref := h.first.settledReady i
      refine ⟨?_, ?_, ?_⟩
      · rw [observed.main]; exact ref.ready
      · rw [observed.values]; exact ref.charge
      · intro q; rw [observed.aux, observed.values]; exact ref.auxiliary q
    have raw (q : Port) : anchor.raw i q = none := by rw [observed.raw]; exact h.first.settledRaw i q
    have window : anchor.x i (.z 0) ≤ Real.log (6 / 5) + 1 / 1000 := by
      rw [observed.values]; exact (native_training_headroom accepted h i).2
    have member := input_after_anchor prefixRun suffix (rowAdmission (externalRow p (secondDate p) .second i))
      (split ▸ seenSecond i) beforeSecond
    have certified := training_row_from_anchor accepted prefixRun suffix .second (by intro h; cases h) i readyDate
      beforeSecond ready raw window member (split ▸ fires)
      (split ▸ cuts _ (by simp [exactCutDates, ExternalWave.intake]))
    rwa [← split] at certified

private theorem second_settled_reference {p : Parameters N} (accepted : p.check = true)
    (h : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) h.last)
    (cuts : ∀ t ∈ exactCutDates p, HasExecutionCut run t) :
    ∃ (anchor : Snapshot N) (prefixRun : Execution (nativeParameters N) (router p) (prepared p) anchor)
      (suffix : Execution (nativeParameters N) (router p) anchor h.last),
      run = prefixRun.append suffix ∧ anchor.time = secondDate p + 15 / 2 ∧
      anchor.ObservationalEq h.second.settled := by
  let reference := h.start.append (h.first.intake.append (h.first.wave.append
      (h.first.quiet.append (h.second.intake.append h.second.wave))))
  have complete : CompleteThrough reference (secondDate p + 15 / 2) := by
    have done := h.second.settledComplete
    have clock := congrArg (fun t => t + 15 / 2) h.first.date
    exact ⟨done.1.trans clock, done.2.1, fun token mem => clock ▸ done.2.2 token mem⟩
  obtain ⟨anchor, prefixRun, suffix, done, split⟩ := cuts (secondDate p + 15 / 2) (by simp [exactCutDates])
  exact ⟨anchor, prefixRun, suffix, split, done.1,
    (prefixRun.observational_unique reference (native_box N) (prepared_physical accepted) done complete).1⟩

private theorem launch_emission_at_window {p : Parameters N} {before admitted finished last : Snapshot N}
    (head : Execution (nativeParameters N) (router p) (prepared p) before)
    (jump : Jump (router p) before admitted)
    (body : Execution (nativeParameters N) (router p) admitted finished)
    (tail : Execution (nativeParameters N) (router p) finished last)
    (i : Fin N) (token : Delivery N) (paid : jump.deliveries = [token])
    (clock : before.time = launchDate p) (endClock : finished.time = launchDate p + (auxDeadline : ℝ))
    (early : 0 < latency p i) (late : latency p i < (auxDeadline : ℝ))
    (all : (head.append (.cons (.jump jump) (body.append tail))).emissionTimes i =
      [launchDate p + latency p i]) : body.emissionTimes i = [launchDate p + latency p i] := by
  have silent := jump.no_emissions_of_delivery token (by rw [paid]; simp)
  have pieces := all
  simp only [Execution.emissionTimes_append, Execution.emissionTimes_cons, Move.ledger, silent,
    List.filter_nil, List.map_nil, List.nil_append] at pieces
  have noEarly : head.emissionTimes i = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro date mem
    have inWord := List.mem_append_left (body.emissionTimes i ++ tail.emissionTimes i) mem
    rw [pieces, List.mem_singleton] at inWord
    obtain ⟨event, inEvents, eq⟩ := List.mem_map.mp mem
    have bound := (head.emission_time_bounds event (List.mem_filter.mp inEvents).1).2
    rw [clock, eq, inWord] at bound
    linarith
  have noLate : tail.emissionTimes i = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro date mem
    have inWord := List.mem_append_right (head.emissionTimes i)
      (List.mem_append_right (body.emissionTimes i) mem)
    rw [pieces, List.mem_singleton] at inWord
    obtain ⟨event, inEvents, eq⟩ := List.mem_map.mp mem
    have bound := (tail.emission_time_bounds event (List.mem_filter.mp inEvents).1).1
    rw [endClock, eq, inWord] at bound
    linarith
  simpa only [noEarly, noLate, List.nil_append, List.append_nil] using pieces

/-- Launch rows have one exact FIRE and zero ERROR and MARK on their
physical auxiliary windows. The wire cut is before any receipt. -/
theorem exact_launch_row_doses {p : Parameters N} (accepted : p.check = true)
    (h : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) h.last)
    (cuts : ∀ t ∈ exactCutDates p, HasExecutionCut run t)
    (fired : run.ledger.emissions = h.run.ledger.emissions)
    (seen : ∀ i, rowAdmission (externalRow p (launchDate p) .launch i) ∈ NativeReciprocal.nativeAdmissions run) :
    ∀ i, RowDose p run (externalRow p (launchDate p) .launch i) := by
  obtain ⟨anchor, prefixRun, suffix, split, readyDate, observed⟩ := second_settled_reference accepted h run cuts
  obtain ⟨wire, wireHead, _, wireDone, _, wireSection, _, _, _⟩ := native_exact_wire_cut accepted h run cuts fired
  have gap : (8 : ℝ) ≤ p.gap2 := by exact_mod_cast (of_decide_eq_true accepted : p.Valid).2.2.1.2
  have beforeLaunch : anchor.time < launchDate p := by rw [readyDate]; unfold launchDate; linarith
  have deadline : HasExecutionCut run (launchDate p + (auxDeadline : ℝ)) := cuts _ (by simp [exactCutDates])
  have exactFires := native_fires_frozen h run fired
  let box := native_box N
  intro i
  have member := input_after_anchor prefixRun suffix (rowAdmission (externalRow p (launchDate p) .launch i))
    (split ▸ seen i) beforeLaunch
  obtain ⟨before, admitted, finished, wait, jump, body, tail, slice, paid, clock, endClock,
    noWaitInput, noBodyInput⟩ := external_pulse_window accepted prefixRun suffix .launch i readyDate beforeLaunch
      member (split ▸ exactFires) (split ▸ deadline)
  let head := prefixRun.append wait
  have whole : run = head.append (.cons (.jump jump) (body.append tail)) := by
    rw [split, slice, Execution.append_assoc]
  have ready : ReadyCoordinates anchor i := by
    have ref := h.second.settledReady i
    refine ⟨?_, ?_, ?_⟩
    · rw [observed.main]; exact ref.ready
    · rw [observed.values]; exact ref.charge
    · intro q; rw [observed.aux, observed.values]; exact ref.auxiliary q
  have raw (q : Port) : anchor.raw i q = none := by rw [observed.raw]; exact h.second.settledRaw i q
  obtain ⟨beforeReady, beforeRaw, beforeGain⟩ := quiet_before_external wait i ready raw noWaitInput
  let token : Delivery N := ⟨i, 0, launchDate p⟩
  have paidToken : jump.deliveries = [token] := paid
  obtain ⟨_, sameAux, active, inactive⟩ := admission_fields jump token paidToken beforeRaw
  have aux (q : Port) : admitted.aux i q = .ready ∧ RestBand (admitted.x i (.m q)) := by
    rw [sameAux, jump.physical_continuous]
    exact beforeReady.auxiliary q
  let through := head.append (.cons (.jump jump) (.nil _))
  have valid : RawValid admitted := through.raw_valid (by intro _ _ _ raw; cases raw)
  have physical := through.physical_invariant box (prepared_physical accepted)
  have date : finished.time = admitted.time + (auxDeadline : ℝ) := by
    rw [jump.time_unchanged, clock]; exact endClock
  have long : admitted.time + 419 / 300 ≤ finished.time := by rw [date]; norm_num [auxDeadline]
  have noInput (q : Port) : NoArrivalAt body i q := fun d mem => Or.inl (noBodyInput d mem)
  obtain ⟨cycle⟩ := body.sensor_cycle box physical.region i 0 (aux 0).1 active (aux 0).2 long
  have expired : admitted.time + 1 < finished.time := by rw [date]; norm_num [auxDeadline]
  have dry := body.raw_expired_states i admitted.time valid (fun q => by
    by_cases eq : q = 0
    · subst q; exact Or.inr active
    · exact Or.inl (inactive q eq)) noInput
  have settled (q : Port) : finished.raw i q = none ∧ finished.aux i q = .ready := by
    refine ⟨body.allStates_final dry expired q, ?_⟩
    by_cases eq : q = 0
    · subst q; exact (cycle.final_rest valid active (noInput 0)).1
    · exact (body.aux_no_input_rest_band i q (aux q).1 (aux q).2 (inactive q eq) (noInput q)).1.1
  have launchCount : body.emissionTimes i = [launchDate p + latency p i] := by
    have observedFires : run.emissionTimes i = [launchDate p + latency p i] := by
      simpa only [Execution.emissionTimes, fired, h.emissions] using h.fires i
    have bounds := scalar_latency accepted i
    exact launch_emission_at_window head jump body tail i token paidToken clock endClock
      (by linarith [bounds.1]) (by norm_num [auxDeadline]; linarith [bounds.2.1]) (whole ▸ observedFires)
  have anchorGain (q : Port) : anchor.x i (.z q) = h.last.x i (.z q) := by
    rw [observed.values, h.second.settledGains, h.first.gains, h.startGain, h.endpointGain]
    by_cases eq : q = 0
    · simp [eq]
      ring
    · simp [eq]
  have noError (q : Port) : body.ledger.error i q = 0 := by
    have startGain : admitted.x i (.z q) = h.last.x i (.z q) := by
      rw [jump.physical_continuous, beforeGain, anchorGain]
    have balance := body.gain_balance i q
    have monotone := tail.gain_nondecreasing box i q
    have nonnegative := body.section_error_nonnegative box i q
    linarith
  let throughBody := through.append body
  have splitBody : run = throughBody.append tail := by
    simp only [whole, throughBody, through, Execution.append_assoc, Execution.append]
  have wireLater : finished.time < launchDate p + 19 / 10 := by
    rw [endClock]
    norm_num [ExternalWave.intake, auxDeadline]
  obtain ⟨after, extra, _, afterDone, _⟩ := HasExecutionCut.after_prefix throughBody tail wireLater
    (splitBody ▸ cuts _ (by simp [exactCutDates] : launchDate p + 19 / 10 ∈ exactCutDates p))
  have afterComplete : CompleteThrough (throughBody.append extra) (launchDate p + 19 / 10) := afterDone
  have agrees := ((throughBody.append extra).observational_unique wireHead box (prepared_physical accepted)
    afterComplete wireDone).1
  have recoveryAfter : after.x i .b = 9 / 50 := by rw [agrees.values]; exact wireSection.recovery i
  have anchorRecovery : anchor.x i .b = 9 / 50 := by
    rw [observed.values, h.second.settledRecovery, h.first.recovery, h.startRecovery]
    rfl
  have warm : 9 / 50 ≤ admitted.x i .b := by
    rw [jump.physical_continuous, ← anchorRecovery]
    exact wait.recovery_nondecreasing box i
  have noRecovery : body.ledger.recovery i = 0 := by
    have balance := body.recovery_balance i
    have b := body.recovery_nondecreasing box i
    have rest := extra.recovery_nondecreasing box i
    rw [recoveryAfter] at rest
    linarith
  have noMark (q : Port) : body.ledger.mark i q = 0 := by
    have sum := body.recovery_sum_marks i
    rw [noRecovery] at sum
    have upper := Finset.single_le_sum (f := fun q => body.ledger.mark i q)
      (fun q _ => body.section_mark_nonnegative box i q) (Finset.mem_univ q)
    linarith [body.section_mark_nonnegative box i q]
  have label : NativeReciprocal.jumpAdmissions jump = [rowAdmission (externalRow p (launchDate p) .launch i)] :=
    jump_admission_of_delivery jump _ paid beforeReady.ready
  refine ⟨before, admitted, finished, head, jump, body, tail, whole, label, clock, endClock, noBodyInput,
    launchCount, ?_, ?_, noRecovery, ?_, settled⟩
  · intro q
    simpa [externalRow] using noError q
  · intro q
    simpa [externalRow] using noMark q
  · intro bad
    cases bad

private theorem native_total_doses {p : Parameters N} (accepted : p.check = true)
    (h : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) h.last)
    (receipt : ∀ source, RowDose p run (receiptRow p source)) :
    ∀ i, run.ledger.error i 0 = 2 * unitDose .port0 ∧ run.ledger.error i 1 = 0 ∧
      run.ledger.error i 2 = 0 ∧ run.ledger.mark i 0 = 0 ∧ run.ledger.mark i 1 = 0 ∧
      run.ledger.mark i 2 = unitDose .recovery := by
  let box := native_box N
  intro i
  have err (q : Port) : run.ledger.error i q = if q = 0 then 6 / 5 else 0 := by
    have balance := run.gain_balance i q
    rw [h.endpointGain] at balance
    linarith
  have warm : run.ledger.recovery i = 1 / 10 := by
    have balance := run.recovery_balance i
    rw [h.endpointRecovery] at balance
    change (7 / 25 : ℝ) = 9 / 50 + run.ledger.recovery i at balance
    linarith
  have total : ∑ q : Port, run.ledger.mark i q = 1 / 10 := (run.recovery_sum_marks i).symm.trans warm
  let source := sourceOf accepted i
  have target : p.successor source = i := sourceOf_receives accepted i
  obtain ⟨before, admitted, finished, head, arrival, body, tail, split, _, _, _, _, _, _, mark, _⟩ := receipt source
  have selected : body.ledger.mark i 2 = 1 / 10 := by
    have localDose := mark 2
    change body.ledger.mark (p.successor source) 2 = (if (2 : Port) = 2 ∧ Stage.receipt = .receipt then 1 / 10 else 0) at localDose
    simpa only [target, true_and, ite_true] using localDose
  have lower : 1 / 10 ≤ run.ledger.mark i 2 := by
    rw [split, Execution.mark_append]
    change 1 / 10 ≤ head.ledger.mark i 2 + (arrival.ledger.mark i 2 + (body.append tail).ledger.mark i 2)
    rw [arrival.no_mark_actuation, Execution.mark_append, selected]
    linarith [head.section_mark_nonnegative box i 2, tail.section_mark_nonnegative box i 2]
  have m0 := run.section_mark_nonnegative box i 0
  have m1 := run.section_mark_nonnegative box i 1
  have all : run.ledger.mark i 0 + run.ledger.mark i 1 + run.ledger.mark i 2 = 1 / 10 := by
    simp [Fin.sum_univ_succ] at total
    linarith
  exact ⟨by unfold unitDose; linarith [show run.ledger.error i 0 = 6 / 5 from err 0],
    by simpa using err 1, by simpa using err 2,
    by linarith, by linarith, by unfold unitDose; linarith⟩

/-- All frozen physical row doses and the native queue correspondence hold
on one complete execution with the guarded replay. -/
theorem native_with_exact_row_doses {p : Parameters N} (accepted : p.check = true) :
    ∃ (last : Snapshot N) (run : Execution (nativeParameters N) (router p) (prepared p) last)
      (rows : List (Row N)) (out : State N),
      (CompleteThrough run (horizon p) ∧ run.ContactsTransversal ∧
      TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) rows out ∧
      rows.length = 4 * N ∧ rows.map rowAdmission = NativeReciprocal.nativeAdmissions run ∧
      (Transaction.fires inputCell rows).Perm run.ledger.emissions ∧
      run.ledger.emissions.Perm ((List.finRange N).map (fun i => (i, launchDate p + latency p i))) ∧
      (∀ row ∈ rows, RowMatches p row ∧ RowDose p run row) ∧
      (∀ i, run.ledger.error i 0 = 2 * unitDose .port0 ∧ run.ledger.error i 1 = 0 ∧
        run.ledger.error i 2 = 0 ∧ run.ledger.mark i 0 = 0 ∧ run.ledger.mark i 1 = 0 ∧
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
      AutonomousFeedback.Schedule.SafeMemory Q d B rail (fun _ => 0) out ∧
      (∀ i c, out.writes (Address.mk i c).encode =
        match c with | .port0 => 2 | .port1 => 0 | .recovery => 1) ∧
      (∀ other word, Trace (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) word other →
        word.length ≤ 4 * N ∧
        (∀ entry ∈ word, entry.2 = targetDecision entry.1.input) ∧
        (other.pending = [] → word.Perm (Transaction.word rows) ∧ other.writes = out.writes) ∧
        ∃ terminal suffix, Trace (calendar p) d (· ≤ ·) other suffix terminal ∧ terminal.pending = [] ∧
          (word ++ suffix).Perm (Transaction.word rows) ∧ terminal.writes = out.writes) ∧
      (∀ (other : Snapshot N)
        (comparison : Execution (nativeParameters N) (router p) (prepared p) other),
        CompleteThrough comparison (horizon p) →
          last.ObservationalEq other ∧ run.ledger.emissions.Perm comparison.ledger.emissions)) ∧
      QuietSuffix p run := by
  obtain ⟨history, run, complete, drained, cuts, _, admitted, fires, _, _, _, contacts⟩ :=
    native_exact_execution accepted
  obtain ⟨receipts, out, replay, word, length, outDrained, physical, kinds, writes⟩ :=
    exact_guarded_replay accepted history run cuts admitted fires
  let first := (List.finRange N).map (externalRow p firstDate .first)
  let second := (List.finRange N).map (externalRow p (secondDate p) .second)
  let launch := (List.finRange N).map (externalRow p (launchDate p) .launch)
  let rows := first ++ second ++ launch ++ receipts
  have admittedRow (r : Row N) (mem : r ∈ rows) : rowAdmission r ∈ NativeReciprocal.nativeAdmissions run := by
    rw [← word]
    exact List.mem_map_of_mem mem
  have seenFirst (i : Fin N) : externalRow p firstDate .first i ∈ first := List.mem_map_of_mem (List.mem_finRange i)
  have seenSecond (i : Fin N) : externalRow p (secondDate p) .second i ∈ second := List.mem_map_of_mem (List.mem_finRange i)
  have seenLaunch (i : Fin N) : externalRow p (launchDate p) .launch i ∈ launch := List.mem_map_of_mem (List.mem_finRange i)
  have fireWord := native_fires_frozen history run fires
  have pulse := exact_training_row_doses accepted history run cuts fireWord
    (fun i => admittedRow _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (seenFirst i)))))
    (fun i => admittedRow _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (seenSecond i)))))
  have strong := exact_launch_row_doses accepted history run cuts fires
    (fun i => admittedRow _ (List.mem_append_left _ (List.mem_append_right _ (seenLaunch i))))
  have exactRows (r : Row N) (mem : r ∈ rows) : RowMatches p r ∧ RowDose p run r := by
    simp only [rows, List.mem_append] at mem
    rcases mem with (((train1 | train2) | fire) | receipt)
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp train1
      exact ⟨(external_row_matches accepted i).1, (pulse i).1⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp train2
      exact ⟨(external_row_matches accepted i).2.1, (pulse i).2⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp fire
      exact ⟨(external_row_matches accepted i).2.2, strong i⟩
    · exact (physical r receipt).2
  have rowFires : Transaction.fires inputCell rows =
      (List.finRange N).map (fun i => (i, launchDate p + latency p i)) := scheduled_row_fires receipts kinds
  have wireQueue : ∃ (cut : Snapshot N) (head : Execution (nativeParameters N) (router p) (prepared p) cut)
      (tail : Execution (nativeParameters N) (router p) cut history.last),
      run = head.append tail ∧ head.ledger.emissions.length = N ∧
        cut.pending.Perm (rows.flatMap (fun row => row.children.map toDelivery)) := by
    obtain ⟨cut, head, tail, _, split, wires, count, _, _⟩ := native_exact_wire_cut accepted history run cuts fires
    have children : rows.flatMap (fun row => row.children.map toDelivery) =
        (List.finRange N).map (receiptToken p) := by
      rw [planned_children_word (fun r mem => (exactRows r mem).1), rowFires, List.flatMap_map]
      calc
        _ = (List.finRange N).flatMap (fun i => [receiptToken p i]) := by
          apply List.flatMap_congr
          intro i _
          exact router_launch accepted i
        _ = _ := by
          rw [← List.flatMap_map (receiptToken p) (fun d => [d]) (List.finRange N)]
          exact List.flatMap_singleton' _
    exact ⟨cut, head, tail, split, count, children.symm ▸ wires.queue⟩
  obtain ⟨states, flows⟩ := all_below_rail_of_endpoint run (native_endpoint_below_rail accepted history)
  obtain ⟨safe, universal⟩ := guarded_trace_refinement accepted replay (fun r mem => (exactRows r mem).1) outDrained
  refine ⟨history.last, run, rows, out, ⟨complete, contacts.mpr history.contacts_transversal, replay, length, word,
    rowFires.symm ▸ fireWord.symm, fireWord, exactRows, ?_, ?_, exact_training_cuts accepted history run cuts,
    wireQueue, drained, outDrained, settled_replay_memory history out writes, states, flows, safe, writes, universal, ?_⟩,
    native_exact_quiet_suffix accepted history run cuts fires⟩
  · exact native_total_doses accepted history run (receipt_row_doses accepted history run cuts fires)
  · exact exact_prefix_correspondence accepted history run cuts receipts kinds out replay word fireWord
  · intro other comparison otherComplete
    exact native_horizon_unique run comparison (prepared_physical accepted) complete otherComplete

/-- Every tuple accepted by the frozen checker satisfies the full native
multi-token refinement. -/
theorem native_multi_token_refinement : NativeMultiTokenRefinement := by
  intro N p accepted
  obtain ⟨reserve, rank, causal, ties⟩ := guarded_conjuncts accepted
  obtain ⟨last, run, rows, out, refinement, _⟩ := native_with_exact_row_doses accepted
  exact ⟨reserve, rank, causal, ties, scalar_latency accepted, last, run, rows, out, refinement⟩

end NetworkStability.NativeMultiToken
