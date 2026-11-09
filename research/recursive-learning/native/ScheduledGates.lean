import LearnerFanIn

/-! A report is a FIRE in a declared interval. An earlier physical FIRE
may prepare a gate. Only the declared interval is connected downstream. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

structure ReportWindow where
  start : ℝ
  stop : ℝ

noncomputable def ReportWindow.accepts (w : ReportWindow) (F : ℝ) : Bool :=
  decide (w.start ≤ F ∧ F < w.stop)

noncomputable def ReportWindow.dates {n θ route s u} (w : ReportWindow)
    (e : @Execution n θ route s u) (i : Fin n) : List ℝ :=
  (e.emissionTimes i).filter w.accepts

/-- A report carries one bit, with exactly one physical firing date for a
true bit. The sender can have other physical events outside the window. -/
def Reports {n θ route s u} (e : @Execution n θ route s u) (i : Fin n)
    (w : ReportWindow) (bit : Bool) : Prop :=
  (w.dates e i).length = if bit then 1 else 0

/-- The contract records the actual input deliveries and the output
report. A client may additionally specify an effect on the endpoint. -/
structure ScheduledCell (θ : Fin 1 → Parameters) (start : Snapshot 1)
    (T : ℝ) (window : ReportWindow) (bit : Bool) (effect : Snapshot 1 → Prop) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) start final
  complete : CompleteThrough execution T
  transverse : execution.ContactsTransversal
  deliveries : execution.deliveries.Perm start.pending
  reports : Reports execution 0 window bit
  effect_holds : effect final

private theorem report_option_length {fire : Option ℝ} {bit : Bool} (h : fire.isSome = bit) :
    fire.toList.length = if bit then 1 else 0 := by
  cases fire <;> rw [← h] <;> rfl

noncomputable def counterWindow (read : ℝ) : ReportWindow := ⟨read, read + 1⟩

noncomputable def conjunction_report_contract {θ start calendar T third read}
    (r : CalendarDoseReadout θ start calendar (conjunctionProbe read) T third)
    (queue : start.pending = calendar) :
    ScheduledCell θ (withFuture start [conjunctionProbe read]) T (counterWindow read) third
      (fun s => s.pending = []) := by
  refine ⟨r.final, r.execution, r.complete, r.transverse, ?_, ?_, r.empty⟩
  · rw [r.deliveries]
    change (calendar ++ [conjunctionProbe read]).Perm ([conjunctionProbe read] ++ start.pending)
    rw [queue]
    exact List.perm_append_comm
  · have emissions : r.execution.emissionTimes 0 = r.fire.toList := by
      rw [Execution.emissionTimes, r.emissions]
      cases r.fire <;> rfl
    unfold Reports ReportWindow.dates
    rw [emissions]
    have kept : r.fire.toList.filter (counterWindow read).accepts = r.fire.toList := by
      cases h : r.fire with
      | none => rfl
      | some F =>
        have bounds := r.window F h
        change read < F ∧ F < read + 1 at bounds
        simp [ReportWindow.accepts, counterWindow, bounds.1.le, bounds.2]
    rw [kept]
    exact report_option_length r.reports

noncomputable def notWindow (clock : ℝ) : ReportWindow := ⟨clock + 17, clock + 18⟩

noncomputable def notTrigger (clock : ℝ) : Delivery 1 := ⟨0, 1, clock + 1⟩

noncomputable def notExternal (clock : ℝ) : List (Delivery 1) := lessonProbeQueue false clock

noncomputable def scheduledNotStart (origin clock : ℝ) (present : Bool) : Snapshot 1 :=
  {lessonProbeStart present clock with time := origin}

private theorem not_sources_future {clock : ℝ} {present : Bool} :
    ∀ d ∈ (lessonProbeStart present clock).pending, clock ≤ d.due ∧ d.due ≤ clock + 17 := by
  intro d h
  cases present
  all_goals simp [lessonProbeStart, lessonProbeQueue] at h
  all_goals rcases h with rfl | h
  all_goals try rcases h with rfl | rfl
  all_goals dsimp
  all_goals constructor <;> linarith

private theorem not_readout_dates {θ present clock}
    (r : LessonProbeRun θ present clock (clock + 26)) :
    Reports r.execution 0 (notWindow clock) (!present) := by
  have admission : ((notWindow clock).dates r.admission.execution 0) = [] := by
    unfold ReportWindow.dates Execution.emissionTimes
    rw [List.filter_map]
    apply List.map_eq_nil_iff.mpr
    apply List.filter_eq_nil_iff.mpr
    intro ev hv
    have early := r.admission.earlyEmissions ev (List.mem_filter.mp hv).1
    simp [ReportWindow.accepts, notWindow, not_le.mpr early]
  unfold Reports ReportWindow.dates at *
  rw [LessonProbeRun.execution, Execution.emissionTimes_append, List.filter_append, admission, List.nil_append]
  cases present with
  | true =>
    have no : r.readout.ledger.emissions = [] := r.emissions
    simp [Execution.emissionTimes, no]
  | false =>
    obtain ⟨F, fire⟩ := r.emissions
    have mem : (0, F) ∈ r.readout.ledger.emissions := by simp [fire]
    have after := (r.readout.emission_time_bounds (0, F) mem).1
    rw [r.admission.complete.1] at after
    have before := r.earlyReadout _ mem
    change clock + 17 ≤ F at after
    change F < clock + 18 at before
    simp [Execution.emissionTimes, fire, ReportWindow.accepts, notWindow, after, before]

/-- A diagnostic cell reports precisely when its optional trigger was
absent. In the other case the trigger causes a preparation FIRE outside
the report window. Both cases receive the same two external pulses. -/
theorem scheduled_not_exists {θ ε origin clock T} (box : @PhysicalBox 1 θ ε)
    (before : origin < clock) (horizon : clock + 45 < T) (present : Bool) :
    Nonempty (ScheduledCell θ (scheduledNotStart origin clock present) T (notWindow clock)
      (!present) (fun s => s.pending = [])) := by
  let start := lessonProbeStart present clock
  obtain ⟨lead, prefPositive, prefSilent, _⟩ := rest_prefix (θ := θ) (s := start) before
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun d hd => (not_sources_future d hd).1)
  obtain ⟨r, dispatch⟩ := lesson_probe_dispatch_state_exists box present clock
  obtain ⟨tail⟩ := learner_wait_exists (θ := θ) (T := T) dispatch r.pendingEmpty
    (by rw [r.complete.1]; linarith)
  let e : Execution θ (fun _ _ => []) (scheduledNotStart origin clock present) tail.final :=
    (lead.append r.execution).append tail.execution
  have pos := (Execution.contactsTransversal_append _ _).2
    ⟨(Execution.contactsTransversal_append _ _).2 ⟨prefPositive, r.contacts_transversal⟩, tail.transverse⟩
  have allDue : ∀ d ∈ (scheduledNotStart origin clock present).pending, d.due ≤ T := by
    intro d h
    have due := (not_sources_future d h).2
    linarith
  refine ⟨⟨_, e, tail.complete, pos, e.deliveries_perm_sources T tail.complete allDue (fun _ _ => rfl),
    ?_, tail.empty⟩⟩
  have pp : lead.emissionTimes 0 = [] := by simp [Execution.emissionTimes, prefSilent]
  have tt : tail.execution.emissionTimes 0 = [] := by simp [Execution.emissionTimes, tail.silent]
  have same : e.emissionTimes 0 = r.execution.emissionTimes 0 := by
    change ((lead.append r.execution).append tail.execution).emissionTimes 0 = _
    rw [Execution.emissionTimes_append, Execution.emissionTimes_append, pp, tt, List.nil_append, List.append_nil]
  unfold Reports ReportWindow.dates
  rw [same]
  exact not_readout_dates r

/-- A report may schedule a whole list of inputs. A reserved time after
the report window makes every delivery strictly causal. -/
noncomputable def forwardReport {n} (sender : Fin n) (w : ReportWindow) (tokens : List (Delivery 1)) :
    HeadRoutes n := atCell sender (fun F => if w.accepts F then tokens else [])

theorem forward_report_strict {n} (sender : Fin n) (w : ReportWindow) {tokens : List (Delivery 1)}
    (after : ∀ d ∈ tokens, w.stop ≤ d.due) : StrictHeadRoutes (forwardReport sender w tokens) := by
  apply atCell_strict
  intro F d mem
  by_cases h : w.start ≤ F ∧ F < w.stop
  · exact h.2.trans_le (after d (by simpa [ReportWindow.accepts, h] using mem))
  · simp [ReportWindow.accepts, h] at mem

private theorem flat_map_report (w : ReportWindow) (tokens : List (Delivery 1)) (dates : List ℝ) :
    dates.flatMap (fun F => if w.accepts F then tokens else []) =
      (dates.filter w.accepts).flatMap (fun _ => tokens) := by
  induction dates with
  | nil => rfl
  | cons date dates ih =>
    cases h : w.accepts date <;> simp [h, ih]

theorem forward_report_inputs {n θ route s u}
    (e : @Execution n θ route s u) (sender : Fin n) (w : ReportWindow) (tokens : List (Delivery 1))
    (bit : Bool) (reports : Reports e sender w bit) :
    e.headInputQueue (forwardReport sender w tokens) = if bit then tokens else [] := by
  rw [forwardReport, atCell_inputs, flat_map_report]
  change (w.dates e sender).flatMap (fun _ => tokens) = _
  cases bit with
  | false =>
    have empty : w.dates e sender = [] := List.length_eq_zero_iff.mp reports
    simp [empty]
  | true =>
    obtain ⟨F, date⟩ := List.length_eq_one_iff.mp reports
    simp [date]

private theorem scheduled_not_pending (origin clock : ℝ) (bit : Bool) :
    (scheduledNotStart origin clock bit).pending =
      (if bit then [notTrigger clock] else []) ++ notExternal clock := by
  rfl

/-- Attach a NOT to any certified sender. Its trigger is routed from the
sender's report window; the diagnostic and read pulses are external.
The new report bit is the negation of the sender's report bit. -/
theorem compose_report_not {n θ θH ε route s u T clock}
    (send : @Execution n θ route s u) (done : CompleteThrough send T)
    (box : @PhysicalBox 1 θH ε) (sender : Fin n) (inputWindow : ReportWindow) (bit : Bool)
    (reports : Reports send sender inputWindow bit)
    (before : s.time < clock) (horizon : clock + 45 < T) (margin : inputWindow.stop ≤ clock + 1) :
    ∃ (receiver : ScheduledCell θH (scheduledNotStart s.time clock bit) T (notWindow clock)
        (!bit) (fun q => q.pending = []))
      (weave : CausalHeadWeave send receiver.execution
        (independentHeadQueue s ((scheduledNotStart s.time clock bit).requeue (notExternal clock)))
        (forwardReport sender inputWindow [notTrigger clock])),
      CompleteThrough weave.execution T ∧
      Reports weave.execution 0 (notWindow clock) (!bit) ∧
      (∀ i, weave.execution.emissionTimes i.succ = send.emissionTimes i) := by
  obtain ⟨receiver⟩ := scheduled_not_exists box before horizon bit
  let contacts := forwardReport sender inputWindow [notTrigger clock]
  have causal : StrictHeadRoutes contacts := forward_report_strict sender inputWindow (by
    intro d h
    obtain rfl := List.mem_singleton.mp h
    exact margin)
  have queue : (notExternal clock ++ send.headInputQueue contacts).Perm
      (scheduledNotStart s.time clock bit).pending := by
    rw [scheduled_not_pending, show send.headInputQueue contacts = _ from
      forward_report_inputs send sender inputWindow [notTrigger clock] bit reports]
    exact List.perm_append_comm
  obtain ⟨weave⟩ := compose_scheduled_receiver send receiver.execution done receiver.complete
    rfl (notExternal clock) contacts causal queue
  refine ⟨receiver, weave, weave.complete done receiver.complete, ?_, weave.tail_emission_times⟩
  unfold Reports ReportWindow.dates
  rw [weave.head_emission_times]
  exact receiver.reports

/-- A wire samples one sender window and schedules one delivery. The
same sender and window may be used by several wires. -/
structure ReportWire (n : ℕ) where
  sender : Fin n
  window : ReportWindow
  due : ℝ

noncomputable def reportWireContacts {n} (wires : List (ReportWire n)) : HeadRoutes n :=
  fun i F => wires.flatMap (fun wire =>
    forwardReport wire.sender wire.window [⟨0, 0, wire.due⟩] i F)

theorem report_wire_contacts_strict {n} {wires : List (ReportWire n)}
    (margin : ∀ wire ∈ wires, wire.window.stop ≤ wire.due) :
    StrictHeadRoutes (reportWireContacts wires) := by
  intro i F d h
  obtain ⟨wire, mem, delivered⟩ := List.mem_flatMap.mp h
  apply forward_report_strict wire.sender wire.window _ i F d delivered
  intro d hd
  obtain rfl := List.mem_singleton.mp hd
  exact margin wire mem

def receivedReportDates {n} (wires : List (ReportWire n)) (bits : ReportWire n → Bool) : List ℝ :=
  (wires.filter bits).map ReportWire.due

theorem report_wire_contacts_inputs {n θ route s u}
    (e : @Execution n θ route s u) (wires : List (ReportWire n)) (bits : ReportWire n → Bool)
    (reports : ∀ wire ∈ wires, Reports e wire.sender wire.window (bits wire)) :
    (e.headInputQueue (reportWireContacts wires)).Perm (conjunctionDoseTokens 0 (receivedReportDates wires bits)) := by
  induction wires with
  | nil => simp [Execution.headInputQueue, reportWireContacts, receivedReportDates, conjunctionDoseTokens]
  | cons wire wires ih =>
    let one := forwardReport wire.sender wire.window [⟨0, 0, wire.due⟩]
    let tail := reportWireContacts wires
    have split := (List.flatMap_append_perm e.ledger.emissions
      (fun ev => one ev.1 ev.2) (fun ev => tail ev.1 ev.2)).symm
    change (e.headInputQueue (reportWireContacts (wire :: wires))).Perm
      (e.headInputQueue one ++ e.headInputQueue tail) at split
    have first : e.headInputQueue one = if bits wire then [⟨0, 0, wire.due⟩] else [] :=
      forward_report_inputs e wire.sender wire.window _ (bits wire) (reports wire (by simp))
    have rest := ih (fun w hw => reports w (by simp [hw]))
    refine split.trans ((rest.append_left (e.headInputQueue one)).trans (List.Perm.of_eq ?_))
    rw [first]
    cases h : bits wire <;> simp [receivedReportDates, conjunctionDoseTokens, h]

private theorem reports_count {n} (wires : List (ReportWire n)) (bits : ReportWire n → Bool) :
    (receivedReportDates wires bits).length ≤ wires.length ∧
    ((receivedReportDates wires bits).length = wires.length ↔ ∀ wire ∈ wires, bits wire = true) := by
  simp only [receivedReportDates, List.length_map]
  exact ⟨List.length_filter_le _ _, List.length_filter_eq_length_iff⟩

noncomputable def scheduledAndStart (origin read : ℝ) (arity : ℕ) : Snapshot 1 :=
  (conjunctionCounter origin arity).requeue [conjunctionProbe read]

/-- A report-driven AND can be appended to any native execution. Wires
have separated receiver slots, and the read follows every possible dose.
The router and external input are independent of the reports. -/
theorem compose_report_and {n θ θH ε route s u T read}
    (send : @Execution n θ route s u) (done : CompleteThrough send T)
    (box : @PhysicalBox 1 θH ε) (wires : List (ReportWire n)) (bits : ReportWire n → Bool)
    (nonempty : 0 < wires.length)
    (reports : ∀ wire ∈ wires, Reports send wire.sender wire.window (bits wire))
    (margin : ∀ wire ∈ wires, wire.window.stop ≤ wire.due)
    (future : ∀ wire ∈ wires, s.time < wire.due)
    (gap : wires.Pairwise (fun x y => x.due + 8 ≤ y.due))
    (beforeRead : ∀ wire ∈ wires, wire.due + 15 / 2 < read)
    (before : s.time < read) (afterRead : read + 23 ≤ T) :
    ∃ (v : Snapshot (n + 1))
      (e : Execution (prependParameters θH θ) (prependRouted route (reportWireContacts wires))
        (queueHead s (scheduledAndStart s.time read wires.length)) v),
      CompleteThrough e T ∧ (send.ContactsTransversal → e.ContactsTransversal) ∧
      Reports e 0 (counterWindow read) (decide (∀ wire ∈ wires, bits wire = true)) ∧
      (∀ i, e.emissionTimes i.succ = send.emissionTimes i) ∧
      (∀ i, v.x i.succ = u.x i) ∧
      (∀ i, lessonReceipts e.deliveries i.succ = lessonReceipts send.deliveries i) := by
  classical
  let dates := receivedReportDates wires bits
  have count := reports_count wires bits
  have fromWire (d : ℝ) (h : d ∈ dates) : ∃ w ∈ wires, w.due = d := by
    obtain ⟨w, mem, eq⟩ := List.mem_map.mp h
    exact ⟨w, (List.mem_filter.mp mem).1, eq⟩
  have separated : dates.Pairwise (fun a b => a + 8 ≤ b) :=
    List.pairwise_map.mpr (gap.filter _)
  obtain ⟨r⟩ := native_conjunction_counter_exists box s.time read T wires.length dates
    nonempty count.1 before afterRead
    (fun d hd => by obtain ⟨w, hw, rfl⟩ := fromWire d hd; exact future w hw)
    (fun d hd => by obtain ⟨w, hw, rfl⟩ := fromWire d hd; exact beforeRead w hw) separated
  let cell := conjunction_report_contract r rfl
  have issued := report_wire_contacts_inputs send wires bits reports
  obtain ⟨weave⟩ := compose_scheduled_receiver send cell.execution done cell.complete
    rfl [conjunctionProbe read] (reportWireContacts wires) (report_wire_contacts_strict margin)
    (List.Perm.cons _ issued)
  let e : Execution (prependParameters θH θ) (prependRouted route (reportWireContacts wires))
      (queueHead s (scheduledAndStart s.time read wires.length)) _ := weave.execution
  have gateReport : Reports weave.execution 0 (counterWindow read) (decide (dates.length = wires.length)) := by
    unfold Reports ReportWindow.dates
    rw [weave.head_emission_times]
    exact cell.reports
  have bitEq : decide (dates.length = wires.length) = decide (∀ wire ∈ wires, bits wire = true) := by
    exact decide_eq_decide.mpr count.2
  refine ⟨_, e, weave.complete done cell.complete, fun h => weave.contacts_transversal h cell.transverse,
    ?_, weave.tail_emission_times, fun _ => rfl, CausalTraceBalance.tail_receipts weave.trace⟩
  rw [← bitEq]
  exact gateReport

/-- The external initial state of a NOT has the same coordinates in both
cases. The optional trigger is absent from this operational queue. -/
noncomputable def scheduledNotBase (origin clock : ℝ) : Snapshot 1 :=
  (scheduledNotStart origin clock false).requeue (notExternal clock)

/-- A scheduled NAND composes two physical cells. The NOT is driven by the
new AND report and all earlier report dates are preserved. -/
theorem compose_report_nand {n θ θA θN ε route s u T read clock}
    (send : @Execution n θ route s u) (done : CompleteThrough send T)
    (andBox : @PhysicalBox 1 θA ε) (notBox : @PhysicalBox 1 θN ε)
    (wires : List (ReportWire n)) (bits : ReportWire n → Bool)
    (nonempty : 0 < wires.length)
    (reports : ∀ wire ∈ wires, Reports send wire.sender wire.window (bits wire))
    (margin : ∀ wire ∈ wires, wire.window.stop ≤ wire.due)
    (future : ∀ wire ∈ wires, s.time < wire.due)
    (gap : wires.Pairwise (fun x y => x.due + 8 ≤ y.due))
    (beforeRead : ∀ wire ∈ wires, wire.due + 15 / 2 < read)
    (before : s.time < read) (next : read ≤ clock) (horizon : clock + 45 < T) :
    let andRoute := prependRouted route (reportWireContacts wires)
    let route' := prependRouted andRoute (forwardReport 0 (counterWindow read) [notTrigger clock])
    let start := queueHead (queueHead s (scheduledAndStart s.time read wires.length))
      (scheduledNotBase s.time clock)
    ∃ (v : Snapshot (n + 1 + 1)) (e : Execution (prependParameters θN (prependParameters θA θ))
        route' start v),
      CompleteThrough e T ∧
      Reports e 0 (notWindow clock) (!(decide (∀ wire ∈ wires, bits wire = true))) ∧
      (∀ i, e.emissionTimes i.succ.succ = send.emissionTimes i) := by
  classical
  obtain ⟨_, counted, countedDone, _, countedReport, countedDates, _, _⟩ :=
    compose_report_and send done andBox wires bits nonempty reports margin future gap beforeRead
      before (by linarith)
  have date : (queueHead s (scheduledAndStart s.time read wires.length)).time = s.time := rfl
  obtain ⟨_, weave, complete, reported, dates⟩ := compose_report_not counted countedDone notBox 0
    (counterWindow read) _ countedReport (by rw [date]; linarith) horizon (by
      change read + 1 ≤ clock + 1
      linarith)
  exact ⟨_, weave.execution, complete, reported, fun i => (dates i.succ).trans (countedDates i)⟩

end RecursiveLearning.Native
