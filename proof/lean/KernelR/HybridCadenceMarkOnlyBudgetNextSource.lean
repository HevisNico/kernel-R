import KernelR.HybridContactTransversalityFrame
import KernelR.HybridCadenceMarkOnlyJitterNextSource
import KernelR.HybridCadenceFullBudgetReturns

/-! The actual protected MARK return is before3.35, so the same physical
return-prefix construction serves full-budget received gaps of at least3.7.
Only the new factory has the wider timing domain. -/
namespace KernelR.Hybrid

theorem cadence_mark_only_full_budget_next_source_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (H : ℝ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 37 / 250 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 1 / 4)
    (hbown : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hqueue : s.pending = ⟨0,p,H⟩ :: later) (hgap : s.time + 37 / 10 ≤ H)
    (hLater : ∀ d ∈ later, H < d.due) :
    Nonempty (CadenceMarkOnlyJitterNextSource θ s p H later) := by
  let s0 := cadenceMarkJitterLocalState s
  have hf0 : PhysicalInvariant θ s0 := ⟨hf.region,hf.gain_cap,hf.recovery_cap,hf.reserve⟩
  obtain ⟨m⟩ := cadence_mark_only_response_exists (route := fun _ _ => []) hb s0 p hf0 hv
    hm hq hbown ha hr ho (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let returnPrefix := m.markPrefix.execution.append (m.auxiliary.execution.append m.returnSpan)
  have hReconstruct : m.execution = returnPrefix.append m.returnRest := by
    simp only [returnPrefix,Execution.append_assoc,m.reconstruct]
  have hPrefix : m.execution.IsPrefix returnPrefix := by rw [hReconstruct]; exact .append_left _ _
  have hePrefix : returnPrefix.ledger.emissions = [] := by
    have h := m.emissions
    rw [hReconstruct,Execution.emissions_append] at h
    exact (List.append_eq_nil_iff.mp h).1
  have hdPrefix : returnPrefix.deliveries = [] := by
    have h := m.deliveries
    rw [hReconstruct,Execution.deliveries_append] at h
    exact (List.append_eq_nil_iff.mp h).1
  have hdReturn : m.returnSpan.deliveries = [] := by
    have h := hdPrefix
    simp only [returnPrefix,Execution.deliveries_append] at h
    exact (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).2).2
  have hNoReturn (q : Port) : NoArrivalAt m.returnSpan 0 q := by simp [NoArrivalAt,hdReturn]
  have hAuxReturn (q : Port) : m.returnState.aux 0 q = .ready ∧ RestBand (m.returnState.x 0 (.m q)) :=
    (m.returnSpan.aux_no_input_rest_band 0 q (m.auxiliary.auxiliary 0 q) (m.auxiliary.rest q)
      (m.auxiliary.raw_none 0 q) (hNoReturn q)).1
  have hRawReturn : ∀ j q, m.returnState.raw j q = none := by
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (m.returnSpan.raw_absent_of_no_arrival 0 q (m.auxiliary.raw_none 0 q) (hNoReturn q)).1
  have hReadyReturn : ∀ j, ReadyCoordinates m.returnState j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    refine ⟨m.returnReady,?_,hAuxReturn⟩
    rw [m.returnCharge]
    constructor <;> norm_num
  have hGainReturn : ∀ j q, m.returnState.x j (.z q) = s.x j (.z q) :=
    fun j q => hPrefix.gain_eq_of_final hb j q (m.gains j q)
  have hRecReturn : m.returnState.x 0 .b = s.x 0 .b + 1 / 10 := by
    have hEnd : m.final.x 0 .b = m.auxiliary.final.x 0 .b :=
      m.recovery_gain.trans ((m.auxiliary.recovery 0).trans m.markPrefix.recovery_gain).symm
    have hP : (m.returnSpan.append m.returnRest).IsPrefix m.returnSpan := .append_left _ _
    exact (hP.recovery_eq_of_final hb 0 hEnd).trans
      ((m.auxiliary.recovery 0).trans m.markPrefix.recovery_gain)
  have hEmpty : m.returnState.pending = [] := returnPrefix.pending_eq_of_no_events hePrefix hdPrefix
  have hEnd : m.returnState.time < H :=
    (m.return_before_full_budget_gap hbown.1).trans_le (by
      change s.time + 67 / 20 ≤ H
      linarith [hgap])
  let flow : Flow θ m.returnState (quietAt m.returnState H) :=
    quietFlow m.returnState hEnd (fun j => (hReadyReturn j).ready)
      (fun j q => ((hReadyReturn j).auxiliary q).1) hRawReturn
      (fun j => by linarith [(hReadyReturn j).charge.2])
      (fun j q => by linarith [((hReadyReturn j).auxiliary q).2.2])
      (by intro d hd; rw [hEmpty] at hd; contradiction)
  let quiet : Execution θ (fun _ _ => []) m.returnState (quietAt m.returnState H) := .cons (.flow flow) (.nil _)
  let offline := returnPrefix.append quiet
  have heOffline : offline.ledger.emissions = [] := by rw [Execution.emissions_append,hePrefix]; rfl
  have hdOffline : offline.deliveries = [] := by rw [Execution.deliveries_append,hdPrefix]; rfl
  let future : List (Delivery 1) := ⟨0,p,H⟩ :: later
  have prefixContacts : returnPrefix.ContactsTransversal := by
    have certificate := m.contacts_transversal
    rw [hReconstruct, Execution.contactsTransversal_append] at certificate
    exact certificate.1
  have offlineContacts : offline.ContactsTransversal := by
    simp [offline, quiet, Execution.ContactsTransversal, prefixContacts]
  obtain ⟨framed0,hFrame,hFrameDel,hFrameContacts⟩ :=
    offline.appendFuture_emptyRoute_transversal future
    (by intro d hd; rcases List.mem_cons.mp hd with he | hd
        · subst d; exact le_rfl
        · exact (hLater d hd).le)
  have hSource : s = appendPending s0 future := by
    simp only [s0,cadenceMarkJitterLocalState,appendPending,future,List.nil_append]
    rw [← hqueue]
  let before := appendPending (quietAt m.returnState H) future
  let framed : Execution θ (fun _ _ => []) s before := framed0.cast_source hSource
  have hFramedLedger : framed.ledger = offline.ledger := (framed0.cast_source_ledger hSource).trans hFrame
  have heFramed : framed.ledger.emissions = [] := (congrArg (fun L : Ledger 1 => L.emissions) hFramedLedger).trans heOffline
  have hdFramed : framed.deliveries = [] := (framed0.cast_source_deliveries hSource).trans (hFrameDel.trans hdOffline)
  have hBeforeQueue : before.pending = [] ++ (⟨0,p,H⟩ : Delivery 1) :: later := by
    change m.returnState.pending ++ future = _
    rw [hEmpty]
  let final : Snapshot 1 := {setRaw before 0 p (some before.time) with pending := later}
  let arrival : Jump (fun _ _ => []) before final := .arrive before ⟨0,p,H⟩ [] later hBeforeQueue rfl (hRawReturn 0 p)
  let trace := framed.append (.cons (.jump arrival) (.nil _))
  have hQuietReady : ∀ j, ReadyCoordinates (quietAt m.returnState H) j := fun j =>
    quietAt_ready_coordinates m.returnState j (hReadyReturn j) hEnd.le
  have hReady : ∀ j, ReadyCoordinates final j := fun j =>
    ⟨(hQuietReady j).ready,(hQuietReady j).charge,(hQuietReady j).auxiliary⟩
  have hCharge : final.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (m.returnState.x 0 .q) m.returnState.time H = _
    rw [m.returnCharge]; simp [relax]
  have hRaw : final.raw 0 p = some H := by simp [final,setRaw,before,appendPending,quietAt]
  have hOther (q : Port) (hq : q ≠ p) : final.raw 0 q = none := by
    change (setRaw before 0 p (some before.time)).raw 0 q = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inr hq)]
    exact hRawReturn 0 q
  have hGains : ∀ j q, final.x j (.z q) = s.x j (.z q) := hGainReturn
  have hRecovery : final.x 0 .b = s.x 0 .b + 1 / 10 := hRecReturn
  have heTrace : trace.ledger.emissions = [] := by
    have hj : arrival.ledger.emissions = [] := rfl
    simp only [trace,Execution.emissions_append,heFramed,Execution.ledger,Move.ledger,hj,
      Ledger.add,Ledger.zero,List.nil_append]
  have hdTrace : trace.deliveries = [⟨0,p,H⟩] := by
    have hj : arrival.deliveries = [⟨0,p,H⟩] := rfl
    simp only [trace,Execution.deliveries_append,hdFramed,Execution.deliveries,Move.deliveries,hj,List.nil_append,List.append_nil]
  have hError (q : Port) : trace.ledger.error 0 q = 0 := by
    have h := trace.gain_balance 0 q
    rw [hGains] at h; linarith
  have hRecoveryDose : trace.ledger.recovery 0 = 1 / 10 := by
    have h := trace.recovery_balance 0
    rw [hRecovery] at h; linarith
  have hMarkOther (q : Port) (hq : q ≠ p) : trace.ledger.mark 0 q = 0 := by
    have hNo : NoArrivalAt trace 0 q := by simp [NoArrivalAt,hdTrace,Ne.symm hq]
    have hAux := trace.aux_ready_without_input_band 0 q (ha q).1 (ha q).2.2 (ho q hq) hNo
    exact trace.mark_zero_aux 0 q .ready (by decide) (trace.allStates_aux_flows 0 q .ready hAux)
  have hMark : trace.ledger.mark 0 p = 1 / 10 := by
    have hsum : (∑ q : Port, trace.ledger.mark 0 q) = trace.ledger.mark 0 p :=
      Finset.sum_eq_single p (fun q _ hq => hMarkOther q hq) (by simp)
    have h := trace.recovery_sum_marks 0
    rw [hRecoveryDose,hsum] at h
    exact h.symm
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := hLater
  have hComplete : CompleteThrough trace H := by
    refine ⟨rfl,?_,hLater⟩
    intro u; apply BeforeGuards.no_jump
    · constructor
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rw [(hReady 0).ready,hCharge]; norm_num
      · intro j q
        rw [((hReady j).auxiliary q).1]
        linarith [((hReady j).auxiliary q).2.2]
    · intro j q origin hraw
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hq : q = p
      · subst q
        have ho : origin = H := Option.some.inj (hraw.symm.trans hRaw)
        rw [ho]
        change H < H + 1
        linarith
      · rw [hOther q hq] at hraw; contradiction
    · exact hFuture
  refine ⟨{
    response := m, returnPrefix := returnPrefix, prefix_state := rfl, prefix_reconstruct := hReconstruct
    return_ready := hReadyReturn, return_raw_none := hRawReturn
    quietFlow := flow, quiet := quiet, quiet_reconstruct := rfl
    offline := offline, offline_reconstruct := rfl, before := before, before_state := rfl
    framed := framed, framed_ledger := hFramedLedger, final := final, final_state := rfl
    arrival := arrival, execution := trace, reconstruct := rfl, date := rfl, values := rfl
    contacts_transversal := by
      simp only [trace, Execution.contactsTransversal_append]
      refine ⟨?_, ?_⟩
      · exact (framed0.contactsTransversal_cast_source hSource).mpr
          (hFrameContacts.mpr offlineContacts)
      · simp [arrival, Execution.ContactsTransversal, Jump.ContactTransversal]
    ready := hReady, charge := hCharge, raw_active := hRaw, raw_other := hOther, pending := rfl
    gains := hGains, recovery_gain := hRecovery, recovery_band := ?_
    emissions := heTrace, deliveries := hdTrace, error_zero := hError, mark_target := hMark
    mark_other := hMarkOther, recovery_dose := hRecoveryDose
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv, complete := hComplete
  }⟩
  rw [hRecovery]
  constructor <;> linarith [hbown.1,hbown.2]

end KernelR.Hybrid
