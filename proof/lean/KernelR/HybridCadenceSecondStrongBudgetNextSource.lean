import KernelR.HybridContactTransversalityFrame
import KernelR.HybridCadenceSecondStrongJitterNextSource
import KernelR.HybridCadenceSecondStrongBudgetSpan

/-! The full3/20-budget second strong response reaches its actual next
source with the wider mixed charge band[.118,.142]. Its own exact-rest
latency, physical energy and full ledger are retained through framing. -/
namespace KernelR.Hybrid

structure CadenceSecondStrongBudgetNextSource (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (H : ℝ) (later : List (Delivery 1)) where
  fire : FirstLearnedFire θ (fun _ _ => []) (cadenceJitterLocalState s) 0 p
  fast : PortFastCompletion θ (fun _ _ => []) fire.final p
  rest_latency : fire.latency = restLatency (Real.exp (s.x 0 (.z p)))
  fire_window : s.time + 13 / 20 < fire.final.time ∧ fire.final.time < s.time + 33 / 50
  span : CadenceSecondStrongBudgetSpan fast H
  offline : Execution θ (fun _ _ => []) (cadenceJitterLocalState s) span.final
  offline_reconstruct : offline = (fire.execution.append fast.execution).append span.execution
  before : Snapshot 1
  before_state : before = appendPending span.final (⟨0,p,H⟩ :: later)
  framed : Execution θ (fun _ _ => []) s before
  framed_ledger : framed.ledger = offline.ledger
  final : Snapshot 1
  final_state : final = {setRaw before 0 p (some before.time) with pending := later}
  arrival : Jump (fun _ _ => []) before final
  execution : Execution θ (fun _ _ => []) s final
  contacts_transversal : execution.ContactsTransversal
  reconstruct : execution = framed.append (.cons (.jump arrival) (.nil _))
  date : final.time = H
  values : final.x = span.final.x
  main_slow : final.main 0 = .slow
  auxiliary : ∀ j q, final.aux j q = .ready
  rest : ∀ q, RestBand (final.x 0 (.m q))
  charge : 59 / 500 ≤ final.x 0 .q ∧ final.x 0 .q ≤ 71 / 500
  energy : final.x 0 .energy = span.final.x 0 .energy
  raw_active : final.raw 0 p = some H
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = later
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = [(0,fire.final.time)]
  deliveries : execution.deliveries = [⟨0,p,H⟩]
  error_zero : ∀ q, execution.ledger.error 0 q = 0
  mark_zero : ∀ q, execution.ledger.mark 0 q = 0
  recovery_zero : execution.ledger.recovery 0 = 0
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution H

theorem cadence_second_strong_full_budget_next_source_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (H : ℝ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (3 / 10)) (hq : s.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hB : 27999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 28001 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hqueue : s.pending = ⟨0,p,H⟩ :: later)
    (hgap : s.time + 37 / 10 ≤ H ∧ H ≤ s.time + 43 / 10)
    (hLater : ∀ d ∈ later, H < d.due) :
    Nonempty (CadenceSecondStrongBudgetNextSource θ s p H later) := by
  let s0 := cadenceJitterLocalState s
  have hf0 : PhysicalInvariant θ s0 := ⟨hf.region,hf.gain_cap,hf.recovery_cap,hf.reserve⟩
  have hv0 : RawValid s0 := hv
  have hs0 : CadenceReadyCoordinates s0 0 (3 / 10) := ⟨hs.ready,hs.charge,hs.auxiliary⟩
  have hp0 : ∀ d ∈ s0.pending, s0.time + 4 ≤ d.due := by
    intro d hd
    change d ∈ ([] : List (Delivery 1)) at hd
    contradiction
  have hg := cadence_three_dose_gain_bounds hz
  obtain ⟨fire⟩ := cadence_first_strong_fire_exists hb s0 p hf0 hv0 hs0 hg hr ho hp0
  obtain ⟨fast⟩ := fire.cadence_residual_fast_completion_exists hb hs0 hg.2 ho hp0
  have hRoot : readyPulse (1 / 10) (Real.exp (s.x 0 (.z p))) 0 fire.latency = 1 := by
    have h := fire.response_root
    change readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time (s.time + fire.latency) = 1 at h
    simpa only [readyPulse,hq,add_sub_cancel_left,sub_zero] using h
  have hRest := restLatency_unique ⟨hg.1,by linarith [hg.2]⟩
    ⟨by linarith [fire.early],fire.deadline.le⟩ hRoot
  have hFireWindow : s.time + 13 / 20 < fire.final.time ∧ fire.final.time < s.time + 33 / 50 := by
    change s.time + 13 / 20 < s.time + fire.latency ∧ s.time + fire.latency < s.time + 33 / 50
    rw [hRest]
    constructor <;> linarith [restLatency_three_doses_bounds hz.1 hz.2]
  obtain ⟨span⟩ := fire.cadence_second_strong_full_budget_span_exists hb fast H hgap hq hz hB
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let offline := (fire.execution.append fast.execution).append span.execution
  have heOffline : offline.ledger.emissions = [(0,fire.final.time)] := by
    simp only [offline,Execution.emissions_append,fire.emissions,fast.emissions,span.emissions,List.append_nil]
    rfl
  have hdOffline : offline.deliveries = [] := by
    simp only [offline,Execution.deliveries_append,fire.deliveries,fast.deliveries,span.deliveries,List.append_nil]
  have hEmpty : span.final.pending = [] := by
    rw [span.pending,fast.pending,fire.pending,List.append_nil]
    rfl
  let future : List (Delivery 1) := ⟨0,p,H⟩ :: later
  have hOfflineTransversal : offline.ContactsTransversal := by
    simp [offline, fire.contacts_transversal, fast.contacts_transversal, span.contacts_transversal]
  obtain ⟨framed0,hFrame,hFrameDel,hFrameTransversal⟩ := offline.appendFuture_emptyRoute_transversal future
    (by intro d hd; rw [span.date]; rcases List.mem_cons.mp hd with he | hd
        · subst d; exact le_rfl
        · exact (hLater d hd).le)
  have hSource : s = appendPending s0 future := by
    simp only [s0,cadenceJitterLocalState,appendPending,future,List.nil_append]
    rw [←hqueue]
  let before := appendPending span.final future
  let framed : Execution θ (fun _ _ => []) s before := framed0.cast_source hSource
  have hFramedTransversal : framed.ContactsTransversal := by
    simpa only [framed, Execution.contactsTransversal_cast_source] using
      hFrameTransversal.mpr hOfflineTransversal
  have hFramedLedger : framed.ledger = offline.ledger := (framed0.cast_source_ledger hSource).trans hFrame
  have heFramed : framed.ledger.emissions = [(0,fire.final.time)] :=
    (congrArg (fun L : Ledger 1 => L.emissions) hFramedLedger).trans heOffline
  have hdFramed : framed.deliveries = [] := (framed0.cast_source_deliveries hSource).trans (hFrameDel.trans hdOffline)
  have hBeforeQueue : before.pending = [] ++ (⟨0,p,H⟩ : Delivery 1) :: later := by
    change span.final.pending ++ future = _
    rw [hEmpty]
  let final : Snapshot 1 := {setRaw before 0 p (some before.time) with pending := later}
  let arrival : Jump (fun _ _ => []) before final :=
    .arrive before ⟨0,p,H⟩ [] later hBeforeQueue span.date.symm (span.raw_none 0 p)
  let trace := framed.append (.cons (.jump arrival) (.nil _))
  have hRaw : final.raw 0 p = some H := by simp [final,setRaw,before,appendPending,span.date]
  have hOther (q : Port) (hq : q ≠ p) : final.raw 0 q = none := by
    change (setRaw before 0 p (some before.time)).raw 0 q = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inr hq)]
    exact span.raw_none 0 q
  have hGains : ∀ j q, final.x j (.z q) = s.x j (.z q) := fun j q =>
    (span.gains j q).trans ((fast.gains j q).trans (fire.gain_preserved j q))
  have hRecovery : ∀ j, final.x j .b = s.x j .b := fun j =>
    (span.recovery j).trans ((fast.recovery j).trans (fire.recovery_preserved j))
  have heTrace : trace.ledger.emissions = [(0,fire.final.time)] := by
    have hj : arrival.ledger.emissions = [] := rfl
    simp only [trace,Execution.emissions_append,heFramed,Execution.ledger,Move.ledger,hj,
      Ledger.add,Ledger.zero,List.append_nil]
  have hdTrace : trace.deliveries = [⟨0,p,H⟩] := by
    have hj : arrival.deliveries = [⟨0,p,H⟩] := rfl
    simp only [trace,Execution.deliveries_append,hdFramed,Execution.deliveries,Move.deliveries,hj,
      List.nil_append,List.append_nil]
  have hError (q : Port) : trace.ledger.error 0 q = 0 := by
    have h := trace.gain_balance 0 q
    rw [hGains] at h; linarith
  have hRecoveryZero : trace.ledger.recovery 0 = 0 := by
    have h := trace.recovery_balance 0
    rw [hRecovery] at h; linarith
  have hMarkOther (q : Port) (hq : q ≠ p) : trace.ledger.mark 0 q = 0 := by
    have hNo : NoArrivalAt trace 0 q := by simp [NoArrivalAt,hdTrace,Ne.symm hq]
    have hAux := trace.aux_ready_without_input_band 0 q (hs.auxiliary q).1 (hs.auxiliary q).2.2 (ho q hq) hNo
    exact trace.mark_zero_aux 0 q .ready (by decide) (trace.allStates_aux_flows 0 q .ready hAux)
  have hMark (q : Port) : trace.ledger.mark 0 q = 0 := by
    by_cases hq : q = p
    · subst q
      have hsum : (∑ q : Port, trace.ledger.mark 0 q) = trace.ledger.mark 0 p :=
        Finset.sum_eq_single p (fun q _ hq => hMarkOther q hq) (by simp)
      have h := trace.recovery_sum_marks 0
      rw [hRecoveryZero,hsum] at h
      exact h.symm
    · exact hMarkOther q hq
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ later at hd
    change span.final.time < d.due
    rw [span.date]
    exact hLater d hd
  have hComplete : CompleteThrough trace H := by
    refine ⟨span.date,?_,hLater⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change (match span.final.main 0 with
          | .ready => span.final.x 0 .q < 1
          | .fast => 1 / 4 < span.final.x 0 .q
          | .slow => 1 / 10 < span.final.x 0 .q)
        rw [span.main_slow]
        linarith [span.charge.1]
      · intro j q
        change (match span.final.aux j q with
          | .ready => span.final.x j (.m q) < 1
          | .mark => 4 / 5 < span.final.x j (.m q)
          | .silent => 1 / 10 < span.final.x j (.m q)
          | .error => 1 / 40 < span.final.x j (.m q))
        rw [span.auxiliary]
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        linarith [(span.rest q).2]
    · intro j q origin hraw
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hq : q = p
      · subst q
        have he : origin = H := Option.some.inj (hraw.symm.trans hRaw)
        rw [he]
        change span.final.time < H + 1
        rw [span.date]; linarith
      · rw [hOther q hq] at hraw; contradiction
    · exact hFuture
  exact ⟨{
    fire := fire, fast := fast, rest_latency := hRest, fire_window := hFireWindow, span := span, offline := offline, offline_reconstruct := rfl
    before := before, before_state := rfl, framed := framed, framed_ledger := hFramedLedger
    final := final, final_state := rfl, arrival := arrival, execution := trace, reconstruct := rfl
    contacts_transversal := by
      simp [trace, arrival, Execution.ContactsTransversal, Jump.ContactTransversal, hFramedTransversal]
    date := span.date, values := rfl, main_slow := span.main_slow, auxiliary := span.auxiliary
    rest := span.rest, charge := span.charge, energy := rfl, raw_active := hRaw, raw_other := hOther
    pending := rfl, gains := hGains, recovery := hRecovery, emissions := heTrace, deliveries := hdTrace
    error_zero := hError, mark_zero := hMark, recovery_zero := hRecoveryZero
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv, complete := hComplete
  }⟩

namespace CadenceSecondStrongBudgetNextSource
variable {θ s p H later} (r : CadenceSecondStrongBudgetNextSource θ s p H later)

theorem emission_count : (r.execution.emissionTimes 0).length = 1 := by
  simp [Execution.emissionTimes,r.emissions]

end CadenceSecondStrongBudgetNextSource
end KernelR.Hybrid
