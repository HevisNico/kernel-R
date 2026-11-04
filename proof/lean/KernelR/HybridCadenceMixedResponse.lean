import KernelR.HybridCadenceMixedReopen
import KernelR.HybridReadySilentErrorStart
import KernelR.HybridCadenceMixedPulse
import KernelR.HybridErrorCompletion
import KernelR.HybridCadenceSilent
import KernelR.HybridCadenceStrongPulse

/-! Construct the mixed cadence input from its actual SLOW charge. The
protected MARK, logarithmic reopening, remaining RAW, ERROR, and quiet tail
are actual paths; no execution reaching the final section is supplied. -/
namespace KernelR.Hybrid
open Set

structure CadenceMixedResponse (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port) where
  markPrefix : CadenceMixedPrefix θ (fun _ _ => []) s p
  reopened : CadenceMixedReopen markPrefix
  errorStart : ReadySilentErrorStart θ (fun _ _ => []) reopened.final p s.time markPrefix.final.time
  errorEnd : ErrorCompletion θ (fun _ _ => []) errorStart.final 0 p
  final : Snapshot 1
  wait : Execution θ (fun _ _ => []) errorEnd.final final
  execution : Execution θ (fun _ _ => []) s final
  contacts_transversal : execution.ContactsTransversal
  reconstruct : execution = markPrefix.execution.append (reopened.execution.append
    (errorStart.execution.append (errorEnd.execution.append wait)))
  date : final.time = s.time + 4
  pulse : CadenceMixedPulse execution 0 p
  coordinates : CadenceReadyCoordinates final 0 (8 / 25)
  charge_lower : 1 / 10 ≤ final.x 0 .q
  raw_none : ∀ q, final.raw 0 q = none
  gain_target : final.x 0 (.z p) = s.x 0 (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → final.x 0 (.z q) = s.x 0 (.z q)
  recovery_gain : final.x 0 .b = s.x 0 .b + 1 / 10
  recovery_band : 37999 / 100000 ≤ final.x 0 .b ∧ final.x 0 .b ≤ 38001 / 100000
  pending : final.pending = s.pending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

theorem cadence_mixed_response_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 61 / 500 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 7 / 50)
    (hB : 27999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 28001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    Nonempty (CadenceMixedResponse θ s p) := by
  obtain ⟨m⟩ := cadence_mixed_prefix_exists (route := fun _ _ => []) hb s p hf hv hm hq hB ha hr ho hp
  obtain ⟨r⟩ := cadence_mixed_reopen_exists m hb hq hB hp
  have hg := cadence_three_dose_gain_bounds hz
  have hhalf : Real.exp (-a * (1 / 2 : ℝ)) = 1 / 2 := by
    have hsq : Real.exp (-a * (1 / 2 : ℝ)) ^ 2 = 1 / 4 := by
      rw [pow_two,← Real.exp_add,show -a * (1 / 2 : ℝ) + -a * (1 / 2) = -a by ring,exp_neg_a]
    nlinarith [Real.exp_pos (-a * (1 / 2 : ℝ))]
  have hScale : rawInputScale (some s.time) r.final.time ≤ 1 / 2 := by
    change Real.exp (-a * (r.final.time - s.time)) ≤ _
    rw [← hhalf]
    apply Real.exp_le_exp.mpr
    nlinarith [r.window.1,a_coarse_bounds.1]
  have hGainR : Real.exp (r.final.x 0 (.z p)) ≤ 19 / 10 := by
    rw [r.gains,m.gain_preserved]
    exact hg.2
  have hAmp : Real.exp (r.final.x 0 (.z p)) * rawInputScale (some s.time) r.final.time ≤ 7 / 6 := by
    have h := mul_le_mul hGainR hScale (rawInputScale_nonnegative _ _)
      (by norm_num : (0 : ℝ) ≤ 19 / 10)
    linarith
  have hmargin : ∀ time, r.final.time ≤ time → readyPulse (1 / 10)
      (Real.exp (r.final.x 0 (.z p)) * rawInputScale (some s.time) r.final.time) r.final.time time ≤ 24 / 25 := by
    intro time ht
    exact readyPulse_weak_input_error_margin (by norm_num) hAmp ht
  obtain ⟨start⟩ := ready_silent_error_start_exists (route := fun _ _ => []) hb r.final p s.time m.final.time
    r.physical r.raw_valid r.charge r.main_ready r.aux_silent r.sensor_clock r.auxiliary_other
    r.raw_active r.raw_other r.window ⟨m.error_lower,m.error_upper⟩
    (by intro time ht; rw [r.charge]; exact hmargin time ht)
    (by intro d hd; rw [r.pending,m.pending] at hd; exact hp d hd)
  have hDuration : errorTailDuration θ start.final 0 p = Real.log 4 / (θ 0).le p := by
    simp only [errorTailDuration,start.sensor_charge]
    norm_num
  have hEndDate : start.final.time + errorTailDuration θ start.final 0 p < s.time + 419 / 300 := by
    rw [start.date,hDuration]
    linarith [m.sensor_budget]
  have hEndRaw : s.time + 1 < start.final.time + errorTailDuration θ start.final 0 p := by
    rw [start.date,hDuration]
    linarith [(hb.aux_durations_lower 0 p).2.1,(hb.aux_durations_lower 0 p).2.2,m.early]
  have hGainStart : start.final.x 0 (.z p) = s.x 0 (.z p) := by
    rw [start.gains,r.gains,m.gain_preserved]
  have hHeadroom : start.final.x 0 (.z p) + 8 * (start.final.x 0 (.m p) - 1 / 40) <
      Real.log ((θ 0).cap p) := by
    rw [hGainStart,start.sensor_charge]
    have hh := hb.low_gain_headroom 0 p
    linarith [hz.2]
  have hOtherAux : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → start.final.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (start.auxiliary_other q (by simpa using h)).1
  have hOtherRaw : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → start.final.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact start.raw_other q (by simpa using h)
  have hOtherBelow : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → start.final.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    linarith [(start.auxiliary_other q (by simpa using h)).2.2]
  have hQueue : start.final.pending = s.pending := start.pending.trans (r.pending.trans m.pending)
  have hFuture : ∀ d ∈ start.final.pending, start.final.time + errorTailDuration θ start.final 0 p < d.due := by
    intro d hd
    rw [hQueue] at hd
    linarith [hp d hd]
  have hError : Nonempty (ErrorCompletion θ (fun _ _ => []) start.final 0 p) := by
    by_cases hraw : start.final.time < s.time + 1
    · apply error_completion_with_raw_tail hb start.final 0 p start.physical start.main_ready
        start.aux_error hOtherAux s.time ?_ hOtherRaw (by rw [start.sensor_charge]; norm_num)
        (by rw [start.sensor_charge]) hHeadroom ?_ hraw hEndRaw start.charge_margin
        start.main_below hOtherBelow hFuture
      · rw [start.raw_option,ite_eq_left hraw]
      · rw [start.date]
        exact m.error_lower.le
    · apply error_completion_without_raw hb start.final 0 p start.physical start.main_ready
        start.aux_error hOtherAux ?_ (by rw [start.sensor_charge]; norm_num)
        (by rw [start.sensor_charge]) hHeadroom start.main_below hOtherBelow hFuture
      intro j q
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hq : q = p
      · subst q
        rw [start.raw_option,ite_eq_right hraw]
      · exact start.raw_other q hq
  obtain ⟨err⟩ := hError
  have hWait : err.final.time < s.time + 4 := by rw [err.date]; linarith
  have hPending : err.final.pending = s.pending := err.pending.trans hQueue
  let flow := quietFlow (θ := θ) err.final hWait err.main_ready err.aux_ready err.raw_none
    err.main_below err.aux_below
    (by intro d hd; rw [hPending] at hd; exact hp d hd)
  let wait : Execution θ (fun _ _ => []) err.final (quietAt err.final (s.time + 4)) :=
    .cons (.flow flow) (.nil _)
  let execution := m.execution.append (r.execution.append (start.execution.append (err.execution.append wait)))
  have hDel : execution.deliveries = [] := by
    simp only [execution,Execution.deliveries_append,m.deliveries,r.deliveries,start.deliveries,err.deliveries]
    rfl
  obtain ⟨pulse⟩ := execution.cadence_mixed_pulse hb hf hv 0 p hm hq hB ha hz hr ho
    (by intro q; simp [NoArrivalAt,hDel]) (by change s.time + 19 / 5 ≤ s.time + 4; linarith)
  refine ⟨{
    markPrefix := m, reopened := r, errorStart := start, errorEnd := err
    contacts_transversal := by
      simp [execution, wait, Execution.ContactsTransversal,
        m.contacts_transversal, r.contacts_transversal, start.contacts_transversal, err.contacts_transversal]
    final := quietAt err.final (s.time + 4), wait := wait, execution := execution, reconstruct := rfl
    date := rfl, pulse := pulse
    coordinates := ⟨pulse.ready,⟨by linarith [pulse.charge.1],pulse.charge_cadence⟩,pulse.auxiliary⟩
    charge_lower := pulse.charge.1, raw_none := pulse.raw_finished, gain_target := pulse.gain_target
    gain_other := pulse.gain_other, recovery_gain := pulse.recovery_gain
    recovery_band := by rw [pulse.recovery_gain]; constructor <;> linarith [hB.1,hB.2]
    pending := hPending, emissions := ?_, deliveries := hDel
    physical := execution.physical_invariant hb hf, raw_valid := execution.raw_valid hv
  }⟩
  simp only [execution,Execution.emissions_append,m.emissions,r.emissions,start.emissions,err.emissions]
  rfl

end KernelR.Hybrid
