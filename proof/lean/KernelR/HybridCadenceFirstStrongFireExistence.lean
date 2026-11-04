import KernelR.HybridCadenceResidualRootBounds
import KernelR.HybridCadenceSilent
import KernelR.HybridResponseMarginInput
import KernelR.HybridPortFastCompletion

/-! Construct the first cadence FIRE from its true carried READY charge.
Only the first FAST phase is completed; the source due four units later is
retained, since it may meet the genuine subsequent SLOW path. -/
namespace KernelR.Hybrid
open Set

theorem cadence_first_strong_fire_exists {θ ε}
    (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (3 / 10))
    (hg : 9 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 19 / 10)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    Nonempty (FirstLearnedFire θ (fun _ _ => []) s 0 p) := by
  have hm : ∀ j, s.main j = .ready := by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hs.ready
  have ha : ∀ j q, s.aux j q = .ready := by
    intro j q; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact (hs.auxiliary q).1
  have hq0 : ∀ j, s.x j .q < 1 := by
    intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [hs.charge.2]
  have hx0 : ∀ j q, s.x j (.m q) < 1 := by
    intro j q; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hs.auxiliary q).2.2]
  have hother : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.raw j q = none := by
    intro j q h; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact ho q (by simpa using h)
  have hmain : ∀ time, s.time ≤ time → time ≤ s.time + 1 / 10 →
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time time < 1 := by
    intro time hl hu
    exact (readyPulse_cadence_residual_four_tenths_margin hs.charge.2 hg.2 hl (by linarith)).2
  obtain ⟨f⟩ := first_input_mark_of_response_margin_until_exists s hb 0 p hm ha hr hother hq0 hx0
    hmain (hs.auxiliary p).2 (fun d hd => by linarith [hp d hd])
  obtain ⟨g⟩ := f.first_silent_of_response_margin_until_exists hb hmain
    (fun d hd => by linarith [hp d hd])
  obtain ⟨latency,hearly,hdeadline,hroot,hprior,hslope⟩ := readyPulse_cadence_residual_first_crossing_transversal hs.charge hg
  let T := s.time + latency
  have hT : g.final.time < T := by rw [g.date]; dsimp [T]; linarith [g.deadline]
  have hstart : s.time ≤ g.final.time := by
    have h := g.flow.positive
    change s.time + f.latency < g.final.time at h
    linarith [f.early]
  have hrawSupport : ∀ origin, some s.time = some origin → origin ≤ g.final.time ∧ T ≤ origin + 1 := by
    intro origin he
    have h := (Option.some.inj he).symm
    subst origin
    exact ⟨hstart,by dsimp [T]; linarith⟩
  have hq : ∀ time ∈ Ico g.final.time T, readyPulse (g.final.x 0 .q)
      (Real.exp (g.final.x 0 (.z p)) * rawInputScale (some s.time) g.final.time) g.final.time time < 1 := by
    intro time ht
    rw [g.response_restart]
    exact hprior time ⟨hstart.trans ht.1,ht.2⟩
  have hschedule := protected_decay_schedule (initial := (4 / 5 : ℝ)) (floor := (1 / 10 : ℝ))
    (by norm_num) (by norm_num) (hb.rates_positive 0 p).2.1
  have hratio : Real.log ((4 / 5 : ℝ) / (1 / 10)) / (θ 0).ls p = Real.log 8 / (θ 0).ls p := by norm_num
  have hguard : ∀ time ∈ Icc g.final.time T,
      1 / 10 < (4 / 5 : ℝ) * Real.exp (-(θ 0).ls p * (time - g.final.time)) := by
    intro time ht
    apply hschedule.2.2 (time - g.final.time) (by linarith [ht.1])
    rw [hratio]
    have he := (g.errorDate_bounds hb).1
    change s.time + 99 / 100 < g.final.time + Real.log 8 / (θ 0).ls p at he
    dsimp [T] at ht
    linarith [ht.2]
  have hx : ∀ time ∈ Ico g.final.time T, (if AuxMode.silent = .mark then (4 / 5 : ℝ) else 1 / 10) <
      g.final.x 0 (.m p) * Real.exp (-protectedReadyRate (θ 0) p .silent * (time - g.final.time)) := by
    intro time ht
    simpa only [reduceCtorEq,ite_false,g.sensor_charge,protectedReadyRate] using hguard time ⟨ht.1,ht.2.le⟩
  let flow := readyProtectedFlow g.final 0 p .silent (some s.time) hT (Or.inr rfl)
    g.main_ready g.aux_silent g.aux_other g.raw_active g.raw_other hrawSupport g.main_below g.aux_below hq hx
    (fun d hd => by change d ∈ s.pending at hd; dsimp [T]; linarith [hp d hd])
  have hthreshold : (g.learnedFireBefore latency).x 0 .q = 1 := by
    simp only [FirstInputSilent.learnedFireBefore,readyProtectedEnd,readyProtectedValues,protectedRawAmplitude,ite_true]
    rw [g.response_restart]
    exact hroot
  let endBefore := g.learnedFireBefore latency
  let endFinal := g.learnedFireFinal (fun _ _ => []) latency
  let execution : Execution θ (fun _ _ => []) s endFinal := (g.execution (fun _ _ => [])).append
    (.cons (.flow flow) (.cons (.jump (.fire endBefore 0 (g.main_ready 0) hthreshold)) (.nil _)))
  refine ⟨{
    firstMark := f, firstSilent := g, latency := latency
    early := by linarith, deadline := hdeadline, response_root := hroot, scalar_slope := hslope
    flow := flow, threshold := hthreshold, sensor_above_floor := ?_
    physical := execution.physical_invariant hb hf, raw_valid := execution.raw_valid hv
  }⟩
  simpa [FirstInputSilent.learnedFireBefore,readyProtectedEnd,readyProtectedValues,protectedReadyRate,g.sensor_charge]
    using hguard T ⟨hT.le,le_rfl⟩

namespace FirstLearnedFire
variable {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
  (fire : FirstLearnedFire θ (fun _ _ => []) s 0 p)

theorem cadence_residual_window
    (hs : CadenceReadyCoordinates s 0 (3 / 10)) (hg : Real.exp (s.x 0 (.z p)) ≤ 19 / 10) :
    s.time + 2 / 5 < fire.final.time ∧ fire.final.time < s.time + 9 / 10 := by
  refine ⟨?_,?_⟩
  · rw [fire.date]
    exact readyPulse_cadence_residual_root_after_four_tenths hs.charge.2 hg
      (by linarith [fire.early]) fire.response_root
  · rw [fire.date]; linarith [fire.deadline]

theorem cadence_residual_other_rest (hs : CadenceReadyCoordinates s 0 (3 / 10))
    (ho : ∀ q, q ≠ p → s.raw 0 q = none) (q : Port) (hq : q ≠ p) :
    RestBand (fire.final.x 0 (.m q)) :=
  (fire.execution.aux_no_input_rest_band 0 q (hs.auxiliary q).1 (hs.auxiliary q).2 (ho q hq)
    (by simp [NoArrivalAt,fire.deliveries])).1.2

theorem cadence_residual_fast_completion_exists {ε} (hb : PhysicalBox θ ε)
    (hs : CadenceReadyCoordinates s 0 (3 / 10)) (hg : Real.exp (s.x 0 (.z p)) ≤ 19 / 10)
    (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    Nonempty (PortFastCompletion θ (fun _ _ => []) fire.final p) := by
  let P := fire.firstSilent.final.time
  let Te := fire.firstSilent.errorDate
  let Tr := s.time + fire.firstMark.latency + auxCycleDuration (θ 0) p
  have hw := fire.cadence_residual_window hs hg
  have hPstart : s.time ≤ P := by
    change s.time ≤ s.time + fire.firstMark.latency + Real.log (5 / 4) / (θ 0).lm p
    linarith [fire.firstMark.early,(hb.aux_durations_positive 0 p).1]
  have hPupper : P < s.time + 1 / 20 := fire.firstSilent.deadline
  have hP : P < fire.final.time := by linarith [hw.1]
  have hTe := fire.firstSilent.errorDate_bounds hb
  have hcycle := hb.first_cycle_schedule 0 p ⟨fire.firstMark.early,fire.firstMark.deadline⟩
  have hTr : s.time + 1 < Tr ∧ Tr < s.time + 419 / 300 := by
    constructor <;> dsimp [Tr] <;> linarith [hcycle.2.2.2.2.1,hcycle.2.2.2.2.2]
  have hTrEq : Tr = Te + Real.log 4 / (θ 0).le p := by
    have hPdate : P = fire.firstMark.silentDate := fire.firstSilent.date
    change Tr = (P + Real.log 8 / (θ 0).ls p) + Real.log 4 / (θ 0).le p
    rw [hPdate]
    dsimp [Tr,FirstInputMark.silentDate,auxCycleDuration]
    ring
  refine port_fast_completion_exists hb fire.final p s.time P Te Tr fire.physical fire.raw_valid
    fire.main_fast fire.aux_silent fire.aux_other fire.raw_active fire.raw_other
    (fire.cadence_residual_other_rest hs ho) fire.charge ?_ ⟨by linarith [hw.1],by linarith [hw.2]⟩
    hP.le rfl hTrEq (by linarith [hw.2,hTe.1]) hTr.1 (by linarith [hw.1,hTr.2]) ?_
  · simp only [FirstLearnedFire.final,FirstInputSilent.learnedFireFinal,
      FirstInputSilent.learnedFireBefore,setMain,readyProtectedEnd,readyProtectedValues,
      and_self,ite_true,fire.firstSilent.sensor_charge]
    rfl
  · intro d hd
    rw [fire.pending,List.append_nil] at hd
    linarith [hp d hd,hw.2]

theorem cadence_residual_complete
    (hs : CadenceReadyCoordinates s 0 (3 / 10))
    (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    CompleteThrough fire.execution fire.final.time := by
  have hFuture : ∀ d ∈ fire.final.pending, fire.final.time < d.due := by
    intro d hd
    rw [fire.pending,List.append_nil] at hd
    rw [fire.date]
    linarith [hp d hd,fire.deadline]
  refine ⟨rfl,?_,hFuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [fire.main_fast,fire.charge]
      norm_num
    · intro j q
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hq : q = p
      · subst q
        rw [fire.aux_silent]
        exact fire.sensor_above
      · rw [fire.aux_other 0 q (Or.inr hq)]
        linarith [(fire.cadence_residual_other_rest hs ho q hq).2]
  · intro j q origin hraw
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    by_cases hq : q = p
    · subst q
      have he : origin = s.time := Option.some.inj (hraw.symm.trans fire.raw_active)
      rw [he,fire.date]
      linarith [fire.deadline]
    · rw [fire.raw_other 0 q (Or.inr hq)] at hraw
      contradiction
  · exact hFuture

theorem cadence_residual_error_zero (q : Port) : fire.execution.ledger.error 0 q = 0 := by
  have h := fire.execution.gain_balance 0 q
  rw [fire.gain_preserved] at h
  linarith

theorem cadence_residual_recovery_zero : fire.execution.ledger.recovery 0 = 0 := by
  have h := fire.execution.recovery_balance 0
  rw [fire.recovery_preserved] at h
  linarith

theorem cadence_residual_mark_zero (hs : CadenceReadyCoordinates s 0 (3 / 10))
    (ho : ∀ q, q ≠ p → s.raw 0 q = none) (q : Port) : fire.execution.ledger.mark 0 q = 0 := by
  have hother : ∀ r, r ≠ p → fire.execution.ledger.mark 0 r = 0 := by
    intro r hr
    have hquiet := fire.execution.aux_ready_without_input_band 0 r (hs.auxiliary r).1
      (hs.auxiliary r).2.2 (ho r hr) (by simp [NoArrivalAt,fire.deliveries])
    exact fire.execution.mark_zero_aux 0 r .ready (by decide)
      (fire.execution.allStates_aux_flows 0 r .ready hquiet)
  have hsum : (∑ r : Port, fire.execution.ledger.mark 0 r) = fire.execution.ledger.mark 0 p :=
    Finset.sum_eq_single p (fun r _ hr => hother r hr) (by simp)
  by_cases hq : q = p
  · subst q
    have h := fire.execution.recovery_sum_marks 0
    rw [fire.cadence_residual_recovery_zero,hsum] at h
    exact h.symm
  · exact hother q hq

theorem cadence_residual_emission_count : (fire.execution.emissionTimes 0).length = 1 := by
  simp [Execution.emissionTimes,fire.emissions]

end FirstLearnedFire
end KernelR.Hybrid
