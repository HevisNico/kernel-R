import KernelR.HybridCadenceFullBudgetReturns

/-! Choose a genuine existing high-completion witness whose retained physical
reopen is before3.68. The old completion type deliberately had only a3.8
interface, so this stronger existential is constructed afresh; no stronger
property is inferred from an arbitrary older witness. All shared protected
phase constructors, physical paths and exact queues remain unchanged. -/
namespace KernelR.Hybrid
open Set

private theorem full_budget_slow_charge_preguard {B F time : ℝ}
    (hB : 0 ≤ B ∧ B ≤ 2 / 5) (hl : F + 1 ≤ time) (hu : time ≤ F + 2) :
    1 / 10 < (1 / 4 : ℝ) * Real.exp (-B * (time - (F + 1))) := by
  have hd : 0 ≤ time - (F + 1) ∧ time - (F + 1) ≤ 1 := by constructor <;> linarith
  have hp : B * (time - (F + 1)) ≤ 2 / 5 := by nlinarith [hB.1,hB.2,hd.1,hd.2]
  have he := Real.add_one_le_exp (-B * (time - (F + 1)))
  linarith

private theorem full_budget_high_slow_section_exists {θ route} (s : Snapshot 1) (F B : ℝ)
    (hm : s.main 0 = if s.time < F + 1 then .fast else .slow)
    (hq : s.x 0 .q = cadenceProtectedCharge B F s.time)
    (ha : ∀ j q, s.aux j q = .ready) (hr : ∀ j q, s.raw j q = none)
    (hs : ∀ q, RestBand (s.x 0 (.m q)))
    (hp : ∀ d ∈ s.pending, max s.time (F + 1) ≤ d.due) :
    Nonempty (CadenceHighSlowSection θ route s F B) := by
  by_cases htime : s.time < F + 1
  · have hmfast : s.main 0 = .fast := by simpa only [htime,ite_true] using hm
    have hqfast : s.x 0 .q = Real.exp (-a * (s.time - F)) := by
      simpa only [cadenceProtectedCharge,htime,ite_true] using hq
    have hclock (t : ℝ) : s.x 0 .q * Real.exp (-a * (t - s.time)) =
        Real.exp (-a * (t - F)) := by rw [hqfast,attenuation_split]
    have hquarter : Real.exp (-a * ((F + 1) - F)) = (1 / 4 : ℝ) := by
      norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    let flow : Flow θ s (protectedMainEnd θ s 0 0 .fast .ready none (F + 1)) :=
      protectedMainFlow s 0 0 .fast .ready none htime (Or.inl rfl) (Or.inl rfl) hmfast
        (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (ha 0 0)
        (fun j q _ => ha j q) (hr 0 0) (fun j q _ => hr j q) (by intros; contradiction)
        (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
        (by intro j q _; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hs q).2])
        (by intro t ht
            simp only [ite_true,protectedMainRate]
            rw [hclock,←hquarter]
            apply Real.exp_lt_exp.mpr
            nlinarith [a_coarse_bounds.1,ht.2])
        (by intro t ht
            simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
            exact relax_lt (by norm_num) ht.1 (by linarith [(hs 0).2]) (by norm_num))
        (fun d hd => (le_max_right _ _).trans (hp d hd))
    let before := protectedMainEnd θ s 0 0 .fast .ready none (F + 1)
    have hthreshold : before.x 0 .q = 1 / 4 := by
      simpa only [before,protectedMainEnd,protectedMainValues,ite_true,protectedMainRate]
        using (hclock (F + 1)).trans hquarter
    let final := setMain before 0 .slow
    refine ⟨{
      final := final
      execution := .cons (.flow flow) (.cons (.jump (.fastEnd before 0 hmfast hthreshold)) (.nil _))
      contacts_transversal := by trivial
      date := (max_eq_right htime.le).symm
      main_slow := by simp [final,setMain]
      charge_clock := by change before.x 0 .q = _; rw [hthreshold]; simp [final,setMain,before,protectedMainEnd]
      auxiliary := ha, rest := ?_, raw_none := hr, pending := rfl
      gains := fun _ _ => rfl, recovery := fun _ => rfl, emissions := rfl, deliveries := rfl
    }⟩
    intro q
    have hb := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) htime.le (hs q)
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    by_cases hq0 : q = 0
    · subst q
      simpa [final,setMain,before,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hb
    · simpa [final,setMain,before,protectedMainEnd,protectedMainValues,hq0,RestBand] using hb
  · exact ⟨{
      final := s, execution := .nil _, date := (max_eq_left (le_of_not_gt htime)).symm
      contacts_transversal := by trivial
      main_slow := by simpa only [htime,ite_false] using hm
      charge_clock := by simpa only [cadenceProtectedCharge,htime,ite_false] using hq
      auxiliary := ha, rest := hs, raw_none := hr, pending := rfl
      gains := fun _ _ => rfl, recovery := fun _ => rfl, emissions := rfl, deliveries := rfl
    }⟩

private theorem full_budget_high_ready_return_exists {θ route} (s : Snapshot 1) (source F B : ℝ)
    (hm : s.main 0 = .slow)
    (hq : s.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (s.time - (F + 1))))
    (hbown : s.x 0 .b = B) (hB : 37999 / 100000 ≤ B ∧ B ≤ 38001 / 100000)
    (hF : source + 4 / 25 < F ∧ F < source + 13 / 50)
    (htime : F + 1 ≤ s.time ∧ s.time ≤ source + 7 / 5)
    (ha : ∀ j q, s.aux j q = .ready) (hs : ∀ q, RestBand (s.x 0 (.m q)))
    (hr : ∀ j q, s.raw j q = none)
    (hp : ∀ d ∈ s.pending, source + 4 ≤ d.due) :
    ∃ r : CadenceHighReadyReturn θ route s source, r.returnState.time < source + 92 / 25 := by
  have hBpos : 0 < B := by linarith [hB.1]
  have hqb : 1 / 10 < s.x 0 .q := by
    rw [hq]
    exact full_budget_slow_charge_preguard ⟨by linarith [hB.1],by linarith [hB.2]⟩
      htime.1 (by linarith [htime.2,hF.1])
  have hD : 0 < slowReopenDuration s 0 :=
    div_pos (Real.log_pos ((lt_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 10)).mpr (by linarith)))
      (by rw [hbown]; exact hBpos)
  have hR : s.time + slowReopenDuration s 0 = F + 1 + Real.log (5 / 2 : ℝ) / B := by
    have hratio : s.x 0 .q / (1 / 10 : ℝ) =
        (5 / 2 : ℝ) * Real.exp (-B * (s.time - (F + 1))) := by rw [hq]; ring
    simp only [slowReopenDuration,hbown,hratio,Real.log_mul (by norm_num : (5 / 2 : ℝ) ≠ 0)
      (Real.exp_ne_zero _),Real.log_exp]
    field_simp [ne_of_gt hBpos]
    ring
  have hLog : Real.log (5 / 2 : ℝ) / B < 5 / 2 :=
    (div_lt_iff₀ hBpos).mpr (by linarith [KernelR.log_recovery_bounds.2,hB.1])
  let T := s.time + slowReopenDuration s 0
  have hT : s.time < T := by dsimp [T]; linarith
  have hdeadline : T < source + 19 / 5 := by dsimp [T]; rw [hR]; linarith [hF.2]
  have hwait : T < source + 4 := by linarith
  have hTight : T < source + 92 / 25 := by
    apply full_budget_high_reopen_bound hB.1 (show F - source < 13 / 50 by linarith [hF.2])
    dsimp [T]
    rw [hR]
    ring
  let flow : Flow θ s (protectedMainEnd θ s 0 0 .slow .ready none T) :=
    protectedMainFlow s 0 0 .slow .ready none hT (Or.inr rfl) (Or.inl rfl) hm
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (ha 0 0)
      (fun j q _ => ha j q) (hr 0 0) (fun j q _ => hr j q) (by intros; contradiction)
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
      (by intro j q _; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hs q).2])
      (by intro t ht
          simp only [reduceCtorEq,ite_false,protectedMainRate]
          exact slowReopen_preguard s 0 hqb (by rw [hbown]; exact hBpos) ht.2)
      (by intro t ht
          simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (by linarith [(hs 0).2]) (by norm_num))
      (fun d hd => by linarith [hp d hd])
  let before := protectedMainEnd θ s 0 0 .slow .ready none T
  have hthreshold : before.x 0 .q = 1 / 10 := by
    simpa [before,protectedMainEnd,protectedMainValues,protectedMainRate,T] using
      slowReopen_root s 0 hqb (by rw [hbown]; exact hBpos)
  let reopened := setMain before 0 .ready
  let head : Execution θ route s reopened :=
    .cons (.flow flow) (.cons (.jump (.reopen before 0 hm hthreshold)) (.nil _))
  have haux : ∀ j q, reopened.aux j q = .ready ∧ RestBand (reopened.x j (.m q)) := by
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    constructor
    · exact ha 0 q
    · have hb := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hs q)
        (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
      by_cases hq0 : q = 0
      · subst q
        simpa [reopened,setMain,before,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hb
      · simpa [reopened,setMain,before,protectedMainEnd,protectedMainValues,hq0,RestBand] using hb
  have hready : ∀ j, ReadyCoordinates reopened j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    refine ⟨by simp [reopened,setMain],?_,haux 0⟩
    change 1 / 10 - 1 / 100000 ≤ before.x 0 .q ∧ before.x 0 .q ≤ 7 / 50
    rw [hthreshold]
    constructor <;> norm_num
  let waitFlow : Flow θ reopened (quietAt reopened (source + 4)) := quietFlow reopened hwait
    (fun j => (hready j).ready) (fun j q => (haux j q).1) hr
    (fun j => by linarith [(hready j).charge.2]) (fun j q => by linarith [(haux j q).2.2]) hp
  let rest : Execution θ route reopened (quietAt reopened (source + 4)) := .cons (.flow waitFlow) (.nil _)
  let final := quietAt reopened (source + 4)
  refine ⟨{
    final := final, execution := head.append rest, date := rfl
    contacts_transversal := by simp [head, rest, Execution.ContactsTransversal, Jump.ContactTransversal]
    ready := fun j => quietAt_ready_coordinates reopened j (hready j) hwait.le
    charge := ?_, raw_none := hr, pending := rfl, gains := fun _ _ => rfl, recovery := fun _ => rfl
    emissions := rfl, deliveries := rfl, returnState := reopened, head := head, rest := rest
    head_transversal := by trivial
    reconstruct := rfl, return_date := rfl, return_deadline := hdeadline
    return_ready := hready, return_charge := hthreshold, return_raw_none := hr
    return_pending := rfl, return_gains := fun _ _ => rfl, return_recovery := fun _ => rfl
    head_emissions := rfl, head_deliveries := rfl
  },hTight⟩
  change relax (1 / 2) (1 / 10) (before.x 0 .q) T (source + 4) = 1 / 10
  rw [hthreshold]
  simp [relax]

theorem CadenceHighFire.full_budget_completion_exists {θ ε} {s : Snapshot 1} {p : Port}
    (fire : CadenceHighFire θ (fun _ _ => []) s 0 p) (hb : PhysicalBox θ ε)
    (hs : CadenceReadyCoordinates s 0 (8 / 25))
    (hB : 37999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 38001 / 100000)
    (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    ∃ c : CadenceHighCompletion fire, c.returned.returnState.time < s.time + 92 / 25 := by
  let F := fire.final.time
  let P := fire.firstSilent.final.time
  let Te := fire.firstSilent.errorDate
  let Tr := s.time + fire.firstMark.latency + auxCycleDuration (θ 0) p
  let B := s.x 0 .b
  have hF := fire.window
  have hPstart : s.time ≤ P := by
    change s.time ≤ s.time + fire.firstMark.latency + Real.log (5 / 4) / (θ 0).lm p
    linarith [fire.firstMark.early,(hb.aux_durations_positive 0 p).1]
  have hPupper : P < s.time + 1 / 20 := fire.firstSilent.deadline
  have hTe : s.time + 99 / 100 < Te ∧ Te < s.time + 123 / 100 :=
    fire.firstSilent.errorDate_bounds hb
  have hcycle := hb.first_cycle_schedule 0 p ⟨fire.firstMark.early,fire.firstMark.deadline⟩
  have hTr : s.time + 1 < Tr ∧ Tr < s.time + 419 / 300 := by
    constructor <;> dsimp [Tr] <;> linarith [hcycle.2.2.2.2.1,hcycle.2.2.2.2.2]
  have hTrEq : Tr = Te + Real.log 4 / (θ 0).le p := by
    change Tr = (P + Real.log 8 / (θ 0).ls p) + Real.log 4 / (θ 0).le p
    have hPdate : P = fire.firstMark.silentDate := fire.firstSilent.date
    rw [hPdate]
    dsimp [Tr,FirstInputMark.silentDate,auxCycleDuration]
    ring
  have hTeTr : Te < Tr := by rw [hTrEq]; linarith [(hb.aux_durations_positive 0 p).2.2]
  have hBwide : 0 ≤ B ∧ B ≤ 2 / 5 := by constructor <;> dsimp [B] <;> linarith [hB.1,hB.2]
  have hpF : ∀ d ∈ fire.final.pending, s.time + 4 ≤ d.due := by
    intro d hd
    rw [fire.pending,List.append_nil] at hd
    exact hp d hd
  have hother : ∀ j q, j ≠ 0 ∨ q ≠ p → fire.final.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ p := by simpa using h
    linarith [(fire.other_rest hs ho q hq).2]
  have hsensor : fire.final.x 0 (.m p) = (4 / 5 : ℝ) *
      Real.exp (-protectedReadyRate (θ 0) p .silent * (fire.final.time - P)) := by
    simp only [CadenceHighFire.final,FirstInputSilent.learnedFireFinal,
      FirstInputSilent.learnedFireBefore,setMain,readyProtectedEnd,readyProtectedValues,
      and_self,ite_true,fire.firstSilent.sensor_charge]
    rfl
  obtain ⟨silent⟩ := cadence_protected_aux_phase_exists (route := fun _ _ => []) hb fire.final p .silent
    s.time Te F P (4 / 5) B (Or.inl rfl) (by change F < Te; linarith [hF.2,hTe.1])
    (by simpa only [show fire.final.time < F + 1 by dsimp [F]; linarith,ite_true] using fire.main_fast)
    fire.aux_silent fire.aux_other
    (by rw [ite_eq_left (show fire.final.time < s.time + 1 by linarith [hF.2])]; exact fire.raw_active)
    fire.raw_other (by linarith [hF.1]) (by dsimp [F]; linarith [hF.1]) hother
    (by rw [fire.charge]; simp [cadenceProtectedCharge,F]) hsensor (fire.recovery_preserved 0)
    hBwide (by linarith [hPupper,hF.1]) (by dsimp [F]; linarith [hTe.2,hF.1])
    (by norm_num [fastAuxFloor])
    (by dsimp [Te,FirstInputSilent.errorDate,P,fastAuxFloor,protectedReadyRate]; norm_num)
    (fun d hd => by linarith [hpF d hd,hTe.2])
  have hSilentFloor : silent.final.x 0 (.m p) = 1 / 10 := by
    rw [silent.sensor_clock]
    simpa [Te,FirstInputSilent.errorDate,P,protectedReadyRate] using
      silent_full_decay_end (start := P) (ne_of_gt (hb.rates_positive 0 p).2.1)
  let afterError := setAux silent.final 0 p .error
  let toError : Execution θ (fun _ _ => []) fire.final afterError := silent.execution.append
    (.cons (.jump (.error silent.final 0 p silent.aux_mode hSilentFloor)) (.nil _))
  have hErrorOther : ∀ j q, j ≠ 0 ∨ q ≠ p → afterError.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ p := by simpa using h
    simpa [afterError,setAux,hq] using silent.aux_other 0 q (Or.inr hq)
  obtain ⟨err⟩ := cadence_protected_aux_phase_exists (route := fun _ _ => []) hb afterError p .error
    s.time Tr F Te (1 / 10) B (Or.inr rfl)
    (by change silent.final.time < Tr; rw [silent.date]; exact hTeTr)
    (by simpa only [afterError,setAux,silent.date] using silent.main_mode)
    (by simp [afterError,setAux]) hErrorOther
    (by simpa only [afterError,setAux,silent.date] using silent.raw_mode)
    silent.raw_other (by change s.time ≤ silent.final.time; rw [silent.date]; linarith [hTe.1])
    (by dsimp [F]; linarith [hF.1]) silent.other_below
    (by simpa only [afterError,setAux,silent.date] using silent.main_clock)
    (by change silent.final.x 0 (.m p) = _; rw [hSilentFloor]; simp [afterError,setAux,silent.date])
    ((silent.recovery 0).trans (fire.recovery_preserved 0)) hBwide
    (by change Te ≤ silent.final.time; rw [silent.date])
    (by dsimp [F]; linarith [hTr.2,hF.1]) (by norm_num [fastAuxFloor])
    (by simpa only [fastAuxFloor,protectedReadyRate,show AuxMode.error ≠ .silent by decide,ite_false,
      show (1 / 10 : ℝ) / (1 / 40) = 4 by norm_num] using hTrEq.le)
    (fun d hd => by change d ∈ silent.final.pending at hd; rw [silent.pending] at hd; linarith [hpF d hd,hTr.2])
  have hErrorFloor : err.final.x 0 (.m p) = 1 / 40 := by
    rw [err.sensor_clock,hTrEq]
    have he := (protected_decay_schedule (by norm_num : (0 : ℝ) < 1 / 40)
      (by norm_num : (1 / 40 : ℝ) < 1 / 10) (hb.rates_positive 0 p).2.2).2.1
    norm_num at he
    simpa only [protectedReadyRate,add_sub_cancel_left,neg_mul] using he
  let afterReady := setAux err.final 0 p .ready
  let toReady : Execution θ (fun _ _ => []) fire.final afterReady := toError.append
    (err.execution.append (.cons (.jump (.auxReady err.final 0 p err.aux_mode hErrorFloor)) (.nil _)))
  have hAux : ∀ j q, afterReady.aux j q = .ready := by
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    by_cases hq : q = p
    · subst q; simp [afterReady,setAux]
    · simpa [afterReady,setAux,hq] using err.aux_other 0 q (Or.inr hq)
  have hRaw : ∀ j q, afterReady.raw j q = none := by
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    by_cases hq : q = p
    · subst q
      change err.final.raw 0 p = none
      simpa only [show ¬Tr < s.time + 1 by linarith [hTr.1],ite_false] using err.raw_mode
    · exact err.raw_other 0 q (Or.inr hq)
  have hDeliveries : (fire.execution.append toReady).deliveries = [] := by
    simp only [toReady,toError,Execution.deliveries_append,fire.deliveries,silent.deliveries,
      err.deliveries,Execution.deliveries,Move.deliveries,Jump.deliveries,List.append_nil]
  have hRest : ∀ q, RestBand (afterReady.x 0 (.m q)) := by
    intro q
    by_cases hq : q = p
    · subst q
      change RestBand (err.final.x 0 (.m p))
      rw [hErrorFloor]
      constructor <;> norm_num
    · exact ((fire.execution.append toReady).aux_no_input_rest_band 0 q (hs.auxiliary q).1
        (hs.auxiliary q).2 (ho q hq) (by simp only [NoArrivalAt,hDeliveries]; simp)).1.2
  obtain ⟨slow⟩ := full_budget_high_slow_section_exists (θ := θ) (route := fun _ _ => []) afterReady F B
    (by simpa only [afterReady,setAux,err.date] using err.main_mode)
    (by simpa only [afterReady,setAux,err.date] using err.main_clock) hAux hRaw hRest
    (fun d hd => by
      change d ∈ err.final.pending at hd
      rw [err.pending] at hd
      change d ∈ silent.final.pending at hd
      rw [silent.pending] at hd
      apply max_le
      · change err.final.time ≤ d.due
        rw [err.date]
        linarith [hpF d hd,hTr.2]
      · dsimp [F]
        linarith [hpF d hd,hF.2])
  have hSlowB : slow.final.x 0 .b = B :=
    (slow.recovery 0).trans ((err.recovery 0).trans ((silent.recovery 0).trans (fire.recovery_preserved 0)))
  have hSlowTime : F + 1 ≤ slow.final.time ∧ slow.final.time ≤ s.time + 7 / 5 := by
    rw [slow.date]
    change F + 1 ≤ max err.final.time (F + 1) ∧ max err.final.time (F + 1) ≤ s.time + 7 / 5
    rw [err.date]
    exact ⟨le_max_right _ _,max_le (by linarith [hTr.2]) (by dsimp [F]; linarith [hF.2])⟩
  obtain ⟨returned,hReturnTight⟩ := full_budget_high_ready_return_exists (θ := θ) (route := fun _ _ => []) slow.final s.time F B
    slow.main_slow slow.charge_clock hSlowB hB hF hSlowTime slow.auxiliary slow.rest slow.raw_none
    (fun d hd => by
      rw [slow.pending] at hd
      change d ∈ err.final.pending at hd
      rw [err.pending] at hd
      change d ∈ silent.final.pending at hd
      rw [silent.pending] at hd
      exact hpF d hd)
  let toSlow : Execution θ (fun _ _ => []) fire.final slow.final := toReady.append slow.execution
  let execution := toSlow.append returned.execution
  refine ⟨{
    final := returned.final, execution := execution, date := returned.date, ready := returned.ready
    contacts_transversal := by
      simp [execution, toSlow, toReady, toError, Execution.ContactsTransversal, Jump.ContactTransversal,
        silent.contacts_transversal, err.contacts_transversal, slow.contacts_transversal, returned.contacts_transversal]
    charge := returned.charge, raw_none := returned.raw_none
    pending := ?_, gains := ?_, recovery := ?_, emissions := ?_, deliveries := ?_
    physical := execution.physical_invariant hb fire.physical
    raw_valid := execution.raw_valid fire.raw_valid
    slowSection := slow.final, toSlow := toSlow
    toSlow_transversal := by
      simp [toSlow, toReady, toError, Execution.ContactsTransversal, Jump.ContactTransversal,
        silent.contacts_transversal, err.contacts_transversal, slow.contacts_transversal]
    toSlow_pending := slow.pending.trans (err.pending.trans silent.pending)
    toSlow_gains := fun j q => (slow.gains j q).trans ((err.gains j q).trans (silent.gains j q))
    toSlow_recovery := fun j => (slow.recovery j).trans ((err.recovery j).trans (silent.recovery j))
    toSlow_emissions := ?_, toSlow_deliveries := ?_
    returned := returned, returned_final := rfl, reconstruct := HEq.rfl
  },hReturnTight⟩
  · exact returned.pending.trans (slow.pending.trans (err.pending.trans silent.pending))
  · intro j q
    exact (returned.gains j q).trans ((slow.gains j q).trans ((err.gains j q).trans (silent.gains j q)))
  · intro j
    exact (returned.recovery j).trans ((slow.recovery j).trans ((err.recovery j).trans (silent.recovery j)))
  · simp only [execution,toSlow,toReady,toError,Execution.emissions_append,returned.emissions,
      slow.emissions,err.emissions,silent.emissions,Execution.ledger,Move.ledger,Jump.ledger,
      Ledger.add,Ledger.zero,List.append_nil]
  · simp only [execution,toSlow,toReady,toError,Execution.deliveries_append,returned.deliveries,
      slow.deliveries,err.deliveries,silent.deliveries,Execution.deliveries,Move.deliveries,
      Jump.deliveries,List.append_nil]

  · simp only [toSlow,toReady,toError,Execution.emissions_append,
      slow.emissions,err.emissions,silent.emissions,Execution.ledger,Move.ledger,Jump.ledger,
      Ledger.add,Ledger.zero,List.append_nil]
  · simp only [toSlow,toReady,toError,Execution.deliveries_append,
      slow.deliveries,err.deliveries,silent.deliveries,Execution.deliveries,Move.deliveries,
      Jump.deliveries,List.append_nil]

end KernelR.Hybrid
