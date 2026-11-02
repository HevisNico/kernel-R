import KernelR.HybridCadenceHighFireExistence
import KernelR.HybridPrefixBeforeFlow
import KernelR.HybridPrefixStableMemory
import KernelR.HybridSlowReopenExistence

/-! The high-gain response may still be SILENT or ERROR at its genuine FAST
exit. Its protected auxiliary phases retain the same main and sensor clocks,
RAW expiry, queue and forced energy solution across that exit. -/
namespace KernelR.Hybrid
open Set

noncomputable def cadenceProtectedCharge (B F time : ℝ) : ℝ :=
  if time < F + 1 then Real.exp (-a * (time - F))
  else (1 / 4) * Real.exp (-B * (time - (F + 1)))

structure CadenceProtectedAuxPhase (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) (mode : AuxMode) (origin T F P initial B : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  date : final.time = T
  main_mode : final.main 0 = if T < F + 1 then .fast else .slow
  main_clock : final.x 0 .q = cadenceProtectedCharge B F T
  aux_mode : final.aux 0 p = mode
  aux_other : ∀ j q, j ≠ 0 ∨ q ≠ p → final.aux j q = .ready
  sensor_clock : final.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (T - P))
  other_below : ∀ j q, j ≠ 0 ∨ q ≠ p → final.x j (.m q) < 1
  raw_mode : final.raw 0 p = if T < origin + 1 then some origin else none
  raw_other : ∀ j q, j ≠ 0 ∨ q ≠ p → final.raw j q = none
  pending : final.pending = s.pending
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []

private theorem cadence_slow_charge_preguard {B F time : ℝ}
    (hB : 0 ≤ B ∧ B ≤ 2 / 5) (hl : F + 1 ≤ time) (hu : time ≤ F + 2) :
    1 / 10 < (1 / 4 : ℝ) * Real.exp (-B * (time - (F + 1))) := by
  have hd : 0 ≤ time - (F + 1) ∧ time - (F + 1) ≤ 1 := by constructor <;> linarith
  have hp : B * (time - (F + 1)) ≤ 2 / 5 := by nlinarith [hB.1,hB.2,hd.1,hd.2]
  have he := Real.add_one_le_exp (-B * (time - (F + 1)))
  linarith

private theorem cadence_slow_aux_phase_exists {θ ε route} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (mode : AuxMode) (origin T F P initial B : ℝ)
    (hmode : mode = .silent ∨ mode = .error) (hT : s.time < T)
    (hm : s.main 0 = .slow) (ha : s.aux 0 p = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ p → s.aux j q = .ready)
    (hr : ∀ j q, s.raw j q = none)
    (hx : ∀ j q, j ≠ 0 ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : s.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (s.time - (F + 1))))
    (hs : s.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (s.time - P)))
    (hbown : s.x 0 .b = B) (hB : 0 ≤ B ∧ B ≤ 2 / 5)
    (horigin : origin < F) (hstart : F + 1 ≤ s.time) (hF : T ≤ F + 2)
    (hP : P ≤ s.time) (hi : fastAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / fastAuxFloor mode) / protectedReadyRate (θ 0) p mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Nonempty (CadenceProtectedAuxPhase θ route s p mode origin T F P initial B) := by
  have hn : mode ≠ .ready := by rcases hmode with rfl | rfl <;> decide
  have hfloor : 0 < fastAuxFloor mode := by rcases hmode with rfl | rfl <;> norm_num [fastAuxFloor]
  have hrpos : 0 < protectedReadyRate (θ 0) p mode := by
    rcases hmode with rfl | rfl
    · exact (hb.rates_positive 0 p).2.1
    · exact (hb.rates_positive 0 p).2.2
  have hdecay := protected_decay_schedule hfloor hi hrpos
  have hmain_clock (t : ℝ) : s.x 0 .q * Real.exp (-B * (t - s.time)) =
      (1 / 4 : ℝ) * Real.exp (-B * (t - (F + 1))) := by
    rw [hq,mul_assoc,attenuation_split]
  have hsensor_clock (t : ℝ) : s.x 0 (.m p) *
      Real.exp (-protectedReadyRate (θ 0) p mode * (t - s.time)) =
      initial * Real.exp (-protectedReadyRate (θ 0) p mode * (t - P)) := by
    rw [hs,mul_assoc,attenuation_split]
  let flow : Flow θ s (protectedMainEnd θ s 0 p .slow mode none T) :=
    protectedMainFlow s 0 p .slow mode none hT (Or.inr rfl)
      (by rcases hmode with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr rfl))
      hm (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) ha hao (hr 0 p)
      (fun j q _ => hr j q) (by intros; contradiction)
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) hx
      (by intro t ht
          simp only [reduceCtorEq,ite_false,protectedMainRate,hbown]
          rw [hmain_clock]
          exact cadence_slow_charge_preguard hB (by linarith [ht.1]) (by linarith [ht.2]))
      (by intro t ht
          simp only [hn,ite_false]
          change fastAuxFloor mode < _
          rw [hsensor_clock]
          exact hdecay.2.2 (t - P) (by linarith [ht.1]) (by linarith [ht.2])) hp
  let final := protectedMainEnd θ s 0 p .slow mode none T
  have hfast : ¬T < F + 1 := by linarith
  have hraw : ¬T < origin + 1 := by linarith
  refine ⟨{
    final := final, execution := .cons (.flow flow) (.nil _), date := rfl
    main_mode := by simpa only [final,protectedMainEnd,hfast,ite_false] using hm
    main_clock := ?_, aux_mode := ha, aux_other := hao, sensor_clock := ?_
    other_below := ?_, raw_mode := by simpa only [final,protectedMainEnd,hraw,ite_false] using hr 0 p
    raw_other := fun j q _ => hr j q, pending := rfl
    gains := fun _ _ => rfl, recovery := fun _ => rfl, emissions := rfl, deliveries := rfl
  }⟩
  · simpa [final,protectedMainEnd,protectedMainValues,protectedMainRate,hbown,cadenceProtectedCharge,hfast]
      using hmain_clock T
  · simpa [final,protectedMainEnd,protectedMainValues,hn] using hsensor_clock T
  · intro j q h
    have hne : ¬ (j = 0 ∧ q = p) := by tauto
    simpa [final,protectedMainEnd,protectedMainValues,hne] using
      relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hx j q h) (by norm_num : (1 / 40 : ℝ) < 1)

noncomputable def CadenceProtectedAuxPhase.prepend {θ route s v p mode origin T F P initial B}
    (r : CadenceProtectedAuxPhase θ route v p mode origin T F P initial B)
    (e : Execution θ route s v) (hp : v.pending = s.pending)
    (hg : ∀ j q, v.x j (.z q) = s.x j (.z q))
    (hb : ∀ j, v.x j .b = s.x j .b)
    (he : e.ledger.emissions = []) (hd : e.deliveries = []) :
    CadenceProtectedAuxPhase θ route s p mode origin T F P initial B where
  final := r.final
  execution := e.append r.execution
  date := r.date
  main_mode := r.main_mode
  main_clock := r.main_clock
  aux_mode := r.aux_mode
  aux_other := r.aux_other
  sensor_clock := r.sensor_clock
  other_below := r.other_below
  raw_mode := r.raw_mode
  raw_other := r.raw_other
  pending := r.pending.trans hp
  gains := fun j q => (r.gains j q).trans (hg j q)
  recovery := fun j => (r.recovery j).trans (hb j)
  emissions := by rw [Execution.emissions_append,he,r.emissions,List.nil_append]
  deliveries := by rw [Execution.deliveries_append,hd,r.deliveries,List.nil_append]

/-- Continue the same auxiliary clock across the real FAST exit, consuming
RAW expiry at its original date and every equal-date boundary jump. -/
theorem cadence_protected_aux_phase_exists {θ ε route} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (mode : AuxMode) (origin T F P initial B : ℝ)
    (hmode : mode = .silent ∨ mode = .error) (hT : s.time < T)
    (hm : s.main 0 = if s.time < F + 1 then .fast else .slow)
    (ha : s.aux 0 p = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw 0 p = if s.time < origin + 1 then some origin else none)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ p → s.raw j q = none)
    (horigin : origin ≤ s.time) (hFsource : origin < F)
    (hx : ∀ j q, j ≠ 0 ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : s.x 0 .q = cadenceProtectedCharge B F s.time)
    (hs : s.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (s.time - P)))
    (hbown : s.x 0 .b = B) (hB : 0 ≤ B ∧ B ≤ 2 / 5)
    (hP : P ≤ s.time) (hF : T ≤ F + 2) (hi : fastAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / fastAuxFloor mode) / protectedReadyRate (θ 0) p mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Nonempty (CadenceProtectedAuxPhase θ route s p mode origin T F P initial B) := by
  by_cases hstart : s.time < F + 1
  · rw [ite_eq_left hstart] at hm
    have hqfast : s.x 0 .q = Real.exp (-a * (s.time - F)) := by
      simpa only [cadenceProtectedCharge,hstart,ite_true] using hq
    by_cases hstop : T < F + 1
    · obtain ⟨r,ht,hrT⟩ := port_fast_aux_phase_exists (route := route) hb s p mode origin T F P initial
        hmode hT hm ha hao hr ho horigin hx hqfast hs hP hstop.le hi hphase hp
      exact ⟨{
        final := r.final, execution := r.execution, date := ht
        main_mode := by simpa only [hstop,ite_true] using r.main_fast
        main_clock := by simpa only [ht,cadenceProtectedCharge,hstop,ite_true] using r.main_clock
        aux_mode := r.aux_mode, aux_other := r.aux_other
        sensor_clock := by simpa only [ht] using r.sensor_clock
        other_below := r.other_below, raw_mode := hrT, raw_other := r.raw_other
        pending := r.pending, gains := r.gains, recovery := r.recovery
        emissions := r.emissions, deliveries := r.deliveries
      }⟩
    · obtain ⟨r,ht,hrT⟩ := port_fast_aux_phase_exists (route := route) hb s p mode origin (F + 1) F P initial
        hmode hstart hm ha hao hr ho horigin hx hqfast hs hP le_rfl hi
        (by linarith) (fun d hd => by linarith [hp d hd])
      have hquarter : r.final.x 0 .q = 1 / 4 := by
        rw [r.main_clock,ht]
        norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      let after := setMain r.final 0 .slow
      let prefixRun : Execution θ route s after := r.execution.append
        (.cons (.jump (.fastEnd r.final 0 r.main_fast hquarter)) (.nil _))
      have haftertime : after.time = F + 1 := ht
      have hafterq : after.x 0 .q = 1 / 4 := hquarter
      have hafterraw : ∀ j q, after.raw j q = none := by
        intro j q
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        by_cases hqp : q = p
        · subst q
          change r.final.raw 0 p = none
          simpa only [show ¬F + 1 < origin + 1 by linarith,ite_false] using hrT
        · exact r.raw_other 0 q (Or.inr hqp)
      have hafterclock : after.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (after.time - (F + 1))) := by
        rw [hafterq,haftertime]
        simp
      have hafterb : after.x 0 .b = B := (r.recovery 0).trans hbown
      have heP : prefixRun.ledger.emissions = [] := by
        simp only [prefixRun,Execution.emissions_append,r.emissions,Execution.ledger,Move.ledger,Jump.ledger,Ledger.add,Ledger.zero,List.append_nil]
      have hdP : prefixRun.deliveries = [] := by
        simp only [prefixRun,Execution.deliveries_append,r.deliveries,Execution.deliveries,Move.deliveries,Jump.deliveries,List.append_nil]
      have hrP : ∀ j, after.x j .b = s.x j .b := r.recovery
      have hgP : ∀ j q, after.x j (.z q) = s.x j (.z q) := r.gains
      have hqP : after.pending = s.pending := r.pending
      by_cases heq : T = F + 1
      · have hfast : ¬T < F + 1 := by linarith
        have hraw : ¬T < origin + 1 := by linarith
        exact ⟨{
          final := after, execution := prefixRun, date := haftertime.trans heq.symm
          main_mode := by simp [after,setMain,hfast]
          main_clock := by simp [cadenceProtectedCharge,heq,hafterq]
          aux_mode := r.aux_mode, aux_other := r.aux_other
          sensor_clock := by simpa only [after,setMain,ht,heq] using r.sensor_clock
          other_below := r.other_below
          raw_mode := by simpa only [hraw,ite_false] using hafterraw 0 p
          raw_other := fun j q _ => hafterraw j q
          pending := hqP, gains := hgP, recovery := hrP, emissions := heP, deliveries := hdP
        }⟩
      · obtain ⟨slow⟩ := cadence_slow_aux_phase_exists (route := route) hb after p mode origin T F P initial B
          hmode (by rw [haftertime]; exact lt_of_le_of_ne (le_of_not_gt hstop) (Ne.symm heq))
          (by simp [after,setMain]) r.aux_mode r.aux_other hafterraw r.other_below hafterclock
          (by simpa only [after,setMain,ht] using r.sensor_clock) hafterb hB hFsource
          (by rw [haftertime]) hF (by rw [haftertime]; linarith) hi hphase
          (fun d hd => by rw [hqP] at hd; exact hp d hd)
        exact ⟨slow.prepend prefixRun hqP hgP hrP heP hdP⟩
  · rw [ite_eq_right hstart] at hm
    have hqslow : s.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (s.time - (F + 1))) := by
      simpa only [cadenceProtectedCharge,hstart,ite_false] using hq
    have hrnone : ∀ j q, s.raw j q = none := by
      intro j q
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hqp : q = p
      · subst q
        simpa only [show ¬s.time < origin + 1 by linarith,ite_false] using hr
      · exact ho 0 q (Or.inr hqp)
    exact cadence_slow_aux_phase_exists hb s p mode origin T F P initial B hmode hT hm ha hao
      hrnone hx hqslow hs hbown hB hFsource (le_of_not_gt hstart) hF hP hi hphase hp

structure CadenceHighSlowSection (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (F B : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  date : final.time = max s.time (F + 1)
  main_slow : final.main 0 = .slow
  charge_clock : final.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (final.time - (F + 1)))
  auxiliary : ∀ j q, final.aux j q = .ready
  rest : ∀ q, RestBand (final.x 0 (.m q))
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = s.pending
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []

private theorem cadence_high_slow_section_exists {θ route} (s : Snapshot 1) (F B : ℝ)
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
      main_slow := by simpa only [htime,ite_false] using hm
      charge_clock := by simpa only [cadenceProtectedCharge,htime,ite_false] using hq
      auxiliary := ha, rest := hs, raw_none := hr, pending := rfl
      gains := fun _ _ => rfl, recovery := fun _ => rfl, emissions := rfl, deliveries := rfl
    }⟩

structure CadenceHighReadyReturn (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (source : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  date : final.time = source + 4
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = s.pending
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  returnState : Snapshot 1
  head : Execution θ route s returnState
  rest : Execution θ route returnState final
  reconstruct : execution = head.append rest
  return_date : returnState.time = s.time + slowReopenDuration s 0
  return_deadline : returnState.time < source + 19 / 5
  return_ready : ∀ j, ReadyCoordinates returnState j
  return_charge : returnState.x 0 .q = 1 / 10
  return_raw_none : ∀ j q, returnState.raw j q = none
  return_pending : returnState.pending = s.pending
  return_gains : ∀ j q, returnState.x j (.z q) = s.x j (.z q)
  return_recovery : ∀ j, returnState.x j .b = s.x j .b
  head_emissions : head.ledger.emissions = []
  head_deliveries : head.deliveries = []

private theorem cadence_high_ready_return_exists {θ route} (s : Snapshot 1) (source F B : ℝ)
    (hm : s.main 0 = .slow)
    (hq : s.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (s.time - (F + 1))))
    (hbown : s.x 0 .b = B) (hB : 37999 / 100000 ≤ B ∧ B ≤ 38001 / 100000)
    (hF : source + 4 / 25 < F ∧ F < source + 13 / 50)
    (htime : F + 1 ≤ s.time ∧ s.time ≤ source + 7 / 5)
    (ha : ∀ j q, s.aux j q = .ready) (hs : ∀ q, RestBand (s.x 0 (.m q)))
    (hr : ∀ j q, s.raw j q = none)
    (hp : ∀ d ∈ s.pending, source + 4 ≤ d.due) :
    Nonempty (CadenceHighReadyReturn θ route s source) := by
  have hBpos : 0 < B := by linarith [hB.1]
  have hqb : 1 / 10 < s.x 0 .q := by
    rw [hq]
    exact cadence_slow_charge_preguard ⟨by linarith [hB.1],by linarith [hB.2]⟩
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
    ready := fun j => quietAt_ready_coordinates reopened j (hready j) hwait.le
    charge := ?_, raw_none := hr, pending := rfl, gains := fun _ _ => rfl, recovery := fun _ => rfl
    emissions := rfl, deliveries := rfl, returnState := reopened, head := head, rest := rest
    reconstruct := rfl, return_date := rfl, return_deadline := hdeadline
    return_ready := hready, return_charge := hthreshold, return_raw_none := hr
    return_pending := rfl, return_gains := fun _ _ => rfl, return_recovery := fun _ => rfl
    head_emissions := rfl, head_deliveries := rfl
  }⟩
  change relax (1 / 2) (1 / 10) (before.x 0 .q) T (source + 4) = 1 / 10
  rw [hthreshold]
  simp [relax]

structure CadenceHighCompletion {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    (fire : CadenceHighFire θ (fun _ _ => []) s 0 p) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) fire.final final
  date : final.time = s.time + 4
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = fire.final.pending
  gains : ∀ j q, final.x j (.z q) = fire.final.x j (.z q)
  recovery : ∀ j, final.x j .b = fire.final.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  slowSection : Snapshot 1
  toSlow : Execution θ (fun _ _ => []) fire.final slowSection
  toSlow_pending : slowSection.pending = fire.final.pending
  toSlow_gains : ∀ j q, slowSection.x j (.z q) = fire.final.x j (.z q)
  toSlow_recovery : ∀ j, slowSection.x j .b = fire.final.x j .b
  toSlow_emissions : toSlow.ledger.emissions = []
  toSlow_deliveries : toSlow.deliveries = []
  returned : CadenceHighReadyReturn θ (fun _ _ => []) slowSection s.time
  returned_final : final = returned.final
  reconstruct : HEq execution (toSlow.append returned.execution)

/-- Complete the actual high response, including the auxiliary phase that
straddles its FAST exit. A source due exactly at S+4 remains pending. -/
theorem CadenceHighFire.high_completion_exists {θ ε} {s : Snapshot 1} {p : Port}
    (fire : CadenceHighFire θ (fun _ _ => []) s 0 p) (hb : PhysicalBox θ ε)
    (hs : CadenceReadyCoordinates s 0 (8 / 25))
    (hB : 37999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 38001 / 100000)
    (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    Nonempty (CadenceHighCompletion fire) := by
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
  obtain ⟨slow⟩ := cadence_high_slow_section_exists (θ := θ) (route := fun _ _ => []) afterReady F B
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
  obtain ⟨returned⟩ := cadence_high_ready_return_exists (θ := θ) (route := fun _ _ => []) slow.final s.time F B
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
    charge := returned.charge, raw_none := returned.raw_none
    pending := ?_, gains := ?_, recovery := ?_, emissions := ?_, deliveries := ?_
    physical := execution.physical_invariant hb fire.physical
    raw_valid := execution.raw_valid fire.raw_valid
    slowSection := slow.final, toSlow := toSlow
    toSlow_pending := slow.pending.trans (err.pending.trans silent.pending)
    toSlow_gains := fun j q => (slow.gains j q).trans ((err.gains j q).trans (silent.gains j q))
    toSlow_recovery := fun j => (slow.recovery j).trans ((err.recovery j).trans (silent.recovery j))
    toSlow_emissions := ?_, toSlow_deliveries := ?_
    returned := returned, returned_final := rfl, reconstruct := HEq.rfl
  }⟩
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

namespace CadenceHighCompletion
variable {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
  {fire : CadenceHighFire θ (fun _ _ => []) s 0 p} (c : CadenceHighCompletion fire)

/-- The actual protected prefix ends after its guarded logarithmic reopen. -/
noncomputable def returnExecution : Execution θ (fun _ _ => []) fire.final c.returned.returnState :=
  c.toSlow.append c.returned.head

theorem return_ready : ∀ j, ReadyCoordinates c.returned.returnState j := c.returned.return_ready

theorem return_charge : c.returned.returnState.x 0 .q = 1 / 10 := c.returned.return_charge

theorem return_raw_none : ∀ j q, c.returned.returnState.raw j q = none := c.returned.return_raw_none

theorem return_pending : c.returned.returnState.pending = fire.final.pending :=
  c.returned.return_pending.trans c.toSlow_pending

theorem return_gains (j : Fin 1) (q : Port) :
    c.returned.returnState.x j (.z q) = fire.final.x j (.z q) :=
  (c.returned.return_gains j q).trans (c.toSlow_gains j q)

theorem return_recovery (j : Fin 1) : c.returned.returnState.x j .b = fire.final.x j .b :=
  (c.returned.return_recovery j).trans (c.toSlow_recovery j)

theorem return_emissions : c.returnExecution.ledger.emissions = [] := by
  rw [returnExecution,Execution.emissions_append,c.toSlow_emissions,c.returned.head_emissions,List.nil_append]

theorem return_deliveries : c.returnExecution.deliveries = [] := by
  rw [returnExecution,Execution.deliveries_append,c.toSlow_deliveries,c.returned.head_deliveries,List.nil_append]

/-- The actual logarithmic reopen is complete strictly before3.8 after
its source, leaving room for later independently jittered gaps of at least3.9. -/
theorem return_deadline : c.returned.returnState.time < s.time + 19 / 5 :=
  c.returned.return_deadline

theorem auxiliary_rest (q : Port) :
    c.final.aux 0 q = .ready ∧ RestBand (c.final.x 0 (.m q)) :=
  (c.ready 0).auxiliary q

theorem guards : BeforeGuards c.final c.final.x := by
  constructor
  · intro j
    rw [(c.ready j).ready]
    linarith [(c.ready j).charge.2]
  · intro j q
    rw [((c.ready j).auxiliary q).1]
    linarith [((c.ready j).auxiliary q).2.2]

/-- Saturation includes source urgency, so a token due exactly at S+4 must
first be delivered by the actual next-source constructor. -/
theorem complete_if_strict_future (hp : ∀ d ∈ c.final.pending, c.final.time < d.due) :
    CompleteThrough c.execution c.final.time := by
  refine ⟨rfl,?_,hp⟩
  intro u
  exact c.guards.no_jump (by intro j q origin h; rw [c.raw_none j q] at h; contradiction) hp u

/-- Resume the very path retained by a real outgoing-wire cut. -/
noncomputable def fromCut {H : ℝ} (cut : c.execution.BeforeFlowCut H) :
    Execution θ (fun _ _ => []) cut.state c.final :=
  .cons (.flow cut.flow) cut.rest

theorem fromCut_emissions {H : ℝ} (cut : c.execution.BeforeFlowCut H) :
    (c.fromCut cut).ledger.emissions = [] := by
  have he := (List.append_eq_nil_iff.mp (cut.emissions.symm.trans c.emissions)).2
  exact he

theorem fromCut_deliveries {H : ℝ} (cut : c.execution.BeforeFlowCut H) :
    (c.fromCut cut).deliveries = [] := by
  have hd := (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans c.deliveries)).2
  exact hd

theorem fromCut_gains {ε H} (hb : PhysicalBox θ ε) (cut : c.execution.BeforeFlowCut H) (q : Port) :
    c.final.x 0 (.z q) = cut.state.x 0 (.z q) := by
  have hc := cut.isPrefix.gain_eq_of_final hb 0 q (c.gains 0 q)
  rw [c.gains,hc]

theorem fromCut_recovery {ε H} (hb : PhysicalBox θ ε) (cut : c.execution.BeforeFlowCut H) :
    c.final.x 0 .b = cut.state.x 0 .b := by
  have hc := cut.isPrefix.recovery_eq_of_final hb 0 (c.recovery 0)
  rw [c.recovery,hc]

end CadenceHighCompletion
end KernelR.Hybrid
