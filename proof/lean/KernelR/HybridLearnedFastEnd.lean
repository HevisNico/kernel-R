import KernelR.HybridBirthFirstFastEnd

namespace KernelR.Hybrid
open Set

structure LearnedFastEnd {θ : Fin 1 → Parameters} {s : Snapshot 1} (c : FirstLearnedFire θ (fun _ _ => []) s 0 0) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) c.final final
  date : final.time = c.final.time + 1
  main_slow : final.main 0 = .slow
  charge : final.x 0 .q = 1 / 4
  auxiliary : ∀ j p, final.aux j p = .ready
  sensor_charge : final.x 0 (.m 0) = 1 / 40
  rest : ∀ p, RestBand (final.x 0 (.m p))
  raw_none : ∀ j p, final.raw j p = none
  pending : final.pending = c.final.pending
  gains : ∀ j p, final.x j (.z p) = c.final.x j (.z p)
  recovery : ∀ j, final.x j .b = c.final.x j .b
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []


theorem FirstLearnedFire.learned_fast_end_exists {θ ε} {s : Snapshot 1}
    (c : FirstLearnedFire θ (fun _ _ => []) s 0 0) (hb : PhysicalBox θ ε)
    (hs : ReadyCoordinates s 0) (hg : Real.exp (s.x 0 (.z 0)) ≤ 2)
    (ho : ∀ p, p ≠ 0 → s.raw 0 p = none)
    (hp : ∀ d ∈ s.pending, s.time + 8 ≤ d.due) :
    Nonempty (LearnedFastEnd c) := by
  let F := c.final.time
  let P := c.firstSilent.final.time
  let Te := c.firstSilent.errorDate
  let Tr := s.time + c.firstMark.latency + auxCycleDuration (θ 0) 0
  have hFdate : F = s.time + c.latency := c.date
  have hFearly : s.time + 2 / 5 < F := by
    exact readyPulse_root_after_four_tenths hs.charge.2 hg
      (by rw [hFdate]; linarith [c.early]) c.response_root
  have hFupper : F < s.time + 9 / 10 := by rw [hFdate]; linarith [c.deadline]
  have hP : P < s.time + 1 / 20 := c.firstSilent.deadline
  have hPstart : s.time ≤ P := by
    change s.time ≤ s.time + c.firstMark.latency + Real.log (5 / 4) / (θ 0).lm 0
    linarith [c.firstMark.early,(hb.aux_durations_positive 0 0).1]
  have hTe : s.time + 99 / 100 < Te ∧ Te < s.time + 123 / 100 :=
    c.firstSilent.errorDate_bounds hb
  have hcycle := hb.first_cycle_schedule 0 0 ⟨c.firstMark.early,c.firstMark.deadline⟩
  have hTr : s.time + 1 < Tr ∧ Tr < s.time + 419 / 300 := by
    constructor <;> dsimp [Tr] <;> linarith [hcycle.2.2.2.2.1,hcycle.2.2.2.2.2]
  have hTeTr : Te < Tr := by
    have hd := (hb.aux_durations_positive 0 0).2.2
    change s.time + c.firstMark.latency + Real.log (5 / 4) / (θ 0).lm 0 +
      Real.log 8 / (θ 0).ls 0 < s.time + c.firstMark.latency + auxCycleDuration (θ 0) 0
    dsimp [auxCycleDuration]
    linarith
  have hTrF : Tr < F + 1 := by linarith [hTr.2]
  have hfuture : ∀ d ∈ c.final.pending, F + 1 ≤ d.due := by
    intro d hd
    rw [c.pending] at hd
    simp only [List.append_nil] at hd
    linarith [hp d hd]
  have hother : ∀ j q, j ≠ 0 ∨ q ≠ 0 → c.final.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ 0 := by simpa using h
    have hh := c.execution.aux_no_input_rest_band 0 q (hs.auxiliary q).1
      (hs.auxiliary q).2 (ho q hq)
      (by simp [NoArrivalAt,c.deliveries])
    change c.final.x 0 (.m q) < 1
    linarith [hh.1.2.2]
  have hclock : c.final.x 0 .q = Real.exp (-a * (c.final.time - F)) := by
    simp only [F,sub_self,mul_zero,Real.exp_zero]
    exact c.charge
  have hsensor : c.final.x 0 (.m 0) = (4 / 5 : ℝ) * Real.exp (-protectedReadyRate (θ 0) 0 .silent * (c.final.time - P)) := by
    change c.firstSilent.final.x 0 (.m 0) * Real.exp (-protectedReadyRate (θ 0) 0 .silent *
      (s.time + c.latency - c.firstSilent.final.time)) = _
    rw [c.firstSilent.sensor_charge]
    rfl
  obtain ⟨silent,hsdate,hsraw⟩ := fast_aux_phase_exists (route := fun _ _ => []) hb c.final .silent s.time Te F P (4 / 5)
    (Or.inl rfl) (by change F < Te; linarith [hTe.1]) c.main_fast c.aux_silent
    c.aux_other (by rw [ite_eq_left (show c.final.time < s.time + 1 by change F < _; linarith)]; exact c.raw_active)
    c.raw_other (by change s.time ≤ F; linarith) hother hclock hsensor
    (by change P ≤ F; linarith) (by linarith [hTrF]) (by norm_num [fastAuxFloor])
    (by dsimp [Te,FirstInputSilent.errorDate,P,fastAuxFloor,protectedReadyRate]; norm_num)
    (fun d hd => by linarith [hfuture d hd])
  have hsthreshold : silent.final.x 0 (.m 0) = 1 / 10 := by
    rw [silent.sensor_clock,hsdate]
    simpa [Te,FirstInputSilent.errorDate,P,protectedReadyRate] using
      silent_full_decay_end (start := P) (ne_of_gt (hb.rates_positive 0 0).2.1)
  let se := setAux silent.final 0 0 .error
  let es : Execution θ (fun _ _ => []) c.final se := silent.execution.append
    (.cons (.jump (.error silent.final 0 0 silent.aux_mode hsthreshold)) (.nil _))
  have hseother : ∀ j q, j ≠ 0 ∨ q ≠ 0 → se.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ 0 := by simpa using h
    simpa [se,setAux,hq] using silent.aux_other 0 q (Or.inr hq)
  have hTrsplit : Tr = Te + Real.log 4 / (θ 0).le 0 := by
    change Tr = (P + Real.log 8 / (θ 0).ls 0) + Real.log 4 / (θ 0).le 0
    have hPdate : P = c.firstMark.silentDate := c.firstSilent.date
    rw [hPdate]
    dsimp [Tr,FirstInputMark.silentDate,auxCycleDuration]
    ring
  obtain ⟨err,hedate,heraw⟩ := fast_aux_phase_exists (route := fun _ _ => []) hb se .error s.time Tr F Te (1 / 10)
    (Or.inr rfl) (by change silent.final.time < Tr; rw [hsdate]; exact hTeTr)
    silent.main_fast (by simp [se,setAux]) hseother
    (by simpa only [se,setAux,hsdate] using hsraw) silent.raw_other
    (by change s.time ≤ silent.final.time; rw [hsdate]; linarith [hTe.1]) silent.other_below
    silent.main_clock (by simpa only [se,setAux,hsdate,sub_self,mul_zero,Real.exp_zero,mul_one] using hsthreshold)
    (by change Te ≤ silent.final.time; rw [hsdate]) hTrF.le (by norm_num [fastAuxFloor])
    (by change Tr ≤ Te + Real.log ((1 / 10 : ℝ) / (1 / 40)) / (θ 0).le 0
        norm_num
        exact hTrsplit.le)
    (fun d hd => by change d ∈ silent.final.pending at hd; rw [silent.pending] at hd; linarith [hfuture d hd])
  have hethreshold : err.final.x 0 (.m 0) = 1 / 40 := by
    rw [err.sensor_clock,hedate]
    rw [hTrsplit]
    have hend := (protected_decay_schedule (by norm_num : (0 : ℝ) < 1 / 40)
      (by norm_num : (1 / 40 : ℝ) < 1 / 10) (hb.rates_positive 0 0).2.2).2.1
    norm_num at hend
    simpa only [protectedReadyRate,add_sub_cancel_left,neg_mul] using hend
  let ready := setAux err.final 0 0 .ready
  let er : Execution θ (fun _ _ => []) se ready := err.execution.append
    (.cons (.jump (.auxReady err.final 0 0 err.aux_mode hethreshold)) (.nil _))
  have hreadyraw : ∀ j p, ready.raw j p = none := by
    intro j p
    by_cases h : j = 0 ∧ p = 0
    · rcases h with ⟨rfl,rfl⟩
      change err.final.raw 0 0 = none
      simpa [show ¬Tr < s.time + 1 by linarith [hTr.1]] using heraw
    · exact err.raw_other j p (by tauto)
  have hreadyaux : ∀ j p, ready.aux j p = .ready := by
    intro j p
    by_cases h : j = 0 ∧ p = 0
    · rcases h with ⟨rfl,rfl⟩; simp [ready,setAux]
    · have hh : j ≠ 0 ∨ p ≠ 0 := by tauto
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hp : p ≠ 0 := by simpa using hh
      simpa [ready,setAux,hp] using err.aux_other 0 p (Or.inr hp)
  have hreadydate : ready.time = Tr := hedate
  have hreadym : ready.x 0 (.m 0) = 1 / 40 := hethreshold
  have hqglobal (t : ℝ) : ready.x 0 .q * Real.exp (-a * (t - ready.time)) = Real.exp (-a * (t - F)) := by
    change err.final.x 0 .q * Real.exp (-a * (t - err.final.time)) = _
    rw [err.main_clock,attenuation_split]
  let flow : Flow θ ready (protectedMainEnd θ ready 0 0 .fast .ready none (F + 1)) :=
    protectedMainFlow ready 0 0 .fast .ready none (by rw [hreadydate]; exact hTrF)
      (Or.inl rfl) (Or.inl rfl) err.main_fast
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (hreadyaux 0 0)
      (fun j p _ => hreadyaux j p) (hreadyraw 0 0) (fun j p _ => hreadyraw j p) (by intros; contradiction)
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) err.other_below
      (by intro t ht
          simp only [ite_true,protectedMainRate]
          rw [hqglobal]
          have he : Real.exp (-a * ((F + 1) - F)) = (1 / 4 : ℝ) := by
            norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
          rw [← he]
          apply Real.exp_lt_exp.mpr
          nlinarith [a_coarse_bounds.1,ht.2])
      (by intro t ht
          simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (by rw [hreadym]; norm_num) (by norm_num))
      (fun d hd => by change d ∈ err.final.pending at hd; rw [err.pending] at hd
                      change d ∈ silent.final.pending at hd; rw [silent.pending] at hd; exact hfuture d hd)
  let before := protectedMainEnd θ ready 0 0 .fast .ready none (F + 1)
  have hbeforeq : before.x 0 .q = 1 / 4 := by
    change ready.x 0 .q * Real.exp (-a * ((F + 1) - ready.time)) = _
    rw [hqglobal]
    norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  let final := setMain before 0 .slow
  let finish : Execution θ (fun _ _ => []) ready final :=
    .cons (.flow flow) (.cons (.jump (.fastEnd before 0 err.main_fast hbeforeq)) (.nil _))
  let e := es.append (er.append finish)
  have hdel : e.deliveries = [] := by
    simp [e,es,er,finish,Execution.deliveries_append,silent.deliveries,err.deliveries,
      Execution.deliveries,Move.deliveries,Jump.deliveries]
  have hfinishEm : finish.ledger.emissions = [] := rfl
  have herEm : er.ledger.emissions = [] := by
    change (err.execution.append (.cons (.jump (.auxReady err.final 0 0 err.aux_mode hethreshold)) (.nil _))).ledger.emissions = []
    rw [Execution.emissions_append,err.emissions]
    rfl
  have hesEm : es.ledger.emissions = [] := by
    rw [Execution.emissions_append,silent.emissions]
    rfl
  have hem : e.ledger.emissions = [] := by
    change (es.append (er.append finish)).ledger.emissions = []
    rw [Execution.emissions_append es (er.append finish),hesEm,
      Execution.emissions_append er finish,herEm,hfinishEm]
    rfl
  have hfinalm : final.x 0 (.m 0) = 1 / 40 := by
    simp [final,setMain,before,protectedMainEnd,protectedMainValues,rawInputScale,
      auxPulse_zero_eq_relax,relax,hreadym]
  refine ⟨{
    final := final
    execution := e
    date := rfl
    main_slow := by simp [final,setMain]
    charge := hbeforeq
    auxiliary := hreadyaux
    sensor_charge := hfinalm
    rest := ?_
    raw_none := hreadyraw
    pending := err.pending.trans silent.pending
    gains := fun j p => (err.gains j p).trans (silent.gains j p)
    recovery := fun j => (err.recovery j).trans (silent.recovery j)
    physical := e.physical_invariant hb c.physical
    raw_valid := e.raw_valid c.raw_valid
    emissions := hem
    deliveries := hdel
  }⟩
  intro p
  by_cases hp : p = 0
  · subst p; rw [hfinalm]; constructor <;> norm_num
  · let eFire : Execution θ (fun _ _ => []) c.final final := e
    have hdelFire : eFire.deliveries = [] := hdel
    let whole := c.execution.append eFire
    exact (whole.aux_no_input_rest_band 0 p (hs.auxiliary p).1
      (hs.auxiliary p).2 (ho p hp)
      (by
        have hwhole : whole.deliveries = [] := by
          change (c.execution.append eFire).deliveries = []
          rw [Execution.deliveries_append,c.deliveries,hdelFire]
          rfl
        intro d hd
        rw [hwhole] at hd
        contradiction)).1.2

end KernelR.Hybrid
