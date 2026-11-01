import KernelR.HybridMidLearnedFastEnd
import KernelR.HybridGuardNoJump

/-! Port-generic FAST completion from an actual firing section. The input
contains physical coordinates and scalar clocks, never an incoming execution. -/
namespace KernelR.Hybrid
open Set

structure PortFastCompletion (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) where
  final : Snapshot 1
  execution : Execution θ route s final
  date : final.time = s.time + 1
  main_slow : final.main 0 = .slow
  charge : final.x 0 .q = 1 / 4
  auxiliary : ∀ j q, final.aux j q = .ready
  sensor_charge : final.x 0 (.m p) = 1 / 40
  rest : ∀ q, RestBand (final.x 0 (.m q))
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = s.pending
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []

/-- Continue the actual SILENT sensor and protected main clocks through
ERROR, auxiliary READY and a real FAST exit. RAW expiry is performed at its
original date, including coincidence with an auxiliary section. -/
theorem port_fast_completion_exists {θ ε route} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (origin P Te Tr : ℝ)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : s.main 0 = .fast) (ha : s.aux 0 p = .silent)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw 0 p = some origin)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ p → s.raw j q = none)
    (hrest : ∀ q, q ≠ p → RestBand (s.x 0 (.m q)))
    (hq : s.x 0 .q = 1)
    (hsensor : s.x 0 (.m p) = (4 / 5 : ℝ) *
      Real.exp (-protectedReadyRate (θ 0) p .silent * (s.time - P)))
    (horigin : origin ≤ s.time ∧ s.time < origin + 1)
    (hP : P ≤ s.time)
    (hTe : Te = P + Real.log 8 / (θ 0).ls p)
    (hTr : Tr = Te + Real.log 4 / (θ 0).le p)
    (hError : s.time < Te) (hAfterRaw : origin + 1 < Tr)
    (hTrF : Tr < s.time + 1)
    (hfuture : ∀ d ∈ s.pending, s.time + 1 ≤ d.due) :
    Nonempty (PortFastCompletion θ route s p) := by
  let F := s.time
  have hTeTr : Te < Tr := by
    rw [hTr]
    have hd : 0 < Real.log 4 / (θ 0).le p :=
      div_pos (Real.log_pos (by norm_num)) (hb.rates_positive 0 p).2.2
    linarith
  have hother : ∀ j q, j ≠ 0 ∨ q ≠ p → s.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ p := by simpa using h
    linarith [(hrest q hq).2]
  have hclock : s.x 0 .q = Real.exp (-a * (s.time - F)) := by
    simpa only [F,sub_self,mul_zero,Real.exp_zero] using hq
  obtain ⟨silent,hsdate,hsraw⟩ := port_fast_aux_phase_exists (route := route) hb s p .silent origin Te F P (4 / 5)
    (Or.inl rfl) hError hm ha
    hao (by rw [ite_eq_left horigin.2]; exact hr)
    ho horigin.1 hother hclock hsensor
    hP (by linarith [hTrF]) (by norm_num [fastAuxFloor])
    (by rw [hTe]; norm_num [fastAuxFloor,protectedReadyRate])
    (fun d hd => by linarith [hfuture d hd])
  have hsthreshold : silent.final.x 0 (.m p) = 1 / 10 := by
    rw [silent.sensor_clock,hsdate]
    simpa [hTe,protectedReadyRate] using
      silent_full_decay_end (start := P) (ne_of_gt (hb.rates_positive 0 p).2.1)
  let se := setAux silent.final 0 p .error
  let es : Execution θ route s se := silent.execution.append
    (.cons (.jump (.error silent.final 0 p silent.aux_mode hsthreshold)) (.nil _))
  have hseother : ∀ j q, j ≠ 0 ∨ q ≠ p → se.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ p := by simpa using h
    simpa [se,setAux,hq] using silent.aux_other 0 q (Or.inr hq)
  have hTrsplit : Tr = Te + Real.log 4 / (θ 0).le p := hTr
  obtain ⟨err,hedate,heraw⟩ := port_fast_aux_phase_exists (route := route) hb se p .error origin Tr F Te (1 / 10)
    (Or.inr rfl) (by change silent.final.time < Tr; rw [hsdate]; exact hTeTr)
    silent.main_fast (by simp [se,setAux]) hseother
    (by simpa only [se,setAux,hsdate] using hsraw) silent.raw_other
    (by change origin ≤ silent.final.time; rw [hsdate]; linarith [horigin.1,hError]) silent.other_below
    silent.main_clock (by simpa only [se,setAux,hsdate,sub_self,mul_zero,Real.exp_zero,mul_one] using hsthreshold)
    (by change Te ≤ silent.final.time; rw [hsdate]) hTrF.le (by norm_num [fastAuxFloor])
    (by change Tr ≤ Te + Real.log ((1 / 10 : ℝ) / (1 / 40)) / (θ 0).le p
        norm_num
        exact hTrsplit.le)
    (fun d hd => by change d ∈ silent.final.pending at hd; rw [silent.pending] at hd; linarith [hfuture d hd])
  have hethreshold : err.final.x 0 (.m p) = 1 / 40 := by
    rw [err.sensor_clock,hedate]
    rw [hTrsplit]
    have hend := (protected_decay_schedule (by norm_num : (0 : ℝ) < 1 / 40)
      (by norm_num : (1 / 40 : ℝ) < 1 / 10) (hb.rates_positive 0 p).2.2).2.1
    norm_num at hend
    simpa only [protectedReadyRate,add_sub_cancel_left,neg_mul] using hend
  let ready := setAux err.final 0 p .ready
  let er : Execution θ route se ready := err.execution.append
    (.cons (.jump (.auxReady err.final 0 p err.aux_mode hethreshold)) (.nil _))
  have hreadyraw : ∀ j q, ready.raw j q = none := by
    intro j q
    by_cases h : j = 0 ∧ q = p
    · rcases h with ⟨hj,hq⟩
      subst j
      subst q
      change err.final.raw 0 p = none
      simpa [show ¬Tr < origin + 1 by linarith [hAfterRaw]] using heraw
    · exact err.raw_other j q (by tauto)
  have hreadyaux : ∀ j q, ready.aux j q = .ready := by
    intro j q
    by_cases h : j = 0 ∧ q = p
    · rcases h with ⟨hj,hq⟩
      subst j
      subst q
      simp [ready,setAux]
    · have hh : j ≠ 0 ∨ q ≠ p := by tauto
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hq : q ≠ p := by simpa using hh
      simpa [ready,setAux,hq] using err.aux_other 0 q (Or.inr hq)
  have hreadydate : ready.time = Tr := hedate
  have hreadym : ready.x 0 (.m p) = 1 / 40 := hethreshold
  have hqglobal (t : ℝ) : ready.x 0 .q * Real.exp (-a * (t - ready.time)) = Real.exp (-a * (t - F)) := by
    change err.final.x 0 .q * Real.exp (-a * (t - err.final.time)) = _
    rw [err.main_clock,attenuation_split]
  let flow : Flow θ ready (protectedMainEnd θ ready 0 p .fast .ready none (F + 1)) :=
    protectedMainFlow ready 0 p .fast .ready none (by rw [hreadydate]; exact hTrF)
      (Or.inl rfl) (Or.inl rfl) err.main_fast
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (hreadyaux 0 p)
      (fun j p _ => hreadyaux j p) (hreadyraw 0 p) (fun j p _ => hreadyraw j p) (by intros; contradiction)
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
  let before := protectedMainEnd θ ready 0 p .fast .ready none (F + 1)
  have hbeforeq : before.x 0 .q = 1 / 4 := by
    change ready.x 0 .q * Real.exp (-a * ((F + 1) - ready.time)) = _
    rw [hqglobal]
    norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  let final := setMain before 0 .slow
  let finish : Execution θ route ready final :=
    .cons (.flow flow) (.cons (.jump (.fastEnd before 0 err.main_fast hbeforeq)) (.nil _))
  let e := es.append (er.append finish)
  have hdel : e.deliveries = [] := by
    simp [e,es,er,finish,Execution.deliveries_append,silent.deliveries,err.deliveries,
      Execution.deliveries,Move.deliveries,Jump.deliveries]
  have hfinishEm : finish.ledger.emissions = [] := rfl
  have herEm : er.ledger.emissions = [] := by
    change (err.execution.append (.cons (.jump (.auxReady err.final 0 p err.aux_mode hethreshold)) (.nil _))).ledger.emissions = []
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
  have hfinalm : final.x 0 (.m p) = 1 / 40 := by
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
    physical := e.physical_invariant hb hf
    raw_valid := e.raw_valid hv
    emissions := hem
    deliveries := hdel
  }⟩
  intro q
  by_cases hq : q = p
  · subst q; rw [hfinalm]; constructor <;> norm_num
  · exact (e.aux_no_input_rest_band 0 q (hao 0 q (Or.inr hq))
      (hrest q hq) (ho 0 q (Or.inr hq))
      (by simp [NoArrivalAt,hdel])).1.2

end KernelR.Hybrid
