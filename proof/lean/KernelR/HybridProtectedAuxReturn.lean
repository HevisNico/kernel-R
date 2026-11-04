import KernelR.HybridSlowAuxLeg
import KernelR.HybridBirthFirstFastEnd

namespace KernelR.Hybrid
open Set

/-- An event-free main SLOW segment, including optional RAW expiry. The two
scalar clocks are global so they survive every legal cut. -/
structure SlowAuxTrace (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1)
    (mode : AuxMode) (B Q S P initial : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  main_slow : final.main 0 = .slow
  aux_mode : final.aux 0 0 = mode
  aux_other : ∀ j q, j ≠ 0 ∨ q ≠ 0 → final.aux j q = .ready
  main_clock : final.x 0 .q = Q * Real.exp (-B * (final.time - S))
  sensor_clock : final.x 0 (.m 0) = initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (final.time - P))
  other_below : ∀ j q, j ≠ 0 ∨ q ≠ 0 → final.x j (.m q) < 1
  raw_other : ∀ j q, j ≠ 0 ∨ q ≠ 0 → final.raw j q = none
  pending : final.pending = s.pending
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []

noncomputable def SlowAuxTrace.ofLeg {θ route s mode origin T B Q S P initial}
    (leg : SlowAuxLeg θ s mode origin T B Q S P initial)
    (hm : s.main 0 = .slow) (ha : s.aux 0 0 = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.aux j q = .ready)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.raw j q = none) :
    SlowAuxTrace θ route s mode B Q S P initial where
  final := protectedMainEnd θ s 0 0 .slow mode origin T
  execution := .cons (.flow leg.flow) (.nil _)
  contacts_transversal := by trivial
  main_slow := hm
  aux_mode := ha
  aux_other := hao
  main_clock := leg.main_solution
  sensor_clock := leg.sensor_solution
  other_below := leg.other_below
  raw_other := ho
  pending := rfl
  gains := fun _ _ => rfl
  recovery := fun _ => rfl
  emissions := rfl
  deliveries := rfl

noncomputable def SlowAuxTrace.expire {θ route s mode B Q S P initial}
    (r : SlowAuxTrace θ route s mode B Q S P initial) (origin : ℝ)
    (hr : r.final.raw 0 0 = some origin) (ht : r.final.time = origin + 1) :
    SlowAuxTrace θ route s mode B Q S P initial where
  final := setRaw r.final 0 0 none
  execution := r.execution.append (rawExpiryExecution r.final 0 0 origin hr ht)
  contacts_transversal := by
    simpa [rawExpiryExecution, rawExpiryJump, Execution.ContactsTransversal,
      Jump.ContactTransversal] using r.contacts_transversal
  main_slow := r.main_slow
  aux_mode := r.aux_mode
  aux_other := r.aux_other
  main_clock := r.main_clock
  sensor_clock := r.sensor_clock
  other_below := r.other_below
  raw_other := by intro j q h; rw [raw_update_other _ _ _ _ _ _ h]; exact r.raw_other j q h
  pending := r.pending
  gains := r.gains
  recovery := r.recovery
  emissions := by simp [Execution.emissions_append,r.emissions,rawExpiryExecution,rawExpiryJump,Execution.ledger,Move.ledger,Jump.ledger,Ledger.add,Ledger.zero]
  deliveries := by simp [Execution.deliveries_append,r.deliveries,rawExpiryExecution,rawExpiryJump,Execution.deliveries,Move.deliveries,Jump.deliveries]

noncomputable def SlowAuxTrace.append {θ route s mode B Q S P initial}
    (r : SlowAuxTrace θ route s mode B Q S P initial)
    (v : SlowAuxTrace θ route r.final mode B Q S P initial) :
    SlowAuxTrace θ route s mode B Q S P initial where
  final := v.final
  execution := r.execution.append v.execution
  contacts_transversal := by
    simpa using And.intro r.contacts_transversal v.contacts_transversal
  main_slow := v.main_slow
  aux_mode := v.aux_mode
  aux_other := v.aux_other
  main_clock := v.main_clock
  sensor_clock := v.sensor_clock
  other_below := v.other_below
  raw_other := v.raw_other
  pending := v.pending.trans r.pending
  gains := fun j q => (v.gains j q).trans (r.gains j q)
  recovery := fun j => (v.recovery j).trans (r.recovery j)
  emissions := by simp [Execution.emissions_append,r.emissions,v.emissions]
  deliveries := by simp [Execution.deliveries_append,r.deliveries,v.deliveries]

/-- A complete protected auxiliary decay while the main cell is SLOW. RAW
expiry is taken at its actual date; the endpoint consumes expiry at equality. -/
theorem slow_aux_phase_exists {θ ε route} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (mode : AuxMode) (origin T B Q S P initial : ℝ)
    (hmode : mode = .silent ∨ mode = .error)
    (hT : s.time < T) (hm : s.main 0 = .slow) (ha : s.aux 0 0 = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.aux j q = .ready)
    (hr : s.raw 0 0 = if s.time < origin + 1 then some origin else none)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.raw j q = none)
    (horigin : origin ≤ s.time)
    (hx : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.x j (.m q) < 1)
    (hq : s.x 0 .q = Q * Real.exp (-B * (s.time - S))) (hB : s.x 0 .b = B)
    (hs : s.x 0 (.m 0) = initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (s.time - P)))
    (hP : P ≤ s.time) (hS : S ≤ s.time) (hF : T ≤ S + 41 / 30)
    (hQ : 17 / 125 ≤ Q ∧ Q ≤ 4 / 25) (hBrange : 17999 / 100000 ≤ B ∧ B ≤ 18001 / 100000) (hi : slowAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / slowAuxFloor mode) / protectedReadyRate (θ 0) 0 mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    ∃ r : SlowAuxTrace θ route s mode B Q S P initial,
      r.final.time = T ∧ r.final.raw 0 0 = if T < origin + 1 then some origin else none := by
  by_cases hstart : s.time < origin + 1
  · rw [ite_eq_left hstart] at hr
    by_cases hend : T < origin + 1
    · obtain ⟨leg⟩ := slow_aux_leg_exists hb s mode (some origin) T B Q S P initial hmode hT hm ha hao hr ho
        (by intro o he; cases Option.some.inj he; exact ⟨horigin,hend.le⟩) hx hq hB hs hP hS hF hQ hBrange hi hphase hp
      exact ⟨.ofLeg leg hm ha hao ho,rfl,by simpa [SlowAuxTrace.ofLeg,protectedMainEnd,hend] using hr⟩
    · obtain ⟨leg⟩ := slow_aux_leg_exists hb s mode (some origin) (origin + 1) B Q S P initial hmode hstart hm ha hao hr ho
        (by intro o he; cases Option.some.inj he; exact ⟨horigin,le_rfl⟩) hx hq hB hs hP hS
        (by linarith) hQ hBrange hi (by linarith) (fun d hd => by linarith [hp d hd])
      let firstLeg :=  SlowAuxTrace.ofLeg (route := route) leg hm ha hao ho
      let expired := firstLeg.expire origin hr rfl
      have he : expired.final.time = origin + 1 := rfl
      have hraw : expired.final.raw 0 0 = none := by simp [expired,SlowAuxTrace.expire,setRaw]
      by_cases heq : T = origin + 1
      · exact ⟨expired,by simpa [heq] using he,by simpa [hend] using hraw⟩
      · have hnext : expired.final.time < T := by rw [he]; exact lt_of_le_of_ne (le_of_not_gt hend) (Ne.symm heq)
        obtain ⟨last⟩ := slow_aux_leg_exists hb expired.final mode none T B Q S P initial hmode hnext
          expired.main_slow expired.aux_mode expired.aux_other hraw expired.raw_other (by intros; contradiction)
          expired.other_below expired.main_clock (by rw [expired.recovery]; exact hB) expired.sensor_clock (by rw [he]; linarith) (by rw [he]; linarith) hF hQ hBrange hi hphase
          (fun d hd => by rw [expired.pending] at hd; exact hp d hd)
        let suffix := SlowAuxTrace.ofLeg (route := route) last expired.main_slow expired.aux_mode expired.aux_other expired.raw_other
        exact ⟨expired.append suffix,rfl,by simpa [SlowAuxTrace.append,suffix,SlowAuxTrace.ofLeg,protectedMainEnd,hend] using hraw⟩
  · rw [ite_eq_right hstart] at hr
    obtain ⟨leg⟩ := slow_aux_leg_exists hb s mode none T B Q S P initial hmode hT hm ha hao hr ho
      (by intros; contradiction) hx hq hB hs hP hS hF hQ hBrange hi hphase hp
    refine ⟨.ofLeg leg hm ha hao ho,rfl,?_⟩
    have hend : ¬T < origin + 1 := by linarith
    simpa [SlowAuxTrace.ofLeg,protectedMainEnd,hend] using hr

structure ProtectedAuxReturn (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) (p : Port) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  time_bounds : 3311 / 100 < final.time ∧ final.time < 401 / 12
  main_slow : final.main 0 = .slow
  auxiliary : ∀ j q, final.aux j q = .ready
  rest : ∀ q, RestBand (final.x 0 (.m q))
  raw_none : ∀ j q, final.raw j q = none
  charge : 1 / 10 < final.x 0 .q ∧ final.x 0 .q ≤ 4 / 25
  charge_clock : final.x 0 .q = s.x 0 .q * Real.exp (-s.x 0 .b * (final.time - s.time))
  sensor_charge : final.x 0 (.m p) = 1 / 40
  recovery : ∀ j, final.x j .b = s.x j .b
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  pending : final.pending = s.pending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- Construct the genuine remaining auxiliary cycle from the protected MARK
endpoint. Main charge keeps its actual residual, and raw33 is consumed. -/
theorem protected_aux_return_exists {θ ε route} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (htime : 3201 / 100 < s.time ∧ s.time < 641 / 20)
    (hm : s.main 0 = .slow) (ha : s.aux 0 0 = .silent) (hsensor : s.x 0 (.m 0) = 4 / 5)
    (hq : 17 / 125 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hB : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (hao : ∀ q, q ≠ 0 → s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 0 = some 32) (ho : ∀ q, q ≠ 0 → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, (40 : ℝ) ≤ d.due) :
    Nonempty (ProtectedAuxReturn θ route s 0) := by
  let Te := s.time + Real.log 8 / (θ 0).ls 0
  let Tr := Te + Real.log 4 / (θ 0).le 0
  have hpositive := hb.aux_durations_positive 0 0
  have hlower := hb.aux_durations_lower 0 0
  have hdur : Real.log 8 / (θ 0).ls 0 + Real.log 4 / (θ 0).le 0 ≤ 41 / 30 := by
    have h := hb.aux_cycle_duration_upper 0 0
    dsimp [auxCycleDuration] at h
    linarith [hpositive.1]
  have hTr : 3311 / 100 < Tr ∧ Tr < 401 / 12 := by
    constructor <;> dsimp [Tr,Te] <;> linarith [htime.1,htime.2,hlower.2.1,hlower.2.2,hdur]
  have hfuture : ∀ d ∈ s.pending, Tr ≤ d.due := by intro d hd; linarith [hp d hd,hTr.2]
  have hauxOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ 0 → s.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (hao q (by simpa using h)).1
  have hrawOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ 0 → s.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho q (by simpa using h)
  have hother : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ 0 → s.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    linarith [(hao q (by simpa using h)).2.2]
  obtain ⟨silent,hsdate,hsraw⟩ := slow_aux_phase_exists (route := route) hb s .silent 32 Te
    (s.x 0 .b) (s.x 0 .q) s.time s.time (4 / 5) (Or.inl rfl)
    (by dsimp [Te]; linarith [hpositive.2.1]) hm ha hauxOther
    (by rw [ite_eq_left (show s.time < (32 : ℝ) + 1 by linarith [htime.2])]; exact hr)
    hrawOther (by linarith [htime.1]) hother (by simp) rfl (by simpa using hsensor)
    le_rfl le_rfl (by dsimp [Te]; linarith [hpositive.2.2]) hq hB (by norm_num [slowAuxFloor])
    (by dsimp [Te,slowAuxFloor,protectedReadyRate]; norm_num)
    (fun d hd => by dsimp [Tr] at hfuture; linarith [hfuture d hd,hpositive.2.2])
  have hsthreshold : silent.final.x 0 (.m 0) = 1 / 10 := by
    rw [silent.sensor_clock,hsdate]
    simpa [Te,protectedReadyRate] using silent_full_decay_end (start := s.time) (ne_of_gt (hb.rates_positive 0 0).2.1)
  let se := setAux silent.final 0 0 .error
  let es : Execution θ route s se := silent.execution.append
    (.cons (.jump (.error silent.final 0 0 silent.aux_mode hsthreshold)) (.nil _))
  have hseOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ 0 → se.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ 0 := by simpa using h
    simpa [se,setAux,hq] using silent.aux_other 0 q (Or.inr hq)
  obtain ⟨err,hedate,heraw⟩ := slow_aux_phase_exists (route := route) hb se .error 32 Tr
    (s.x 0 .b) (s.x 0 .q) s.time Te (1 / 10) (Or.inr rfl)
    (by change silent.final.time < Tr; rw [hsdate]; dsimp [Tr]; linarith [hpositive.2.2])
    silent.main_slow (by simp [se,setAux]) hseOther
    (by simpa only [se,setAux,hsdate] using hsraw) silent.raw_other
    (by change (32 : ℝ) ≤ silent.final.time; rw [hsdate]; dsimp [Te]; linarith [htime.1,hpositive.2.1])
    silent.other_below silent.main_clock (silent.recovery 0)
    (by simpa only [se,setAux,hsdate,sub_self,mul_zero,Real.exp_zero,mul_one] using hsthreshold)
    (by change Te ≤ silent.final.time; rw [hsdate])
    (by change s.time ≤ silent.final.time; rw [hsdate]; dsimp [Te]; linarith [hpositive.2.1])
    (by dsimp [Tr,Te]; linarith) hq hB (by norm_num [slowAuxFloor])
    (by dsimp [Tr,slowAuxFloor,protectedReadyRate]; norm_num)
    (fun d hd => by change d ∈ silent.final.pending at hd; rw [silent.pending] at hd; exact hfuture d hd)
  have hethreshold : err.final.x 0 (.m 0) = 1 / 40 := by
    rw [err.sensor_clock,hedate]
    have hend := (protected_decay_schedule (by norm_num : (0 : ℝ) < 1 / 40)
      (by norm_num : (1 / 40 : ℝ) < 1 / 10) (hb.rates_positive 0 0).2.2).2.1
    norm_num at hend
    simpa only [Tr,protectedReadyRate,add_sub_cancel_left,neg_mul] using hend
  let final := setAux err.final 0 0 .ready
  let e := es.append (err.execution.append
    (.cons (.jump (.auxReady err.final 0 0 err.aux_mode hethreshold)) (.nil _)))
  have hfinalReady : ∀ j q, final.aux j q = .ready := by
    intro j q
    by_cases h : j = 0 ∧ q = 0
    · rcases h with ⟨rfl,rfl⟩; simp [final,setAux]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hq : q ≠ 0 := by simpa using h
      simpa [final,setAux,hq] using err.aux_other 0 q (Or.inr hq)
  have hfinalRaw : ∀ j q, final.raw j q = none := by
    intro j q
    by_cases h : j = 0 ∧ q = 0
    · rcases h with ⟨rfl,rfl⟩
      change err.final.raw 0 0 = none
      simpa [show ¬Tr < (32 : ℝ) + 1 by linarith [hTr.1]] using heraw
    · exact err.raw_other j q (by tauto)
  have hclock : final.x 0 .q = s.x 0 .q * Real.exp (-s.x 0 .b * (final.time - s.time)) := err.main_clock
  have hdel : e.deliveries = [] := by
    simp [e,es,Execution.deliveries_append,silent.deliveries,err.deliveries,Execution.deliveries,Move.deliveries,Jump.deliveries]
  have hem : e.ledger.emissions = [] := by
    simp [e,es,Execution.emissions_append,silent.emissions,err.emissions,Execution.ledger,Move.ledger,Jump.ledger,Ledger.add,Ledger.zero]
  refine ⟨{
    final := final
    execution := e
    contacts_transversal := by
      simpa [e, es, Execution.ContactsTransversal, Jump.ContactTransversal]
        using And.intro silent.contacts_transversal err.contacts_transversal
    time_bounds := by change 3311 / 100 < err.final.time ∧ err.final.time < 401 / 12; rw [hedate]; exact hTr
    main_slow := err.main_slow
    auxiliary := hfinalReady
    rest := ?_
    raw_none := hfinalRaw
    charge := ?_
    charge_clock := hclock
    sensor_charge := hethreshold
    recovery := fun j => (err.recovery j).trans (silent.recovery j)
    gains := fun j q => (err.gains j q).trans (silent.gains j q)
    pending := err.pending.trans silent.pending
    emissions := hem
    deliveries := hdel
    physical := e.physical_invariant hb hf
    raw_valid := e.raw_valid hv
  }⟩
  · intro q
    by_cases hq : q = 0
    · subst q; change RestBand (err.final.x 0 (.m 0)); rw [hethreshold]; constructor <;> norm_num
    · have hno : NoArrivalAt e 0 q := by simp [NoArrivalAt,hdel]
      exact (e.aux_no_input_rest_band 0 q (hao q hq).1 (hao q hq).2 (ho q hq) hno).1.2
  · rw [hclock]
    dsimp only [final,setAux]
    have h := slow_aux_charge_bounds (S := s.time) (t := err.final.time) hq hB (by rw [hedate]; dsimp [Tr,Te]; linarith [hpositive.2.1,hpositive.2.2])
      (by rw [hedate]; dsimp [Tr,Te]; linarith)
    exact ⟨by linarith [h.1],h.2⟩

end KernelR.Hybrid
