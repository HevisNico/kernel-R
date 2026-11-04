import KernelR.HybridSlowAuxLeg
import KernelR.HybridContactTransversality
import KernelR.HybridBirthFirstFastEnd

namespace KernelR.Hybrid
open Set

structure PortSlowAuxLeg (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port) (mode : AuxMode)
    (origin : Option ℝ) (T B Q S P initial : ℝ) where
  flow : Flow θ s (protectedMainEnd θ s 0 p .slow mode origin T)
  main_solution : (protectedMainEnd θ s 0 p .slow mode origin T).x 0 .q = Q * Real.exp (-B * (T - S))
  sensor_solution : (protectedMainEnd θ s 0 p .slow mode origin T).x 0 (.m p) =
    initial * Real.exp (-protectedReadyRate (θ 0) p mode * (T - P))
  other_below : ∀ j q, j ≠ 0 ∨ q ≠ p →
    (protectedMainEnd θ s 0 p .slow mode origin T).x j (.m q) < 1

theorem port_slow_aux_leg_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (mode : AuxMode) (origin : Option ℝ) (T B Q S P initial : ℝ)
    (hmode : mode = .silent ∨ mode = .error)
    (hT : s.time < T) (hmain : s.main 0 = .slow) (haux : s.aux 0 p = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw 0 p = origin) (ho : ∀ j q, j ≠ 0 ∨ q ≠ p → s.raw j q = none)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hother : ∀ j q, j ≠ 0 ∨ q ≠ p → s.x j (.m q) < 1)
    (hclock : s.x 0 .q = Q * Real.exp (-B * (s.time - S))) (hB : s.x 0 .b = B)
    (hsensor : s.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (s.time - P)))
    (hstart : P ≤ s.time) (hS : S ≤ s.time) (hfinish : T ≤ S + 41 / 30)
    (hQ : 17 / 125 ≤ Q ∧ Q ≤ 4 / 25) (hBrange : 17999 / 100000 ≤ B ∧ B ≤ 18001 / 100000)
    (hi : slowAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / slowAuxFloor mode) / protectedReadyRate (θ 0) p mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Nonempty (PortSlowAuxLeg θ s p mode origin T B Q S P initial) := by
  have hn : mode ≠ .ready := by rcases hmode with rfl | rfl <;> decide
  have hrpos : 0 < protectedReadyRate (θ 0) p mode := by
    rcases hmode with rfl | rfl
    · exact (hb.rates_positive 0 p).2.1
    · exact (hb.rates_positive 0 p).2.2
  have hfloor : 0 < slowAuxFloor mode := by rcases hmode with rfl | rfl <;> norm_num [slowAuxFloor]
  have hdecay := protected_decay_schedule hfloor hi hrpos
  have hmain_clock (t : ℝ) : s.x 0 .q * Real.exp (-B * (t - s.time)) = Q * Real.exp (-B * (t - S)) := by
    rw [hclock,mul_assoc,attenuation_split]
  have hsensor_clock (t : ℝ) : s.x 0 (.m p) * Real.exp (-protectedReadyRate (θ 0) p mode * (t - s.time)) =
      initial * Real.exp (-protectedReadyRate (θ 0) p mode * (t - P)) := by
    rw [hsensor,mul_assoc,attenuation_split]
  let flow := protectedMainFlow s 0 p .slow mode origin hT (Or.inr rfl)
    (by rcases hmode with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr rfl))
    hmain (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) haux hao hr ho hsupport
    (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) hother
    (by intro t ht
        simp only [reduceCtorEq,ite_false,protectedMainRate,hB]
        rw [hmain_clock]
        linarith [(slow_aux_charge_bounds hQ hBrange (hS.trans ht.1) (ht.2.le.trans hfinish)).1])
    (by intro t ht
        simp only [hn,ite_false]
        rw [hsensor_clock]
        exact hdecay.2.2 (t - P) (by linarith [ht.1]) (by linarith [ht.2])) hp
  refine ⟨⟨flow,?_,?_,?_⟩⟩
  · simpa [protectedMainEnd,protectedMainValues,protectedMainRate,hB] using hmain_clock T
  · simpa [protectedMainEnd,protectedMainValues,hn] using hsensor_clock T
  · intro j q h
    have hne : ¬(j = 0 ∧ q = p) := by tauto
    simpa [protectedMainEnd,protectedMainValues,hne] using
      relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hother j q h) (by norm_num : (1 / 40 : ℝ) < 1)


/-- An event-free main SLOW segment, including optional RAW expiry. The two
scalar clocks are global so they survive every legal cut. -/
structure PortSlowAuxTrace (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) (p : Port)
    (mode : AuxMode) (B Q S P initial : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  main_slow : final.main 0 = .slow
  aux_mode : final.aux 0 p = mode
  aux_other : ∀ j q, j ≠ 0 ∨ q ≠ p → final.aux j q = .ready
  main_clock : final.x 0 .q = Q * Real.exp (-B * (final.time - S))
  sensor_clock : final.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (final.time - P))
  other_below : ∀ j q, j ≠ 0 ∨ q ≠ p → final.x j (.m q) < 1
  raw_other : ∀ j q, j ≠ 0 ∨ q ≠ p → final.raw j q = none
  pending : final.pending = s.pending
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []

noncomputable def PortSlowAuxTrace.ofLeg {θ route s p mode origin T B Q S P initial}
    (leg : PortSlowAuxLeg θ s p mode origin T B Q S P initial)
    (hm : s.main 0 = .slow) (ha : s.aux 0 p = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ p → s.aux j q = .ready)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ p → s.raw j q = none) :
    PortSlowAuxTrace θ route s p mode B Q S P initial where
  final := protectedMainEnd θ s 0 p .slow mode origin T
  execution := .cons (.flow leg.flow) (.nil _)
  contacts_transversal := trivial
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

noncomputable def PortSlowAuxTrace.expire {θ route s p mode B Q S P initial}
    (r : PortSlowAuxTrace θ route s p mode B Q S P initial) (origin : ℝ)
    (hr : r.final.raw 0 p = some origin) (ht : r.final.time = origin + 1) :
    PortSlowAuxTrace θ route s p mode B Q S P initial where
  final := setRaw r.final 0 p none
  execution := r.execution.append (rawExpiryExecution r.final 0 p origin hr ht)
  contacts_transversal := by
    simp [Execution.ContactsTransversal, Jump.ContactTransversal, rawExpiryExecution,
      rawExpiryJump, r.contacts_transversal]
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

noncomputable def PortSlowAuxTrace.append {θ route s p mode B Q S P initial}
    (r : PortSlowAuxTrace θ route s p mode B Q S P initial)
    (v : PortSlowAuxTrace θ route r.final p mode B Q S P initial) :
    PortSlowAuxTrace θ route s p mode B Q S P initial where
  final := v.final
  execution := r.execution.append v.execution
  contacts_transversal := by simpa using And.intro r.contacts_transversal v.contacts_transversal
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
theorem port_slow_aux_phase_exists {θ ε route} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (mode : AuxMode) (origin T B Q S P initial : ℝ)
    (hmode : mode = .silent ∨ mode = .error)
    (hT : s.time < T) (hm : s.main 0 = .slow) (ha : s.aux 0 p = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw 0 p = if s.time < origin + 1 then some origin else none)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ p → s.raw j q = none)
    (horigin : origin ≤ s.time)
    (hx : ∀ j q, j ≠ 0 ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : s.x 0 .q = Q * Real.exp (-B * (s.time - S))) (hB : s.x 0 .b = B)
    (hs : s.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (s.time - P)))
    (hP : P ≤ s.time) (hS : S ≤ s.time) (hF : T ≤ S + 41 / 30)
    (hQ : 17 / 125 ≤ Q ∧ Q ≤ 4 / 25) (hBrange : 17999 / 100000 ≤ B ∧ B ≤ 18001 / 100000) (hi : slowAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / slowAuxFloor mode) / protectedReadyRate (θ 0) p mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    ∃ r : PortSlowAuxTrace θ route s p mode B Q S P initial,
      r.final.time = T ∧ r.final.raw 0 p = if T < origin + 1 then some origin else none := by
  by_cases hstart : s.time < origin + 1
  · rw [ite_eq_left hstart] at hr
    by_cases hend : T < origin + 1
    · obtain ⟨leg⟩ := port_slow_aux_leg_exists hb s p mode (some origin) T B Q S P initial hmode hT hm ha hao hr ho
        (by intro o he; cases Option.some.inj he; exact ⟨horigin,hend.le⟩) hx hq hB hs hP hS hF hQ hBrange hi hphase hp
      exact ⟨.ofLeg leg hm ha hao ho,rfl,by simpa [PortSlowAuxTrace.ofLeg,protectedMainEnd,hend] using hr⟩
    · obtain ⟨leg⟩ := port_slow_aux_leg_exists hb s p mode (some origin) (origin + 1) B Q S P initial hmode hstart hm ha hao hr ho
        (by intro o he; cases Option.some.inj he; exact ⟨horigin,le_rfl⟩) hx hq hB hs hP hS
        (by linarith) hQ hBrange hi (by linarith) (fun d hd => by linarith [hp d hd])
      let firstLeg :=  PortSlowAuxTrace.ofLeg (route := route) leg hm ha hao ho
      let expired := firstLeg.expire origin hr rfl
      have he : expired.final.time = origin + 1 := rfl
      have hraw : expired.final.raw 0 p = none := by simp [expired,PortSlowAuxTrace.expire,setRaw]
      by_cases heq : T = origin + 1
      · exact ⟨expired,by simpa [heq] using he,by simpa [hend] using hraw⟩
      · have hnext : expired.final.time < T := by rw [he]; exact lt_of_le_of_ne (le_of_not_gt hend) (Ne.symm heq)
        obtain ⟨last⟩ := port_slow_aux_leg_exists hb expired.final p mode none T B Q S P initial hmode hnext
          expired.main_slow expired.aux_mode expired.aux_other hraw expired.raw_other (by intros; contradiction)
          expired.other_below expired.main_clock (by rw [expired.recovery]; exact hB) expired.sensor_clock (by rw [he]; linarith) (by rw [he]; linarith) hF hQ hBrange hi hphase
          (fun d hd => by rw [expired.pending] at hd; exact hp d hd)
        let suffix := PortSlowAuxTrace.ofLeg (route := route) last expired.main_slow expired.aux_mode expired.aux_other expired.raw_other
        exact ⟨expired.append suffix,rfl,by simpa [PortSlowAuxTrace.append,suffix,PortSlowAuxTrace.ofLeg,protectedMainEnd,hend] using hraw⟩
  · rw [ite_eq_right hstart] at hr
    obtain ⟨leg⟩ := port_slow_aux_leg_exists hb s p mode none T B Q S P initial hmode hT hm ha hao hr ho
      (by intros; contradiction) hx hq hB hs hP hS hF hQ hBrange hi hphase hp
    refine ⟨.ofLeg leg hm ha hao ho,rfl,?_⟩
    have hend : ¬T < origin + 1 := by linarith
    simpa [PortSlowAuxTrace.ofLeg,protectedMainEnd,hend] using hr

structure PortProtectedAuxReturn (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) (p : Port) (origin : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  time_bounds : origin + 111 / 100 < final.time ∧ final.time < origin + 17 / 12
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
endpoint. Main charge keeps its actual residual, and RAW expires at its actual source-relative date. -/
theorem port_protected_aux_return_exists {θ ε route} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port) (origin : ℝ)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (htime : origin + 1 / 100 < s.time ∧ s.time < origin + 1 / 20)
    (hm : s.main 0 = .slow) (ha : s.aux 0 p = .silent) (hsensor : s.x 0 (.m p) = 4 / 5)
    (hq : 17 / 125 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hB : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (hao : ∀ q, q ≠ p → s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some origin) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, origin + 31 / 4 ≤ d.due) :
    Nonempty (PortProtectedAuxReturn θ route s p origin) := by
  let Te := s.time + Real.log 8 / (θ 0).ls p
  let Tr := Te + Real.log 4 / (θ 0).le p
  have hpositive := hb.aux_durations_positive 0 p
  have hlower := hb.aux_durations_lower 0 p
  have hdur : Real.log 8 / (θ 0).ls p + Real.log 4 / (θ 0).le p ≤ 41 / 30 := by
    have h := hb.aux_cycle_duration_upper 0 p
    dsimp [auxCycleDuration] at h
    linarith [hpositive.1]
  have hTr : origin + 111 / 100 < Tr ∧ Tr < origin + 17 / 12 := by
    constructor <;> dsimp [Tr,Te] <;> linarith [htime.1,htime.2,hlower.2.1,hlower.2.2,hdur]
  have hfuture : ∀ d ∈ s.pending, Tr ≤ d.due := by intro d hd; linarith [hp d hd,hTr.2]
  have hauxOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (hao q (by simpa using h)).1
  have hrawOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho q (by simpa using h)
  have hother : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    linarith [(hao q (by simpa using h)).2.2]
  obtain ⟨silent,hsdate,hsraw⟩ := port_slow_aux_phase_exists (route := route) hb s p .silent origin Te
    (s.x 0 .b) (s.x 0 .q) s.time s.time (4 / 5) (Or.inl rfl)
    (by dsimp [Te]; linarith [hpositive.2.1]) hm ha hauxOther
    (by rw [ite_eq_left (show s.time < origin + 1 by linarith [htime.2])]; exact hr)
    hrawOther (by linarith [htime.1]) hother (by simp) rfl (by simpa using hsensor)
    le_rfl le_rfl (by dsimp [Te]; linarith [hpositive.2.2]) hq hB (by norm_num [slowAuxFloor])
    (by dsimp [Te,slowAuxFloor,protectedReadyRate]; norm_num)
    (fun d hd => by dsimp [Tr] at hfuture; linarith [hfuture d hd,hpositive.2.2])
  have hsthreshold : silent.final.x 0 (.m p) = 1 / 10 := by
    rw [silent.sensor_clock,hsdate]
    simpa [Te,protectedReadyRate] using silent_full_decay_end (start := s.time) (ne_of_gt (hb.rates_positive 0 p).2.1)
  let se := setAux silent.final 0 p .error
  let es : Execution θ route s se := silent.execution.append
    (.cons (.jump (.error silent.final 0 p silent.aux_mode hsthreshold)) (.nil _))
  have hseOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → se.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ p := by simpa using h
    simpa [se,setAux,hq] using silent.aux_other 0 q (Or.inr hq)
  obtain ⟨err,hedate,heraw⟩ := port_slow_aux_phase_exists (route := route) hb se p .error origin Tr
    (s.x 0 .b) (s.x 0 .q) s.time Te (1 / 10) (Or.inr rfl)
    (by change silent.final.time < Tr; rw [hsdate]; dsimp [Tr]; linarith [hpositive.2.2])
    silent.main_slow (by simp [se,setAux]) hseOther
    (by simpa only [se,setAux,hsdate] using hsraw) silent.raw_other
    (by change origin ≤ silent.final.time; rw [hsdate]; dsimp [Te]; linarith [htime.1,hpositive.2.1])
    silent.other_below silent.main_clock (silent.recovery 0)
    (by simpa only [se,setAux,hsdate,sub_self,mul_zero,Real.exp_zero,mul_one] using hsthreshold)
    (by change Te ≤ silent.final.time; rw [hsdate])
    (by change s.time ≤ silent.final.time; rw [hsdate]; dsimp [Te]; linarith [hpositive.2.1])
    (by dsimp [Tr,Te]; linarith) hq hB (by norm_num [slowAuxFloor])
    (by dsimp [Tr,slowAuxFloor,protectedReadyRate]; norm_num)
    (fun d hd => by change d ∈ silent.final.pending at hd; rw [silent.pending] at hd; exact hfuture d hd)
  have hethreshold : err.final.x 0 (.m p) = 1 / 40 := by
    rw [err.sensor_clock,hedate]
    have hend := (protected_decay_schedule (by norm_num : (0 : ℝ) < 1 / 40)
      (by norm_num : (1 / 40 : ℝ) < 1 / 10) (hb.rates_positive 0 p).2.2).2.1
    norm_num at hend
    simpa only [Tr,protectedReadyRate,add_sub_cancel_left,neg_mul] using hend
  let final := setAux err.final 0 p .ready
  let e := es.append (err.execution.append
    (.cons (.jump (.auxReady err.final 0 p err.aux_mode hethreshold)) (.nil _)))
  have hfinalReady : ∀ j q, final.aux j q = .ready := by
    intro j q
    by_cases h : j = 0 ∧ q = p
    · rcases h with ⟨rfl,rfl⟩; simp [final,setAux]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hq : q ≠ p := by simpa using h
      simpa [final,setAux,hq] using err.aux_other 0 q (Or.inr hq)
  have hfinalRaw : ∀ j q, final.raw j q = none := by
    intro j q
    by_cases h : j = 0 ∧ q = p
    · rcases h with ⟨hj,hq⟩
      subst j
      subst q
      change err.final.raw 0 p = none
      simpa [show ¬Tr < origin + 1 by linarith [hTr.1]] using heraw
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
      simp [e, es, Execution.ContactsTransversal, Jump.ContactTransversal,
        silent.contacts_transversal, err.contacts_transversal]
    time_bounds := by change origin + 111 / 100 < err.final.time ∧ err.final.time < origin + 17 / 12; rw [hedate]; exact hTr
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
    by_cases hq : q = p
    · subst q; change RestBand (err.final.x 0 (.m p)); rw [hethreshold]; constructor <;> norm_num
    · have hno : NoArrivalAt e 0 q := by simp [NoArrivalAt,hdel]
      exact (e.aux_no_input_rest_band 0 q (hao q hq).1 (hao q hq).2 (ho q hq) hno).1.2
  · rw [hclock]
    dsimp only [final,setAux]
    have h := slow_aux_charge_bounds (S := s.time) (t := err.final.time) hq hB (by rw [hedate]; dsimp [Tr,Te]; linarith [hpositive.2.1,hpositive.2.2])
      (by rw [hedate]; dsimp [Tr,Te]; linarith)
    exact ⟨by linarith [h.1],h.2⟩


end KernelR.Hybrid
