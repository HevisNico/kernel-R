import KernelR.HybridContactTransversality
import KernelR.HybridCadenceMarkOnly
import KernelR.HybridProtectedInputCycle

/-! A SLOW period-four input constructs its own protected MARK, expires RAW,
finishes ERROR while still SLOW, and returns at its actual logarithmic root.
All charge, recovery and energy clocks are carried through the handoffs. -/
namespace KernelR.Hybrid
open Set

private theorem cadence_mark_initial_charge {q b start t : ℝ}
    (hq : 37 / 250 ≤ q ∧ q ≤ 1 / 4)
    (hb : 17999 / 100000 ≤ b ∧ b ≤ 18001 / 100000)
    (ht : start ≤ t) (hu : t ≤ start + 1 / 40) :
    147 / 1000 ≤ q * Real.exp (-b * (t - start)) ∧
      q * Real.exp (-b * (t - start)) ≤ 1 / 4 := by
  have hd : 0 ≤ t-start := by linarith
  have hprod : b*(t-start)≤(18001/100000:ℝ)*(1/40) :=
    mul_le_mul hb.2 (by linarith) hd (by norm_num)
  have he := Real.add_one_le_exp (-b*(t-start))
  have hp := mul_le_mul_of_nonneg_right hq.1 (Real.exp_pos (-b*(t-start))).le
  have hu' := mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (show -b*(t-start)≤0 by nlinarith [hb.1]))
    (show 0≤q by linarith [hq.1])
  constructor <;> nlinarith [hb.1,hb.2,hq.2]

private theorem cadence_mark_final_charge {θ ε} (hb : @PhysicalBox 1 θ ε)
    (s : Snapshot 1) (p : Port) (hm : s.x 0 (.m p)=1)
    (hq : 147/1000≤s.x 0 .q ∧ s.x 0 .q≤1/4)
    (hbown : 17999/100000≤s.x 0 .b ∧ s.x 0 .b≤18001/100000)
    {t : ℝ} (ht : s.time≤t) (hend : t≤s.time+slowMarkDuration θ s 0 p) :
    18/125≤slowMarkMain θ s 0 p t ∧ slowMarkMain θ s 0 p t≤1/4 := by
  have hr := (hb.rates_positive 0 p).1
  have hd : 0≤t-s.time := by linarith
  have htime : t-s.time≤1/45 := by
    have h := slowMarkDuration_upper hb s 0 p (by rw [hm]; norm_num) hm.le
    linarith
  have he := Real.exp_le_one_iff.mpr (show -(θ 0).lm p*(t-s.time)≤0 by nlinarith)
  have hquotNon : 0≤(1-Real.exp (-(θ 0).lm p*(t-s.time)))/(θ 0).lm p :=
    div_nonneg (sub_nonneg.mpr he) hr.le
  have hquotUpper : (1-Real.exp (-(θ 0).lm p*(t-s.time)))/(θ 0).lm p≤t-s.time := by
    apply (div_le_iff₀ hr).mpr
    nlinarith [Real.add_one_le_exp (-(θ 0).lm p*(t-s.time))]
  have hIpos : 0≤slowMarkIntegral θ s 0 p t := by
    dsimp only [slowMarkIntegral]; rw [hm]; nlinarith [hbown.1]
  have hIupper : slowMarkIntegral θ s 0 p t≤(68001/100000:ℝ)*(1/45) := by
    dsimp only [slowMarkIntegral]; rw [hm]; nlinarith [hbown.2]
  have hmul := mul_le_mul_of_nonneg_right hq.1 (Real.exp_pos (-slowMarkIntegral θ s 0 p t)).le
  have hu := mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hIpos)) (show 0≤s.x 0 .q by linarith [hq.1])
  dsimp only [slowMarkMain]
  constructor <;> nlinarith [hq.2,Real.add_one_le_exp (-slowMarkIntegral θ s 0 p t)]

structure CadenceMarkPrefix (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) (p : Port) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  main_flows : execution.MainFlows 0 .slow
  early : s.time+1/100<final.time
  deadline : final.time<s.time+1/20
  sensor_budget : final.time-s.time+Real.log 8/(θ 0).ls p+Real.log 4/(θ 0).le p<419/300
  main_slow : final.main 0=.slow
  aux_silent : final.aux 0 p=.silent
  auxiliary_other : ∀ q, q≠p → final.aux 0 q=.ready ∧ RestBand (final.x 0 (.m q))
  sensor_charge : final.x 0 (.m p)=4/5
  charge : 18/125≤final.x 0 .q ∧ final.x 0 .q≤1/4
  recovery_gain : final.x 0 .b=s.x 0 .b+1/10
  gain_preserved : ∀ q, final.x 0 (.z q)=s.x 0 (.z q)
  raw_active : final.raw 0 p=some s.time
  raw_other : ∀ q, q≠p → final.raw 0 q=none
  pending : final.pending=s.pending
  emissions : execution.ledger.emissions=[]
  deliveries : execution.deliveries=[]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

theorem cadence_mark_prefix_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 37 / 250 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 1 / 4)
    (hbown : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) : Nonempty (CadenceMarkPrefix θ route s p) := by
  obtain ⟨latency,hearly,hdeadline,hroot,hprior,hslope⟩ :=
    hb.first_sensor_crossing_transversal 0 p (ha p).2.1 (ha p).2.2
  let M := s.time + latency
  let beforeMark := protectedMainEnd θ s 0 p .slow .ready (some s.time) M
  have hM : s.time < M := by dsimp [M]; linarith
  have hmOther : ∀ j : Fin 1, j ≠ 0 → s.main j = .ready := by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))
  have haOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (ha q).1
  have hrOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho q (by simpa using h)
  have hqx : ∀ j : Fin 1, j ≠ 0 → s.x j .q < 1 := by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))
  have hmx : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    linarith [(ha q).2.2]
  have preCharge : ∀ t ∈ Icc s.time M, 147 / 1000 ≤ s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) ∧
      s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) ≤ 1 / 4 := by
    intro t ht
    exact cadence_mark_initial_charge hq hbown ht.1 (by dsimp [M] at ht; linarith [ht.2])
  let firstFlow := protectedMainFlow (θ := θ) s 0 p .slow .ready (some s.time) hM (Or.inr rfl) (Or.inl rfl)
    hm hmOther (ha p).1 haOther hr hrOther
    (by intro o he; cases Option.some.inj he; exact ⟨le_rfl,by dsimp [M]; linarith⟩)
    hqx hmx
    (by intro t ht; simp only [reduceCtorEq,ite_false,protectedMainRate]; linarith [(preCharge t ⟨ht.1,ht.2.le⟩).1])
    (by intro t ht; simpa [rawInputScale] using hprior t ht)
    (fun d hd => by dsimp [M]; linarith [hp d hd])
  have hthreshold : beforeMark.x 0 (.m p) = 1 := by
    simpa [beforeMark,protectedMainEnd,protectedMainValues,rawInputScale,M] using hroot
  let markStart := setAux beforeMark 0 p .mark
  let first : Execution θ route s markStart :=
    .cons (.flow firstFlow) (.cons (.jump (.mark _ 0 p (ha p).1 hthreshold)) (.nil _))
  have hmarkm : markStart.x 0 (.m p) = 1 := hthreshold
  have hmarkb : markStart.x 0 .b = s.x 0 .b := rfl
  have hmarkq : 147 / 1000 ≤ markStart.x 0 .q ∧ markStart.x 0 .q ≤ 1 / 4 := by
    simpa [markStart,setAux,beforeMark,protectedMainEnd,protectedMainValues,protectedMainRate] using preCharge M ⟨hM.le,le_rfl⟩
  have hmarkB : 17999 / 100000 ≤ markStart.x 0 .b ∧ markStart.x 0 .b ≤ 18001 / 100000 := by rw [hmarkb]; exact hbown
  have hmarkhead : markStart.x 0 .b + (1 / 2) * (markStart.x 0 (.m p) - 4 / 5) < 11 / 10 := by
    rw [hmarkm,hmarkb]
    linarith [hbown.2]
  let T := markStart.time + slowMarkDuration θ markStart 0 p
  have hT : markStart.time < T := by dsimp [T]; linarith [slowMarkDuration_positive hb markStart 0 p (by rw [hmarkm]; norm_num)]
  have hTupper : T < s.time + 1 / 20 := by
    have hd := slowMarkDuration_upper hb markStart 0 p (by rw [hmarkm]; norm_num) hmarkm.le
    change s.time + latency + slowMarkDuration θ markStart 0 p < s.time + 1 / 20
    linarith
  have markCharge : ∀ t ∈ Icc markStart.time T, 18 / 125 ≤ slowMarkMain θ markStart 0 p t ∧
      slowMarkMain θ markStart 0 p t ≤ 1 / 4 := by
    intro t ht
    exact cadence_mark_final_charge hb markStart p hmarkm hmarkq hmarkB ht.1 ht.2
  have hmarkmode : markStart.aux 0 p = .mark := by simp [markStart,setAux]
  have hmarkmain : markStart.main 0 = .slow := hm
  have hmOther' : ∀ j : Fin 1, j ≠ 0 → markStart.main j = .ready := by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))
  have haOther' : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → markStart.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ p := by simpa using h
    simpa [markStart,setAux,beforeMark,protectedMainEnd,hq] using (ha q).1
  have hr' : markStart.raw 0 p = some s.time := hr
  have hrOther' : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → markStart.raw j q = none := hrOther
  have hqx' : ∀ j : Fin 1, j ≠ 0 → markStart.x j .q < 1 := by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))
  have hmx' : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → markStart.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hqp : q ≠ p := by simpa using h
    have hrest := relax_lt (rate := (1 / 2 : ℝ)) (target := (1 / 40 : ℝ))
      (initial := s.x 0 (.m q)) (start := s.time) (t := M)
      (by norm_num) hM.le (hmx 0 q (Or.inr hqp)) (by norm_num : (1 / 40 : ℝ) < 1)
    simpa [markStart,setAux,beforeMark,protectedMainEnd,protectedMainValues,hqp] using hrest
  let secondFlow := slowMarkFlow hb markStart 0 p (some s.time) hT le_rfl hmarkmain hmOther' hmarkmode haOther'
    hr' hrOther' (by rw [hmarkm]; norm_num) hmarkm.le ((first.physical_invariant hb hf).reserve 0) hmarkhead
    (by intro o he; cases Option.some.inj he; exact ⟨hM.le,by linarith⟩) hqx' hmx'
    (by intro t ht; linarith [(markCharge t ⟨ht.1,ht.2.le⟩).1])
    (fun d hd => by change d ∈ s.pending at hd; linarith [hp d hd])
  let final := setAux (slowMarkEnd θ markStart 0 p T) 0 p .silent
  let e : Execution θ route s final := first.append
    (.cons (.flow secondFlow) (.cons (.jump (.silent (slowMarkEnd θ markStart 0 p T) 0 p hmarkmode
      (slowMarkEnd_sensor hb markStart 0 p (by rw [hmarkm]; norm_num)))) (.nil _)))
  have firstContacts : first.ContactsTransversal := by
    simp only [first, Execution.ContactsTransversal, Jump.ContactTransversal, and_true]
    exact firstFlow.aux_contact_field_positive 0 p (ha p).1 hr
      (by change M < s.time + 1; dsimp [M]; linarith)
      (by simpa only [protectedMainEnd, M] using hslope)
  have contacts : e.ContactsTransversal := by
    simpa [e, Jump.ContactTransversal] using firstContacts
  have hno : ∀ q, NoArrivalAt e 0 q := by simp [NoArrivalAt,e,first,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries]
  refine ⟨{
    final := final
    execution := e
    contacts_transversal := contacts
    main_flows := by
      simp only [e,first,Execution.append,Execution.MainFlows,Flow.mainIs]
      exact ⟨hm,hmarkmain,trivial⟩
    early := by change s.time + 1 / 100 < T; change s.time + 1 / 100 < s.time + latency + slowMarkDuration θ markStart 0 p; linarith [slowMarkDuration_positive hb markStart 0 p (by rw [hmarkm]; norm_num)]
    deadline := hTupper
    main_slow := hm
    aux_silent := by simp [final,setAux]
    auxiliary_other := fun q hq => (e.aux_no_input_rest_band 0 q (ha q).1 (ha q).2 (ho q hq) (hno q)).1
    sensor_charge := slowMarkEnd_sensor hb markStart 0 p (by rw [hmarkm]; norm_num)
    charge := markCharge T ⟨hT.le,le_rfl⟩
    sensor_budget := ?_
    recovery_gain := ?_
    gain_preserved := fun _ => rfl
    raw_active := hr
    raw_other := ho
    pending := rfl
    emissions := by simp [e,first,Execution.emissions_append,Execution.ledger,Move.ledger,Flow.ledger,Jump.ledger,Ledger.add,Ledger.zero]
    deliveries := by simp [e,first,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries]
    physical := e.physical_invariant hb hf
    raw_valid := e.raw_valid hv
  }⟩
  · have hd := hb.aux_cycle_duration_upper 0 p
    have hmDuration : slowMarkDuration θ markStart 0 p = Real.log (5 / 4) / (θ 0).lm p := by
      simp only [slowMarkDuration,hmarkm]
      norm_num
    change s.time + latency + slowMarkDuration θ markStart 0 p - s.time +
      Real.log 8 / (θ 0).ls p + Real.log 4 / (θ 0).le p < 419 / 300
    rw [hmDuration]
    dsimp [auxCycleDuration] at hd
    linarith
  · have h := slowMarkEnd_recovery hb markStart 0 p (by rw [hmarkm]; norm_num)
    rw [hmarkm,hmarkb] at h
    change (slowMarkEnd θ markStart 0 p (markStart.time + slowMarkDuration θ markStart 0 p)).x 0 .b = s.x 0 .b + 1 / 10
    linarith


private theorem cadence_guarded_aux_leg_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (mode : AuxMode) (origin : Option ℝ) (T B Q S P initial : ℝ)
    (hmode : mode=.silent ∨ mode=.error) (hT : s.time<T)
    (hm : s.main 0=.slow) (ha : s.aux 0 p=mode)
    (hao : ∀ j q, j≠0 ∨ q≠p → s.aux j q=.ready)
    (hr : s.raw 0 p=origin) (ho : ∀ j q, j≠0 ∨ q≠p → s.raw j q=none)
    (hsupport : ∀ o, origin=some o → o≤s.time ∧ T≤o+1)
    (hx : ∀ j q, j≠0 ∨ q≠p → s.x j (.m q)<1)
    (hq : s.x 0 .q=Q*Real.exp (-B*(s.time-S))) (hB : s.x 0 .b=B)
    (hs : s.x 0 (.m p)=initial*Real.exp (-protectedReadyRate (θ 0) p mode*(s.time-P)))
    (hP : P≤s.time) (hS : S≤s.time)
    (hguard : ∀ t, S≤t → t≤T → 1/10<Q*Real.exp (-B*(t-S)))
    (hi : slowAuxFloor mode < initial)
    (hphase : T≤P+Real.log (initial/slowAuxFloor mode)/protectedReadyRate (θ 0) p mode)
    (hp : ∀ d∈s.pending, T≤d.due) :
    Nonempty (PortSlowAuxLeg θ s p mode origin T B Q S P initial) := by
  have hn : mode≠.ready := by rcases hmode with rfl|rfl <;> decide
  have hrpos : 0<protectedReadyRate (θ 0) p mode := by
    rcases hmode with rfl|rfl
    · exact (hb.rates_positive 0 p).2.1
    · exact (hb.rates_positive 0 p).2.2
  have hfloor : 0<slowAuxFloor mode := by rcases hmode with rfl|rfl <;> norm_num [slowAuxFloor]
  have hdecay := protected_decay_schedule hfloor hi hrpos
  have hmain_clock (t : ℝ) : s.x 0 .q*Real.exp (-B*(t-s.time))=Q*Real.exp (-B*(t-S)) := by
    rw [hq,mul_assoc,attenuation_split]
  have hsensor_clock (t : ℝ) : s.x 0 (.m p)*Real.exp (-protectedReadyRate (θ 0) p mode*(t-s.time))=
      initial*Real.exp (-protectedReadyRate (θ 0) p mode*(t-P)) := by
    rw [hs,mul_assoc,attenuation_split]
  let f := protectedMainFlow s 0 p .slow mode origin hT (Or.inr rfl)
    (by rcases hmode with rfl|rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr rfl))
    hm (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) ha hao hr ho hsupport
    (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) hx
    (by intro t ht
        simp only [reduceCtorEq,ite_false,protectedMainRate,hB]
        rw [hmain_clock]
        linarith [hguard t (hS.trans ht.1) ht.2.le])
    (by intro t ht
        simp only [hn,ite_false]
        rw [hsensor_clock]
        exact hdecay.2.2 (t-P) (by linarith [ht.1]) (by linarith [ht.2])) hp
  refine ⟨⟨f,?_,?_,?_⟩⟩
  · simpa [protectedMainEnd,protectedMainValues,protectedMainRate,hB] using hmain_clock T
  · simpa [protectedMainEnd,protectedMainValues,hn] using hsensor_clock T
  · intro j q h
    have hne : ¬(j=0 ∧ q=p) := by tauto
    simpa [protectedMainEnd,protectedMainValues,hne] using
      relax_lt (by norm_num : (0:ℝ)≤1/2) hT.le (hx j q h) (by norm_num : (1/40:ℝ)<1)

private theorem cadence_guarded_aux_phase_exists {θ ε route} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (mode : AuxMode) (origin T B Q S P initial : ℝ)
    (hmode : mode=.silent ∨ mode=.error) (hT : s.time<T)
    (hm : s.main 0=.slow) (ha : s.aux 0 p=mode)
    (hao : ∀ j q, j≠0 ∨ q≠p → s.aux j q=.ready)
    (hr : s.raw 0 p=if s.time<origin+1 then some origin else none)
    (ho : ∀ j q, j≠0 ∨ q≠p → s.raw j q=none) (horigin : origin≤s.time)
    (hx : ∀ j q, j≠0 ∨ q≠p → s.x j (.m q)<1)
    (hq : s.x 0 .q=Q*Real.exp (-B*(s.time-S))) (hB : s.x 0 .b=B)
    (hs : s.x 0 (.m p)=initial*Real.exp (-protectedReadyRate (θ 0) p mode*(s.time-P)))
    (hP : P≤s.time) (hS : S≤s.time)
    (hguard : ∀ t, S≤t → t≤T → 1/10<Q*Real.exp (-B*(t-S)))
    (hi : slowAuxFloor mode < initial)
    (hphase : T≤P+Real.log (initial/slowAuxFloor mode)/protectedReadyRate (θ 0) p mode)
    (hp : ∀ d∈s.pending, T≤d.due) :
    ∃ r : PortSlowAuxTrace θ route s p mode B Q S P initial,
      r.final.time=T ∧ r.final.raw 0 p=if T<origin+1 then some origin else none := by
  by_cases hstart : s.time<origin+1
  · rw [ite_eq_left hstart] at hr
    by_cases hend : T<origin+1
    · obtain ⟨leg⟩ := cadence_guarded_aux_leg_exists hb s p mode (some origin) T B Q S P initial
        hmode hT hm ha hao hr ho (by intro o he; cases Option.some.inj he; exact ⟨horigin,hend.le⟩)
        hx hq hB hs hP hS hguard hi hphase hp
      exact ⟨.ofLeg leg hm ha hao ho,rfl,by simpa [PortSlowAuxTrace.ofLeg,protectedMainEnd,hend] using hr⟩
    · obtain ⟨leg⟩ := cadence_guarded_aux_leg_exists hb s p mode (some origin) (origin+1) B Q S P initial
        hmode hstart hm ha hao hr ho (by intro o he; cases Option.some.inj he; exact ⟨horigin,le_rfl⟩)
        hx hq hB hs hP hS (fun t h1 h2 => hguard t h1 (by linarith)) hi (by linarith)
        (fun d hd => by linarith [hp d hd])
      let first := PortSlowAuxTrace.ofLeg (route:=route) leg hm ha hao ho
      let expired := first.expire origin hr rfl
      have he : expired.final.time=origin+1 := rfl
      have hraw : expired.final.raw 0 p=none := by simp [expired,PortSlowAuxTrace.expire,setRaw]
      by_cases heq : T=origin+1
      · exact ⟨expired,by simpa [heq] using he,by simpa [hend] using hraw⟩
      · have hnext : expired.final.time<T := by rw [he]; exact lt_of_le_of_ne (le_of_not_gt hend) (Ne.symm heq)
        obtain ⟨last⟩ := cadence_guarded_aux_leg_exists hb expired.final p mode none T B Q S P initial
          hmode hnext expired.main_slow expired.aux_mode expired.aux_other hraw expired.raw_other
          (by intros; contradiction) expired.other_below expired.main_clock
          (by rw [expired.recovery]; exact hB) expired.sensor_clock
          (by rw [he]; linarith) (by rw [he]; linarith) hguard hi hphase
          (fun d hd => by rw [expired.pending] at hd; exact hp d hd)
        let suffix := PortSlowAuxTrace.ofLeg (route:=route) last expired.main_slow expired.aux_mode expired.aux_other expired.raw_other
        exact ⟨expired.append suffix,rfl,by simpa [PortSlowAuxTrace.append,suffix,PortSlowAuxTrace.ofLeg,protectedMainEnd,hend] using hraw⟩
  · rw [ite_eq_right hstart] at hr
    obtain ⟨leg⟩ := cadence_guarded_aux_leg_exists hb s p mode none T B Q S P initial
      hmode hT hm ha hao hr ho (by intros; contradiction) hx hq hB hs hP hS hguard hi hphase hp
    refine ⟨.ofLeg leg hm ha hao ho,rfl,?_⟩
    have hend : ¬T<origin+1 := by linarith
    simpa [PortSlowAuxTrace.ofLeg,protectedMainEnd,hend] using hr

structure CadenceMarkAuxReturn (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) (p : Port) (origin : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  time_bounds : origin + 111 / 100 < final.time ∧ final.time < origin + 419 / 300
  main_slow : final.main 0 = .slow
  auxiliary : ∀ j q, final.aux j q = .ready
  rest : ∀ q, RestBand (final.x 0 (.m q))
  raw_none : ∀ j q, final.raw j q = none
  charge : 1 / 10 < final.x 0 .q ∧ final.x 0 .q ≤ 1 / 4
  charge_clock : final.x 0 .q = s.x 0 .q * Real.exp (-s.x 0 .b * (final.time - s.time))
  sensor_charge : final.x 0 (.m p) = 1 / 40
  recovery : ∀ j, final.x j .b = s.x j .b
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  pending : final.pending = s.pending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

theorem cadence_mark_aux_return_exists {θ ε route} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port) (origin : ℝ)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (htime : origin + 1 / 100 < s.time ∧ s.time < origin + 1 / 20)
    (hm : s.main 0 = .slow) (ha : s.aux 0 p = .silent) (hsensor : s.x 0 (.m p) = 4 / 5)
    (hq : 1 / 10 < s.x 0 .q ∧ s.x 0 .q ≤ 1 / 4)
    (hB : 0 ≤ s.x 0 .b)
    (hbudget : s.time-origin+Real.log 8/(θ 0).ls p+Real.log 4/(θ 0).le p<419/300)
    (hguard : ∀ t, s.time≤t → t≤origin+419/300 →
      1/10<s.x 0 .q*Real.exp (-s.x 0 .b*(t-s.time)))
    (hao : ∀ q, q ≠ p → s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some origin) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, origin + 4 ≤ d.due) :
    Nonempty (CadenceMarkAuxReturn θ route s p origin) := by
  let Te := s.time + Real.log 8 / (θ 0).ls p
  let Tr := Te + Real.log 4 / (θ 0).le p
  have hpositive := hb.aux_durations_positive 0 p
  have hlower := hb.aux_durations_lower 0 p
  have hdur : Real.log 8 / (θ 0).ls p + Real.log 4 / (θ 0).le p ≤ 41 / 30 := by
    have h := hb.aux_cycle_duration_upper 0 p
    dsimp [auxCycleDuration] at h
    linarith [hpositive.1]
  have hTr : origin + 111 / 100 < Tr ∧ Tr < origin + 419 / 300 := by
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
  obtain ⟨silent,hsdate,hsraw⟩ := cadence_guarded_aux_phase_exists (route := route) hb s p .silent origin Te
    (s.x 0 .b) (s.x 0 .q) s.time s.time (4 / 5) (Or.inl rfl)
    (by dsimp [Te]; linarith [hpositive.2.1]) hm ha hauxOther
    (by rw [ite_eq_left (show s.time < origin + 1 by linarith [htime.2])]; exact hr)
    hrawOther (by linarith [htime.1]) hother (by simp) rfl (by simpa using hsensor)
    le_rfl le_rfl
    (fun t h1 h2 => hguard t h1 (by dsimp [Te] at h2; linarith [hbudget,hpositive.2.2]))
    (by norm_num [slowAuxFloor])
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
  obtain ⟨err,hedate,heraw⟩ := cadence_guarded_aux_phase_exists (route := route) hb se p .error origin Tr
    (s.x 0 .b) (s.x 0 .q) s.time Te (1 / 10) (Or.inr rfl)
    (by change silent.final.time < Tr; rw [hsdate]; dsimp [Tr]; linarith [hpositive.2.2])
    silent.main_slow (by simp [se,setAux]) hseOther
    (by simpa only [se,setAux,hsdate] using hsraw) silent.raw_other
    (by change origin ≤ silent.final.time; rw [hsdate]; dsimp [Te]; linarith [htime.1,hpositive.2.1])
    silent.other_below silent.main_clock (silent.recovery 0)
    (by simpa only [se,setAux,hsdate,sub_self,mul_zero,Real.exp_zero,mul_one] using hsthreshold)
    (by change Te ≤ silent.final.time; rw [hsdate])
    (by change s.time ≤ silent.final.time; rw [hsdate]; dsimp [Te]; linarith [hpositive.2.1])
    (fun t h1 h2 => hguard t h1 (by dsimp [Tr,Te] at h2; linarith [hbudget]))
    (by norm_num [slowAuxFloor])
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
      simp [e, es, silent.contacts_transversal, err.contacts_transversal,
        Execution.ContactsTransversal, Jump.ContactTransversal]
    time_bounds := by change origin + 111 / 100 < err.final.time ∧ err.final.time < origin + 419 / 300; rw [hedate]; exact hTr
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
    constructor
    · exact hguard _ (by change s.time≤err.final.time; rw [hedate]; dsimp [Tr,Te]; linarith [hpositive.2.1,hpositive.2.2])
        (by change err.final.time≤origin+419/300; rw [hedate]; exact hTr.2.le)
    · have ht : s.time≤final.time := e.time_monotone
      have he := Real.exp_le_one_iff.mpr (show -s.x 0 .b*(final.time-s.time)≤0 by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left he (show 0≤s.x 0 .q by linarith [hq.1]),hq.2]

private theorem cadence_mark_decay_guard {q B S t : ℝ}
    (hq : 37/250≤q) (hB : 0≤B ∧ B≤28001/100000)
    (_ht : S≤t) (hu : t≤S+419/300) : 1/10<q*Real.exp (-B*(t-S)) := by
  have hqpos : 0<q := by linarith
  have hlog : (9/23:ℝ)≤Real.log (q/(1/10)) := by
    apply mark_only_log_margin.2.trans (Real.log_le_log (by norm_num) ?_)
    linarith
  have hprod : B*(t-S)≤(28001/100000:ℝ)*(419/300) := by nlinarith [hB.1,hB.2]
  have he := Real.exp_lt_exp.mpr (show B*(t-S)<Real.log (q/(1/10)) by linarith [mark_only_log_margin.1])
  rw [Real.exp_log (by positivity : 0<q/(1/10))] at he
  have hmul := mul_lt_mul_of_pos_right he (Real.exp_pos (-B*(t-S)))
  have hc : Real.exp (B*(t-S))*Real.exp (-B*(t-S))=1 := by rw [←Real.exp_add]; simp
  rw [hc] at hmul
  norm_num [div_eq_mul_inv] at hmul
  have hfinal : 1/10 < q*Real.exp (-(B*(t-S))) := by nlinarith [hmul]
  simpa only [neg_mul] using hfinal

structure CadenceMarkOnlyResponse (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) where
  markPrefix : CadenceMarkPrefix θ route s p
  auxiliary : CadenceMarkAuxReturn θ route markPrefix.final p s.time
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  date : final.time=s.time+4
  pulse : CadenceMarkOnlyPulse execution 0 p
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q=1/10
  raw_none : ∀ j q, final.raw j q=none
  gains : ∀ j q, final.x j (.z q)=s.x j (.z q)
  recovery_gain : final.x 0 .b=s.x 0 .b+1/10
  recovery_band : 27999/100000≤final.x 0 .b ∧ final.x 0 .b≤28001/100000
  pending : final.pending=s.pending
  emissions : execution.ledger.emissions=[]
  deliveries : execution.deliveries=[]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  returnState : Snapshot 1
  returnSpan : Execution θ route auxiliary.final returnState
  returnRest : Execution θ route returnState final
  reconstruct : execution=markPrefix.execution.append (auxiliary.execution.append (returnSpan.append returnRest))
  returnDate : returnState.time=auxiliary.final.time+slowReopenDuration auxiliary.final 0
  returnDeadline : returnState.time<s.time+19/5
  returnReady : returnState.main 0=.ready
  returnCharge : returnState.x 0 .q=1/10

/-- The charge and own recovery bands are inputs; every phase and the final
READY return are constructed. The next queued source may be due at S+4 and
is deliberately left pending for the next-source constructor. -/
theorem cadence_mark_only_response_exists {θ ε route} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : s.main 0=.slow) (hq : 37/250≤s.x 0 .q ∧ s.x 0 .q≤1/4)
    (hbown : 17999/100000≤s.x 0 .b ∧ s.x 0 .b≤18001/100000)
    (ha : ∀ q, s.aux 0 q=.ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p=some s.time) (ho : ∀ q, q≠p → s.raw 0 q=none)
    (hp : ∀ d∈s.pending, s.time+4≤d.due) :
    Nonempty (CadenceMarkOnlyResponse θ route s p) := by
  obtain ⟨m⟩ := cadence_mark_prefix_exists (route := route) hb s p hf hv hm hq hbown ha hr ho hp
  let B := s.x 0 .b+1/10
  have hB : 0<B := by dsimp [B]; linarith [hbown.1]
  have hBrange : 0≤B ∧ B≤28001/100000 := by dsimp [B]; constructor <;> linarith [hbown.1,hbown.2]
  have hbudget := m.execution.recovery_upper_of_end hb 0 B (by rw [m.recovery_gain])
  have hI := m.execution.accumulatedRecovery_of_upper 0 B hbudget.2
  have hsol := m.execution.slow_solution 0 m.main_flows
  have hguard : ∀ t, m.final.time≤t → t≤s.time+419/300 →
      1/10<m.final.x 0 .q*Real.exp (-m.final.x 0 .b*(t-m.final.time)) := by
    intro t ht hu
    have ht0 := m.execution.time_monotone.trans ht
    have hbase := cadence_mark_decay_guard hq.1 hBrange ht0 hu
    have he := Real.exp_le_exp.mpr (show -B*(t-s.time)≤
        -m.execution.accumulatedRecovery 0-B*(t-m.final.time) by linarith)
    have hmul := mul_le_mul_of_nonneg_left he (by linarith [hq.1] : 0≤s.x 0 .q)
    rw [m.recovery_gain,hsol,mul_assoc,←Real.exp_add]
    simpa only [sub_eq_add_neg,neg_mul,B] using hbase.trans_le hmul
  obtain ⟨a⟩ := cadence_mark_aux_return_exists (route := route) hb m.final p s.time m.physical m.raw_valid
    ⟨m.early,m.deadline⟩ m.main_slow m.aux_silent m.sensor_charge
    ⟨by linarith [m.charge.1],m.charge.2⟩ (by rw [m.recovery_gain]; exact hB.le)
    m.sensor_budget hguard m.auxiliary_other m.raw_active m.raw_other
    (by intro d hd; rw [m.pending] at hd; exact hp d hd)
  let T := a.final.time+slowReopenDuration a.final 0
  have hbA : a.final.x 0 .b=B := (a.recovery 0).trans m.recovery_gain
  have hT : a.final.time<T := by
    dsimp [T,slowReopenDuration]
    exact lt_add_of_pos_right _ (div_pos
      (Real.log_pos ((lt_div_iff₀ (by norm_num : (0:ℝ)<1/10)).mpr (by linarith [a.charge.1])))
      (by rw [hbA]; exact hB))
  have hqMpos : 0<m.final.x 0 .q := by linarith [m.charge.1]
  have hlog : Real.log (a.final.x 0 .q/(1/10))=
      Real.log (m.final.x 0 .q/(1/10))-B*(a.final.time-m.final.time) := by
    rw [a.charge_clock,m.recovery_gain]
    rw [Real.log_div (mul_ne_zero (ne_of_gt hqMpos) (Real.exp_ne_zero _)) (by norm_num),
      Real.log_mul (ne_of_gt hqMpos) (Real.exp_ne_zero _),Real.log_exp,
      Real.log_div (ne_of_gt hqMpos) (by norm_num)]
    ring
  have hRootClock : T=m.final.time+Real.log (m.final.x 0 .q/(1/10))/B := by
    dsimp [T,slowReopenDuration]
    rw [hbA,hlog]
    field_simp [ne_of_gt hB]; ring
  have hlogUpper : Real.log (m.final.x 0 .q/(1/10))≤Real.log (5/2) := by
    apply Real.log_le_log (by positivity) ?_
    linarith [m.charge.2]
  have hquot : Real.log (m.final.x 0 .q/(1/10))/B<15/4 := by
    apply (div_lt_iff₀ hB).mpr
    dsimp [B]
    nlinarith [KernelR.log_recovery_bounds.2,hbown.1]
  have hdeadline : T<s.time+19/5 := by rw [hRootClock]; linarith [m.deadline]
  have hwait : T<s.time+4 := by linarith
  have hmo : ∀ j : Fin 1, j≠0 → a.final.main j=.ready := by intro j hj; exact (hj (Subsingleton.elim _ _)).elim
  have hao : ∀ j q, j≠(0:Fin 1) ∨ q≠p → a.final.aux j q=.ready := fun j q _ => a.auxiliary j q
  have hqx : ∀ j : Fin 1, j≠0 → a.final.x j .q<1 := by intro j hj; exact (hj (Subsingleton.elim _ _)).elim
  have hmx : ∀ j q, j≠(0:Fin 1) ∨ q≠p → a.final.x j (.m q)<1 := by
    intro j q _
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    linarith [(a.rest q).2]
  let slowFlow : Flow θ a.final (protectedMainEnd θ a.final 0 p .slow .ready none T) :=
    protectedMainFlow a.final 0 p .slow .ready none hT (Or.inr rfl) (Or.inl rfl)
      a.main_slow hmo (a.auxiliary 0 p) hao (a.raw_none 0 p) (fun j q _ => a.raw_none j q)
      (by intros; contradiction) hqx hmx
      (by intro t ht
          simpa [protectedMainRate] using slowReopen_preguard a.final 0 a.charge.1 (by rw [hbA]; exact hB) ht.2)
      (by intro t ht
          simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (by linarith [(a.rest p).2]) (by norm_num))
      (fun d hd => by rw [a.pending,m.pending] at hd; linarith [hp d hd])
  let before := protectedMainEnd θ a.final 0 p .slow .ready none T
  have hthreshold : before.x 0 .q=1/10 := by
    simpa [before,protectedMainEnd,protectedMainValues,protectedMainRate,T] using
      slowReopen_root a.final 0 a.charge.1 (by rw [hbA]; exact hB)
  let reopened := setMain before 0 .ready
  let head : Execution θ route a.final reopened :=
    .cons (.flow slowFlow) (.cons (.jump (.reopen before 0 a.main_slow hthreshold)) (.nil _))
  have haux : ∀ j q, reopened.aux j q=.ready ∧ RestBand (reopened.x j (.m q)) := by
    intro j q
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    refine ⟨a.auxiliary 0 q,?_⟩
    have hbnd := relax_mem_Icc (by norm_num : (0:ℝ)≤1/2) hT.le (a.rest q)
      (by constructor <;> norm_num : (1/40:ℝ)∈Icc (1/40-1/100000) (1/40+1/100000))
    by_cases hqp : q=p
    · subst q
      simpa [reopened,setMain,before,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hbnd
    · simpa [reopened,setMain,before,protectedMainEnd,protectedMainValues,hqp,RestBand] using hbnd
  have hready : ∀ j, ReadyCoordinates reopened j := by
    intro j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    refine ⟨by simp [reopened,setMain],?_,haux 0⟩
    change 1/10-1/100000≤before.x 0 .q ∧ before.x 0 .q≤7/50
    rw [hthreshold]; constructor <;> norm_num
  have hraw : ∀ j q, reopened.raw j q=none := a.raw_none
  have hpending : reopened.pending=s.pending := a.pending.trans m.pending
  let waitFlow := quietFlow (θ:=θ) reopened hwait
    (fun j => (hready j).ready) (fun j q => (haux j q).1) hraw
    (fun j => by linarith [(hready j).charge.2]) (fun j q => by linarith [(haux j q).2.2])
    (fun d hd => by rw [hpending] at hd; exact hp d hd)
  let wait : Execution θ route reopened (quietAt reopened (s.time+4)) := .cons (.flow waitFlow) (.nil _)
  let final := quietAt reopened (s.time+4)
  let e := m.execution.append (a.execution.append (head.append wait))
  have hdel : e.deliveries=[] := by
    simp [e,Execution.deliveries_append,m.deliveries,a.deliveries,head,wait,Execution.deliveries,Move.deliveries,Jump.deliveries]
  obtain ⟨pulse⟩ := e.cadence_mark_only_pulse hb hf hv 0 p hm hq hbown ha hr ho
    (by intro q; simp [NoArrivalAt,hdel]) (by change s.time+19/5≤s.time+4; linarith)
  have hfinalReady : ∀ j, ReadyCoordinates final j := fun j =>
    quietAt_ready_coordinates reopened j (hready j) hwait.le
  have hHeadEm : head.ledger.emissions = [] := rfl
  have hWaitEm : wait.ledger.emissions = [] := rfl
  refine ⟨{
    markPrefix := m, auxiliary := a, final := final, execution := e, date := rfl, pulse := pulse
    contacts_transversal := by
      simp [e, head, wait, m.contacts_transversal, a.contacts_transversal,
        Execution.ContactsTransversal, Jump.ContactTransversal]
    ready := hfinalReady, charge := pulse.charge_rest
    raw_none := fun j q => by have hj : j=0 := Subsingleton.elim _ _; subst j; exact pulse.raw_finished q
    gains := fun j q => by have hj : j=0 := Subsingleton.elim _ _; subst j; exact pulse.gain_preserved q
    recovery_gain := pulse.recovery_gain
    recovery_band := by rw [pulse.recovery_gain]; constructor <;> linarith [hbown.1,hbown.2]
    pending := hpending
    emissions := ?_, deliveries := hdel, physical := e.physical_invariant hb hf, raw_valid := e.raw_valid hv
    returnState := reopened, returnSpan := head, returnRest := wait, reconstruct := rfl
    returnDate := rfl, returnDeadline := hdeadline, returnReady := by simp [reopened,setMain]
    returnCharge := hthreshold
  }⟩
  change (m.execution.append (a.execution.append (head.append wait))).ledger.emissions = []
  rw [Execution.emissions_append,m.emissions,Execution.emissions_append,a.emissions,
    Execution.emissions_append,hHeadEm,hWaitEm]
  rfl

namespace CadenceMarkOnlyResponse
variable {θ route s p} (c : CadenceMarkOnlyResponse θ route s p)

theorem mark_dose : c.execution.ledger.mark 0 p=1/10 := c.pulse.mark_case.mark_dose

theorem error_zero (q : Port) : c.execution.ledger.error 0 q=0 := c.pulse.error_zero q

theorem mark_other (q : Port) (hq : q≠p) : c.execution.ledger.mark 0 q=0 :=
  c.pulse.mark_case.mark_other q hq

end CadenceMarkOnlyResponse

structure CadenceMarkOnlyNextSource {θ route s p} (c : CadenceMarkOnlyResponse θ route s p)
    (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  date : final.time=s.time+4
  values : final.x=c.final.x
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q=1/10
  raw_active : final.raw 0 p=some final.time
  raw_other : ∀ q, q≠p → final.raw 0 q=none
  gains : ∀ j q, final.x j (.z q)=s.x j (.z q)
  recovery_gain : final.x 0 .b=s.x 0 .b+1/10
  pending : final.pending=later
  emissions : execution.ledger.emissions=[]
  deliveries : execution.deliveries=[⟨0,p,s.time+4⟩]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (s.time+4)

theorem cadence_mark_only_next_source_exists {θ ε route s p}
    (c : CadenceMarkOnlyResponse θ route s p) (hb : PhysicalBox θ ε)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (later : List (Delivery 1)) (hqueue : s.pending=⟨0,p,s.time+4⟩::later)
    (hlater : ∀ d∈later, s.time+4<d.due) :
    Nonempty (CadenceMarkOnlyNextSource c later) := by
  let final : Snapshot 1 := {setRaw c.final 0 p (some c.final.time) with pending:=later}
  let arrival : Jump route c.final final := .arrive c.final ⟨0,p,s.time+4⟩ [] later
    (c.pending.trans hqueue) c.date.symm (c.raw_none 0 p)
  have haEm : arrival.ledger.emissions=[] := rfl
  have haDel : arrival.deliveries=[⟨0,p,s.time+4⟩] := rfl
  let trace := c.execution.append (.cons (.jump arrival) (.nil _))
  have hraw : final.raw 0 p=some final.time := by simp [final,setRaw]
  have hother : ∀ q, q≠p → final.raw 0 q=none := by
    intro q hq
    simp [final,setRaw,hq,c.raw_none]
  have hready : ∀ j, ReadyCoordinates final j := fun j =>
    ⟨(c.ready j).ready,(c.ready j).charge,(c.ready j).auxiliary⟩
  have hfuture : ∀ d∈final.pending, final.time<d.due := by
    intro d hd
    change d∈later at hd
    change c.final.time<d.due
    rw [c.date]
    exact hlater d hd
  have hcomplete : CompleteThrough trace (s.time+4) := by
    refine ⟨c.date,?_,?_⟩
    · intro u
      apply BeforeGuards.no_jump
      · constructor
        · intro j
          rw [(hready j).ready]
          linarith [(hready j).charge.2]
        · intro j q
          rw [((hready j).auxiliary q).1]
          linarith [((hready j).auxiliary q).2.2]
      · intro j q origin hr
        have hj : j=0 := Subsingleton.elim _ _
        subst j
        by_cases hq : q=p
        · subst q
          have ho : origin=final.time := Option.some.inj (hr.symm.trans hraw)
          rw [ho]; linarith
        · rw [hother q hq] at hr; contradiction
      · exact hfuture
    · intro d hd
      rw [←c.date]
      exact hfuture d hd
  exact ⟨{
    final:=final,execution:=trace,date:=c.date,values:=rfl,ready:=hready,charge:=c.charge
    contacts_transversal := by
      simp [trace, arrival, c.contacts_transversal, Execution.ContactsTransversal,
        Jump.ContactTransversal]
    raw_active:=hraw,raw_other:=hother,gains:=c.gains,recovery_gain:=c.recovery_gain,pending:=rfl
    emissions:=by
      simp only [trace,Execution.emissions_append,c.emissions,Execution.ledger,Move.ledger,
        haEm,Ledger.add,Ledger.zero,List.nil_append]
    deliveries:=by
      simp only [trace,Execution.deliveries_append,c.deliveries,Execution.deliveries,Move.deliveries,
        haDel,List.nil_append,List.append_nil]
    physical:=trace.physical_invariant hb hf,raw_valid:=trace.raw_valid hv,complete:=hcomplete
  }⟩

end KernelR.Hybrid
