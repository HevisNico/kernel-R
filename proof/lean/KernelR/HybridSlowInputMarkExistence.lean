import KernelR.HybridContactTransversality
import KernelR.HybridProtectedMainFlowExistence
import KernelR.HybridSlowProtectedMarkFlowExistence
import KernelR.HybridScalarFirstCrossing
import KernelR.HybridSilentReturn
/-! A fresh input while SLOW constructs a complete MARK dose with the own recovery memory. -/
namespace KernelR.Hybrid
open Set

theorem slow_input_mark_initial_charge {q b start t : ℝ}
    (hq : 7 / 50 ≤ q ∧ q ≤ 4 / 25) (hb : 7999 / 100000 ≤ b ∧ b ≤ 8001 / 100000)
    (ht : start ≤ t) (hu : t ≤ start + 1 / 40) :
    1397 / 10000 ≤ q * Real.exp (-b * (t - start)) ∧ q * Real.exp (-b * (t - start)) ≤ 4 / 25 := by
  have hd : 0 ≤ t - start := sub_nonneg.mpr ht
  have hbpos : 0 ≤ b := by linarith [hb.1]
  have htime : t - start ≤ 1 / 40 := by linarith
  have hprodUpper : b * (t - start) ≤ (8001 / 100000 : ℝ) * (1 / 40) := by nlinarith [hb.2]
  have he := Real.add_one_le_exp (-b * (t - start))
  have hmul := mul_le_mul_of_nonneg_right hq.1 (Real.exp_pos (-b * (t - start))).le
  have hexp : Real.exp (-b * (t - start)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hmulUpper := mul_le_mul_of_nonneg_left hexp (show 0 ≤ q by linarith [hq.1])
  constructor <;> nlinarith [hq.2]

/-- The changing-recovery SLOW solution retains a strong charge margin over
the whole short MARK phase, directly from its initial physical coordinates. -/
theorem slow_input_mark_final_charge {θ ε} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1) (p : Port)
    (hm : s.x 0 (.m p) = 1) (hq : 1397 / 10000 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hbown : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000)
    {t : ℝ} (ht : s.time ≤ t) (hend : t ≤ s.time + slowMarkDuration θ s 0 p) :
    17 / 125 ≤ slowMarkMain θ s 0 p t ∧ slowMarkMain θ s 0 p t ≤ 4 / 25 := by
  have hr := (hb.rates_positive 0 p).1
  have hd : 0 ≤ t - s.time := sub_nonneg.mpr ht
  have htime : t - s.time ≤ 1 / 45 := by
    have h := slowMarkDuration_upper hb s 0 p (by rw [hm]; norm_num) hm.le
    linarith
  have hexp : Real.exp (-(θ 0).lm p * (t - s.time)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hquotNon : 0 ≤ (1 - Real.exp (-(θ 0).lm p * (t - s.time))) / (θ 0).lm p :=
    div_nonneg (sub_nonneg.mpr hexp) hr.le
  have hquotUpper : (1 - Real.exp (-(θ 0).lm p * (t - s.time))) / (θ 0).lm p ≤ t - s.time := by
    apply (div_le_iff₀ hr).mpr
    nlinarith [Real.add_one_le_exp (-(θ 0).lm p * (t - s.time))]
  have hIntegralNon : 0 ≤ slowMarkIntegral θ s 0 p t := by
    dsimp only [slowMarkIntegral]
    rw [hm]
    nlinarith [hbown.1]
  have hIntegralUpper : slowMarkIntegral θ s 0 p t ≤ (58001 / 100000 : ℝ) * (1 / 45) := by
    dsimp only [slowMarkIntegral]
    rw [hm]
    nlinarith [hbown.2]
  have he := Real.add_one_le_exp (-slowMarkIntegral θ s 0 p t)
  have hmul := mul_le_mul_of_nonneg_right hq.1 (Real.exp_pos (-slowMarkIntegral θ s 0 p t)).le
  have heUpper : Real.exp (-slowMarkIntegral θ s 0 p t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hIntegralNon)
  have hmulUpper := mul_le_mul_of_nonneg_left heUpper (show 0 ≤ s.x 0 .q by linarith [hq.1])
  dsimp only [slowMarkMain]
  constructor <;> nlinarith [hq.2]

structure SlowInputMark (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) (p : Port) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  early : s.time + 1 / 100 < final.time
  deadline : final.time < s.time + 1 / 20
  main_slow : final.main 0 = .slow
  aux_silent : final.aux 0 p = .silent
  auxiliary_other : ∀ q, q ≠ p → final.aux 0 q = .ready ∧ RestBand (final.x 0 (.m q))
  sensor_charge : final.x 0 (.m p) = 4 / 5
  charge : 17 / 125 ≤ final.x 0 .q ∧ final.x 0 .q ≤ 4 / 25
  recovery_gain : final.x 0 .b = s.x 0 .b + 1 / 10
  gain_preserved : ∀ q, final.x 0 (.z q) = s.x 0 (.z q)
  raw_active : final.raw 0 p = some s.time
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = s.pending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- The actual first sensor crossing, two physical flows and both auxiliary
jumps are built from the current SLOW section. No incoming execution or
learning dose is supplied, and all queued tokens retain their multiplicity. -/
theorem slow_input_mark_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 7 / 50 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hbown : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 8 ≤ d.due) : Nonempty (SlowInputMark θ route s p) := by
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
  have preCharge : ∀ t ∈ Icc s.time M, 1397 / 10000 ≤ s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) ∧
      s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) ≤ 4 / 25 := by
    intro t ht
    exact slow_input_mark_initial_charge hq hbown ht.1 (by dsimp [M] at ht; linarith [ht.2])
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
  have hmarkq : 1397 / 10000 ≤ markStart.x 0 .q ∧ markStart.x 0 .q ≤ 4 / 25 := by
    simpa [markStart,setAux,beforeMark,protectedMainEnd,protectedMainValues,protectedMainRate] using preCharge M ⟨hM.le,le_rfl⟩
  have hmarkB : 7999 / 100000 ≤ markStart.x 0 .b ∧ markStart.x 0 .b ≤ 8001 / 100000 := by rw [hmarkb]; exact hbown
  have hmarkhead : markStart.x 0 .b + (1 / 2) * (markStart.x 0 (.m p) - 4 / 5) < 11 / 10 := by
    rw [hmarkm,hmarkb]
    linarith [hbown.2]
  let T := markStart.time + slowMarkDuration θ markStart 0 p
  have hT : markStart.time < T := by dsimp [T]; linarith [slowMarkDuration_positive hb markStart 0 p (by rw [hmarkm]; norm_num)]
  have hTupper : T < s.time + 1 / 20 := by
    have hd := slowMarkDuration_upper hb markStart 0 p (by rw [hmarkm]; norm_num) hmarkm.le
    change s.time + latency + slowMarkDuration θ markStart 0 p < s.time + 1 / 20
    linarith
  have markCharge : ∀ t ∈ Icc markStart.time T, 17 / 125 ≤ slowMarkMain θ markStart 0 p t ∧
      slowMarkMain θ markStart 0 p t ≤ 4 / 25 := by
    intro t ht
    exact slow_input_mark_final_charge hb markStart p hmarkm hmarkq hmarkB ht.1 ht.2
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
    early := by change s.time + 1 / 100 < T; change s.time + 1 / 100 < s.time + latency + slowMarkDuration θ markStart 0 p; linarith [slowMarkDuration_positive hb markStart 0 p (by rw [hmarkm]; norm_num)]
    deadline := hTupper
    main_slow := hm
    aux_silent := by simp [final,setAux]
    auxiliary_other := fun q hq => (e.aux_no_input_rest_band 0 q (ha q).1 (ha q).2 (ho q hq) (hno q)).1
    sensor_charge := slowMarkEnd_sensor hb markStart 0 p (by rw [hmarkm]; norm_num)
    charge := markCharge T ⟨hT.le,le_rfl⟩
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
  have h := slowMarkEnd_recovery hb markStart 0 p (by rw [hmarkm]; norm_num)
  rw [hmarkm,hmarkb] at h
  change (slowMarkEnd θ markStart 0 p (markStart.time + slowMarkDuration θ markStart 0 p)).x 0 .b = s.x 0 .b + 1 / 10
  linarith

end KernelR.Hybrid
