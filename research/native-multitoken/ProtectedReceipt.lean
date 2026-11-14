import NativeMultiTokenMilestone
import KernelR.HybridCadenceMarkOnlyExistence

/-! A protected one-cell receipt for the multi-token calendar. -/
namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid Set MeasureTheory
open scoped BigOperators

private theorem quarter_above_reopen {cost : ℝ} (bound : cost < 9 / 10) :
    1 / 10 < (1 / 4) * Real.exp (-cost) := by
  have ref : Real.exp (- Real.log (5 / 2)) = (2 / 5 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]
    norm_num
  have drop : (2 / 5 : ℝ) < Real.exp (-cost) := by
    rw [← ref]
    exact Real.exp_lt_exp.mpr (by linarith [KernelR.log_recovery_bounds.1])
  linarith

/-- The still-draining sensor bounds recovery before assuming a completed MARK.
Only the uniquely active port can enter MARK, starting at its unit guard. -/
theorem provisional_mark_recovery {θ ε} (box : @PhysicalBox 1 θ ε) (s : Snapshot 1)
    (p : Port) (sensor : s.x 0 (.m p) = 1) (recovery : s.x 0 .b = 9 / 50)
    {t : ℝ} (after : s.time ≤ t) (before : t ≤ s.time + slowMarkDuration θ s 0 p) :
    0 ≤ slowMarkRecovery θ s 0 p t ∧ slowMarkRecovery θ s 0 p t ≤ 7 / 25 := by
  have floor := slowMarkSensor_floor box s 0 p (by rw [sensor]; norm_num) before
  have expLe : Real.exp (-(θ 0).lm p * (t - s.time)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (box.rates_positive 0 p).1.le) (sub_nonneg.mpr after))
  have upper : slowMarkSensor θ s 0 p t ≤ 1 := by
    simpa [slowMarkSensor, sensor] using expLe
  unfold slowMarkRecovery
  rw [sensor, recovery]
  constructor <;> linarith

private theorem provisional_mark_integral {θ ε} (box : @PhysicalBox 1 θ ε) (s : Snapshot 1)
    (p : Port) (sensor : s.x 0 (.m p) = 1) (recovery : s.x 0 .b = 9 / 50)
    {t : ℝ} (after : s.time ≤ t) (before : t ≤ s.time + slowMarkDuration θ s 0 p) :
    0 ≤ slowMarkIntegral θ s 0 p t ∧ slowMarkIntegral θ s 0 p t ≤ 7 / 25 * (t - s.time) := by
  have continuous : Continuous (slowMarkRecovery θ s 0 p) := by
    unfold slowMarkRecovery slowMarkSensor
    fun_prop
  have integral : slowMarkIntegral θ s 0 p t = ∫ v in s.time..t, slowMarkRecovery θ s 0 p v := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => slowMarkIntegral_derivative (θ := θ) s 0 p v
        (ne_of_gt (box.rates_positive 0 p).1)) (continuous.intervalIntegrable s.time t)
    simpa [slowMarkIntegral] using h.symm
  rw [integral]
  have pointwise (v : ℝ) (hv : v ∈ Icc s.time t) :=
    provisional_mark_recovery box s p sensor recovery hv.1 (hv.2.trans before)
  refine ⟨intervalIntegral.integral_nonneg after (fun v hv => (pointwise v hv).1), ?_⟩
  have le := intervalIntegral.integral_mono_on (μ := volume) after
    (continuous.intervalIntegrable s.time t) (intervalIntegrable_const (c := (7 / 25 : ℝ)))
    (fun v hv => (pointwise v hv).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at le
  linarith

private structure ReceiptMarkPrefix (θ : Fin 1 → KernelR.Hybrid.Parameters)
    (route : Router 1) (s : Snapshot 1) (p : Port) where
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
  charge : 1/10<final.x 0 .q ∧ final.x 0 .q≤1/4
  recovery_gain : final.x 0 .b=s.x 0 .b+1/10
  gain_preserved : ∀ q, final.x 0 (.z q)=s.x 0 (.z q)
  raw_active : final.raw 0 p=some s.time
  raw_other : ∀ q, q≠p → final.raw 0 q=none
  pending : final.pending=s.pending
  emissions : execution.ledger.emissions=[]
  deliveries : execution.deliveries=[]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

private theorem receipt_mark_prefix_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (fastEnd : ℝ) (earlier : fastEnd ≤ s.time)
    (hq : s.x 0 .q = (1 / 4) * Real.exp (-(9 / 50) * (s.time - fastEnd)))
    (hbown : s.x 0 .b = 9 / 50)
    (budget : (9 / 50) * (s.time - fastEnd) + (7 / 25) * (419 / 300) < 9 / 10)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) : Nonempty (ReceiptMarkPrefix θ route s p) := by
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
  have preBase (t : ℝ) :
      s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) =
      (1 / 4) * Real.exp (-((9 / 50) * (s.time - fastEnd) + (9 / 50) * (t - s.time))) := by
    rw [hq, hbown, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have preCharge (t : ℝ) (ht : t ∈ Icc s.time M) :
      1 / 10 < s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) := by
    rw [preBase]
    apply quarter_above_reopen
    have before := ht.2
    dsimp [M] at before
    linarith
  let firstFlow := protectedMainFlow (θ := θ) s 0 p .slow .ready (some s.time) hM (Or.inr rfl) (Or.inl rfl)
    hm hmOther (ha p).1 haOther hr hrOther
    (by intro o he; cases Option.some.inj he; exact ⟨le_rfl,by dsimp [M]; linarith⟩)
    hqx hmx
    (by intro t ht; simp only [reduceCtorEq,ite_false,protectedMainRate]; exact preCharge t ⟨ht.1,ht.2.le⟩)
    (by intro t ht; simpa [rawInputScale] using hprior t ht)
    (fun d hd => by dsimp [M]; linarith [hp d hd])
  have hthreshold : beforeMark.x 0 (.m p) = 1 := by
    simpa [beforeMark,protectedMainEnd,protectedMainValues,rawInputScale,M] using hroot
  let markStart := setAux beforeMark 0 p .mark
  let first : Execution θ route s markStart :=
    .cons (.flow firstFlow) (.cons (.jump (.mark _ 0 p (ha p).1 hthreshold)) (.nil _))
  have hmarkm : markStart.x 0 (.m p) = 1 := hthreshold
  have hmarkb : markStart.x 0 .b = s.x 0 .b := rfl
  have hmarkclock :
      markStart.x 0 .q = (1 / 4) * Real.exp
        (-((9 / 50) * (s.time - fastEnd) + (9 / 50) * (M - s.time))) := preBase M
  have hmarkB : markStart.x 0 .b = 9 / 50 := hmarkb.trans hbown
  have hmarkhead : markStart.x 0 .b + (1 / 2) * (markStart.x 0 (.m p) - 4 / 5) < 11 / 10 := by
    rw [hmarkm, hmarkB]
    norm_num
  let T := markStart.time + slowMarkDuration θ markStart 0 p
  have hT : markStart.time < T := by dsimp [T]; linarith [slowMarkDuration_positive hb markStart 0 p (by rw [hmarkm]; norm_num)]
  have hTupper : T < s.time + 1 / 20 := by
    have hd := slowMarkDuration_upper hb markStart 0 p (by rw [hmarkm]; norm_num) hmarkm.le
    change s.time + latency + slowMarkDuration θ markStart 0 p < s.time + 1 / 20
    linarith
  have markCharge (t : ℝ) (ht : t ∈ Icc markStart.time T) :
      1 / 10 < slowMarkMain θ markStart 0 p t ∧ slowMarkMain θ markStart 0 p t ≤ 1 / 4 := by
    have integral := provisional_mark_integral hb markStart p hmarkm hmarkB ht.1 ht.2
    have after : M ≤ t := ht.1
    have before : t < s.time + 1 / 20 := ht.2.trans_lt hTupper
    have initial : s.time ≤ M := hM.le
    let cost := (9 / 50) * (s.time - fastEnd) + (9 / 50) * (M - s.time) +
      slowMarkIntegral θ markStart 0 p t
    have form : slowMarkMain θ markStart 0 p t = (1 / 4) * Real.exp (-cost) := by
      rw [slowMarkMain, hmarkclock, mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [cost]
      ring
    rw [form]
    have ilo := integral.1
    have ihi : slowMarkIntegral θ markStart 0 p t ≤ (7 / 25) * (t - M) := integral.2
    exact ⟨quarter_above_reopen (by dsimp [cost]; linarith),
      by
        have nonneg : 0 ≤ cost := by dsimp [cost]; linarith
        exact (mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonneg)) (by norm_num)).trans (by norm_num)⟩
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



/-- The unique receipt port is active at the start. Construct its local
MARK and protected auxiliary return, then reopen at the actual SLOW root. -/
theorem protected_receipt_body {θ ε route} (hb : @PhysicalBox 1 θ ε)
    (s : Snapshot 1) (p : Port) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : s.main 0 = .slow) (fastEnd : ℝ) (earlier : fastEnd ≤ s.time)
    (charge : s.x 0 .q = (1 / 4) * Real.exp (-(9 / 50) * (s.time - fastEnd)))
    (recovery : s.x 0 .b = 9 / 50)
    (budget : (9 / 50) * (s.time - fastEnd) + (7 / 25) * (419 / 300) < 9 / 10)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    ∃ (u : Snapshot 1) (run : Execution θ route s u),
      s.time < u.time ∧ u.time < s.time + 19 / 5 ∧ ReadyCoordinates u 0 ∧
      u.x 0 .q = 1 / 10 ∧ (∀ q, u.raw 0 q = none) ∧ u.pending = s.pending ∧
      run.deliveries = [] ∧ run.ledger.emissions = [] ∧ run.ledger.recovery 0 = 1 / 10 ∧
      ∀ q, run.ledger.error 0 q = 0 ∧
        run.ledger.mark 0 q = if q = p then 1 / 10 else 0 := by
  obtain ⟨m⟩ := receipt_mark_prefix_exists (route := route) hb s p hf hv hm fastEnd earlier
    charge recovery budget ha hr ho hp
  let B := s.x 0 .b + 1 / 10
  have hB : 0 < B := by dsimp [B]; rw [recovery]; norm_num
  have Bexact : B = 7 / 25 := by dsimp [B]; rw [recovery]; norm_num
  have hbudget := m.execution.recovery_upper_of_end hb 0 B (by rw [m.recovery_gain])
  have hI := m.execution.accumulatedRecovery_of_upper 0 B hbudget.2
  have hsol := m.execution.slow_solution 0 m.main_flows
  have hguard (t : ℝ) (after : m.final.time ≤ t) (before : t ≤ s.time + 419 / 300) :
      1 / 10 < m.final.x 0 .q * Real.exp (-m.final.x 0 .b * (t - m.final.time)) := by
    rw [m.recovery_gain, hsol, mul_assoc, ← Real.exp_add, charge, mul_assoc, ← Real.exp_add]
    have hcost : (9 / 50) * (s.time - fastEnd) + m.execution.accumulatedRecovery 0 +
        B * (t - m.final.time) < 9 / 10 := by
      rw [Bexact] at hI ⊢
      linarith
    simpa only [B, neg_add, neg_mul, add_assoc] using quarter_above_reopen hcost
  obtain ⟨a⟩ := cadence_mark_aux_return_exists (route := route) hb m.final p s.time m.physical m.raw_valid
    ⟨m.early, m.deadline⟩ m.main_slow m.aux_silent m.sensor_charge m.charge
    (by rw [m.recovery_gain]; exact hB.le) m.sensor_budget hguard m.auxiliary_other
    m.raw_active m.raw_other (by intro d hd; rw [m.pending] at hd; exact hp d hd)
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
    rw [recovery]
    linarith [KernelR.log_recovery_bounds.2]
  have hdeadline : T<s.time+19/5 := by rw [hRootClock]; linarith [m.deadline]
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
  let run := m.execution.append (a.execution.append head)
  have delivered : run.deliveries = [] := by
    change (m.execution.append (a.execution.append head)).deliveries = []
    rw [Execution.deliveries_append, m.deliveries, Execution.deliveries_append, a.deliveries]
    rfl
  have emitted : run.ledger.emissions = [] := by
    change (m.execution.append (a.execution.append head)).ledger.emissions = []
    rw [Execution.emissions_append, m.emissions, Execution.emissions_append, a.emissions]
    rfl
  have gainZero (q : Port) : run.ledger.error 0 q = 0 := by
    have balance := run.gain_balance 0 q
    have unchanged : reopened.x 0 (.z q) = s.x 0 (.z q) :=
      (a.gains 0 q).trans (m.gain_preserved q)
    linarith
  have total : run.ledger.recovery 0 = 1 / 10 := by
    have balance := run.recovery_balance 0
    have endpoint : reopened.x 0 .b = s.x 0 .b + 1 / 10 := hbA
    linarith
  have markOther (q : Port) (ne : q ≠ p) : run.ledger.mark 0 q = 0 := by
    have no : NoArrivalAt run 0 q := by simp [NoArrivalAt, delivered]
    have states := run.aux_ready_without_input_band 0 q (ha q).1 (ha q).2.2 (ho q ne) no
    exact run.mark_zero_aux 0 q .ready (by decide) (run.allStates_aux_flows 0 q .ready states)
  have sum : (∑ q : Port, run.ledger.mark 0 q) = run.ledger.mark 0 p :=
    Finset.sum_eq_single p (fun q _ ne => markOther q ne) (by simp)
  have markSelected : run.ledger.mark 0 p = 1 / 10 := by
    rw [run.recovery_sum_marks, sum] at total
    exact total
  refine ⟨reopened, run, ?_, hdeadline, hready 0, hthreshold, hraw 0, hpending,
    delivered, emitted, total, ?_⟩
  · change s.time < T
    exact lt_of_le_of_lt (m.execution.time_monotone.trans a.execution.time_monotone) hT
  · intro q
    refine ⟨gainZero q, ?_⟩
    by_cases eq : q = p
    · subst q; simpa using markSelected
    · simpa [eq] using markOther q eq

private theorem receipt_calendar_budget {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    let arrival := launchDate p + latency p i + (p.delay i : ℝ)
    let fastEnd := launchDate p + latency p (p.successor i) + 1
    fastEnd < arrival ∧ (9 / 50) * (arrival - fastEnd) + (7 / 25) * (419 / 300) < 9 / 10 := by
  have good : p.Valid := of_decide_eq_true accepted
  have d := good.2.2.2.2.1 i
  have low : (8 / 5 : ℚ) < p.delay i := by linarith
  have lowR : (8 / 5 : ℝ) < (p.delay i : ℝ) := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr low
  have validBudget := good.2.2.2.2.2 i
  change (9 / 50 : ℚ) * (p.delay i + 3 / 5 - 1) + (7 / 25) * (419 / 300) < 9 / 10 at validBudget
  have budgetR : (9 / 50 : ℝ) * ((p.delay i : ℝ) + 3 / 5 - 1) +
      (7 / 25) * (419 / 300) < 9 / 10 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr validBudget
  obtain ⟨first, last, _, _⟩ := scalar_latency accepted i
  obtain ⟨targetFirst, targetLast, _, _⟩ := scalar_latency accepted (p.successor i)
  dsimp
  constructor <;> linarith

/-- Consume the actual port-2 delivery at its calendar clock in SLOW.
The supplied charge is the continuation from the receiver's own FAST end. -/
theorem protected_slow_admission {p : Parameters N} (accepted : p.check = true) (i : Fin N)
    {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1)
    (physical : PhysicalInvariant θ s) (valid : RawValid s) (mode : s.main 0 = .slow)
    (date : s.time = launchDate p + latency p i + (p.delay i : ℝ))
    (charge : s.x 0 .q = (1 / 4) * Real.exp
      (-(9 / 50) * (s.time - (launchDate p + latency p (p.successor i) + 1))))
    (recovery : s.x 0 .b = 9 / 50) (aux : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (raw : ∀ q, s.raw 0 q = none) (later : List (Delivery 1))
    (queue : s.pending = ⟨0, 2, s.time⟩ :: later)
    (future : ∀ d ∈ later, s.time + 4 ≤ d.due) :
    ∃ (u : Snapshot 1) (run : Execution θ route s u),
      s.time < u.time ∧ u.time < s.time + 19 / 5 ∧ ReadyCoordinates u 0 ∧
      u.x 0 .q = 1 / 10 ∧ (∀ q, u.raw 0 q = none) ∧ u.pending = later ∧
      run.deliveries = [⟨0, 2, s.time⟩] ∧ run.ledger.emissions = [] ∧
      run.ledger.recovery 0 = 1 / 10 ∧
      ∀ q, run.ledger.error 0 q = 0 ∧
        run.ledger.mark 0 q = if q = 2 then 1 / 10 else 0 := by
  let token : Delivery 1 := ⟨0, 2, s.time⟩
  let a := { setRaw s 0 2 (some s.time) with pending := later }
  let intake : Jump route s a := .arrive s token [] later queue rfl (raw 2)
  let first : Execution θ route s a := .cons (.jump intake) (.nil _)
  let fastEnd := launchDate p + latency p (p.successor i) + 1
  obtain ⟨early, budget⟩ := receipt_calendar_budget accepted i
  have clock : a.time = launchDate p + latency p i + (p.delay i : ℝ) := date
  obtain ⟨u, body, after, finish, ready, qRest, rawRest, pending, delivered, emitted, dose, doses⟩ :=
    protected_receipt_body (route := route) hb a 2 (first.physical_invariant hb physical)
      (first.raw_valid valid) mode fastEnd (by rw [clock]; exact early.le) charge recovery
      (by rw [clock]; exact budget) aux (by simp [a, setRaw])
      (fun q ne => by simp [a, setRaw, ne, raw]) future
  refine ⟨u, .cons (.jump intake) body, after, finish, ready, qRest, rawRest, pending,
    ?_, emitted, ?_, ?_⟩
  · change [token] ++ body.deliveries = _
    rw [delivered]
    rfl
  · change 0 + body.ledger.recovery 0 = _
    simpa only [zero_add] using dose
  · intro q
    change 0 + body.ledger.error 0 q = 0 ∧ 0 + body.ledger.mark 0 q = _
    simpa only [zero_add] using doses q

end NetworkStability.NativeMultiToken
