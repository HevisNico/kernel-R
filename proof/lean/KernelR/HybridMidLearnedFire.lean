import KernelR.HybridFirstLearnedFireExistence

/-! True first learned firing for intermediate gains through 2.2, at any port. -/
namespace KernelR.Hybrid
open Set

theorem first_mid_learned_mark_exists {n θ ε} (s : Snapshot n) (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port)
    (hm : ∀ j, s.main j = .ready) (ha : ∀ j q, s.aux j q = .ready)
    (hr : s.raw i p = some s.time)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hq : ∀ j, s.x j .q < 1) (hx : ∀ j q, s.x j (.m q) < 1)
    (hqi : s.x i .q ≤ 7 / 50) (hg : Real.exp (s.x i (.z p)) ≤ 11 / 5)
    (hs : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (hp : ∀ d ∈ s.pending, s.time + 1 / 40 ≤ d.due) :
    Nonempty (FirstInputMark θ s i p) := by
  obtain ⟨latency,hearly,hdeadline,hroot,hprior⟩ := hb.first_sensor_crossing i p hs.1 hs.2
  have htime : s.time < s.time + latency := by linarith
  have hraw : s.time + latency < s.time + 1 := by linarith
  have hmain : ∀ t, s.time ≤ t → t ≤ s.time + 3 / 10 →
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t < 1 :=
    fun t ht hu => readyPulse_mid_gain_not_early hqi (by linarith [hg]) ht hu
  refine ⟨{
    latency := latency
    early := hearly
    deadline := hdeadline
    main_ready := hm
    aux_ready := ha
    raw_active := hr
    raw_other := ho
    flow := readyInputFlow s i p htime hraw hm ha hr ho hq hx
      (fun t ht => hmain t ht.1 (by linarith [ht.2])) hprior (fun d hd => by linarith [hp d hd])
    threshold := hroot
    main_below := ?_
    aux_below := ?_
    pending_future := fun d hd => by linarith [hp d hd]
  }⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [readyInputEnd,readyInputValues,readyInputMainAmplitude] using
        hmain (s.time + latency) htime.le (by linarith)
    · simp only [readyInputEnd,readyInputValues,readyInputMainAmplitude,ite_eq_right hj]
      rw [readyPulse_zero_eq_relax]
      exact relax_lt (by norm_num) htime.le (hq j) (by norm_num)
  · intro j q hother
    have hne : ¬ (j = i ∧ q = p) := by tauto
    simp only [readyInputEnd,readyInputValues,readyInputAuxAmplitude,ite_eq_right hne]
    rw [auxPulse_zero_eq_relax]
    exact relax_lt (by norm_num) htime.le (hx j q) (by norm_num)


theorem FirstInputMark.first_mid_learned_silent_exists {n θ ε s i p} (f : @FirstInputMark n θ s i p)
    (hb : PhysicalBox θ ε) (hqi : s.x i .q ≤ 7 / 50)
    (hg : Real.exp (s.x i (.z p)) ≤ 11 / 5)
    (hp : ∀ d ∈ s.pending, s.time + 1 / 10 ≤ d.due) : Nonempty (FirstInputSilent f) := by
  let D := Real.log (5 / 4 : ℝ) / (θ i).lm p
  have hrate := (hb.rates_positive i p).1
  have hD : 0 < D := div_pos (Real.log_pos (by norm_num)) hrate
  have hDupper : D ≤ 1 / 45 := hb.mark_duration_upper i p
  have htime : f.final.time < f.silentDate := by
    change s.time + f.latency < s.time + f.latency + D
    linarith
  have hdate : f.silentDate < s.time + 1 / 20 := by
    change s.time + f.latency + D < s.time + 1 / 20
    linarith [f.deadline]
  have hqstart : ∀ j, f.final.x j .q < 1 := f.main_below
  have hmstart : ∀ j q, j ≠ i ∨ q ≠ p → f.final.x j (.m q) < 1 := f.aux_below
  have hm : ∀ j, f.final.main j = .ready := f.main_ready
  have ha : f.final.aux i p = .mark := by simp [FirstInputMark.final,setAux]
  have hao : ∀ j q, j ≠ i ∨ q ≠ p → f.final.aux j q = .ready := by
    intro j q h
    rcases h with hj | hq
    · simp [FirstInputMark.final,setAux,readyInputEnd,f.aux_ready,hj]
    · simp [FirstInputMark.final,setAux,readyInputEnd,Function.update_apply,ite_apply,f.aux_ready,hq]
  have hr : f.final.raw i p = some s.time := f.raw_active
  have ho : ∀ j q, j ≠ i ∨ q ≠ p → f.final.raw j q = none := f.raw_other
  have hsensor : f.final.x i (.m p) = 1 := f.sensor_threshold
  have hsupport : ∀ o, some s.time = some o → o ≤ f.final.time ∧ f.silentDate ≤ o + 1 := by
    intro o he
    have heq : o = s.time := (Option.some.inj he).symm
    subst o
    change s.time ≤ s.time + f.latency ∧ f.silentDate ≤ s.time + 1
    constructor <;> linarith [f.early]
  have hq : ∀ t ∈ Ico f.final.time f.silentDate, readyPulse (f.final.x i .q)
      (Real.exp (f.final.x i (.z p)) * rawInputScale (some s.time) f.final.time) f.final.time t < 1 := by
    intro t ht
    rw [f.protected_response_restart]
    refine readyPulse_mid_gain_not_early hqi (by linarith [hg]) ?_ ?_
    · have hs : s.time < f.final.time := by change s.time < s.time + f.latency; linarith [f.early]
      exact hs.le.trans ht.1
    · linarith [ht.2]
  have hend : Real.exp (-(θ i).lm p * D) = (4 / 5 : ℝ) := by
    have hd : -(θ i).lm p * D = -Real.log (5 / 4 : ℝ) := by dsimp [D]; field_simp
    rw [hd,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4)]
    norm_num
  have hx : ∀ t ∈ Ico f.final.time f.silentDate, (if AuxMode.mark = .mark then (4 / 5 : ℝ) else 1 / 10) <
      f.final.x i (.m p) * Real.exp (-protectedReadyRate (θ i) p .mark * (t - f.final.time)) := by
    intro t ht
    simp only [ite_true,hsensor,one_mul,protectedReadyRate]
    rw [← hend]
    apply Real.exp_lt_exp.mpr
    have htime : t - f.final.time < D := by
      change t - (s.time + f.latency) < D
      have ht2 : t < s.time + f.latency + D := ht.2
      linarith
    nlinarith
  let flow := readyProtectedFlow f.final i p .mark (some s.time) htime (Or.inl rfl) hm ha hao hr ho
    hsupport hqstart hmstart hq hx (fun d hd => by change d ∈ s.pending at hd; linarith [hp d hd])
  have hthreshold : f.silentBefore.x i (.m p) = 4 / 5 := by
    simp [FirstInputMark.silentBefore,readyProtectedEnd,readyProtectedValues]
    rw [hsensor]
    simpa only [one_mul,protectedReadyRate,FirstInputMark.silentDate,FirstInputMark.final,
      setAux,readyInputEnd,add_sub_cancel_left,neg_mul] using hend
  refine ⟨⟨flow,hthreshold,?_,?_,hdate,fun d hd => by linarith [hp d hd]⟩⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [FirstInputMark.silentBefore,readyProtectedEnd,readyProtectedValues]
      simp only [protectedRawAmplitude,ite_true]
      rw [f.protected_response_restart]
      exact readyPulse_mid_gain_not_early hqi (by linarith [hg]) (by
        have hs : s.time < f.final.time := by change s.time < s.time + f.latency; linarith [f.early]
        exact hs.le.trans htime.le) (by linarith)
    · change readyPulse (f.final.x j .q) (protectedRawAmplitude f.final i p (some s.time) j) f.final.time f.silentDate < 1
      rw [protectedRawAmplitude,ite_eq_right hj,readyPulse_zero_eq_relax]
      exact relax_lt (by norm_num) htime.le (hqstart j) (by norm_num)
  · intro j q h
    have hnot : ¬ (j = i ∧ q = p) := by tauto
    change (if j = i ∧ q = p then _ else _) < 1
    rw [ite_eq_right hnot]
    exact relax_lt (by norm_num) htime.le (hmstart j q h) (by norm_num)

/-- The first real main threshold and its strict preceding guard come from
the scalar response; sensor transitions before ERROR do not change this gain. -/
theorem readyPulse_first_mid_learned_crossing {initial amplitude start : ℝ}
    (hq : 1 / 10 - 1 / 100000 ≤ initial ∧ initial ≤ 7 / 50)
    (hg : 9 / 5 ≤ amplitude ∧ amplitude ≤ 11 / 5) :
    ∃ latency : ℝ, 3 / 10 < latency ∧ latency < 9 / 10 ∧
      readyPulse initial amplitude start (start + latency) = 1 ∧
      ∀ t ∈ Ico start (start + latency), readyPulse initial amplitude start t < 1 := by
  have hc : Continuous (fun t : ℝ => readyPulse initial amplitude start (start + t)) := by
    unfold readyPulse response
    fun_prop
  obtain ⟨latency,hpos,hend,hroot,hprior⟩ := scalar_first_one_crossing hc
    (by norm_num : (0 : ℝ) < 9 / 10)
    (by rw [add_zero,readyPulse_initial]; linarith [hq.2])
    (readyPulse_emission_by_deadline hq.1 hg.1)
  have hearly : 3 / 10 < latency := by
    by_contra hn
    have h := readyPulse_mid_gain_not_early (amplitude := amplitude) hq.2 (by linarith [hg.2])
      (by linarith : start ≤ start + latency) (by linarith : start + latency ≤ start + 3 / 10)
    rw [hroot] at h
    linarith
  refine ⟨latency,hearly,hend,hroot,?_⟩
  intro t ht
  have h := hprior (t - start) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  simpa only [show start + (t - start) = t by ring] using h

/-- This main contact has positive derivative under the same response bounds. -/
theorem readyPulse_first_mid_learned_crossing_transversal {initial amplitude start : ℝ}
    (hq : 1 / 10 - 1 / 100000 ≤ initial ∧ initial ≤ 7 / 50)
    (hg : 9 / 5 ≤ amplitude ∧ amplitude ≤ 11 / 5) :
    ∃ latency : ℝ, 3 / 10 < latency ∧ latency < 9 / 10 ∧
      readyPulse initial amplitude start (start + latency) = 1 ∧
      (∀ t ∈ Ico start (start + latency), readyPulse initial amplitude start t < 1) ∧
      0 < deriv (readyPulse initial amplitude start) (start + latency) := by
  obtain ⟨latency, early, deadline, root, prior⟩ :=
    readyPulse_first_mid_learned_crossing hq hg (start := start)
  refine ⟨latency, early, deadline, root, prior, ?_⟩
  apply readyPulse_transversal_of_later_value (by linarith [hg.1] : 0 ≤ amplitude)
    (show start + latency < start + 9 / 10 by linarith)
  rw [root]
  exact readyPulse_emission_by_deadline hq.1 hg.1

#print axioms readyPulse_first_mid_learned_crossing_transversal

theorem first_mid_learned_fire_exists {n θ ε route} (s : Snapshot n) (hb : @PhysicalBox n θ ε)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (i : Fin n) (p : Port)
    (hs : ∀ j, ReadyCoordinates s j)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 11 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hp : ∀ d ∈ s.pending, s.time + 31 / 4 ≤ d.due) :
    Nonempty (FirstLearnedFire θ route s i p) := by
  have hm : ∀ j, s.main j = .ready := fun j => (hs j).ready
  have ha : ∀ j q, s.aux j q = .ready := fun j q => ((hs j).auxiliary q).1
  have hq0 : ∀ j, s.x j .q < 1 := fun j => by linarith [(hs j).charge.2]
  have hx0 : ∀ j q, s.x j (.m q) < 1 := fun j q => by linarith [((hs j).auxiliary q).2.2]
  obtain ⟨f⟩ := first_mid_learned_mark_exists s hb i p hm ha hr ho hq0 hx0 (hs i).charge.2 hg.2
    ((hs i).auxiliary p).2 (fun d hd => by linarith [hp d hd])
  obtain ⟨g⟩ := f.first_mid_learned_silent_exists hb (hs i).charge.2 hg.2 (fun d hd => by linarith [hp d hd])
  obtain ⟨latency,hearly,hdeadline,hroot,hprior⟩ := readyPulse_first_mid_learned_crossing (hs i).charge hg
  let T := s.time + latency
  have hT : g.final.time < T := by rw [g.date]; dsimp [T]; linarith [g.deadline]
  have hstart : s.time ≤ g.final.time := by
    have h := g.flow.positive
    change s.time + f.latency < g.final.time at h
    linarith [f.early]
  have hrawSupport : ∀ o, some s.time = some o → o ≤ g.final.time ∧ T ≤ o + 1 := by
    intro o he
    have heq : o = s.time := (Option.some.inj he).symm
    subst o
    exact ⟨hstart,by dsimp [T]; linarith⟩
  have hq : ∀ t ∈ Ico g.final.time T, readyPulse (g.final.x i .q)
      (Real.exp (g.final.x i (.z p)) * rawInputScale (some s.time) g.final.time) g.final.time t < 1 := by
    intro t ht
    rw [g.response_restart]
    exact hprior t ⟨hstart.trans ht.1,ht.2⟩
  have hschedule := protected_decay_schedule (initial := (4 / 5 : ℝ)) (floor := (1 / 10 : ℝ))
    (by norm_num) (by norm_num) (hb.rates_positive i p).2.1
  have hratio : Real.log ((4 / 5 : ℝ) / (1 / 10)) / (θ i).ls p = Real.log 8 / (θ i).ls p := by norm_num
  have hguard : ∀ t ∈ Icc g.final.time T,
      1 / 10 < (4 / 5 : ℝ) * Real.exp (-(θ i).ls p * (t - g.final.time)) := by
    intro t ht
    apply hschedule.2.2 (t - g.final.time) (by linarith [ht.1])
    rw [hratio]
    have he := (g.errorDate_bounds hb).1
    change s.time + 99 / 100 < g.final.time + Real.log 8 / (θ i).ls p at he
    dsimp [T] at ht
    linarith [ht.2]
  have hx : ∀ t ∈ Ico g.final.time T, (if AuxMode.silent = .mark then (4 / 5 : ℝ) else 1 / 10) <
      g.final.x i (.m p) * Real.exp (-protectedReadyRate (θ i) p .silent * (t - g.final.time)) := by
    intro t ht
    simpa only [reduceCtorEq,ite_false,g.sensor_charge,protectedReadyRate] using hguard t ⟨ht.1,ht.2.le⟩
  let flow := readyProtectedFlow g.final i p .silent (some s.time) hT (Or.inr rfl)
    g.main_ready g.aux_silent g.aux_other g.raw_active g.raw_other hrawSupport g.main_below g.aux_below hq hx
    (fun d hd => by change d ∈ s.pending at hd; dsimp [T]; linarith [hp d hd])
  have hthreshold : (g.learnedFireBefore latency).x i .q = 1 := by
    simp only [FirstInputSilent.learnedFireBefore,readyProtectedEnd,readyProtectedValues,protectedRawAmplitude,ite_true]
    rw [g.response_restart]
    exact hroot
  let endBefore := g.learnedFireBefore latency
  let endFinal := g.learnedFireFinal route latency
  let e : Execution θ route s endFinal := (g.execution route).append
    (.cons (.flow flow) (.cons (.jump (.fire endBefore i (g.main_ready i) hthreshold)) (.nil _)))
  refine ⟨{
    firstMark := f
    firstSilent := g
    latency := latency
    early := hearly
    deadline := hdeadline
    response_root := hroot
    flow := flow
    threshold := hthreshold
    sensor_above_floor := ?_
    physical := e.physical_invariant hb hf
    raw_valid := e.raw_valid hv
  }⟩
  simpa [FirstInputSilent.learnedFireBefore,readyProtectedEnd,readyProtectedValues,protectedReadyRate,g.sensor_charge]
    using hguard T ⟨hT.le,le_rfl⟩


end KernelR.Hybrid
