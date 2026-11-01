import KernelR.HybridWeakInputErrorExistence

/-! Construct the first sensor transitions from a scalar main-response guard.
The sensor crossing and physical ODE paths remain the actual ones; no READY
charge reset or previously reaching execution is supplied. -/
namespace KernelR.Hybrid
open Set

/-- Only the brief pre-sensor interval needs a main-response margin. -/
theorem first_input_mark_of_response_margin_until_exists {n θ ε} (s : Snapshot n) (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port)
    (hm : ∀ j, s.main j = .ready) (ha : ∀ j q, s.aux j q = .ready)
    (hr : s.raw i p = some s.time)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hq : ∀ j, s.x j .q < 1) (hx : ∀ j q, s.x j (.m q) < 1)
    (hmain : ∀ t, s.time ≤ t → t ≤ s.time + 1 / 10 →
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t < 1)
    (hs : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (hp : ∀ d ∈ s.pending, s.time + 1 / 40 ≤ d.due) :
    Nonempty (FirstInputMark θ s i p) := by
  obtain ⟨latency,hearly,hdeadline,hroot,hprior⟩ := hb.first_sensor_crossing i p hs.1 hs.2
  have htime : s.time < s.time + latency := by linarith
  have hraw : s.time + latency < s.time + 1 := by linarith
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

theorem first_input_mark_of_response_margin_exists {n θ ε} (s : Snapshot n) (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port)
    (hm : ∀ j, s.main j = .ready) (ha : ∀ j q, s.aux j q = .ready)
    (hr : s.raw i p = some s.time)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hq : ∀ j, s.x j .q < 1) (hx : ∀ j q, s.x j (.m q) < 1)
    (hmain : ∀ t, s.time ≤ t →
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t < 1)
    (hs : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (hp : ∀ d ∈ s.pending, s.time + 1 / 40 ≤ d.due) :
    Nonempty (FirstInputMark θ s i p) :=
  first_input_mark_of_response_margin_until_exists s hb i p hm ha hr ho hq hx
    (fun t ht _ => hmain t ht) hs hp


/-- MARK finishes before source+.05; a margin through source+.1 suffices. -/
theorem FirstInputMark.first_silent_of_response_margin_until_exists {n θ ε s i p} (f : @FirstInputMark n θ s i p)
    (hb : PhysicalBox θ ε)
    (hmain : ∀ t, s.time ≤ t → t ≤ s.time + 1 / 10 →
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t < 1)
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
    apply hmain t
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
      exact hmain _ (by
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

theorem FirstInputMark.first_silent_of_response_margin_exists {n θ ε s i p} (f : @FirstInputMark n θ s i p)
    (hb : PhysicalBox θ ε)
    (hmain : ∀ t, s.time ≤ t →
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t < 1)
    (hp : ∀ d ∈ s.pending, s.time + 1 / 10 ≤ d.due) : Nonempty (FirstInputSilent f) :=
  f.first_silent_of_response_margin_until_exists hb (fun t ht _ => hmain t ht) hp

end KernelR.Hybrid
