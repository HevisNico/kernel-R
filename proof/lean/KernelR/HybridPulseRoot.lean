import KernelR.HybridStableMemory

/-! The physical firing equation, unique latency roots, and residual-charge comparison. -/
namespace KernelR.Hybrid
open Set

/-- The actual first firing satisfies the scalar threshold equation with the
real initial charge. Gain freezing is derived from the sensor cycle. -/
theorem MainTrigger.firing_equation {n θ route s u i p} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) (cycle : SensorCycle e i p) (hr : s.raw i p = some s.time)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q) :
    readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time tr.beforeFire.time = 1 := by
  have hp : e.IsPrefix tr.span :=
    (congrArg (fun actual => actual.IsPrefix tr.span) tr.reconstruct).mpr (.append_left _ _)
  have hdeadline : tr.beforeFire.time < s.time + 9 / 10 := by simpa only [tr.entry.time_unchanged] using tr.deadline
  have hraw := tr.span.raw_active_before i p s.time hr (by linarith)
  have hothers : tr.span.AllFlows (fun {v w} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply tr.span.allFlows_forall (fun q {v w} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases hq : q = p
    · subst q; exact tr.span.allFlows_mono (fun f _ h => False.elim (h rfl)) hraw
    · exact tr.span.allFlows_mono (fun f hf _ => hf) (tr.span.raw_absent_allFlows i q
        (tr.span.raw_absent_of_no_arrival i q (ho q hq) (hp.no_arrival i q (hno q))).2)
  have hgain := hp.all_flows
    (fun {v w} f => ∀ t ∈ Icc v.time w.time, t ≤ s.time + 99 / 100 → f.path t i (.z p) = s.x i (.z p))
    (fun {v w} f {cut} hc hend hf t ht hu => hf t ⟨ht.1,ht.2.trans hend⟩ hu) cycle.gain_before_error
  have hconst : tr.span.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i (.z p) = s.x i (.z p)) := by
    refine tr.span.allFlows_mono ?_ (tr.span.allFlows_and hgain tr.span.allFlows_time_bounds)
    intro v w f hf t ht
    exact hf.1 t ht (by have h := (hf.2 t ht).2; linarith)
  have hdrive : tr.span.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t = Real.exp (s.x i (.z p)) * a * Real.exp (-a * (t - s.time))) := by
    refine tr.span.allFlows_mono ?_ (tr.span.allFlows_and hraw (tr.span.allFlows_and hothers hconst))
    intro v w f hf t ht
    unfold tailDrive
    rw [Finset.sum_eq_single p]
    · simp only [hf.2.2 t ⟨ht.1,ht.2.le⟩,rawTail,hf.1,mul_assoc]
    · intro q _ hq; simp [rawTail,hf.2.1 q hq]
    · simp
  have hm := tr.span.allStates_main_flows i .ready tr.ready_states
  have hu := tr.span.ready_drive_upper i hm (s.x i .q) (Real.exp (s.x i (.z p))) s.time
    (by rw [readyPulse_initial]) (tr.span.allFlows_mono (fun f hf t ht => (hf t ht).le) hdrive)
  have hl := tr.span.ready_drive_lower i hm (s.x i .q) (Real.exp (s.x i (.z p))) s.time
    (by rw [readyPulse_initial]) (tr.span.allFlows_mono (fun f hf t ht => (hf t ht).ge) hdrive)
  have he := le_antisymm hl hu
  have hq : tr.beforeFire.x i .q = 1 := by simpa only [tr.entry.physical_continuous] using tr.charge
  simpa only [hq] using he

theorem response_derivative_lower {t : ℝ} (ht : 0 ≤ t) (hu : t ≤ 9 / 10) :
    (1 / 60 : ℝ) ≤ a * Real.exp (-a * t) - (1 / 2) * response t := by
  have ha : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have htail : Real.exp (-a * (9 / 10)) = (1 / 4) * Real.exp (a / 10) := by
    rw [show -a * (9 / 10) = -a + a / 10 by ring,Real.exp_add,exp_neg_a]
  have hex : (569 / 2000 : ℝ) ≤ Real.exp (-a * t) := by
    have hmono : Real.exp (-a * (9 / 10)) ≤ Real.exp (-a * t) :=
      Real.exp_le_exp.mpr (by nlinarith [a_coarse_bounds.1])
    rw [htail] at hmono
    linarith [Real.add_one_le_exp (a / 10)]
  have hprod := mul_le_mul ha hex (by norm_num : (0 : ℝ) ≤ 569 / 2000) (by linarith : 0 ≤ a)
  linarith [response_global_upper ht]

theorem readyPulse_mono_initial {initial final amplitude start t : ℝ} (hi : initial ≤ final) :
    readyPulse initial amplitude start t ≤ readyPulse final amplitude start t := by
  have h := mul_le_mul_of_nonneg_right hi (Real.exp_pos (-(1 / 2 : ℝ) * (t - start))).le
  unfold readyPulse
  nlinarith

theorem readyPulse_strictMono {initial amplitude start : ℝ}
    (hi : initial ≤ 7 / 50) (ha : 9 / 5 ≤ amplitude) :
    StrictMonoOn (readyPulse initial amplitude start) (Icc start (start + 9 / 10)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t _ => (readyPulse_derivative initial amplitude start t).continuousAt.continuousWithinAt)
  intro t ht
  have hcc := interior_subset ht
  have hd : 0 ≤ t - start := sub_nonneg.mpr hcc.1
  have hdu : t - start ≤ 9 / 10 := by linarith [hcc.2]
  rw [(readyPulse_derivative initial amplitude start t).deriv]
  have hcarry := decay_upper (show initial - 1 / 10 ≤ (1 / 25 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hresponse := response_derivative_lower hd hdu
  have hprod := mul_le_mul ha hresponse (by norm_num : (0 : ℝ) ≤ 1 / 60) (by linarith : 0 ≤ amplitude)
  dsimp [readyPulse]
  nlinarith

theorem readyPulse_root_unique {initial amplitude start t v : ℝ}
    (hi : initial ≤ 7 / 50) (ha : 9 / 5 ≤ amplitude)
    (ht : t ∈ Icc start (start + 9 / 10)) (hv : v ∈ Icc start (start + 9 / 10))
    (hqt : readyPulse initial amplitude start t = 1) (hqv : readyPulse initial amplitude start v = 1) :
    t = v := (readyPulse_strictMono hi ha).injOn ht hv (hqt.trans hqv.symm)

/-- A positive residual advances the first firing relative to a rest-started
reference with the same physical gain; it does not retime any input event. -/
theorem first_firing_le_rest_reference {initial amplitude start first rest : ℝ}
    (hi : 1 / 10 ≤ initial) (ha : 9 / 5 ≤ amplitude)
    (hf : first ∈ Icc start (start + 9 / 10)) (hr : rest ∈ Icc start (start + 9 / 10))
    (hqf : readyPulse initial amplitude start first = 1)
    (hqr : readyPulse (1 / 10) amplitude start rest = 1) : first ≤ rest := by
  by_contra h
  have hlt := readyPulse_strictMono (by norm_num : (1 / 10 : ℝ) ≤ 7 / 50) ha hr hf (lt_of_not_ge h)
  rw [hqr] at hlt
  have hm := readyPulse_mono_initial (amplitude := amplitude) (start := start) (t := first) hi
  rw [hqf] at hm
  linarith

end KernelR.Hybrid
