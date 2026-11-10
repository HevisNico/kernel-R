import CoincidenceTiming

/-! After a trained read FIRE, the pulse ends before FAST can end.
Later READY intervals have no drive and begin below FIRE. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

private theorem ParameterFlow.fast_solution {n θ s u} (f : @ParameterFlow n θ s u) (i : Fin n)
    (hm : s.main i = .fast) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i .q = s.x i .q * Real.exp (-a * (t - s.time)) := by
  have hi : ∀ t ∈ Icc s.time u.time,
      f.path t i .q = f.path s.time i .q + ∫ v in s.time..t, -a * f.path v i .q := by
    intro t ht
    simpa [f.initial, field, hm] using f.integral_eq t ht i .q
  simpa only [f.initial] using decay_of_integral (f.continuous i .q) hi

private theorem ParameterFlow.ready_no_current_solution {n θ s u} (f : @ParameterFlow n θ s u) (i : Fin n)
    (hm : s.main i = .ready) (hr : ∀ p, s.raw i p = none) :
    ∀ t ∈ Icc s.time u.time, f.path t i .q =
      1 / 10 + (s.x i .q - 1 / 10) * Real.exp (-(1 / 2) * (t - s.time)) := by
  let y : ℝ → ℝ := fun t => f.path t i .q - 1 / 10
  have hd (v : ℝ) : field θ s (f.path v) v i .q = -(1 / 2) * y v := by
    simp [field, hm, drive, current, hr, y]
    ring
  have hi : ∀ t ∈ Icc s.time u.time,
      y t = y s.time + ∫ v in s.time..t, -(1 / 2) * y v := by
    intro t ht
    have h := f.integral_eq t ht i .q
    simp_rw [hd] at h
    dsimp [y]; rw [f.initial]
    linarith
  have h := decay_of_integral ((f.continuous i .q).sub continuousOn_const) hi
  intro t ht
  have he := h t ht
  dsimp [y] at he
  rw [f.initial] at he
  linarith

private def ReadTailSafe (θ : Fin 1 → Parameters) (p : Port)
    (origin fireTime : ℝ) (s : Snapshot 1) : Prop :=
  s.pending = [] ∧
    ((s.main 0 = .fast ∧
      (∀ q, s.raw 0 q = if q = p then some origin else none) ∧
      s.time ≤ origin + 1 ∧
      s.x 0 .q = (θ 0).thresholds.fire * Real.exp (-a * (s.time - fireTime))) ∨
    ((∀ q, s.raw 0 q = none) ∧
      (s.main 0 = .ready → s.x 0 .q < (θ 0).thresholds.fire)))

private theorem fast_through_pulse {level origin fireTime t : ℝ}
    (floor : 19 / 20 ≤ level) (fireLate : origin + 3 / 10 ≤ fireTime)
    (tBound : t ≤ origin + 1) :
    1 / 4 < level * Real.exp (-a * (t - fireTime)) := by
  have aPos : 0 < a := a_coarse_bounds.1.trans' (by norm_num)
  have expo : -a * (7 / 10) ≤ -a * (t - fireTime) := by
    have h : t - fireTime ≤ 7 / 10 := by linarith
    nlinarith [mul_nonneg aPos.le (sub_nonneg.mpr h)]
  have expFloor : (7 / 20 : ℝ) ≤ Real.exp (-a * (7 / 10)) := by
    rw [show -a * (7 / 10) = -a + a * (3 / 10) by ring, Real.exp_add, exp_neg_a]
    have h : (4 / 3 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
    linarith [Real.add_one_le_exp (a * (3 / 10))]
  have gain := mul_le_mul floor (expFloor.trans (Real.exp_le_exp.mpr expo))
    (by norm_num) (by linarith)
  linarith

private theorem ReadTailSafe.flow {θ p origin fireTime s u}
    (h : ReadTailSafe θ p origin fireTime s) (f : ParameterFlow θ s u)
    (floor : 19 / 20 ≤ (θ 0).thresholds.fire) :
    ReadTailSafe θ p origin fireTime u := by
  refine ⟨f.queue_fixed.trans h.1, ?_⟩
  rcases h.2 with ⟨fast, raw, _, q⟩ | ⟨raw, below⟩
  · have active : s.raw 0 p = some origin := by rw [raw]; simp
    left
    refine ⟨(congrFun f.main_fixed 0).trans fast, ?_, (f.raw_support 0 p origin active).2, ?_⟩
    · intro j
      rw [f.raw_fixed, raw]
    · rw [← f.final, ParameterFlow.fast_solution f 0 fast _ ⟨f.positive.le, le_rfl⟩, q,
        mul_assoc, ← Real.exp_add]
      congr 2
      ring
  · right
    refine ⟨by intro j; rw [f.raw_fixed]; exact raw j, ?_⟩
    intro ready
    have readyAtStart : s.main 0 = .ready := (congrFun f.main_fixed 0).symm.trans ready
    rw [← f.final, ParameterFlow.ready_no_current_solution f 0 readyAtStart raw _ ⟨f.positive.le, le_rfl⟩]
    exact relax_lt (by norm_num) f.positive.le (below readyAtStart) (by linarith)

private theorem ReadTailSafe.jump {θ p origin fireTime s u}
    (h : ReadTailSafe θ p origin fireTime s)
    (j : ParameterJump θ (fun _ _ => []) s u)
    (floor : 19 / 20 ≤ (θ 0).thresholds.fire)
    (fastEnd : (θ 0).thresholds.fastEnd = 1 / 4)
    (reopen : (θ 0).thresholds.reopen = 1 / 10)
    (fireLate : origin + 3 / 10 ≤ fireTime) :
    ReadTailSafe θ p origin fireTime u ∧ j.emissions = [] := by
  have notFire : s.main 0 = .ready → s.x 0 .q < (θ 0).thresholds.fire := by
    intro ready
    rcases h.2 with h | h
    · rw [h.1] at ready
      cases ready
    · exact h.2 ready
  cases j with
  | fire i mode hit =>
    have eq : i = 0 := Subsingleton.elim _ _
    subst i
    exact False.elim ((ne_of_lt (notFire mode)) hit)
  | fastEnd i mode hit =>
    have eq : i = 0 := Subsingleton.elim _ _
    subst i
    rcases h.2 with ⟨_, _, date, q⟩ | ⟨raw, _⟩
    · rw [fastEnd, q] at hit
      exact False.elim ((ne_of_gt (fast_through_pulse floor fireLate date)) hit)
    · exact ⟨⟨h.1, .inr ⟨raw, by simp [setMain]⟩⟩, rfl⟩
  | reopen i mode hit =>
    have eq : i = 0 := Subsingleton.elim _ _
    subst i
    rcases h.2 with ⟨hm, _, _, _⟩ | ⟨raw, _⟩
    · rw [hm] at mode
      cases mode
    · rw [reopen] at hit
      exact ⟨⟨h.1, .inr ⟨raw, fun _ => by change s.x 0 .q < _; linarith⟩⟩, rfl⟩
  | mark i q mode hit => exact ⟨h, rfl⟩
  | silent i q mode hit => exact ⟨h, rfl⟩
  | error i q mode hit => exact ⟨h, rfl⟩
  | auxReady i q mode hit => exact ⟨h, rfl⟩
  | arrive d before after queue due free =>
    rw [h.1] at queue
    have hlen := congrArg List.length queue
    simp at hlen
  | rawEnd i q t raw date =>
    have eq : i = 0 := Subsingleton.elim _ _
    subst i
    rcases h.2 with ⟨fast, only, _, _⟩ | ⟨none, _⟩
    · have qp : q = p := by
        by_contra neq
        simp [only, neq] at raw
      subst q
      refine ⟨⟨h.1, .inr ⟨?_, ?_⟩⟩, rfl⟩
      · intro q
        by_cases eq : q = p <;> simp [setRaw, eq, only]
      · intro ready
        change s.main 0 = .ready at ready
        rw [fast] at ready
        cases ready
    · simp [none] at raw

private theorem ReadTailSafe.no_emissions {θ : Fin 1 → Parameters} {s u : Snapshot 1}
    {p : Port} {origin fireTime : ℝ}
    (run : ParameterExecution θ (fun _ _ => []) s u)
    (initial : ReadTailSafe θ p origin fireTime s)
    (floor : 19 / 20 ≤ (θ 0).thresholds.fire)
    (fastEnd : (θ 0).thresholds.fastEnd = 1 / 4) (reopen : (θ 0).thresholds.reopen = 1 / 10)
    (fireLate : origin + 3 / 10 ≤ fireTime) : run.emissions = [] := by
  induction run with
  | nil => rfl
  | cons m rest ih =>
    cases m with
    | flow f => exact ih (initial.flow f floor)
    | jump j =>
      obtain ⟨next, labels⟩ := initial.jump j floor fastEnd reopen fireLate
      simp [ParameterExecution.emissions, labels, ih next]

/-- After the read's first FIRE, no subsequent legal finite continuation
emits again. The statement is independent of the chosen horizon. -/
theorem no_second_fire_after_trained_read {θ : Fin 1 → Parameters} {s u : Snapshot 1}
    {p : Port} {origin : ℝ}
    (run : ParameterExecution θ (fun _ _ => []) s u)
    (pending : s.pending = []) (fast : s.main 0 = .fast)
    (raw : ∀ q, s.raw 0 q = if q = p then some origin else none)
    (charge : s.x 0 .q = (θ 0).thresholds.fire)
    (fireLate : origin + 3 / 10 ≤ s.time) (fireLive : s.time ≤ origin + 1)
    (floor : 19 / 20 ≤ (θ 0).thresholds.fire)
    (fastEnd : (θ 0).thresholds.fastEnd = 1 / 4) (reopen : (θ 0).thresholds.reopen = 1 / 10) :
    run.emissions = [] := by
  have initial : ReadTailSafe θ p origin s.time s :=
    ⟨pending, .inl ⟨fast, raw, fireLive, by simpa using charge⟩⟩
  exact initial.no_emissions run floor fastEnd reopen fireLate

/-- A silent read stays silent once its last pulse has expired.
The auxiliary can still finish its ERROR phase. -/
theorem no_fire_after_silent_read_expiry {θ : Fin 1 → Parameters} {s u : Snapshot 1}
    (run : ParameterExecution θ (fun _ _ => []) s u)
    (pending : s.pending = []) (raw : ∀ q, s.raw 0 q = none)
    (subthreshold : s.main 0 = .ready → s.x 0 .q < (θ 0).thresholds.fire)
    (floor : 19 / 20 ≤ (θ 0).thresholds.fire)
    (fastEnd : (θ 0).thresholds.fastEnd = 1 / 4) (reopen : (θ 0).thresholds.reopen = 1 / 10) :
    run.emissions = [] := by
  have initial : ReadTailSafe θ 0 0 1 s := ⟨pending, .inr ⟨raw, subthreshold⟩⟩
  exact initial.no_emissions run floor fastEnd reopen (by norm_num)

/-- Apply the no-extra-report invariant to the actual trained read witness. -/
theorem TrainingRead.no_later_report {θ time gains p upper lower level delay u}
    (read : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (floor : 19 / 20 ≤ level)
    (tail : ParameterExecution θ (fun _ _ => []) read.handoff.decision.final u) :
    tail.emissions = [] := by
  let decision := read.handoff.decision
  have early := decision.outcome.1.le
  have late := decision.outcome.2.1.le
  have startQueue : read.handoff.readStart.pending = [] := read.handoff.ready_at_read.empty
  have raw (q : Port) : decision.final.raw 0 q =
      if q = p then some read.handoff.readStart.time else none := by
    by_cases eq : q = p
    · subst q
      simp only [TolerantSnapshotDecision.final, ite_true, setMain, readyProtectedEnd]
      exact decision.silent.raw_active
    · simp only [TolerantSnapshotDecision.final, ite_true, setMain, readyProtectedEnd, ite_eq_right eq]
      exact decision.silent.raw_other 0 q (Or.inr eq)
  apply no_second_fire_after_trained_read tail (p := p) (origin := read.handoff.readStart.time)
  · change decision.silent.final.pending = []
    rw [decision.silent.queue_preserved]
    exact startQueue
  · simp [TolerantSnapshotDecision.final, setMain]
  · exact raw
  · rw [config]
    exact decision.outcome.2.2.1
  · exact early
  · change decision.stop ≤ read.handoff.readStart.time + 1
    linarith
  · simpa [config, trainingThresholds] using floor
  · simp [config, trainingThresholds]
  · simp [config, trainingThresholds]

private theorem appended_emissions {θ : Fin 1 → Parameters} {s u v : Snapshot 1}
    (e : ParameterExecution θ (fun _ _ => []) s u)
    (tail : ParameterExecution θ (fun _ _ => []) u v) :
    (e.append tail).emissions = e.emissions ++ tail.emissions := by
  induction e with
  | nil => rfl
  | cons m r ih =>
    change (ParameterExecution.cons m (r.append tail)).emissions = _
    rw [ParameterExecution.emissions_cons, ParameterExecution.emissions_cons, ih, List.append_assoc]

/-- A completed extension of the constructed trained read has exactly its
original report, at any extension horizon. -/
theorem TrainingRead.complete_extension_reports {θ time gains p upper lower level delay u T}
    (read : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (floor : 19 / 20 ≤ level)
    (tail : ParameterExecution θ (fun _ _ => []) read.handoff.decision.final u)
    (done : ParameterCompleteThrough tail T) :
    let full := (read.parameterExecution config).append tail
    ParameterCompleteThrough full T ∧ full.emissionTimes 0 = [read.handoff.decision.stop] := by
  dsimp only
  refine ⟨done, ?_⟩
  have empty := read.no_later_report config floor tail
  have one := read.parameterEmissionTimes config
  unfold ParameterExecution.emissionTimes at one ⊢
  simpa only [appended_emissions, empty, List.append_nil] using one

end RecursiveLearning.Native
