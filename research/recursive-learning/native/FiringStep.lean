import Refractory

/-! A training pulse that makes the cell fire. The FIRE happens while the
pulsed sensor is SILENT. The sensor then goes through its ERROR phase
while the main cell is refractory, so no gain is written. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- The first time a continuous quantity reaches a level it starts below. -/
theorem first_hit {f : ℝ → ℝ} {start deadline level : ℝ} (hf : Continuous f)
    (ht : start ≤ deadline) (hlo : f start < level) (hhi : level ≤ f deadline) :
    ∃ root, start < root ∧ root ≤ deadline ∧ f root = level ∧
      ∀ t ∈ Ico start root, f t < level := by
  obtain ⟨w, hw, hvalue⟩ := intermediate_value_Icc ht hf.continuousOn ⟨hlo.le, hhi⟩
  have hcompact : IsCompact (Icc start deadline ∩ f ⁻¹' {level}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  have hnonempty : (Icc start deadline ∩ f ⁻¹' {level}).Nonempty :=
    ⟨w, hw, by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hvalue⟩
  obtain ⟨root, hroot⟩ := hcompact.exists_isLeast hnonempty
  have hmem : root ∈ Icc start deadline := hroot.1.1
  have hvalue : f root = level := hroot.1.2
  have hstart : start < root := by
    by_contra hn
    have heq : root = start := le_antisymm (le_of_not_gt hn) hmem.1
    rw [heq] at hvalue
    linarith
  refine ⟨root, hstart, hmem.2, hvalue, ?_⟩
  intro t ht'
  by_contra hn
  obtain ⟨earlier, hearlier, hcross⟩ := intermediate_value_Icc ht'.1 hf.continuousOn
    ⟨hlo.le, le_of_not_gt hn⟩
  have hleast : root ≤ earlier :=
    hroot.2 ⟨⟨hearlier.1, hearlier.2.trans (ht'.2.le.trans hmem.2)⟩, hcross⟩
  linarith [hearlier.2, ht'.2]

/-- Executions of the parameterized semantics keep the physical bounds. -/
theorem ParameterExecution.physical_invariant {n θ ε route} {s u : Snapshot n}
    (e : ParameterExecution θ route s u) (bounds : ParameterThresholdBounds θ)
    (box : @PhysicalBox n θ ε) (hs : ParameterPhysicalInvariant θ s) :
    ParameterPhysicalInvariant θ u := by
  induction e with
  | nil _ => exact hs
  | cons move _ ih =>
    cases move with
    | flow f =>
      have h := f.invariant_at bounds box hs (t := _) ⟨f.positive.le, le_rfl⟩
      rw [f.at_final] at h
      exact ih h
    | jump j => exact ih (j.physical_invariant hs)

theorem low_threshold_bounds {θ : Fin 1 → Parameters} {p upper lower level}
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20) (entry : 0 ≤ upper) (exit : 0 ≤ lower) :
    ParameterThresholdBounds θ := by
  constructor
  · intro i
    rw [Subsingleton.elim i 0, config]
    change level ≤ 11 / 10
    linarith [fire.2]
  · intro i
    rw [Subsingleton.elim i 0, config]
    norm_num [trainingThresholds]
  · intro i
    rw [Subsingleton.elim i 0, config]
    change (1 / 4 : ℝ) < level
    linarith [fire.1]
  · intro i
    rw [Subsingleton.elim i 0, config]
    norm_num [trainingThresholds]
  · intro i q
    rw [Subsingleton.elim i 0, config]
    norm_num [trainingThresholds]
  · intro i q
    rw [Subsingleton.elim i 0, config]
    norm_num [trainingThresholds]
  · intro i q
    rw [Subsingleton.elim i 0, config]
    by_cases h : q = p
    · subst q
      simp only [trainingThresholds, Function.update_self]
      exact entry
    · norm_num [trainingThresholds, Function.update_of_ne h]
  · intro i q
    rw [Subsingleton.elim i 0, config]
    by_cases h : q = p
    · subst q
      simp only [trainingThresholds, Function.update_self]
      exact exit
    · norm_num [trainingThresholds, Function.update_of_ne h]

theorem RestState.physical {θ : Fin 1 → Parameters} {s : Snapshot 1} (h : RestState θ s) :
    ParameterPhysicalInvariant θ s := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; rw [Subsingleton.elim i 0]; exact h.charge.2.trans (by norm_num)
  · intro i q; rw [Subsingleton.elim i 0]; exact (h.sensors q).2.trans (by norm_num)
  · intro i q; rw [Subsingleton.elim i 0]; exact h.caps q
  · intro i; rw [Subsingleton.elim i 0]; exact h.recovery
  · intro i; rw [Subsingleton.elim i 0]; exact h.energy

theorem rest_gain_bound {θ ε} {s : Snapshot 1} (box : @PhysicalBox 1 θ ε)
    (state : RestState θ s) (p : Port) : Real.exp (s.x 0 (.z p)) ≤ 22 / 5 := by
  have cap := (box.2 0 p).1.2
  change (θ 0).cap p ≤ 4 * (1 + ε) at cap
  have h := Real.exp_le_exp.mpr (state.caps p)
  rw [Real.exp_log (box.cap_positive 0 p)] at h
  linarith [box.epsilon_bounds.2]

/-- No pulse on a rested cell brings the main charge above 18/25 within
its first tenth of a unit, whatever the gain. -/
theorem rest_pulse_start {θ ε} {s : Snapshot 1} (box : @PhysicalBox 1 θ ε)
    (state : RestState θ s) (p : Port) :
    ∀ t, s.time ≤ t → t ≤ s.time + 1 / 10 →
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t ≤ 18 / 25 := by
  intro t h₀ h₁
  have resp := response_upper (sub_nonneg.mpr h₀)
  have respPos := response_nonnegative (sub_nonneg.mpr h₀)
  have small : response (t - s.time) ≤ 7 / 50 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr a_coarse_bounds.2.le) (sub_nonneg.mpr h₀),
      a_coarse_bounds.1]
  have drive := mul_le_mul (rest_gain_bound box state p) small respPos (by norm_num)
  have decay := decay_upper (show s.x 0 .q - 1 / 10 ≤ 1 / 10000 by linarith [state.charge.2])
    (by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (sub_nonneg.mpr h₀)
  dsimp only [readyPulse]
  linarith

/-- FAST lasts at most 21/20 units for a FIRE level between 19/20 and 21/20. -/
theorem fast_duration_bound {level : ℝ} (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20) :
    0 ≤ decayTime level (1 / 4) a ∧ decayTime level (1 / 4) a ≤ 21 / 20 := by
  have apos : 0 < a := by linarith [a_coarse_bounds.1]
  refine ⟨decayTime_nonneg (by norm_num) apos (by linarith [fire.1]), ?_⟩
  have form : level / (1 / 4) = 4 * level := by ring
  have la : Real.log 4 = a := rfl
  have small := Real.log_le_sub_one_of_pos (show 0 < level by linarith [fire.1])
  unfold decayTime
  rw [form, Real.log_mul (by norm_num) (by linarith [fire.1]), la, div_le_iff₀ apos]
  linarith [a_coarse_bounds.1]

/-- SLOW lasts between 6 and 100/7 units for a recovery rate between
7/100 and 1/10. -/
theorem slow_duration_bound {b : ℝ} (recovery : 7 / 100 ≤ b ∧ b ≤ 1 / 10) :
    6 ≤ decayTime (1 / 4) (1 / 10) b ∧ decayTime (1 / 4) (1 / 10) b ≤ 100 / 7 := by
  have bpos : 0 < b := by linarith [recovery.1]
  have form : (1 / 4 : ℝ) / (1 / 10) = 5 / 2 := by norm_num
  have lower := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 2 by norm_num)
  norm_num at lower
  have upper : Real.log (5 / 2) ≤ 1 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith [Real.exp_one_gt_d9])
  unfold decayTime
  rw [form]
  exact ⟨(le_div_iff₀ bpos).2 (by linarith [recovery.2]),
    (div_le_iff₀ bpos).2 (by linarith [recovery.1])⟩

/-- The ERROR phase lasts less than 3/8 of a unit. -/
theorem error_duration_bound {θ ε} (box : @PhysicalBox 1 θ ε) (p : Port) {upper lower : ℝ}
    (bounds : 1 / 200 ≤ lower ∧ lower < upper ∧ upper ≤ 2 / 25) :
    0 ≤ decayTime upper lower ((θ 0).le p) ∧ decayTime upper lower ((θ 0).le p) < 3 / 8 := by
  obtain ⟨lowerFloor, above, upperBound⟩ := bounds
  have lowerPos : 0 < lower := by linarith
  have rpos : 0 < (θ 0).le p := (box.rates_positive 0 p).2.2
  refine ⟨decayTime_nonneg lowerPos rpos above.le, ?_⟩
  have param := ((box.2 0 p).2.2.2.1).1
  change a / (3 / 20) * (1 - ε) ≤ (θ 0).le p at param
  have rlower : (8 : ℝ) ≤ (θ 0).le p := by
    have bound := mul_le_mul (show (4 / 3 : ℝ) / (3 / 20) ≤ a / (3 / 20) by
      dsimp [a]; linarith [KernelR.log_four_bounds.1]) (show (9 / 10 : ℝ) ≤ 1 - ε by
        linarith [box.epsilon_bounds.2]) (by norm_num) (by linarith [a_coarse_bounds.1])
    norm_num at bound
    exact bound.trans param
  have ratio : 1 < upper / lower := (lt_div_iff₀ lowerPos).2 (by linarith)
  have rat : upper / lower ≤ 16 := (div_le_iff₀ lowerPos).2 (by linarith)
  have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 8
  norm_num [Finset.sum_range_succ] at series
  have expBound : (16 : ℝ) < Real.exp 3 := by linarith
  have logBound := (Real.log_lt_iff_lt_exp (zero_lt_one.trans ratio)).2 (rat.trans_lt expBound)
  unfold decayTime
  exact (div_lt_iff₀ rpos).2 (by linarith)

/-- One firing training step. A pulse that brings the main charge of a
rested cell to its realized FIRE level makes the cell fire, and the cell
returns to rest with every gain and the recovery rate unchanged. Its main
charge is then exactly at its rest value. -/
theorem firing_step_exists {θ ε s p upper lower level rest} {later : List (Delivery 1)}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25) (exit : 1 / 200 ≤ lower ∧ lower < upper)
    (state : RestState θ s) (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending = (⟨0, p, s.time⟩ : Delivery 1) :: later)
    (wait : s.time + 22 ≤ rest) (laterDue : ∀ d ∈ later, rest ≤ d.due)
    (fires : ∃ t ∈ Icc s.time (s.time + 1),
      level ≤ readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t) :
    ∃ u, Runs θ s u 1 ∧ RestState θ u ∧ u.time = rest ∧
      u.pending = later ∧ (∀ q, u.x 0 (.z q) = s.x 0 (.z q)) ∧ u.x 0 .b = s.x 0 .b ∧
      u.x 0 .q = 1 / 10 := by
  -- The first contact with the FIRE level.
  let pulse := fun t => readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t
  have pulseCont : Continuous pulse := by
    dsimp only [pulse, readyPulse, response]
    fun_prop
  obtain ⟨t₁, ht₁, high⟩ := fires
  have early := rest_pulse_start box state p
  have startLow : pulse s.time < level :=
    lt_of_le_of_lt (early s.time le_rfl (by linarith)) (by linarith [fire.1])
  obtain ⟨tf, after, before, hit, first⟩ := first_hit pulseCont ht₁.1 startLow high
  have late : s.time + 1 / 10 < tf := by
    by_contra h
    have bound := early tf after.le (not_lt.mp h)
    have bound' : level ≤ 18 / 25 := by
      rw [← hit]
      exact bound
    linarith [fire.1]
  have tfLe : tf ≤ s.time + 1 := before.trans ht₁.2
  -- Admission, MARK and SILENT entry.
  let d : Delivery 1 := ⟨0, p, s.time⟩
  let admitted : Snapshot 1 := { (setRaw s d.cell d.port (some s.time)) with pending := [] ++ later }
  let arrive : ParameterJump θ (fun _ _ => []) s admitted :=
    .arrive s d [] later queue rfl (state.raw p)
  have gainBound := rest_gain_bound box state p
  have start : ∀ t, admitted.time ≤ t → t ≤ admitted.time + 1 / 10 →
      readyPulse (admitted.x 0 .q) (Real.exp (admitted.x 0 (.z p))) admitted.time t < 1 :=
    fun t h₀ h₁ => lt_of_le_of_lt (early t h₀ h₁) (by norm_num)
  have physical : PhysicalInvariant θ admitted := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [Subsingleton.elim i 0]
      refine ⟨state.recovery.1, state.charge.2.trans (by norm_num), fun q => ?_⟩
      rw [show admitted.aux 0 q = .ready from state.aux q]
      exact le_of_lt (lt_of_le_of_lt (state.sensors q).2 (by norm_num [auxUpper]))
    · intro i q; rw [Subsingleton.elim i 0]; exact state.caps q
    · intro i; rw [Subsingleton.elim i 0]; exact state.recovery.2
    · intro i; rw [Subsingleton.elim i 0]; exact state.energy
  have rawA : admitted.raw 0 p = some admitted.time := by simp [admitted, setRaw, d]
  have otherRawA (i : Fin 1) (q : Port) (h : i ≠ 0 ∨ q ≠ p) : admitted.raw i q = none := by
    have hi : i = 0 := Subsingleton.elim _ _
    have hq := h.resolve_left (not_not_intro hi)
    subst hi
    exact (raw_update_other s 0 p (some s.time) 0 q (Or.inr hq)).trans (state.raw q)
  have ahead : ∀ v ∈ admitted.pending, rest ≤ v.due :=
    fun v hv => laterDue v (by simpa [admitted] using hv)
  obtain ⟨mk⟩ := first_input_mark_of_response_margin_until_exists admitted box 0 p
    (fun i => by rw [Subsingleton.elim i 0]; exact state.main)
    (fun i q => by rw [Subsingleton.elim i 0]; exact state.aux q)
    rawA otherRawA
    (fun i => by rw [Subsingleton.elim i 0]; exact state.charge.2.trans_lt (by norm_num))
    (fun i q => by
      rw [Subsingleton.elim i 0]
      exact lt_of_le_of_lt (state.sensors q).2 (by norm_num))
    start (state.sensors p)
    (by
      intro v hv
      have h := ahead v hv
      change s.time + 1 / 40 ≤ v.due
      linarith)
  obtain ⟨g⟩ := mk.first_silent_of_response_margin_until_exists box start
    (by
      intro v hv
      have h := ahead v hv
      change s.time + 1 / 10 ≤ v.due
      linarith)
  have gAfter : s.time ≤ g.final.time := by
    change s.time ≤ s.time + mk.latency + Real.log (5 / 4) / (θ 0).lm p
    linarith [mk.early, (box.aux_durations_positive 0 p).1]
  have gBefore : g.final.time < s.time + 1 / 20 := g.deadline
  have preMark : ∀ t ∈ Ico admitted.time (admitted.time + mk.latency),
      mk.flow.path t 0 .q < level := by
    intro t ht
    have eq := mk.flow.ready_single_pulse_solution 0 p admitted.time (mk.main_ready 0) rawA
      (fun q h => otherRawA 0 q (Or.inr h)) (by rw [mk.aux_ready]; decide) t ⟨ht.1, ht.2.le⟩
    rw [eq]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    have h₁ : t < s.time + mk.latency := ht.2
    exact first t ⟨ht.1, by linarith [mk.deadline]⟩
  have preSilent : ∀ t ∈ Ico mk.final.time g.final.time, g.flow.path t 0 .q < level := by
    intro t ht
    have hm : mk.final.aux 0 p = .mark := by simp [FirstInputMark.final, setAux]
    have eq := g.flow.ready_single_pulse_solution 0 p admitted.time (mk.main_ready 0) mk.raw_active
      (fun q h => mk.raw_other 0 q (Or.inr h)) (by rw [hm]; decide) t ⟨ht.1, ht.2.le⟩
    rw [eq]
    have restart := mk.protected_response_restart t
    change readyPulse (mk.final.x 0 .q)
      (Real.exp (mk.final.x 0 (.z p)) * Real.exp (-a * (mk.final.time - admitted.time)))
      mk.final.time t = _ at restart
    rw [restart]
    have ht' : s.time ≤ t := by
      have h : s.time + mk.latency ≤ t := ht.1
      linarith [mk.early]
    have h₂ : t < g.final.time := ht.2
    exact first t ⟨ht', by linarith⟩
  -- The SILENT leg up to the FIRE.
  have rp : 0 < (θ 0).ls p := (box.rates_positive 0 p).2.1
  obtain ⟨long, short⟩ := low_entry_silent_duration box p entry
  have long' : 1 < decayTime (4 / 5) upper ((θ 0).ls p) := long
  have short' : decayTime (4 / 5) upper ((θ 0).ls p) ≤ 31 / 20 := short
  have up : 0 < upper := by linarith [entry.1]
  obtain ⟨_, _, sensorStrict⟩ :=
    protected_decay_schedule up (show upper < (4 / 5 : ℝ) by linarith [entry.2]) rp
  have above (t : ℝ) (hs : g.final.time ≤ t) (ht : t ≤ s.time + 1) :
      upper < (4 / 5 : ℝ) * Real.exp (-(θ 0).ls p * (t - g.final.time)) := by
    apply sensorStrict _ (sub_nonneg.mpr hs)
    linarith
  have restSilent (q : Port) (hq : q ≠ p) : RestBand (g.final.x 0 (.m q)) := by
    have h₁ : mk.final.x 0 (.m q) =
        relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time (s.time + mk.latency) :=
      readyInputValues_other hq
    have h₂ : g.final.x 0 (.m q) =
        relax (1 / 2) (1 / 40) (mk.final.x 0 (.m q)) mk.final.time mk.silentDate :=
      readyProtectedValues_other (origin := some s.time) hq
    rw [h₂, h₁]
    refine relax_restBand ?_ (relax_restBand (by linarith [mk.early]) (state.sensors q))
    change s.time + mk.latency ≤ s.time + mk.latency + Real.log (5 / 4) / (θ 0).lm p
    linarith [(box.aux_durations_positive 0 p).1]
  have rawCharge (t : ℝ) :
      readyProtectedValues θ g.final 0 p .silent (some s.time) t 0 .q = pulse t := by
    simp only [readyProtectedValues, protectedRawAmplitude, ite_true]
    exact g.response_restart t
  have silentEnergy := ((g.execution (fun _ _ => [])).physical_invariant box physical).reserve 0
  have gtf : g.final.time < tf := by linarith
  obtain ⟨leg⟩ := silent_leg_of_margin (s := g.final) (p := p) (origin := some s.time)
    (upper := upper) (level := level) (stop := tf) box gtf
    g.main_ready g.aux_silent g.aux_other
    (fun q hq => lt_of_le_of_lt (restSilent q hq).2 (by norm_num)) g.raw_active g.raw_other
    (by intro o h; obtain rfl := (Option.some.inj h).symm; exact ⟨gAfter, tfLe⟩)
    (by
      intro v hv
      have h := ahead v (show v ∈ admitted.pending from hv)
      linarith)
    (fun t ht => by rw [rawCharge t]; exact first t ⟨gAfter.trans ht.1, ht.2⟩)
    (by
      intro t ht
      simp only [readyProtectedValues, and_self, ite_true, protectedReadyRate, g.sensor_charge]
      exact above t ht.1 (by linarith [ht.2]))
    (by rw [g.sensor_charge]; norm_num) (by rw [g.gain_preserved]; exact gainBound) silentEnergy
  -- The FIRE.
  let edge := readyProtectedEnd θ g.final 0 p .silent (some s.time) tf
  have edgeCharge : edge.x 0 .q = level := (rawCharge tf).trans hit
  have edgeSensor : edge.x 0 (.m p) =
      (4 / 5 : ℝ) * Real.exp (-(θ 0).ls p * (tf - g.final.time)) := by
    simp [edge, readyProtectedEnd, readyProtectedValues, protectedReadyRate, g.sensor_charge]
  have edgeOther (q : Port) (hq : q ≠ p) : RestBand (edge.x 0 (.m q)) := by
    have value : edge.x 0 (.m q) =
        relax (1 / 2) (1 / 40) (g.final.x 0 (.m q)) g.final.time tf :=
      readyProtectedValues_other (origin := some s.time) hq
    rw [value]
    exact relax_restBand gtf.le (restSilent q hq)
  let fired : Snapshot 1 := { (setMain edge 0 .fast) with
    pending := edge.pending ++ (fun (_ : Fin 1) (_ : ℝ) => ([] : List (Delivery 1))) 0 edge.time }
  let fireJump : ParameterJump θ (fun _ _ => []) edge fired :=
    .fire edge 0 (g.main_ready 0) (by rw [config]; exact edgeCharge)
  have thrFast : (θ 0).thresholds.fastEnd = 1 / 4 := by rw [config]; rfl
  have thrReopen : (θ 0).thresholds.reopen = 1 / 10 := by rw [config]; rfl
  have thrMark (q : Port) : (θ 0).thresholds.mark q = 1 := by rw [config]; rfl
  have thrErrorP : (θ 0).thresholds.error p = upper := by
    rw [config]; simp [trainingThresholds]
  have thrErrorO (q : Port) (h : q ≠ p) : (θ 0).thresholds.error q = 1 / 10 := by
    rw [config]; simp [trainingThresholds, Function.update_of_ne h]
  have thrReadyP : (θ 0).thresholds.auxReady p = lower := by
    rw [config]; simp [trainingThresholds]
  have thrReadyO (q : Port) (h : q ≠ p) : (θ 0).thresholds.auxReady q = 1 / 40 := by
    rw [config]; simp [trainingThresholds, Function.update_of_ne h]
  have firedMain : fired.main 0 = .fast := by simp [fired, setMain]
  have firedAuxP : fired.aux 0 p = .silent := g.aux_silent
  have firedAuxO (q : Port) (h : q ≠ p) : fired.aux 0 q = .ready := g.aux_other 0 q (Or.inr h)
  have firedRawP : fired.raw 0 p = some s.time := g.raw_active
  have firedRawO (q : Port) (h : q ≠ p) : fired.raw 0 q = none := g.raw_other 0 q (Or.inr h)
  have firedCharge : fired.x 0 .q = level := edgeCharge
  have firedB : fired.x 0 .b = s.x 0 .b := rfl
  have firedSensor : fired.x 0 (.m p) =
      (4 / 5 : ℝ) * Real.exp (-(θ 0).ls p * (tf - g.final.time)) := edgeSensor
  have firedTime : fired.time = tf := rfl
  have firedPending : ∀ v ∈ fired.pending, v ∈ later := by
    intro v hv
    have hv' : v ∈ ([] ++ later) ++ ([] : List (Delivery 1)) := hv
    simpa using hv'
  have sched : Scheduled θ fired := {
    refractory := ⟨by rw [firedMain]; decide,
      fun q => by
        by_cases h : q = p
        · subst q; rw [firedAuxP]; decide
        · rw [firedAuxO q h]; decide,
      fun q hr => by
        by_cases h : q = p
        · subst q; rw [firedAuxP] at hr; cases hr
        · exact firedRawO q h⟩
    main_levels := by rw [thrReopen, thrFast]; norm_num
    levels := fun q => by
      by_cases h : q = p
      · subst q
        rw [thrReadyP, thrErrorP, thrMark]
        exact ⟨by linarith [exit.1], exit.2.le, by linarith [entry.2], le_rfl⟩
      · rw [thrReadyO q h, thrErrorO q h, thrMark]
        norm_num
    recovery := by rw [firedB]; linarith [recovery.1]
    fast := fun _ => by rw [thrFast, firedCharge]; linarith [fire.1]
    slow := fun h => by rw [firedMain] at h; cases h
    ready := fun q hr => by
      by_cases h : q = p
      · subst q; rw [firedAuxP] at hr; cases hr
      · exact lt_of_le_of_lt (edgeOther q h).2 (by norm_num)
    silent := fun q hr => by
      by_cases h : q = p
      · subst q
        rw [thrErrorP, firedSensor]
        exact (above tf gtf.le tfLe).le
      · rw [firedAuxO q h] at hr; cases hr
    error := fun q hr => by
      by_cases h : q = p
      · subst q; rw [firedAuxP] at hr; cases hr
      · rw [firedAuxO q h] at hr; cases hr
    raw := fun q o h => by
      by_cases hq : q = p
      · subst q
        rw [firedRawP] at h
        obtain rfl := Option.some.inj h
        exact ⟨after.le, tfLe⟩
      · rw [firedRawO q hq] at h; cases h }
  have fastT := fast_duration_bound fire
  have slowT := slow_duration_bound recovery
  have errT := error_duration_bound box p ⟨exit.1, exit.2, entry.2⟩
  have reopenEq : mainReopen θ fired =
      tf + decayTime level (1 / 4) a + decayTime (1 / 4) (1 / 10) (s.x 0 .b) := by
    rw [mainReopen_fast firedMain, mainNext_fast firedMain, thrFast, thrReopen, firedCharge,
      firedB, firedTime]
  have silentShift : decayTime (fired.x 0 (.m p)) upper ((θ 0).ls p) =
      decayTime (4 / 5) upper ((θ 0).ls p) - (tf - g.final.time) := by
    rw [firedSensor]
    exact decayTime_shift (by norm_num) up rp _
  have readyEq : sensorReady θ fired p = g.final.time + decayTime (4 / 5) upper ((θ 0).ls p) +
      decayTime upper lower ((θ 0).le p) := by
    rw [sensorReady_silent firedAuxP, sensorNext_silent firedAuxP, thrErrorP, thrReadyP,
      silentShift, firedTime]
    ring
  have ord : Ordered θ fired := {
    sensor := fun q hq => by
      by_cases h : q = p
      · subst q
        rw [readyEq, reopenEq]
        linarith [fastT.1, slowT.1, errT.2]
      · exact absurd (firedAuxO q h) hq
    raw := fun q o h => by
      by_cases hq : q = p
      · subst q
        rw [firedRawP] at h
        obtain rfl := Option.some.inj h
        rw [readyEq, reopenEq]
        constructor
        · linarith [fastT.1, slowT.1]
        · linarith [errT.1]
      · rw [firedRawO q hq] at h; cases h
    pending := fun v hv => by
      rw [reopenEq]
      have h := laterDue v (firedPending v hv)
      linarith [fastT.2, slowT.2] }
  -- The refractory period, then the quiet wait.
  obtain ⟨u₁, run, fin⟩ := refractory_run_exists box fired sched ord
  have time₁ : u₁.time = mainReopen θ fired := fin.time
  have charge₁ : u₁.x 0 .q = 1 / 10 := fin.charge.trans thrReopen
  have reopenLate : mainReopen θ fired < rest := by
    rw [reopenEq]
    linarith [fastT.2, slowT.2]
  have readyBefore : sensorReady θ fired p < mainReopen θ fired :=
    ord.sensor p (by rw [firedAuxP]; decide)
  have firedBefore : fired.time ≤ mainReopen θ fired :=
    (sched.dates box).1.trans (sched.dates box).2.1
  have sensor₁ (q : Port) : u₁.x 0 (.m q) < 1 := by
    rw [fin.sensors q]
    by_cases h : q = p
    · subst q
      rw [restSensor_busy (by rw [firedAuxP]; decide), thrReadyP]
      exact relax_lt_one readyBefore.le (by linarith [exit.2, entry.2])
    · rw [restSensor_ready (firedAuxO q h)]
      exact lt_of_le_of_lt (relax_restBand firedBefore (edgeOther q h)).2 (by norm_num)
  let u := quietAt u₁ rest
  have stopRest : u₁.time < rest := by rw [time₁]; exact reopenLate
  have waitFlow : ParameterFlow θ u₁ u := {
    toFlowDynamics := quietDynamics u₁ stopRest
      (fun i => by rw [Subsingleton.elim i 0]; exact fin.main)
      (fun i q => by rw [Subsingleton.elim i 0]; exact fin.aux q)
      (fun i q => by rw [Subsingleton.elim i 0]; exact fin.raw q)
      (fun v hv => laterDue v (firedPending v (fin.queue ▸ hv)))
    guards := by
      intro t ht
      have ht₁ : u₁.time ≤ t := ht.1
      apply guards_ready config fin.main
      · change relax (1 / 2) (1 / 10) (u₁.x 0 .q) u₁.time t < level
        rw [charge₁]
        have flat : relax (1 / 2) (1 / 10) (1 / 10) u₁.time t = 1 / 10 := by simp [relax]
        rw [flat]
        linarith [fire.1]
      · intro q
        have h : relax (1 / 2) (1 / 40) (u₁.x 0 (.m q)) u₁.time t < 1 :=
          relax_lt_one ht₁ (sensor₁ q)
        simp only [fin.aux q]
        exact h }
  have longWait : Real.exp (-(1 / 2) * (rest - sensorReady θ fired p)) ≤ 1 / 9500 := by
    refine (Real.exp_le_exp.mpr ?_).trans exp_neg_long_wait
    rw [readyEq]
    linarith [errT.2]
  have uCharge : u.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (u₁.x 0 .q) u₁.time rest = 1 / 10
    rw [charge₁]
    simp [relax]
  have uSensors (q : Port) : RestBand (u.x 0 (.m q)) := by
    change RestBand (relax (1 / 2) (1 / 40) (u₁.x 0 (.m q)) u₁.time rest)
    rw [fin.sensors q, time₁]
    by_cases h : q = p
    · subst q
      rw [restSensor_busy (by rw [firedAuxP]; decide), thrReadyP, relax_relax]
      have pos := Real.exp_pos (-(1 / 2) * (rest - sensorReady θ fired p))
      have hi := mul_le_mul (show lower - 1 / 40 ≤ 11 / 200 by linarith [exit.2, entry.2])
        longWait pos.le (by norm_num)
      have lo := mul_le_mul (show 1 / 40 - lower ≤ 11 / 200 by linarith [exit.1])
        longWait pos.le (by norm_num)
      refine ⟨?_, ?_⟩ <;> dsimp only [relax] <;> linarith
    · rw [restSensor_ready (firedAuxO q h), relax_relax]
      exact relax_restBand (show tf ≤ rest by linarith) (edgeOther q h)
  have bounds := low_threshold_bounds config fire (by linarith [entry.1]) (by linarith [exit.1])
  have counted : Runs θ s u 1 :=
    (Runs.jump arrive rfl).append ((runs_mark_silent g config preMark preSilent).append
      ((Runs.flow (parameterSilentLeg leg config)).append ((Runs.jump fireJump rfl).append
        (run.append (Runs.flow waitFlow)))))
  obtain ⟨whole, _⟩ := id counted
  have inv := ParameterExecution.physical_invariant whole bounds box state.physical
  have uB : u.x 0 .b = s.x 0 .b := fin.recovery.trans firedB
  have uGains (q : Port) : u.x 0 (.z q) = s.x 0 (.z q) := fin.gains q
  refine ⟨u, counted, ⟨fin.main, fin.aux, fin.raw, ⟨uCharge.ge, uCharge.le.trans (by norm_num)⟩,
    uSensors, ?_, inv.reserve 0, ?_⟩, rfl, ?_, uGains, uB, uCharge⟩
  · rw [uB]
    exact ⟨by linarith [recovery.1], by linarith [recovery.2]⟩
  · intro q
    rw [uGains q]
    exact state.caps q
  · show u₁.pending = later
    rw [fin.queue]
    show ([] ++ later) ++ ([] : List (Delivery 1)) = later
    simp

end RecursiveLearning.Native
