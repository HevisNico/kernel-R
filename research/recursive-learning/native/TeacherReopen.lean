import SelectorPrecharge
import KernelR.Cadence
import KernelR.HybridSlowProtectedMarkFlowExistence
import KernelR.HybridContactRouterTransport
import KernelR.HybridFuture

/-! A work pulse scheduled by the teacher's own FIRE. The known FAST
duration cancels the firing date. Fabrication enters the SLOW clock only
through the short MARK deficit when the initial recovery is fixed. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

private theorem early_response_monotone : MonotoneOn response (Icc 0 (9 / 10)) := by
  apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_).monotoneOn
  · unfold response
    fun_prop
  · intro t ht
    have range := interior_subset ht
    rw [(response_derivative t).deriv]
    linarith [response_derivative_lower range.1 range.2]

private theorem sensor_response_bounds :
    response (9 / 500) ≤ 491 / 20000 ∧
    (17 / 625 ≤ response (1 / 50) ∧ response (1 / 50) ≤ 1361 / 50000) ∧
    763 / 25000 ≤ response (9 / 400) := by
  have aBounds : (138629 / 100000 : ℝ) ≤ a ∧ a ≤ 138630 / 100000 := by
    dsimp [a]
    constructor <;> linarith [KernelR.log_four_bounds.1, KernelR.log_four_bounds.2]
  have eEarlyHead : Real.exp (-(9 / 1000 : ℝ)) ≤ 991041 / 1000000 := by
    have h := Real.exp_bound (x := -(9 / 1000 : ℝ)) (n := 7) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have eEarlyTail : (975354 / 1000000 : ℝ) ≤ Real.exp (-a * (9 / 500)) := by
    apply le_trans _ (Real.exp_le_exp.mpr (show -(24954 / 1000000 : ℝ) ≤ -a * (9 / 500) by linarith [aBounds.2]))
    have h := Real.exp_bound (x := -(24954 / 1000000 : ℝ)) (n := 7) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have eNominalHead : (990049 / 1000000 : ℝ) ≤ Real.exp (-(1 / 100 : ℝ)) ∧
      Real.exp (-(1 / 100 : ℝ)) ≤ 990051 / 1000000 := by
    have h := Real.exp_bound (x := -(1 / 100 : ℝ)) (n := 7) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    constructor <;> linarith [(abs_sub_le_iff.mp h).1, (abs_sub_le_iff.mp h).2]
  have eNominalTail : (972653 / 1000000 : ℝ) ≤ Real.exp (-a * (1 / 50)) ∧
      Real.exp (-a * (1 / 50)) ≤ 972657 / 1000000 := by
    constructor
    · apply le_trans _ (Real.exp_le_exp.mpr (show -(27727 / 1000000 : ℝ) ≤ -a * (1 / 50) by linarith [aBounds.2]))
      have h := Real.exp_bound (x := -(27727 / 1000000 : ℝ)) (n := 7) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ] at h
      linarith [(abs_sub_le_iff.mp h).2]
    · apply le_trans (Real.exp_le_exp.mpr (show -a * (1 / 50) ≤ -(27725 / 1000000 : ℝ) by linarith [aBounds.1])) _
      have h := Real.exp_bound (x := -(27725 / 1000000 : ℝ)) (n := 7) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ] at h
      linarith [(abs_sub_le_iff.mp h).1]
  have eLateHead : (988812 / 1000000 : ℝ) ≤ Real.exp (-(9 / 800 : ℝ)) := by
    have h := Real.exp_bound (x := -(9 / 800 : ℝ)) (n := 7) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have eLateTail : Real.exp (-a * (9 / 400)) ≤ (969292 / 1000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr (show -a * (9 / 400) ≤ -(31191 / 1000000 : ℝ) by linarith [aBounds.1])) _
    have h := Real.exp_bound (x := -(31191 / 1000000 : ℝ)) (n := 7) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have upper {t d : ℝ} (age : 0 ≤ t)
      (difference : Real.exp (-(1 / 2) * t) - Real.exp (-a * t) ≤ d) :
      response t ≤ (7821 / 5000) * d := by
    have positive : 0 ≤ Real.exp (-(1 / 2) * t) - Real.exp (-a * t) :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [aBounds.1]))
    exact mul_le_mul selector_response_coefficient_bounds.2 difference positive (by norm_num)
  have lower {t d : ℝ} (dNonneg : 0 ≤ d)
      (difference : d ≤ Real.exp (-(1 / 2) * t) - Real.exp (-a * t)) :
      (391 / 250) * d ≤ response t :=
    mul_le_mul selector_response_coefficient_bounds.1 difference dNonneg
      (by linarith [selector_response_coefficient_bounds.1])
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · have h := upper (t := (9 / 500 : ℝ)) (d := 15687 / 1000000) (by norm_num)
      (by rw [show -(1 / 2 : ℝ) * (9 / 500) = -(9 / 1000) by norm_num]; linarith)
    linarith
  · have h := lower (t := (1 / 50 : ℝ)) (d := 17392 / 1000000) (by norm_num)
      (by rw [show -(1 / 2 : ℝ) * (1 / 50) = -(1 / 100) by norm_num]; linarith [eNominalHead.1, eNominalTail.2])
    linarith
  · have h := upper (t := (1 / 50 : ℝ)) (d := 17398 / 1000000) (by norm_num)
      (by rw [show -(1 / 2 : ℝ) * (1 / 50) = -(1 / 100) by norm_num]; linarith [eNominalHead.2, eNominalTail.1])
    linarith
  · have h := lower (t := (9 / 400 : ℝ)) (d := 19520 / 1000000) (by norm_num)
      (by rw [show -(1 / 2 : ℝ) * (9 / 400) = -(9 / 800) by norm_num]; linarith)
    linarith

/-- The two boxes give a sharper MARK onset bracket for a sensor at rest.
The hypothesis can come from the first-contact construction or an actual
sensor-trigger prefix. -/
theorem teacher_sensor_mark_age {n θ ε} (box : @PhysicalBox n θ ε) (i : Fin n) (p : Port)
    {initial start age : ℝ} (rest : RestBand initial) (ageBounds : 0 ≤ age ∧ age ≤ 1 / 40)
    (root : auxPulse initial ((θ i).inputGain p) start (start + age) = 1) :
    9 / 500 < age ∧ age < 9 / 400 := by
  let gain := (θ i).inputGain p
  have gainPos : 0 ≤ gain := (box.input_gain_positive i p).le
  have nomPos : 0 < response (1 / 50) := by linarith [sensor_response_bounds.2.1.1]
  have boxGain := (box.2 i p).2.2.2.2
  change (1 - 1 / 40) / response (1 / 50) * (1 - ε) ≤ gain ∧
      gain ≤ (1 - 1 / 40) / response (1 / 50) * (1 + ε) at boxGain
  have gainProdLower : (9 / 10) * (1 - 1 / 40) ≤ gain * response (1 / 50) := by
    have h := mul_le_mul_of_nonneg_right boxGain.1 nomPos.le
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ nomPos.ne'] at h
    linarith [box.epsilon_bounds.2]
  have gainProdUpper : gain * response (1 / 50) ≤ (11 / 10) * (1 - 1 / 40) := by
    have h := mul_le_mul_of_nonneg_right boxGain.2 nomPos.le
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ nomPos.ne'] at h
    linarith [box.epsilon_bounds.2]
  have gainUpper : gain ≤ 789 / 20 := by
    have h := mul_le_mul_of_nonneg_left sensor_response_bounds.2.1.1 gainPos
    linarith
  have gainLower : (161 / 5 : ℝ) ≤ gain := by
    have h := mul_le_mul_of_nonneg_left sensor_response_bounds.2.1.2 gainPos
    linarith
  have decay : 0 ≤ Real.exp (-(1 / 2) * age) ∧ Real.exp (-(1 / 2) * age) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith [ageBounds.1])⟩
  have residual := decay_upper (rate := (1 / 2 : ℝ))
    (show initial - 1 / 40 ≤ (1 / 100000 : ℝ) from by linarith [rest.2])
    (by norm_num) (by norm_num) ageBounds.1
  have lower : -(1 / 100000 : ℝ) ≤ (initial - 1 / 40) * Real.exp (-(1 / 2) * age) := by
    have h := mul_le_mul_of_nonneg_right (show -(1 / 100000 : ℝ) ≤ initial - 1 / 40 by linarith [rest.1]) decay.1
    linarith [mul_le_mul_of_nonpos_left decay.2 (by norm_num : -(1 / 100000 : ℝ) ≤ 0)]
  rw [auxPulse_formula, add_sub_cancel_left] at root
  change 1 / 40 + (initial - 1 / 40) * Real.exp (-(1 / 2) * age) + gain * response age = 1 at root
  constructor
  · by_contra! before
    have pulse := early_response_monotone
      (show age ∈ Icc 0 (9 / 10) from ⟨ageBounds.1, by linarith [ageBounds.2]⟩)
      (by norm_num : (9 / 500 : ℝ) ∈ Icc 0 (9 / 10)) before
    have product := mul_le_mul gainUpper (pulse.trans sensor_response_bounds.1)
      (response_nonnegative ageBounds.1) (by norm_num)
    linarith
  · by_contra! after
    have pulse := early_response_monotone
      (by norm_num : (9 / 400 : ℝ) ∈ Icc 0 (9 / 10))
      (show age ∈ Icc 0 (9 / 10) from ⟨ageBounds.1, by linarith [ageBounds.2]⟩) after
    have product := mul_le_mul gainLower (sensor_response_bounds.2.2.trans pulse) (by norm_num) gainPos
    linarith

/-- Delay from the teacher FIRE to admission of the work pulse. Only exact
model constants occur here. Neither selector gain nor fabrication is read. -/
noncomputable def teacherWorkOffset : ℝ :=
  1 + (Real.log (5 / 2) - 9741 / 100000) / (2 / 25)

theorem teacher_work_offset_bounds : (11 : ℝ) < teacherWorkOffset ∧ teacherWorkOffset < 12 := by
  unfold teacherWorkOffset
  constructor <;> linarith [KernelR.log_recovery_bounds.1, KernelR.log_recovery_bounds.2]

/-- The actual MARK deficit, including the time before the sensor contact. -/
private theorem teacher_mark_deficit_tight_bounds {n θ ε} (box : @PhysicalBox n θ ε) (i : Fin n) (p : Port)
    {age : ℝ} (timing : 9 / 500 ≤ age ∧ age ≤ 9 / 400) :
    (1337 / 500000 : ℝ) ≤ KernelR.Cadence.markDeficit age ((θ i).lm p) ∧
      KernelR.Cadence.markDeficit age ((θ i).lm p) ≤ 1661 / 500000 := by
  let L := Real.log (5 / 4 : ℝ)
  have logBounds : (22314 / 100000 : ℝ) ≤ L ∧ L ≤ 22315 / 100000 := by
    dsimp [L]
    rw [Real.log_div (by norm_num) (by norm_num)]
    constructor <;> linarith [Real.log_five_gt_d9, Real.log_five_lt_d9,
      KernelR.log_four_bounds.1, KernelR.log_four_bounds.2]
  have pos : 0 < L := by linarith [logBounds.1]
  have factor : (481 / 10000 : ℝ) ≤ 1 / (10 * L) - 2 / 5 ∧
      1 / (10 * L) - 2 / 5 ≤ 482 / 10000 := by
    constructor
    · have h := (le_div_iff₀ (show 0 < 10 * L by positivity)).2
        (show (4481 / 10000 : ℝ) * (10 * L) ≤ 1 by linarith [logBounds.2])
      linarith
    · have h := (div_le_iff₀ (show 0 < 10 * L by positivity)).2
        (show (1 : ℝ) ≤ (4482 / 10000 : ℝ) * (10 * L) by linarith [logBounds.1])
      linarith
  have duration : (1 / 55 : ℝ) ≤ L / (θ i).lm p ∧ L / (θ i).lm p ≤ 1 / 45 :=
    ⟨(box.aux_durations_lower i p).1, box.mark_duration_upper i p⟩
  have lo := mul_le_mul factor.1 duration.1 (by norm_num) (by linarith [factor.1])
  have hi := mul_le_mul factor.2 duration.2 (by linarith [duration.1]) (by norm_num)
  have identity : KernelR.Cadence.markDeficit age ((θ i).lm p) =
      age / 10 + (1 / (10 * L) - 2 / 5) * (L / (θ i).lm p) := by
    unfold KernelR.Cadence.markDeficit
    change age / 10 + (1 / 10 - (2 / 5) * L) / (θ i).lm p = _
    field_simp [pos.ne', (box.rates_positive i p).1.ne']
  rw [identity]
  constructor <;> linarith [timing.1, timing.2]

theorem teacher_mark_deficit_bounds {n θ ε} (box : @PhysicalBox n θ ε) (i : Fin n) (p : Port)
    {age : ℝ} (timing : 9 / 500 ≤ age ∧ age ≤ 9 / 400) :
    (267 / 100000 : ℝ) ≤ KernelR.Cadence.markDeficit age ((θ i).lm p) ∧
      KernelR.Cadence.markDeficit age ((θ i).lm p) ≤ 133 / 40000 := by
  have tight := teacher_mark_deficit_tight_bounds box i p timing
  constructor <;> linarith [tight.1, tight.2]

/-- The original, unsaturated recovery clock has a small positive
symmetric budget, under the same bound on actual MARK onset. -/
theorem teacher_reopen_age_with_jitter {n θ ε} (box : @PhysicalBox n θ ε) (i : Fin n) (p : Port)
    {age delay σ : ℝ} (timing : 9 / 500 ≤ age ∧ age ≤ 9 / 400)
    (budget : σ ≤ 1 / 20000)
    (wire : delay ∈ Icc (teacherWorkOffset - σ) (teacherWorkOffset + σ)) :
    CappedWorkTiming ε
      ((Real.log (5 / 2) - (2 / 25) * (delay - 1) +
        KernelR.Cadence.markDeficit age ((θ i).lm p)) / (9 / 50)) := by
  have deficit := teacher_mark_deficit_tight_bounds box i p timing
  have offset : Real.log (5 / 2) - (2 / 25) * (teacherWorkOffset - 1) = (9741 / 100000 : ℝ) := by
    unfold teacherWorkOffset
    ring
  apply Or.inl
  constructor <;> linarith [deficit.1, deficit.2, wire.1, wire.2]

/-- The fixed schedule puts the solved reopening inside the expanded work
window even at ±10%. All dates are relative to the actual FIRE. -/
theorem teacher_reopen_age {n θ ε} (box : @PhysicalBox n θ ε) (i : Fin n) (p : Port)
    {age : ℝ} (timing : 9 / 500 ≤ age ∧ age ≤ 9 / 400) :
    CappedWorkTiming ε
      ((Real.log (5 / 2) - (2 / 25) * (teacherWorkOffset - 1) +
        KernelR.Cadence.markDeficit age ((θ i).lm p)) / (9 / 50)) := by
  have deficit := teacher_mark_deficit_bounds box i p timing
  have offset : Real.log (5 / 2) - (2 / 25) * (teacherWorkOffset - 1) = (9741 / 100000 : ℝ) := by
    unfold teacherWorkOffset
    ring
  rw [offset]
  apply Or.inl
  constructor <;> linarith [deficit.1, deficit.2]

/-- A local self-delivery scheduled at the fixed offset from the actual
teacher firing, with no dependence on the encoded selector value. -/
noncomputable def teacherWorkDelivery {n : ℕ} (i : Fin n) (p : Port) (fire : ℝ) : Delivery n :=
  ⟨i, p, fire + teacherWorkOffset⟩

/-- If the same self-timer acquires an independent delay range of width
0.1, it cannot keep both endpoint reopenings in the ±10% window. -/
theorem teacher_work_timer_jitter_limit (offset deficit : ℝ) :
    ¬ (CappedWorkTiming (1 / 10)
        ((Real.log (5 / 2) - (2 / 25) * (offset - 1) + deficit) / (9 / 50)) ∧
      CappedWorkTiming (1 / 10)
        ((Real.log (5 / 2) - (2 / 25) * (offset + 1 / 10 - 1) + deficit) / (9 / 50))) := by
  rintro ⟨first, second⟩
  rcases first with first | ⟨bad, _⟩
  · rcases second with second | ⟨bad, _⟩
    · linarith [first.2, second.1]
    · norm_num at bad
  · norm_num at bad

private theorem teacher_work_arrival_profile :
    (1 / 4 : ℝ) * Real.exp (-(2 / 25) * (teacherWorkOffset - 1)) =
      (1 / 10 : ℝ) * Real.exp (9741 / 100000) := by
  have exponent : -(2 / 25 : ℝ) * (teacherWorkOffset - 1) =
      9741 / 100000 - Real.log (5 / 2) := by unfold teacherWorkOffset; ring
  rw [exponent, sub_eq_add_neg, Real.exp_add, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]
  ring

structure TeacherReopenPrefix (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1)
    (p : Port) (ε : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution final.time
  ready : final.main 0 = .ready
  charge : final.x 0 .q = 1 / 10
  recovery : final.x 0 .b = 9 / 50
  active : final.raw 0 p = some s.time
  timing : CappedWorkTiming ε (final.time - s.time)
  gains : ∀ q, final.x 0 (.z q) = s.x 0 (.z q)
  emissions : execution.ledger.emissions = []

/-- Construct the MARK and the actual SLOW-to-READY jump from the
scheduled work admission. The work pulse is still active at reopening. -/
theorem teacher_reopen_prefix_exists {θ ε route s} (box : @PhysicalBox 1 θ ε)
    (p : Port) (physical : PhysicalInvariant θ s)
    (slow : s.main 0 = .slow) (initial : s.x 0 .q = (1 / 10 : ℝ) * Real.exp (9741 / 100000))
    (recovery : s.x 0 .b = 2 / 25)
    (auxiliary : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (active : s.raw 0 p = some s.time) (other : ∀ q, q ≠ p → s.raw 0 q = none)
    (pending : ∀ d ∈ s.pending, s.time + 3 / 5 ≤ d.due) :
    Nonempty (TeacherReopenPrefix θ route s p ε) := by
  obtain ⟨age, early, deadline, root, prior, slope⟩ :=
    box.first_sensor_crossing_transversal 0 p (auxiliary p).2.1 (auxiliary p).2.2
  have sharp := teacher_sensor_mark_age box 0 p (auxiliary p).2
    ⟨by linarith, deadline.le⟩ root
  have deficit := teacher_mark_deficit_bounds box 0 p ⟨sharp.1.le, sharp.2.le⟩
  let J := KernelR.Cadence.markDeficit age ((θ 0).lm p)
  let M := s.time + age
  let D := Real.log (5 / 4) / (θ 0).lm p
  let P := M + D
  let W := s.time + (9741 / 100000 + J) / (9 / 50)
  have Mpos : s.time < M := by dsimp [M]; linarith
  have Ppos : M < P := by dsimp [P,D]; linarith [(box.aux_durations_lower 0 p).1]
  have Pupper : P < s.time + 1 / 20 := by dsimp [P,M,D]; linarith [box.mark_duration_upper 0 p]
  have Wlo : s.time + 139 / 250 ≤ W := by dsimp [W,J]; linarith [deficit.1]
  have Whi : W ≤ s.time + 11193 / 20000 := by dsimp [W,J]; linarith [deficit.2]
  have nonsolo : ∀ j : Fin 1, j ≠ 0 → False := fun j h => h (Subsingleton.elim _ _)
  have auxOther (j : Fin 1) (q : Port) (h : j ≠ 0 ∨ q ≠ p) : s.aux j q = .ready := by
    rw [Subsingleton.elim j 0]; exact (auxiliary q).1
  have rawOther (j : Fin 1) (q : Port) (h : j ≠ 0 ∨ q ≠ p) : s.raw j q = none := by
    rw [Subsingleton.elim j 0]
    exact other q (h.resolve_left (by simp [Subsingleton.elim j 0]))
  have sensorOther (j : Fin 1) (q : Port) (h : j ≠ 0 ∨ q ≠ p) : s.x j (.m q) < 1 := by
    rw [Subsingleton.elim j 0]; linarith [(auxiliary q).2.2]
  let beforeMark := protectedMainEnd θ s 0 p .slow .ready (some s.time) M
  let firstFlow : Flow θ s beforeMark :=
    protectedMainFlow s 0 p .slow .ready (some s.time) Mpos (Or.inr rfl) (Or.inl rfl) slow
      (fun j h => (nonsolo j h).elim) (auxiliary p).1 auxOther active rawOther
      (by intro o h; cases Option.some.inj h; exact ⟨le_rfl, by dsimp [M]; linarith⟩)
      (fun j h => (nonsolo j h).elim) sensorOther
      (by
        intro t ht
        simp only [reduceCtorEq, ite_false, protectedMainRate, recovery, initial, mul_assoc, ← Real.exp_add]
        have positive : 0 < (9741 / 100000 : ℝ) + -(2 / 25) * (t - s.time) := by
          dsimp [M] at ht; linarith [ht.2]
        linarith only [Real.one_lt_exp_iff.mpr positive])
      (by intro t ht; simpa [rawInputScale] using prior t ht)
      (fun d hd => by dsimp [M]; linarith [pending d hd])
  have markGuard : beforeMark.x 0 (.m p) = 1 := by
    simpa [beforeMark, protectedMainEnd, protectedMainValues, rawInputScale, M] using root
  let marking := setAux beforeMark 0 p .mark
  let startMark : Execution θ route s marking :=
    .cons (.flow firstFlow) (.cons (.jump (.mark _ 0 p (auxiliary p).1 markGuard)) (.nil _))
  have markSensor : marking.x 0 (.m p) = 1 := markGuard
  have markRecovery : marking.x 0 .b = 2 / 25 := recovery
  have markTime : marking.time = M := rfl
  have markCharge : marking.x 0 .q = (1 / 10 : ℝ) * Real.exp (9741 / 100000 - (2 / 25) * age) := by
    simp only [marking, setAux, beforeMark, protectedMainEnd, protectedMainValues,
      ite_true, protectedMainRate, reduceCtorEq, ite_false, recovery, initial, mul_assoc, ← Real.exp_add]
    rw [show M - s.time = age by dsimp [M]; ring]
    congr 2; ring
  have markMode : marking.main 0 = .slow := slow
  have duration : slowMarkDuration θ marking 0 p = D := by
    norm_num [slowMarkDuration, markSensor, D]
  have durationUpper : D ≤ 1 / 45 := box.mark_duration_upper 0 p
  have markMainGuard (t : ℝ) (ht : t ∈ Icc M P) : 1 / 10 < slowMarkMain θ marking 0 p t := by
    have timeBound : 0 ≤ t - M ∧ t - M ≤ 1 / 45 := by
      constructor <;> linarith [ht.1, ht.2, show P = M + D from rfl]
    have rate := (box.rates_positive 0 p).1
    have expUpper : Real.exp (-((θ 0).lm p) * (t - M)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [timeBound.1])
    have correction : 0 ≤ (1 - Real.exp (-((θ 0).lm p) * (t - M))) / (θ 0).lm p :=
      div_nonneg (sub_nonneg.mpr expUpper) rate.le
    have integralBound : slowMarkIntegral θ marking 0 p t ≤ (29 / 50 : ℝ) * (1 / 45) := by
      unfold slowMarkIntegral
      rw [markTime, markRecovery, markSensor]
      linarith [timeBound.2]
    unfold slowMarkMain
    rw [markCharge, mul_assoc, ← Real.exp_add]
    have positive : 0 < (9741 / 100000 : ℝ) - (2 / 25) * age - slowMarkIntegral θ marking 0 p t := by
      linarith
    rw [← sub_eq_add_neg]
    linarith only [Real.one_lt_exp_iff.mpr positive]
  have markAuxOther (j : Fin 1) (q : Port) (h : j ≠ 0 ∨ q ≠ p) : marking.aux j q = .ready := by
    have ne := h.resolve_left (by simp [Subsingleton.elim j 0])
    rw [Subsingleton.elim j 0]
    simp [marking, setAux, beforeMark, protectedMainEnd, ne, (auxiliary q).1]
  have markSensorOther (j : Fin 1) (q : Port) (h : j ≠ 0 ∨ q ≠ p) : marking.x j (.m q) < 1 := by
    have ne := h.resolve_left (by simp [Subsingleton.elim j 0])
    rw [Subsingleton.elim j 0]
    simpa [marking, setAux, beforeMark, protectedMainEnd, protectedMainValues, ne] using
      relax_lt (rate := (1 / 2 : ℝ)) (target := (1 / 40 : ℝ)) (by norm_num) Mpos.le
        (sensorOther 0 q (Or.inr ne)) (by norm_num)
  let markFlow : Flow θ marking (slowMarkEnd θ marking 0 p P) :=
    slowMarkFlow box marking 0 p (some s.time) (by rw [markTime]; exact Ppos)
      (by rw [markTime, duration]) markMode (fun j h => (nonsolo j h).elim)
      (by simp [marking,setAux]) markAuxOther active rawOther (by rw [markSensor]; norm_num)
      markSensor.le ((startMark.physical_invariant box physical).reserve 0)
      (by rw [markRecovery, markSensor]; norm_num)
      (by intro o h; cases Option.some.inj h; exact ⟨Mpos.le, by linarith⟩)
      (fun j h => (nonsolo j h).elim) markSensorOther
      (fun t ht => markMainGuard t ⟨ht.1, ht.2.le⟩) (fun d hd => by linarith [pending d hd])
  let silent := setAux (slowMarkEnd θ marking 0 p P) 0 p .silent
  have endpointP : P = marking.time + slowMarkDuration θ marking 0 p := by rw [markTime, duration]
  have silentSensor : silent.x 0 (.m p) = 4 / 5 := by
    change (slowMarkEnd θ marking 0 p P).x 0 (.m p) = _
    rw [endpointP]
    exact slowMarkEnd_sensor box marking 0 p (by rw [markSensor]; norm_num)
  let markTrace : Execution θ route s silent := startMark.append
    (.cons (.flow markFlow) (.cons (.jump (.silent _ 0 p (by simp [slowMarkEnd, marking, setAux]) silentSensor)) (.nil _)))
  have silentRecovery : silent.x 0 .b = 9 / 50 := by
    change (slowMarkEnd θ marking 0 p P).x 0 .b = _
    rw [endpointP, slowMarkEnd_recovery box marking 0 p (by rw [markSensor]; norm_num),
      markRecovery, markSensor]
    norm_num
  have markEndExp : Real.exp (-((θ 0).lm p) * D) = (4 / 5 : ℝ) := by
    have eq : -((θ 0).lm p) * D = -Real.log (5 / 4) := by
      dsimp [D]; field_simp [(box.rates_positive 0 p).1.ne']
    rw [eq, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4)]
    norm_num
  have postClock (t : ℝ) :
      silent.x 0 .q * Real.exp (-silent.x 0 .b * (t - P)) =
        (1 / 10 : ℝ) * Real.exp ((9 / 50) * (W - t)) := by
    change slowMarkMain θ marking 0 p P * Real.exp (-silent.x 0 .b * (t - P)) = _
    rw [silentRecovery, slowMarkMain, markCharge, slowMarkIntegral,
      markTime, markRecovery, markSensor, show P - M = D by dsimp [P]; ring, markEndExp]
    simp only [mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [W,J,KernelR.Cadence.markDeficit]
    change _ = (9 / 50 : ℝ) * (s.time + (9741 / 100000 +
      (age / 10 + (1 / 10 - (2 / 5) * Real.log (5 / 4)) / (θ 0).lm p)) / (9 / 50) - t)
    dsimp [P,M,D]
    ring
  have silentOtherBelow (j : Fin 1) (q : Port) (h : j ≠ 0 ∨ q ≠ p) : silent.x j (.m q) < 1 := by
    have ne := h.resolve_left (by simp [Subsingleton.elim j 0])
    rw [Subsingleton.elim j 0]
    have noArrival : NoArrivalAt markTrace 0 q := by
      simp [NoArrivalAt, markTrace, startMark, Execution.deliveries_append, Execution.deliveries,
        Move.deliveries, Jump.deliveries]
    have band := markTrace.aux_no_input_rest_band 0 q (auxiliary q).1 (auxiliary q).2 (other q ne) noArrival
    linarith [band.1.2.2]
  have silentOtherAux (j : Fin 1) (q : Port) (h : j ≠ 0 ∨ q ≠ p) : silent.aux j q = .ready := by
    have ne := h.resolve_left (by simp [Subsingleton.elim j 0])
    rw [Subsingleton.elim j 0]
    simpa [silent, setAux, slowMarkEnd, ne] using markAuxOther 0 q (Or.inr ne)
  let beforeReturn := protectedMainEnd θ silent 0 p .slow .silent (some s.time) W
  let tailFlow : Flow θ silent beforeReturn :=
    protectedMainFlow silent 0 p .slow .silent (some s.time) (by change P < W; linarith)
      (Or.inr rfl) (Or.inr (Or.inl rfl)) slow (fun j h => (nonsolo j h).elim)
      (by simp [silent,setAux]) silentOtherAux active rawOther
      (by intro o h; cases Option.some.inj h; exact ⟨Mpos.le.trans Ppos.le, by linarith⟩)
      (fun j h => (nonsolo j h).elim) silentOtherBelow
      (by
        intro t ht
        change (1 / 10 : ℝ) < silent.x 0 .q * Real.exp (-silent.x 0 .b * (t - P))
        rw [postClock]
        have h := Real.one_lt_exp_iff.mpr (show 0 < (9 / 50 : ℝ) * (W - t) by linarith [ht.2])
        linarith)
      (by
        intro t ht
        change t ∈ Ico P W at ht
        simp only [reduceCtorEq, ite_false, ite_true, silentSensor, protectedReadyRate]
        have hs := protected_decay_schedule (initial := (4 / 5 : ℝ)) (floor := (1 / 10 : ℝ))
          (by norm_num) (by norm_num) (box.rates_positive 0 p).2.1
        exact hs.2.2 (t - P) (by linarith [ht.1])
          (by norm_num; linarith [ht.2, (box.aux_durations_lower 0 p).2.1]))
      (fun d hd => by linarith [pending d hd])
  have returnGuard : beforeReturn.x 0 .q = 1 / 10 := by
    change silent.x 0 .q * Real.exp (-silent.x 0 .b * (W - P)) = _
    rw [postClock]; simp
  let final := setMain beforeReturn 0 .ready
  let trace := markTrace.append (.cons (.flow tailFlow) (.cons (.jump (.reopen _ 0 slow returnGuard)) (.nil _)))
  have markTransverse : startMark.ContactsTransversal := by
    simp only [startMark, Execution.ContactsTransversal, Jump.ContactTransversal, and_true]
    exact firstFlow.aux_contact_field_positive 0 p (auxiliary p).1 active
      (by change M < s.time + 1; dsimp [M]; linarith)
      (by change 0 < deriv (auxPulse (s.x 0 (.m p)) ((θ 0).inputGain p) s.time) (s.time + age); exact slope)
  have transverse : trace.ContactsTransversal := by
    simpa [trace, markTrace, Jump.ContactTransversal] using markTransverse
  have finalReady : final.main 0 = .ready := by simp [final, setMain]
  have finalGuards : BeforeGuards final final.x := by
    constructor
    · intro i
      rw [Subsingleton.elim i 0, finalReady]
      change beforeReturn.x 0 .q < 1
      linarith [returnGuard]
    · intro i q
      rw [Subsingleton.elim i 0]
      by_cases eq : q = p
      · subst q
        have mode : final.aux 0 p = .silent := by
          simp [final, setMain, beforeReturn, protectedMainEnd, silent, setAux]
        rw [mode]
        change (1 / 10 : ℝ) < beforeReturn.x 0 (.m p)
        simp only [beforeReturn, protectedMainEnd, protectedMainValues, and_self, ite_true,
          reduceCtorEq, ite_false, silentSensor, protectedReadyRate]
        have hs := protected_decay_schedule (initial := (4 / 5 : ℝ)) (floor := (1 / 10 : ℝ))
          (by norm_num) (by norm_num) (box.rates_positive 0 p).2.1
        exact hs.2.2 (W - P) (by linarith)
          (by norm_num; linarith [(box.aux_durations_lower 0 p).2.1])
      · have mode : final.aux 0 q = .ready := silentOtherAux 0 q (Or.inr eq)
        rw [mode]
        change beforeReturn.x 0 (.m q) < 1
        simpa [beforeReturn, protectedMainEnd, protectedMainValues, eq] using
          relax_lt (rate := (1 / 2 : ℝ)) (target := (1 / 40 : ℝ))
            (by norm_num) (show silent.time ≤ W by change P ≤ W; linarith)
            (silentOtherBelow 0 q (Or.inr eq)) (by norm_num)
  have finalFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ s.pending at hd
    change W < d.due
    linarith [pending d hd]
  have complete : CompleteThrough trace final.time := by
    refine ⟨rfl, fun next => finalGuards.no_jump ?_ finalFuture next, finalFuture⟩
    intro i q origin present
    rw [Subsingleton.elim i 0] at present
    change s.raw 0 q = some origin at present
    by_cases eq : q = p
    · subst q
      rw [active] at present
      have same := Option.some.inj present
      change W < origin + 1
      linarith
    · rw [other q eq] at present
      contradiction
  refine ⟨⟨final, trace, transverse, complete, finalReady, returnGuard, silentRecovery, ?_, ?_, ?_, ?_⟩⟩
  · change s.raw 0 p = some s.time
    exact active
  · apply Or.inl
    change 139 / 250 ≤ W - s.time ∧ W - s.time ≤ 11193 / 20000
    constructor <;> linarith
  · intro q
    rfl
  · simp [trace, markTrace, startMark, Execution.emissions_append, Execution.ledger, Move.ledger,
      Flow.ledger, Jump.ledger, Ledger.add, Ledger.zero]

/-- The teacher schedules a single work pulse on its own output event. -/
noncomputable def teacherSelfRouter (work : Port) : Router 1 :=
  fun i fire => [teacherWorkDelivery i work fire]

theorem teacher_self_router_causal (work : Port) : StrictCausalRouter (teacherSelfRouter work) := by
  intro i fire d hd
  simp [teacherSelfRouter] at hd
  subst d
  change fire < fire + teacherWorkOffset
  linarith [teacher_work_offset_bounds.1]

theorem teacher_future_transverse {n θ route s u} (e : @Execution n θ route s u)
    (token : Delivery n) (later : u.time ≤ token.due)
    (positive : e.ContactsTransversal) :
    (e.withFuture [token] (by intro d hd; simpa using (List.mem_singleton.mp hd) ▸ later)).ContactsTransversal := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ih later positive
    | jump jump =>
      exact ⟨(jump.contactTransversal_requeue (jump.withOneFuture token)).1 positive.1,
        ih later positive.2⟩

private theorem teacher_future_deliveries {n θ route s u} (e : @Execution n θ route s u)
    (token : Delivery n) (later : ∀ d ∈ [token], u.time ≤ d.due) :
    (e.withFuture [token] later).deliveries = e.deliveries := by
  induction e with
  | nil => rfl
  | cons move rest ih =>
    cases move with
    | flow f => simpa [Execution.withFuture, Execution.deliveries, Move.deliveries] using ih later
    | jump j =>
      have unchanged : (j.withOneFuture token).deliveries = j.deliveries := by cases j <;> rfl
      change (j.withOneFuture token).deliveries ++ (rest.withFuture [token] later).deliveries =
        j.deliveries ++ rest.deliveries
      rw [unchanged, ih later]

structure TeacherOwnFireReopen (θ : Fin 1 → Parameters) (s : Snapshot 1) (work : Port) (ε : ℝ) where
  fireTime : ℝ
  admitted : Snapshot 1
  lead : Execution θ (teacherSelfRouter work) s admitted
  transverse : lead.ContactsTransversal
  emissions : lead.ledger.emissions = [(0, fireTime)]
  deliveries : lead.deliveries = [teacherWorkDelivery (0 : Fin 1) work fireTime]
  admission : admitted.time = (teacherWorkDelivery (0 : Fin 1) work fireTime).due
  reopen : TeacherReopenPrefix θ (teacherSelfRouter work) admitted work ε
  gains : ∀ p, admitted.x 0 (.z p) = s.x 0 (.z p)

/-- From an already admitted ignition input, one native history contains the
genuine teacher FIRE, its own routed work pulse, and the subsequent reopening.
The work token is created by FIRE and is absent from the initial queue. -/
theorem teacher_own_fire_reopen_exists {θ ε s} (box : @PhysicalBox 1 θ ε)
    (ignite work : Port) (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (ready : ReadyCoordinates s 0)
    (ignitionGain : 9 / 5 ≤ Real.exp (s.x 0 (.z ignite)) ∧ Real.exp (s.x 0 (.z ignite)) ≤ 11 / 5)
    (active : s.raw 0 ignite = some s.time) (other : ∀ q, q ≠ ignite → s.raw 0 q = none)
    (recovery : s.x 0 .b = 2 / 25) (empty : s.pending = []) :
    Nonempty (TeacherOwnFireReopen θ s work ε) := by
  have otherAll (i : Fin 1) (p : Port) (h : i ≠ 0 ∨ p ≠ ignite) : s.raw i p = none := by
    rw [Subsingleton.elim i 0]
    exact other p (h.resolve_left (by simp [Subsingleton.elim i 0]))
  obtain ⟨fire⟩ := first_mid_learned_fire_exists (route := fun _ _ => []) s box physical valid
    0 ignite (fun i => by rw [Subsingleton.elim i 0]; exact ready) ignitionGain active otherAll
    (by simp [empty])
  obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists box ready ignitionGain.2 other (by simp [empty])
  let F := fire.final.time
  let token := teacherWorkDelivery (0 : Fin 1) work F
  let T := token.due
  let route := teacherSelfRouter work
  have fireQueue : fire.final.pending = [] := by rw [fire.pending, empty]; rfl
  have fastQueue : fast.final.pending = [] := fast.pending.trans fireQueue
  have wait : fast.final.time < T := by
    rw [fast.date]
    change F + 1 < F + teacherWorkOffset
    linarith [teacher_work_offset_bounds.1]
  let prior : Execution θ (fun _ _ => []) s (fire.firstSilent.learnedFireBefore fire.latency) :=
    (fire.firstSilent.execution _).append (.cons (.flow fire.flow) (.nil _))
  have priorSilent : prior.ledger.emissions = [] := by
    simp [prior, FirstInputSilent.execution, FirstInputSilent.continuation, FirstInputMark.execution,
      Execution.emissions_append, Execution.ledger, Move.ledger, Flow.ledger, Jump.ledger, Ledger.add, Ledger.zero]
  have priorTransverse : prior.ContactsTransversal := by
    exact (Execution.contactsTransversal_append _ _).2 ⟨fire.firstSilent.contacts_transversal _, trivial⟩
  have priorDeliveries : prior.deliveries = [] := by
    simp [prior, FirstInputSilent.execution, FirstInputSilent.continuation, FirstInputMark.execution,
      Execution.deliveries_append, Execution.deliveries, Move.deliveries, Jump.deliveries]
  obtain ⟨routedPrior, priorLedger, priorDeliveryEq, priorContact⟩ :=
    prior.retarget_router_transversal route (by simp [priorSilent])
  let fireJump : Jump route (fire.firstSilent.learnedFireBefore fire.latency)
      (fire.firstSilent.learnedFireFinal route fire.latency) :=
    .fire _ 0 (fire.firstSilent.main_ready 0) fire.threshold
  have fireEmission : fireJump.ledger.emissions = [(0,F)] := rfl
  have fireContact : fireJump.ContactTransversal θ := fire.contact_field_positive
  have fireEndpoint : fire.firstSilent.learnedFireFinal route fire.latency = withFuture fire.final [token] := by
    have queue : (fire.firstSilent.learnedFireBefore fire.latency).pending = [] :=
      fire.firstSilent.queue_preserved.trans empty
    simp [FirstInputSilent.learnedFireFinal, FirstLearnedFire.final, withFuture, queue, route,
      teacherSelfRouter, token, F, fire.date]
  let fastFuture := fast.execution.withFuture [token] (by intro d hd; simpa using (List.mem_singleton.mp hd) ▸ wait.le)
  have fastSilent : fastFuture.ledger.emissions = [] := by
    rw [Execution.withFuture_ledger, fast.emissions]
  have fastDeliveries : fastFuture.deliveries = [] := by
    rw [teacher_future_deliveries, fast.deliveries]
  obtain ⟨routedFast, fastLedger, fastDeliveryEq, fastContact⟩ :=
    fastFuture.retarget_router_transversal route (by simp [fastSilent])
  have routedFastContact : routedFast.ContactsTransversal :=
    fastContact.mpr (teacher_future_transverse fast.execution token wait.le fast.contacts_transversal)
  let start := withFuture fast.final [token]
  have startB : start.x 0 .b = 2 / 25 :=
    (fast.recovery 0).trans ((fire.recovery_preserved 0).trans recovery)
  have chargeAtT :
      start.x 0 .q * Real.exp (-start.x 0 .b * (T - start.time)) =
        (1 / 10 : ℝ) * Real.exp (9741 / 100000) := by
    change fast.final.x 0 .q * Real.exp (-start.x 0 .b * (T - fast.final.time)) = _
    rw [fast.charge, startB, fast.date]
    change (1 / 4 : ℝ) * Real.exp (-(2 / 25) * (F + teacherWorkOffset - (F + 1))) = _
    rw [show F + teacherWorkOffset - (F + 1) = teacherWorkOffset - 1 by ring]
    exact teacher_work_arrival_profile
  have lower : (1 / 10 : ℝ) < start.x 0 .q * Real.exp (-start.x 0 .b * (T - start.time)) := by
    rw [chargeAtT]
    linarith only [Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 9741 / 100000)]
  let beforeWork := protectedMainEnd θ start 0 work .slow .ready none T
  let quiet : Flow θ start beforeWork :=
    protectedMainFlow start 0 work .slow .ready none wait (Or.inr rfl) (Or.inl rfl)
      fast.main_slow (fun i h => (h (Subsingleton.elim i 0)).elim)
      (fast.auxiliary 0 work) (fun i p _ => fast.auxiliary i p)
      (fast.raw_none 0 work) (fun i p _ => fast.raw_none i p)
      (by intro o h; contradiction) (fun i h => (h (Subsingleton.elim i 0)).elim)
      (fun i p _ => by
        rw [Subsingleton.elim i 0]
        change fast.final.x 0 (.m p) < 1
        linarith [(fast.rest p).2])
      (by
        intro t ht
        change (1 / 10 : ℝ) < start.x 0 .q * Real.exp (-start.x 0 .b * (t - start.time))
        apply lower.trans_le (mul_le_mul_of_nonneg_left _ (by change 0 ≤ fast.final.x 0 .q; rw [fast.charge]; norm_num))
        apply Real.exp_le_exp.mpr
        rw [startB]
        linarith [ht.2])
      (by
        intro t ht
        simp only [ite_true, rawInputScale, mul_zero, auxPulse_zero_eq_relax]
        exact relax_lt (by norm_num) ht.1 (by
          change fast.final.x 0 (.m work) < 1
          linarith [(fast.rest work).2]) (by norm_num))
      (by intro d hd; change d ∈ [token] ++ fast.final.pending at hd; simp [fastQueue] at hd; subst d; exact le_rfl)
  let admitted : Snapshot 1 := { (setRaw beforeWork token.cell token.port (some beforeWork.time)) with pending := [] }
  let arrive : Jump route beforeWork admitted :=
    .arrive _ token [] [] (by simp [beforeWork, protectedMainEnd, start, withFuture, fastQueue])
      rfl (fast.raw_none 0 work)
  let handoff : Execution θ route start admitted := .cons (.flow quiet) (.cons (.jump arrive) (.nil _))
  have workSensor (p : Port) : admitted.aux 0 p = .ready ∧ RestBand (admitted.x 0 (.m p)) := by
    refine ⟨fast.auxiliary 0 p, ?_⟩
    have band := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) wait.le (fast.rest p)
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    by_cases eq : p = work
    · subst p
      simpa [admitted, setRaw, beforeWork, protectedMainEnd, protectedMainValues, rawInputScale,
        auxPulse_zero_eq_relax, RestBand, start, withFuture] using band
    · simpa [admitted, setRaw, beforeWork, protectedMainEnd, protectedMainValues, eq, RestBand, start, withFuture] using band
  have workOther (q : Port) (ne : q ≠ work) : admitted.raw 0 q = none := by
    simpa [admitted, token, teacherWorkDelivery, setRaw, beforeWork, protectedMainEnd, start,
      withFuture, ne] using fast.raw_none 0 q
  have startPhysical : PhysicalInvariant θ start :=
    ⟨fast.physical.region, fast.physical.gain_cap, fast.physical.recovery_cap, fast.physical.reserve⟩
  have workPhysical := handoff.physical_invariant box startPhysical
  obtain ⟨reopen⟩ := teacher_reopen_prefix_exists box work workPhysical fast.main_slow chargeAtT startB
    workSensor (by simp [admitted, token, teacherWorkDelivery, setRaw]) workOther (by simp [admitted])
  let finish := routedFast.append handoff
  have finishSilent : finish.ledger.emissions = [] := by
    rw [Execution.emissions_append, fastLedger, fastSilent]
    rfl
  have finishDelivery : finish.deliveries = [token] := by
    rw [Execution.deliveries_append, fastDeliveryEq, fastDeliveries]
    rfl
  have finishTransverse : finish.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2 ⟨routedFastContact, ⟨trivial, trivial⟩⟩
  have transport {a b c d : Snapshot 1} (same : b = c) (jump : Jump route a b)
      (tail : Execution θ route c d) :
      ∃ trace : Execution θ route a d,
        trace.ledger.emissions = jump.ledger.emissions ++ tail.ledger.emissions ∧
        trace.deliveries = jump.deliveries ++ tail.deliveries ∧
        (trace.ContactsTransversal ↔ jump.ContactTransversal θ ∧ tail.ContactsTransversal) := by
    cases same
    exact ⟨.cons (.jump jump) tail, rfl, rfl, Iff.rfl⟩
  obtain ⟨routedWork, workLedger, workDelivery, workContacts⟩ := transport fireEndpoint fireJump finish
  let lead := routedPrior.append routedWork
  have leadEmission : lead.ledger.emissions = [(0,F)] := by
    rw [Execution.emissions_append, priorLedger, priorSilent, workLedger, fireEmission, finishSilent]
    rfl
  have leadTransverse : lead.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2
      ⟨priorContact.mpr priorTransverse, workContacts.mpr ⟨fireContact, finishTransverse⟩⟩
  have leadDelivery : lead.deliveries = [token] := by
    rw [Execution.deliveries_append, priorDeliveryEq, priorDeliveries, workDelivery, finishDelivery]
    rfl
  exact ⟨⟨F, admitted, lead, leadTransverse, leadEmission, leadDelivery, rfl, reopen,
    fun p => (fast.gains 0 p).trans (fire.gain_preserved 0 p)⟩⟩

/-- The full prefix, from the admitted ignition pulse through reopening. -/
noncomputable def TeacherOwnFireReopen.execution {θ s work ε} (run : TeacherOwnFireReopen θ s work ε) :
    Execution θ (teacherSelfRouter work) s run.reopen.final :=
  run.lead.append run.reopen.execution

theorem TeacherOwnFireReopen.only_fire {θ s work ε} (run : TeacherOwnFireReopen θ s work ε) :
    run.execution.ledger.emissions = [(0, run.fireTime)] := by
  rw [TeacherOwnFireReopen.execution, Execution.emissions_append, run.emissions, run.reopen.emissions]
  rfl

theorem TeacherOwnFireReopen.gain_preserved {θ s work ε} (run : TeacherOwnFireReopen θ s work ε) (p : Port) :
    run.reopen.final.x 0 (.z p) = s.x 0 (.z p) :=
  (run.reopen.gains p).trans (run.gains p)

theorem TeacherOwnFireReopen.complete {θ s work ε} (run : TeacherOwnFireReopen θ s work ε) :
    CompleteThrough run.execution run.reopen.final.time :=
  run.reopen.complete

private theorem teacher_ignition_below_ready {s : Snapshot 1} (ready : ReadyCoordinates s 0) :
    InitiallyBelowReady s := by
  intro i c guard
  rw [Subsingleton.elim i 0]
  cases c with
  | q => linarith [ready.charge.2]
  | m p => linarith [(ready.auxiliary p).2.2]
  | z _ => exact False.elim guard
  | b => exact False.elim guard
  | energy => exact False.elim guard

/-- The same prefix is a model execution with genuine upward crossings. -/
noncomputable def TeacherOwnFireReopen.toCrossing {θ s work ε} (run : TeacherOwnFireReopen θ s work ε)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s) (ready : ReadyCoordinates s 0) :
    CrossingExecution θ (teacherSelfRouter work) s run.reopen.final :=
  run.execution.toCrossing (teacher_ignition_below_ready ready) box physical
    ((Execution.contactsTransversal_append _ _).2 ⟨run.transverse, run.reopen.transverse⟩)

/-- Complete first-contact runs agree at the constructed reopening horizon. -/
theorem TeacherOwnFireReopen.every_complete {θ s work ε final}
    (run : TeacherOwnFireReopen θ s work ε) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s)
    (execution : Execution θ (teacherSelfRouter work) s final)
    (complete : CompleteThrough execution run.reopen.final.time) :
    final.ObservationalEq run.reopen.final ∧ execution.ledger.emissions = [(0, run.fireTime)] := by
  obtain ⟨endpoint, fires⟩ :=
    execution.observational_unique run.execution box physical complete run.complete
  rw [run.only_fire] at fires
  exact ⟨endpoint, List.perm_singleton.mp fires⟩

/-- Complete upward-crossing runs agree at that same reopening horizon. -/
theorem TeacherOwnFireReopen.every_crossing_complete {θ s work ε final}
    (run : TeacherOwnFireReopen θ s work ε) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (ready : ReadyCoordinates s 0)
    (crossing : CrossingExecution θ (teacherSelfRouter work) s final)
    (complete : CrossingCompleteThrough crossing run.reopen.final.time) :
    final.ObservationalEq run.reopen.final ∧ crossing.execution.ledger.emissions = [(0, run.fireTime)] := by
  have transverse := (Execution.contactsTransversal_append _ _).2
    ⟨run.transverse, run.reopen.transverse⟩
  obtain ⟨native, same⟩ := crossing.execution.toNative_of_transverse_completion run.execution
    (teacher_self_router_causal work) box physical run.complete transverse (le_of_eq complete.1)
  have weakComplete := complete.toWeak_of_native crossing native same
    (teacher_ignition_below_ready ready) box physical
  obtain ⟨endpoint, fires⟩ := run.execution.observational_unique_weak box crossing.execution physical
    run.complete transverse weakComplete
  rw [run.only_fire] at fires
  exact ⟨endpoint.symm, List.perm_singleton.mp fires.symm⟩

end RecursiveLearning.Native
