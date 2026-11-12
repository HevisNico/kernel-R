import Teaching.LessonProbe
import Teaching.SelectorProtection

/-! Read either selector value at the same prepared charge. The FIRE date
    distinguishes the two values. The ensuing protection covers ERROR. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

noncomputable def selectorReadLogGain (high : Bool) : ℝ := if high then 3 / 5 else 0

private theorem selector_gain_bounds (high : Bool) :
    1 ≤ Real.exp (selectorReadLogGain high) ∧ Real.exp (selectorReadLogGain high) ≤ 11 / 6 := by
  cases high
  · norm_num [selectorReadLogGain]
  · simp only [selectorReadLogGain, ite_true]
    constructor
    · exact Real.one_le_exp (by norm_num)
    · have estimate := Real.exp_bound (x := (3 / 5 : ℝ)) (n := 10) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ] at estimate
      linarith [(abs_sub_le_iff.mp estimate).1]

theorem selector_response_coefficient_bounds :
    (391 / 250 : ℝ) ≤ a / (a - 1 / 2) ∧ a / (a - 1 / 2) ≤ 7821 / 5000 := by
  have positive : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  constructor
  · apply (le_div_iff₀ positive).mpr
    dsimp [a]
    linarith [KernelR.log_four_bounds.2]
  · apply (div_le_iff₀ positive).mpr
    dsimp [a]
    linarith [KernelR.log_four_bounds.1]

private theorem selector_early_mono {gain start : ℝ} (lower : 1 ≤ gain) (upper : gain ≤ 2) :
    MonotoneOn (readyPulse (39 / 50) gain start) (Icc start (start + 3 / 10)) := by
  apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_).monotoneOn
  · unfold readyPulse response
    fun_prop
  · intro t ht
    rw [interior_Icc] at ht
    have age : 0 ≤ t - start := sub_nonneg.mpr ht.1.le
    have ageUpper : t - start ≤ 3 / 10 := by linarith [ht.2]
    have decay : Real.exp (-(1 / 2) * (t - start)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have responseBound := response_upper age
    have product : a * (t - start) ≤ 21 / 50 :=
      (mul_le_mul a_coarse_bounds.2.le ageUpper age (by norm_num)).trans (by norm_num)
    have charge : readyPulse (39 / 50) gain start t ≤ 81 / 50 := by
      have bound : gain * response (t - start) ≤ 2 * (21 / 50) :=
        mul_le_mul upper (responseBound.trans product) (response_nonnegative age) (by norm_num)
      unfold readyPulse
      linarith
    have aLower : (27 / 20 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
    have drive : (27 / 20 : ℝ) * (29 / 50) ≤ gain * a * Real.exp (-a * (t - start)) := by
      have expLower : (29 / 50 : ℝ) ≤ Real.exp (-a * (t - start)) := by
        linarith [Real.add_one_le_exp (-a * (t - start))]
      have gainBound : (27 / 20 : ℝ) ≤ gain * a := by
        simpa using mul_le_mul lower aLower (by norm_num) (by linarith : 0 ≤ gain)
      exact mul_le_mul gainBound expLower (by norm_num) (by positivity)
    rw [(readyPulse_derivative _ _ _ _).deriv]
    linarith

private theorem selector_early_margin (high : Bool) {start t : ℝ}
    (after : start ≤ t) (early : t ≤ start + 1 / 10) :
    readyPulse (39 / 50) (Real.exp (selectorReadLogGain high)) start t < 1 := by
  have gain := selector_gain_bounds high
  have mono := selector_early_mono (start := start) gain.1 (by linarith [gain.2])
  apply (mono ⟨after, by linarith⟩ ⟨by linarith, by linarith⟩ early).trans_lt
  have head : Real.exp (-(1 / 20 : ℝ)) ≤ 952 / 1000 := by
    have estimate := Real.exp_bound (x := -(1 / 20 : ℝ)) (n := 8) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at estimate
    linarith [(abs_sub_le_iff.mp estimate).1]
  have tail : (869 / 1000 : ℝ) ≤ Real.exp (-a * (1 / 10)) := by
    apply le_trans _ (Real.exp_le_exp.mpr (show -(7 / 50 : ℝ) ≤ -a * (1 / 10) by
      linarith [a_coarse_bounds.2]))
    have estimate := Real.exp_bound (x := -(7 / 50 : ℝ)) (n := 8) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at estimate
    linarith [(abs_sub_le_iff.mp estimate).2]
  have pulse : response (1 / 10) ≤ 13 / 100 := by
    have difference : Real.exp (-(1 / 20 : ℝ)) - Real.exp (-a * (1 / 10)) ≤ 83 / 1000 := by linarith
    have product := mul_le_mul selector_response_coefficient_bounds.2 difference
      (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith [a_coarse_bounds.1]))) (by norm_num)
    unfold response
    rw [show -(1 / 2 : ℝ) * (1 / 10) = -(1 / 20) by norm_num]
    exact product.trans (by norm_num)
  have amplified := mul_le_mul gain.2 pulse (response_nonnegative (by norm_num)) (by norm_num)
  unfold readyPulse
  rw [add_sub_cancel_left, show -(1 / 2 : ℝ) * (1 / 10) = -(1 / 20) by norm_num]
  linarith

private theorem selector_low_before_split {start t : ℝ}
    (after : start ≤ t) (early : t ≤ start + 3 / 10) :
    readyPulse (39 / 50) 1 start t < 1 := by
  have mono := selector_early_mono (start := start) (gain := 1) (by norm_num) (by norm_num)
  apply (mono ⟨after, early⟩ ⟨by linarith, le_rfl⟩ early).trans_lt
  have head : Real.exp (-(3 / 20 : ℝ)) ≤ 8608 / 10000 := by
    have estimate := Real.exp_bound (x := -(3 / 20 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at estimate
    linarith [(abs_sub_le_iff.mp estimate).1]
  have tail : (6597 / 10000 : ℝ) ≤ Real.exp (-a * (3 / 10)) := by
    apply le_trans _ (Real.exp_le_exp.mpr (show -(4159 / 10000 : ℝ) ≤ -a * (3 / 10) by
      dsimp [a]; linarith [KernelR.log_four_bounds.2]))
    have estimate := Real.exp_bound (x := -(4159 / 10000 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at estimate
    linarith [(abs_sub_le_iff.mp estimate).2]
  have difference : Real.exp (-(3 / 20 : ℝ)) - Real.exp (-a * (3 / 10)) ≤ 2011 / 10000 := by linarith
  have product := mul_le_mul selector_response_coefficient_bounds.2 difference
    (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith [a_coarse_bounds.1]))) (by norm_num)
  unfold readyPulse response
  rw [add_sub_cancel_left, show -(1 / 2 : ℝ) * (3 / 10) = -(3 / 20) by norm_num]
  linarith

private theorem selector_high_after_split (start : ℝ) :
    1 < readyPulse (13 / 20) (Real.exp (3 / 5)) start (start + 39 / 200) := by
  have head : (907 / 1000 : ℝ) ≤ Real.exp (-(39 / 400 : ℝ)) := by
    have estimate := Real.exp_bound (x := -(39 / 400 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at estimate
    linarith [(abs_sub_le_iff.mp estimate).2]
  have tail : Real.exp (-a * (39 / 200)) ≤ (764 / 1000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr (show -a * (39 / 200) ≤ -(2703 / 10000 : ℝ) by
      dsimp [a]; linarith [KernelR.log_four_bounds.1]))
    have estimate := Real.exp_bound (x := -(2703 / 10000 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at estimate
    linarith [(abs_sub_le_iff.mp estimate).1]
  have difference : (143 / 1000 : ℝ) ≤ Real.exp (-(39 / 400 : ℝ)) - Real.exp (-a * (39 / 200)) := by linarith
  have product := mul_le_mul selector_response_coefficient_bounds.1 difference (by norm_num)
    (div_pos (by linarith [a_coarse_bounds.1]) (by linarith [a_coarse_bounds.1])).le
  have pulse : (223 / 1000 : ℝ) ≤ response (39 / 200) := by
    unfold response
    rw [show -(1 / 2 : ℝ) * (39 / 200) = -(39 / 400) by norm_num]
    exact (by norm_num : (223 / 1000 : ℝ) ≤ (391 / 250) * (143 / 1000)).trans product
  have amplified := mul_le_mul learnedProbe_gain.1 pulse (by norm_num : (0 : ℝ) ≤ 223 / 1000)
    (Real.exp_pos _).le
  unfold readyPulse
  rw [add_sub_cancel_left, show -(1 / 2 : ℝ) * (39 / 200) = -(39 / 400) by norm_num]
  linarith

private theorem selector_low_after_window (start : ℝ) :
    1 < readyPulse (13 / 20) 1 start (start + 4 / 5) := by
  have head : (6703 / 10000 : ℝ) ≤ Real.exp (-(2 / 5 : ℝ)) := by
    have estimate := Real.exp_bound (x := -(2 / 5 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at estimate
    linarith [(abs_sub_le_iff.mp estimate).2]
  have tail : Real.exp (-a * (4 / 5)) ≤ (3299 / 10000 : ℝ) := by
    have half : Real.exp (-a * (2 / 5)) ≤ (57436 / 100000 : ℝ) := by
      apply le_trans (Real.exp_le_exp.mpr (show -a * (2 / 5) ≤ -(55451 / 100000 : ℝ) by
        dsimp [a]; linarith [KernelR.log_four_bounds.1]))
      have estimate := Real.exp_bound (x := -(55451 / 100000 : ℝ)) (n := 11) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ] at estimate
      linarith [(abs_sub_le_iff.mp estimate).1]
    rw [show -a * (4 / 5) = -a * (2 / 5) + -a * (2 / 5) by ring, Real.exp_add]
    exact (mul_le_mul half half (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
  have difference : (3404 / 10000 : ℝ) ≤ Real.exp (-(2 / 5 : ℝ)) - Real.exp (-a * (4 / 5)) := by linarith
  have product := mul_le_mul selector_response_coefficient_bounds.1 difference (by norm_num)
    (div_pos (by linarith [a_coarse_bounds.1]) (by linarith [a_coarse_bounds.1])).le
  unfold readyPulse response
  rw [add_sub_cancel_left, show -(1 / 2 : ℝ) * (4 / 5) = -(2 / 5) by norm_num]
  linarith

/-- The first READY contacts are strict, with two disjoint latency windows. -/
theorem selector_read_response {charge start : ℝ} (high : Bool)
    (band : 13 / 20 ≤ charge ∧ charge ≤ 39 / 50) :
    ∃ latency : ℝ,
      (if high then 1 / 10 < latency ∧ latency < 39 / 200
        else 3 / 10 < latency ∧ latency < 4 / 5) ∧
      readyPulse charge (Real.exp (selectorReadLogGain high)) start (start + latency) = 1 ∧
      (∀ t ∈ Ico start (start + latency),
        readyPulse charge (Real.exp (selectorReadLogGain high)) start t < 1) ∧
      0 < deriv (readyPulse charge (Real.exp (selectorReadLogGain high)) start) (start + latency) := by
  let D : ℝ := if high then 39 / 200 else 4 / 5
  have deadline : 0 < D := by cases high <;> norm_num [D]
  have above : 1 < readyPulse charge (Real.exp (selectorReadLogGain high)) start (start + D) := by
    apply lt_of_lt_of_le _ (readyPulse_mono_initial band.1)
    cases high
    · simpa [selectorReadLogGain, D] using selector_low_after_window start
    · simpa [selectorReadLogGain, D] using selector_high_after_split start
  have continuous : Continuous (fun x : ℝ =>
      readyPulse charge (Real.exp (selectorReadLogGain high)) start (start + x)) := by
    unfold readyPulse response
    fun_prop
  obtain ⟨latency, positive, upper, root, pre⟩ := scalar_first_one_crossing continuous deadline
    (by rw [add_zero, readyPulse_initial]; linarith [band.2]) above
  have lower : (if high then (1 / 10 : ℝ) else 3 / 10) < latency := by
    by_contra notAfter
    have before := le_of_not_gt notAfter
    cases high with
    | false =>
      have margin := selector_low_before_split (start := start) (t := start + latency)
        (by linarith) (by change latency ≤ (3 / 10 : ℝ) at before; linarith)
      rw [show Real.exp (selectorReadLogGain false) = 1 by simp [selectorReadLogGain]] at root
      have strict := lt_of_le_of_lt (readyPulse_mono_initial band.2) margin
      rw [root] at strict
      exact (lt_irrefl _ strict)
    | true =>
      have margin := selector_early_margin true (start := start) (t := start + latency)
        (by linarith) (by change latency ≤ (1 / 10 : ℝ) at before; linarith)
      have strict := lt_of_le_of_lt (readyPulse_mono_initial band.2) margin
      rw [root] at strict
      exact (lt_irrefl _ strict)
  refine ⟨latency, ?_, root, ?_, ?_⟩
  · cases high <;> exact ⟨lower,upper⟩
  · intro t ht
    have margin := pre (t - start) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [show start + (t - start) = t by ring] using margin
  · apply readyPulse_transversal_of_later_value (Real.exp_pos _).le
      (show start + latency < start + D by linarith)
    rw [root]
    exact above

structure SelectorReadPrepared (s : Snapshot 1) (high : Bool) : Prop where
  ready : s.main 0 = .ready
  charge : 13 / 20 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 39 / 50
  gain : s.x 0 (.z 2) = selectorReadLogGain high
  recovery : 0 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 11 / 10
  auxiliary : ∀ p, s.aux 0 p = .ready ∧ RestBand (s.x 0 (.m p))
  raw : s.raw 0 2 = some s.time
  other : ∀ p, p ≠ 2 → s.raw 0 p = none
  empty : s.pending = []

structure SelectorReadRun (θ : Fin 1 → Parameters) (s : Snapshot 1) (high : Bool) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  horizon : ℝ
  complete : CompleteThrough execution horizon
  transversal : execution.ContactsTransversal
  latency : ℝ
  window : if high then 1 / 10 < latency ∧ latency < 39 / 200
    else 3 / 10 < latency ∧ latency < 4 / 5
  emissions : execution.ledger.emissions = [(0, s.time + latency)]
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)
  recovery : final.x 0 .b = s.x 0 .b
  auxiliaryReady : ∀ p, final.aux 0 p = .ready
  rawNone : ∀ p, final.raw 0 p = none
  empty : final.pending = []
  horizonBounds : s.time + 1 < horizon ∧ horizon < s.time + 419 / 300
  mainClock : final.main 0 = if horizon < s.time + latency + 1 then .fast else .slow
  chargeClock : final.x 0 .q = cadenceProtectedCharge (s.x 0 .b) (s.time + latency) horizon
  auxiliaryBelow : ∀ p, final.x 0 (.m p) < 1

/-- The read uses the actual admitted pulse. Both outcomes fire early
    enough to cover the whole ERROR phase with FAST or SLOW protection. -/
theorem selector_read_run_exists {θ ε s high}
    (box : @PhysicalBox 1 θ ε) (prepared : SelectorReadPrepared s high) :
    Nonempty (SelectorReadRun θ s high) := by
  have mainReady (i : Fin 1) : s.main i = .ready := by rw [Subsingleton.elim i 0]; exact prepared.ready
  have auxReady (i : Fin 1) (p : Port) : s.aux i p = .ready := by
    rw [Subsingleton.elim i 0]
    exact (prepared.auxiliary p).1
  have rawOther (i : Fin 1) (p : Port) (other : i ≠ 0 ∨ p ≠ 2) : s.raw i p = none := by
    rw [Subsingleton.elim i 0]
    exact prepared.other p (by simpa [Subsingleton.elim i 0] using other)
  have chargeBelow (i : Fin 1) : s.x i .q < 1 := by
    rw [Subsingleton.elim i 0]
    linarith [prepared.charge.2]
  have auxBelow (i : Fin 1) (p : Port) : s.x i (.m p) < 1 := by
    rw [Subsingleton.elim i 0]
    linarith [(prepared.auxiliary p).2.2]
  have margin : ∀ t, s.time ≤ t → t ≤ s.time + 1 / 10 →
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z 2))) s.time t < 1 := by
    rw [prepared.gain]
    intro t after early
    exact lt_of_le_of_lt (readyPulse_mono_initial prepared.charge.2) (selector_early_margin high after early)
  obtain ⟨mark⟩ := first_input_mark_of_response_margin_until_exists s box 0 2 mainReady auxReady
    prepared.raw rawOther chargeBelow auxBelow margin (prepared.auxiliary 2).2 (by simp [prepared.empty])
  obtain ⟨silent⟩ := mark.first_silent_of_response_margin_until_exists box margin (by simp [prepared.empty])
  obtain ⟨latency, window, root, prior, slope⟩ := selector_read_response (start := s.time) high prepared.charge
  have bounds : 1 / 10 < latency ∧ latency < 4 / 5 := by
    cases high <;> simp at window
    all_goals constructor <;> linarith [window.1, window.2]
  let F := s.time + latency
  let P := silent.final.time
  let E := silent.errorDate
  let R := E + Real.log 4 / (θ 0).le 2
  let B := s.x 0 .b
  have afterMark : P < F := by
    dsimp [P, F]
    rw [silent.date]
    linarith [silent.deadline, bounds.1]
  have startMark : s.time ≤ P := by
    dsimp [P]
    rw [silent.date]
    change s.time ≤ s.time + mark.latency + Real.log (5 / 4) / (θ 0).lm 2
    linarith [mark.early, (box.aux_durations_positive 0 2).1]
  have errorBounds := silent.errorDate_bounds box
  have beforeError : F < E := by dsimp [F, E]; linarith [bounds.2, errorBounds.1]
  have cycle := box.first_cycle_schedule 0 2 ⟨mark.early, mark.deadline⟩
  have returnDate : R = s.time + mark.latency + auxCycleDuration (θ 0) 2 := by
    dsimp [R, E, FirstInputSilent.errorDate]
    rw [silent.date]
    unfold FirstInputMark.silentDate auxCycleDuration
    ring
  have returnBounds : s.time + 1 < R ∧ R < s.time + 419 / 300 := by
    rw [returnDate]
    constructor <;> linarith [cycle.2.2.2.2.1, cycle.2.2.2.2.2]
  have errorBeforeReturn : E < R := by dsimp [R]; linarith [(box.aux_durations_positive 0 2).2.2]
  have emptySilent : silent.final.pending = [] := silent.queue_preserved.trans prepared.empty
  have sensorGuard (t : ℝ) (ht : t ∈ Icc P F) :
      1 / 10 < (4 / 5 : ℝ) * Real.exp (-(θ 0).ls 2 * (t - P)) := by
    have decay := protected_decay_schedule (initial := (4 / 5 : ℝ)) (floor := (1 / 10 : ℝ))
      (by norm_num) (by norm_num) (box.rates_positive 0 2).2.1
    apply decay.2.2 (t - P) (by linarith [ht.1])
    norm_num
    have errorDate : E = P + Real.log 8 / (θ 0).ls 2 := rfl
    linarith [ht.2]
  let flow : Flow θ silent.final (silent.learnedFireBefore latency) :=
    readyProtectedFlow silent.final 0 2 .silent (some s.time) afterMark (Or.inr rfl)
      silent.main_ready silent.aux_silent silent.aux_other silent.raw_active silent.raw_other
      (by intro o eq; cases Option.some.inj eq; exact ⟨startMark, by linarith [bounds.2]⟩)
      silent.main_below silent.aux_below
      (by
        intro t ht
        rw [silent.response_restart, prepared.gain]
        exact prior t ⟨startMark.trans ht.1, ht.2⟩)
      (by
        intro t ht
        simpa only [reduceCtorEq, ite_false, silent.sensor_charge, protectedReadyRate] using
          sensorGuard t ⟨ht.1, ht.2.le⟩)
      (by simp [emptySilent])
  let pre := silent.learnedFireBefore latency
  let fired := silent.learnedFireFinal (fun _ _ => []) latency
  have threshold : pre.x 0 .q = 1 := by
    simp only [pre, FirstInputSilent.learnedFireBefore, readyProtectedEnd, readyProtectedValues,
      protectedRawAmplitude, ite_true]
    rw [silent.response_restart, prepared.gain]
    exact root
  let jump : Jump (fun _ _ => []) pre fired := .fire pre 0 (silent.main_ready 0) threshold
  let firing : Execution θ (fun _ _ => []) s fired :=
    (silent.execution _).append (.cons (.flow flow) (.cons (.jump jump) (.nil _)))
  have firingTransverse : firing.ContactsTransversal := by
    apply (Execution.contactsTransversal_append _ _).2
    refine ⟨silent.contacts_transversal _, ?_, trivial⟩
    change 0 < field θ pre pre.x pre.time 0 .q
    rw [silent.learnedFire_field_eq_deriv latency (by linarith [bounds.1]) (by linarith [bounds.2]),
      prepared.gain]
    exact slope
  have firingEmissions : firing.ledger.emissions = [(0, F)] := by
    have silentEmissions : (silent.execution (fun _ _ => [])).ledger.emissions = [] := by
      simp [FirstInputSilent.execution, FirstInputSilent.continuation, FirstInputMark.execution,
        Execution.emissions_append, Execution.ledger, Move.ledger, Flow.ledger, Jump.ledger,
        Ledger.add, Ledger.zero]
    have jumpEmissions : jump.ledger.emissions = [(0, F)] := rfl
    rw [Execution.emissions_append, silentEmissions]
    change [] ++ ([] ++ (jump.ledger.emissions ++ [])) = _
    rw [jumpEmissions]
    rfl
  have firingDeliveries : firing.deliveries = [] := by
    simp [firing, jump, FirstInputSilent.execution, FirstInputSilent.continuation, FirstInputMark.execution,
      Execution.deliveries_append, Execution.deliveries, Move.deliveries, Jump.deliveries]
  have firedGains (p : Port) : fired.x 0 (.z p) = s.x 0 (.z p) := silent.gain_preserved 0 p
  have firedRecovery : fired.x 0 .b = B := silent.recovery_preserved 0
  have firedEmpty : fired.pending = [] := by
    change silent.final.pending ++ [] = []
    simp [emptySilent]
  have otherBelow (i : Fin 1) (p : Port) (other : i ≠ 0 ∨ p ≠ 2) : fired.x i (.m p) < 1 := by
    have different : p ≠ 2 := by simpa [Subsingleton.elim i 0] using other
    have retained := firing.aux_no_input_rest_band 0 p (prepared.auxiliary p).1
      (prepared.auxiliary p).2 (prepared.other p different) (by simp [NoArrivalAt, firingDeliveries])
    rw [Subsingleton.elim i 0]
    linarith [retained.1.2.2]
  have firedSensor : fired.x 0 (.m 2) = (4 / 5 : ℝ) *
      Real.exp (-protectedReadyRate (θ 0) 2 .silent * (F - P)) := by
    simp only [fired, FirstInputSilent.learnedFireFinal, FirstInputSilent.learnedFireBefore,
      setMain, readyProtectedEnd, readyProtectedValues, and_self, ite_true, silent.sensor_charge]
    rfl
  obtain ⟨decay⟩ := selector_protected_aux_phase_exists (route := fun _ _ => []) box fired 2 .silent
    s.time E F P (4 / 5) B (Or.inl rfl) beforeError
    (by change MainMode.fast = (if F < F + 1 then _ else _); simp)
    silent.aux_silent silent.aux_other
    (by change silent.final.raw 0 2 = _; rw [ite_eq_left (by change F < s.time + 1; dsimp [F]; linarith [bounds.2])]
        exact silent.raw_active)
    silent.raw_other (by change s.time ≤ F; dsimp [F]; linarith [bounds.1])
    (by dsimp [F]; linarith [bounds.1]) otherBelow
    (by change pre.x 0 .q = cadenceProtectedCharge B F F; rw [threshold]; simp [cadenceProtectedCharge])
    firedSensor firedRecovery prepared.recovery afterMark.le
    (by dsimp [E, F]; linarith [errorBounds.2, bounds.1])
    (by norm_num [fastAuxFloor])
    (by change E ≤ P + Real.log ((4 / 5 : ℝ) / (1 / 10)) / (θ 0).ls 2
        norm_num; rfl)
    (by simp [firedEmpty])
  have errorGuard : decay.final.x 0 (.m 2) = 1 / 10 := by
    rw [decay.sensor_clock]
    exact silent_full_decay_end (start := P) (ne_of_gt (box.rates_positive 0 2).2.1)
  let errorStart := setAux decay.final 0 2 .error
  let errorJump : Execution θ (fun _ _ => []) decay.final errorStart :=
    .cons (.jump (.error decay.final 0 2 decay.aux_mode errorGuard)) (.nil _)
  have errorOthers (i : Fin 1) (p : Port) (other : i ≠ 0 ∨ p ≠ 2) :
      errorStart.aux i p = .ready := by
    have different : p ≠ 2 := by simpa [Subsingleton.elim i 0] using other
    rw [Subsingleton.elim i 0]
    simpa [errorStart, setAux, different] using decay.aux_other 0 p (Or.inr different)
  obtain ⟨error⟩ := selector_protected_aux_phase_exists (route := fun _ _ => []) box errorStart 2 .error
    s.time R F E (1 / 10) B (Or.inr rfl)
    (by change decay.final.time < R; rwa [decay.date])
    (by simpa only [errorStart, setAux, decay.date] using decay.main_mode)
    (by simp [errorStart, setAux]) errorOthers
    (by simpa only [errorStart, setAux, decay.date] using decay.raw_mode)
    decay.raw_other (by change s.time ≤ decay.final.time; rw [decay.date]; dsimp [E]; linarith [errorBounds.1])
    (by dsimp [F]; linarith [bounds.1]) decay.other_below
    (by simpa only [errorStart, setAux, decay.date] using decay.main_clock)
    (by change decay.final.x 0 (.m 2) = _; rw [errorGuard]; simp [errorStart, setAux, decay.date])
    ((decay.recovery 0).trans firedRecovery) prepared.recovery
    (by change E ≤ decay.final.time; rw [decay.date])
    (by dsimp [F]; linarith [returnBounds.2, bounds.1])
    (by norm_num [fastAuxFloor])
    (by change R ≤ E + Real.log ((1 / 10 : ℝ) / (1 / 40)) / (θ 0).le 2; norm_num; rfl)
    (by change ∀ d ∈ decay.final.pending, R ≤ d.due; simp [decay.pending, firedEmpty])
  have readyGuard : error.final.x 0 (.m 2) = 1 / 40 := by
    rw [error.sensor_clock]
    have endValue := (protected_decay_schedule (by norm_num : (0 : ℝ) < 1 / 40)
      (by norm_num : (1 / 40 : ℝ) < 1 / 10) (box.rates_positive 0 2).2.2).2.1
    norm_num at endValue
    simpa only [R, protectedReadyRate, add_sub_cancel_left, neg_mul] using endValue
  let final := setAux error.final 0 2 .ready
  let readyJump : Execution θ (fun _ _ => []) error.final final :=
    .cons (.jump (.auxReady error.final 0 2 error.aux_mode readyGuard)) (.nil _)
  let execution := ((firing.append decay.execution).append errorJump).append (error.execution.append readyJump)
  have finalAux (p : Port) : final.aux 0 p = .ready := by
    by_cases same : p = 2
    · subst p; simp [final, setAux]
    · simpa [final, setAux, same] using error.aux_other 0 p (Or.inr same)
  have finalRaw (p : Port) : final.raw 0 p = none := by
    by_cases same : p = 2
    · subst p
      simpa only [final, setAux, not_lt.mpr returnBounds.1.le, ite_false] using error.raw_mode
    · exact error.raw_other 0 p (Or.inr same)
  have finalEmpty : final.pending = [] := error.pending.trans (decay.pending.trans firedEmpty)
  have finalGuard : BeforeGuards final final.x := by
    constructor
    · intro i
      rw [Subsingleton.elim i 0]
      change (match error.final.main 0 with
        | .ready => error.final.x 0 .q < 1
        | .fast => 1 / 4 < error.final.x 0 .q
        | .slow => 1 / 10 < error.final.x 0 .q)
      rw [error.main_mode, error.main_clock]
      by_cases fast : R < F + 1
      · simp only [cadenceProtectedCharge, fast, ite_true]
        rw [← exp_neg_a]
        apply Real.exp_lt_exp.mpr
        nlinarith [a_coarse_bounds.1]
      · simp only [cadenceProtectedCharge, fast, ite_false]
        exact selector_slow_charge_preguard prepared.recovery (le_of_not_gt fast)
          (by dsimp [F]; linarith [returnBounds.2, bounds.1])
    · intro i p
      rw [Subsingleton.elim i 0, finalAux]
      change error.final.x 0 (.m p) < 1
      by_cases same : p = 2
      · subst p; rw [readyGuard]; norm_num
      · exact error.other_below 0 p (Or.inr same)
  refine ⟨{
    final := final, execution := execution, horizon := R, complete := ⟨error.date, ?_, by simp [finalEmpty]⟩
    transversal := ?_, latency := latency, window := window, emissions := ?_
    gains := fun p => (error.gains 0 p).trans ((decay.gains 0 p).trans (firedGains p))
    recovery := (error.recovery 0).trans ((decay.recovery 0).trans firedRecovery)
    auxiliaryReady := finalAux, rawNone := finalRaw, empty := finalEmpty, horizonBounds := returnBounds
    mainClock := error.main_mode, chargeClock := error.main_clock
    auxiliaryBelow := fun p => by simpa only [finalAux] using finalGuard.2 0 p
  }⟩
  · intro v
    apply finalGuard.no_jump
    · intro i p origin active
      rw [Subsingleton.elim i 0, finalRaw] at active
      contradiction
    · simp [finalEmpty]
  · simp [execution, firingTransverse, decay.contacts_transversal, error.contacts_transversal,
      errorJump, readyJump, Execution.ContactsTransversal, Jump.ContactTransversal]
  · simp [execution, Execution.emissions_append, firingEmissions, decay.emissions, error.emissions,
      errorJump, readyJump, Execution.ledger, Move.ledger, Jump.ledger, Ledger.add, Ledger.zero, F]

theorem SelectorReadRun.reads_high {θ s high} (run : SelectorReadRun θ s high) :
    run.latency < 1 / 5 ↔ high = true := by
  cases high
  · have late : 3 / 10 < run.latency := run.window.1
    exact ⟨fun h => (not_lt_of_ge (show 1 / 5 ≤ run.latency by linarith) h).elim, fun h => Bool.noConfusion h⟩
  · have early : run.latency < 39 / 200 := run.window.2
    exact ⟨fun _ => rfl, fun _ => by linarith⟩

/-- A routed read can be decoded with delays between 0.3 and 0.4.
    The receiver's reference to the read-pulse arrival may err by 0.0025. -/
theorem SelectorReadRun.reads_high_after_wire {θ s high} (run : SelectorReadRun θ s high)
    {delay reference : ℝ} (wire : 3 / 10 ≤ delay ∧ delay ≤ 2 / 5)
    (clock : s.time - 1 / 400 ≤ reference ∧ reference ≤ s.time + 1 / 400) :
    s.time + run.latency + delay < reference + 239 / 400 ↔ high = true := by
  cases high
  · have late : 3 / 10 < run.latency := run.window.1
    exact ⟨fun h => by linarith [wire.1, clock.2], fun h => Bool.noConfusion h⟩
  · have early : run.latency < 39 / 200 := run.window.2
    exact ⟨fun _ => rfl, fun _ => by linarith [wire.2, clock.1]⟩

/-- Equality at sensor return excludes a gain change even on an intermediate
    cut of the native read, by the existing monotonicity theorem. -/
theorem SelectorReadRun.gain_at_prefix {θ ε s high middle}
    (run : SelectorReadRun θ s high) (box : @PhysicalBox 1 θ ε)
    {cut : Execution θ (fun _ _ => []) s middle} (prefixTrace : run.execution.IsPrefix cut)
    (p : Port) : middle.x 0 (.z p) = s.x 0 (.z p) :=
  prefixTrace.gain_eq_of_final box 0 p (run.gains p)

private theorem selector_read_initial {s high} (prepared : SelectorReadPrepared s high) :
    InitiallyBelowReady s := by
  intro i c ready
  rw [Subsingleton.elim i 0]
  cases c with
  | q => linarith [prepared.charge.2]
  | m p => linarith [(prepared.auxiliary p).2.2]
  | z _ => exact False.elim ready
  | b => exact False.elim ready
  | energy => exact False.elim ready

/-- The native read is a complete upward-crossing history through the
    return of the sensor to READY. -/
theorem selector_read_crossing_exists {θ ε s high}
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ s)
    (prepared : SelectorReadPrepared s high) :
    ∃ (run : SelectorReadRun θ s high)
      (crossing : CrossingExecution θ (fun _ _ => []) s run.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing run.horizon := by
  obtain ⟨run⟩ := selector_read_run_exists box prepared
  have initial := selector_read_initial prepared
  exact ⟨run, run.execution.toCrossing initial box physical run.transversal, rfl,
    run.complete.toCrossing run.execution initial box physical run.transversal⟩

/-- The firing window and unchanged gains hold for every complete
    first-contact execution through the sensor's return horizon. -/
theorem SelectorReadRun.every_complete {θ ε s high final}
    (run : SelectorReadRun θ s high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s)
    (execution : Execution θ (fun _ _ => []) s final) (complete : CompleteThrough execution run.horizon) :
    execution.ledger.emissions = [(0, s.time + run.latency)] ∧
      ∀ p, final.x 0 (.z p) = s.x 0 (.z p) := by
  obtain ⟨endpoint, fires⟩ :=
    execution.observational_unique run.execution box physical complete run.complete
  rw [run.emissions] at fires
  exact ⟨List.perm_singleton.mp fires, fun p => by rw [endpoint.values, run.gains]⟩

/-- All complete geometric reads retain the exact FIRE and all gains. -/
theorem SelectorReadRun.every_crossing_complete {θ ε s high final}
    (run : SelectorReadRun θ s high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (prepared : SelectorReadPrepared s high)
    (crossing : CrossingExecution θ (fun _ _ => []) s final)
    (complete : CrossingCompleteThrough crossing run.horizon) :
    crossing.execution.ledger.emissions = [(0, s.time + run.latency)] ∧
      ∀ p, final.x 0 (.z p) = s.x 0 (.z p) := by
  have routing : StrictCausalRouter (fun (_ : Fin 1) _ => []) :=
    fun _ _ _ member => False.elim (List.not_mem_nil member)
  obtain ⟨native, same⟩ := crossing.execution.toNative_of_transverse_completion run.execution
    routing box physical run.complete run.transversal (le_of_eq complete.1)
  have weakComplete := complete.toWeak_of_native crossing native same (selector_read_initial prepared)
    box physical
  obtain ⟨endpoint, fires⟩ := run.execution.observational_unique_weak box crossing.execution physical
    run.complete run.transversal weakComplete
  rw [run.emissions] at fires
  exact ⟨List.perm_singleton.mp fires.symm, fun p => by rw [← endpoint.values, run.gains]⟩

/-- The two concrete read preparations differ only in the stored gain.
    The canonical selector pulse is already active at time `time`. -/
noncomputable def selectorReadStart (high : Bool) (time : ℝ) (recovery : ℝ := 2 / 25) : Snapshot 1 where
  time := time
  x := fun _ c => match c with
    | .q => 7 / 10
    | .m _ => 1 / 40
    | .z p => if p = 2 then selectorReadLogGain high else 0
    | .b => recovery
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ p => if p = 2 then some time else none
  pending := []

theorem prepared_selector_read_with_recovery_crossing_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (high : Bool) (time recovery : ℝ) (band : 0 ≤ recovery ∧ recovery ≤ 11 / 10) :
    ∃ (run : SelectorReadRun θ (selectorReadStart high time recovery) high)
      (crossing : CrossingExecution θ (fun _ _ => []) (selectorReadStart high time recovery) run.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing run.horizon := by
  have cap (i : Fin 1) (p : Port) : 2 ≤ (θ i).cap p := by
    have lower := (box.2 i p).1.1
    rcases box.1 with h | h
    all_goals rw [h] at lower
    all_goals norm_num at lower
    all_goals linarith
  have physical : PhysicalInvariant θ (selectorReadStart high time recovery) := by
    refine ⟨fun i => by norm_num [UpperRegion, selectorReadStart, auxUpper, band.1], ?_,
      fun _ => band.2, fun i => by norm_num [selectorReadStart]⟩
    intro i p
    change (if p = 2 then selectorReadLogGain high else 0) ≤ Real.log ((θ i).cap p)
    have logCap := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) (cap i p)
    have logTwo := Real.log_two_gt_d9
    split
    · cases high <;> simp [selectorReadLogGain] <;> linarith
    · linarith
  exact selector_read_crossing_exists box physical
    ⟨rfl, by norm_num [selectorReadStart], rfl, band,
      fun _ => ⟨rfl, by norm_num [selectorReadStart, RestBand]⟩, rfl,
      fun p other => by simp [selectorReadStart, other], rfl⟩

theorem prepared_selector_read_crossing_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (high : Bool) (time : ℝ) :
    ∃ (run : SelectorReadRun θ (selectorReadStart high time) high)
      (crossing : CrossingExecution θ (fun _ _ => []) (selectorReadStart high time) run.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing run.horizon :=
  prepared_selector_read_with_recovery_crossing_exists box high time (2 / 25) (by norm_num)

/-- With recovery already saturated, either stored value still has a
complete physical read, preserving all gains and the cap. -/
theorem capped_selector_read_crossing_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (high : Bool) (time : ℝ) :
    ∃ (run : SelectorReadRun θ (selectorReadStart high time (11 / 10)) high)
      (crossing : CrossingExecution θ (fun _ _ => []) (selectorReadStart high time (11 / 10)) run.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing run.horizon ∧
        run.final.x 0 .b = 11 / 10 := by
  obtain ⟨run, crossing, trace, complete⟩ :=
    prepared_selector_read_with_recovery_crossing_exists box high time (11 / 10) (by norm_num)
  exact ⟨run, crossing, trace, complete, run.recovery⟩

end RecursiveLearning.Native
