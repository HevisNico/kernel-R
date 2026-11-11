import SilentStep

/-! The cell after a FIRE. While the main cell is in FAST or SLOW, and no
sensor is in MARK, the main charge and every sensor evolve independently:
the input current reaches neither, no gain is written and the recovery
rate is constant. The flow is explicit for any number of busy sensors. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- The main cell is not READY, no sensor is in MARK, and a READY sensor
has no live pulse. -/
structure Refractory (s : Snapshot 1) : Prop where
  main : s.main 0 ≠ .ready
  no_mark : ∀ q, s.aux 0 q ≠ .mark
  ready_raw : ∀ q, s.aux 0 q = .ready → s.raw 0 q = none

noncomputable def mainRate (s : Snapshot 1) : ℝ :=
  match s.main 0 with
  | .ready => 0
  | .fast => a
  | .slow => s.x 0 .b

noncomputable def sensorRate (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) : ℝ :=
  protectedReadyRate (θ 0) q (s.aux 0 q)

noncomputable def refractoryCharge (s : Snapshot 1) (t : ℝ) : ℝ :=
  s.x 0 .q * Real.exp (-mainRate s * (t - s.time))

noncomputable def refractorySensor (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port)
    (t : ℝ) : ℝ :=
  if s.aux 0 q = .ready then relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t
  else s.x 0 (.m q) * Real.exp (-sensorRate θ s q * (t - s.time))

noncomputable def refractoryWork (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) : ℝ :=
  (match s.main 0 with
    | .ready => 0
    | .fast => a * refractoryCharge s t
    | .slow => 11 / 10) +
  ∑ q : Port, if s.aux 0 q = .ready then 0 else sensorRate θ s q * refractorySensor θ s q t

noncomputable def refractoryEnergy (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) : ℝ :=
  relax 10 100 (s.x 0 .energy) s.time t - linearConvolution 10 (refractoryWork θ s) s.time t

noncomputable def refractoryValues (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) :
    Values 1 := fun _ c => match c with
  | .q => refractoryCharge s t
  | .m q => refractorySensor θ s q t
  | .z q => s.x 0 (.z q)
  | .b => s.x 0 .b
  | .energy => refractoryEnergy θ s t

noncomputable def refractoryAt (θ : Fin 1 → Parameters) (s : Snapshot 1) (T : ℝ) : Snapshot 1 :=
  {s with time := T, x := refractoryValues θ s T}

noncomputable def refractoryRhs (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) : Coord → ℝ
  | .q => -mainRate s * refractoryCharge s t
  | .m q => if s.aux 0 q = .ready then (1 / 2) * (1 / 40 - refractorySensor θ s q t)
      else -sensorRate θ s q * refractorySensor θ s q t
  | .z _ => 0
  | .b => 0
  | .energy => 10 * (100 - refractoryEnergy θ s t) - refractoryWork θ s t

theorem refractorySensor_continuous (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) :
    Continuous (refractorySensor θ s q) := by
  unfold refractorySensor
  by_cases h : s.aux 0 q = .ready
  · simp only [h, ite_true]
    unfold relax
    fun_prop
  · simp only [h, ite_false]
    fun_prop

theorem refractoryWork_continuous (θ : Fin 1 → Parameters) (s : Snapshot 1) :
    Continuous (refractoryWork θ s) := by
  unfold refractoryWork
  apply Continuous.add
  · rcases hm : s.main 0 with _ | _ | _ <;> simp only [refractoryCharge] <;> fun_prop
  · apply continuous_finsetSum
    intro q _
    by_cases h : s.aux 0 q = .ready
    · simp only [h, ite_true]
      fun_prop
    · simp only [h, ite_false]
      exact continuous_const.mul (refractorySensor_continuous θ s q)

theorem refractoryEnergy_derivative (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) :
    HasDerivAt (refractoryEnergy θ s)
      (10 * (100 - refractoryEnergy θ s t) - refractoryWork θ s t) t := by
  exact ((relax_derivative 10 100 (s.x 0 .energy) s.time t).sub
    (linearConvolution_derivative (refractoryWork_continuous θ s) 10 s.time t)).congr_deriv
      (by dsimp only [refractoryEnergy]; ring)

theorem refractoryRhs_continuous (θ : Fin 1 → Parameters) (s : Snapshot 1) (c : Coord) :
    Continuous (fun t => refractoryRhs θ s t c) := by
  have sensor := refractorySensor_continuous θ s
  have work := refractoryWork_continuous θ s
  have energy : Continuous (refractoryEnergy θ s) :=
    continuous_iff_continuousAt.mpr fun t => (refractoryEnergy_derivative θ s t).continuousAt
  cases c with
  | q => simp only [refractoryRhs, refractoryCharge]; fun_prop
  | m q =>
    by_cases h : s.aux 0 q = .ready
    · simp only [refractoryRhs, h, ite_true]
      exact continuous_const.mul (continuous_const.sub (sensor q))
    · simp only [refractoryRhs, h, ite_false]
      exact continuous_const.mul (sensor q)
  | z q => simp only [refractoryRhs]; fun_prop
  | b => simp only [refractoryRhs]; fun_prop
  | energy =>
    simp only [refractoryRhs]
    exact (continuous_const.mul (continuous_const.sub energy)).sub work

theorem refractoryValues_initial (θ : Fin 1 → Parameters) (s : Snapshot 1) :
    refractoryValues θ s s.time = s.x := by
  funext j c
  rw [Subsingleton.elim j 0]
  cases c with
  | q => simp [refractoryValues, refractoryCharge]
  | m q =>
    by_cases h : s.aux 0 q = .ready <;>
      simp [refractoryValues, refractorySensor, h, relax_initial]
  | z q => rfl
  | b => rfl
  | energy => simp [refractoryValues, refractoryEnergy, relax_initial, linearConvolution_initial]

theorem refractoryValues_derivative (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ)
    (i : Fin 1) (c : Coord) :
    HasDerivAt (fun v => refractoryValues θ s v i c) (refractoryRhs θ s t c) t := by
  cases c with
  | q =>
    have h := ((((hasDerivAt_id t).sub_const s.time).const_mul (-mainRate s)).exp).const_mul
      (s.x 0 .q)
    have f : (fun v => refractoryValues θ s v i .q) =
        fun v => s.x 0 .q * Real.exp (-mainRate s * (id v - s.time)) := rfl
    rw [f]
    convert h using 1
    simp only [refractoryRhs, refractoryCharge, id_eq]
    ring
  | m q =>
    by_cases hr : s.aux 0 q = .ready
    · have h := relax_derivative (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t
      have f : (fun v => refractoryValues θ s v i (.m q)) =
          relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time := by
        funext v
        simp [refractoryValues, refractorySensor, hr]
      rw [f]
      simpa [refractoryRhs, refractorySensor, hr] using h
    · have h := ((((hasDerivAt_id t).sub_const s.time).const_mul (-sensorRate θ s q)).exp).const_mul
        (s.x 0 (.m q))
      have f : (fun v => refractoryValues θ s v i (.m q)) =
          fun v => s.x 0 (.m q) * Real.exp (-sensorRate θ s q * (id v - s.time)) := by
        funext v
        simp [refractoryValues, refractorySensor, hr]
      rw [f]
      convert h using 1
      simp only [refractoryRhs, refractorySensor, hr, ite_false, id_eq]
      ring
  | z q => exact hasDerivAt_const t (s.x 0 (.z q))
  | b => exact hasDerivAt_const t (s.x 0 .b)
  | energy => exact refractoryEnergy_derivative θ s t

/-- In the refractory regime the kernel field is the explicit one. -/
theorem refractory_field {θ : Fin 1 → Parameters} {s : Snapshot 1} (hs : Refractory s)
    (t : ℝ) (i : Fin 1) (c : Coord) :
    field θ s (refractoryValues θ s t) t i c = refractoryRhs θ s t c := by
  rw [Subsingleton.elim i 0]
  have current0 (q : Port) (h : s.aux 0 q = .ready) : current s 0 q t = 0 := by
    simp [current, hs.ready_raw q h]
  have noError (q : Port) : errorAct θ s (refractoryValues θ s t) 0 q = 0 := by
    simp [errorAct, hs.main]
  have noMark (q : Port) : markAct θ s (refractoryValues θ s t) 0 q = 0 := by
    simp [markAct, hs.no_mark q]
  have drain (q : Port) :
      (if s.aux 0 q = .ready then (θ 0).inputGain q * current s 0 q t
        else auxDrain (θ 0) (s.aux 0 q) q (refractoryValues θ s t 0 (.m q))) =
      if s.aux 0 q = .ready then 0 else sensorRate θ s q * refractorySensor θ s q t := by
    by_cases h : s.aux 0 q = .ready
    · simp [h, current0 q h]
    · simp only [h, ite_false]
      rcases hm : s.aux 0 q with _ | _ | _ | _
      · exact absurd hm h
      · exact absurd hm (hs.no_mark q)
      · simp [auxDrain, sensorRate, protectedReadyRate, hm, refractoryValues]
      · simp [auxDrain, sensorRate, protectedReadyRate, hm, refractoryValues]
  cases c with
  | q =>
    rcases hm : s.main 0 with _ | _ | _
    · exact absurd hm hs.main
    · simp [field, hm, refractoryRhs, mainRate, refractoryValues]
    · simp [field, hm, refractoryRhs, mainRate, refractoryValues]
  | m q =>
    by_cases h : s.aux 0 q = .ready
    · simp [field, h, current0 q h, refractoryRhs, refractoryValues]
    · have d := drain q
      simp only [h, ite_false] at d
      simp only [field, h, ite_false, refractoryRhs, d]
      ring
  | z q => simp [field, noError, refractoryRhs]
  | b => simp [field, noMark, refractoryRhs]
  | energy =>
    have w : work θ s (refractoryValues θ s t) 0 t = refractoryWork θ s t := by
      simp only [work, refractoryWork, noError, noMark, drain, Finset.sum_const_zero, add_zero]
      rcases hm : s.main 0 with _ | _ | _
      · exact absurd hm hs.main
      · simp [refractoryValues]
      · simp
    simp [field, w, refractoryRhs, refractoryValues]

/-- The explicit flow of the refractory regime. No threshold is attached:
the guards are checked by the caller at the realized levels. -/
noncomputable def refractoryDynamics {θ : Fin 1 → Parameters} (s : Snapshot 1) {T : ℝ}
    (ht : s.time < T) (hs : Refractory s)
    (support : ∀ q o, s.raw 0 q = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) : FlowDynamics θ s (refractoryAt θ s T) where
  positive := ht
  path := refractoryValues θ s
  initial := refractoryValues_initial θ s
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun i c => (continuous_iff_continuousAt.mpr fun t =>
    (refractoryValues_derivative θ s t i c).continuousAt).continuousOn
  integrable := by
    intro i c
    have e : (fun t => field θ s (refractoryValues θ s t) t i c) = fun t => refractoryRhs θ s t c :=
      funext fun t => refractory_field hs t i c
    rw [e]
    exact (refractoryRhs_continuous θ s c).intervalIntegrable _ _
  mark_integrable := by
    intro i q
    rw [Subsingleton.elim i 0]
    simp [markAct, hs.no_mark q]
  integral_eq := by
    intro t _ i c
    have e : (fun t => field θ s (refractoryValues θ s t) t i c) = fun t => refractoryRhs θ s t c :=
      funext fun t => refractory_field hs t i c
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => refractoryValues_derivative θ s v i c)
      ((refractoryRhs_continuous θ s c).intervalIntegrable s.time t)
    rw [refractoryValues_initial] at h
    rw [e]
    linarith
  raw_support := by
    intro i q o h
    rw [Subsingleton.elim i 0] at h
    exact support q o h
  pending_urgent := hp

/-! ### Event dates -/

/-- Time for an exponential decay at `rate` to bring `x` down to `thr`. -/
noncomputable def decayTime (x thr rate : ℝ) : ℝ := Real.log (x / thr) / rate

theorem decay_eq {x thr rate : ℝ} (hx : 0 < x) (hthr : 0 < thr) (hr : 0 < rate) (d : ℝ) :
    x * Real.exp (-rate * d) = thr * Real.exp (rate * (decayTime x thr rate - d)) := by
  have h : rate * (decayTime x thr rate - d) = Real.log (x / thr) + -rate * d := by
    unfold decayTime
    rw [mul_sub, mul_div_cancel₀ _ hr.ne']
    ring
  have hne := hthr.ne'
  rw [h, Real.exp_add, Real.exp_log (div_pos hx hthr)]
  field_simp

theorem decay_above {x thr rate d : ℝ} (hx : 0 < x) (hthr : 0 < thr) (hr : 0 < rate)
    (h : d < decayTime x thr rate) : thr < x * Real.exp (-rate * d) := by
  rw [decay_eq hx hthr hr]
  have one : 1 < Real.exp (rate * (decayTime x thr rate - d)) :=
    Real.one_lt_exp_iff.mpr (mul_pos hr (sub_pos.mpr h))
  nlinarith

theorem decay_ge {x thr rate d : ℝ} (hx : 0 < x) (hthr : 0 < thr) (hr : 0 < rate)
    (h : d ≤ decayTime x thr rate) : thr ≤ x * Real.exp (-rate * d) := by
  rw [decay_eq hx hthr hr]
  have one : 1 ≤ Real.exp (rate * (decayTime x thr rate - d)) :=
    Real.one_le_exp (mul_nonneg hr.le (sub_nonneg.mpr h))
  nlinarith

theorem decay_at {x thr rate : ℝ} (hx : 0 < x) (hthr : 0 < thr) (hr : 0 < rate) :
    x * Real.exp (-rate * decayTime x thr rate) = thr := by
  rw [decay_eq hx hthr hr, sub_self, mul_zero, Real.exp_zero, mul_one]

theorem decayTime_shift {x thr rate : ℝ} (hx : 0 < x) (hthr : 0 < thr) (hr : 0 < rate) (d : ℝ) :
    decayTime (x * Real.exp (-rate * d)) thr rate = decayTime x thr rate - d := by
  rw [decay_eq hx hthr hr]
  generalize decayTime x thr rate - d = w
  unfold decayTime
  rw [mul_div_cancel_left₀ _ hthr.ne', Real.log_exp, mul_div_cancel_left₀ _ hr.ne']

theorem decayTime_nonneg {x thr rate : ℝ} (hthr : 0 < thr) (hr : 0 < rate) (h : thr ≤ x) :
    0 ≤ decayTime x thr rate :=
  div_nonneg (Real.log_nonneg ((one_le_div hthr).mpr h)) hr.le

theorem decayTime_zero {x thr rate : ℝ} (hx : 0 < x) (hthr : 0 < thr) (hr : 0 < rate)
    (h : decayTime x thr rate = 0) : x = thr := by
  have at_ := decay_at hx hthr hr
  rw [h] at at_
  simpa using at_

theorem relax_relax (rate target x t₀ t₁ t₂ : ℝ) :
    relax rate target (relax rate target x t₀ t₁) t₁ t₂ = relax rate target x t₀ t₂ := by
  have split : Real.exp (-rate * (t₂ - t₀)) =
      Real.exp (-rate * (t₁ - t₀)) * Real.exp (-rate * (t₂ - t₁)) := by
    rw [← Real.exp_add]
    ring_nf
  unfold relax
  rw [split]
  ring

noncomputable def mainNext (θ : Fin 1 → Parameters) (s : Snapshot 1) : ℝ :=
  s.time + match s.main 0 with
    | .ready => 0
    | .fast => decayTime (s.x 0 .q) (θ 0).thresholds.fastEnd a
    | .slow => decayTime (s.x 0 .q) (θ 0).thresholds.reopen (s.x 0 .b)

/-- The date at which the main cell returns to READY. -/
noncomputable def mainReopen (θ : Fin 1 → Parameters) (s : Snapshot 1) : ℝ :=
  mainNext θ s + match s.main 0 with
    | .fast => decayTime (θ 0).thresholds.fastEnd (θ 0).thresholds.reopen (s.x 0 .b)
    | _ => 0

noncomputable def sensorNext (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) : ℝ :=
  s.time + match s.aux 0 q with
    | .silent => decayTime (s.x 0 (.m q)) ((θ 0).thresholds.error q) ((θ 0).ls q)
    | .error => decayTime (s.x 0 (.m q)) ((θ 0).thresholds.auxReady q) ((θ 0).le q)
    | _ => 0

/-- The date at which a busy sensor returns to READY. -/
noncomputable def sensorReady (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) : ℝ :=
  sensorNext θ s q + match s.aux 0 q with
    | .silent => decayTime ((θ 0).thresholds.error q) ((θ 0).thresholds.auxReady q) ((θ 0).le q)
    | _ => 0

/-- The charge of a sensor at a later date, once it is READY again. -/
noncomputable def restSensor (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) (t : ℝ) : ℝ :=
  if s.aux 0 q = .ready then relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t
  else relax (1 / 2) (1 / 40) ((θ 0).thresholds.auxReady q) (sensorReady θ s q) t

theorem mainNext_fast {θ : Fin 1 → Parameters} {s : Snapshot 1} (h : s.main 0 = .fast) :
    mainNext θ s = s.time + decayTime (s.x 0 .q) (θ 0).thresholds.fastEnd a := by
  simp [mainNext, h]

theorem mainNext_slow {θ : Fin 1 → Parameters} {s : Snapshot 1} (h : s.main 0 = .slow) :
    mainNext θ s = s.time + decayTime (s.x 0 .q) (θ 0).thresholds.reopen (s.x 0 .b) := by
  simp [mainNext, h]

theorem mainReopen_fast {θ : Fin 1 → Parameters} {s : Snapshot 1} (h : s.main 0 = .fast) :
    mainReopen θ s = mainNext θ s +
      decayTime (θ 0).thresholds.fastEnd (θ 0).thresholds.reopen (s.x 0 .b) := by
  simp [mainReopen, h]

theorem mainReopen_slow {θ : Fin 1 → Parameters} {s : Snapshot 1} (h : s.main 0 = .slow) :
    mainReopen θ s = mainNext θ s := by
  simp [mainReopen, h]

theorem sensorNext_silent {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q = .silent) : sensorNext θ s q =
      s.time + decayTime (s.x 0 (.m q)) ((θ 0).thresholds.error q) ((θ 0).ls q) := by
  simp [sensorNext, h]

theorem sensorNext_error {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q = .error) : sensorNext θ s q =
      s.time + decayTime (s.x 0 (.m q)) ((θ 0).thresholds.auxReady q) ((θ 0).le q) := by
  simp [sensorNext, h]

theorem sensorReady_silent {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q = .silent) : sensorReady θ s q = sensorNext θ s q +
      decayTime ((θ 0).thresholds.error q) ((θ 0).thresholds.auxReady q) ((θ 0).le q) := by
  simp [sensorReady, h]

theorem sensorReady_error {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q = .error) : sensorReady θ s q = sensorNext θ s q := by
  simp [sensorReady, h]

theorem restSensor_ready {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q = .ready) (t : ℝ) :
    restSensor θ s q t = relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t := by
  simp [restSensor, h]

theorem restSensor_busy {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q ≠ .ready) (t : ℝ) :
    restSensor θ s q t =
      relax (1 / 2) (1 / 40) ((θ 0).thresholds.auxReady q) (sensorReady θ s q) t := by
  simp [restSensor, h]

/-- A refractory state whose pending threshold contacts all lie ahead. -/
structure Scheduled (θ : Fin 1 → Parameters) (s : Snapshot 1) : Prop where
  refractory : Refractory s
  main_levels : 0 < (θ 0).thresholds.reopen ∧
    (θ 0).thresholds.reopen ≤ (θ 0).thresholds.fastEnd
  levels : ∀ q, 0 < (θ 0).thresholds.auxReady q ∧
    (θ 0).thresholds.auxReady q ≤ (θ 0).thresholds.error q ∧
    (θ 0).thresholds.error q < 1 ∧ 1 ≤ (θ 0).thresholds.mark q
  recovery : 0 < s.x 0 .b
  fast : s.main 0 = .fast → (θ 0).thresholds.fastEnd ≤ s.x 0 .q
  slow : s.main 0 = .slow → (θ 0).thresholds.reopen ≤ s.x 0 .q
  ready : ∀ q, s.aux 0 q = .ready → s.x 0 (.m q) < 1
  silent : ∀ q, s.aux 0 q = .silent → (θ 0).thresholds.error q ≤ s.x 0 (.m q)
  error : ∀ q, s.aux 0 q = .error → (θ 0).thresholds.auxReady q ≤ s.x 0 (.m q)
  raw : ∀ q o, s.raw 0 q = some o → o ≤ s.time ∧ s.time ≤ o + 1

/-- Every busy sensor is READY again, and every pulse has ended, before
the main cell reopens. A pulse ends before its sensor reopens. -/
structure Ordered (θ : Fin 1 → Parameters) (s : Snapshot 1) : Prop where
  sensor : ∀ q, s.aux 0 q ≠ .ready → sensorReady θ s q < mainReopen θ s
  raw : ∀ q o, s.raw 0 q = some o → o + 1 < mainReopen θ s ∧ o + 1 < sensorReady θ s q
  pending : ∀ d ∈ s.pending, mainReopen θ s ≤ d.due

/-- Two states on the same refractory timeline. -/
structure Same (θ : Fin 1 → Parameters) (s s' : Snapshot 1) : Prop where
  reopen : mainReopen θ s' = mainReopen θ s
  sensors : ∀ q t, restSensor θ s' q t = restSensor θ s q t
  gains : ∀ q, s'.x 0 (.z q) = s.x 0 (.z q)
  recovery : s'.x 0 .b = s.x 0 .b
  queue : s'.pending = s.pending

/-- The state at the reopening of the main cell. -/
structure RefractoryEnd (θ : Fin 1 → Parameters) (s u : Snapshot 1) : Prop where
  time : u.time = mainReopen θ s
  main : u.main 0 = .ready
  charge : u.x 0 .q = (θ 0).thresholds.reopen
  aux : ∀ q, u.aux 0 q = .ready
  raw : ∀ q, u.raw 0 q = none
  gains : ∀ q, u.x 0 (.z q) = s.x 0 (.z q)
  recovery : u.x 0 .b = s.x 0 .b
  queue : u.pending = s.pending
  sensors : ∀ q, u.x 0 (.m q) = restSensor θ s q (mainReopen θ s)

theorem RefractoryEnd.of_same {θ : Fin 1 → Parameters} {s s' u : Snapshot 1}
    (h : Same θ s s') (e : RefractoryEnd θ s' u) : RefractoryEnd θ s u :=
  ⟨e.time.trans h.reopen, e.main, e.charge, e.aux, e.raw, fun q => (e.gains q).trans (h.gains q),
    e.recovery.trans h.recovery, e.queue.trans h.queue,
    fun q => by rw [e.sensors q, h.reopen, h.sensors]⟩

theorem Same.trans {θ : Fin 1 → Parameters} {s s' s'' : Snapshot 1}
    (h : Same θ s s') (k : Same θ s' s'') : Same θ s s'' :=
  ⟨k.reopen.trans h.reopen, fun q t => (k.sensors q t).trans (h.sensors q t),
    fun q => (k.gains q).trans (h.gains q), k.recovery.trans h.recovery, k.queue.trans h.queue⟩

theorem Scheduled.charge_pos {θ : Fin 1 → Parameters} {s : Snapshot 1} (h : Scheduled θ s) :
    0 < s.x 0 .q := by
  rcases hm : s.main 0 with _ | _ | _
  · exact absurd hm h.refractory.main
  · exact lt_of_lt_of_le (lt_of_lt_of_le h.main_levels.1 h.main_levels.2) (h.fast hm)
  · exact lt_of_lt_of_le h.main_levels.1 (h.slow hm)

theorem Scheduled.dates {θ ε} {s : Snapshot 1} (box : @PhysicalBox 1 θ ε) (h : Scheduled θ s) :
    s.time ≤ mainNext θ s ∧ mainNext θ s ≤ mainReopen θ s ∧
      ∀ q, s.time ≤ sensorNext θ s q ∧ sensorNext θ s q ≤ sensorReady θ s q := by
  have apos : 0 < a := by linarith [a_coarse_bounds.1]
  have fpos := lt_of_lt_of_le h.main_levels.1 h.main_levels.2
  refine ⟨?_, ?_, fun q => ?_⟩
  · rcases hm : s.main 0 with _ | _ | _
    · exact absurd hm h.refractory.main
    · rw [mainNext_fast hm]
      linarith [decayTime_nonneg fpos apos (h.fast hm)]
    · rw [mainNext_slow hm]
      linarith [decayTime_nonneg h.main_levels.1 h.recovery (h.slow hm)]
  · rcases hm : s.main 0 with _ | _ | _
    · exact absurd hm h.refractory.main
    · rw [mainReopen_fast hm]
      linarith [decayTime_nonneg h.main_levels.1 h.recovery h.main_levels.2]
    · rw [mainReopen_slow hm]
  · obtain ⟨lpos, lle, _, _⟩ := h.levels q
    have rates := box.rates_positive 0 q
    rcases hm : s.aux 0 q with _ | _ | _ | _
    · simp [sensorNext, sensorReady, hm]
    · exact absurd hm (h.refractory.no_mark q)
    · rw [sensorReady_silent hm, sensorNext_silent hm]
      constructor
      · linarith [decayTime_nonneg (lt_of_lt_of_le lpos lle) rates.2.1 (h.silent q hm)]
      · linarith [decayTime_nonneg lpos rates.2.2 lle]
    · rw [sensorReady_error hm, sensorNext_error hm]
      exact ⟨by linarith [decayTime_nonneg lpos rates.2.2 (h.error q hm)], le_rfl⟩

/-! ### Advancing to the next event -/

theorem at_charge_fast {θ : Fin 1 → Parameters} {s : Snapshot 1} {τ : ℝ} (h : s.main 0 = .fast) :
    (refractoryAt θ s τ).x 0 .q = s.x 0 .q * Real.exp (-a * (τ - s.time)) := by
  simp [refractoryAt, refractoryValues, refractoryCharge, mainRate, h]

theorem at_charge_slow {θ : Fin 1 → Parameters} {s : Snapshot 1} {τ : ℝ} (h : s.main 0 = .slow) :
    (refractoryAt θ s τ).x 0 .q = s.x 0 .q * Real.exp (-s.x 0 .b * (τ - s.time)) := by
  simp [refractoryAt, refractoryValues, refractoryCharge, mainRate, h]

theorem at_sensor_ready {θ : Fin 1 → Parameters} {s : Snapshot 1} {τ : ℝ} {q : Port}
    (h : s.aux 0 q = .ready) :
    (refractoryAt θ s τ).x 0 (.m q) = relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time τ := by
  simp [refractoryAt, refractoryValues, refractorySensor, h]

theorem at_sensor_silent {θ : Fin 1 → Parameters} {s : Snapshot 1} {τ : ℝ} {q : Port}
    (h : s.aux 0 q = .silent) :
    (refractoryAt θ s τ).x 0 (.m q) = s.x 0 (.m q) * Real.exp (-(θ 0).ls q * (τ - s.time)) := by
  simp [refractoryAt, refractoryValues, refractorySensor, sensorRate, protectedReadyRate, h]

theorem at_sensor_error {θ : Fin 1 → Parameters} {s : Snapshot 1} {τ : ℝ} {q : Port}
    (h : s.aux 0 q = .error) :
    (refractoryAt θ s τ).x 0 (.m q) = s.x 0 (.m q) * Real.exp (-(θ 0).le q * (τ - s.time)) := by
  simp [refractoryAt, refractoryValues, refractorySensor, sensorRate, protectedReadyRate, h]

/-- A flow in the refractory regime keeps every event date. -/
theorem advance_same {θ ε} {s : Snapshot 1} (box : @PhysicalBox 1 θ ε) (h : Scheduled θ s) (τ : ℝ) :
    Same θ s (refractoryAt θ s τ) ∧ mainNext θ (refractoryAt θ s τ) = mainNext θ s ∧
      ∀ q, s.aux 0 q ≠ .ready →
        sensorNext θ (refractoryAt θ s τ) q = sensorNext θ s q ∧
        sensorReady θ (refractoryAt θ s τ) q = sensorReady θ s q := by
  have apos : 0 < a := by linarith [a_coarse_bounds.1]
  have fpos := lt_of_lt_of_le h.main_levels.1 h.main_levels.2
  have hb : (refractoryAt θ s τ).x 0 .b = s.x 0 .b := rfl
  have ht : (refractoryAt θ s τ).time = τ := rfl
  have mainEq : mainNext θ (refractoryAt θ s τ) = mainNext θ s := by
    rcases hm : s.main 0 with _ | _ | _
    · exact absurd hm h.refractory.main
    · rw [mainNext_fast (s := refractoryAt θ s τ) hm, mainNext_fast hm, at_charge_fast hm,
        decayTime_shift h.charge_pos fpos apos, ht]
      ring
    · rw [mainNext_slow (s := refractoryAt θ s τ) hm, mainNext_slow hm, at_charge_slow hm, hb,
        decayTime_shift h.charge_pos h.main_levels.1 h.recovery, ht]
      ring
  have reopenEq : mainReopen θ (refractoryAt θ s τ) = mainReopen θ s := by
    rcases hm : s.main 0 with _ | _ | _
    · exact absurd hm h.refractory.main
    · rw [mainReopen_fast (s := refractoryAt θ s τ) hm, mainReopen_fast hm, mainEq, hb]
    · rw [mainReopen_slow (s := refractoryAt θ s τ) hm, mainReopen_slow hm, mainEq]
  have sensorEq (q : Port) (busy : s.aux 0 q ≠ .ready) :
      sensorNext θ (refractoryAt θ s τ) q = sensorNext θ s q ∧
        sensorReady θ (refractoryAt θ s τ) q = sensorReady θ s q := by
    obtain ⟨lpos, lle, _, _⟩ := h.levels q
    have rates := box.rates_positive 0 q
    rcases hm : s.aux 0 q with _ | _ | _ | _
    · exact absurd hm busy
    · exact absurd hm (h.refractory.no_mark q)
    · have next : sensorNext θ (refractoryAt θ s τ) q = sensorNext θ s q := by
        rw [sensorNext_silent (s := refractoryAt θ s τ) hm, sensorNext_silent hm,
          at_sensor_silent hm, decayTime_shift
            (lt_of_lt_of_le (lt_of_lt_of_le lpos lle) (h.silent q hm))
            (lt_of_lt_of_le lpos lle) rates.2.1, ht]
        ring
      exact ⟨next, by rw [sensorReady_silent (s := refractoryAt θ s τ) hm, sensorReady_silent hm, next]⟩
    · have next : sensorNext θ (refractoryAt θ s τ) q = sensorNext θ s q := by
        rw [sensorNext_error (s := refractoryAt θ s τ) hm, sensorNext_error hm,
          at_sensor_error hm, decayTime_shift (lt_of_lt_of_le lpos (h.error q hm)) lpos rates.2.2, ht]
        ring
      exact ⟨next, by rw [sensorReady_error (s := refractoryAt θ s τ) hm, sensorReady_error hm, next]⟩
  refine ⟨⟨reopenEq, ?_, fun _ => rfl, rfl, rfl⟩, mainEq, sensorEq⟩
  intro q t
  by_cases hr : s.aux 0 q = .ready
  · rw [restSensor_ready (s := refractoryAt θ s τ) hr, restSensor_ready hr, at_sensor_ready hr, ht,
      relax_relax]
  · rw [restSensor_busy (s := refractoryAt θ s τ) hr, restSensor_busy hr, (sensorEq q hr).2]

/-- The cell flows up to any date that precedes all its pending events. -/
theorem advance {θ ε} {s : Snapshot 1} {τ : ℝ} (box : @PhysicalBox 1 θ ε)
    (sched : Scheduled θ s) (ord : Ordered θ s) (lt : s.time < τ)
    (main : τ ≤ mainNext θ s)
    (sensor : ∀ q, s.aux 0 q ≠ .ready → τ ≤ sensorNext θ s q)
    (raw : ∀ q o, s.raw 0 q = some o → τ ≤ o + 1) :
    Nonempty (ParameterFlow θ s (refractoryAt θ s τ)) ∧ Scheduled θ (refractoryAt θ s τ) ∧
      Ordered θ (refractoryAt θ s τ) := by
  have apos : 0 < a := by linarith [a_coarse_bounds.1]
  have fpos := lt_of_lt_of_le sched.main_levels.1 sched.main_levels.2
  have dates := sched.dates box
  have chargePos := sched.charge_pos
  have mainFast (hm : s.main 0 = .fast) :
      τ - s.time ≤ decayTime (s.x 0 .q) (θ 0).thresholds.fastEnd a := by
    rw [mainNext_fast hm] at main
    linarith
  have mainSlow (hm : s.main 0 = .slow) :
      τ - s.time ≤ decayTime (s.x 0 .q) (θ 0).thresholds.reopen (s.x 0 .b) := by
    rw [mainNext_slow hm] at main
    linarith
  have sensorSilent (q : Port) (hm : s.aux 0 q = .silent) :
      τ - s.time ≤ decayTime (s.x 0 (.m q)) ((θ 0).thresholds.error q) ((θ 0).ls q) := by
    have h := sensor q (by rw [hm]; decide)
    rw [sensorNext_silent hm] at h
    linarith
  have sensorError (q : Port) (hm : s.aux 0 q = .error) :
      τ - s.time ≤ decayTime (s.x 0 (.m q)) ((θ 0).thresholds.auxReady q) ((θ 0).le q) := by
    have h := sensor q (by rw [hm]; decide)
    rw [sensorNext_error hm] at h
    linarith
  have silentPos (q : Port) (hm : s.aux 0 q = .silent) : 0 < s.x 0 (.m q) :=
    lt_of_lt_of_le (lt_of_lt_of_le (sched.levels q).1 (sched.levels q).2.1) (sched.silent q hm)
  have errorPos (q : Port) (hm : s.aux 0 q = .error) : 0 < s.x 0 (.m q) :=
    lt_of_lt_of_le (sched.levels q).1 (sched.error q hm)
  have flow : ParameterFlow θ s (refractoryAt θ s τ) := {
    toFlowDynamics := refractoryDynamics s lt sched.refractory
      (fun q o h => ⟨(sched.raw q o h).1, raw q o h⟩)
      (fun d hd => le_trans (main.trans dates.2.1) (ord.pending d hd))
    guards := by
      intro t ht
      have ht₁ : s.time ≤ t := ht.1
      have ht₂ : t < τ := ht.2
      constructor
      · intro i
        rw [Subsingleton.elim i 0]
        rcases hm : s.main 0 with _ | _ | _
        · exact absurd hm sched.refractory.main
        · show (θ 0).thresholds.fastEnd < (refractoryAt θ s t).x 0 .q
          rw [at_charge_fast hm]
          exact decay_above chargePos fpos apos (by linarith [mainFast hm])
        · show (θ 0).thresholds.reopen < (refractoryAt θ s t).x 0 .q
          rw [at_charge_slow hm]
          exact decay_above chargePos sched.main_levels.1 sched.recovery (by linarith [mainSlow hm])
      · intro i q
        rw [Subsingleton.elim i 0]
        have rates := box.rates_positive 0 q
        obtain ⟨lpos, lle, _, mark⟩ := sched.levels q
        rcases hm : s.aux 0 q with _ | _ | _ | _
        · show (refractoryAt θ s t).x 0 (.m q) < (θ 0).thresholds.mark q
          rw [at_sensor_ready hm]
          exact lt_of_lt_of_le (relax_lt_one ht₁ (sched.ready q hm)) mark
        · exact absurd hm (sched.refractory.no_mark q)
        · show (θ 0).thresholds.error q < (refractoryAt θ s t).x 0 (.m q)
          rw [at_sensor_silent hm]
          exact decay_above (silentPos q hm) (lt_of_lt_of_le lpos lle) rates.2.1
            (by linarith [sensorSilent q hm])
        · show (θ 0).thresholds.auxReady q < (refractoryAt θ s t).x 0 (.m q)
          rw [at_sensor_error hm]
          exact decay_above (errorPos q hm) lpos rates.2.2 (by linarith [sensorError q hm])
  }
  obtain ⟨same, _, sensorEq⟩ := advance_same box sched τ
  refine ⟨⟨flow⟩, ?_, ?_⟩
  · exact {
      refractory := ⟨sched.refractory.main, sched.refractory.no_mark, sched.refractory.ready_raw⟩
      main_levels := sched.main_levels
      levels := sched.levels
      recovery := sched.recovery
      fast := fun hm => by
        rw [at_charge_fast (s := s) hm]
        exact decay_ge chargePos fpos apos (mainFast hm)
      slow := fun hm => by
        rw [at_charge_slow (s := s) hm]
        exact decay_ge chargePos sched.main_levels.1 sched.recovery (mainSlow hm)
      ready := fun q hm => by
        rw [at_sensor_ready (s := s) hm]
        exact relax_lt_one lt.le (sched.ready q hm)
      silent := fun q hm => by
        rw [at_sensor_silent (s := s) hm]
        exact decay_ge (silentPos q hm)
          (lt_of_lt_of_le (sched.levels q).1 (sched.levels q).2.1)
          (box.rates_positive 0 q).2.1 (sensorSilent q hm)
      error := fun q hm => by
        rw [at_sensor_error (s := s) hm]
        exact decay_ge (errorPos q hm) (sched.levels q).1 (box.rates_positive 0 q).2.2
          (sensorError q hm)
      raw := fun q o h => ⟨(sched.raw q o h).1.trans lt.le, raw q o h⟩ }
  · exact {
      sensor := fun q hq => by
        rw [(sensorEq q hq).2, same.reopen]
        exact ord.sensor q hq
      raw := fun q o h => by
        have h' : s.raw 0 q = some o := h
        have busy : s.aux 0 q ≠ .ready := fun hr => by
          rw [sched.refractory.ready_raw q hr] at h'
          cases h'
        rw [(sensorEq q busy).2, same.reopen]
        exact ord.raw q o h'
      pending := fun d hd => by
        rw [same.reopen]
        exact ord.pending d hd }

/-! ### The pending events, one at a time -/

def mainCount : MainMode → ℕ
  | .fast => 2
  | .slow => 1
  | .ready => 0

def auxCount : AuxMode → ℕ
  | .silent => 2
  | .error => 1
  | _ => 0

def rawCount : Option ℝ → ℕ
  | some _ => 1
  | none => 0

/-- The number of mode changes and pulse ends still ahead. -/
def remaining (s : Snapshot 1) : ℕ :=
  mainCount (s.main 0) + ∑ q : Port, auxCount (s.aux 0 q) + ∑ q : Port, rawCount (s.raw 0 q)

theorem setAux_same (s : Snapshot 1) (q : Port) (mode : AuxMode) :
    (setAux s 0 q mode).aux 0 q = mode := by
  simp [setAux]

theorem setAux_other (s : Snapshot 1) {q q' : Port} (mode : AuxMode) (h : q' ≠ q) :
    (setAux s 0 q mode).aux 0 q' = s.aux 0 q' := by
  simp [setAux, h]

theorem sensorReady_congr {θ : Fin 1 → Parameters} {s s' : Snapshot 1} {q : Port}
    (hx : s'.x = s.x) (ht : s'.time = s.time) (ha : s'.aux 0 q = s.aux 0 q) :
    sensorReady θ s' q = sensorReady θ s q := by
  unfold sensorReady sensorNext
  rw [hx, ht, ha]

theorem restSensor_congr {θ : Fin 1 → Parameters} {s s' : Snapshot 1} {q : Port}
    (hx : s'.x = s.x) (ht : s'.time = s.time) (ha : s'.aux 0 q = s.aux 0 q) (t : ℝ) :
    restSensor θ s' q t = restSensor θ s q t := by
  unfold restSensor sensorReady sensorNext
  rw [hx, ht, ha]

theorem jump_fast_end {θ : Fin 1 → Parameters} {s : Snapshot 1}
    (sched : Scheduled θ s) (ord : Ordered θ s) (hm : s.main 0 = .fast)
    (due : mainNext θ s = s.time) :
    Runs θ s (setMain s 0 .slow) 0 ∧
      Scheduled θ (setMain s 0 .slow) ∧ Ordered θ (setMain s 0 .slow) ∧
      remaining (setMain s 0 .slow) < remaining s ∧ Same θ s (setMain s 0 .slow) := by
  have apos : 0 < a := by linarith [a_coarse_bounds.1]
  have fpos := lt_of_lt_of_le sched.main_levels.1 sched.main_levels.2
  have zero : decayTime (s.x 0 .q) (θ 0).thresholds.fastEnd a = 0 := by
    rw [mainNext_fast hm] at due
    linarith
  have contact : s.x 0 .q = (θ 0).thresholds.fastEnd :=
    decayTime_zero sched.charge_pos fpos apos zero
  have hs' : (setMain s 0 .slow).main 0 = .slow := by simp [setMain]
  have reopenEq : mainReopen θ (setMain s 0 .slow) = mainReopen θ s := by
    rw [mainReopen_slow hs', mainNext_slow hs', mainReopen_fast hm, due]
    show s.time + decayTime (s.x 0 .q) _ (s.x 0 .b) = _
    rw [contact]
  refine ⟨Runs.jump (.fastEnd s 0 hm contact) rfl, ?_, ?_, ?_, ⟨reopenEq, fun _ _ => rfl, fun _ => rfl, rfl, rfl⟩⟩
  · exact {
      refractory := ⟨by rw [hs']; decide, sched.refractory.no_mark, sched.refractory.ready_raw⟩
      main_levels := sched.main_levels
      levels := sched.levels
      recovery := sched.recovery
      fast := fun h => by rw [hs'] at h; cases h
      slow := fun _ => by
        show _ ≤ s.x 0 .q
        rw [contact]
        exact sched.main_levels.2
      ready := sched.ready
      silent := sched.silent
      error := sched.error
      raw := sched.raw }
  · exact {
      sensor := fun q hq => by rw [reopenEq]; exact ord.sensor q hq
      raw := fun q o h => by rw [reopenEq]; exact ord.raw q o h
      pending := fun d hd => by rw [reopenEq]; exact ord.pending d hd }
  · show mainCount ((setMain s 0 .slow).main 0) + ∑ q : Port, auxCount (s.aux 0 q) +
        ∑ q : Port, rawCount (s.raw 0 q) <
      mainCount (s.main 0) + ∑ q : Port, auxCount (s.aux 0 q) + ∑ q : Port, rawCount (s.raw 0 q)
    rw [hs', hm]
    simp only [mainCount]
    omega

theorem jump_reopen {θ ε} {s : Snapshot 1} (box : @PhysicalBox 1 θ ε)
    (sched : Scheduled θ s) (ord : Ordered θ s) (hm : s.main 0 = .slow)
    (due : mainNext θ s = s.time) :
    ∃ u, Runs θ s u 0 ∧ RefractoryEnd θ s u := by
  have zero : decayTime (s.x 0 .q) (θ 0).thresholds.reopen (s.x 0 .b) = 0 := by
    rw [mainNext_slow hm] at due
    linarith
  have contact : s.x 0 .q = (θ 0).thresholds.reopen :=
    decayTime_zero sched.charge_pos sched.main_levels.1 sched.recovery zero
  have reopenNow : mainReopen θ s = s.time := by rw [mainReopen_slow hm, due]
  have dates := sched.dates box
  have allReady (q : Port) : s.aux 0 q = .ready := by
    by_contra h
    have lt := ord.sensor q h
    rw [reopenNow] at lt
    linarith [(dates.2.2 q).1, (dates.2.2 q).2]
  have noRaw (q : Port) : s.raw 0 q = none := by
    rcases h : s.raw 0 q with _ | o
    · rfl
    · exfalso
      have lt := (ord.raw q o h).1
      rw [reopenNow] at lt
      linarith [(sched.raw q o h).2]
  refine ⟨setMain s 0 .ready, Runs.jump (.reopen s 0 hm contact) rfl,
    ⟨reopenNow.symm, by simp [setMain], contact, allReady, noRaw, fun _ => rfl, rfl, rfl,
      fun q => ?_⟩⟩
  show s.x 0 (.m q) = _
  rw [restSensor_ready (allReady q), reopenNow, relax_initial]

theorem jump_error {θ ε} {s : Snapshot 1} {q : Port} (box : @PhysicalBox 1 θ ε)
    (sched : Scheduled θ s) (ord : Ordered θ s) (hm : s.aux 0 q = .silent)
    (due : sensorNext θ s q = s.time) :
    Runs θ s (setAux s 0 q .error) 0 ∧
      Scheduled θ (setAux s 0 q .error) ∧ Ordered θ (setAux s 0 q .error) ∧
      remaining (setAux s 0 q .error) < remaining s ∧ Same θ s (setAux s 0 q .error) := by
  obtain ⟨lpos, lle, llt, mark⟩ := sched.levels q
  have rates := box.rates_positive 0 q
  have zero : decayTime (s.x 0 (.m q)) ((θ 0).thresholds.error q) ((θ 0).ls q) = 0 := by
    rw [sensorNext_silent hm] at due
    linarith
  have contact : s.x 0 (.m q) = (θ 0).thresholds.error q :=
    decayTime_zero (lt_of_lt_of_le (lt_of_lt_of_le lpos lle) (sched.silent q hm))
      (lt_of_lt_of_le lpos lle) rates.2.1 zero
  have hs' := setAux_same s q .error
  have other (q' : Port) (h : q' ≠ q) := setAux_other s .error h
  have readyEq : sensorReady θ (setAux s 0 q .error) q = sensorReady θ s q := by
    rw [sensorReady_error hs', sensorNext_error hs', sensorReady_silent hm, due]
    show s.time + decayTime (s.x 0 (.m q)) _ _ = _
    rw [contact]
  have readyOther (q' : Port) (h : q' ≠ q) :
      sensorReady θ (setAux s 0 q .error) q' = sensorReady θ s q' :=
    sensorReady_congr rfl rfl (other q' h)
  refine ⟨Runs.jump (.error s 0 q hm contact) rfl, ?_, ?_, ?_, ⟨rfl, ?_, fun _ => rfl, rfl, rfl⟩⟩
  · exact {
      refractory := ⟨sched.refractory.main,
        fun q' => by
          by_cases h : q' = q
          · subst q'; rw [hs']; decide
          · rw [other q' h]; exact sched.refractory.no_mark q',
        fun q' hr => by
          by_cases h : q' = q
          · subst q'; rw [hs'] at hr; cases hr
          · rw [other q' h] at hr; exact sched.refractory.ready_raw q' hr⟩
      main_levels := sched.main_levels
      levels := sched.levels
      recovery := sched.recovery
      fast := sched.fast
      slow := sched.slow
      ready := fun q' hr => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at hr; cases hr
        · rw [other q' h] at hr; exact sched.ready q' hr
      silent := fun q' hr => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at hr; cases hr
        · rw [other q' h] at hr; exact sched.silent q' hr
      error := fun q' hr => by
        by_cases h : q' = q
        · subst q'
          show _ ≤ s.x 0 (.m q)
          rw [contact]
          exact lle
        · rw [other q' h] at hr; exact sched.error q' hr
      raw := sched.raw }
  · exact {
      sensor := fun q' hq' => by
        by_cases h : q' = q
        · subst q'
          rw [readyEq]
          exact ord.sensor q (by rw [hm]; decide)
        · rw [readyOther q' h]
          exact ord.sensor q' (by rw [← other q' h]; exact hq')
      raw := fun q' o h' => by
        by_cases h : q' = q
        · subst q'
          rw [readyEq]
          exact ord.raw q o h'
        · rw [readyOther q' h]
          exact ord.raw q' o h'
      pending := ord.pending }
  · have le : ∀ q' ∈ (Finset.univ : Finset Port),
        auxCount ((setAux s 0 q .error).aux 0 q') ≤ auxCount (s.aux 0 q') := by
      intro q' _
      by_cases h : q' = q
      · subst q'; rw [hs', hm]; decide
      · rw [other q' h]
    have lt := Finset.sum_lt_sum le ⟨q, Finset.mem_univ q, by rw [hs', hm]; decide⟩
    show mainCount (s.main 0) + ∑ q' : Port, auxCount ((setAux s 0 q .error).aux 0 q') +
        ∑ q' : Port, rawCount (s.raw 0 q') <
      mainCount (s.main 0) + ∑ q' : Port, auxCount (s.aux 0 q') + ∑ q' : Port, rawCount (s.raw 0 q')
    omega
  · intro q' t
    by_cases h : q' = q
    · subst q'
      rw [restSensor_busy (by rw [hs']; decide), restSensor_busy (by rw [hm]; decide), readyEq]
    · exact restSensor_congr (s := s) (s' := setAux s 0 q .error) rfl rfl (other q' h) t

theorem jump_ready {θ ε} {s : Snapshot 1} {q : Port} (box : @PhysicalBox 1 θ ε)
    (sched : Scheduled θ s) (ord : Ordered θ s) (hm : s.aux 0 q = .error)
    (due : sensorNext θ s q = s.time) :
    Runs θ s (setAux s 0 q .ready) 0 ∧
      Scheduled θ (setAux s 0 q .ready) ∧ Ordered θ (setAux s 0 q .ready) ∧
      remaining (setAux s 0 q .ready) < remaining s ∧ Same θ s (setAux s 0 q .ready) := by
  obtain ⟨lpos, lle, llt, mark⟩ := sched.levels q
  have rates := box.rates_positive 0 q
  have zero : decayTime (s.x 0 (.m q)) ((θ 0).thresholds.auxReady q) ((θ 0).le q) = 0 := by
    rw [sensorNext_error hm] at due
    linarith
  have contact : s.x 0 (.m q) = (θ 0).thresholds.auxReady q :=
    decayTime_zero (lt_of_lt_of_le lpos (sched.error q hm)) lpos rates.2.2 zero
  have rawNone : s.raw 0 q = none := by
    rcases h : s.raw 0 q with _ | o
    · rfl
    · exfalso
      have lt := (ord.raw q o h).2
      rw [sensorReady_error hm, due] at lt
      linarith [(sched.raw q o h).2]
  have hs' := setAux_same s q .ready
  have other (q' : Port) (h : q' ≠ q) := setAux_other s .ready h
  have readyOther (q' : Port) (h : q' ≠ q) :
      sensorReady θ (setAux s 0 q .ready) q' = sensorReady θ s q' :=
    sensorReady_congr rfl rfl (other q' h)
  refine ⟨Runs.jump (.auxReady s 0 q hm contact) rfl, ?_, ?_, ?_, ⟨rfl, ?_, fun _ => rfl, rfl, rfl⟩⟩
  · exact {
      refractory := ⟨sched.refractory.main,
        fun q' => by
          by_cases h : q' = q
          · subst q'; rw [hs']; decide
          · rw [other q' h]; exact sched.refractory.no_mark q',
        fun q' hr => by
          by_cases h : q' = q
          · subst q'; exact rawNone
          · rw [other q' h] at hr; exact sched.refractory.ready_raw q' hr⟩
      main_levels := sched.main_levels
      levels := sched.levels
      recovery := sched.recovery
      fast := sched.fast
      slow := sched.slow
      ready := fun q' hr => by
        by_cases h : q' = q
        · subst q'
          show s.x 0 (.m q) < 1
          rw [contact]
          linarith
        · rw [other q' h] at hr; exact sched.ready q' hr
      silent := fun q' hr => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at hr; cases hr
        · rw [other q' h] at hr; exact sched.silent q' hr
      error := fun q' hr => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at hr; cases hr
        · rw [other q' h] at hr; exact sched.error q' hr
      raw := sched.raw }
  · exact {
      sensor := fun q' hq' => by
        by_cases h : q' = q
        · subst q'; exact absurd hs' hq'
        · rw [readyOther q' h]
          exact ord.sensor q' (by rw [← other q' h]; exact hq')
      raw := fun q' o h' => by
        by_cases h : q' = q
        · subst q'
          have h'' : s.raw 0 q = some o := h'
          rw [rawNone] at h''
          cases h''
        · rw [readyOther q' h]
          exact ord.raw q' o h'
      pending := ord.pending }
  · have le : ∀ q' ∈ (Finset.univ : Finset Port),
        auxCount ((setAux s 0 q .ready).aux 0 q') ≤ auxCount (s.aux 0 q') := by
      intro q' _
      by_cases h : q' = q
      · subst q'; rw [hs', hm]; decide
      · rw [other q' h]
    have lt := Finset.sum_lt_sum le ⟨q, Finset.mem_univ q, by rw [hs', hm]; decide⟩
    show mainCount (s.main 0) + ∑ q' : Port, auxCount ((setAux s 0 q .ready).aux 0 q') +
        ∑ q' : Port, rawCount (s.raw 0 q') <
      mainCount (s.main 0) + ∑ q' : Port, auxCount (s.aux 0 q') + ∑ q' : Port, rawCount (s.raw 0 q')
    omega
  · intro q' t
    by_cases h : q' = q
    · subst q'
      rw [restSensor_ready hs', restSensor_busy (by rw [hm]; decide), sensorReady_error hm, due]
      show relax _ _ (s.x 0 (.m q)) s.time t = _
      rw [contact]
    · exact restSensor_congr (s := s) (s' := setAux s 0 q .ready) rfl rfl (other q' h) t

theorem jump_raw_end {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port} {o : ℝ}
    (sched : Scheduled θ s) (ord : Ordered θ s) (active : s.raw 0 q = some o)
    (due : o + 1 = s.time) :
    Runs θ s (setRaw s 0 q none) 0 ∧
      Scheduled θ (setRaw s 0 q none) ∧ Ordered θ (setRaw s 0 q none) ∧
      remaining (setRaw s 0 q none) < remaining s ∧ Same θ s (setRaw s 0 q none) := by
  have hs' : (setRaw s 0 q none).raw 0 q = none := by simp [setRaw]
  have other (q' : Port) (h : q' ≠ q) : (setRaw s 0 q none).raw 0 q' = s.raw 0 q' :=
    raw_update_other s 0 q none 0 q' (Or.inr h)
  refine ⟨Runs.jump (.rawEnd s 0 q o active due.symm) rfl, ?_, ?_, ?_, ⟨rfl, fun _ _ => rfl, fun _ => rfl, rfl, rfl⟩⟩
  · exact {
      refractory := ⟨sched.refractory.main, sched.refractory.no_mark,
        fun q' hr => by
          by_cases h : q' = q
          · subst q'; exact hs'
          · rw [other q' h]; exact sched.refractory.ready_raw q' hr⟩
      main_levels := sched.main_levels
      levels := sched.levels
      recovery := sched.recovery
      fast := sched.fast
      slow := sched.slow
      ready := sched.ready
      silent := sched.silent
      error := sched.error
      raw := fun q' o' h' => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at h'; cases h'
        · rw [other q' h] at h'; exact sched.raw q' o' h' }
  · exact {
      sensor := ord.sensor
      raw := fun q' o' h' => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at h'; cases h'
        · rw [other q' h] at h'; exact ord.raw q' o' h'
      pending := ord.pending }
  · have le : ∀ q' ∈ (Finset.univ : Finset Port),
        rawCount ((setRaw s 0 q none).raw 0 q') ≤ rawCount (s.raw 0 q') := by
      intro q' _
      by_cases h : q' = q
      · subst q'; rw [hs', active]; simp [rawCount]
      · rw [other q' h]
    have lt := Finset.sum_lt_sum le ⟨q, Finset.mem_univ q, by rw [hs', active]; simp [rawCount]⟩
    show mainCount (s.main 0) + ∑ q' : Port, auxCount (s.aux 0 q') +
        ∑ q' : Port, rawCount ((setRaw s 0 q none).raw 0 q') <
      mainCount (s.main 0) + ∑ q' : Port, auxCount (s.aux 0 q') + ∑ q' : Port, rawCount (s.raw 0 q')
    omega

/-- The earliest pending event of a refractory state. -/
theorem next_event {θ ε} {s : Snapshot 1} (box : @PhysicalBox 1 θ ε) (sched : Scheduled θ s) :
    ∃ τ, s.time ≤ τ ∧ τ ≤ mainNext θ s ∧
      (∀ q, s.aux 0 q ≠ .ready → τ ≤ sensorNext θ s q) ∧
      (∀ q o, s.raw 0 q = some o → τ ≤ o + 1) ∧
      (τ = mainNext θ s ∨ (∃ q, s.aux 0 q ≠ .ready ∧ τ = sensorNext θ s q) ∨
        ∃ q o, s.raw 0 q = some o ∧ τ = o + 1) := by
  have dates := sched.dates box
  let date : Unit ⊕ Port ⊕ Port → ℝ := fun e => match e with
    | .inl _ => mainNext θ s
    | .inr (.inl q) => if s.aux 0 q = .ready then mainNext θ s else sensorNext θ s q
    | .inr (.inr q) => match s.raw 0 q with
      | some o => o + 1
      | none => mainNext θ s
  obtain ⟨e, -, least⟩ := Finset.exists_min_image Finset.univ date ⟨.inl (), Finset.mem_univ _⟩
  have main : date e ≤ mainNext θ s := least (.inl ()) (Finset.mem_univ _)
  have sensor (q : Port) (busy : s.aux 0 q ≠ .ready) : date e ≤ sensorNext θ s q := by
    have h := least (.inr (.inl q)) (Finset.mem_univ _)
    simpa [date, busy] using h
  have raw (q : Port) (o : ℝ) (active : s.raw 0 q = some o) : date e ≤ o + 1 := by
    have h := least (.inr (.inr q)) (Finset.mem_univ _)
    simpa [date, active] using h
  refine ⟨date e, ?_, main, sensor, raw, ?_⟩
  · rcases e with _ | q | q
    · exact dates.1
    · by_cases busy : s.aux 0 q = .ready
      · simpa [date, busy] using dates.1
      · simpa [date, busy] using (dates.2.2 q).1
    · rcases active : s.raw 0 q with _ | o
      · simpa [date, active] using dates.1
      · simpa [date, active] using (sched.raw q o active).2
  · rcases e with _ | q | q
    · exact Or.inl rfl
    · by_cases busy : s.aux 0 q = .ready
      · exact Or.inl (by simp [date, busy])
      · exact Or.inr (Or.inl ⟨q, busy, by simp [date, busy]⟩)
    · rcases active : s.raw 0 q with _ | o
      · exact Or.inl (by simp [date, active])
      · exact Or.inr (Or.inr ⟨q, o, active, by simp [date, active]⟩)

/-- The refractory period as an execution. From a state after a FIRE,
with any number of busy sensors and live pulses, the cell runs to the
reopening of its main charge. Events are taken in their time order,
whatever that order is. No gain and no recovery rate changes, and each
sensor ends on its own explicit relaxation. -/
theorem refractory_run_exists {θ ε} (box : @PhysicalBox 1 θ ε) (s : Snapshot 1)
    (sched : Scheduled θ s) (ord : Ordered θ s) :
    ∃ u, Runs θ s u 0 ∧ RefractoryEnd θ s u := by
  generalize hn : remaining s = n
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    obtain ⟨τ, after, main, sensor, raw, which⟩ := next_event box sched
    obtain ⟨s₁, pre, sched₁, ord₁, count₁, same₁, due⟩ :
        ∃ s₁, Runs θ s s₁ 0 ∧ Scheduled θ s₁ ∧
          Ordered θ s₁ ∧ remaining s₁ = remaining s ∧ Same θ s s₁ ∧
          (mainNext θ s₁ = s₁.time ∨ (∃ q, s₁.aux 0 q ≠ .ready ∧ sensorNext θ s₁ q = s₁.time) ∨
            ∃ q o, s₁.raw 0 q = some o ∧ o + 1 = s₁.time) := by
      rcases after.eq_or_lt with now | later
      · refine ⟨s, Runs.nil s, sched, ord, rfl, ⟨rfl, fun _ _ => rfl, fun _ => rfl, rfl, rfl⟩, ?_⟩
        rw [now]
        rcases which with h | ⟨q, hq, h⟩ | ⟨q, o, hr, h⟩
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl ⟨q, hq, h.symm⟩)
        · exact Or.inr (Or.inr ⟨q, o, hr, h.symm⟩)
      · obtain ⟨⟨flow⟩, sched₁, ord₁⟩ := advance box sched ord later main sensor raw
        obtain ⟨same, mainEq, sensorEq⟩ := advance_same box sched τ
        refine ⟨refractoryAt θ s τ, Runs.flow flow, sched₁, ord₁, rfl, same, ?_⟩
        rcases which with h | ⟨q, hq, h⟩ | ⟨q, o, hr, h⟩
        · exact Or.inl (mainEq.trans h.symm)
        · exact Or.inr (Or.inl ⟨q, hq, (sensorEq q hq).1.trans h.symm⟩)
        · exact Or.inr (Or.inr ⟨q, o, hr, h.symm⟩)
    have step : (∃ u, Runs θ s₁ u 0 ∧ RefractoryEnd θ s₁ u) ∨
        ∃ s₂, Runs θ s₁ s₂ 0 ∧ Scheduled θ s₂ ∧ Ordered θ s₂ ∧
          remaining s₂ < remaining s₁ ∧ Same θ s₁ s₂ := by
      rcases due with h | ⟨q, hq, h⟩ | ⟨q, o, hr, h⟩
      · rcases hm : s₁.main 0 with _ | _ | _
        · exact absurd hm sched₁.refractory.main
        · exact Or.inr ⟨_, jump_fast_end sched₁ ord₁ hm h⟩
        · exact Or.inl (jump_reopen box sched₁ ord₁ hm h)
      · rcases hm : s₁.aux 0 q with _ | _ | _ | _
        · exact absurd hm hq
        · exact absurd hm (sched₁.refractory.no_mark q)
        · exact Or.inr ⟨_, jump_error box sched₁ ord₁ hm h⟩
        · exact Or.inr ⟨_, jump_ready box sched₁ ord₁ hm h⟩
      · exact Or.inr ⟨_, jump_raw_end sched₁ ord₁ hr h⟩
    rcases step with ⟨u, run, done⟩ | ⟨s₂, jump, sched₂, ord₂, less, same₂⟩
    · exact ⟨u, pre.append run, done.of_same same₁⟩
    · obtain ⟨u, run, done⟩ := ih (remaining s₂) (by omega) s₂ sched₂ ord₂ rfl
      exact ⟨u, pre.append (jump.append run), (done.of_same same₂).of_same same₁⟩

end RecursiveLearning.Native
