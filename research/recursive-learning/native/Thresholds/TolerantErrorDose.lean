import Thresholds.ThresholdTolerance

/-! The original integral field gives a rate-independent dose at arbitrary
realized ERROR endpoints. Dose accumulation supplies the gain contract
for a separately prepared read of the same port. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid MeasureTheory Set

/-- A mode-fixed exposed ERROR segment. The upper and lower charges are
the realized sensor endpoints, with the original R field on the whole
segment. The open-gate hypotheses account for cap and energy clipping. -/
structure ExposedErrorSpan (θ : Fin 1 → Parameters) (p : Port)
    (before after upper lower : ℝ) where
  start : Snapshot 1
  stop : ℝ
  path : ℝ → Values 1
  positive : start.time < stop
  ready : start.main 0 = .ready
  error : start.aux 0 p = .error
  gates : ∀ t ∈ Icc start.time stop,
    0 < path t 0 .energy ∧ path t 0 (.z p) < Real.log ((θ 0).cap p)
  initial : path start.time = start.x
  continuous : ∀ i c, ContinuousOn (fun t => path t i c) (Icc start.time stop)
  integrable : ∀ i c, IntervalIntegrable (fun t => field θ start (path t) t i c)
    volume start.time stop
  sensor_guard : ∀ t ∈ Ico start.time stop, lower < path t 0 (.m p)
  charge_in : start.x 0 (.m p) = upper
  charge_out : path stop 0 (.m p) = lower
  gain_in : start.x 0 (.z p) = before
  gain_out : path stop 0 (.z p) = after
  integral_eq : ∀ t ∈ Icc start.time stop, ∀ i c,
    path t i c = start.x i c + ∫ v in start.time..t, field θ start (path v) v i c

/-- The decay rate cancels for all realized threshold endpoints. -/
theorem ExposedErrorSpan.dose {θ p before after upper lower}
    (span : ExposedErrorSpan θ p before after upper lower) :
    after - before = 8 * (upper - lower) := by
  have last : span.stop ∈ Icc span.start.time span.stop := ⟨span.positive.le, le_rfl⟩
  have charge := span.integral_eq span.stop last 0 (.m p)
  have gain := span.integral_eq span.stop last 0 (.z p)
  rw [span.charge_in, span.charge_out] at charge
  rw [span.gain_in, span.gain_out] at gain
  have balance :
      (∫ t in span.start.time..span.stop, field θ span.start (span.path t) t 0 (.z p)) =
        -8 * (∫ t in span.start.time..span.stop, field θ span.start (span.path t) t 0 (.m p)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le span.positive.le] at ht
    have gates := span.gates t ht
    simp [field, errorAct, span.error, span.ready, gates.1, gates.2, auxDrain]
    ring
  linarith

/-- Sensor endpoint errors contribute additively to a bound on the
absolute error in the nominal dose of 0.6. -/
theorem ExposedErrorSpan.dose_error {θ p before after upper lower δhi δlo}
    (span : ExposedErrorSpan θ p before after upper lower)
    (hi : |upper - 1 / 10| ≤ δhi) (lo : |lower - 1 / 40| ≤ δlo) :
    |after - before - 3 / 5| ≤ 8 * (δhi + δlo) := by
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp hi
  obtain ⟨lo₁, lo₂⟩ := abs_le.mp lo
  exact abs_le.mpr ⟨by linarith [span.dose], by linarith [span.dose]⟩

/-- An ordered collection of exposed segments with a common port and
matching end and start log-gains. Intervening states are not recorded
by this contract. -/
inductive ExposedErrorTrain (θ : Fin 1 → Parameters) (p : Port) :
    ℝ → List (ℝ × ℝ) → ℝ → Prop
  | nil (gain : ℝ) : ExposedErrorTrain θ p gain [] gain
  | cons {before next after upper lower : ℝ} {tail : List (ℝ × ℝ)}
      (span : ExposedErrorSpan θ p before next upper lower)
      (rest : ExposedErrorTrain θ p next tail after) :
      ExposedErrorTrain θ p before ((upper, lower) :: tail) after

theorem ExposedErrorTrain.total_dose {θ p before cuts after}
    (train : ExposedErrorTrain θ p before cuts after) :
    after - before = (cuts.map (fun cut => 8 * (cut.1 - cut.2))).sum := by
  induction train with
  | nil => simp
  | cons span _ ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [span.dose]

theorem ExposedErrorTrain.log_gain_error {θ p before cuts after δhi δlo}
    (train : ExposedErrorTrain θ p before cuts after)
    (limits : ∀ cut ∈ cuts, |cut.1 - 1 / 10| ≤ δhi ∧ |cut.2 - 1 / 40| ≤ δlo) :
    |after - before - (cuts.length : ℝ) * (3 / 5)| ≤
      (cuts.length : ℝ) * (8 * (δhi + δlo)) := by
  induction train with
  | nil => simp
  | @cons before next after upper lower tail span rest ih =>
    have first := limits (upper, lower) (by simp)
    have head := abs_le.mp (span.dose_error first.1 first.2)
    have later := abs_le.mp (ih (fun cut mem => limits cut (List.mem_cons_of_mem _ mem)))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    exact abs_le.mpr ⟨by linarith [head.1, later.1], by linarith [head.2, later.2]⟩

/-- If the extremal gains after k = cuts.length exposed doses lie in
the high read band, a prepared read of that same port fires for every
allowed main threshold. The read clock and remaining physical state
are those of the prepared readout contract. -/
theorem tolerant_readout_after_error_train {θ ε time gains p level cuts after δhi δlo}
    (box : @PhysicalBox 1 θ ε) (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (train : ExposedErrorTrain θ p (gains p) cuts after)
    (limits : ∀ cut ∈ cuts, |cut.1 - 1 / 10| ≤ δhi ∧ |cut.2 - 1 / 40| ≤ δlo)
    (minGain : 2 ≤ Real.exp (gains p + (cuts.length : ℝ) * (3 / 5 - 8 * (δhi + δlo))))
    (maxGain : Real.exp (gains p + (cuts.length : ℝ) * (3 / 5 + 8 * (δhi + δlo))) ≤ 12 / 5)
    (other : ∀ q, q ≠ p → Real.exp (gains q) ≤ 18 / 5) :
    Nonempty (TolerantPortDecision θ time (Function.update gains p after) p true level) := by
  have bound := abs_le.mp (train.log_gain_error limits)
  apply tolerant_port_readout box threshold
  · change 2 ≤ Real.exp (Function.update gains p after p) ∧
      Real.exp (Function.update gains p after p) ≤ 12 / 5
    rw [Function.update_self]
    exact ⟨minGain.trans (Real.exp_le_exp.mpr (by linarith [bound.1])),
      (Real.exp_le_exp.mpr (by linarith [bound.2])).trans maxGain⟩
  · intro q hq
    rw [Function.update_of_ne hq]
    exact other q hq

private theorem exp_dose_lower : (12 / 7 : ℝ) ≤ Real.exp (11 / 20 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 11 / 20 by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem exp_dose_upper : Real.exp (13 / 20 : ℝ) ≤ 2 := by
  have h := Real.exp_bound (x := (13 / 20 : ℝ)) (n := 8) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith [(abs_sub_le_iff.mp h).1]

/-- The concrete high-band budget for one dose with both sensor
endpoints within five percent of nominal. -/
theorem one_error_dose_gain {z upper lower : ℝ}
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : |lower - 1 / 40| ≤ 1 / 800)
    (initial : 7 / 6 ≤ Real.exp z ∧ Real.exp z ≤ 6 / 5) :
    2 ≤ Real.exp (z + 8 * (upper - lower)) ∧ Real.exp (z + 8 * (upper - lower)) ≤ 12 / 5 := by
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp hi
  obtain ⟨lo₁, lo₂⟩ := abs_le.mp lo
  have dose : 11 / 20 ≤ 8 * (upper - lower) ∧ 8 * (upper - lower) ≤ 13 / 20 := by
    constructor <;> linarith
  rw [Real.exp_add]
  constructor
  · have h := mul_le_mul initial.1 (exp_dose_lower.trans (Real.exp_le_exp.mpr dose.1))
      (by norm_num : (0 : ℝ) ≤ 12 / 7) (Real.exp_pos _).le
    norm_num at h
    exact h
  · have h := mul_le_mul initial.2 ((Real.exp_le_exp.mpr dose.2).trans exp_dose_upper)
      (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 6 / 5)
    norm_num at h
    exact h

/-- The wide read band accepts every dose between the displayed endpoints. -/
theorem wide_error_dose_gain {z upper lower : ℝ}
    (dose : 11 / 20 ≤ 8 * (upper - lower) ∧ 8 * (upper - lower) ≤ 77 / 100)
    (initial : 7 / 6 ≤ Real.exp z ∧ Real.exp z ≤ 6 / 5) :
    2 ≤ Real.exp (z + 8 * (upper - lower)) ∧ Real.exp (z + 8 * (upper - lower)) ≤ 13 / 5 := by
  have expUpper : Real.exp (77 / 100 : ℝ) ≤ 13 / 6 := by
    have h := Real.exp_bound (x := (77 / 100 : ℝ)) (n := 8) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  rw [Real.exp_add]
  constructor
  · have h := mul_le_mul initial.1 (exp_dose_lower.trans (Real.exp_le_exp.mpr dose.1))
      (by norm_num : (0 : ℝ) ≤ 12 / 7) (Real.exp_pos _).le
    norm_num at h
    exact h
  · have h := mul_le_mul initial.2 ((Real.exp_le_exp.mpr dose.2).trans expUpper)
      (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 6 / 5)
    norm_num at h
    exact h

/-- A one-dose memory test on the same port. An untrained gain in
[7/6, 1.2] reads silent. One exposed ERROR dose with each sensor
endpoint within 5% of nominal makes the prepared read fire. -/
theorem tolerant_one_dose_memory {θ ε time gains p level after upper lower}
    (box : @PhysicalBox 1 θ ε) (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (span : ExposedErrorSpan θ p (gains p) after upper lower)
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : |lower - 1 / 40| ≤ 1 / 800)
    (initialGain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (other : ∀ q, q ≠ p → Real.exp (gains q) ≤ 18 / 5) :
    Nonempty (TolerantPortDecision θ time gains p false level) ∧
    Nonempty (TolerantPortDecision θ time (Function.update gains p after) p true level) := by
  constructor
  · exact tolerant_port_readout box threshold initialGain.2 other
  · apply tolerant_port_readout box threshold
    · have dose := span.dose
      rw [Function.update_self]
      rw [show after = gains p + 8 * (upper - lower) by linarith]
      exact one_error_dose_gain hi lo initialGain
    · intro q hq
      rw [Function.update_of_ne hq]
      exact other q hq

end RecursiveLearning.Native
