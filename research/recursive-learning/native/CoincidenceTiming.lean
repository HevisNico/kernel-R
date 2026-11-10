import ParameterTraining

/-! Bounds on actual read FIRE dates and the resulting two-report timing test.
The numeric brackets below are proved over the reals using exponential series. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

theorem TolerantSnapshotDecision.firing_equation {θ s p level}
    (run : TolerantSnapshotDecision θ s p true level) :
    readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) 0 (run.stop - s.time) = level := by
  have h := run.charge.symm.trans run.outcome.2.2.1
  simpa only [readyPulse, sub_zero] using h

private theorem pulse_le_of_bounds {q₁ q₂ g₁ g₂ t : ℝ}
    (hq : q₁ ≤ q₂) (hg : g₁ ≤ g₂) (ht : 0 ≤ t) :
    readyPulse q₁ g₁ 0 t ≤ readyPulse q₂ g₂ 0 t := by
  apply (readyPulse_mono_initial (amplitude := g₁) (start := 0) (t := t) hq).trans
  have h := mul_le_mul_of_nonneg_right hg (response_nonnegative ht)
  simp only [readyPulse, sub_zero]
  linarith

/-- Evaluate the upper response at the early date and the lower response
at the late date. This brackets the actual FIRE latency for all allowed
read charges, gains and thresholds. -/
theorem TolerantSnapshotDecision.latency_bounds {θ s p level qLo qHi gLo gHi fLo fHi early late}
    (run : TolerantSnapshotDecision θ s p true level)
    (charge : s.x 0 .q ∈ Icc qLo qHi) (chargeCap : s.x 0 .q ≤ 7 / 50)
    (gain : Real.exp (s.x 0 (.z p)) ∈ Icc gLo gHi) (gainFloor : 9 / 5 ≤ Real.exp (s.x 0 (.z p)))
    (threshold : level ∈ Icc fLo fHi)
    (earlyIn : early ∈ Icc (0 : ℝ) (9 / 10)) (lateIn : late ∈ Icc (0 : ℝ) (9 / 10))
    (earlyBelow : readyPulse qHi gHi 0 early ≤ fLo)
    (lateAbove : fHi ≤ readyPulse qLo gLo 0 late) :
    run.stop - s.time ∈ Icc early late := by
  have after := run.outcome.1
  have before := run.outcome.2.1
  have fireIn : run.stop - s.time ∈ Icc (0 : ℝ) (9 / 10) := ⟨by linarith, by linarith⟩
  have mono := readyPulse_strictMono (start := 0) chargeCap gainFloor
  rw [zero_add] at mono
  have hit := run.firing_equation
  constructor
  · by_contra h
    have lt := mono fireIn earlyIn (lt_of_not_ge h)
    have le := (pulse_le_of_bounds charge.2 gain.2 earlyIn.1).trans (earlyBelow.trans threshold.1)
    linarith
  · by_contra h
    have lt := mono lateIn fireIn (lt_of_not_ge h)
    have le := threshold.2.trans (lateAbove.trans (pulse_le_of_bounds charge.1 gain.1 lateIn.1))
    linarith

private theorem exp_bracket {x low high : ℝ} {n : ℕ} (hx : |x| ≤ 1) (hn : 0 < n)
    (bounds :
      let sum := ∑ m ∈ Finset.range n, x ^ m / m.factorial
      let err := |x| ^ n * (n.succ / (n.factorial * n))
      low ≤ sum - err ∧ sum + err ≤ high) :
    Real.exp x ∈ Icc low high := by
  dsimp only at bounds
  have h := abs_le.mp (Real.exp_bound hx hn)
  exact ⟨by linarith [bounds.1, h.1], by linarith [bounds.2, h.2]⟩

theorem exp_bracket_10 {x low high : ℝ} (hx : |x| ≤ 1)
    (bounds :
      let sum := ∑ m ∈ Finset.range 10, x ^ m / m.factorial
      let err := |x| ^ 10 * (11 / (3628800 * 10))
      low ≤ sum - err ∧ sum + err ≤ high) :
    Real.exp x ∈ Icc low high := by
  apply exp_bracket (n := 10) hx (by norm_num)
  norm_num [Nat.factorial] at bounds ⊢
  exact bounds

theorem response_ratio_bounds :
    a / (a - 1 / 2) ∈ Icc (156414 / 100000 : ℝ) (156415 / 100000) := by
  have aPos : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  constructor
  · apply (le_div_iff₀ aPos).2
    dsimp [a]
    linarith [KernelR.log_four_bounds.2]
  · apply (div_le_iff₀ aPos).2
    dsimp [a]
    linarith [KernelR.log_four_bounds.1]

private theorem early_response :
    response (697 / 2000) ≤ 349172 / 1000000 := by
  have slow : Real.exp (-(1 / 2 : ℝ) * (697 / 2000)) ≤ 840087 / 1000000 := by
    have h : Real.exp (-(697 / 4000 : ℝ)) ∈ Icc (0 : ℝ) (840087 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.2 using 2
    norm_num
  have fast : (6168535 / 10000000 : ℝ) ≤ Real.exp (-a * (697 / 2000)) := by
    have h : Real.exp (-(138629437 / 100000000 : ℝ) * (697 / 2000)) ∈
        Icc (6168535 / 10000000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact h.1.trans (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.2]))
  have nonneg : 0 ≤ Real.exp (-(1 / 2 : ℝ) * (697 / 2000)) - Real.exp (-a * (697 / 2000)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith [a_coarse_bounds.1]))
  unfold response
  exact (mul_le_mul response_ratio_bounds.2 (show Real.exp (-(1 / 2 : ℝ) * (697 / 2000)) -
    Real.exp (-a * (697 / 2000)) ≤ 2232335 / 10000000 by linarith)
    nonneg (by norm_num)).trans (by norm_num)

private theorem late_response :
    (381033 / 1000000 : ℝ) ≤ response (199 / 500) := by
  have slow : (8195498 / 10000000 : ℝ) ≤ Real.exp (-(1 / 2) * (199 / 500)) := by
    have h : Real.exp (-(199 / 1000 : ℝ)) ∈ Icc (8195498 / 10000000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.1 using 2
    norm_num
  have fast : Real.exp (-a * (199 / 500)) ≤ 575944 / 1000000 := by
    have h : Real.exp (-(138629436 / 100000000 : ℝ) * (199 / 500)) ∈
        Icc (0 : ℝ) (575944 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])).trans h.2
  have aPos : 0 ≤ a / (a - 1 / 2) :=
    (by norm_num : (0 : ℝ) ≤ 156414 / 100000).trans response_ratio_bounds.1
  unfold response
  exact (by norm_num : (381033 / 1000000 : ℝ) ≤
    (156414 / 100000) * (2436058 / 10000000)).trans
    (mul_le_mul response_ratio_bounds.1 (show (2436058 / 10000000 : ℝ) ≤
      Real.exp (-(1 / 2) * (199 / 500)) - Real.exp (-a * (199 / 500)) by linarith)
      (by norm_num) aPos)

/-- Three sufficient rectangles for the ERROR and FIRE radii at
100 microseconds per model unit, for nominal ERROR exit 0.01. -/
def Exit001TimingBox (error fire : ℝ) : Prop :=
  (error ≤ 1 / 100 ∧ fire ≤ 3 / 100) ∨
  (error ≤ 2 / 100 ∧ fire ≤ 2 / 100) ∨
  (error ≤ 3 / 100 ∧ fire ≤ 1 / 100)

/-- The discrete version uses radii in thousandths. -/
def Exit001TimingGrid (error fire : ℕ) : Prop :=
  (error ≤ 10 ∧ fire ≤ 30) ∨ (error ≤ 20 ∧ fire ≤ 20) ∨ (error ≤ 30 ∧ fire ≤ 10)
deriving Decidable

theorem Exit001TimingGrid.sound {e f : ℕ} (h : Exit001TimingGrid e f) :
    Exit001TimingBox ((e : ℝ) / 1000) ((f : ℝ) / 1000) := by
  rcases h with ⟨he, hf⟩ | ⟨he, hf⟩ | ⟨he, hf⟩
  · left
    constructor <;> linarith [show (e : ℝ) ≤ 10 by exact_mod_cast he,
      show (f : ℝ) ≤ 30 by exact_mod_cast hf]
  · right; left
    constructor <;> linarith [show (e : ℝ) ≤ 20 by exact_mod_cast he,
      show (f : ℝ) ≤ 20 by exact_mod_cast hf]
  · right; right
    constructor <;> linarith [show (e : ℝ) ≤ 30 by exact_mod_cast he,
      show (f : ℝ) ≤ 10 by exact_mod_cast hf]

theorem exit_001_timing_grid_count :
    let radii : List ℕ := [0, 3, 10, 20, 30, 50]
    ((radii.flatMap fun e => radii.map fun f => (e, f)).filter
      fun pair => decide (Exit001TimingGrid pair.1 pair.2)).length = 22 := by decide

private theorem corner_bounds {e f : ℝ} (box : Exit001TimingBox e f) :
    readyPulse (201 / 2000) ((6 / 5) * Real.exp (18 / 25 + e)) 0 (697 / 2000) ≤ 1 - f ∧
    1 + f ≤ readyPulse (1 / 10) ((6 / 5) * Real.exp (18 / 25 - e)) 0 (199 / 500) := by
  have h (err threshold gLo gHi : ℝ) (he : e ≤ err) (hf : f ≤ threshold)
      (gainLo : gLo ≤ (6 / 5) * Real.exp (18 / 25 - err)) (gainLoNonneg : 0 ≤ gLo)
      (gainHi : (6 / 5) * Real.exp (18 / 25 + err) ≤ gHi)
      (lowCheck : 201 / 2000 + gHi * (349172 / 1000000) ≤ 1 - threshold)
      (highCheck : 1 + threshold ≤ 1 / 10 + gLo * (381033 / 1000000)) :
      readyPulse (201 / 2000) ((6 / 5) * Real.exp (18 / 25 + e)) 0 (697 / 2000) ≤ 1 - f ∧
      1 + f ≤ readyPulse (1 / 10) ((6 / 5) * Real.exp (18 / 25 - e)) 0 (199 / 500) := by
    have loGain : gLo ≤ (6 / 5) * Real.exp (18 / 25 - e) :=
      gainLo.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (show 18 / 25 - err ≤ 18 / 25 - e by linarith)) (by norm_num))
    have hiGain : (6 / 5) * Real.exp (18 / 25 + e) ≤ gHi :=
      (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (show 18 / 25 + e ≤ 18 / 25 + err by linarith)) (by norm_num)).trans gainHi
    have carry : Real.exp (-(697 / 4000 : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by norm_num)
    have early := (pulse_le_of_bounds (q₁ := 201 / 2000) le_rfl hiGain (by norm_num : (0 : ℝ) ≤ 697 / 2000))
    have late := (pulse_le_of_bounds (q₁ := 1 / 10) le_rfl loGain (by norm_num : (0 : ℝ) ≤ 199 / 500))
    have eBound := mul_le_mul_of_nonneg_left early_response
      (show 0 ≤ gHi from (mul_nonneg (by norm_num) (Real.exp_pos _).le).trans gainHi)
    have lBound := mul_le_mul_of_nonneg_left late_response gainLoNonneg
    simp only [readyPulse, sub_zero] at early late ⊢
    norm_num at early late ⊢
    exact ⟨by linarith, by linarith⟩
  rcases box with ⟨he, hf⟩ | ⟨he, hf⟩ | ⟨he, hf⟩
  · apply h (1 / 100) (3 / 100) (2440788 / 1000000) (2490098 / 1000000) he hf
    · have bound : Real.exp (71 / 100 : ℝ) ∈ Icc (2033991 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      norm_num
      linarith [bound.1]
    · norm_num
    · have bound : Real.exp (73 / 100 : ℝ) ∈ Icc (0 : ℝ) (2075081 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      norm_num
      linarith [bound.2]
    · norm_num
    · norm_num
  · apply h (2 / 100) (2 / 100) (2416502 / 1000000) (2515124 / 1000000) he hf
    · have bound : Real.exp (70 / 100 : ℝ) ∈ Icc (2013752 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      norm_num
      linarith [bound.1]
    · norm_num
    · have bound : Real.exp (74 / 100 : ℝ) ∈ Icc (0 : ℝ) (2095936 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      norm_num
      linarith [bound.2]
    · norm_num
    · norm_num
  · apply h (3 / 100) (1 / 100) (2392457 / 1000000) (2540402 / 1000000) he hf
    · have bound : Real.exp (69 / 100 : ℝ) ∈ Icc (1993715 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      norm_num
      linarith [bound.1]
    · norm_num
    · have bound : Real.exp (75 / 100 : ℝ) ∈ Icc (0 : ℝ) (2117001 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      norm_num
      linarith [bound.2]
    · norm_num
    · norm_num

/-- The actual trained-port FIRE is in a common latency interval across
either fabrication box and all three maximal timing rectangles. -/
theorem training_read_exit_001_benchmark {θ ε time gains p delay e f}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (errors : Exit001TimingBox e f)
    (hi : |(θ 0).thresholds.error p - 1 / 10| ≤ e / 10)
    (lo : |(θ 0).thresholds.auxReady p - 1 / 100| ≤ e / 40)
    (fire : |(θ 0).thresholds.fire - 1| ≤ f)
    (delayMin : 333 / 20 ≤ delay)
    (gain : Real.exp (gains p) = 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ T final,
      T - (time + delay) ∈ Icc (697 / 2000) (199 / 500) ∧
      (∃ ex : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p delay) final,
        ParameterCompleteThrough ex T) ∧
      ∀ {u} (ex : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p delay) u),
        ParameterCompleteThrough ex T → u.ObservationalEq final ∧ ex.emissionTimes 0 = [T] := by
  let upper := (θ 0).thresholds.error p
  let lower := (θ 0).thresholds.auxReady p
  let level := (θ 0).thresholds.fire
  change |upper - 1 / 10| ≤ e / 10 at hi
  change |lower - 1 / 100| ≤ e / 40 at lo
  change |level - 1| ≤ f at fire
  have eMax : e ≤ 3 / 100 := by rcases errors with h | h | h <;> linarith [h.1]
  have fMax : f ≤ 3 / 100 := by rcases errors with h | h | h <;> linarith [h.2]
  have hi₅ : |upper - 1 / 10| ≤ 1 / 200 := by linarith
  have hhi := abs_le.mp hi
  have hlo := abs_le.mp lo
  have hfire := abs_le.mp fire
  have threshold : level ∈ Icc (19 / 20 : ℝ) (21 / 20) := ⟨by linarith [hfire.1], by linarith [hfire.2]⟩
  have dose : 18 / 25 - e ≤ 8 * (upper - lower) ∧ 8 * (upper - lower) ≤ 18 / 25 + e :=
    ⟨by linarith [hhi.1, hlo.2], by linarith [hhi.2, hlo.1]⟩
  have decay : Real.exp (-(1 / 2) * (delay - 159 / 100)) ≤ 1 / 1680 := by
    have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 15 / 2 by norm_num) 15
    norm_num [Finset.sum_range_succ] at series
    calc
      _ ≤ Real.exp (-(15 / 2)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num)
          (show (1680 : ℝ) ≤ Real.exp (15 / 2) by linarith)
  have offset : |lower - 1 / 40| ≤ 13 / 800 := abs_le.mpr ⟨by linarith [hlo.1], by linarith [hlo.2]⟩
  have rest : |lower - 1 / 40| * Real.exp (-(1 / 2) * (delay - 159 / 100)) ≤ 1 / 100000 :=
    (mul_le_mul offset decay (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
  have birth : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5 := by rw [gain]; norm_num
  obtain ⟨run⟩ := training_read_exists_in_band (time := time) box threshold hi₅
    (by linarith [hlo.1] : 7 / 800 ≤ lower) ⟨by linarith [dose.1], by linarith [dose.2]⟩
    (by linarith) rest birth caps
  have readCharge : run.handoff.readStart.x 0 .q ∈ Icc (1 / 10 : ℝ) (201 / 2000) := by
    refine ⟨run.handoff.ready_at_read.charge.1, run.read_charge_bound.trans ?_⟩
    have h := mul_le_mul_of_nonneg_left decay (by norm_num : (0 : ℝ) ≤ 21 / 25)
    linarith
  have readGainEq : Real.exp (run.handoff.readStart.x 0 (.z p)) = (6 / 5) * Real.exp (8 * (upper - lower)) := by
    rw [run.handoff.learned_at_read, run.dose_from_birth, Real.exp_add, gain]
  have readGain : Real.exp (run.handoff.readStart.x 0 (.z p)) ∈
      Icc ((6 / 5) * Real.exp (18 / 25 - e)) ((6 / 5) * Real.exp (18 / 25 + e)) := by
    rw [readGainEq]
    exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr dose.1) (by norm_num),
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr dose.2) (by norm_num)⟩
  have gainFloor : 9 / 5 ≤ Real.exp (run.handoff.readStart.x 0 (.z p)) := by
    rw [readGainEq]
    linarith [Real.add_one_le_exp (8 * (upper - lower)), dose.1]
  have corners := corner_bounds errors
  have latency := run.handoff.decision.latency_bounds readCharge
    (readCharge.2.trans (by norm_num)) readGain gainFloor
    (show level ∈ Icc (1 - f) (1 + f) from ⟨by linarith [hfire.1], by linarith [hfire.2]⟩)
    (by norm_num) (by norm_num) corners.1 corners.2
  rw [run.read_date] at latency
  exact ⟨run.handoff.decision.stop, run.handoff.decision.final, latency,
    ⟨run.parameterExecution config, run.parameterComplete config threshold.1⟩,
    fun ex complete => run.every_complete_run config box threshold hi₅ (by linarith [hlo.1]) caps ex complete⟩

/-- At 100 microseconds per model unit, the two trained-port reports
satisfy the registered 15 microsecond aperture exactly for zero offset.
The wires use one common delay, so it cancels from the arrival skew. -/
theorem coincidence_of_trained_latency {leftRead rightRead leftFire rightFire wire offset jitterL jitterR : ℝ}
    (left : leftFire - leftRead ∈ Icc (697 / 2000) (199 / 500))
    (right : rightFire - rightRead ∈ Icc (697 / 2000) (199 / 500))
    (jitterLeft : |jitterL| ≤ 1 / 20) (jitterRight : |jitterR| ≤ 1 / 20)
    (schedule : rightRead - leftRead = offset + jitterR - jitterL)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10) :
    |(rightFire + wire) - (leftFire + wire)| < 3 / 20 ↔ offset = 0 := by
  have jl := abs_le.mp jitterLeft
  have jr := abs_le.mp jitterRight
  have l := left.1
  have l' := left.2
  have r := right.1
  have r' := right.2
  rw [abs_lt]
  rcases offsets with h | h | h <;> subst offset <;> constructor
  · intro skew
    linarith [skew.1, jl.1, jr.2]
  · norm_num
  · simp
  · intro _
    exact ⟨by linarith [jl.2, jr.1], by linarith [jl.1, jr.2]⟩
  · intro skew
    linarith [skew.2, jl.2, jr.1]
  · norm_num

end RecursiveLearning.Native
