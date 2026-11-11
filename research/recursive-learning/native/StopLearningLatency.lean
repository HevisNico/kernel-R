import TimedCurrentSeparation

/-! Read latency after training that stops at the first FIRE on a weakened
pulse. The statements concern the READY read equation of a rested cell.

A training pulse of relative amplitude `c` acts on the main charge as a
canonical pulse at gain `c * gain`. If the last gain increment turned a
silent weakened pulse into a firing one, the latency of a later
full-amplitude read is confined to an interval that depends on `c` and on
the largest increment only. The gain and the FIRE threshold do not appear
in it. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The unit response rises throughout the pulse. -/
theorem response_strictMono_pulse : StrictMonoOn response (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun v _ => (response_derivative v).continuousAt.continuousWithinAt)
  intro v hv
  have ht := interior_subset hv
  rw [(response_derivative v).deriv]
  have alo : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have tail : (1 / 4 : ℝ) ≤ Real.exp (-a * v) := by
    rw [← exp_neg_a]
    exact Real.exp_le_exp.mpr
      (by nlinarith [mul_nonneg (show 0 ≤ a by linarith) (sub_nonneg.mpr ht.2)])
  linarith [mul_le_mul alo tail (by norm_num) (by linarith : 0 ≤ a),
    response_uniform_upper ht.1]

theorem response_zero : response 0 = 0 := by
  simp [response]

theorem response_one_pos : 0 < response 1 := by
  have h := response_strictMono_pulse (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) zero_lt_one
  rwa [response_zero] at h

/-- The READY response of a rested cell to one pulse arriving at time zero. -/
theorem readyPulse_at_rest (gain t : ℝ) :
    readyPulse (1 / 10) gain 0 t = 1 / 10 + gain * response t := by
  simp [readyPulse]

/-- A pulse of relative amplitude `c` leaves a rested cell below its FIRE
threshold for the whole pulse. -/
def SilentPulse (gain c fire : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, readyPulse (1 / 10) (c * gain) 0 t < fire

/-- A pulse of relative amplitude `c` brings a rested cell to its FIRE
threshold during the pulse. -/
def FiringPulse (gain c fire : ℝ) : Prop :=
  ∃ t ∈ Icc (0 : ℝ) 1, fire ≤ readyPulse (1 / 10) (c * gain) 0 t

theorem SilentPulse.peak {gain c fire : ℝ} (h : SilentPulse gain c fire) :
    1 / 10 + c * gain * response 1 < fire := by
  have top := h 1 ⟨zero_le_one, le_rfl⟩
  rwa [readyPulse_at_rest] at top

theorem FiringPulse.peak {gain c fire : ℝ} (h : FiringPulse gain c fire)
    (amplitude : 0 ≤ c * gain) : fire ≤ 1 / 10 + c * gain * response 1 := by
  obtain ⟨t, ht, reached⟩ := h
  rw [readyPulse_at_rest] at reached
  have mono := response_strictMono_pulse.monotoneOn ht
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) ht.2
  have scaled := mul_le_mul_of_nonneg_left mono amplitude
  linarith

/-- The state in which training by weakened pulses stops. The current gain
fires on a weakened pulse, and the gain before the last increment did not.
That increment was at most `d` in log-gain. -/
def StoppedTraining (gain c fire d : ℝ) : Prop :=
  FiringPulse gain c fire ∧
    ∃ x, 0 < x ∧ x ≤ d ∧ SilentPulse (gain * Real.exp (-x)) c fire

/-- One increment of at most `d` that turns a silent weakened pulse into a
firing one leaves the cell in the stopped state. -/
theorem stopped_of_last_step {gain c fire d x : ℝ} (silent : SilentPulse gain c fire)
    (fired : FiringPulse (gain * Real.exp x) c fire) (positive : 0 < x) (bounded : x ≤ d) :
    StoppedTraining (gain * Real.exp x) c fire d := by
  refine ⟨fired, x, positive, bounded, ?_⟩
  rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- After training stops, the response reached at the read FIRE lies between
two levels fixed by the amplitude ratio and the largest increment. -/
theorem stopped_read_response {gain c fire d t : ℝ} (cPos : 0 < c) (gainPos : 0 < gain)
    (stopped : StoppedTraining gain c fire d) (read : FirstPulseReport (1 / 10) gain fire t) :
    c * Real.exp (-d) * response 1 < response t ∧ response t ≤ c * response 1 := by
  obtain ⟨fired, x, _, xMax, silent⟩ := stopped
  have hit := read.hit
  rw [readyPulse_at_rest] at hit
  have upper := fired.peak (mul_nonneg cPos.le gainPos.le)
  have lower := silent.peak
  have peak : 0 < response 1 := response_one_pos
  have decay : Real.exp (-d) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  constructor
  · have scaled : gain * (c * Real.exp (-x) * response 1) < gain * response t := by linarith
    have strict := lt_of_mul_lt_mul_left scaled gainPos.le
    have step : c * Real.exp (-d) * response 1 ≤ c * Real.exp (-x) * response 1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left decay cPos.le) peak.le
    exact step.trans_lt strict
  · have scaled : gain * response t ≤ gain * (c * response 1) := by linarith
    exact le_of_mul_le_mul_left scaled gainPos

/-- The read latency lies in a window given by two certified points of the
unit response. The gain and the FIRE threshold do not enter the window. -/
theorem stopped_read_latency {gain c fire d t tLo tHi : ℝ} (cPos : 0 < c) (gainPos : 0 < gain)
    (stopped : StoppedTraining gain c fire d) (read : FirstPulseReport (1 / 10) gain fire t)
    (lo : tLo ∈ Icc (0 : ℝ) 1) (hi : tHi ∈ Icc (0 : ℝ) 1)
    (below : response tLo ≤ c * Real.exp (-d) * response 1)
    (above : c * response 1 ≤ response tHi) :
    t ∈ Ioc tLo tHi := by
  obtain ⟨h₁, h₂⟩ := stopped_read_response cPos gainPos stopped read
  exact ⟨(response_strictMono_pulse.lt_iff_lt lo read.live).mp (below.trans_lt h₁),
    (response_strictMono_pulse.le_iff_le read.live hi).mp (h₂.trans above)⟩

/-- A cell that fires on a weakened pulse fires on a full pulse. -/
theorem stopped_read_exists {gain c fire : ℝ} (cPos : 0 < c) (cLt : c < 1) (gainPos : 0 < gain)
    (rest : 1 / 10 < fire) (fired : FiringPulse gain c fire) :
    ∃ t, FirstPulseReport (1 / 10) gain fire t := by
  have peak := fired.peak (mul_nonneg cPos.le gainPos.le)
  have rise : 0 < response 1 := response_one_pos
  have top : fire < readyPulse (1 / 10) gain 0 1 := by
    rw [readyPulse_at_rest]
    nlinarith [mul_pos (mul_pos gainPos rise) (sub_pos.mpr cLt)]
  have start : readyPulse (1 / 10) gain 0 0 < fire := by
    rw [readyPulse_at_rest, response_zero]
    linarith
  have continuous : Continuous (readyPulse (1 / 10) gain 0) :=
    continuous_iff_continuousAt.mpr fun t => (readyPulse_derivative _ _ _ t).continuousAt
  obtain ⟨root, pos, late, hit, before⟩ :=
    scalar_first_crossing continuous zero_lt_one start top
  exact ⟨root, ⟨⟨pos.le, late.le⟩, hit, before⟩⟩

/-- Two cells trained the same way read within the width of the window,
whatever their gains and FIRE thresholds. -/
theorem stopped_read_skew {gain₁ gain₂ c fire₁ fire₂ d t₁ t₂ tLo tHi : ℝ} (cPos : 0 < c)
    (pos₁ : 0 < gain₁) (pos₂ : 0 < gain₂)
    (stopped₁ : StoppedTraining gain₁ c fire₁ d) (stopped₂ : StoppedTraining gain₂ c fire₂ d)
    (read₁ : FirstPulseReport (1 / 10) gain₁ fire₁ t₁)
    (read₂ : FirstPulseReport (1 / 10) gain₂ fire₂ t₂)
    (lo : tLo ∈ Icc (0 : ℝ) 1) (hi : tHi ∈ Icc (0 : ℝ) 1)
    (below : response tLo ≤ c * Real.exp (-d) * response 1)
    (above : c * response 1 ≤ response tHi) :
    |t₁ - t₂| < tHi - tLo := by
  obtain ⟨a₁, b₁⟩ := stopped_read_latency cPos pos₁ stopped₁ read₁ lo hi below above
  obtain ⟨a₂, b₂⟩ := stopped_read_latency cPos pos₂ stopped₂ read₂ lo hi below above
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem response_one_bounds :
    response 1 ∈ Icc (55766 / 100000 : ℝ) (55767 / 100000) := by
  have half : Real.exp (-(1 / 2 : ℝ)) ∈ Icc (606530 / 1000000 : ℝ) (606531 / 1000000) :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  have value : response 1 = a / (a - 1 / 2) * (Real.exp (-(1 / 2 : ℝ)) - 1 / 4) := by
    unfold response
    rw [mul_one, mul_one, exp_neg_a]
  have ratio := response_ratio_bounds
  have nonneg : (0 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) - 1 / 4 := by linarith [half.1]
  have ratioNonneg : (0 : ℝ) ≤ a / (a - 1 / 2) := (by norm_num : (0 : ℝ) ≤ 156414 / 100000).trans ratio.1
  rw [value]
  constructor
  · exact (by norm_num : (55766 / 100000 : ℝ) ≤ (156414 / 100000) * (356530 / 1000000)).trans
      (mul_le_mul ratio.1 (by linarith [half.1]) (by norm_num) ratioNonneg)
  · exact (mul_le_mul ratio.2 (show Real.exp (-(1 / 2 : ℝ)) - 1 / 4 ≤ 356531 / 1000000 by
      linarith [half.2]) nonneg (by norm_num)).trans (by norm_num)

private theorem response_low_point : response (71 / 200) ≤ 35357 / 100000 := by
  have slow : Real.exp (-(1 / 2 : ℝ) * (71 / 200)) ≤ 837362 / 1000000 := by
    have h : Real.exp (-(71 / 400 : ℝ)) ∈ Icc (0 : ℝ) (837362 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.2 using 2
    norm_num
  have fast : (61132 / 100000 : ℝ) ≤ Real.exp (-a * (71 / 200)) := by
    have h : Real.exp (-(138629437 / 100000000 : ℝ) * (71 / 200)) ∈
        Icc (61132 / 100000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact h.1.trans (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.2]))
  have nonneg : 0 ≤ Real.exp (-(1 / 2 : ℝ) * (71 / 200)) - Real.exp (-a * (71 / 200)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith [a_coarse_bounds.1]))
  unfold response
  exact (mul_le_mul response_ratio_bounds.2 (show Real.exp (-(1 / 2 : ℝ) * (71 / 200)) -
    Real.exp (-a * (71 / 200)) ≤ 226042 / 1000000 by linarith)
    nonneg (by norm_num)).trans (by norm_num)

private theorem response_high_point : (3729 / 10000 : ℝ) ≤ response (77 / 200) := by
  have slow : (82489 / 100000 : ℝ) ≤ Real.exp (-(1 / 2) * (77 / 200)) := by
    have h : Real.exp (-(77 / 400 : ℝ)) ∈ Icc (82489 / 100000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.1 using 2
    norm_num
  have fast : Real.exp (-a * (77 / 200)) ≤ 58642 / 100000 := by
    have h : Real.exp (-(138629436 / 100000000 : ℝ) * (77 / 200)) ∈
        Icc (0 : ℝ) (58642 / 100000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])).trans h.2
  have ratioNonneg : 0 ≤ a / (a - 1 / 2) :=
    (by norm_num : (0 : ℝ) ≤ 156414 / 100000).trans response_ratio_bounds.1
  unfold response
  exact (by norm_num : (3729 / 10000 : ℝ) ≤ (156414 / 100000) * (23847 / 100000)).trans
    (mul_le_mul response_ratio_bounds.1 (show (23847 / 100000 : ℝ) ≤
      Real.exp (-(1 / 2) * (77 / 200)) - Real.exp (-a * (77 / 200)) by linarith)
      (by norm_num) ratioNonneg)

private theorem window_two_thirds :
    response (71 / 200) ≤ (2 / 3) * Real.exp (-(1 / 20 : ℝ)) * response 1 ∧
    (2 / 3) * response 1 ≤ response (77 / 200) := by
  have step : Real.exp (-(1 / 20 : ℝ)) ∈ Icc (95122 / 100000 : ℝ) 1 :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  have peak := response_one_bounds
  have product : (95122 / 100000 : ℝ) * (55766 / 100000) ≤
      Real.exp (-(1 / 20 : ℝ)) * response 1 :=
    mul_le_mul step.1 peak.1 (by norm_num) (Real.exp_pos _).le
  constructor
  · rw [mul_assoc]
    linarith [response_low_point]
  · linarith [response_high_point, peak.2]

/-- With training pulses at two thirds of the read amplitude and increments
of at most `1/20` in log-gain, every read fires between 0.355 and 0.385
model units after its pulse, for any positive gain and any FIRE threshold. -/
theorem stopped_read_latency_two_thirds {gain fire t : ℝ} (gainPos : 0 < gain)
    (stopped : StoppedTraining gain (2 / 3) fire (1 / 20))
    (read : FirstPulseReport (1 / 10) gain fire t) :
    t ∈ Ioc (71 / 200 : ℝ) (77 / 200) :=
  stopped_read_latency (by norm_num) gainPos stopped read
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    window_two_thirds.1 window_two_thirds.2

/-- Two cells trained this way differ in read latency by less than 0.03
model units, whatever their gains and FIRE thresholds. -/
theorem stopped_read_skew_two_thirds {gain₁ gain₂ fire₁ fire₂ t₁ t₂ : ℝ}
    (pos₁ : 0 < gain₁) (pos₂ : 0 < gain₂)
    (stopped₁ : StoppedTraining gain₁ (2 / 3) fire₁ (1 / 20))
    (stopped₂ : StoppedTraining gain₂ (2 / 3) fire₂ (1 / 20))
    (read₁ : FirstPulseReport (1 / 10) gain₁ fire₁ t₁)
    (read₂ : FirstPulseReport (1 / 10) gain₂ fire₂ t₂) :
    |t₁ - t₂| < 3 / 100 := by
  have h := stopped_read_skew (by norm_num : (0 : ℝ) < 2 / 3) pos₁ pos₂ stopped₁ stopped₂
    read₁ read₂ (tLo := 71 / 200) (tHi := 77 / 200)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    window_two_thirds.1 window_two_thirds.2
  norm_num at h
  exact h

end RecursiveLearning.Native
