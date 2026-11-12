import Coincidence.TimedCurrentSeparation

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

/-! ### The amplitude ratio from two ports, and the end of training

The kernel adds the currents of the ports. Two ports trained separately by
canonical pulses, then read by one pulse on each at the same time, behave
as one port trained at relative amplitude one half. -/

theorem silent_of_peak {gain c fire : ℝ} (amplitude : 0 ≤ c * gain)
    (peak : 1 / 10 + c * gain * response 1 < fire) : SilentPulse gain c fire := by
  intro t ht
  rw [readyPulse_at_rest]
  have mono := response_strictMono_pulse.monotoneOn ht
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) ht.2
  have scaled := mul_le_mul_of_nonneg_left mono amplitude
  linarith

theorem firing_of_peak {gain c fire : ℝ} (peak : fire ≤ 1 / 10 + c * gain * response 1) :
    FiringPulse gain c fire :=
  ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [readyPulse_at_rest]; exact peak⟩

theorem silent_of_not_firing {gain c fire : ℝ} (quiet : ¬ FiringPulse gain c fire) :
    SilentPulse gain c fire := by
  intro t ht
  by_contra reached
  exact quiet ⟨t, ht, not_lt.mp reached⟩

theorem not_firing_of_silent {gain c fire : ℝ} (silent : SilentPulse gain c fire) :
    ¬ FiringPulse gain c fire := by
  rintro ⟨t, ht, reached⟩
  exact absurd (silent t ht) (not_lt.mpr reached)

/-- Two ports, each stopped under canonical training pulses, form together a
port stopped at relative amplitude one half. -/
theorem stopped_pair {g₁ g₂ fire d : ℝ} (pos₁ : 0 < g₁) (pos₂ : 0 < g₂)
    (first : StoppedTraining g₁ 1 fire d) (second : StoppedTraining g₂ 1 fire d) :
    StoppedTraining (g₁ + g₂) (1 / 2) fire d := by
  obtain ⟨fired₁, x₁, positive₁, max₁, silent₁⟩ := first
  obtain ⟨fired₂, x₂, _, max₂, silent₂⟩ := second
  have top₁ := fired₁.peak (by linarith)
  have top₂ := fired₂.peak (by linarith)
  have low₁ := silent₁.peak
  have low₂ := silent₂.peak
  have peak : 0 < response 1 := response_one_pos
  refine ⟨firing_of_peak (by linarith), max x₁ x₂, lt_max_of_lt_left positive₁,
    max_le max₁ max₂, ?_⟩
  have decay₁ : Real.exp (-(max x₁ x₂)) ≤ Real.exp (-x₁) :=
    Real.exp_le_exp.mpr (by linarith [le_max_left x₁ x₂])
  have decay₂ : Real.exp (-(max x₁ x₂)) ≤ Real.exp (-x₂) :=
    Real.exp_le_exp.mpr (by linarith [le_max_right x₁ x₂])
  have part₁ : g₁ * Real.exp (-(max x₁ x₂)) * response 1 ≤ g₁ * Real.exp (-x₁) * response 1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left decay₁ pos₁.le) peak.le
  have part₂ : g₂ * Real.exp (-(max x₁ x₂)) * response 1 ≤ g₂ * Real.exp (-x₂) * response 1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left decay₂ pos₂.le) peak.le
  apply silent_of_peak
  · exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) (Real.exp_pos _).le)
  · linarith

/-- Training by pulses of relative amplitude `c` stops. If each increment of
log-gain lies between `dMin > 0` and `d`, and the first pulse is silent,
some pulse is the first to fire, every earlier pulse was silent, and the
cell is then in the stopped state. -/
theorem training_stops {g x : ℕ → ℝ} {c fire dMin d : ℝ}
    (cPos : 0 < c) (start : 0 < g 0) (minPos : 0 < dMin)
    (step : ∀ n, g (n + 1) = g n * Real.exp (x n))
    (bounds : ∀ n, dMin ≤ x n ∧ x n ≤ d)
    (silent : SilentPulse (g 0) c fire) :
    ∃ n, StoppedTraining (g (n + 1)) c fire d ∧ ∀ m ≤ n, SilentPulse (g m) c fire := by
  classical
  have peak : 0 < response 1 := response_one_pos
  have positive : ∀ n, 0 < g n := by
    intro n
    induction n with
    | zero => exact start
    | succ k ih => rw [step k]; exact mul_pos ih (Real.exp_pos _)
  have growth : ∀ n, g 0 ≤ g n ∧ g 0 + (n : ℝ) * (g 0 * dMin) ≤ g n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have factor : 1 + dMin ≤ Real.exp (x k) := by
        linarith [Real.add_one_le_exp (x k), (bounds k).1]
      have scaled := mul_le_mul_of_nonneg_left factor (positive k).le
      have floor := mul_le_mul_of_nonneg_right ih.1 minPos.le
      rw [step k]
      push_cast
      constructor <;> nlinarith [mul_pos start minPos]
  have eventually : ∃ n, FiringPulse (g n) c fire := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((fire - 1 / 10) / (c * response 1) / (g 0 * dMin))
    have large : (fire - 1 / 10) / (c * response 1) < (N : ℝ) * (g 0 * dMin) :=
      (div_lt_iff₀ (mul_pos start minPos)).mp hN
    have reach : (fire - 1 / 10) / (c * response 1) ≤ g N := by
      linarith [(growth N).2, start]
    have scaled := mul_le_mul_of_nonneg_left reach (mul_pos cPos peak).le
    have cancel : c * response 1 * ((fire - 1 / 10) / (c * response 1)) = fire - 1 / 10 := by
      have hc : c ≠ 0 := cPos.ne'
      have hr : response 1 ≠ 0 := peak.ne'
      field_simp
    exact ⟨N, firing_of_peak (by linarith)⟩
  have nonzero : Nat.find eventually ≠ 0 := by
    intro zero
    have fired := Nat.find_spec eventually
    rw [zero] at fired
    exact not_firing_of_silent silent fired
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have before : ∀ m ≤ k, SilentPulse (g m) c fire := by
    intro m hm
    exact silent_of_not_firing (Nat.find_min eventually (by omega))
  have fired : FiringPulse (g (k + 1)) c fire := by
    have h := Nat.find_spec eventually
    rwa [hk] at h
  refine ⟨k, ?_, before⟩
  rw [step k] at fired ⊢
  exact stopped_of_last_step (before k le_rfl) fired
    (lt_of_lt_of_le minPos (bounds k).1) (bounds k).2

private theorem response_pair_low : response (239 / 1000) ≤ 26496 / 100000 := by
  have slow : Real.exp (-(1 / 2 : ℝ) * (239 / 1000)) ≤ 887365 / 1000000 := by
    have h : Real.exp (-(239 / 2000 : ℝ)) ∈ Icc (0 : ℝ) (887365 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.2 using 2
    norm_num
  have fast : (717972 / 1000000 : ℝ) ≤ Real.exp (-a * (239 / 1000)) := by
    have h : Real.exp (-(138629437 / 100000000 : ℝ) * (239 / 1000)) ∈
        Icc (717972 / 1000000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact h.1.trans (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.2]))
  have nonneg : 0 ≤ Real.exp (-(1 / 2 : ℝ) * (239 / 1000)) - Real.exp (-a * (239 / 1000)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith [a_coarse_bounds.1]))
  unfold response
  exact (mul_le_mul response_ratio_bounds.2 (show Real.exp (-(1 / 2 : ℝ) * (239 / 1000)) -
    Real.exp (-a * (239 / 1000)) ≤ 169393 / 1000000 by linarith)
    nonneg (by norm_num)).trans (by norm_num)

private theorem response_pair_high : (27935 / 100000 : ℝ) ≤ response (32 / 125) := by
  have slow : (879853 / 1000000 : ℝ) ≤ Real.exp (-(1 / 2) * (32 / 125)) := by
    have h : Real.exp (-(16 / 125 : ℝ)) ∈ Icc (879853 / 1000000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.1 using 2
    norm_num
  have fast : Real.exp (-a * (32 / 125)) ≤ 70125 / 100000 := by
    have h : Real.exp (-(138629436 / 100000000 : ℝ) * (32 / 125)) ∈
        Icc (0 : ℝ) (70125 / 100000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])).trans h.2
  have ratioNonneg : 0 ≤ a / (a - 1 / 2) :=
    (by norm_num : (0 : ℝ) ≤ 156414 / 100000).trans response_ratio_bounds.1
  unfold response
  exact (by norm_num : (27935 / 100000 : ℝ) ≤ (156414 / 100000) * (178603 / 1000000)).trans
    (mul_le_mul response_ratio_bounds.1 (show (178603 / 1000000 : ℝ) ≤
      Real.exp (-(1 / 2) * (32 / 125)) - Real.exp (-a * (32 / 125)) by linarith)
      (by norm_num) ratioNonneg)

theorem window_half :
    response (239 / 1000) ≤ (1 / 2) * Real.exp (-(1 / 20 : ℝ)) * response 1 ∧
    (1 / 2) * response 1 ≤ response (32 / 125) := by
  have step : Real.exp (-(1 / 20 : ℝ)) ∈ Icc (95122 / 100000 : ℝ) 1 :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  have peak := response_one_bounds
  have product : (95122 / 100000 : ℝ) * (55766 / 100000) ≤
      Real.exp (-(1 / 20 : ℝ)) * response 1 :=
    mul_le_mul step.1 peak.1 (by norm_num) (Real.exp_pos _).le
  constructor
  · rw [mul_assoc]
    linarith [response_pair_low]
  · linarith [response_pair_high, peak.2]


/-- A gain that reaches the FIRE level alone, while one dose of at most
1/20 below it did not, reaches it later than 0.355 units after the start
of the pulse: the response at 0.355 is below `exp(-1/20)` times its peak. -/
theorem window_alone : response (71 / 200) ≤ Real.exp (-(1 / 20 : ℝ)) * response 1 := by
  have step : Real.exp (-(1 / 20 : ℝ)) ∈ Icc (95122 / 100000 : ℝ) 1 :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  have peak := response_one_bounds
  have product : (95122 / 100000 : ℝ) * (55766 / 100000) ≤
      Real.exp (-(1 / 20 : ℝ)) * response 1 :=
    mul_le_mul step.1 peak.1 (by norm_num) (Real.exp_pos _).le
  linarith [response_low_point]

/-- Two ports trained separately by canonical pulses, with increments of at
most `1/20`, and read together: the cell fires between 0.239 and 0.256
model units after the two read pulses, for any gains and FIRE threshold. -/
theorem stopped_pair_read_latency {g₁ g₂ fire t : ℝ} (pos₁ : 0 < g₁) (pos₂ : 0 < g₂)
    (first : StoppedTraining g₁ 1 fire (1 / 20)) (second : StoppedTraining g₂ 1 fire (1 / 20))
    (read : FirstPulseReport (1 / 10) (g₁ + g₂) fire t) :
    t ∈ Ioc (239 / 1000 : ℝ) (32 / 125) :=
  stopped_read_latency (by norm_num) (by linarith) (stopped_pair pos₁ pos₂ first second) read
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ window_half.1 window_half.2

/-- Two such cells differ in read latency by less than 0.017 model units,
whatever their four gains and two FIRE thresholds. -/
theorem stopped_pair_read_skew {g₁ g₂ h₁ h₂ fire fire' t t' : ℝ}
    (pos₁ : 0 < g₁) (pos₂ : 0 < g₂) (pos₃ : 0 < h₁) (pos₄ : 0 < h₂)
    (first : StoppedTraining g₁ 1 fire (1 / 20)) (second : StoppedTraining g₂ 1 fire (1 / 20))
    (third : StoppedTraining h₁ 1 fire' (1 / 20)) (fourth : StoppedTraining h₂ 1 fire' (1 / 20))
    (read : FirstPulseReport (1 / 10) (g₁ + g₂) fire t)
    (read' : FirstPulseReport (1 / 10) (h₁ + h₂) fire' t') :
    |t - t'| < 17 / 1000 := by
  obtain ⟨lo, hi⟩ := stopped_pair_read_latency pos₁ pos₂ first second read
  obtain ⟨lo', hi'⟩ := stopped_pair_read_latency pos₃ pos₄ third fourth read'
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-! ### A rest charge that is close to its nominal value

Between pulses the main charge relaxes toward `1/10` without reaching it.
The window keeps its form, with a factor that tends to one with the
residual charge. -/

/-- The READY response from a charge `q0` to one pulse arriving at time zero. -/
theorem readyPulse_from (q0 gain t : ℝ) :
    readyPulse q0 gain 0 t =
      1 / 10 + (q0 - 1 / 10) * Real.exp (-(1 / 2) * t) + gain * response t := by
  simp [readyPulse]

/-- Training stopped at gain `gain` and relative amplitude `c`, seen from
rest charges within `δ` above `1/10`. The current gain fired from the
charge `qFire`, and the gain before the last increment, of at most `d`,
stayed silent from the charge `qSilent`. A later full-amplitude read from
the charge `qRead` reaches a response level between two bounds in which
neither the gain nor the charges appear. -/
theorem stopped_read_response_residual {gain c fire d δ x qFire qSilent qRead tFire t : ℝ}
    (cPos : 0 < c) (gainPos : 0 < gain) (margin : 1 / 10 + δ < fire)
    (fireCharge : qFire ∈ Icc (1 / 10) (1 / 10 + δ))
    (silentCharge : 1 / 10 ≤ qSilent) (readCharge : qRead ∈ Icc (1 / 10) (1 / 10 + δ))
    (increment : x ≤ d)
    (fireTime : tFire ∈ Icc (0 : ℝ) 1)
    (fired : fire ≤ readyPulse qFire (c * gain) 0 tFire)
    (silent : readyPulse qSilent (c * (gain * Real.exp (-x))) 0 1 < fire)
    (read : FirstPulseReport qRead gain fire t) :
    c * Real.exp (-d) * response 1 * (fire - 1 / 10 - δ) < response t * (fire - 1 / 10) ∧
    response t * (fire - 1 / 10 - δ) ≤ c * response 1 * (fire - 1 / 10) := by
  have peak : 0 < response 1 := response_one_pos
  have rise := response_strictMono_pulse.monotoneOn fireTime
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) fireTime.2
  have decayFire : (qFire - 1 / 10) * Real.exp (-(1 / 2) * tFire) ≤ δ := by
    have unit : Real.exp (-(1 / 2) * tFire) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [fireTime.1])
    nlinarith [fireCharge.1, fireCharge.2, Real.exp_pos (-(1 / 2) * tFire)]
  have decaySilent : 0 ≤ (qSilent - 1 / 10) * Real.exp (-(1 / 2) * (1 : ℝ)) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  have decayRead : 0 ≤ (qRead - 1 / 10) * Real.exp (-(1 / 2) * t) ∧
      (qRead - 1 / 10) * Real.exp (-(1 / 2) * t) ≤ δ := by
    have unit : Real.exp (-(1 / 2) * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [read.live.1])
    exact ⟨mul_nonneg (by linarith [readCharge.1]) (Real.exp_pos _).le,
      by nlinarith [readCharge.1, readCharge.2, Real.exp_pos (-(1 / 2) * t)]⟩
  have hit := read.hit
  rw [readyPulse_from] at fired silent hit
  have scaled := mul_le_mul_of_nonneg_left rise (mul_nonneg cPos.le gainPos.le)
  -- the three facts, as bounds on gain times a response level
  have top : fire - 1 / 10 - δ ≤ c * gain * response 1 := by linarith
  have bottom : c * (gain * Real.exp (-x)) * response 1 < fire - 1 / 10 := by linarith
  have level : fire - 1 / 10 - δ ≤ gain * response t ∧ gain * response t ≤ fire - 1 / 10 := by
    constructor <;> linarith [decayRead.1, decayRead.2]
  have decay : Real.exp (-d) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have gap : 0 < fire - 1 / 10 - δ := by linarith
  have levelNonneg : 0 ≤ response t := response_nonnegative read.live.1
  constructor
  · -- c e^{-d} h(1) (F - 1/10 - δ) ≤ c e^{-x} h(1) * (gain h(t)) < (F - 1/10) * h(t) after dividing by gain
    have first : c * Real.exp (-d) * response 1 ≤ c * Real.exp (-x) * response 1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left decay cPos.le) peak.le
    have lowPos : 0 ≤ c * Real.exp (-x) * response 1 :=
      mul_nonneg (mul_nonneg cPos.le (Real.exp_pos _).le) peak.le
    have chain : gain * (c * Real.exp (-x) * response 1 * (fire - 1 / 10 - δ)) <
        gain * (response t * (fire - 1 / 10)) := by
      have a₁ : c * Real.exp (-x) * response 1 * (fire - 1 / 10 - δ) ≤
          c * Real.exp (-x) * response 1 * (gain * response t) :=
        mul_le_mul_of_nonneg_left level.1 lowPos
      have a₂ : gain * (c * Real.exp (-x) * response 1) * (gain * response t) ≤
          (fire - 1 / 10) * (gain * response t) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg gainPos.le levelNonneg)
      have strict : gain * (c * Real.exp (-x) * response 1) < fire - 1 / 10 := by linarith
      nlinarith [mul_pos gainPos gap, mul_nonneg gainPos.le levelNonneg]
    have core := lt_of_mul_lt_mul_left chain gainPos.le
    have widen : c * Real.exp (-d) * response 1 * (fire - 1 / 10 - δ) ≤
        c * Real.exp (-x) * response 1 * (fire - 1 / 10 - δ) :=
      mul_le_mul_of_nonneg_right first gap.le
    exact widen.trans_lt core
  · have chain : gain * (response t * (fire - 1 / 10 - δ)) ≤
        gain * (c * response 1 * (fire - 1 / 10)) := by
      have a₁ : gain * response t * (fire - 1 / 10 - δ) ≤ (fire - 1 / 10) * (fire - 1 / 10 - δ) :=
        mul_le_mul_of_nonneg_right level.2 gap.le
      have a₂ : (fire - 1 / 10) * (fire - 1 / 10 - δ) ≤ (fire - 1 / 10) * (c * gain * response 1) :=
        mul_le_mul_of_nonneg_left top (by linarith)
      nlinarith
    exact le_of_mul_le_mul_left chain gainPos

end RecursiveLearning.Native
