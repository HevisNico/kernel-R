import KernelR.HybridFirstLearnedFireExistence
import KernelR.HybridPulseRoot

/-! Equal real resting responses give equal physical latencies. All source
and receiving clocks remain their actual dates, including fresh wire jitter. -/
namespace KernelR.Hybrid
open Set

/-- At exact rest the carried term vanishes, so positivity of the actual
amplitude alone gives strict monotonicity on the physical firing bracket. -/
theorem readyPulse_rest_strictMono {amplitude start : ℝ} (hG : 0 < amplitude) :
    StrictMonoOn (readyPulse (1 / 10) amplitude start) (Icc start (start + 9 / 10)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t _ => (readyPulse_derivative (1 / 10) amplitude start t).continuousAt.continuousWithinAt)
  intro t ht
  have hcc := interior_subset ht
  have hd : 0 ≤ t - start := sub_nonneg.mpr hcc.1
  have hu : t - start ≤ 9 / 10 := by linarith [hcc.2]
  have hresponse : 0 < a * Real.exp (-a * (t - start)) - (1 / 2) * response (t - start) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 60) (response_derivative_lower hd hu)
  have hpositive := mul_pos hG hresponse
  rw [(readyPulse_derivative (1 / 10) amplitude start t).deriv]
  dsimp only [readyPulse]
  nlinarith

/-- Translation of the source origin changes no latency of the same resting
response. Both roots are actual threshold equations, not selected calendars. -/
theorem readyPulse_rest_roots_same_latency {amplitude sourceA sourceB latencyA latencyB : ℝ}
    (hG : 0 < amplitude)
    (hA : latencyA ∈ Icc (0 : ℝ) (9 / 10))
    (hB : latencyB ∈ Icc (0 : ℝ) (9 / 10))
    (hrootA : readyPulse (1 / 10) amplitude sourceA (sourceA + latencyA) = 1)
    (hrootB : readyPulse (1 / 10) amplitude sourceB (sourceB + latencyB) = 1) :
    latencyA = latencyB := by
  have ha : readyPulse (1 / 10) amplitude 0 latencyA = 1 := by
    simpa only [readyPulse,add_sub_cancel_left,sub_zero] using hrootA
  have hb : readyPulse (1 / 10) amplitude 0 latencyB = 1 := by
    simpa only [readyPulse,add_sub_cancel_left,sub_zero] using hrootB
  exact (readyPulse_rest_strictMono (start := 0) hG).injOn
    (by simpa using hA) (by simpa using hB) (ha.trans hb.symm)

/-- Two independently constructed firings retain a common physical latency
only because their own current gain and exact resting charges coincide. -/
theorem FirstLearnedFire.latency_eq_of_rest_gain {n θ route s t i p}
    (c : @FirstLearnedFire n θ route s i p) (d : FirstLearnedFire θ route t i p)
    (hqS : s.x i .q = 1 / 10) (hqT : t.x i .q = 1 / 10)
    (hz : s.x i (.z p) = t.x i (.z p)) : c.latency = d.latency := by
  have hc := c.response_root
  have hd := d.response_root
  rw [hqS] at hc
  rw [hqT,← hz] at hd
  exact readyPulse_rest_roots_same_latency (Real.exp_pos _)
    ⟨by linarith [c.early],c.deadline.le⟩ ⟨by linarith [d.early],d.deadline.le⟩ hc hd

/-- The source spacing transfers to the actual firing dates; no common
latency is supplied as a premise. -/
theorem FirstLearnedFire.firing_gap_eight_of_rest_gain {n θ route s t i p}
    (c : @FirstLearnedFire n θ route s i p) (d : FirstLearnedFire θ route t i p)
    (hqS : s.x i .q = 1 / 10) (hqT : t.x i .q = 1 / 10)
    (hz : s.x i (.z p) = t.x i (.z p)) (hstep : t.time = s.time + 8) :
    d.final.time = c.final.time + 8 := by
  rw [d.date,c.date,hstep,← c.latency_eq_of_rest_gain d hqS hqT hz]
  ring

/-- The two fresh delays are kept independent in the receiving interval. -/
theorem received_gap_eight_of_fire_gap {first second delayFirst delaySecond : ℝ}
    (hfire : second = first + 8)
    (hfirst : 3 / 10 ≤ delayFirst ∧ delayFirst ≤ 2 / 5)
    (hsecond : 3 / 10 ≤ delaySecond ∧ delaySecond ≤ 2 / 5) :
    79 / 10 ≤ (second + delaySecond) - (first + delayFirst) ∧
      (second + delaySecond) - (first + delayFirst) ≤ 81 / 10 := by
  constructor <;> linarith [hfirst.1,hfirst.2,hsecond.1,hsecond.2]

theorem FirstLearnedFire.received_gap_eight_of_rest_gain {n θ route s t i p}
    (c : @FirstLearnedFire n θ route s i p) (d : FirstLearnedFire θ route t i p)
    (hqS : s.x i .q = 1 / 10) (hqT : t.x i .q = 1 / 10)
    (hz : s.x i (.z p) = t.x i (.z p)) (hstep : t.time = s.time + 8)
    (delay : ℝ → ℝ) (hdelay : ∀ time, 3 / 10 ≤ delay time ∧ delay time ≤ 2 / 5) :
    79 / 10 ≤ (d.final.time + delay d.final.time) - (c.final.time + delay c.final.time) ∧
      (d.final.time + delay d.final.time) - (c.final.time + delay c.final.time) ≤ 81 / 10 :=
  received_gap_eight_of_fire_gap (c.firing_gap_eight_of_rest_gain d hqS hqT hz hstep)
    (hdelay c.final.time) (hdelay d.final.time)

end KernelR.Hybrid
