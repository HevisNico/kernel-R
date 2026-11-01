import KernelR.HybridPulseBounds
/-! Own birth gains bound the initial main response for every physical port. -/
namespace KernelR.Hybrid

theorem BirthState.nominal_pulse_gain_upper {n s} (hs : @BirthState n s)
    (i : Fin n) (p : Port) : Real.exp (s.x i (.z p)) ≤ 4 / 3 := by
  have hnom : 0 < nominalGain p ∧ nominalGain p ≤ 6 / 5 := by
    unfold nominalGain
    split_ifs <;> norm_num
  have hlog := Real.log_le_log hnom.1 hnom.2
  have hz := ((hs.2.2 i).2.2.2.2 p).1.2
  apply fast_nominal_raw_gain_upper
  linarith

/-- Every birth charge is strictly inside the READY guard. This bounds the
explicit main response at the first input without an observed execution. -/
theorem BirthState.nominal_pulse_main_guard {n s} (hs : @BirthState n s)
    (i : Fin n) (p : Port) {origin t : ℝ} (ht : origin ≤ t) :
    readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) origin t < 1 := by
  exact readyPulse_nominal_silent (by linarith [(hs.2.2 i).2.1.2])
    (hs.nominal_pulse_gain_upper i p) ht

end KernelR.Hybrid
