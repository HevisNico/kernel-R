import Gate4Cases

/-! Campaign 4: the targets of amendment 2, section 3, written by cases.py. Each checker is
decided separately on every case and budget; the asserted value is the Python mirror's. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4

open TwoLayer (SlotTiming ReadObservation)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P0_K0 : checkCascadeValid cascade_P0_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P0_K0 : checkTrainingSeparation cascade_P0_K0 left right trace_P0_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P0_K0 : checkCascadeCalibrationOneSided cascade_P0_K0 left right trace_P0_K0.observations trace_P0_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P0_K3 : checkCascadeValid cascade_P0_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P0_K3 : checkTrainingSeparation cascade_P0_K3 left right trace_P0_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P0_K3 : checkCascadeCalibrationOneSided cascade_P0_K3 left right trace_P0_K3.observations trace_P0_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P1_K0 : checkCascadeValid cascade_P1_K0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P1_K0 : checkTrainingSeparation cascade_P1_K0 left right trace_P1_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P1_K0 : checkCascadeCalibrationOneSided cascade_P1_K0 left right trace_P1_K0.observations trace_P1_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P1_K3 : checkCascadeValid cascade_P1_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P1_K3 : checkTrainingSeparation cascade_P1_K3 left right trace_P1_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P1_K3 : checkCascadeCalibrationOneSided cascade_P1_K3 left right trace_P1_K3.observations trace_P1_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P2_K0 : checkCascadeValid cascade_P2_K0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P2_K0 : checkTrainingSeparation cascade_P2_K0 left right trace_P2_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P2_K0 : checkCascadeCalibrationOneSided cascade_P2_K0 left right trace_P2_K0.observations trace_P2_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P2_K3 : checkCascadeValid cascade_P2_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P2_K3 : checkTrainingSeparation cascade_P2_K3 left right trace_P2_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P2_K3 : checkCascadeCalibrationOneSided cascade_P2_K3 left right trace_P2_K3.observations trace_P2_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P3_K0 : checkCascadeValid cascade_P3_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P3_K0 : checkTrainingSeparation cascade_P3_K0 left right trace_P3_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P3_K0 : checkCascadeCalibrationOneSided cascade_P3_K0 left right trace_P3_K0.observations trace_P3_K0.scoreAt = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P3_K3 : checkCascadeValid cascade_P3_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P3_K3 : checkTrainingSeparation cascade_P3_K3 left right trace_P3_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P3_K3 : checkCascadeCalibrationOneSided cascade_P3_K3 left right trace_P3_K3.observations trace_P3_K3.scoreAt = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P4_K0 : checkCascadeValid cascade_P4_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P4_K0 : checkTrainingSeparation cascade_P4_K0 left right trace_P4_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P4_K0 : checkCascadeCalibrationOneSided cascade_P4_K0 left right trace_P4_K0.observations trace_P4_K0.scoreAt = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P4_K3 : checkCascadeValid cascade_P4_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P4_K3 : checkTrainingSeparation cascade_P4_K3 left right trace_P4_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P4_K3 : checkCascadeCalibrationOneSided cascade_P4_K3 left right trace_P4_K3.observations trace_P4_K3.scoreAt = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P4p_K0 : checkCascadeValid cascade_P4p_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P4p_K0 : checkTrainingSeparation cascade_P4p_K0 left right trace_P4p_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P4p_K0 : checkCascadeCalibrationOneSided cascade_P4p_K0 left right trace_P4p_K0.observations trace_P4p_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P4p_K3 : checkCascadeValid cascade_P4p_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P4p_K3 : checkTrainingSeparation cascade_P4p_K3 left right trace_P4p_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P4p_K3 : checkCascadeCalibrationOneSided cascade_P4p_K3 left right trace_P4p_K3.observations trace_P4p_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P5_K0 : checkCascadeValid cascade_P5_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P5_K0 : checkTrainingSeparation cascade_P5_K0 left right trace_P5_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P5_K0 : checkCascadeCalibrationOneSided cascade_P5_K0 left right trace_P5_K0.observations trace_P5_K0.scoreAt = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P5_K3 : checkCascadeValid cascade_P5_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P5_K3 : checkTrainingSeparation cascade_P5_K3 left right trace_P5_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P5_K3 : checkCascadeCalibrationOneSided cascade_P5_K3 left right trace_P5_K3.observations trace_P5_K3.scoreAt = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P6_K0 : checkCascadeValid cascade_P6_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P6_K0 : checkTrainingSeparation cascade_P6_K0 left right trace_P6_K0.observations = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P6_K0 : checkCascadeCalibrationOneSided cascade_P6_K0 left right trace_P6_K0.observations trace_P6_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_P6_K3 : checkCascadeValid cascade_P6_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_P6_K3 : checkTrainingSeparation cascade_P6_K3 left right trace_P6_K3.observations = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_P6_K3 : checkCascadeCalibrationOneSided cascade_P6_K3 left right trace_P6_K3.observations trace_P6_K3.scoreAt = true := by decide +kernel

/-! P4 (amendment 2, section 3): c's test read on ABCD. -/

theorem p4_emission : (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).emissions = [(79443 / 100 : Rat)] := by decide +kernel

theorem p4_arrival_b : (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).arrival 1 = some (19862 / 25 : Rat) := by decide +kernel

/-- `∀ j v, arrival j = some v → v ≤ t` is false: line b's arrival is after the emission. -/
theorem p4_not_all_arrivals_before : ¬ ∀ j v, (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).arrival j = some v → v ≤ (79443 / 100 : Rat) :=
  fun h => absurd (h 1 _ p4_arrival_b) (by decide +kernel)

/-- The same condition as a check over the two lines. -/
theorem p4_arrivals_before_check : (List.finRange 2).all (fun j => ((trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).arrival j).all fun v => decide (v ≤ (79443 / 100 : Rat))) = false := by decide +kernel

theorem p4_emission_window : (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).start ≤ (79443 / 100 : Rat) ∧ (79443 / 100 : Rat) ≤ (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).start + right.deadline := by decide +kernel

theorem p4_arrivals_in_skew_check : (List.finRange 2).all (fun j => ((trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).arrival j).all fun v => decide ((trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).start ≤ v ∧ v ≤ (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).start + right.skew)) = true := by decide +kernel

/-- Every arrival lies in `[s, s + skew]`. -/
theorem p4_arrivals_in_skew : ∀ j v, (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).arrival j = some v → (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).start ≤ v ∧ v ≤ (trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0).start + right.skew := by
  intro j v h
  have all := p4_arrivals_in_skew_check
  rw [List.all_eq_true] at all
  have hj := all j (List.mem_finRange j)
  rw [h] at hj
  simpa using hj

end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4
