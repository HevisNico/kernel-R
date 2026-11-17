import Diag5

/-! Campaign 4: the targets of amendment 2, section 3, written by cases.py. Each checker is
decided separately on every case and budget; the asserted value is the Python mirror's. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4

open TwoLayer (SlotTiming ReadObservation)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102338_K0 : checkCascadeValid cascade_Z102338_K0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102338_K0 : checkTrainingSeparation cascade_Z102338_K0 left right trace_Z102338_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102338_K0 : checkCascadeCalibrationOneSided cascade_Z102338_K0 left right trace_Z102338_K0.observations trace_Z102338_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102338_K3 : checkCascadeValid cascade_Z102338_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102338_K3 : checkTrainingSeparation cascade_Z102338_K3 left right trace_Z102338_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102338_K3 : checkCascadeCalibrationOneSided cascade_Z102338_K3 left right trace_Z102338_K3.observations trace_Z102338_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102339_K0 : checkCascadeValid cascade_Z102339_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102339_K0 : checkTrainingSeparation cascade_Z102339_K0 left right trace_Z102339_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102339_K0 : checkCascadeCalibrationOneSided cascade_Z102339_K0 left right trace_Z102339_K0.observations trace_Z102339_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102339_K3 : checkCascadeValid cascade_Z102339_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102339_K3 : checkTrainingSeparation cascade_Z102339_K3 left right trace_Z102339_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102339_K3 : checkCascadeCalibrationOneSided cascade_Z102339_K3 left right trace_Z102339_K3.observations trace_Z102339_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102340_K0 : checkCascadeValid cascade_Z102340_K0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102340_K0 : checkTrainingSeparation cascade_Z102340_K0 left right trace_Z102340_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102340_K0 : checkCascadeCalibrationOneSided cascade_Z102340_K0 left right trace_Z102340_K0.observations trace_Z102340_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102340_K3 : checkCascadeValid cascade_Z102340_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102340_K3 : checkTrainingSeparation cascade_Z102340_K3 left right trace_Z102340_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102340_K3 : checkCascadeCalibrationOneSided cascade_Z102340_K3 left right trace_Z102340_K3.observations trace_Z102340_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102341_K0 : checkCascadeValid cascade_Z102341_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102341_K0 : checkTrainingSeparation cascade_Z102341_K0 left right trace_Z102341_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102341_K0 : checkCascadeCalibrationOneSided cascade_Z102341_K0 left right trace_Z102341_K0.observations trace_Z102341_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102341_K3 : checkCascadeValid cascade_Z102341_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102341_K3 : checkTrainingSeparation cascade_Z102341_K3 left right trace_Z102341_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102341_K3 : checkCascadeCalibrationOneSided cascade_Z102341_K3 left right trace_Z102341_K3.observations trace_Z102341_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102342_K0 : checkCascadeValid cascade_Z102342_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102342_K0 : checkTrainingSeparation cascade_Z102342_K0 left right trace_Z102342_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102342_K0 : checkCascadeCalibrationOneSided cascade_Z102342_K0 left right trace_Z102342_K0.observations trace_Z102342_K0.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Z102342_K3 : checkCascadeValid cascade_Z102342_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Z102342_K3 : checkTrainingSeparation cascade_Z102342_K3 left right trace_Z102342_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Z102342_K3 : checkCascadeCalibrationOneSided cascade_Z102342_K3 left right trace_Z102342_K3.observations trace_Z102342_K3.scoreAt = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in


end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4
