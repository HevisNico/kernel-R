import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.Kc_yl_K10_ANDOR3_6131

set_option maxRecDepth 100000

def c1_0_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 31774 else 31774, help := 0, threshold := 100000, trainError := 314, testError := 314, dose := 8529, maxWrites := 4, rail := 1000000 }
theorem c1_0_K0_t0 : Checker.cellValid c1_0_K0 = true := by decide +kernel
theorem c1_0_K0_t1 : c1_0_K0.stop (0 : Fin 2) = 3 := by decide +kernel
theorem c1_0_K0_t2 : decide (0 < c1_0_K0.dose) = true := by decide +kernel
theorem c1_0_K0_t3 : decide (0 < c1_0_K0.stop (0 : Fin 2) ∧ c1_0_K0.stop (0 : Fin 2) ≤ c1_0_K0.maxWrites) = true := by decide +kernel
theorem c1_0_K0_t4 : decide (c1_0_K0.groupScore (0 : Fin 2) 0 + c1_0_K0.trainError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t5 : decide (c1_0_K0.groupScore (0 : Fin 2) 1 + c1_0_K0.trainError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t6 : decide (c1_0_K0.groupScore (0 : Fin 2) 2 + c1_0_K0.trainError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t7 : decide (c1_0_K0.threshold + c1_0_K0.trainError ≤ c1_0_K0.groupScore (0 : Fin 2) (c1_0_K0.stop (0 : Fin 2))) = true := by decide +kernel
theorem c1_0_K0_t8 : decide (c1_0_K0.gain c1_0_K0.expectedWrites (0 : Fin 2) < c1_0_K0.rail) = true := by decide +kernel
theorem c1_0_K0_t9 : decide (c1_0_K0.gain c1_0_K0.expectedWrites (1 : Fin 2) < c1_0_K0.rail) = true := by decide +kernel
theorem c1_0_K0_t10 : decide (c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c1_0_K0.testError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t11 : decide (c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false) + c1_0_K0.testError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t12 : decide (c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_0_K0.testError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t13 : decide (c1_0_K0.threshold + c1_0_K0.testError ≤ c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else true)) = true := by decide +kernel
def c1_0_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 31774 else 31774, help := 0, threshold := 100000, trainError := 2895, testError := 2895, dose := 8529, maxWrites := 4, rail := 1000000 }
theorem c1_0_K3_t0 : Checker.cellValid c1_0_K3 = false := by decide +kernel
theorem c1_0_K3_t1 : c1_0_K3.stop (0 : Fin 2) = 3 := by decide +kernel
theorem c1_0_K3_t2 : decide (0 < c1_0_K3.dose) = true := by decide +kernel
theorem c1_0_K3_t3 : decide (0 < c1_0_K3.stop (0 : Fin 2) ∧ c1_0_K3.stop (0 : Fin 2) ≤ c1_0_K3.maxWrites) = true := by decide +kernel
theorem c1_0_K3_t4 : decide (c1_0_K3.groupScore (0 : Fin 2) 0 + c1_0_K3.trainError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t5 : decide (c1_0_K3.groupScore (0 : Fin 2) 1 + c1_0_K3.trainError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t6 : decide (c1_0_K3.groupScore (0 : Fin 2) 2 + c1_0_K3.trainError < c1_0_K3.threshold) = false := by decide +kernel
theorem c1_0_K3_t7 : decide (c1_0_K3.threshold + c1_0_K3.trainError ≤ c1_0_K3.groupScore (0 : Fin 2) (c1_0_K3.stop (0 : Fin 2))) = true := by decide +kernel
theorem c1_0_K3_t8 : decide (c1_0_K3.gain c1_0_K3.expectedWrites (0 : Fin 2) < c1_0_K3.rail) = true := by decide +kernel
theorem c1_0_K3_t9 : decide (c1_0_K3.gain c1_0_K3.expectedWrites (1 : Fin 2) < c1_0_K3.rail) = true := by decide +kernel
theorem c1_0_K3_t10 : decide (c1_0_K3.score c1_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c1_0_K3.testError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t11 : decide (c1_0_K3.score c1_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false) + c1_0_K3.testError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t12 : decide (c1_0_K3.score c1_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_0_K3.testError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t13 : decide (c1_0_K3.threshold + c1_0_K3.testError ≤ c1_0_K3.score c1_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else true)) = true := by decide +kernel

def c1_1_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 89790 else 0, help := 0, threshold := 100000, trainError := 137, testError := 137, dose := 7526, maxWrites := 3, rail := 1000000 }
theorem c1_1_K0_t0 : Checker.cellValid c1_1_K0 = true := by decide +kernel
theorem c1_1_K0_t1 : c1_1_K0.stop (0 : Fin 2) = 2 := by decide +kernel
theorem c1_1_K0_t2 : decide (0 < c1_1_K0.dose) = true := by decide +kernel
theorem c1_1_K0_t3 : decide (0 < c1_1_K0.stop (0 : Fin 2) ∧ c1_1_K0.stop (0 : Fin 2) ≤ c1_1_K0.maxWrites) = true := by decide +kernel
theorem c1_1_K0_t4 : decide (c1_1_K0.groupScore (0 : Fin 2) 0 + c1_1_K0.trainError < c1_1_K0.threshold) = true := by decide +kernel
theorem c1_1_K0_t5 : decide (c1_1_K0.groupScore (0 : Fin 2) 1 + c1_1_K0.trainError < c1_1_K0.threshold) = true := by decide +kernel
theorem c1_1_K0_t6 : decide (c1_1_K0.threshold + c1_1_K0.trainError ≤ c1_1_K0.groupScore (0 : Fin 2) (c1_1_K0.stop (0 : Fin 2))) = true := by decide +kernel
theorem c1_1_K0_t7 : decide (c1_1_K0.gain c1_1_K0.expectedWrites (0 : Fin 2) < c1_1_K0.rail) = true := by decide +kernel
theorem c1_1_K0_t8 : decide (c1_1_K0.gain c1_1_K0.expectedWrites (1 : Fin 2) < c1_1_K0.rail) = true := by decide +kernel
theorem c1_1_K0_t9 : decide (c1_1_K0.score c1_1_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c1_1_K0.testError < c1_1_K0.threshold) = true := by decide +kernel
theorem c1_1_K0_t10 : decide (c1_1_K0.score c1_1_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_1_K0.testError < c1_1_K0.threshold) = true := by decide +kernel
theorem c1_1_K0_t11 : decide (c1_1_K0.threshold + c1_1_K0.testError ≤ c1_1_K0.score c1_1_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel
def c1_1_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 89790 else 0, help := 0, threshold := 100000, trainError := 1273, testError := 1273, dose := 7526, maxWrites := 3, rail := 1000000 }
theorem c1_1_K3_t0 : Checker.cellValid c1_1_K3 = true := by decide +kernel
theorem c1_1_K3_t1 : c1_1_K3.stop (0 : Fin 2) = 2 := by decide +kernel
theorem c1_1_K3_t2 : decide (0 < c1_1_K3.dose) = true := by decide +kernel
theorem c1_1_K3_t3 : decide (0 < c1_1_K3.stop (0 : Fin 2) ∧ c1_1_K3.stop (0 : Fin 2) ≤ c1_1_K3.maxWrites) = true := by decide +kernel
theorem c1_1_K3_t4 : decide (c1_1_K3.groupScore (0 : Fin 2) 0 + c1_1_K3.trainError < c1_1_K3.threshold) = true := by decide +kernel
theorem c1_1_K3_t5 : decide (c1_1_K3.groupScore (0 : Fin 2) 1 + c1_1_K3.trainError < c1_1_K3.threshold) = true := by decide +kernel
theorem c1_1_K3_t6 : decide (c1_1_K3.threshold + c1_1_K3.trainError ≤ c1_1_K3.groupScore (0 : Fin 2) (c1_1_K3.stop (0 : Fin 2))) = true := by decide +kernel
theorem c1_1_K3_t7 : decide (c1_1_K3.gain c1_1_K3.expectedWrites (0 : Fin 2) < c1_1_K3.rail) = true := by decide +kernel
theorem c1_1_K3_t8 : decide (c1_1_K3.gain c1_1_K3.expectedWrites (1 : Fin 2) < c1_1_K3.rail) = true := by decide +kernel
theorem c1_1_K3_t9 : decide (c1_1_K3.score c1_1_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c1_1_K3.testError < c1_1_K3.threshold) = true := by decide +kernel
theorem c1_1_K3_t10 : decide (c1_1_K3.score c1_1_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_1_K3.testError < c1_1_K3.threshold) = true := by decide +kernel
theorem c1_1_K3_t11 : decide (c1_1_K3.threshold + c1_1_K3.testError ≤ c1_1_K3.score c1_1_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel

def c2_0_K0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 44185 else 55813, help := 0, threshold := 100000, trainError := 443, testError := 443, dose := 24224, maxWrites := 3, rail := 1000000 }
theorem c2_0_K0_t0 : Checker.cellValid c2_0_K0 = true := by decide +kernel
theorem c2_0_K0_t1 : c2_0_K0.stop (0 : Fin 2) = 3 := by decide +kernel
theorem c2_0_K0_t2 : c2_0_K0.stop (1 : Fin 2) = 2 := by decide +kernel
theorem c2_0_K0_t3 : decide (0 < c2_0_K0.dose) = true := by decide +kernel
theorem c2_0_K0_t4 : decide (0 < c2_0_K0.stop (0 : Fin 2) ∧ c2_0_K0.stop (0 : Fin 2) ≤ c2_0_K0.maxWrites) = true := by decide +kernel
theorem c2_0_K0_t5 : decide (c2_0_K0.groupScore (0 : Fin 2) 0 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t6 : decide (c2_0_K0.groupScore (0 : Fin 2) 1 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t7 : decide (c2_0_K0.groupScore (0 : Fin 2) 2 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t8 : decide (c2_0_K0.threshold + c2_0_K0.trainError ≤ c2_0_K0.groupScore (0 : Fin 2) (c2_0_K0.stop (0 : Fin 2))) = true := by decide +kernel
theorem c2_0_K0_t9 : decide (0 < c2_0_K0.stop (1 : Fin 2) ∧ c2_0_K0.stop (1 : Fin 2) ≤ c2_0_K0.maxWrites) = true := by decide +kernel
theorem c2_0_K0_t10 : decide (c2_0_K0.groupScore (1 : Fin 2) 0 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t11 : decide (c2_0_K0.groupScore (1 : Fin 2) 1 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t12 : decide (c2_0_K0.threshold + c2_0_K0.trainError ≤ c2_0_K0.groupScore (1 : Fin 2) (c2_0_K0.stop (1 : Fin 2))) = true := by decide +kernel
theorem c2_0_K0_t13 : decide (c2_0_K0.gain c2_0_K0.expectedWrites (0 : Fin 2) < c2_0_K0.rail) = true := by decide +kernel
theorem c2_0_K0_t14 : decide (c2_0_K0.gain c2_0_K0.expectedWrites (1 : Fin 2) < c2_0_K0.rail) = true := by decide +kernel
theorem c2_0_K0_t15 : decide (c2_0_K0.score c2_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c2_0_K0.testError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t16 : decide (c2_0_K0.threshold + c2_0_K0.testError ≤ c2_0_K0.score c2_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel
theorem c2_0_K0_t17 : decide (c2_0_K0.threshold + c2_0_K0.testError ≤ c2_0_K0.score c2_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true)) = true := by decide +kernel
def c2_0_K3 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 44185 else 55813, help := 0, threshold := 100000, trainError := 4115, testError := 4115, dose := 24224, maxWrites := 3, rail := 1000000 }
theorem c2_0_K3_t0 : Checker.cellValid c2_0_K3 = true := by decide +kernel
theorem c2_0_K3_t1 : c2_0_K3.stop (0 : Fin 2) = 3 := by decide +kernel
theorem c2_0_K3_t2 : c2_0_K3.stop (1 : Fin 2) = 2 := by decide +kernel
theorem c2_0_K3_t3 : decide (0 < c2_0_K3.dose) = true := by decide +kernel
theorem c2_0_K3_t4 : decide (0 < c2_0_K3.stop (0 : Fin 2) ∧ c2_0_K3.stop (0 : Fin 2) ≤ c2_0_K3.maxWrites) = true := by decide +kernel
theorem c2_0_K3_t5 : decide (c2_0_K3.groupScore (0 : Fin 2) 0 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t6 : decide (c2_0_K3.groupScore (0 : Fin 2) 1 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t7 : decide (c2_0_K3.groupScore (0 : Fin 2) 2 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t8 : decide (c2_0_K3.threshold + c2_0_K3.trainError ≤ c2_0_K3.groupScore (0 : Fin 2) (c2_0_K3.stop (0 : Fin 2))) = true := by decide +kernel
theorem c2_0_K3_t9 : decide (0 < c2_0_K3.stop (1 : Fin 2) ∧ c2_0_K3.stop (1 : Fin 2) ≤ c2_0_K3.maxWrites) = true := by decide +kernel
theorem c2_0_K3_t10 : decide (c2_0_K3.groupScore (1 : Fin 2) 0 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t11 : decide (c2_0_K3.groupScore (1 : Fin 2) 1 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t12 : decide (c2_0_K3.threshold + c2_0_K3.trainError ≤ c2_0_K3.groupScore (1 : Fin 2) (c2_0_K3.stop (1 : Fin 2))) = true := by decide +kernel
theorem c2_0_K3_t13 : decide (c2_0_K3.gain c2_0_K3.expectedWrites (0 : Fin 2) < c2_0_K3.rail) = true := by decide +kernel
theorem c2_0_K3_t14 : decide (c2_0_K3.gain c2_0_K3.expectedWrites (1 : Fin 2) < c2_0_K3.rail) = true := by decide +kernel
theorem c2_0_K3_t15 : decide (c2_0_K3.score c2_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c2_0_K3.testError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t16 : decide (c2_0_K3.threshold + c2_0_K3.testError ≤ c2_0_K3.score c2_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel
theorem c2_0_K3_t17 : decide (c2_0_K3.threshold + c2_0_K3.testError ≤ c2_0_K3.score c2_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true)) = true := by decide +kernel

def c3_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 87055 else 0, help := 0, threshold := 100000, trainError := 145, testError := 145, dose := 7868, maxWrites := 3, rail := 1000000 }
theorem c3_0_K0_t0 : Checker.cellValid c3_0_K0 = true := by decide +kernel
theorem c3_0_K0_t1 : c3_0_K0.stop (0 : Fin 2) = 2 := by decide +kernel
theorem c3_0_K0_t2 : decide (0 < c3_0_K0.dose) = true := by decide +kernel
theorem c3_0_K0_t3 : decide (0 < c3_0_K0.stop (0 : Fin 2) ∧ c3_0_K0.stop (0 : Fin 2) ≤ c3_0_K0.maxWrites) = true := by decide +kernel
theorem c3_0_K0_t4 : decide (c3_0_K0.groupScore (0 : Fin 2) 0 + c3_0_K0.trainError < c3_0_K0.threshold) = true := by decide +kernel
theorem c3_0_K0_t5 : decide (c3_0_K0.groupScore (0 : Fin 2) 1 + c3_0_K0.trainError < c3_0_K0.threshold) = true := by decide +kernel
theorem c3_0_K0_t6 : decide (c3_0_K0.threshold + c3_0_K0.trainError ≤ c3_0_K0.groupScore (0 : Fin 2) (c3_0_K0.stop (0 : Fin 2))) = true := by decide +kernel
theorem c3_0_K0_t7 : decide (c3_0_K0.gain c3_0_K0.expectedWrites (0 : Fin 2) < c3_0_K0.rail) = true := by decide +kernel
theorem c3_0_K0_t8 : decide (c3_0_K0.gain c3_0_K0.expectedWrites (1 : Fin 2) < c3_0_K0.rail) = true := by decide +kernel
theorem c3_0_K0_t9 : decide (c3_0_K0.score c3_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c3_0_K0.testError < c3_0_K0.threshold) = true := by decide +kernel
theorem c3_0_K0_t10 : decide (c3_0_K0.score c3_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c3_0_K0.testError < c3_0_K0.threshold) = true := by decide +kernel
theorem c3_0_K0_t11 : decide (c3_0_K0.threshold + c3_0_K0.testError ≤ c3_0_K0.score c3_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel
def c3_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 87055 else 0, help := 0, threshold := 100000, trainError := 1327, testError := 1327, dose := 7868, maxWrites := 3, rail := 1000000 }
theorem c3_0_K3_t0 : Checker.cellValid c3_0_K3 = true := by decide +kernel
theorem c3_0_K3_t1 : c3_0_K3.stop (0 : Fin 2) = 2 := by decide +kernel
theorem c3_0_K3_t2 : decide (0 < c3_0_K3.dose) = true := by decide +kernel
theorem c3_0_K3_t3 : decide (0 < c3_0_K3.stop (0 : Fin 2) ∧ c3_0_K3.stop (0 : Fin 2) ≤ c3_0_K3.maxWrites) = true := by decide +kernel
theorem c3_0_K3_t4 : decide (c3_0_K3.groupScore (0 : Fin 2) 0 + c3_0_K3.trainError < c3_0_K3.threshold) = true := by decide +kernel
theorem c3_0_K3_t5 : decide (c3_0_K3.groupScore (0 : Fin 2) 1 + c3_0_K3.trainError < c3_0_K3.threshold) = true := by decide +kernel
theorem c3_0_K3_t6 : decide (c3_0_K3.threshold + c3_0_K3.trainError ≤ c3_0_K3.groupScore (0 : Fin 2) (c3_0_K3.stop (0 : Fin 2))) = true := by decide +kernel
theorem c3_0_K3_t7 : decide (c3_0_K3.gain c3_0_K3.expectedWrites (0 : Fin 2) < c3_0_K3.rail) = true := by decide +kernel
theorem c3_0_K3_t8 : decide (c3_0_K3.gain c3_0_K3.expectedWrites (1 : Fin 2) < c3_0_K3.rail) = true := by decide +kernel
theorem c3_0_K3_t9 : decide (c3_0_K3.score c3_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c3_0_K3.testError < c3_0_K3.threshold) = true := by decide +kernel
theorem c3_0_K3_t10 : decide (c3_0_K3.score c3_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c3_0_K3.testError < c3_0_K3.threshold) = true := by decide +kernel
theorem c3_0_K3_t11 : decide (c3_0_K3.threshold + c3_0_K3.testError ≤ c3_0_K3.score c3_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel

end LearnedCoincidence.Layered.Kc_yl_K10_ANDOR3_6131
