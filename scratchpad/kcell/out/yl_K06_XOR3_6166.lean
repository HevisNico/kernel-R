import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.Kc_yl_K06_XOR3_6166

set_option maxRecDepth 100000

def c1_0_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 33242 else 33242, help := 0, threshold := 100000, trainError := 307, testError := 307, dose := 8345, maxWrites := 4, rail := 1000000 }
theorem c1_0_K0_t0 : Checker.cellValid c1_0_K0 = false := by decide +kernel
theorem c1_0_K0_t1 : c1_0_K0.stop (0 : Fin 2) = 3 := by decide +kernel
theorem c1_0_K0_t2 : decide (0 < c1_0_K0.dose) = true := by decide +kernel
theorem c1_0_K0_t3 : decide (0 < c1_0_K0.stop (0 : Fin 2) ∧ c1_0_K0.stop (0 : Fin 2) ≤ c1_0_K0.maxWrites) = true := by decide +kernel
theorem c1_0_K0_t4 : decide (c1_0_K0.groupScore (0 : Fin 2) 0 + c1_0_K0.trainError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t5 : decide (c1_0_K0.groupScore (0 : Fin 2) 1 + c1_0_K0.trainError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t6 : decide (c1_0_K0.groupScore (0 : Fin 2) 2 + c1_0_K0.trainError < c1_0_K0.threshold) = false := by decide +kernel
theorem c1_0_K0_t7 : decide (c1_0_K0.threshold + c1_0_K0.trainError ≤ c1_0_K0.groupScore (0 : Fin 2) (c1_0_K0.stop (0 : Fin 2))) = true := by decide +kernel
theorem c1_0_K0_t8 : decide (c1_0_K0.gain c1_0_K0.expectedWrites (0 : Fin 2) < c1_0_K0.rail) = true := by decide +kernel
theorem c1_0_K0_t9 : decide (c1_0_K0.gain c1_0_K0.expectedWrites (1 : Fin 2) < c1_0_K0.rail) = true := by decide +kernel
theorem c1_0_K0_t10 : decide (c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c1_0_K0.testError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t11 : decide (c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false) + c1_0_K0.testError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t12 : decide (c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_0_K0.testError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t13 : decide (c1_0_K0.threshold + c1_0_K0.testError ≤ c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else true)) = true := by decide +kernel
def c1_0_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 33242 else 33242, help := 0, threshold := 100000, trainError := 2828, testError := 2828, dose := 8345, maxWrites := 4, rail := 1000000 }
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

def c1_1_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 38170 else 38170, help := 0, threshold := 100000, trainError := 284, testError := 284, dose := 7728, maxWrites := 3, rail := 1000000 }
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
theorem c1_1_K0_t10 : decide (c1_1_K0.score c1_1_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false) + c1_1_K0.testError < c1_1_K0.threshold) = true := by decide +kernel
theorem c1_1_K0_t11 : decide (c1_1_K0.score c1_1_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_1_K0.testError < c1_1_K0.threshold) = true := by decide +kernel
theorem c1_1_K0_t12 : decide (c1_1_K0.threshold + c1_1_K0.testError ≤ c1_1_K0.score c1_1_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else true)) = true := by decide +kernel
def c1_1_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 38170 else 38170, help := 0, threshold := 100000, trainError := 2610, testError := 2610, dose := 7728, maxWrites := 3, rail := 1000000 }
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
theorem c1_1_K3_t10 : decide (c1_1_K3.score c1_1_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false) + c1_1_K3.testError < c1_1_K3.threshold) = true := by decide +kernel
theorem c1_1_K3_t11 : decide (c1_1_K3.score c1_1_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_1_K3.testError < c1_1_K3.threshold) = true := by decide +kernel
theorem c1_1_K3_t12 : decide (c1_1_K3.threshold + c1_1_K3.testError ≤ c1_1_K3.score c1_1_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else true)) = true := by decide +kernel

def c2_0_K0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 50615 else 49384, help := 0, threshold := 100000, trainError := 714, testError := 714, dose := 35802, maxWrites := 3, rail := 1000000 }
theorem c2_0_K0_t0 : Checker.cellValid c2_0_K0 = true := by decide +kernel
theorem c2_0_K0_t1 : c2_0_K0.stop (0 : Fin 2) = 2 := by decide +kernel
theorem c2_0_K0_t2 : c2_0_K0.stop (1 : Fin 2) = 2 := by decide +kernel
theorem c2_0_K0_t3 : decide (0 < c2_0_K0.dose) = true := by decide +kernel
theorem c2_0_K0_t4 : decide (0 < c2_0_K0.stop (0 : Fin 2) ∧ c2_0_K0.stop (0 : Fin 2) ≤ c2_0_K0.maxWrites) = true := by decide +kernel
theorem c2_0_K0_t5 : decide (c2_0_K0.groupScore (0 : Fin 2) 0 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t6 : decide (c2_0_K0.groupScore (0 : Fin 2) 1 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t7 : decide (c2_0_K0.threshold + c2_0_K0.trainError ≤ c2_0_K0.groupScore (0 : Fin 2) (c2_0_K0.stop (0 : Fin 2))) = true := by decide +kernel
theorem c2_0_K0_t8 : decide (0 < c2_0_K0.stop (1 : Fin 2) ∧ c2_0_K0.stop (1 : Fin 2) ≤ c2_0_K0.maxWrites) = true := by decide +kernel
theorem c2_0_K0_t9 : decide (c2_0_K0.groupScore (1 : Fin 2) 0 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t10 : decide (c2_0_K0.groupScore (1 : Fin 2) 1 + c2_0_K0.trainError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t11 : decide (c2_0_K0.threshold + c2_0_K0.trainError ≤ c2_0_K0.groupScore (1 : Fin 2) (c2_0_K0.stop (1 : Fin 2))) = true := by decide +kernel
theorem c2_0_K0_t12 : decide (c2_0_K0.gain c2_0_K0.expectedWrites (0 : Fin 2) < c2_0_K0.rail) = true := by decide +kernel
theorem c2_0_K0_t13 : decide (c2_0_K0.gain c2_0_K0.expectedWrites (1 : Fin 2) < c2_0_K0.rail) = true := by decide +kernel
theorem c2_0_K0_t14 : decide (c2_0_K0.score c2_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c2_0_K0.testError < c2_0_K0.threshold) = true := by decide +kernel
theorem c2_0_K0_t15 : decide (c2_0_K0.threshold + c2_0_K0.testError ≤ c2_0_K0.score c2_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel
theorem c2_0_K0_t16 : decide (c2_0_K0.threshold + c2_0_K0.testError ≤ c2_0_K0.score c2_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true)) = true := by decide +kernel
def c2_0_K3 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 50615 else 49384, help := 0, threshold := 100000, trainError := 6108, testError := 6108, dose := 35802, maxWrites := 3, rail := 1000000 }
theorem c2_0_K3_t0 : Checker.cellValid c2_0_K3 = true := by decide +kernel
theorem c2_0_K3_t1 : c2_0_K3.stop (0 : Fin 2) = 2 := by decide +kernel
theorem c2_0_K3_t2 : c2_0_K3.stop (1 : Fin 2) = 2 := by decide +kernel
theorem c2_0_K3_t3 : decide (0 < c2_0_K3.dose) = true := by decide +kernel
theorem c2_0_K3_t4 : decide (0 < c2_0_K3.stop (0 : Fin 2) ∧ c2_0_K3.stop (0 : Fin 2) ≤ c2_0_K3.maxWrites) = true := by decide +kernel
theorem c2_0_K3_t5 : decide (c2_0_K3.groupScore (0 : Fin 2) 0 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t6 : decide (c2_0_K3.groupScore (0 : Fin 2) 1 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t7 : decide (c2_0_K3.threshold + c2_0_K3.trainError ≤ c2_0_K3.groupScore (0 : Fin 2) (c2_0_K3.stop (0 : Fin 2))) = true := by decide +kernel
theorem c2_0_K3_t8 : decide (0 < c2_0_K3.stop (1 : Fin 2) ∧ c2_0_K3.stop (1 : Fin 2) ≤ c2_0_K3.maxWrites) = true := by decide +kernel
theorem c2_0_K3_t9 : decide (c2_0_K3.groupScore (1 : Fin 2) 0 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t10 : decide (c2_0_K3.groupScore (1 : Fin 2) 1 + c2_0_K3.trainError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t11 : decide (c2_0_K3.threshold + c2_0_K3.trainError ≤ c2_0_K3.groupScore (1 : Fin 2) (c2_0_K3.stop (1 : Fin 2))) = true := by decide +kernel
theorem c2_0_K3_t12 : decide (c2_0_K3.gain c2_0_K3.expectedWrites (0 : Fin 2) < c2_0_K3.rail) = true := by decide +kernel
theorem c2_0_K3_t13 : decide (c2_0_K3.gain c2_0_K3.expectedWrites (1 : Fin 2) < c2_0_K3.rail) = true := by decide +kernel
theorem c2_0_K3_t14 : decide (c2_0_K3.score c2_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c2_0_K3.testError < c2_0_K3.threshold) = true := by decide +kernel
theorem c2_0_K3_t15 : decide (c2_0_K3.threshold + c2_0_K3.testError ≤ c2_0_K3.score c2_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel
theorem c2_0_K3_t16 : decide (c2_0_K3.threshold + c2_0_K3.testError ≤ c2_0_K3.score c2_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true)) = true := by decide +kernel

def c3_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 90265 else 0, help := 0, threshold := 100000, trainError := 137, testError := 137, dose := 7467, maxWrites := 3, rail := 1000000 }
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
def c3_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 90265 else 0, help := 0, threshold := 100000, trainError := 1262, testError := 1262, dose := 7467, maxWrites := 3, rail := 1000000 }
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

end LearnedCoincidence.Layered.Kc_yl_K06_XOR3_6166
