import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.Kc_d4check_out_K01_NOT1_6220

set_option maxRecDepth 100000

def c1_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 87544 else 0, help := 0, threshold := 100000, trainError := 134, testError := 134, dose := 7807, maxWrites := 3, rail := 1000000 }
theorem c1_0_K0_t0 : Checker.cellValid c1_0_K0 = true := by decide +kernel
theorem c1_0_K0_t1 : c1_0_K0.stop (0 : Fin 2) = 2 := by decide +kernel
theorem c1_0_K0_t2 : decide (0 < c1_0_K0.dose) = true := by decide +kernel
theorem c1_0_K0_t3 : decide (0 < c1_0_K0.stop (0 : Fin 2) ∧ c1_0_K0.stop (0 : Fin 2) ≤ c1_0_K0.maxWrites) = true := by decide +kernel
theorem c1_0_K0_t4 : decide (c1_0_K0.groupScore (0 : Fin 2) 0 + c1_0_K0.trainError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t5 : decide (c1_0_K0.groupScore (0 : Fin 2) 1 + c1_0_K0.trainError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t6 : decide (c1_0_K0.threshold + c1_0_K0.trainError ≤ c1_0_K0.groupScore (0 : Fin 2) (c1_0_K0.stop (0 : Fin 2))) = true := by decide +kernel
theorem c1_0_K0_t7 : decide (c1_0_K0.gain c1_0_K0.expectedWrites (0 : Fin 2) < c1_0_K0.rail) = true := by decide +kernel
theorem c1_0_K0_t8 : decide (c1_0_K0.gain c1_0_K0.expectedWrites (1 : Fin 2) < c1_0_K0.rail) = true := by decide +kernel
theorem c1_0_K0_t9 : decide (c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c1_0_K0.testError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t10 : decide (c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_0_K0.testError < c1_0_K0.threshold) = true := by decide +kernel
theorem c1_0_K0_t11 : decide (c1_0_K0.threshold + c1_0_K0.testError ≤ c1_0_K0.score c1_0_K0.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel
def c1_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 87544 else 0, help := 0, threshold := 100000, trainError := 1309, testError := 1309, dose := 7807, maxWrites := 3, rail := 1000000 }
theorem c1_0_K3_t0 : Checker.cellValid c1_0_K3 = true := by decide +kernel
theorem c1_0_K3_t1 : c1_0_K3.stop (0 : Fin 2) = 2 := by decide +kernel
theorem c1_0_K3_t2 : decide (0 < c1_0_K3.dose) = true := by decide +kernel
theorem c1_0_K3_t3 : decide (0 < c1_0_K3.stop (0 : Fin 2) ∧ c1_0_K3.stop (0 : Fin 2) ≤ c1_0_K3.maxWrites) = true := by decide +kernel
theorem c1_0_K3_t4 : decide (c1_0_K3.groupScore (0 : Fin 2) 0 + c1_0_K3.trainError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t5 : decide (c1_0_K3.groupScore (0 : Fin 2) 1 + c1_0_K3.trainError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t6 : decide (c1_0_K3.threshold + c1_0_K3.trainError ≤ c1_0_K3.groupScore (0 : Fin 2) (c1_0_K3.stop (0 : Fin 2))) = true := by decide +kernel
theorem c1_0_K3_t7 : decide (c1_0_K3.gain c1_0_K3.expectedWrites (0 : Fin 2) < c1_0_K3.rail) = true := by decide +kernel
theorem c1_0_K3_t8 : decide (c1_0_K3.gain c1_0_K3.expectedWrites (1 : Fin 2) < c1_0_K3.rail) = true := by decide +kernel
theorem c1_0_K3_t9 : decide (c1_0_K3.score c1_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else false) + c1_0_K3.testError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t10 : decide (c1_0_K3.score c1_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then false else true) + c1_0_K3.testError < c1_0_K3.threshold) = true := by decide +kernel
theorem c1_0_K3_t11 : decide (c1_0_K3.threshold + c1_0_K3.testError ≤ c1_0_K3.score c1_0_K3.expectedWrites (fun a : Fin 2 => if a.val = 0 then true else false)) = true := by decide +kernel

end LearnedCoincidence.Layered.Kc_d4check_out_K01_NOT1_6220
