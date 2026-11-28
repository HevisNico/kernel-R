import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.FitXOR3

set_option maxRecDepth 100000

def c1_0_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 36365 else 36365, help := 0, threshold := 100000, trainError := 289, testError := 289, dose := 7954, maxWrites := 3, rail := 1000000 }
theorem c1_0_K0_valid : Checker.cellValid c1_0_K0 = true := by decide +kernel
theorem c1_0_K0_stop0 : c1_0_K0.stop 0 = 2 := by decide +kernel
def c1_0_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 36365 else 36365, help := 0, threshold := 100000, trainError := 2682, testError := 2682, dose := 7954, maxWrites := 3, rail := 1000000 }
theorem c1_0_K3_valid : Checker.cellValid c1_0_K3 = true := by decide +kernel
theorem c1_0_K3_stop0 : c1_0_K3.stop 0 = 2 := by decide +kernel

def c1_1_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 41147 else 41147, help := 0, threshold := 100000, trainError := 268, testError := 268, dose := 7356, maxWrites := 3, rail := 1000000 }
theorem c1_1_K0_valid : Checker.cellValid c1_1_K0 = true := by decide +kernel
theorem c1_1_K0_stop0 : c1_1_K0.stop 0 = 2 := by decide +kernel
def c1_1_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 41147 else 41147, help := 0, threshold := 100000, trainError := 2485, testError := 2485, dose := 7356, maxWrites := 3, rail := 1000000 }
theorem c1_1_K3_valid : Checker.cellValid c1_1_K3 = true := by decide +kernel
theorem c1_1_K3_stop0 : c1_1_K3.stop 0 = 2 := by decide +kernel

def c2_0_K0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 52570 else 47427, help := 0, threshold := 100000, trainError := 396, testError := 613, dose := 19586, maxWrites := 4, rail := 1000000 }
theorem c2_0_K0_valid : Checker.cellValid c2_0_K0 = true := by decide +kernel
theorem c2_0_K0_stop0 : c2_0_K0.stop 0 = 3 := by decide +kernel
theorem c2_0_K0_stop1 : c2_0_K0.stop 1 = 3 := by decide +kernel
def c2_0_K3 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 52570 else 47427, help := 0, threshold := 100000, trainError := 3371, testError := 6550, dose := 19586, maxWrites := 4, rail := 1000000 }
theorem c2_0_K3_valid : Checker.cellValid c2_0_K3 = false := by decide +kernel
theorem c2_0_K3_stop0 : c2_0_K3.stop 0 = 3 := by decide +kernel
theorem c2_0_K3_stop1 : c2_0_K3.stop 1 = 3 := by decide +kernel

def c3_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 79825 else 0, help := 0, threshold := 100000, trainError := 160, testError := 160, dose := 8772, maxWrites := 4, rail := 1000000 }
theorem c3_0_K0_valid : Checker.cellValid c3_0_K0 = true := by decide +kernel
theorem c3_0_K0_stop0 : c3_0_K0.stop 0 = 3 := by decide +kernel
def c3_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 79825 else 0, help := 0, threshold := 100000, trainError := 1487, testError := 1487, dose := 8772, maxWrites := 4, rail := 1000000 }
theorem c3_0_K3_valid : Checker.cellValid c3_0_K3 = true := by decide +kernel
theorem c3_0_K3_stop0 : c3_0_K3.stop 0 = 3 := by decide +kernel

end LearnedCoincidence.Layered.FitXOR3
