import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.FitANDOR3

set_option maxRecDepth 100000

def c1_0_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 33358 else 33358, help := 0, threshold := 100000, trainError := 303, testError := 303, dose := 8330, maxWrites := 3, rail := 1000000 }
theorem c1_0_K0_valid : Checker.cellValid c1_0_K0 = false := by decide +kernel
theorem c1_0_K0_stop0 : c1_0_K0.stop 0 = 2 := by decide +kernel
def c1_0_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 33358 else 33358, help := 0, threshold := 100000, trainError := 2819, testError := 2819, dose := 8330, maxWrites := 3, rail := 1000000 }
theorem c1_0_K3_valid : Checker.cellValid c1_0_K3 = false := by decide +kernel
theorem c1_0_K3_stop0 : c1_0_K3.stop 0 = 2 := by decide +kernel

def c1_1_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 88605 else 0, help := 0, threshold := 100000, trainError := 142, testError := 142, dose := 7674, maxWrites := 3, rail := 1000000 }
theorem c1_1_K0_valid : Checker.cellValid c1_1_K0 = true := by decide +kernel
theorem c1_1_K0_stop0 : c1_1_K0.stop 0 = 2 := by decide +kernel
def c1_1_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 88605 else 0, help := 0, threshold := 100000, trainError := 1301, testError := 1301, dose := 7674, maxWrites := 3, rail := 1000000 }
theorem c1_1_K3_valid : Checker.cellValid c1_1_K3 = true := by decide +kernel
theorem c1_1_K3_stop0 : c1_1_K3.stop 0 = 2 := by decide +kernel

def c2_0_K0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40900 else 59100, help := 0, threshold := 100000, trainError := 547, testError := 878, dose := 29992, maxWrites := 3, rail := 1000000 }
theorem c2_0_K0_valid : Checker.cellValid c2_0_K0 = true := by decide +kernel
theorem c2_0_K0_stop0 : c2_0_K0.stop 0 = 2 := by decide +kernel
theorem c2_0_K0_stop1 : c2_0_K0.stop 1 = 2 := by decide +kernel
def c2_0_K3 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40900 else 59100, help := 0, threshold := 100000, trainError := 5084, testError := 9919, dose := 29992, maxWrites := 3, rail := 1000000 }
theorem c2_0_K3_valid : Checker.cellValid c2_0_K3 = false := by decide +kernel
theorem c2_0_K3_stop0 : c2_0_K3.stop 0 = 2 := by decide +kernel
theorem c2_0_K3_stop1 : c2_0_K3.stop 1 = 2 := by decide +kernel

def c3_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 83915 else 0, help := 0, threshold := 100000, trainError := 151, testError := 151, dose := 8261, maxWrites := 3, rail := 1000000 }
theorem c3_0_K0_valid : Checker.cellValid c3_0_K0 = true := by decide +kernel
theorem c3_0_K0_stop0 : c3_0_K0.stop 0 = 2 := by decide +kernel
def c3_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 83915 else 0, help := 0, threshold := 100000, trainError := 1391, testError := 1391, dose := 8261, maxWrites := 3, rail := 1000000 }
theorem c3_0_K3_valid : Checker.cellValid c3_0_K3 = false := by decide +kernel
theorem c3_0_K3_stop0 : c3_0_K3.stop 0 = 2 := by decide +kernel

end LearnedCoincidence.Layered.FitANDOR3
