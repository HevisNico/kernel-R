import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.FitANDOR3

set_option maxRecDepth 100000

-- c1_0: not measured (question 1, group 0: ceil(s*) 3 vs first FIRE 2)
def c1_1_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 88606 else 0, help := 0, threshold := 100000, trainError := 104, testError := 104, dose := 7674, maxWrites := 3, rail := 1000000 }
theorem c1_1_K0_valid : Checker.cellValid c1_1_K0 = true := by decide +kernel
theorem c1_1_K0_stop0 : c1_1_K0.stop 0 = 2 := by decide +kernel
def c1_1_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 88606 else 0, help := 0, threshold := 100000, trainError := 1263, testError := 1263, dose := 7674, maxWrites := 3, rail := 1000000 }
theorem c1_1_K3_valid : Checker.cellValid c1_1_K3 = true := by decide +kernel
theorem c1_1_K3_stop0 : c1_1_K3.stop 0 = 2 := by decide +kernel

def c2_0_K0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40901 else 59097, help := 0, threshold := 100000, trainError := 471, testError := 802, dose := 29996, maxWrites := 3, rail := 1000000 }
theorem c2_0_K0_valid : Checker.cellValid c2_0_K0 = true := by decide +kernel
theorem c2_0_K0_stop0 : c2_0_K0.stop 0 = 2 := by decide +kernel
theorem c2_0_K0_stop1 : c2_0_K0.stop 1 = 2 := by decide +kernel
def c2_0_K3 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40901 else 59097, help := 0, threshold := 100000, trainError := 5008, testError := 9844, dose := 29996, maxWrites := 3, rail := 1000000 }
theorem c2_0_K3_valid : Checker.cellValid c2_0_K3 = false := by decide +kernel
theorem c2_0_K3_stop0 : c2_0_K3.stop 0 = 2 := by decide +kernel
theorem c2_0_K3_stop1 : c2_0_K3.stop 1 = 2 := by decide +kernel

def c3_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 83958 else 0, help := 0, threshold := 100000, trainError := 144, testError := 144, dose := 8255, maxWrites := 3, rail := 1000000 }
theorem c3_0_K0_valid : Checker.cellValid c3_0_K0 = true := by decide +kernel
theorem c3_0_K0_stop0 : c3_0_K0.stop 0 = 2 := by decide +kernel
def c3_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 83958 else 0, help := 0, threshold := 100000, trainError := 1383, testError := 1383, dose := 8255, maxWrites := 3, rail := 1000000 }
theorem c3_0_K3_valid : Checker.cellValid c3_0_K3 = false := by decide +kernel
theorem c3_0_K3_stop0 : c3_0_K3.stop 0 = 2 := by decide +kernel

end LearnedCoincidence.Layered.FitANDOR3
