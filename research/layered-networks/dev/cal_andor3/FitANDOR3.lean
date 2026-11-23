import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.FitANDOR3

set_option maxRecDepth 100000

-- c1_0: not measured (D3: scan group 0 has no scan-native FIRE (its bracket end comes from a training read under network timing))
def c1_1_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 70431 else 0, help := 0, threshold := 100000, trainError := 247, testError := 247, dose := 9946, maxWrites := 4, rail := 1000000 }
theorem c1_1_K0_valid : Checker.cellValid c1_1_K0 = true := by decide +kernel
theorem c1_1_K0_stop0 : c1_1_K0.stop 0 = 3 := by decide +kernel
def c1_1_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 70431 else 0, help := 0, threshold := 100000, trainError := 3278, testError := 3278, dose := 9946, maxWrites := 4, rail := 1000000 }
theorem c1_1_K3_valid : Checker.cellValid c1_1_K3 = false := by decide +kernel
theorem c1_1_K3_stop0 : c1_1_K3.stop 0 = 3 := by decide +kernel

def c2_0_K0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40714 else 59269, help := 0, threshold := 100000, trainError := 436, testError := 768, dose := 14989, maxWrites := 4, rail := 1000000 }
theorem c2_0_K0_valid : Checker.cellValid c2_0_K0 = false := by decide +kernel
theorem c2_0_K0_stop0 : c2_0_K0.stop 0 = 4 := by decide +kernel
theorem c2_0_K0_stop1 : c2_0_K0.stop 1 = 3 := by decide +kernel
def c2_0_K3 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40714 else 59269, help := 0, threshold := 100000, trainError := 5027, testError := 9888, dose := 14989, maxWrites := 4, rail := 1000000 }
theorem c2_0_K3_valid : Checker.cellValid c2_0_K3 = false := by decide +kernel
theorem c2_0_K3_stop0 : c2_0_K3.stop 0 = 4 := by decide +kernel
theorem c2_0_K3_stop1 : c2_0_K3.stop 1 = 3 := by decide +kernel

def c3_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 52667 else 0, help := 0, threshold := 100000, trainError := 324, testError := 324, dose := 12164, maxWrites := 5, rail := 1000000 }
theorem c3_0_K0_valid : Checker.cellValid c3_0_K0 = true := by decide +kernel
theorem c3_0_K0_stop0 : c3_0_K0.stop 0 = 4 := by decide +kernel
def c3_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 52667 else 0, help := 0, threshold := 100000, trainError := 4000, testError := 4000, dose := 12164, maxWrites := 5, rail := 1000000 }
theorem c3_0_K3_valid : Checker.cellValid c3_0_K3 = false := by decide +kernel
theorem c3_0_K3_stop0 : c3_0_K3.stop 0 = 4 := by decide +kernel

end LearnedCoincidence.Layered.FitANDOR3
