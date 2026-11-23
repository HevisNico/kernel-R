import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.FitXOR3

set_option maxRecDepth 100000

def c1_0_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 35463 else 35463, help := 0, threshold := 100000, trainError := 259, testError := 259, dose := 8067, maxWrites := 3, rail := 1000000 }
theorem c1_0_K0_valid : Checker.cellValid c1_0_K0 = true := by decide +kernel
theorem c1_0_K0_stop0 : c1_0_K0.stop 0 = 2 := by decide +kernel
def c1_0_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 35463 else 35463, help := 0, threshold := 100000, trainError := 2687, testError := 2687, dose := 8067, maxWrites := 3, rail := 1000000 }
theorem c1_0_K3_valid : Checker.cellValid c1_0_K3 = true := by decide +kernel
theorem c1_0_K3_stop0 : c1_0_K3.stop 0 = 2 := by decide +kernel

def c1_1_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 40332 else 40332, help := 0, threshold := 100000, trainError := 235, testError := 235, dose := 7458, maxWrites := 3, rail := 1000000 }
theorem c1_1_K0_valid : Checker.cellValid c1_1_K0 = true := by decide +kernel
theorem c1_1_K0_stop0 : c1_1_K0.stop 0 = 2 := by decide +kernel
def c1_1_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 40332 else 40332, help := 0, threshold := 100000, trainError := 2483, testError := 2483, dose := 7458, maxWrites := 3, rail := 1000000 }
theorem c1_1_K3_valid : Checker.cellValid c1_1_K3 = true := by decide +kernel
theorem c1_1_K3_stop0 : c1_1_K3.stop 0 = 2 := by decide +kernel

def c2_0_K0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 52571 else 47429, help := 0, threshold := 100000, trainError := 302, testError := 519, dose := 19587, maxWrites := 4, rail := 1000000 }
theorem c2_0_K0_valid : Checker.cellValid c2_0_K0 = true := by decide +kernel
theorem c2_0_K0_stop0 : c2_0_K0.stop 0 = 3 := by decide +kernel
theorem c2_0_K0_stop1 : c2_0_K0.stop 1 = 3 := by decide +kernel
def c2_0_K3 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 52571 else 47429, help := 0, threshold := 100000, trainError := 3277, testError := 6457, dose := 19587, maxWrites := 4, rail := 1000000 }
theorem c2_0_K3_valid : Checker.cellValid c2_0_K3 = false := by decide +kernel
theorem c2_0_K3_stop0 : c2_0_K3.stop 0 = 3 := by decide +kernel
theorem c2_0_K3_stop1 : c2_0_K3.stop 1 = 3 := by decide +kernel

def c3_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 79824 else 0, help := 0, threshold := 100000, trainError := 117, testError := 117, dose := 8772, maxWrites := 4, rail := 1000000 }
theorem c3_0_K0_valid : Checker.cellValid c3_0_K0 = true := by decide +kernel
theorem c3_0_K0_stop0 : c3_0_K0.stop 0 = 3 := by decide +kernel
def c3_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 79824 else 0, help := 0, threshold := 100000, trainError := 1444, testError := 1444, dose := 8772, maxWrites := 4, rail := 1000000 }
theorem c3_0_K3_valid : Checker.cellValid c3_0_K3 = true := by decide +kernel
theorem c3_0_K3_stop0 : c3_0_K3.stop 0 = 3 := by decide +kernel

end LearnedCoincidence.Layered.FitXOR3
