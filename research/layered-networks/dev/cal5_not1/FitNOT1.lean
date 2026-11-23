import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.FitNOT1

set_option maxRecDepth 100000

def c1_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 85458 else 0, help := 0, threshold := 100000, trainError := 108, testError := 108, dose := 8068, maxWrites := 3, rail := 1000000 }
theorem c1_0_K0_valid : Checker.cellValid c1_0_K0 = true := by decide +kernel
theorem c1_0_K0_stop0 : c1_0_K0.stop 0 = 2 := by decide +kernel
def c1_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 85458 else 0, help := 0, threshold := 100000, trainError := 1324, testError := 1324, dose := 8068, maxWrites := 3, rail := 1000000 }
theorem c1_0_K3_valid : Checker.cellValid c1_0_K3 = true := by decide +kernel
theorem c1_0_K3_stop0 : c1_0_K3.stop 0 = 2 := by decide +kernel

end LearnedCoincidence.Layered.FitNOT1
