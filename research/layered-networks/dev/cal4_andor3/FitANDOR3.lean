import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.FitANDOR3

set_option maxRecDepth 100000

def c1_0_K0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 223 else 223, help := 0, threshold := 100000, trainError := 722, testError := 722, dose := 12472, maxWrites := 5, rail := 1000000 }
theorem c1_0_K0_valid : Checker.cellValid c1_0_K0 = false := by decide +kernel
theorem c1_0_K0_stop0 : c1_0_K0.stop 0 = 4 := by decide +kernel
def c1_0_K3 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 223 else 223, help := 0, threshold := 100000, trainError := 8323, testError := 8323, dose := 12472, maxWrites := 5, rail := 1000000 }
theorem c1_0_K3_valid : Checker.cellValid c1_0_K3 = false := by decide +kernel
theorem c1_0_K3_stop0 : c1_0_K3.stop 0 = 4 := by decide +kernel

def c1_1_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 70623 else 0, help := 0, threshold := 100000, trainError := 420, testError := 420, dose := 9922, maxWrites := 4, rail := 1000000 }
theorem c1_1_K0_valid : Checker.cellValid c1_1_K0 = false := by decide +kernel
theorem c1_1_K0_stop0 : c1_1_K0.stop 0 = 3 := by decide +kernel
def c1_1_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 70623 else 0, help := 0, threshold := 100000, trainError := 3444, testError := 3444, dose := 9922, maxWrites := 4, rail := 1000000 }
theorem c1_1_K3_valid : Checker.cellValid c1_1_K3 = false := by decide +kernel
theorem c1_1_K3_stop0 : c1_1_K3.stop 0 = 3 := by decide +kernel

def c2_0_K0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40697 else 59285, help := 0, threshold := 100000, trainError := 544, testError := 876, dose := 14969, maxWrites := 4, rail := 1000000 }
theorem c2_0_K0_valid : Checker.cellValid c2_0_K0 = false := by decide +kernel
theorem c2_0_K0_stop0 : c2_0_K0.stop 0 = 4 := by decide +kernel
theorem c2_0_K0_stop1 : c2_0_K0.stop 1 = 3 := by decide +kernel
def c2_0_K3 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40697 else 59285, help := 0, threshold := 100000, trainError := 5129, testError := 9983, dose := 14969, maxWrites := 4, rail := 1000000 }
theorem c2_0_K3_valid : Checker.cellValid c2_0_K3 = false := by decide +kernel
theorem c2_0_K3_stop0 : c2_0_K3.stop 0 = 4 := by decide +kernel
theorem c2_0_K3_stop1 : c2_0_K3.stop 1 = 3 := by decide +kernel

def c3_0_K0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 52891 else 0, help := 0, threshold := 100000, trainError := 342, testError := 342, dose := 12136, maxWrites := 5, rail := 1000000 }
theorem c3_0_K0_valid : Checker.cellValid c3_0_K0 = true := by decide +kernel
theorem c3_0_K0_stop0 : c3_0_K0.stop 0 = 4 := by decide +kernel
def c3_0_K3 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 52891 else 0, help := 0, threshold := 100000, trainError := 4010, testError := 4010, dose := 12136, maxWrites := 5, rail := 1000000 }
theorem c3_0_K3_valid : Checker.cellValid c3_0_K3 = false := by decide +kernel
theorem c3_0_K3_stop0 : c3_0_K3.stop 0 = 4 := by decide +kernel

end LearnedCoincidence.Layered.FitANDOR3
