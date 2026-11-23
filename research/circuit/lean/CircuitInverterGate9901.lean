import CircuitInverterGateBridge

/-! The bridge applied to one measured instance: seed 9901 of the redesigned cell
(J0 = 4.0), with the values the instance worker sent (`Inverter_9901.lean` on its
local branch research/inverter-instances, cd8823e). The rational premises are
checked here by the kernel, at the nominal allowance K0 and at K3. The conclusions
are conditional on the measured real hypotheses of `gate_silence` and
`gate_firing`, including the state bound `|x| ≤ H0 * hl = 27/20`, which is not one
of the gate's own premises and must be measured. -/

namespace KernelR.Circuit.InverterGate.Instance9901

open KernelR.Circuit.InverterGate

def design : Design := ⟨1 / 4, 3 / 10, 3 / 10, 9 / 2, 1, 9 / 10⟩

def measuresK0 : Measures :=
  ⟨48023 / 100000, 24439 / 50000, 96901 / 200000, 171 / 40000, 77 / 500000, 28893 / 1000000,
    4767 / 1000000, 1299 / 500000, 401 / 1000000, 938473 / 1000000, 103 / 100000, 1031 / 1000000,
    260951 / 500000, 201 / 1000⟩

def allowanceK0 : Allowance := ⟨0, 0⟩

def measuresK3 : Measures := { measuresK0 with early := 1 / 5 }

def allowanceK3 : Allowance := ⟨2011 / 1000000, 2353 / 1000000⟩

theorem orderK0 : Order design measuresK0 allowanceK0 := by
  unfold Order; decide +kernel
theorem silenceBeforeK0 : SilenceBefore design measuresK0 allowanceK0 := by
  unfold SilenceBefore; decide +kernel
theorem silenceAfterK0 : SilenceAfter design measuresK0 allowanceK0 := by
  unfold SilenceAfter; decide +kernel
theorem firingBeforeK0 : FiringBefore design measuresK0 allowanceK0 := by
  unfold FiringBefore; decide +kernel
theorem firingAfterK0 : FiringAfter design measuresK0 allowanceK0 := by
  unfold FiringAfter; decide +kernel

theorem orderK3 : Order design measuresK3 allowanceK3 := by
  unfold Order; decide +kernel
theorem silenceBeforeK3 : SilenceBefore design measuresK3 allowanceK3 := by
  unfold SilenceBefore; decide +kernel
theorem silenceAfterK3 : SilenceAfter design measuresK3 allowanceK3 := by
  unfold SilenceAfter; decide +kernel
theorem firingBeforeK3 : FiringBefore design measuresK3 allowanceK3 := by
  unfold FiringBefore; decide +kernel
theorem firingAfterK3 : FiringAfter design measuresK3 allowanceK3 := by
  unfold FiringAfter; decide +kernel

/-- Seed 9901 at K3, with the input present: `gate_silence` applied to the checked
premises. Any trajectory meeting the measured real hypotheses stays silent. -/
example {actual leak help inhibitory wrongSign : ℝ → ℝ} {initial actualLevel : ℝ} :=
  @gate_silence design measuresK3 allowanceK3 orderK3 silenceBeforeK3 silenceAfterK3
    actual leak help inhibitory wrongSign initial actualLevel

/-- Seed 9901 at K3, with the input absent: `gate_firing` applied to the checked
premises. Any trajectory meeting the measured real hypotheses fires between
`h + early` and `h + hl`. -/
example {actual leak help inhibitory : ℝ → ℝ} {initial actualLevel : ℝ} :=
  @gate_firing design measuresK3 allowanceK3 orderK3 firingBeforeK3 firingAfterK3
    actual leak help inhibitory initial actualLevel

end KernelR.Circuit.InverterGate.Instance9901
