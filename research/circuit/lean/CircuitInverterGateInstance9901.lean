import CircuitInverterGateProof

/-! Seed 9901 (redesigned cell, J0 = 4.0) on the single-source gate. The values are
the instance worker's, with its corrected state bounds measured on the kept traces:
`xPresent = 13442/15625` (R2, over `[0, D]`) and `xAbsent = 23779/20000` (R1, over
`[0, h + hl]`). Every rational premise, `StateBound` included, is checked by the
kernel at K0 and K3. The conclusions remain conditional on the measured real
hypotheses of `gate_silence` and `gate_firing`. Supersedes
`CircuitInverterGate9901.lean`, whose definitions are the earlier restatement. -/

namespace KernelR.Circuit.Gate.Instance9901

open KernelR.Circuit.Gate

def design : Design := ⟨1 / 4, 3 / 10, 3 / 10, 9 / 2, 1, 9 / 10⟩

def measuresK0 : Measures :=
  ⟨48023 / 100000, 24439 / 50000, 96901 / 200000, 171 / 40000, 77 / 500000, 28893 / 1000000,
    4767 / 1000000, 1299 / 500000, 401 / 1000000, 938473 / 1000000, 103 / 100000, 1031 / 1000000,
    260951 / 500000, 201 / 1000⟩

def allowanceK0 : Allowance := ⟨0, 0⟩

def measuresK3 : Measures := { measuresK0 with early := 1 / 5 }

def allowanceK3 : Allowance := ⟨2011 / 1000000, 2353 / 1000000⟩

def xPresent : Rat := 13442 / 15625
def xAbsent : Rat := 23779 / 20000

theorem stateBound : StateBound design xPresent xAbsent := by decide +kernel

theorem orderK0 : Order design measuresK0 allowanceK0 := by decide +kernel
theorem silenceBeforeK0 : SilenceBefore design measuresK0 allowanceK0 := by decide +kernel
theorem silenceAfterK0 : SilenceAfter design measuresK0 allowanceK0 := by decide +kernel
theorem firingBeforeK0 : FiringBefore design measuresK0 allowanceK0 := by decide +kernel
theorem firingAfterK0 : FiringAfter design measuresK0 allowanceK0 := by decide +kernel

theorem orderK3 : Order design measuresK3 allowanceK3 := by decide +kernel
theorem silenceBeforeK3 : SilenceBefore design measuresK3 allowanceK3 := by decide +kernel
theorem silenceAfterK3 : SilenceAfter design measuresK3 allowanceK3 := by decide +kernel
theorem firingBeforeK3 : FiringBefore design measuresK3 allowanceK3 := by decide +kernel
theorem firingAfterK3 : FiringAfter design measuresK3 allowanceK3 := by decide +kernel

/-- Seed 9901 at K3, input present: `gate_silence` on the checked premises. -/
example {actual leak help inhibitory wrongSign : ℝ → ℝ} {initial actualLevel : ℝ} :=
  @gate_silence design measuresK3 allowanceK3 xPresent xAbsent orderK3 silenceBeforeK3 silenceAfterK3
    stateBound actual leak help inhibitory wrongSign initial actualLevel

/-- Seed 9901 at K3, input absent: `gate_firing` on the checked premises. -/
example {actual leak help inhibitory : ℝ → ℝ} {initial actualLevel : ℝ} :=
  @gate_firing design measuresK3 allowanceK3 xPresent xAbsent orderK3 firingBeforeK3 firingAfterK3
    stateBound actual leak help inhibitory initial actualLevel

end KernelR.Circuit.Gate.Instance9901
