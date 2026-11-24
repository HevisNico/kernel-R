import InverterInstanceTiming

/-! The kernel gate of inverter instance 9928 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_9928_K0 : Measures := ⟨(48301 / 100000 : Rat), (48873 / 100000 : Rat), (48587 / 100000 : Rat), (143 / 50000 : Rat), (147 / 1000000 : Rat), (176177 / 1000000 : Rat), (1627 / 500000 : Rat), (749 / 125000 : Rat), (35013 / 1000000 : Rat), (236577 / 250000 : Rat), (489 / 500000 : Rat), (979 / 1000000 : Rat), (486547 / 1000000 : Rat), (39 / 250 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_9928_K3 : Measures := ⟨(48301 / 100000 : Rat), (48873 / 100000 : Rat), (48587 / 100000 : Rat), (143 / 50000 : Rat), (147 / 1000000 : Rat), (176177 / 1000000 : Rat), (1627 / 500000 : Rat), (749 / 125000 : Rat), (35013 / 1000000 : Rat), (236577 / 250000 : Rat), (489 / 500000 : Rat), (979 / 1000000 : Rat), (486547 / 1000000 : Rat), (31 / 200 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_9928_K0 : check design m_9928_K0 k_K0 timing = true := by decide +kernel

theorem Order_9928_K0 : decide (Order design m_9928_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_9928_K0 : decide (SilenceBefore design m_9928_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_9928_K0 : decide (SilenceAfter design m_9928_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_9928_K0 : decide (FiringBefore design m_9928_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_9928_K0 : decide (FiringAfter design m_9928_K0 k_K0) = true := by decide +kernel
theorem Timing_9928_K0 : decide (Timing design m_9928_K0 timing) = true := by decide +kernel

theorem premises_9928_K0 : Premises design m_9928_K0 k_K0 timing := check_sound check_9928_K0

theorem inverterRead_9928_K0 : InverterRead timing (absentRead m_9928_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9928_K0

theorem check_9928_K3 : check design m_9928_K3 k_K3 timing = false := by decide +kernel

theorem Order_9928_K3 : decide (Order design m_9928_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_9928_K3 : decide (SilenceBefore design m_9928_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_9928_K3 : decide (SilenceAfter design m_9928_K3 k_K3) = false := by decide +kernel
theorem FiringBefore_9928_K3 : decide (FiringBefore design m_9928_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_9928_K3 : decide (FiringAfter design m_9928_K3 k_K3) = true := by decide +kernel
theorem Timing_9928_K3 : decide (Timing design m_9928_K3 timing) = true := by decide +kernel

theorem StateBound_9928 : decide (StateBound design (867529 / 1000000 : Rat) (26951 / 20000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
