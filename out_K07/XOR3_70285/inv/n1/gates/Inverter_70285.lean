import InverterInstanceTiming

/-! The kernel gate of inverter instance 70285 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_70285_K0 : Measures := ⟨(6009 / 12500 : Rat), (48877 / 100000 : Rat), (96949 / 200000 : Rat), (161 / 40000 : Rat), (77 / 500000 : Rat), (46909 / 1000000 : Rat), (2139 / 500000 : Rat), (3669 / 500000 : Rat), (3107 / 200000 : Rat), (188143 / 200000 : Rat), (257 / 250000 : Rat), (1029 / 1000000 : Rat), (518579 / 1000000 : Rat), (191 / 1000 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_70285_K3 : Measures := ⟨(6009 / 12500 : Rat), (48877 / 100000 : Rat), (96949 / 200000 : Rat), (161 / 40000 : Rat), (77 / 500000 : Rat), (46909 / 1000000 : Rat), (2139 / 500000 : Rat), (3669 / 500000 : Rat), (3107 / 200000 : Rat), (188143 / 200000 : Rat), (257 / 250000 : Rat), (1029 / 1000000 : Rat), (518579 / 1000000 : Rat), (19 / 100 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_70285_K0 : check design m_70285_K0 k_K0 timing = true := by decide +kernel

theorem Order_70285_K0 : decide (Order design m_70285_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_70285_K0 : decide (SilenceBefore design m_70285_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_70285_K0 : decide (SilenceAfter design m_70285_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_70285_K0 : decide (FiringBefore design m_70285_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_70285_K0 : decide (FiringAfter design m_70285_K0 k_K0) = true := by decide +kernel
theorem Timing_70285_K0 : decide (Timing design m_70285_K0 timing) = true := by decide +kernel

theorem premises_70285_K0 : Premises design m_70285_K0 k_K0 timing := check_sound check_70285_K0

theorem inverterRead_70285_K0 : InverterRead timing (absentRead m_70285_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_70285_K0

theorem check_70285_K3 : check design m_70285_K3 k_K3 timing = true := by decide +kernel

theorem Order_70285_K3 : decide (Order design m_70285_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_70285_K3 : decide (SilenceBefore design m_70285_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_70285_K3 : decide (SilenceAfter design m_70285_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_70285_K3 : decide (FiringBefore design m_70285_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_70285_K3 : decide (FiringAfter design m_70285_K3 k_K3) = true := by decide +kernel
theorem Timing_70285_K3 : decide (Timing design m_70285_K3 timing) = true := by decide +kernel

theorem premises_70285_K3 : Premises design m_70285_K3 k_K3 timing := check_sound check_70285_K3

theorem inverterRead_70285_K3 : InverterRead timing (absentRead m_70285_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_70285_K3

theorem StateBound_70285 : decide (StateBound design (431129 / 500000 : Rat) (306409 / 250000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
