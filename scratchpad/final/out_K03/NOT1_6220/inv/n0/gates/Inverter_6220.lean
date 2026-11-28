import InverterInstanceTiming

/-! The kernel gate of inverter instance 6220 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_6220_K0 : Measures := ⟨(481 / 1000 : Rat), (48879 / 100000 : Rat), (96979 / 200000 : Rat), (779 / 200000 : Rat), (149 / 1000000 : Rat), (50153 / 1000000 : Rat), (4417 / 1000000 : Rat), (1421 / 50000 : Rat), (19703 / 1000000 : Rat), (187187 / 200000 : Rat), (13 / 12500 : Rat), (1041 / 1000000 : Rat), (517767 / 1000000 : Rat), (37 / 200 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_6220_K3 : Measures := ⟨(481 / 1000 : Rat), (48879 / 100000 : Rat), (96979 / 200000 : Rat), (779 / 200000 : Rat), (149 / 1000000 : Rat), (50153 / 1000000 : Rat), (4417 / 1000000 : Rat), (1421 / 50000 : Rat), (19703 / 1000000 : Rat), (187187 / 200000 : Rat), (13 / 12500 : Rat), (1041 / 1000000 : Rat), (517767 / 1000000 : Rat), (183 / 1000 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_6220_K0 : check design m_6220_K0 k_K0 timing = true := by decide +kernel

theorem Order_6220_K0 : decide (Order design m_6220_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_6220_K0 : decide (SilenceBefore design m_6220_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_6220_K0 : decide (SilenceAfter design m_6220_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_6220_K0 : decide (FiringBefore design m_6220_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_6220_K0 : decide (FiringAfter design m_6220_K0 k_K0) = true := by decide +kernel
theorem Timing_6220_K0 : decide (Timing design m_6220_K0 timing) = true := by decide +kernel

theorem premises_6220_K0 : Premises design m_6220_K0 k_K0 timing := check_sound check_6220_K0

theorem inverterRead_6220_K0 : InverterRead timing (absentRead m_6220_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6220_K0

theorem check_6220_K3 : check design m_6220_K3 k_K3 timing = true := by decide +kernel

theorem Order_6220_K3 : decide (Order design m_6220_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_6220_K3 : decide (SilenceBefore design m_6220_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_6220_K3 : decide (SilenceAfter design m_6220_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_6220_K3 : decide (FiringBefore design m_6220_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_6220_K3 : decide (FiringAfter design m_6220_K3 k_K3) = true := by decide +kernel
theorem Timing_6220_K3 : decide (Timing design m_6220_K3 timing) = true := by decide +kernel

theorem premises_6220_K3 : Premises design m_6220_K3 k_K3 timing := check_sound check_6220_K3

theorem inverterRead_6220_K3 : InverterRead timing (absentRead m_6220_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6220_K3

theorem StateBound_6220 : decide (StateBound design (17157 / 20000 : Rat) (19312 / 15625 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
