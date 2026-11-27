import InverterInstanceTiming

/-! The kernel gate of inverter instance 18985 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_18985_K0 : Measures := ⟨(9619 / 20000 : Rat), (12219 / 25000 : Rat), (96971 / 200000 : Rat), (781 / 200000 : Rat), (143 / 1000000 : Rat), (577 / 12500 : Rat), (2719 / 1000000 : Rat), (9771 / 1000000 : Rat), (15963 / 1000000 : Rat), (920889 / 1000000 : Rat), (1009 / 1000000 : Rat), (101 / 100000 : Rat), (507737 / 1000000 : Rat), (191 / 1000 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_18985_K3 : Measures := ⟨(9619 / 20000 : Rat), (12219 / 25000 : Rat), (96971 / 200000 : Rat), (781 / 200000 : Rat), (143 / 1000000 : Rat), (577 / 12500 : Rat), (2719 / 1000000 : Rat), (9771 / 1000000 : Rat), (15963 / 1000000 : Rat), (920889 / 1000000 : Rat), (1009 / 1000000 : Rat), (101 / 100000 : Rat), (507737 / 1000000 : Rat), (19 / 100 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_18985_K0 : check design m_18985_K0 k_K0 timing = true := by decide +kernel

theorem Order_18985_K0 : decide (Order design m_18985_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_18985_K0 : decide (SilenceBefore design m_18985_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_18985_K0 : decide (SilenceAfter design m_18985_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_18985_K0 : decide (FiringBefore design m_18985_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_18985_K0 : decide (FiringAfter design m_18985_K0 k_K0) = true := by decide +kernel
theorem Timing_18985_K0 : decide (Timing design m_18985_K0 timing) = true := by decide +kernel

theorem premises_18985_K0 : Premises design m_18985_K0 k_K0 timing := check_sound check_18985_K0

theorem inverterRead_18985_K0 : InverterRead timing (absentRead m_18985_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_18985_K0

theorem check_18985_K3 : check design m_18985_K3 k_K3 timing = true := by decide +kernel

theorem Order_18985_K3 : decide (Order design m_18985_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_18985_K3 : decide (SilenceBefore design m_18985_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_18985_K3 : decide (SilenceAfter design m_18985_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_18985_K3 : decide (FiringBefore design m_18985_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_18985_K3 : decide (FiringAfter design m_18985_K3 k_K3) = true := by decide +kernel
theorem Timing_18985_K3 : decide (Timing design m_18985_K3 timing) = true := by decide +kernel

theorem premises_18985_K3 : Premises design m_18985_K3 k_K3 timing := check_sound check_18985_K3

theorem inverterRead_18985_K3 : InverterRead timing (absentRead m_18985_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_18985_K3

theorem StateBound_18985 : decide (StateBound design (844221 / 1000000 : Rat) (12411 / 10000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
