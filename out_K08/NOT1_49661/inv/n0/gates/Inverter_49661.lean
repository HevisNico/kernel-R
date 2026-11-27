import InverterInstanceTiming

/-! The kernel gate of inverter instance 49661 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_49661_K0 : Measures := ⟨(4813 / 10000 : Rat), (6109 / 12500 : Rat), (48501 / 100000 : Rat), (371 / 100000 : Rat), (33 / 200000 : Rat), (77879 / 1000000 : Rat), (3063 / 1000000 : Rat), (231 / 15625 : Rat), (1909 / 1000000 : Rat), (975327 / 1000000 : Rat), (1011 / 1000000 : Rat), (253 / 250000 : Rat), (508697 / 1000000 : Rat), (37 / 200 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_49661_K3 : Measures := ⟨(4813 / 10000 : Rat), (6109 / 12500 : Rat), (48501 / 100000 : Rat), (371 / 100000 : Rat), (33 / 200000 : Rat), (77879 / 1000000 : Rat), (3063 / 1000000 : Rat), (231 / 15625 : Rat), (1909 / 1000000 : Rat), (975327 / 1000000 : Rat), (1011 / 1000000 : Rat), (253 / 250000 : Rat), (508697 / 1000000 : Rat), (23 / 125 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_49661_K0 : check design m_49661_K0 k_K0 timing = true := by decide +kernel

theorem Order_49661_K0 : decide (Order design m_49661_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_49661_K0 : decide (SilenceBefore design m_49661_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_49661_K0 : decide (SilenceAfter design m_49661_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_49661_K0 : decide (FiringBefore design m_49661_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_49661_K0 : decide (FiringAfter design m_49661_K0 k_K0) = true := by decide +kernel
theorem Timing_49661_K0 : decide (Timing design m_49661_K0 timing) = true := by decide +kernel

theorem premises_49661_K0 : Premises design m_49661_K0 k_K0 timing := check_sound check_49661_K0

theorem inverterRead_49661_K0 : InverterRead timing (absentRead m_49661_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_49661_K0

theorem check_49661_K3 : check design m_49661_K3 k_K3 timing = true := by decide +kernel

theorem Order_49661_K3 : decide (Order design m_49661_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_49661_K3 : decide (SilenceBefore design m_49661_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_49661_K3 : decide (SilenceAfter design m_49661_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_49661_K3 : decide (FiringBefore design m_49661_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_49661_K3 : decide (FiringAfter design m_49661_K3 k_K3) = true := by decide +kernel
theorem Timing_49661_K3 : decide (Timing design m_49661_K3 timing) = true := by decide +kernel

theorem premises_49661_K3 : Premises design m_49661_K3 k_K3 timing := check_sound check_49661_K3

theorem inverterRead_49661_K3 : InverterRead timing (absentRead m_49661_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_49661_K3

theorem StateBound_49661 : decide (StateBound design (893947 / 1000000 : Rat) (1255849 / 1000000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
