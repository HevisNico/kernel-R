import InverterInstanceTiming

/-! The kernel gate of inverter instance 9958 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_9958_K0 : Measures := ⟨(9609 / 20000 : Rat), (48871 / 100000 : Rat), (24229 / 50000 : Rat), (413 / 100000 : Rat), (71 / 500000 : Rat), (659 / 15625 : Rat), (4033 / 1000000 : Rat), (1377 / 250000 : Rat), (1821 / 1000000 : Rat), (98117 / 100000 : Rat), (201 / 200000 : Rat), (503 / 500000 : Rat), (514593 / 1000000 : Rat), (49 / 250 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_9958_K3 : Measures := ⟨(9609 / 20000 : Rat), (48871 / 100000 : Rat), (24229 / 50000 : Rat), (413 / 100000 : Rat), (71 / 500000 : Rat), (659 / 15625 : Rat), (4033 / 1000000 : Rat), (1377 / 250000 : Rat), (1821 / 1000000 : Rat), (98117 / 100000 : Rat), (201 / 200000 : Rat), (503 / 500000 : Rat), (514593 / 1000000 : Rat), (39 / 200 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_9958_K0 : check design m_9958_K0 k_K0 timing = true := by decide +kernel

theorem Order_9958_K0 : decide (Order design m_9958_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_9958_K0 : decide (SilenceBefore design m_9958_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_9958_K0 : decide (SilenceAfter design m_9958_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_9958_K0 : decide (FiringBefore design m_9958_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_9958_K0 : decide (FiringAfter design m_9958_K0 k_K0) = true := by decide +kernel
theorem Timing_9958_K0 : decide (Timing design m_9958_K0 timing) = true := by decide +kernel

theorem premises_9958_K0 : Premises design m_9958_K0 k_K0 timing := check_sound check_9958_K0

theorem inverterRead_9958_K0 : InverterRead timing (absentRead m_9958_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9958_K0

theorem check_9958_K3 : check design m_9958_K3 k_K3 timing = true := by decide +kernel

theorem Order_9958_K3 : decide (Order design m_9958_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_9958_K3 : decide (SilenceBefore design m_9958_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_9958_K3 : decide (SilenceAfter design m_9958_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_9958_K3 : decide (FiringBefore design m_9958_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_9958_K3 : decide (FiringAfter design m_9958_K3 k_K3) = true := by decide +kernel
theorem Timing_9958_K3 : decide (Timing design m_9958_K3 timing) = true := by decide +kernel

theorem premises_9958_K3 : Premises design m_9958_K3 k_K3 timing := check_sound check_9958_K3

theorem inverterRead_9958_K3 : InverterRead timing (absentRead m_9958_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9958_K3

theorem StateBound_9958 : decide (StateBound design (899351 / 1000000 : Rat) (612117 / 500000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
