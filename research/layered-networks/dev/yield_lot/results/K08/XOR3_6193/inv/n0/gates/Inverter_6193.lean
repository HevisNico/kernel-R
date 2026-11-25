import InverterInstanceTiming

/-! The kernel gate of inverter instance 6193 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_6193_K0 : Measures := ⟨(24023 / 50000 : Rat), (12219 / 25000 : Rat), (48461 / 100000 : Rat), (83 / 20000 : Rat), (31 / 200000 : Rat), (3149 / 62500 : Rat), (4467 / 1000000 : Rat), (4627 / 200000 : Rat), (4591 / 200000 : Rat), (928963 / 1000000 : Rat), (1017 / 1000000 : Rat), (509 / 500000 : Rat), (20779 / 40000 : Rat), (37 / 200 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_6193_K3 : Measures := ⟨(24023 / 50000 : Rat), (12219 / 25000 : Rat), (48461 / 100000 : Rat), (83 / 20000 : Rat), (31 / 200000 : Rat), (3149 / 62500 : Rat), (4467 / 1000000 : Rat), (4627 / 200000 : Rat), (4591 / 200000 : Rat), (928963 / 1000000 : Rat), (1017 / 1000000 : Rat), (509 / 500000 : Rat), (20779 / 40000 : Rat), (23 / 125 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_6193_K0 : check design m_6193_K0 k_K0 timing = true := by decide +kernel

theorem Order_6193_K0 : decide (Order design m_6193_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_6193_K0 : decide (SilenceBefore design m_6193_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_6193_K0 : decide (SilenceAfter design m_6193_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_6193_K0 : decide (FiringBefore design m_6193_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_6193_K0 : decide (FiringAfter design m_6193_K0 k_K0) = true := by decide +kernel
theorem Timing_6193_K0 : decide (Timing design m_6193_K0 timing) = true := by decide +kernel

theorem premises_6193_K0 : Premises design m_6193_K0 k_K0 timing := check_sound check_6193_K0

theorem inverterRead_6193_K0 : InverterRead timing (absentRead m_6193_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6193_K0

theorem check_6193_K3 : check design m_6193_K3 k_K3 timing = true := by decide +kernel

theorem Order_6193_K3 : decide (Order design m_6193_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_6193_K3 : decide (SilenceBefore design m_6193_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_6193_K3 : decide (SilenceAfter design m_6193_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_6193_K3 : decide (FiringBefore design m_6193_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_6193_K3 : decide (FiringAfter design m_6193_K3 k_K3) = true := by decide +kernel
theorem Timing_6193_K3 : decide (Timing design m_6193_K3 timing) = true := by decide +kernel

theorem premises_6193_K3 : Premises design m_6193_K3 k_K3 timing := check_sound check_6193_K3

theorem inverterRead_6193_K3 : InverterRead timing (absentRead m_6193_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6193_K3

theorem StateBound_6193 : decide (StateBound design (13306 / 15625 : Rat) (246127 / 200000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
