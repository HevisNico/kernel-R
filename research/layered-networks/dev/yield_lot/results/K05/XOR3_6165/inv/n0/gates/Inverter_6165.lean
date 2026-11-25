import InverterInstanceTiming

/-! The kernel gate of inverter instance 6165 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_6165_K0 : Measures := ⟨(24029 / 50000 : Rat), (611 / 1250 : Rat), (48469 / 100000 : Rat), (411 / 100000 : Rat), (79 / 500000 : Rat), (20313 / 500000 : Rat), (4613 / 1000000 : Rat), (15269 / 1000000 : Rat), (9493 / 1000000 : Rat), (886097 / 1000000 : Rat), (1017 / 1000000 : Rat), (509 / 500000 : Rat), (103583 / 200000 : Rat), (24 / 125 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_6165_K3 : Measures := ⟨(24029 / 50000 : Rat), (611 / 1250 : Rat), (48469 / 100000 : Rat), (411 / 100000 : Rat), (79 / 500000 : Rat), (20313 / 500000 : Rat), (4613 / 1000000 : Rat), (15269 / 1000000 : Rat), (9493 / 1000000 : Rat), (886097 / 1000000 : Rat), (1017 / 1000000 : Rat), (509 / 500000 : Rat), (103583 / 200000 : Rat), (191 / 1000 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_6165_K0 : check design m_6165_K0 k_K0 timing = true := by decide +kernel

theorem Order_6165_K0 : decide (Order design m_6165_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_6165_K0 : decide (SilenceBefore design m_6165_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_6165_K0 : decide (SilenceAfter design m_6165_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_6165_K0 : decide (FiringBefore design m_6165_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_6165_K0 : decide (FiringAfter design m_6165_K0 k_K0) = true := by decide +kernel
theorem Timing_6165_K0 : decide (Timing design m_6165_K0 timing) = true := by decide +kernel

theorem premises_6165_K0 : Premises design m_6165_K0 k_K0 timing := check_sound check_6165_K0

theorem inverterRead_6165_K0 : InverterRead timing (absentRead m_6165_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6165_K0

theorem check_6165_K3 : check design m_6165_K3 k_K3 timing = true := by decide +kernel

theorem Order_6165_K3 : decide (Order design m_6165_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_6165_K3 : decide (SilenceBefore design m_6165_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_6165_K3 : decide (SilenceAfter design m_6165_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_6165_K3 : decide (FiringBefore design m_6165_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_6165_K3 : decide (FiringAfter design m_6165_K3 k_K3) = true := by decide +kernel
theorem Timing_6165_K3 : decide (Timing design m_6165_K3 timing) = true := by decide +kernel

theorem premises_6165_K3 : Premises design m_6165_K3 k_K3 timing := check_sound check_6165_K3

theorem inverterRead_6165_K3 : InverterRead timing (absentRead m_6165_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6165_K3

theorem StateBound_6165 : decide (StateBound design (406107 / 500000 : Rat) (1220731 / 1000000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
