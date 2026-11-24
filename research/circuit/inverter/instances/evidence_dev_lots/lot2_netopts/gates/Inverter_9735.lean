import InverterInstanceTiming

/-! The kernel gate of inverter instance 9735 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_9735_K0 : Measures := ⟨(48051 / 100000 : Rat), (6109 / 12500 : Rat), (96923 / 200000 : Rat), (821 / 200000 : Rat), (79 / 500000 : Rat), (45541 / 1000000 : Rat), (3191 / 1000000 : Rat), (8563 / 1000000 : Rat), (439 / 40000 : Rat), (238199 / 250000 : Rat), (251 / 250000 : Rat), (201 / 200000 : Rat), (63939 / 125000 : Rat), (193 / 1000 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_9735_K3 : Measures := ⟨(48051 / 100000 : Rat), (6109 / 12500 : Rat), (96923 / 200000 : Rat), (821 / 200000 : Rat), (79 / 500000 : Rat), (45541 / 1000000 : Rat), (3191 / 1000000 : Rat), (8563 / 1000000 : Rat), (439 / 40000 : Rat), (238199 / 250000 : Rat), (251 / 250000 : Rat), (201 / 200000 : Rat), (63939 / 125000 : Rat), (191 / 1000 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_9735_K0 : check design m_9735_K0 k_K0 timing = true := by decide +kernel

theorem Order_9735_K0 : decide (Order design m_9735_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_9735_K0 : decide (SilenceBefore design m_9735_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_9735_K0 : decide (SilenceAfter design m_9735_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_9735_K0 : decide (FiringBefore design m_9735_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_9735_K0 : decide (FiringAfter design m_9735_K0 k_K0) = true := by decide +kernel
theorem Timing_9735_K0 : decide (Timing design m_9735_K0 timing) = true := by decide +kernel

theorem premises_9735_K0 : Premises design m_9735_K0 k_K0 timing := check_sound check_9735_K0

theorem inverterRead_9735_K0 : InverterRead timing (absentRead m_9735_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9735_K0

theorem check_9735_K3 : check design m_9735_K3 k_K3 timing = true := by decide +kernel

theorem Order_9735_K3 : decide (Order design m_9735_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_9735_K3 : decide (SilenceBefore design m_9735_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_9735_K3 : decide (SilenceAfter design m_9735_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_9735_K3 : decide (FiringBefore design m_9735_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_9735_K3 : decide (FiringAfter design m_9735_K3 k_K3) = true := by decide +kernel
theorem Timing_9735_K3 : decide (Timing design m_9735_K3 timing) = true := by decide +kernel

theorem premises_9735_K3 : Premises design m_9735_K3 k_K3 timing := check_sound check_9735_K3

theorem inverterRead_9735_K3 : InverterRead timing (absentRead m_9735_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9735_K3

theorem StateBound_9735 : decide (StateBound design (873469 / 1000000 : Rat) (1963 / 1600 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
