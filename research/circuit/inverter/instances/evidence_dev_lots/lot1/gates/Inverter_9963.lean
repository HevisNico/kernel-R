import InverterInstanceCheck

/-! The kernel gate of inverter instance 9963 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Gate

open LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_9963_K0 : Measures := ⟨(12071 / 25000 : Rat), (48877 / 100000 : Rat), (97161 / 200000 : Rat), (593 / 200000 : Rat), (79 / 500000 : Rat), (1743 / 12500 : Rat), (2203 / 500000 : Rat), (10459 / 1000000 : Rat), (9801 / 500000 : Rat), (452563 / 500000 : Rat), (499 / 500000 : Rat), (999 / 1000000 : Rat), (494341 / 1000000 : Rat), (21 / 125 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_9963_K3 : Measures := ⟨(12071 / 25000 : Rat), (48877 / 100000 : Rat), (97161 / 200000 : Rat), (593 / 200000 : Rat), (79 / 500000 : Rat), (1743 / 12500 : Rat), (2203 / 500000 : Rat), (10459 / 1000000 : Rat), (9801 / 500000 : Rat), (452563 / 500000 : Rat), (499 / 500000 : Rat), (999 / 1000000 : Rat), (494341 / 1000000 : Rat), (167 / 1000 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_9963_K0 : check design m_9963_K0 k_K0 timing = true := by decide +kernel

theorem Order_9963_K0 : decide (Order design m_9963_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_9963_K0 : decide (SilenceBefore design m_9963_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_9963_K0 : decide (SilenceAfter design m_9963_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_9963_K0 : decide (FiringBefore design m_9963_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_9963_K0 : decide (FiringAfter design m_9963_K0 k_K0) = true := by decide +kernel
theorem Timing_9963_K0 : decide (Timing design m_9963_K0 timing) = true := by decide +kernel

theorem premises_9963_K0 : Premises design m_9963_K0 k_K0 timing := check_sound check_9963_K0

theorem inverterRead_9963_K0 : InverterRead timing (absentRead m_9963_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9963_K0

theorem check_9963_K3 : check design m_9963_K3 k_K3 timing = true := by decide +kernel

theorem Order_9963_K3 : decide (Order design m_9963_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_9963_K3 : decide (SilenceBefore design m_9963_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_9963_K3 : decide (SilenceAfter design m_9963_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_9963_K3 : decide (FiringBefore design m_9963_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_9963_K3 : decide (FiringAfter design m_9963_K3 k_K3) = true := by decide +kernel
theorem Timing_9963_K3 : decide (Timing design m_9963_K3 timing) = true := by decide +kernel

theorem premises_9963_K3 : Premises design m_9963_K3 k_K3 timing := check_sound check_9963_K3

theorem inverterRead_9963_K3 : InverterRead timing (absentRead m_9963_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9963_K3

end LearnedCoincidence.MonotoneDNF.InverterInstance.Gate
