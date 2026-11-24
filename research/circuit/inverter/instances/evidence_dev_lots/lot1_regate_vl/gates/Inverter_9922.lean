import InverterInstanceCheck

/-! The kernel gate of inverter instance 9922 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Gate

open LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_9922_K0 : Measures := ⟨(5991 / 12500 : Rat), (611 / 1250 : Rat), (12101 / 25000 : Rat), (119 / 25000 : Rat), (39 / 250000 : Rat), (22429 / 250000 : Rat), (2513 / 1000000 : Rat), (3279 / 500000 : Rat), (1533 / 1000000 : Rat), (186873 / 200000 : Rat), (517 / 500000 : Rat), (207 / 200000 : Rat), (534191 / 1000000 : Rat), (23 / 125 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_9922_K3 : Measures := ⟨(5991 / 12500 : Rat), (611 / 1250 : Rat), (12101 / 25000 : Rat), (119 / 25000 : Rat), (39 / 250000 : Rat), (22429 / 250000 : Rat), (2513 / 1000000 : Rat), (3279 / 500000 : Rat), (1533 / 1000000 : Rat), (186873 / 200000 : Rat), (517 / 500000 : Rat), (207 / 200000 : Rat), (534191 / 1000000 : Rat), (183 / 1000 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_9922_K0 : check design m_9922_K0 k_K0 timing = true := by decide +kernel

theorem Order_9922_K0 : decide (Order design m_9922_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_9922_K0 : decide (SilenceBefore design m_9922_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_9922_K0 : decide (SilenceAfter design m_9922_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_9922_K0 : decide (FiringBefore design m_9922_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_9922_K0 : decide (FiringAfter design m_9922_K0 k_K0) = true := by decide +kernel
theorem Timing_9922_K0 : decide (Timing design m_9922_K0 timing) = true := by decide +kernel

theorem premises_9922_K0 : Premises design m_9922_K0 k_K0 timing := check_sound check_9922_K0

theorem inverterRead_9922_K0 : InverterRead timing (absentRead m_9922_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9922_K0

theorem check_9922_K3 : check design m_9922_K3 k_K3 timing = true := by decide +kernel

theorem Order_9922_K3 : decide (Order design m_9922_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_9922_K3 : decide (SilenceBefore design m_9922_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_9922_K3 : decide (SilenceAfter design m_9922_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_9922_K3 : decide (FiringBefore design m_9922_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_9922_K3 : decide (FiringAfter design m_9922_K3 k_K3) = true := by decide +kernel
theorem Timing_9922_K3 : decide (Timing design m_9922_K3 timing) = true := by decide +kernel

theorem premises_9922_K3 : Premises design m_9922_K3 k_K3 timing := check_sound check_9922_K3

theorem inverterRead_9922_K3 : InverterRead timing (absentRead m_9922_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9922_K3

theorem StateBound_9922 : decide (StateBound design (85647 / 100000 : Rat) (45241 / 40000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Gate
