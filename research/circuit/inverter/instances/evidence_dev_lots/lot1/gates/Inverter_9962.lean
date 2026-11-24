import InverterInstanceCheck

/-! The kernel gate of inverter instance 9962 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Gate

open LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_9962_K0 : Measures := ⟨(2399 / 5000 : Rat), (12219 / 25000 : Rat), (12107 / 25000 : Rat), (14 / 3125 : Rat), (71 / 500000 : Rat), (58687 / 1000000 : Rat), (2993 / 1000000 : Rat), (2703 / 250000 : Rat), (131 / 12500 : Rat), (975127 / 1000000 : Rat), (1037 / 1000000 : Rat), (519 / 500000 : Rat), (52949 / 100000 : Rat), (189 / 1000 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_9962_K3 : Measures := ⟨(2399 / 5000 : Rat), (12219 / 25000 : Rat), (12107 / 25000 : Rat), (14 / 3125 : Rat), (71 / 500000 : Rat), (58687 / 1000000 : Rat), (2993 / 1000000 : Rat), (2703 / 250000 : Rat), (131 / 12500 : Rat), (975127 / 1000000 : Rat), (1037 / 1000000 : Rat), (519 / 500000 : Rat), (52949 / 100000 : Rat), (47 / 250 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_9962_K0 : check design m_9962_K0 k_K0 timing = true := by decide +kernel

theorem Order_9962_K0 : decide (Order design m_9962_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_9962_K0 : decide (SilenceBefore design m_9962_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_9962_K0 : decide (SilenceAfter design m_9962_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_9962_K0 : decide (FiringBefore design m_9962_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_9962_K0 : decide (FiringAfter design m_9962_K0 k_K0) = true := by decide +kernel
theorem Timing_9962_K0 : decide (Timing design m_9962_K0 timing) = true := by decide +kernel

theorem premises_9962_K0 : Premises design m_9962_K0 k_K0 timing := check_sound check_9962_K0

theorem inverterRead_9962_K0 : InverterRead timing (absentRead m_9962_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9962_K0

theorem check_9962_K3 : check design m_9962_K3 k_K3 timing = true := by decide +kernel

theorem Order_9962_K3 : decide (Order design m_9962_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_9962_K3 : decide (SilenceBefore design m_9962_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_9962_K3 : decide (SilenceAfter design m_9962_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_9962_K3 : decide (FiringBefore design m_9962_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_9962_K3 : decide (FiringAfter design m_9962_K3 k_K3) = true := by decide +kernel
theorem Timing_9962_K3 : decide (Timing design m_9962_K3 timing) = true := by decide +kernel

theorem premises_9962_K3 : Premises design m_9962_K3 k_K3 timing := check_sound check_9962_K3

theorem inverterRead_9962_K3 : InverterRead timing (absentRead m_9962_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9962_K3

end LearnedCoincidence.MonotoneDNF.InverterInstance.Gate
