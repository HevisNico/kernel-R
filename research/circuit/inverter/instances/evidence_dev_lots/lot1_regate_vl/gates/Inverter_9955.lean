import InverterInstanceCheck

/-! The kernel gate of inverter instance 9955 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Gate

open LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_9955_K0 : Measures := ⟨(1927 / 4000 : Rat), (24439 / 50000 : Rat), (97053 / 200000 : Rat), (703 / 200000 : Rat), (79 / 500000 : Rat), (13629 / 125000 : Rat), (2629 / 1000000 : Rat), (529 / 62500 : Rat), (7477 / 1000000 : Rat), (930649 / 1000000 : Rat), (127 / 125000 : Rat), (1017 / 1000000 : Rat), (7896 / 15625 : Rat), (89 / 500 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_9955_K3 : Measures := ⟨(1927 / 4000 : Rat), (24439 / 50000 : Rat), (97053 / 200000 : Rat), (703 / 200000 : Rat), (79 / 500000 : Rat), (13629 / 125000 : Rat), (2629 / 1000000 : Rat), (529 / 62500 : Rat), (7477 / 1000000 : Rat), (930649 / 1000000 : Rat), (127 / 125000 : Rat), (1017 / 1000000 : Rat), (7896 / 15625 : Rat), (177 / 1000 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_9955_K0 : check design m_9955_K0 k_K0 timing = true := by decide +kernel

theorem Order_9955_K0 : decide (Order design m_9955_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_9955_K0 : decide (SilenceBefore design m_9955_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_9955_K0 : decide (SilenceAfter design m_9955_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_9955_K0 : decide (FiringBefore design m_9955_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_9955_K0 : decide (FiringAfter design m_9955_K0 k_K0) = true := by decide +kernel
theorem Timing_9955_K0 : decide (Timing design m_9955_K0 timing) = true := by decide +kernel

theorem premises_9955_K0 : Premises design m_9955_K0 k_K0 timing := check_sound check_9955_K0

theorem inverterRead_9955_K0 : InverterRead timing (absentRead m_9955_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9955_K0

theorem check_9955_K3 : check design m_9955_K3 k_K3 timing = true := by decide +kernel

theorem Order_9955_K3 : decide (Order design m_9955_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_9955_K3 : decide (SilenceBefore design m_9955_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_9955_K3 : decide (SilenceAfter design m_9955_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_9955_K3 : decide (FiringBefore design m_9955_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_9955_K3 : decide (FiringAfter design m_9955_K3 k_K3) = true := by decide +kernel
theorem Timing_9955_K3 : decide (Timing design m_9955_K3 timing) = true := by decide +kernel

theorem premises_9955_K3 : Premises design m_9955_K3 k_K3 timing := check_sound check_9955_K3

theorem inverterRead_9955_K3 : InverterRead timing (absentRead m_9955_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9955_K3

theorem StateBound_9955 : decide (StateBound design (8531 / 10000 : Rat) (1290599 / 1000000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Gate
