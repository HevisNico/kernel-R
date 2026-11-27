import InverterInstanceTiming

/-! The kernel gate of inverter instance 99508 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_99508_K0 : Measures := ⟨(48079 / 100000 : Rat), (24437 / 50000 : Rat), (96953 / 200000 : Rat), (159 / 40000 : Rat), (31 / 200000 : Rat), (8519 / 200000 : Rat), (1417 / 200000 : Rat), (14009 / 1000000 : Rat), (1401 / 500000 : Rat), (9701 / 10000 : Rat), (1023 / 1000000 : Rat), (16 / 15625 : Rat), (514431 / 1000000 : Rat), (97 / 500 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_99508_K3 : Measures := ⟨(48079 / 100000 : Rat), (24437 / 50000 : Rat), (96953 / 200000 : Rat), (159 / 40000 : Rat), (31 / 200000 : Rat), (8519 / 200000 : Rat), (1417 / 200000 : Rat), (14009 / 1000000 : Rat), (1401 / 500000 : Rat), (9701 / 10000 : Rat), (1023 / 1000000 : Rat), (16 / 15625 : Rat), (514431 / 1000000 : Rat), (193 / 1000 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_99508_K0 : check design m_99508_K0 k_K0 timing = true := by decide +kernel

theorem Order_99508_K0 : decide (Order design m_99508_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_99508_K0 : decide (SilenceBefore design m_99508_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_99508_K0 : decide (SilenceAfter design m_99508_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_99508_K0 : decide (FiringBefore design m_99508_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_99508_K0 : decide (FiringAfter design m_99508_K0 k_K0) = true := by decide +kernel
theorem Timing_99508_K0 : decide (Timing design m_99508_K0 timing) = true := by decide +kernel

theorem premises_99508_K0 : Premises design m_99508_K0 k_K0 timing := check_sound check_99508_K0

theorem inverterRead_99508_K0 : InverterRead timing (absentRead m_99508_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_99508_K0

theorem check_99508_K3 : check design m_99508_K3 k_K3 timing = true := by decide +kernel

theorem Order_99508_K3 : decide (Order design m_99508_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_99508_K3 : decide (SilenceBefore design m_99508_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_99508_K3 : decide (SilenceAfter design m_99508_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_99508_K3 : decide (FiringBefore design m_99508_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_99508_K3 : decide (FiringAfter design m_99508_K3 k_K3) = true := by decide +kernel
theorem Timing_99508_K3 : decide (Timing design m_99508_K3 timing) = true := by decide +kernel

theorem premises_99508_K3 : Premises design m_99508_K3 k_K3 timing := check_sound check_99508_K3

theorem inverterRead_99508_K3 : InverterRead timing (absentRead m_99508_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_99508_K3

theorem StateBound_99508 : decide (StateBound design (55571 / 62500 : Rat) (48909 / 40000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
