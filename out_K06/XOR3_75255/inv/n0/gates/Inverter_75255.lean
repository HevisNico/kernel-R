import InverterInstanceTiming

/-! The kernel gate of inverter instance 75255 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_75255_K0 : Measures := ⟨(48037 / 100000 : Rat), (24439 / 50000 : Rat), (19383 / 40000 : Rat), (841 / 200000 : Rat), (79 / 500000 : Rat), (39009 / 1000000 : Rat), (1861 / 500000 : Rat), (22557 / 1000000 : Rat), (9733 / 1000000 : Rat), (939509 / 1000000 : Rat), (1019 / 1000000 : Rat), (51 / 50000 : Rat), (10389 / 20000 : Rat), (191 / 1000 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_75255_K3 : Measures := ⟨(48037 / 100000 : Rat), (24439 / 50000 : Rat), (19383 / 40000 : Rat), (841 / 200000 : Rat), (79 / 500000 : Rat), (39009 / 1000000 : Rat), (1861 / 500000 : Rat), (22557 / 1000000 : Rat), (9733 / 1000000 : Rat), (939509 / 1000000 : Rat), (1019 / 1000000 : Rat), (51 / 50000 : Rat), (10389 / 20000 : Rat), (19 / 100 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_75255_K0 : check design m_75255_K0 k_K0 timing = true := by decide +kernel

theorem Order_75255_K0 : decide (Order design m_75255_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_75255_K0 : decide (SilenceBefore design m_75255_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_75255_K0 : decide (SilenceAfter design m_75255_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_75255_K0 : decide (FiringBefore design m_75255_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_75255_K0 : decide (FiringAfter design m_75255_K0 k_K0) = true := by decide +kernel
theorem Timing_75255_K0 : decide (Timing design m_75255_K0 timing) = true := by decide +kernel

theorem premises_75255_K0 : Premises design m_75255_K0 k_K0 timing := check_sound check_75255_K0

theorem inverterRead_75255_K0 : InverterRead timing (absentRead m_75255_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_75255_K0

theorem check_75255_K3 : check design m_75255_K3 k_K3 timing = true := by decide +kernel

theorem Order_75255_K3 : decide (Order design m_75255_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_75255_K3 : decide (SilenceBefore design m_75255_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_75255_K3 : decide (SilenceAfter design m_75255_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_75255_K3 : decide (FiringBefore design m_75255_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_75255_K3 : decide (FiringAfter design m_75255_K3 k_K3) = true := by decide +kernel
theorem Timing_75255_K3 : decide (Timing design m_75255_K3 timing) = true := by decide +kernel

theorem premises_75255_K3 : Premises design m_75255_K3 k_K3 timing := check_sound check_75255_K3

theorem inverterRead_75255_K3 : InverterRead timing (absentRead m_75255_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_75255_K3

theorem StateBound_75255 : decide (StateBound design (6889 / 8000 : Rat) (1212853 / 1000000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
