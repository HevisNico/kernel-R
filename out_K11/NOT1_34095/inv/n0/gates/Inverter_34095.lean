import InverterInstanceTiming

/-! The kernel gate of inverter instance 34095 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_34095_K0 : Measures := ⟨(24039 / 50000 : Rat), (391 / 800 : Rat), (96953 / 200000 : Rat), (797 / 200000 : Rat), (147 / 1000000 : Rat), (24063 / 500000 : Rat), (497 / 125000 : Rat), (6321 / 1000000 : Rat), (7157 / 1000000 : Rat), (188213 / 200000 : Rat), (1011 / 1000000 : Rat), (253 / 250000 : Rat), (51139 / 100000 : Rat), (193 / 1000 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_34095_K3 : Measures := ⟨(24039 / 50000 : Rat), (391 / 800 : Rat), (96953 / 200000 : Rat), (797 / 200000 : Rat), (147 / 1000000 : Rat), (24063 / 500000 : Rat), (497 / 125000 : Rat), (6321 / 1000000 : Rat), (7157 / 1000000 : Rat), (188213 / 200000 : Rat), (1011 / 1000000 : Rat), (253 / 250000 : Rat), (51139 / 100000 : Rat), (24 / 125 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_34095_K0 : check design m_34095_K0 k_K0 timing = true := by decide +kernel

theorem Order_34095_K0 : decide (Order design m_34095_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_34095_K0 : decide (SilenceBefore design m_34095_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_34095_K0 : decide (SilenceAfter design m_34095_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_34095_K0 : decide (FiringBefore design m_34095_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_34095_K0 : decide (FiringAfter design m_34095_K0 k_K0) = true := by decide +kernel
theorem Timing_34095_K0 : decide (Timing design m_34095_K0 timing) = true := by decide +kernel

theorem premises_34095_K0 : Premises design m_34095_K0 k_K0 timing := check_sound check_34095_K0

theorem inverterRead_34095_K0 : InverterRead timing (absentRead m_34095_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_34095_K0

theorem check_34095_K3 : check design m_34095_K3 k_K3 timing = true := by decide +kernel

theorem Order_34095_K3 : decide (Order design m_34095_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_34095_K3 : decide (SilenceBefore design m_34095_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_34095_K3 : decide (SilenceAfter design m_34095_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_34095_K3 : decide (FiringBefore design m_34095_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_34095_K3 : decide (FiringAfter design m_34095_K3 k_K3) = true := by decide +kernel
theorem Timing_34095_K3 : decide (Timing design m_34095_K3 timing) = true := by decide +kernel

theorem premises_34095_K3 : Premises design m_34095_K3 k_K3 timing := check_sound check_34095_K3

theorem inverterRead_34095_K3 : InverterRead timing (absentRead m_34095_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_34095_K3

theorem StateBound_34095 : decide (StateBound design (215661 / 250000 : Rat) (1233107 / 1000000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
