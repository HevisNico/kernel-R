import InverterInstanceTiming

/-! The kernel gate of inverter instance 6212 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_6212_K0 : Measures := ⟨(24023 / 50000 : Rat), (48873 / 100000 : Rat), (96919 / 200000 : Rat), (827 / 200000 : Rat), (37 / 250000 : Rat), (40819 / 1000000 : Rat), (4259 / 1000000 : Rat), (4443 / 500000 : Rat), (537 / 125000 : Rat), (241247 / 250000 : Rat), (1011 / 1000000 : Rat), (253 / 250000 : Rat), (515743 / 1000000 : Rat), (39 / 200 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_6212_K3 : Measures := ⟨(24023 / 50000 : Rat), (48873 / 100000 : Rat), (96919 / 200000 : Rat), (827 / 200000 : Rat), (37 / 250000 : Rat), (40819 / 1000000 : Rat), (4259 / 1000000 : Rat), (4443 / 500000 : Rat), (537 / 125000 : Rat), (241247 / 250000 : Rat), (1011 / 1000000 : Rat), (253 / 250000 : Rat), (515743 / 1000000 : Rat), (97 / 500 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_6212_K0 : check design m_6212_K0 k_K0 timing = true := by decide +kernel

theorem Order_6212_K0 : decide (Order design m_6212_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_6212_K0 : decide (SilenceBefore design m_6212_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_6212_K0 : decide (SilenceAfter design m_6212_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_6212_K0 : decide (FiringBefore design m_6212_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_6212_K0 : decide (FiringAfter design m_6212_K0 k_K0) = true := by decide +kernel
theorem Timing_6212_K0 : decide (Timing design m_6212_K0 timing) = true := by decide +kernel

theorem premises_6212_K0 : Premises design m_6212_K0 k_K0 timing := check_sound check_6212_K0

theorem inverterRead_6212_K0 : InverterRead timing (absentRead m_6212_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6212_K0

theorem check_6212_K3 : check design m_6212_K3 k_K3 timing = true := by decide +kernel

theorem Order_6212_K3 : decide (Order design m_6212_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_6212_K3 : decide (SilenceBefore design m_6212_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_6212_K3 : decide (SilenceAfter design m_6212_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_6212_K3 : decide (FiringBefore design m_6212_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_6212_K3 : decide (FiringAfter design m_6212_K3 k_K3) = true := by decide +kernel
theorem Timing_6212_K3 : decide (Timing design m_6212_K3 timing) = true := by decide +kernel

theorem premises_6212_K3 : Premises design m_6212_K3 k_K3 timing := check_sound check_6212_K3

theorem inverterRead_6212_K3 : InverterRead timing (absentRead m_6212_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6212_K3

theorem StateBound_6212 : decide (StateBound design (221141 / 250000 : Rat) (4853 / 4000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
