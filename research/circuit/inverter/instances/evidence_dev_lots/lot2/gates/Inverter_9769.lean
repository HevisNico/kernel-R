import InverterInstanceTiming

/-! The kernel gate of inverter instance 9769 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_9769_K0 : Measures := ⟨(48001 / 100000 : Rat), (48873 / 100000 : Rat), (48437 / 100000 : Rat), (109 / 25000 : Rat), (163 / 1000000 : Rat), (16527 / 500000 : Rat), (823 / 200000 : Rat), (7243 / 500000 : Rat), (1689 / 200000 : Rat), (465351 / 500000 : Rat), (63 / 62500 : Rat), (1009 / 1000000 : Rat), (520383 / 1000000 : Rat), (39 / 200 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_9769_K3 : Measures := ⟨(48001 / 100000 : Rat), (48873 / 100000 : Rat), (48437 / 100000 : Rat), (109 / 25000 : Rat), (163 / 1000000 : Rat), (16527 / 500000 : Rat), (823 / 200000 : Rat), (7243 / 500000 : Rat), (1689 / 200000 : Rat), (465351 / 500000 : Rat), (63 / 62500 : Rat), (1009 / 1000000 : Rat), (520383 / 1000000 : Rat), (97 / 500 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_9769_K0 : check design m_9769_K0 k_K0 timing = true := by decide +kernel

theorem Order_9769_K0 : decide (Order design m_9769_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_9769_K0 : decide (SilenceBefore design m_9769_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_9769_K0 : decide (SilenceAfter design m_9769_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_9769_K0 : decide (FiringBefore design m_9769_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_9769_K0 : decide (FiringAfter design m_9769_K0 k_K0) = true := by decide +kernel
theorem Timing_9769_K0 : decide (Timing design m_9769_K0 timing) = true := by decide +kernel

theorem premises_9769_K0 : Premises design m_9769_K0 k_K0 timing := check_sound check_9769_K0

theorem inverterRead_9769_K0 : InverterRead timing (absentRead m_9769_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9769_K0

theorem check_9769_K3 : check design m_9769_K3 k_K3 timing = true := by decide +kernel

theorem Order_9769_K3 : decide (Order design m_9769_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_9769_K3 : decide (SilenceBefore design m_9769_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_9769_K3 : decide (SilenceAfter design m_9769_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_9769_K3 : decide (FiringBefore design m_9769_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_9769_K3 : decide (FiringAfter design m_9769_K3 k_K3) = true := by decide +kernel
theorem Timing_9769_K3 : decide (Timing design m_9769_K3 timing) = true := by decide +kernel

theorem premises_9769_K3 : Premises design m_9769_K3 k_K3 timing := check_sound check_9769_K3

theorem inverterRead_9769_K3 : InverterRead timing (absentRead m_9769_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_9769_K3

theorem StateBound_9769 : decide (StateBound design (853239 / 1000000 : Rat) (602977 / 500000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
