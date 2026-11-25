import InverterInstanceTiming

/-! The kernel gate of inverter instance 6173 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_6173_K0 : Measures := ⟨(9629 / 20000 : Rat), (391 / 800 : Rat), (4851 / 10000 : Rat), (73 / 20000 : Rat), (149 / 1000000 : Rat), (41187 / 500000 : Rat), (1083 / 250000 : Rat), (10107 / 500000 : Rat), (13631 / 500000 : Rat), (934419 / 1000000 : Rat), (499 / 500000 : Rat), (999 / 1000000 : Rat), (501033 / 1000000 : Rat), (177 / 1000 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_6173_K3 : Measures := ⟨(9629 / 20000 : Rat), (391 / 800 : Rat), (4851 / 10000 : Rat), (73 / 20000 : Rat), (149 / 1000000 : Rat), (41187 / 500000 : Rat), (1083 / 250000 : Rat), (10107 / 500000 : Rat), (13631 / 500000 : Rat), (934419 / 1000000 : Rat), (499 / 500000 : Rat), (999 / 1000000 : Rat), (501033 / 1000000 : Rat), (22 / 125 : Rat)⟩
def k_K3 : Allowance := ⟨(2011 / 1000000 : Rat), (2353 / 1000000 : Rat)⟩

theorem check_6173_K0 : check design m_6173_K0 k_K0 timing = true := by decide +kernel

theorem Order_6173_K0 : decide (Order design m_6173_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_6173_K0 : decide (SilenceBefore design m_6173_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_6173_K0 : decide (SilenceAfter design m_6173_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_6173_K0 : decide (FiringBefore design m_6173_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_6173_K0 : decide (FiringAfter design m_6173_K0 k_K0) = true := by decide +kernel
theorem Timing_6173_K0 : decide (Timing design m_6173_K0 timing) = true := by decide +kernel

theorem premises_6173_K0 : Premises design m_6173_K0 k_K0 timing := check_sound check_6173_K0

theorem inverterRead_6173_K0 : InverterRead timing (absentRead m_6173_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6173_K0

theorem check_6173_K3 : check design m_6173_K3 k_K3 timing = true := by decide +kernel

theorem Order_6173_K3 : decide (Order design m_6173_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_6173_K3 : decide (SilenceBefore design m_6173_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_6173_K3 : decide (SilenceAfter design m_6173_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_6173_K3 : decide (FiringBefore design m_6173_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_6173_K3 : decide (FiringAfter design m_6173_K3 k_K3) = true := by decide +kernel
theorem Timing_6173_K3 : decide (Timing design m_6173_K3 timing) = true := by decide +kernel

theorem premises_6173_K3 : Premises design m_6173_K3 k_K3 timing := check_sound check_6173_K3

theorem inverterRead_6173_K3 : InverterRead timing (absentRead m_6173_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_6173_K3

theorem StateBound_6173 : decide (StateBound design (428301 / 500000 : Rat) (1263933 / 1000000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
