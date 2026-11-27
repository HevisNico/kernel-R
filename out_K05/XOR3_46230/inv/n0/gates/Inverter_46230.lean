import InverterInstanceTiming

/-! The kernel gate of inverter instance 46230 (SKY130 tt_mm, its seed), written by
research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of
the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Instances

open KernelR.Circuit.Gate LearnedCoincidence.MonotoneDNF.InverterInstance

def design : Design := ⟨(1 / 4 : Rat), (3 / 10 : Rat), (3 / 10 : Rat), (9 / 2 : Rat), (1 : Rat), (9 / 10 : Rat)⟩
def timing : InverterTiming := ⟨(1 / 4 : Rat), (2 / 5 : Rat), (13 / 20 : Rat)⟩

def m_46230_K0 : Measures := ⟨(1923 / 4000 : Rat), (48873 / 100000 : Rat), (24237 / 50000 : Rat), (399 / 100000 : Rat), (69 / 500000 : Rat), (41341 / 1000000 : Rat), (2889 / 1000000 : Rat), (6137 / 500000 : Rat), (11813 / 1000000 : Rat), (60231 / 62500 : Rat), (1017 / 1000000 : Rat), (509 / 500000 : Rat), (102469 / 200000 : Rat), (24 / 125 : Rat)⟩
def k_K0 : Allowance := ⟨(0 : Rat), (0 : Rat)⟩

def m_46230_K3 : Measures := ⟨(1923 / 4000 : Rat), (48873 / 100000 : Rat), (24237 / 50000 : Rat), (399 / 100000 : Rat), (69 / 500000 : Rat), (41341 / 1000000 : Rat), (2889 / 1000000 : Rat), (6137 / 500000 : Rat), (11813 / 1000000 : Rat), (60231 / 62500 : Rat), (1017 / 1000000 : Rat), (509 / 500000 : Rat), (102469 / 200000 : Rat), (191 / 1000 : Rat)⟩
def k_K3 : Allowance := ⟨(1253 / 500000 : Rat), (2597 / 1000000 : Rat)⟩

theorem check_46230_K0 : check design m_46230_K0 k_K0 timing = true := by decide +kernel

theorem Order_46230_K0 : decide (Order design m_46230_K0 k_K0) = true := by decide +kernel
theorem SilenceBefore_46230_K0 : decide (SilenceBefore design m_46230_K0 k_K0) = true := by decide +kernel
theorem SilenceAfter_46230_K0 : decide (SilenceAfter design m_46230_K0 k_K0) = true := by decide +kernel
theorem FiringBefore_46230_K0 : decide (FiringBefore design m_46230_K0 k_K0) = true := by decide +kernel
theorem FiringAfter_46230_K0 : decide (FiringAfter design m_46230_K0 k_K0) = true := by decide +kernel
theorem Timing_46230_K0 : decide (Timing design m_46230_K0 timing) = true := by decide +kernel

theorem premises_46230_K0 : Premises design m_46230_K0 k_K0 timing := check_sound check_46230_K0

theorem inverterRead_46230_K0 : InverterRead timing (absentRead m_46230_K0) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_46230_K0

theorem check_46230_K3 : check design m_46230_K3 k_K3 timing = true := by decide +kernel

theorem Order_46230_K3 : decide (Order design m_46230_K3 k_K3) = true := by decide +kernel
theorem SilenceBefore_46230_K3 : decide (SilenceBefore design m_46230_K3 k_K3) = true := by decide +kernel
theorem SilenceAfter_46230_K3 : decide (SilenceAfter design m_46230_K3 k_K3) = true := by decide +kernel
theorem FiringBefore_46230_K3 : decide (FiringBefore design m_46230_K3 k_K3) = true := by decide +kernel
theorem FiringAfter_46230_K3 : decide (FiringAfter design m_46230_K3 k_K3) = true := by decide +kernel
theorem Timing_46230_K3 : decide (Timing design m_46230_K3 timing) = true := by decide +kernel

theorem premises_46230_K3 : Premises design m_46230_K3 k_K3 timing := check_sound check_46230_K3

theorem inverterRead_46230_K3 : InverterRead timing (absentRead m_46230_K3) ∧ InverterRead timing presentRead :=
  inverterRead_of_premises premises_46230_K3

theorem StateBound_46230 : decide (StateBound design (88331 / 100000 : Rat) (610667 / 500000 : Rat)) = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.InverterInstance.Instances
