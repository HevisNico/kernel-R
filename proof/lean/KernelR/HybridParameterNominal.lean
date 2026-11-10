import KernelR.HybridParameterExecution
import KernelR.HybridUniversalExecution

/-! The nominal specialization preserves completion and ordered emissions
in both execution interfaces. -/
namespace KernelR.Hybrid

theorem ParameterJump.emissions_toNominal {n θ route s u}
    (j : @ParameterJump n θ route s u) (nominal : NominalThresholds θ) :
    (j.toNominal nominal).ledger.emissions = j.emissions := by
  cases j <;> rfl

theorem ParameterExecution.emissions_toNominal {n θ route s u}
    (e : @ParameterExecution n θ route s u) (nominal : NominalThresholds θ) :
    (e.toNominal nominal).ledger.emissions = e.emissions := by
  induction e with
  | nil => rfl
  | cons m rest ih =>
    cases m with
    | flow f =>
      simpa [ParameterExecution.toNominal, ParameterExecution.emissions, Execution.ledger, Move.ledger,
        Flow.ledger, Ledger.add] using ih
    | jump j =>
      simp [ParameterExecution.toNominal, ParameterExecution.emissions, Execution.ledger, Move.ledger,
        Ledger.add, ParameterJump.emissions_toNominal, ih]

/-- The parameterized interface recovers the every-complete-run result
at nominal levels, with exact per-cell FIRE dates. -/
theorem ParameterExecution.nominal_observational_unique {n θ ε route s u v T}
    (e : @ParameterExecution n θ route s u) (f : ParameterExecution θ route s v)
    (nominal : NominalThresholds θ) (box : PhysicalBox θ ε) (initial : PhysicalInvariant θ s)
    (he : ParameterCompleteThrough e T) (hf : ParameterCompleteThrough f T) :
    u.ObservationalEq v ∧ ∀ i, e.emissionTimes i = f.emissionTimes i := by
  have he' := (e.complete_nominal_iff nominal).1 he
  have hf' := (f.complete_nominal_iff nominal).1 hf
  refine ⟨((e.toNominal nominal).observational_unique (f.toNominal nominal) box initial he' hf').1, ?_⟩
  intro i
  have times := (e.toNominal nominal).emissionTimes_unique (f.toNominal nominal) box initial he' hf' i
  simpa only [Execution.emissionTimes, ParameterExecution.emissionTimes, emissions_toNominal] using times

end KernelR.Hybrid
