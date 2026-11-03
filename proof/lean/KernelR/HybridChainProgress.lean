import KernelR.HybridFiniteProgress
import KernelR.HybridUniversalBirthCadenceChain
import KernelR.HybridPrefixBeforeFlow
import KernelR.HybridQuietFlowExistence

/-!
# Progress for the constructed finite-chain protocol

The finite complete witness discharges the reference-existence premise.
After its source queue is exhausted, actual quiet flows extend it to any
later horizon. Combining this construction with finite progress gives a
strictly later continuation of every competing finite execution, including
those whose endpoint is already beyond the original protocol horizon.
Unbounded time after input exhaustion does not mean infinitely many FIREs.
-/
namespace KernelR.Hybrid

/-- Every horizon at or after birth has an actual complete finite witness.
Earlier horizons cut the existing witness; later ones append a quiet flow.
-/
theorem ConstructedBirthCadenceChain.complete_horizon
    {n θ bornCells K sigma centre delay T}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (H : ℝ) (afterBirth : (familyPreparationBornSource bornCells K).time ≤ H) :
    HasCompleteExecution θ chain.router (familyPreparationBornSource bornCells K) H := by
  by_cases earlier : H < T
  · obtain ⟨v, cut, _, complete⟩ :=
      chain.execution.complete_prefix_at H afterBirth (by rw [chain.date]; exact earlier)
    exact ⟨v, cut, complete⟩
  · by_cases equal : H = T
    · subst H
      exact ⟨chain.final, chain.execution, chain.complete⟩
    · have later : T < H :=
        lt_of_le_of_ne (le_of_not_gt earlier) (Ne.symm equal)
      obtain ⟨quiet, complete⟩ := quiet_complete_exists (θ := θ)
        (route := chain.router) chain.final
        (by rw [chain.date]; exact later)
        (fun i => (chain.ready i).ready)
        (fun i p => ((chain.ready i).auxiliary p).1)
        chain.raw_none
        (by intro i; rw [chain.charge i]; norm_num)
        (by
          intro i p
          have bound := ((chain.ready i).auxiliary p).2.2
          linarith)
        (by intro d member; rw [chain.pending] at member; simp at member)
      exact ⟨quietAt chain.final H, chain.execution.append quiet, complete⟩

/-- Every actual finite competing execution admits a complete continuation
to each later chosen horizon. Completeness of that prefix is not a premise.
-/
theorem ConstructedBirthCadenceChain.extend_execution
    {n θ bornCells K sigma centre delay T ε}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (box : PhysicalBox θ ε) {u}
    (initialRun : Execution θ chain.router (familyPreparationBornSource bornCells K) u)
    (H : ℝ) (later : u.time ≤ H) :
    ∃ v, ∃ tail : Execution θ chain.router u v,
      CompleteThrough (initialRun.append tail) H := by
  apply initialRun.extend_complete box
    (chain.preparation.source_birth.physical_invariant box)
    (chain.complete_horizon H (initialRun.time_monotone.trans later)) later

/-- A strict time continuation exists from every reachable finite endpoint.
The unit here is the model time unit; no externally triggered pulse is added.
-/
theorem ConstructedBirthCadenceChain.progress_one_time_unit
    {n θ bornCells K sigma centre delay T ε}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (box : PhysicalBox θ ε) {u}
    (initialRun : Execution θ chain.router (familyPreparationBornSource bornCells K) u) :
    ∃ v, ∃ tail : Execution θ chain.router u v,
      v.time = u.time + 1 ∧ CompleteThrough (initialRun.append tail) (u.time + 1) := by
  obtain ⟨v, tail, complete⟩ := chain.extend_execution box initialRun (u.time + 1) (by linarith)
  exact ⟨v, tail, complete.1, complete⟩

/-- Maximality at the original protocol horizon implies its previously
proved physical outcome; terminal saturation is now a derived property.
-/
theorem ConstructedBirthCadenceChain.maximal_outcome
    {n θ bornCells K sigma centre delay T ε}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (box : PhysicalBox θ ε) {u}
    (initialRun : Execution θ chain.router (familyPreparationBornSource bornCells K) u)
    (maximal : RightMaximalThrough θ chain.router u T) :
    UniversalCadenceOutcome θ bornCells K T u initialRun.emissionTimes
      initialRun.ledger.emissions.length := by
  have complete := initialRun.maximal_complete box
    (chain.preparation.source_birth.physical_invariant box)
    ⟨chain.final, chain.execution, chain.complete⟩ maximal
  exact chain.every_complete_outcome box initialRun complete

#print axioms ConstructedBirthCadenceChain.progress_one_time_unit
#print axioms ConstructedBirthCadenceChain.maximal_outcome

end KernelR.Hybrid
