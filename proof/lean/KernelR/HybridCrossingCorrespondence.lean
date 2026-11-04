import KernelR.HybridCrossingExecution
import KernelR.HybridWeakNativeRefinement
import KernelR.HybridUniversalBirthCadenceChain

/-! Correspondence of threshold-contact and geometric upward-crossing
semantics on the constructed protocol. The competing model run supplies
only its own ODE history and geometric terminal saturation. -/
namespace KernelR.Hybrid

theorem FiniteCausalChainData.strict_causal_router (data : FiniteCausalChainData)
    (depth : ℕ) : StrictCausalRouter (data.route depth) := by
  induction depth with
  | zero => intro i t token member; simp [FiniteCausalChainData.route] at member
  | succ depth ih =>
    intro i t token member
    cases i using Fin.cases with
    | zero => simp [FiniteCausalChainData.route, prependRouted] at member
    | succ i =>
      change token ∈ (data.route depth i t).map Delivery.succ ++
        (data.contacts depth i t).map Delivery.head at member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨original, present, rfl⟩ := List.mem_map.mp old
        exact ih i t original present
      · obtain ⟨original, present, rfl⟩ := List.mem_map.mp added
        exact data.strict_contacts depth i t original present

theorem ConstructedBirthCadenceChain.strict_causal_router
    {n θ bornCells K sigma centre delay T}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T) :
    StrictCausalRouter chain.router :=
  (chain.preparation.cadenceData delay T chain.delay_positive).strict_causal_router n

/-- No native trace, contact certificate, calendar or stronger terminal
saturation is supplied by the competing crossing execution. Its exact weak
moves are proved to be native moves before the common horizon. -/
theorem CrossingExecution.toNative_complete {n θ ε route s u v T}
    (candidate : @CrossingExecution n θ route s u)
    (reference : Execution θ route s v) (routing : StrictCausalRouter route)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (initial : InitiallyBelowReady s) (complete : CompleteThrough reference T)
    (positive : reference.ContactsTransversal)
    (modelComplete : CrossingCompleteThrough candidate T) :
    ∃ native : Execution θ route s u,
      native.toWeak = candidate.execution ∧ CompleteThrough native T := by
  obtain ⟨native, same⟩ := candidate.execution.toNative_of_transverse_completion
    reference routing box physical complete positive (by rw [modelComplete.1])
  have weakComplete := modelComplete.toWeak_of_native candidate native same initial box physical
  have observed := (Execution.observational_unique_weak box reference candidate.execution
    physical complete positive weakComplete).1
  exact ⟨native, same, modelComplete.1,
    observational_no_jump observed complete.2.1, modelComplete.2.2⟩

namespace ConstructedBirthCadenceChain
variable {n θ bornCells K sigma centre delay T ε}
  (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)

/-- The constructed history itself realizes actual left approaches and
incoming-mode ODE crossings, with the original birth state and router. -/
noncomputable def crossingExecution (box : PhysicalBox θ ε) :
    CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) chain.final :=
  chain.execution.toCrossingFromBirth chain.source_birth box chain.contacts_transversal

theorem crossingExecution_complete (box : PhysicalBox θ ε) :
    CrossingCompleteThrough (chain.crossingExecution box) T :=
  chain.complete.toCrossing chain.execution chain.source_birth.initiallyBelowReady box
    (chain.source_birth.physical_invariant box) chain.contacts_transversal

/-- Every geometrically complete model history refines to a complete native
history with exactly the same paths and physical jump occurrences. -/
theorem crossing_refines_native (box : PhysicalBox θ ε) {u}
    (candidate : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) u)
    (complete : CrossingCompleteThrough candidate T) :
    ∃ native : Execution θ chain.router (familyPreparationBornSource bornCells K) u,
      native.toWeak = candidate.execution ∧ CompleteThrough native T :=
  candidate.toNative_complete chain.execution chain.strict_causal_router box
    (chain.source_birth.physical_invariant box) chain.source_birth.initiallyBelowReady
    chain.complete chain.contacts_transversal complete

/-- Equality of the physical endpoint and each ordered FIRE list holds for
all complete crossing executions, independently of simultaneous event order. -/
theorem every_crossing_complete (box : PhysicalBox θ ε) {u}
    (candidate : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) u)
    (complete : CrossingCompleteThrough candidate T) :
    chain.final.ObservationalEq u ∧
      ∀ i, candidate.execution.emissionTimes i = chain.execution.emissionTimes i := by
  obtain ⟨native, same, nativeComplete⟩ := chain.crossing_refines_native box candidate complete
  obtain ⟨endpoint, times⟩ := chain.all_complete box u native nativeComplete
  refine ⟨endpoint, ?_⟩
  intro i
  rw [← same]
  simpa only [WeakExecution.emissionTimes, Execution.emissionTimes, Execution.toWeak_ledger] using times i

/-- All previously proved terminal learning, recovery and exact finite-chain
counts transfer to the model's actual endpoint and emitted lists. -/
theorem crossing_outcome (box : PhysicalBox θ ε) {u}
    (candidate : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) u)
    (complete : CrossingCompleteThrough candidate T) :
    UniversalCadenceOutcome θ bornCells K T u candidate.execution.emissionTimes
      candidate.execution.ledger.emissions.length := by
  obtain ⟨native, same, nativeComplete⟩ := chain.crossing_refines_native box candidate complete
  have result := chain.every_complete_outcome box native nativeComplete
  rw [← same]
  simpa only [Execution.toWeak_emissionTimes, Execution.toWeak_ledger] using result

/-- Conversely each complete native outcome has a geometrically valid
crossing representative, up to the same physical observations and FIRE lists.
This does not identify simultaneous-event linearizations syntactically. -/
theorem native_has_crossing_representative (box : PhysicalBox θ ε) {u}
    (native : Execution θ chain.router (familyPreparationBornSource bornCells K) u)
    (complete : CompleteThrough native T) :
    ∃ v, ∃ model : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) v,
      CrossingCompleteThrough model T ∧ u.ObservationalEq v ∧
      ∀ i, native.emissionTimes i = model.execution.emissionTimes i := by
  obtain ⟨observed, times⟩ := chain.all_complete box u native complete
  refine ⟨chain.final, chain.crossingExecution box, chain.crossingExecution_complete box,
    observed.symm, ?_⟩
  intro i
  simpa only [crossingExecution, Execution.toCrossingFromBirth, Execution.toCrossing,
    WeakExecution.emissionTimes, Execution.emissionTimes, Execution.toWeak_ledger] using times i

end ConstructedBirthCadenceChain

#print axioms CrossingExecution.toNative_complete
#print axioms ConstructedBirthCadenceChain.every_crossing_complete
#print axioms ConstructedBirthCadenceChain.native_has_crossing_representative
end KernelR.Hybrid
