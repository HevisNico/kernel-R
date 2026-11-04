import KernelR.HybridCrossingCorrespondence

/-! The universal finite-chain protocol in genuine upward-crossing semantics.
Birth, parameter, source, wire and budget inputs are unchanged. -/
namespace KernelR.Hybrid

def ConstructedBirthCadenceChain.AllCrossingComplete
    {n θ bornCells K sigma centre delay T}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T) : Prop :=
  ∀ u (model : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) u),
    CrossingCompleteThrough model T →
      chain.final.ObservationalEq u ∧
        ∀ i, model.execution.emissionTimes i = chain.execution.emissionTimes i

def ConstructedIndexedBirthCadenceChain.AllCrossingCompleteErrors
    {n θ bornCells K sigma centre error T}
    (chain : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T) : Prop :=
  ∀ u (model : CrossingExecution θ chain.chain.router (familyPreparationBornSource bornCells K) u),
    CrossingCompleteThrough model T → ∀ (j : ℕ) (hj : j < n) (k : ℕ)
      (hk : k < ((model.execution.emissionTimes (indexedCadenceSender n j hj)).drop
        (finiteChainPreparationCount n (indexedCadenceSender n j hj))).length),
      chain.delay j ((model.execution.emissionTimes (indexedCadenceSender n j hj)).drop
        (finiteChainPreparationCount n (indexedCadenceSender n j hj)))[k] = centre j + error j k

theorem ConstructedIndexedBirthCadenceChain.all_crossing_complete_errors
    {n θ bornCells K sigma centre error T ε}
    (chain : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T)
    (box : PhysicalBox θ ε) : chain.AllCrossingCompleteErrors := by
  intro u model complete
  obtain ⟨native, same, nativeComplete⟩ := chain.chain.crossing_refines_native box model complete
  have result := chain.all_complete_errors box u native nativeComplete
  rw [← same]
  simpa only [Execution.toWeak_emissionTimes] using result

namespace CrossingChainHeadline

/-- A genuine crossing witness exists; every complete model execution has
the same physical endpoint, ordered FIRE times and prescribed wire errors.
No execution, slope certificate or crossing premise is a protocol input. -/
theorem every_finite_chain_every_crossing_execution {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q = .ready)
    (hqueue : ∀ i, (bornCells i).pending = sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (error : ℕ → ℕ → ℝ)
    (hK : 4 * (n+1) + 12 ≤ K) (hsigma : ∀ j, 0 ≤ sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n ≤ 3/20)
    (hcentre : ∀ j, j < n → (3/10 : ℝ) + sigma j ≤ centre j ∧ centre j ≤ 2/5 - sigma j)
    (herror : ∀ j, j < n → ∀ i, -sigma j ≤ error j i ∧ error j i ≤ sigma j) :
    ∃ chain : ConstructedIndexedBirthCadenceChain θ bornCells K sigma centre error
        (cadenceChainTerminal n K),
      (∃ model : CrossingExecution θ chain.chain.router
          (familyPreparationBornSource bornCells K) chain.chain.final,
        CrossingCompleteThrough model (cadenceChainTerminal n K)) ∧
      chain.chain.AllCrossingComplete ∧ chain.AllCrossingCompleteErrors := by
  obtain ⟨chain⟩ := indexed_birth_cadence_chain_exists hborn hb ha hqueue sigma centre error
    hK hsigma hbudget hcentre herror
  exact ⟨chain, ⟨chain.chain.crossingExecution hb, chain.chain.crossingExecution_complete hb⟩,
    (fun _ model complete => chain.chain.every_crossing_complete hb model complete),
    chain.all_crossing_complete_errors hb⟩

theorem terminal_state_and_counts {n θ bornCells K sigma centre error T ε}
    (chain : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T)
    (box : PhysicalBox θ ε) {u}
    (model : CrossingExecution θ chain.chain.router (familyPreparationBornSource bornCells K) u)
    (complete : CrossingCompleteThrough model T) :
    UniversalCadenceOutcome θ bornCells K T u model.execution.emissionTimes
      model.execution.ledger.emissions.length :=
  chain.chain.crossing_outcome box model complete

#print axioms every_finite_chain_every_crossing_execution
#print axioms terminal_state_and_counts
end CrossingChainHeadline
end KernelR.Hybrid
