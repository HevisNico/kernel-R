import KernelR.HybridUniversalBirthCadenceChain

/-! Universal finite-chain headline. A physical witness exists for each
admissible input/error family, and every complete finite execution from the
same birth state with its fixed router has the stated actual observations.
This does not quantify over stopped prefixes or infinite maximal runs. -/
namespace KernelR.Hybrid.UniversalChainHeadline

theorem every_finite_chain_every_complete_execution {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ→ℝ) (error : ℕ→ℕ→ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ i, -sigma j≤error j i ∧ error j i≤sigma j) :
    ∃ c : ConstructedIndexedBirthCadenceChain θ bornCells K sigma centre error (cadenceChainTerminal n K),
      c.chain.AllComplete ∧ c.AllCompleteErrors := by
  obtain ⟨c⟩ := indexed_birth_cadence_chain_exists hborn hb ha hqueue sigma centre error
    hK hsigma hbudget hcentre herror
  exact ⟨c,c.chain.all_complete hb,c.all_complete_errors hb⟩

variable {n θ bornCells K sigma centre error T ε}
  (c : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T)

theorem terminal_state_and_counts (hb : PhysicalBox θ ε) {u : Snapshot (n+1)}
    (e : Execution θ c.chain.router (familyPreparationBornSource bornCells K) u)
    (hc : CompleteThrough e T) :
    UniversalCadenceOutcome θ bornCells K T u e.emissionTimes e.ledger.emissions.length :=
  c.chain.every_complete_outcome hb e hc

theorem prescribed_errors_on_every_complete_execution (hb : PhysicalBox θ ε) :
    c.AllCompleteErrors := c.all_complete_errors hb

#print axioms every_finite_chain_every_complete_execution
#print axioms terminal_state_and_counts
#print axioms prescribed_errors_on_every_complete_execution

end KernelR.Hybrid.UniversalChainHeadline
