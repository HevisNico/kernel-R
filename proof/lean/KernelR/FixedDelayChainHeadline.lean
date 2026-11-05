import KernelR.HybridFiniteChainCanonicalRouter
import KernelR.HybridCrossingCorrespondence

/-! A delay family is supplied before constructing either semantic witness.
The router in every quantified execution is the explicitly defined protocol,
independent of the existentially constructed physical history. -/
namespace KernelR.Hybrid.FixedDelayChainHeadline

/-- Every admissible fixed delay family admits native and geometric witnesses
of the same actual history. Every complete history in either semantics under
that same canonical router has the prescribed physical and FIRE outcomes. -/
theorem every_finite_chain_fixed_delay {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n + 1), BirthState (bornCells i))
    (hb : @PhysicalBox (n + 1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q = .ready)
    (hqueue : ∀ i, (bornCells i).pending = sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ)
    (hK : 4 * (n + 1) + 12 ≤ K) (hsigma : ∀ j, 0 ≤ sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n ≤ 3 / 20)
    (hcentre : ∀ j, j < n → (3 / 10 : ℝ) + sigma j ≤ centre j ∧ centre j ≤ 2 / 5 - sigma j)
    (herror : ∀ j, j < n → ∀ time,
      -sigma j ≤ delay j time - centre j ∧ delay j time - centre j ≤ sigma j) :
    ∃ terminal : Snapshot (n + 1),
      ∃ native : Execution θ (canonicalFiniteChainRouter n delay (cadenceChainTerminal n K))
          (familyPreparationBornSource bornCells K) terminal,
      ∃ geometric : CrossingExecution θ (canonicalFiniteChainRouter n delay (cadenceChainTerminal n K))
          (familyPreparationBornSource bornCells K) terminal,
        CompleteThrough native (cadenceChainTerminal n K) ∧
        CrossingCompleteThrough geometric (cadenceChainTerminal n K) ∧
        native.toWeak = geometric.execution ∧
        (∀ u (candidate : Execution θ
            (canonicalFiniteChainRouter n delay (cadenceChainTerminal n K))
            (familyPreparationBornSource bornCells K) u),
          CompleteThrough candidate (cadenceChainTerminal n K) →
          terminal.ObservationalEq u ∧
            (∀ i, candidate.emissionTimes i = native.emissionTimes i) ∧
            UniversalCadenceOutcome θ bornCells K (cadenceChainTerminal n K) u
              candidate.emissionTimes candidate.ledger.emissions.length) ∧
        (∀ u (candidate : CrossingExecution θ
            (canonicalFiniteChainRouter n delay (cadenceChainTerminal n K))
            (familyPreparationBornSource bornCells K) u),
          CrossingCompleteThrough candidate (cadenceChainTerminal n K) →
          terminal.ObservationalEq u ∧
            (∀ i, candidate.execution.emissionTimes i = native.emissionTimes i) ∧
            UniversalCadenceOutcome θ bornCells K (cadenceChainTerminal n K) u
              candidate.execution.emissionTimes candidate.execution.ledger.emissions.length) := by
  obtain ⟨chain⟩ := birth_cadence_chain_exists hborn hb ha hqueue sigma centre delay
    hK hsigma hbudget hcentre herror
  rw [← chain.router_eq_canonical]
  refine ⟨chain.final, chain.execution, chain.crossingExecution hb, chain.complete,
    chain.crossingExecution_complete hb, rfl, ?_, ?_⟩
  · intro u candidate complete
    have same := chain.all_complete hb u candidate complete
    exact ⟨same.1, same.2, chain.every_complete_outcome hb candidate complete⟩
  · intro u candidate complete
    have same := chain.every_crossing_complete hb candidate complete
    exact ⟨same.1, same.2, chain.crossing_outcome hb candidate complete⟩

#print axioms every_finite_chain_fixed_delay

end KernelR.Hybrid.FixedDelayChainHeadline
