import KernelR.ExplicitFiniteChainRouter
import KernelR.FixedDelayChainHeadline

/-! A delay family is supplied before constructing either semantic witness.
The router in every quantified execution is the closed-form protocol,
independent of the existentially constructed physical history. -/
namespace KernelR.Hybrid.TrustedHeadline

/-- Every supplied delay family satisfying the stated bounds admits native and
geometric witnesses of the same actual history. Every complete history in either
semantics under that router has the prescribed physical and FIRE outcomes. -/
theorem every_finite_chain {n θ bornCells K ε}
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
      ∃ native : Execution θ (explicitFiniteChainRouter n delay (cadenceChainTerminal n K))
          (familyPreparationBornSource bornCells K) terminal,
      ∃ geometric : CrossingExecution θ (explicitFiniteChainRouter n delay (cadenceChainTerminal n K))
          (familyPreparationBornSource bornCells K) terminal,
        CompleteThrough native (cadenceChainTerminal n K) ∧
        CrossingCompleteThrough geometric (cadenceChainTerminal n K) ∧
        native.toWeak = geometric.execution ∧
        (∀ u (candidate : Execution θ
            (explicitFiniteChainRouter n delay (cadenceChainTerminal n K))
            (familyPreparationBornSource bornCells K) u),
          CompleteThrough candidate (cadenceChainTerminal n K) →
          terminal.ObservationalEq u ∧
            (∀ i, candidate.emissionTimes i = native.emissionTimes i) ∧
            UniversalCadenceOutcome θ bornCells K (cadenceChainTerminal n K) u
              candidate.emissionTimes candidate.ledger.emissions.length) ∧
        (∀ u (candidate : CrossingExecution θ
            (explicitFiniteChainRouter n delay (cadenceChainTerminal n K))
            (familyPreparationBornSource bornCells K) u),
          CrossingCompleteThrough candidate (cadenceChainTerminal n K) →
          terminal.ObservationalEq u ∧
            (∀ i, candidate.execution.emissionTimes i = native.emissionTimes i) ∧
            UniversalCadenceOutcome θ bornCells K (cadenceChainTerminal n K) u
              candidate.execution.emissionTimes candidate.execution.ledger.emissions.length) := by
  let contract : Router (n + 1) → Prop := fun route =>
    ∃ terminal : Snapshot (n + 1),
      ∃ native : Execution θ (route)
          (familyPreparationBornSource bornCells K) terminal,
      ∃ geometric : CrossingExecution θ (route)
          (familyPreparationBornSource bornCells K) terminal,
        CompleteThrough native (cadenceChainTerminal n K) ∧
        CrossingCompleteThrough geometric (cadenceChainTerminal n K) ∧
        native.toWeak = geometric.execution ∧
        (∀ u (candidate : Execution θ
            (route)
            (familyPreparationBornSource bornCells K) u),
          CompleteThrough candidate (cadenceChainTerminal n K) →
          terminal.ObservationalEq u ∧
            (∀ i, candidate.emissionTimes i = native.emissionTimes i) ∧
            UniversalCadenceOutcome θ bornCells K (cadenceChainTerminal n K) u
              candidate.emissionTimes candidate.ledger.emissions.length) ∧
        (∀ u (candidate : CrossingExecution θ
            (route)
            (familyPreparationBornSource bornCells K) u),
          CrossingCompleteThrough candidate (cadenceChainTerminal n K) →
          terminal.ObservationalEq u ∧
            (∀ i, candidate.execution.emissionTimes i = native.emissionTimes i) ∧
            UniversalCadenceOutcome θ bornCells K (cadenceChainTerminal n K) u
              candidate.execution.emissionTimes candidate.execution.ledger.emissions.length)
  have original : contract (canonicalFiniteChainRouter n delay (cadenceChainTerminal n K)) :=
    FixedDelayChainHeadline.every_finite_chain_fixed_delay
      hborn hb ha hqueue sigma centre delay hK hsigma hbudget hcentre herror
  exact Eq.mp (congrArg contract
    (canonicalFiniteChainRouter_eq_explicit n delay (cadenceChainTerminal n K))) original

#print axioms every_finite_chain

end KernelR.Hybrid.TrustedHeadline
