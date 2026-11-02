import KernelR.HybridIndexedBirthCadenceChain

/-! Finite-chain headline for arbitrary prescribed per-emission wire errors.
N=n+1 ranges over all positive finite sizes. Native delays and the complete
physical trace are constructed, not supplied. Error indices refer only to
actual FAST-phase sender FIREs in the final global execution. -/
namespace KernelR.Hybrid.IndexedChainHeadline

theorem every_finite_chain_exists {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ→ℝ) (error : ℕ→ℕ→ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ i, -sigma j≤error j i ∧ error j i≤sigma j) :
    Nonempty (ConstructedIndexedBirthCadenceChain θ bornCells K sigma centre error (cadenceChainTerminal n K)) := by
  exact indexed_birth_cadence_chain_exists hborn hb ha hqueue sigma centre error
    hK hsigma hbudget hcentre herror

variable {n θ bornCells K sigma centre error T}
  (c : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T)

theorem terminal_state_and_counts (hK : 4*(n+1)+12≤K) :
    c.chain.final.time=T ∧ (∀ i, ReadyCoordinates c.chain.final i) ∧
    (∀ i, c.chain.final.x i .q=1/10) ∧ (∀ i p, c.chain.final.raw i p=none) ∧
    c.chain.final.pending=[] ∧
    (∀ i, c.chain.final.x i (.z (cadenceActivePort n i))=
      (bornCells i).x 0 (.z (cadenceActivePort n i))+12/5) ∧
    (∀ i, c.chain.final.x i .b=(bornCells i).x 0 .b+3/10) ∧
    (∀ i, (c.chain.fastExecution.emissionTimes i).length=K-5-2*(n-i.val)) ∧
    c.chain.fastExecution.ledger.emissions.length=(n+1)*(K-(n+1)-4) ∧
    c.chain.execution.ledger.emissions.length=(n+1)*(K-(n+1)+8)+2 := by
  refine ⟨c.chain.date,c.chain.ready,c.chain.charge,c.chain.raw_none,c.chain.pending,
    c.chain.gain_target,c.chain.recovery,c.chain.fast_count,?_,c.chain.total_emission_count⟩
  rw [c.chain.fast_ledger]
  exact c.chain.fast.actual_emission_count hK

theorem prescribed_errors_on_actual_fires :
    (∀ j, j<n → ∀ time, -sigma j≤c.delay j time-centre j ∧ c.delay j time-centre j≤sigma j) ∧
    (∀ (j : ℕ) (hj : j<n) (i : ℕ)
      (hi : i<(c.chain.fastExecution.emissionTimes (indexedCadenceSender n j hj)).length),
      c.delay j (c.chain.fastExecution.emissionTimes (indexedCadenceSender n j hj))[i]=
        centre j+error j i) :=
  ⟨c.error_bounds,c.realizes⟩

#print axioms every_finite_chain_exists
#print axioms terminal_state_and_counts
#print axioms prescribed_errors_on_actual_fires

end KernelR.Hybrid.IndexedChainHeadline
