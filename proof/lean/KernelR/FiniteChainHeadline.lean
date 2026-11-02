import KernelR.HybridBirthCadenceChain

/-! Public finite-chain headline. N is represented as n+1, hence ranges over
all positive finite sizes. Physical parameters are fixed in time. Channel
functions are sampled at actual FIREs; this interface does not assert a
separate universal theorem about arbitrary admissible executions. -/
namespace KernelR.Hybrid.FiniteChainHeadline

theorem every_finite_chain_exists {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ time, -sigma j≤delay j time-centre j ∧ delay j time-centre j≤sigma j) :
    Nonempty (ConstructedBirthCadenceChain θ bornCells K sigma centre delay (cadenceChainTerminal n K)) := by
  exact birth_cadence_chain_exists hborn hb ha hqueue sigma centre delay hK hsigma hbudget hcentre herror

variable {n θ bornCells K sigma centre delay T}
  (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)

theorem terminal_state_and_memories :
    c.final.time=T ∧ (∀ i, ReadyCoordinates c.final i) ∧
    (∀ i, c.final.x i .q=1/10) ∧ (∀ i p, c.final.raw i p=none) ∧
    c.final.pending=[] ∧
    (∀ i, c.final.x i (.z (cadenceActivePort n i))=
      (bornCells i).x 0 (.z (cadenceActivePort n i))+12/5) ∧
    (∀ i, c.final.x i .b=(bornCells i).x 0 .b+3/10) :=
  ⟨c.date,c.ready,c.charge,c.raw_none,c.pending,c.gain_target,c.recovery⟩

theorem actual_counts (hK : 4*(n+1)+12≤K) :
    (∀ i, (c.fastExecution.emissionTimes i).length=K-5-2*(n-i.val)) ∧
    (c.fastExecution.emissionTimes 0).length=K-2*(n+1)-3 ∧
    c.fastExecution.ledger.emissions.length=(n+1)*(K-(n+1)-4) ∧
    (∀ i, (c.execution.emissionTimes i).length=
      finiteChainPreparationCount n i+(K-5-2*(n-i.val))) ∧
    c.execution.ledger.emissions.length=(n+1)*(K-(n+1)+8)+2 := by
  refine ⟨c.fast_count,?_,?_,c.cumulative_count,c.total_emission_count⟩
  · have h := c.fast_count 0
    simp only [Fin.val_zero,Nat.sub_zero] at h
    rw [h]
    omega
  · rw [c.fast_ledger]
    exact c.fast.actual_emission_count hK

#print axioms every_finite_chain_exists
#print axioms terminal_state_and_memories
#print axioms actual_counts

end KernelR.Hybrid.FiniteChainHeadline
