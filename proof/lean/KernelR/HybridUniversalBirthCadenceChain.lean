import KernelR.HybridUniversalExecution
import KernelR.HybridIndexedBirthCadenceChain

/-! Universal finite-chain refinement. Existence is constructed first; every
other complete finite execution under that fixed router then has the same
physical endpoint and actual per-cell FIRE dates. -/
namespace KernelR.Hybrid

/-- The operational router of the complete birth-to-terminal witness. -/
noncomputable abbrev ConstructedBirthCadenceChain.router {n θ bornCells K sigma centre delay T}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T) : Router (n+1) :=
  (c.preparation.cadenceData delay T c.delay_positive).route n

/-- Universal observations of the actual trace, not an assumed output calendar. -/
def ConstructedBirthCadenceChain.AllComplete {n θ bornCells K sigma centre delay T}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T) : Prop :=
  ∀ (u : Snapshot (n+1))
    (e : Execution θ c.router (familyPreparationBornSource bornCells K) u),
    CompleteThrough e T →
      c.final.ObservationalEq u ∧ ∀ i, e.emissionTimes i=c.execution.emissionTimes i

/-- No hypothesis about the competing trace's intermediate states, events or
outputs is required beyond its operational rules and terminal completeness. -/
theorem ConstructedBirthCadenceChain.all_complete {n θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) : c.AllComplete := by
  intro u e he
  have hs := c.preparation.source_birth.physical_invariant hb
  exact ⟨(c.execution.observational_unique e hb hs c.complete he).1,
    fun i => e.emissionTimes_unique c.execution hb hs he c.complete i⟩

/-- FAST-phase dates are obtained from the full actual ledger by dropping the
physically proved number of preparation FIREs (14 at the leaf, 12 at a relay). -/
theorem ConstructedBirthCadenceChain.drop_preparation_times {n θ bornCells K sigma centre delay T}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T) (i : Fin (n+1)) :
    (c.execution.emissionTimes i).drop (finiteChainPreparationCount n i)=
      c.fastExecution.emissionTimes i := by
  have ht : c.fastExecution.emissionTimes i=c.fast.stage.execution.emissionTimes i := by
    simp only [Execution.emissionTimes,c.fast_ledger]
  rw [ht,c.emission_times,←c.preparation.emission_count_per_cell i]
  simp

/-- Direct physical conclusions for a complete trace, with its own actual
FIRE lists and total traffic supplied only as observations of that trace. -/
structure UniversalCadenceOutcome {n} (θ : Fin (n+1)→Parameters)
    (bornCells : Fin (n+1)→Snapshot 1) (K : ℕ) (T : ℝ)
    (u : Snapshot (n+1)) (times : Fin (n+1)→List ℝ) (total : ℕ) : Prop where
  date : u.time=T
  ready : ∀ i, ReadyCoordinates u i
  charge : ∀ i, u.x i .q=1/10
  raw_none : ∀ i p, u.raw i p=none
  pending : u.pending=[]
  gain : ∀ i, u.x i (.z (cadenceActivePort n i))=
    (bornCells i).x 0 (.z (cadenceActivePort n i))+12/5
  recovery : ∀ i, u.x i .b=(bornCells i).x 0 .b+3/10
  fast_count : ∀ i, ((times i).drop (finiteChainPreparationCount n i)).length=K-5-2*(n-i.val)
  cumulative_count : ∀ i, (times i).length=finiteChainPreparationCount n i+(K-5-2*(n-i.val))
  total_count : total=(n+1)*(K-(n+1)+8)+2
  physical : PhysicalInvariant θ u

private theorem ready_observational {n} {s u : Snapshot n}
    (h : s.ObservationalEq u) (i : Fin n) (hr : ReadyCoordinates s i) : ReadyCoordinates u i := by
  refine ⟨?_,?_,?_⟩
  · rw [←h.main]; exact hr.ready
  · rw [←h.values]; exact hr.charge
  · intro p
    rw [←h.aux,←h.values]
    exact hr.auxiliary p

/-- Every complete actual execution of a constructed birth program has its
claimed physical terminal state, own memories, FAST counts and full traffic. -/
theorem ConstructedBirthCadenceChain.every_complete_outcome {n θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) {u}
    (e : Execution θ c.router (familyPreparationBornSource bornCells K) u)
    (hc : CompleteThrough e T) :
    UniversalCadenceOutcome θ bornCells K T u e.emissionTimes e.ledger.emissions.length := by
  obtain ⟨h,ht⟩ := c.all_complete hb u e hc
  have hp := (c.execution.observational_unique e hb
    (c.preparation.source_birth.physical_invariant hb) c.complete hc).2
  refine ⟨hc.1,fun i => ready_observational h i (c.ready i),?_,?_,?_,?_,?_,?_,?_,?_,
    h.physical_invariant c.physical⟩
  · intro i; rw [←h.values]; exact c.charge i
  · intro i p; rw [←h.raw]; exact c.raw_none i p
  · exact (List.Perm.nil_eq (c.pending ▸ h.pending)).symm
  · intro i; rw [←h.values]; exact c.gain_target i
  · intro i; rw [←h.values]; exact c.recovery i
  · intro i; rw [ht i,c.drop_preparation_times]; exact c.fast_count i
  · intro i; rw [ht i]; exact c.cumulative_count i
  · exact hp.length_eq.symm.trans c.total_emission_count

/-- The indexed error promise concerns every complete trace of the resulting
fixed router. Indices exclude the actual preparation prefix. -/
def ConstructedIndexedBirthCadenceChain.AllCompleteErrors {n θ bornCells K sigma centre error T}
    (c : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T) : Prop :=
  ∀ (u : Snapshot (n+1))
    (e : Execution θ c.chain.router (familyPreparationBornSource bornCells K) u),
    CompleteThrough e T → ∀ (j : ℕ) (hj : j<n) (k : ℕ)
      (hk : k<((e.emissionTimes (indexedCadenceSender n j hj)).drop
        (finiteChainPreparationCount n (indexedCadenceSender n j hj))).length),
      c.delay j ((e.emissionTimes (indexedCadenceSender n j hj)).drop
        (finiteChainPreparationCount n (indexedCadenceSender n j hj)))[k]=centre j+error j k

theorem ConstructedIndexedBirthCadenceChain.all_complete_errors
    {n θ bornCells K sigma centre error T ε}
    (c : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T)
    (hb : PhysicalBox θ ε) : c.AllCompleteErrors := by
  intro u e hc j hj k hk
  have ht := (c.chain.all_complete hb u e hc).2 (indexedCadenceSender n j hj)
  have hd : (e.emissionTimes (indexedCadenceSender n j hj)).drop
      (finiteChainPreparationCount n (indexedCadenceSender n j hj))=
      c.chain.fastExecution.emissionTimes (indexedCadenceSender n j hj) := by
    rw [ht,c.chain.drop_preparation_times]
  have hk' : k<(c.chain.fastExecution.emissionTimes (indexedCadenceSender n j hj)).length := by
    simpa only [hd] using hk
  simpa only [hd] using c.realizes j hj k hk'

/-- Every admissible fixed native delay family has a physical complete witness;
all other complete executions under the same protocol share its observations. -/
theorem universal_birth_cadence_chain_exists {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ time, -sigma j≤delay j time-centre j ∧ delay j time-centre j≤sigma j) :
    ∃ c : ConstructedBirthCadenceChain θ bornCells K sigma centre delay (cadenceChainTerminal n K),
      c.AllComplete := by
  obtain ⟨c⟩ := birth_cadence_chain_exists hborn hb ha hqueue sigma centre delay
    hK hsigma hbudget hcentre herror
  exact ⟨c,c.all_complete hb⟩

#print axioms universal_birth_cadence_chain_exists

end KernelR.Hybrid
