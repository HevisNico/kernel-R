import KernelR.HybridPreparedCadenceChainConstruction
import KernelR.HybridFiniteChainPreparedData
import KernelR.HybridCadenceChainCounts
import KernelR.HybridEmissionRouterTransport

/-! Complete physical finite cadence from independently born cells. One fixed
router governs the entire preparation and fast phase. Its contacts are closed
at every actual preparation FIRE, so retargeting preserves the whole physical
trace, ledger and receiving order; no router switch or reaching premise is
introduced. -/
namespace KernelR.Hybrid

private noncomputable def birth_chain_cast {k θ θ' route s s' u}
    (e : @Execution k θ route s u) (hp : θ=θ') (hs : s'=s) :
    Execution θ' route s' u := by cases hp; cases hs; exact e

private theorem birth_chain_cast_ledger {k θ θ' route s s' u}
    (e : @Execution k θ route s u) (hp : θ=θ') (hs : s'=s) :
    (birth_chain_cast e hp hs).ledger=e.ledger := by cases hp; cases hs; rfl

private theorem birth_chain_cast_deliveries {k θ θ' route s s' u}
    (e : @Execution k θ route s u) (hp : θ=θ') (hs : s'=s) :
    (birth_chain_cast e hp hs).deliveries=e.deliveries := by cases hp; cases hs; rfl

private theorem birth_chain_append_ledger {k θ route s u v}
    (e : @Execution k θ route s u) (f : Execution θ route u v) :
    (e.append f).ledger=e.ledger.add f.ledger := by
  induction e with
  | nil => simp [Execution.append,Execution.ledger,Ledger.zero,Ledger.add]
  | cons step rest ih =>
    simp only [Execution.append,Execution.ledger,ih,Ledger.add,add_assoc,List.append_assoc]

/-- A finite router built from contacts closed before160 is itself closed
before160 at every physical cell, including its retained internal edges. -/
theorem finite_chain_route_before_open {d : FiniteCausalChainData} {n : ℕ}
    (hclosed : ∀ j, j<n → ∀ (i : Fin (j+1)) time, time<(160:ℝ) → d.contacts j i time=[])
    (i : Fin (n+1)) {time : ℝ} (ht : time<(160:ℝ)) : d.route n i time=[] := by
  have all : ∀ j, j≤n → ∀ i : Fin (j+1), d.route j i time=[] := by
    intro j
    induction j with
    | zero => intro _ _; rfl
    | succ j ih =>
      intro hj i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        change (d.route j i time).map Delivery.succ ++ (d.contacts j i time).map Delivery.head=[]
        rw [ih (by omega) i,hclosed j (by omega) i time ht]
        rfl
  exact all n (Nat.le_refl n) i

structure ConstructedBirthCadenceChain {n : ℕ} (θ : Fin (n+1) → Parameters)
    (bornCells : Fin (n+1) → Snapshot 1) (K : ℕ) (sigma centre : ℕ → ℝ)
    (delay : ℕ → ℝ → ℝ) (T : ℝ) where
  delay_positive : ∀ j, j<n → ∀ time, 0<delay j time
  preparation : FiniteChainFamilyPreparation θ bornCells K
  fast : ConstructedCadenceChainStage (preparation.cadenceData delay T delay_positive)
    K T n (KernelR.Chain.prefixLength n) (KernelR.Chain.tailLength K n) (KernelR.Chain.pathJitter sigma n)
  preparedExecution : Execution θ ((preparation.cadenceData delay T delay_positive).route n)
    preparation.source preparation.final
  preparation_ledger : preparedExecution.ledger=preparation.execution.ledger
  preparation_deliveries : preparedExecution.deliveries=preparation.execution.deliveries
  fastExecution : Execution θ ((preparation.cadenceData delay T delay_positive).route n)
    preparation.final fast.stage.final
  fast_ledger : fastExecution.ledger=fast.stage.execution.ledger
  fast_deliveries : fastExecution.deliveries=fast.stage.execution.deliveries
  execution : Execution θ ((preparation.cadenceData delay T delay_positive).route n)
    preparation.source fast.stage.final
  reconstruct : execution=preparedExecution.append fastExecution
  ledger : execution.ledger=preparation.execution.ledger.add fast.stage.execution.ledger
  deliveries : execution.deliveries=preparation.execution.deliveries++fast.stage.execution.deliveries
  emission_times : ∀ i, execution.emissionTimes i=
    preparation.execution.emissionTimes i++fast.stage.execution.emissionTimes i
  date : fast.stage.final.time=T
  ready : ∀ i, ReadyCoordinates fast.stage.final i
  charge : ∀ i, fast.stage.final.x i .q=1/10
  raw_none : ∀ i q, fast.stage.final.raw i q=none
  pending : fast.stage.final.pending=[]
  gain_target : ∀ i, fast.stage.final.x i (.z (cadenceActivePort n i))=
    (bornCells i).x 0 (.z (cadenceActivePort n i))+12/5
  gain_other : ∀ i q, q≠cadenceActivePort n i → fast.stage.final.x i (.z q)=preparation.final.x i (.z q)
  recovery : ∀ i, fast.stage.final.x i .b=(bornCells i).x 0 .b+3/10
  fast_count : ∀ i, (fastExecution.emissionTimes i).length=K-5-2*(n-i.val)
  cumulative_count : ∀ i, (execution.emissionTimes i).length=
    finiteChainPreparationCount n i+(K-5-2*(n-i.val))
  total_emission_count : execution.ledger.emissions.length=(n+1)*(K-(n+1)+8)+2
  physical : PhysicalInvariant θ fast.stage.final
  raw_valid : RawValid fast.stage.final
  complete : CompleteThrough execution T

/-- From independent birth states, exact sixteen-source preparation programs,
a finite source budget and bounded channels, construct the complete global
physical history. No prepared state, calendar, reaching trace or local law is
supplied by the caller. -/
theorem birth_cadence_chain_exists {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ time, -sigma j≤delay j time-centre j ∧ delay j time-centre j≤sigma j) :
    Nonempty (ConstructedBirthCadenceChain θ bornCells K sigma centre delay (cadenceChainTerminal n K)) := by
  have hd : ∀ j, j<n → ∀ time, 0<delay j time := by
    intro j hj time
    have hc := hcentre j hj
    have he := herror j hj time
    linarith [hc.1,he.1]
  obtain ⟨preparation⟩ := finite_chain_family_preparation_exists (K:=K) hborn hb ha hqueue
  let T := cadenceChainTerminal n K
  let d := preparation.cadenceData delay T hd
  have domain : PreparedCadenceChainDomain d ε n K sigma centre delay :=
    preparation.cadence_domain (hd:=hd) hb sigma centre hK hsigma hbudget hcentre herror
  obtain ⟨fast⟩ := domain.construct_exists
  have hp : d.parameters n=θ := preparation.cadence_parameters_full
  have hs : preparation.final=d.source n := preparation.cadence_source_full.symm
  let fastExecution := birth_chain_cast fast.stage.execution hp hs
  have hFastLedger : fastExecution.ledger=fast.stage.execution.ledger := birth_chain_cast_ledger _ hp hs
  have hFastDelivered : fastExecution.deliveries=fast.stage.execution.deliveries := birth_chain_cast_deliveries _ hp hs
  have hclosed : ∀ j, j<n → ∀ (i : Fin (j+1)) time, time<(160:ℝ) → d.contacts j i time=[] := by
    intro j hj i time ht
    rw [domain.contacts j hj]
    exact finite_cadence_head_contact_before_open _ _ _ _ _ _ ht
  have hRouteMatches : ∀ event∈preparation.execution.ledger.emissions,
      ([] : List (Delivery (n+1)))=d.route n event.1 event.2 := by
    intro event he
    have ht := (preparation.execution.emission_time_bounds event he).2
    rw [preparation.date] at ht
    exact (finite_chain_route_before_open hclosed event.1 (by linarith)).symm
  obtain ⟨preparedExecution,hPrepLedger,hPrepDelivered⟩ := preparation.execution.retarget_router (d.route n) hRouteMatches
  let execution := preparedExecution.append fastExecution
  have hLedger : execution.ledger=preparation.execution.ledger.add fast.stage.execution.ledger := by
    change (preparedExecution.append fastExecution).ledger=_
    rw [birth_chain_append_ledger,hPrepLedger,hFastLedger]
  have hDelivered : execution.deliveries=preparation.execution.deliveries++fast.stage.execution.deliveries := by
    change (preparedExecution.append fastExecution).deliveries=_
    rw [Execution.deliveries_append,hPrepDelivered,hFastDelivered]
  have hTimes (i : Fin (n+1)) : execution.emissionTimes i=
      preparation.execution.emissionTimes i++fast.stage.execution.emissionTimes i := by
    simp only [Execution.emissionTimes,hLedger,Ledger.add,List.filter_append,List.map_append]
  have hFastTimes (i : Fin (n+1)) : fastExecution.emissionTimes i=fast.stage.execution.emissionTimes i := by
    simp only [Execution.emissionTimes,hFastLedger]
  have hOwnGain (i : Fin (n+1)) : fast.stage.final.x i (.z (cadenceActivePort n i))=
      (bornCells i).x 0 (.z (cadenceActivePort n i))+12/5 := by
    have hg := fast.gain_target i
    rw [←hs] at hg
    by_cases hi : i=Fin.last n
    · subst i
      have hprep := preparation.gain_other (Fin.last n) 0 (by simp [finiteChainPreparationPort])
      simp only [cadenceActivePort,Fin.val_last,ite_true] at hg ⊢
      rw [hprep] at hg
      exact hg
    · have hval : i.val≠n := by
        intro h
        apply hi
        apply Fin.ext
        exact h
      have hprep := preparation.gain_target i
      simp only [finiteChainPreparationPort,finiteChainPreparationDose,hi,ite_false] at hprep
      simp only [cadenceActivePort,hval,ite_false] at hg ⊢
      rw [hprep] at hg
      linarith
  have hRecovery (i : Fin (n+1)) : fast.stage.final.x i .b=(bornCells i).x 0 .b+3/10 := by
    have h := fast.recovery i
    rw [←hs,preparation.recovery] at h
    linarith
  have hPhysical : PhysicalInvariant θ fast.stage.final := by
    simpa only [hp] using fast.stage.physical
  refine ⟨{
    delay_positive:=hd,preparation:=preparation,fast:=fast,preparedExecution:=preparedExecution
    preparation_ledger:=hPrepLedger,preparation_deliveries:=hPrepDelivered
    fastExecution:=fastExecution,fast_ledger:=hFastLedger,fast_deliveries:=hFastDelivered
    execution:=execution,reconstruct:=rfl,ledger:=hLedger,deliveries:=hDelivered,emission_times:=hTimes
    date:=fast.stage.complete.1,ready:=fast.stage.ready,charge:=fast.stage.charge,raw_none:=fast.stage.raw_none
    pending:=fast.stage.pending,gain_target:=hOwnGain,gain_other:=?_,recovery:=hRecovery
    fast_count:=?_,cumulative_count:=?_,total_emission_count:=?_,physical:=hPhysical
    raw_valid:=fast.stage.raw_valid,complete:=?_
  }⟩
  · intro i q hq
    have h := fast.gain_other i q hq
    rw [←hs] at h
    exact h
  · intro i
    exact (congrArg List.length (hFastTimes i)).trans (fast.counts i)
  · intro i
    rw [hTimes,List.length_append,preparation.emission_count_per_cell,fast.counts]
  · exact fast.birth_emission_count preparation.execution execution preparation.total_emission_count hLedger hK
  · simpa only [CompleteThrough] using fast.stage.complete

namespace ConstructedBirthCadenceChain
variable {n θ bornCells K sigma centre delay T}
  (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)

noncomputable abbrev source : Snapshot (n+1) := c.preparation.source

noncomputable abbrev final : Snapshot (n+1) := c.fast.stage.final

theorem source_birth : BirthState c.source := c.preparation.source_birth

theorem source_values (i : Fin (n+1)) : c.source.x i=(bornCells i).x 0 := c.preparation.source_values i

theorem energy_actual (i : Fin (n+1)) : c.final.x i .energy=(c.fast.stage.cells i).2.final.x 0 .energy :=
  c.fast.actual_energy i

end ConstructedBirthCadenceChain
end KernelR.Hybrid
