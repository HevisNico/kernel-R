import KernelR.HybridBirthCadenceChain
import KernelR.HybridIndexedPreparedCadenceChain

/-! Full physical finite-chain realization of prescribed per-emission wire
errors. Wire indices count FAST-phase sender FIREs only. The final one-router
history retains the entire preparation and every original source at birth. -/
namespace KernelR.Hybrid

private noncomputable def indexed_birth_chain_cast {k θ θ' route s s' u}
    (e : @Execution k θ route s u) (hp : θ=θ') (hs : s'=s) :
    Execution θ' route s' u := by cases hp; cases hs; exact e

private theorem indexed_birth_chain_cast_ledger {k θ θ' route s s' u}
    (e : @Execution k θ route s u) (hp : θ=θ') (hs : s'=s) :
    (indexed_birth_chain_cast e hp hs).ledger=e.ledger := by cases hp; cases hs; rfl

private theorem indexed_birth_chain_cast_deliveries {k θ θ' route s s' u}
    (e : @Execution k θ route s u) (hp : θ=θ') (hs : s'=s) :
    (indexed_birth_chain_cast e hp hs).deliveries=e.deliveries := by cases hp; cases hs; rfl

private theorem indexed_birth_chain_append_ledger {k θ route s u v}
    (e : @Execution k θ route s u) (f : Execution θ route u v) :
    (e.append f).ledger=e.ledger.add f.ledger := by
  induction e with
  | nil => simp [Execution.append,Execution.ledger,Ledger.zero,Ledger.add]
  | cons step rest ih =>
    simp only [Execution.append,Execution.ledger,ih,Ledger.add,add_assoc,List.append_assoc]

structure ConstructedIndexedBirthCadenceChain {n : ℕ} (θ : Fin (n+1)→Parameters)
    (bornCells : Fin (n+1)→Snapshot 1) (K : ℕ) (sigma centre : ℕ→ℝ)
    (error : ℕ→ℕ→ℝ) (T : ℝ) where
  delay : ℕ→ℝ→ℝ
  error_bounds : ∀ j, j<n → ∀ t, -sigma j≤delay j t-centre j ∧ delay j t-centre j≤sigma j
  chain : ConstructedBirthCadenceChain θ bornCells K sigma centre delay T
  realizes : ∀ (j : ℕ) (hj : j<n) (i : ℕ)
    (hi : i<(chain.fastExecution.emissionTimes (indexedCadenceSender n j hj)).length),
    delay j (chain.fastExecution.emissionTimes (indexedCadenceSender n j hj))[i]=centre j+error j i

/-- Every prescribed bounded error sequence on every physical wire admits one
fixed native router and a complete actual birth-to-terminal execution. No
native delay functions, execution or calendar are supplied by the caller. -/
theorem indexed_birth_cadence_chain_exists {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ→ℝ) (error : ℕ→ℕ→ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ i, -sigma j≤error j i ∧ error j i≤sigma j) :
    Nonempty (ConstructedIndexedBirthCadenceChain θ bornCells K sigma centre error (cadenceChainTerminal n K)) := by
  obtain ⟨preparation⟩ := finite_chain_family_preparation_exists (K:=K) hborn hb ha hqueue
  obtain ⟨indexed⟩ := preparation.indexed_cadence_stage_exists hb sigma centre error hK hsigma
    hbudget hcentre herror n (Nat.le_refl n)
  let delay := indexed.delay
  let hd := indexed.positive
  let T := cadenceChainTerminal n K
  let d := preparation.cadenceData delay T hd
  let fast := indexed.cadence
  have domain : PreparedCadenceChainDomain d ε n K sigma centre delay :=
    preparation.cadence_domain (hd:=hd) hb sigma centre hK hsigma hbudget hcentre indexed.error_bounds
  have hp : d.parameters n=θ := preparation.cadence_parameters_full
  have hs : preparation.final=d.source n := preparation.cadence_source_full.symm
  let fastExecution := indexed_birth_chain_cast fast.stage.execution hp hs
  have hFastLedger : fastExecution.ledger=fast.stage.execution.ledger := indexed_birth_chain_cast_ledger _ hp hs
  have hFastDelivered : fastExecution.deliveries=fast.stage.execution.deliveries := indexed_birth_chain_cast_deliveries _ hp hs
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
    rw [indexed_birth_chain_append_ledger,hPrepLedger,hFastLedger]
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
    have h : PhysicalInvariant (d.parameters n) fast.stage.final := fast.stage.physical
    rw [hp] at h
    exact h
  refine ⟨{
    delay:=delay,error_bounds:=indexed.error_bounds
    chain:={
      delay_positive:=hd,preparation:=preparation,fast:=fast,preparedExecution:=preparedExecution
      preparation_ledger:=hPrepLedger,preparation_deliveries:=hPrepDelivered
      fastExecution:=fastExecution,fast_ledger:=hFastLedger,fast_deliveries:=hFastDelivered
      execution:=execution,reconstruct:=rfl,ledger:=hLedger,deliveries:=hDelivered,emission_times:=hTimes
      date:=fast.stage.complete.1,ready:=fast.stage.ready,charge:=fast.stage.charge,raw_none:=fast.stage.raw_none
      pending:=fast.stage.pending,gain_target:=hOwnGain,gain_other:=?_,recovery:=hRecovery
      fast_count:=?_,cumulative_count:=?_,total_emission_count:=?_,physical:=hPhysical
      raw_valid:=fast.stage.raw_valid,complete:=?_
    }
    realizes:=?_
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
  · intro j hj i hi
    change delay j (fastExecution.emissionTimes (indexedCadenceSender n j hj))[i]=centre j+error j i
    have hi' : i<(fast.stage.execution.emissionTimes (indexedCadenceSender n j hj)).length := by
      simpa only [hFastTimes] using hi
    simpa only [hFastTimes] using indexed.realizes j hj i hi'

end KernelR.Hybrid
