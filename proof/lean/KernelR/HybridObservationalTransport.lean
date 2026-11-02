import KernelR.HybridSnapshotObservational
import KernelR.Refinement
import KernelR.HybridNeutralExecutionProduct
import KernelR.HybridPhysicalInvariant

/-! Pending-token lists are operational presentations, not physical coordinates.
Transport along a permutation preserves every physical flow, each FIRE label,
and terminal saturation. It neither adds progress nor assumes an outcome. -/
namespace KernelR.Hybrid

/-- The differential field does not inspect the pending-list presentation. -/
theorem Snapshot.ObservationalEq.field {n θ} {s t : Snapshot n}
    (h : s.ObservationalEq t) : field θ s = field θ t := by
  rcases s with ⟨st,sx,sm,sa,sr,sq⟩
  rcases t with ⟨tt,tx,tm,ta,tr,tq⟩
  rcases h with ⟨ht,hx,hm,ha,hr,hq⟩
  dsimp at ht hx hm ha hr hq
  subst tt; subst tx; subst tm; subst ta; subst tr
  rfl

/-- The physical invariant depends only on observed coordinates and modes. -/
theorem Snapshot.ObservationalEq.physical_invariant {n θ} {s t : Snapshot n}
    (h : s.ObservationalEq t) (hs : PhysicalInvariant θ s) : PhysicalInvariant θ t := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [UpperRegion,←h.values,←h.aux] using hs.region
  · simpa only [←h.values] using hs.gain_cap
  · simpa only [←h.values] using hs.recovery_cap
  · simpa only [←h.values] using hs.reserve

/-- Re-present an actual flow with a permuted initial pending queue. -/
noncomputable def Flow.rebase_observational {n θ s u t} (f : @Flow n θ s u)
    (h : s.ObservationalEq t) : Flow θ t {u with pending:=t.pending} where
  positive := by simpa only [←h.time] using f.positive
  path := f.path
  initial := by simpa only [←h.time] using f.initial.trans h.values
  final := f.final
  main_fixed := f.main_fixed.trans h.main
  aux_fixed := f.aux_fixed.trans h.aux
  raw_fixed := f.raw_fixed.trans h.raw
  queue_fixed := rfl
  continuous := by simpa only [←h.time] using f.continuous
  integrable := by simpa only [←h.time,←h.field] using f.integrable
  mark_integrable := by
    simpa only [←h.time,markAct,←h.main,←h.aux] using f.mark_integrable
  integral_eq := by
    simpa only [←h.time,←h.values,←h.field] using f.integral_eq
  guards := by
    simpa only [←h.time,BeforeGuards,←h.main,←h.aux] using f.guards
  raw_support := by
    simpa only [←h.raw,←h.time] using f.raw_support
  pending_urgent := by
    intro d hd
    exact f.pending_urgent d (h.pending.mem_iff.mpr hd)

/-- The re-presented flow ends in the same physical state. -/
theorem Flow.rebase_observational_final {n θ s u t} (f : @Flow n θ s u)
    (h : s.ObservationalEq t) : u.ObservationalEq {u with pending:=t.pending} := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (List.Perm.of_eq f.queue_fixed).trans h.pending

/-- Queue re-presentation preserves the actual jump constructor and FIRE label. -/
theorem Jump.transport_observational_emissions {n route s u t} (j : @Jump n route s u)
    (h : s.ObservationalEq t) :
    ∃ v, ∃ j' : Jump route t v,
      u.ObservationalEq v ∧ j'.ledger.emissions=j.ledger.emissions := by
  rcases s with ⟨st,sx,sm,sa,sr,sq⟩
  rcases t with ⟨tt,tx,tm,ta,tr,tq⟩
  rcases h with ⟨ht,hx,hm,ha,hr,hq⟩
  dsimp at ht hx hm ha hr hq
  subst tt; subst tx; subst tm; subst ta; subst tr
  cases j with
  | fire i mode guard =>
    exact ⟨_,Jump.fire _ i mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq.append_right _⟩,rfl⟩
  | fastEnd i mode guard =>
    exact ⟨_,Jump.fastEnd _ i mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | reopen i mode guard =>
    exact ⟨_,Jump.reopen _ i mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | mark i p mode guard =>
    exact ⟨_,Jump.mark _ i p mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | silent i p mode guard =>
    exact ⟨_,Jump.silent _ i p mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | error i p mode guard =>
    exact ⟨_,Jump.error _ i p mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | auxReady i p mode guard =>
    exact ⟨_,Jump.auxReady _ i p mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | rawEnd i p origin active due =>
    exact ⟨_,Jump.rawEnd _ i p origin active due,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | arrive d before after queue due free =>
    change sq=before++d::after at queue
    have hd : d∈tq := hq.mem_iff.mp (by rw [queue]; simp)
    obtain ⟨before',after',hqueue'⟩ := List.mem_iff_append.mp hd
    refine ⟨_,Jump.arrive _ d before' after' hqueue' due free,⟨rfl,rfl,rfl,rfl,rfl,?_⟩,rfl⟩
    rw [queue,hqueue'] at hq
    exact List.Perm.cons_inv ((List.perm_middle).symm.trans (hq.trans List.perm_middle))

/-- Every move transports without changing its FIRE labels. -/
theorem Move.transport_observational_emissions {n θ route s u t} (m : @Move n θ route s u)
    (h : s.ObservationalEq t) :
    ∃ v, ∃ m' : Move θ route t v,
      u.ObservationalEq v ∧ m'.ledger.emissions=m.ledger.emissions := by
  cases m with
  | flow f =>
    exact ⟨_,.flow (f.rebase_observational h),f.rebase_observational_final h,rfl⟩
  | jump j =>
    obtain ⟨v,j',hv,he⟩ := j.transport_observational_emissions h
    exact ⟨v,.jump j',hv,he⟩

/-- A complete finite trace can be re-presented from an observationally equal
snapshot, preserving the exact global FIRE list, hence each cell's list. -/
theorem Execution.transport_observational_emissions_count {n θ route s u t}
    (e : @Execution n θ route s u) (h : s.ObservationalEq t) :
    ∃ v, ∃ e' : Execution θ route t v,
      u.ObservationalEq v ∧ e'.ledger.emissions=e.ledger.emissions ∧
      e'.moveCount=e.moveCount := by
  induction e generalizing t with
  | nil s => exact ⟨t,.nil t,h,rfl,rfl⟩
  | cons move rest ih =>
    obtain ⟨mid,move',hm,hem⟩ := move.transport_observational_emissions h
    obtain ⟨v,rest',hv,her,hcount⟩ := ih hm
    refine ⟨v,.cons move' rest',hv,?_,?_⟩
    · simp only [Execution.ledger,Ledger.add,hem,her]
    · simp only [Execution.moveCount,hcount]

/-- Forgetting syntactic length leaves exact FIRE-list transport. -/
theorem Execution.transport_observational_emissions {n θ route s u t}
    (e : @Execution n θ route s u) (h : s.ObservationalEq t) :
    ∃ v, ∃ e' : Execution θ route t v,
      u.ObservationalEq v ∧ e'.ledger.emissions=e.ledger.emissions := by
  obtain ⟨v,e',hv,he,_⟩ := e.transport_observational_emissions_count h
  exact ⟨v,e',hv,he⟩

/-- Terminal saturation is independent of how the pending list is ordered. -/
theorem completeThrough_of_observational {n θ route s u t v T}
    (e : @Execution n θ route s u) (e' : Execution θ route t v)
    (h : u.ObservationalEq v) (hc : CompleteThrough e T) : CompleteThrough e' T := by
  refine ⟨h.time.symm.trans hc.1,observational_no_jump h hc.2.1,?_⟩
  intro d hd
  exact hc.2.2 d (h.pending.mem_iff.mpr hd)

/-- The same transport preserves completeness and the ordered per-cell FIRE
lists. No endpoint property or execution equivalence is a caller premise. -/
theorem Execution.transport_complete_observational {n θ route s u t T}
    (e : @Execution n θ route s u) (h : s.ObservationalEq t)
    (hc : CompleteThrough e T) :
    ∃ v, ∃ e' : Execution θ route t v,
      u.ObservationalEq v ∧ CompleteThrough e' T ∧
      ∀ i, e'.emissionTimes i=e.emissionTimes i := by
  obtain ⟨v,e',hv,he⟩ := e.transport_observational_emissions h
  refine ⟨v,e',hv,completeThrough_of_observational e e' hv hc,?_⟩
  intro i
  simp only [Execution.emissionTimes,he]

end KernelR.Hybrid
