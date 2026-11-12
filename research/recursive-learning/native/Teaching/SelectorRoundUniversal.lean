import Teaching.SelectorReprepare
import KernelR.HybridInputBalance
import KernelR.HybridUniversalExecution

/-! Transfer a constructed complete round's behavior to every complete
execution with the same initial state, fixed router and endpoint date.
The pending list is an operational presentation: physical coordinates agree
exactly, and a final empty or singleton queue gives literal snapshot equality.
These comparison theorems do not construct a round or choose its calendar. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

theorem snapshot_eq_of_observational_pending {n} {s t : Snapshot n}
    (same : s.ObservationalEq t) (queue : s.pending = t.pending) : s = t := by
  cases s with
  | mk st sx sm sa sr sq =>
    cases t with
    | mk tt tx tm ta tr tq =>
      obtain ⟨ht, hx, hm, ha, hr, _⟩ := same
      dsimp at ht hx hm ha hr queue
      cases ht; cases hx; cases hm; cases ha; cases hr; cases queue
      rfl

theorem snapshot_eq_of_observational_empty {n} {s t : Snapshot n}
    (same : s.ObservationalEq t) (empty : t.pending = []) : s = t := by
  apply snapshot_eq_of_observational_pending same
  have queues := same.pending
  rw [empty] at queues
  exact (List.perm_nil.mp queues).trans empty.symm

theorem snapshot_eq_of_observational_singleton {n} {s t : Snapshot n}
    (same : s.ObservationalEq t) (token : Delivery n) (queue : t.pending = [token]) : s = t := by
  apply snapshot_eq_of_observational_pending same
  have queues := same.pending
  rw [queue] at queues
  exact (List.perm_singleton.mp queues).trans queue.symm

/-- Token conservation upgrades native observational uniqueness to equality
of delivery multiplicities, including initially queued external inputs. -/
theorem complete_round_deliveries {n θ ε route s u v T}
    (reference : @Execution n θ route s u) (candidate : Execution θ route s v)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (complete : CompleteThrough reference T) (done : CompleteThrough candidate T) :
    candidate.deliveries.Perm reference.deliveries := by
  obtain ⟨state, fires⟩ := candidate.observational_unique reference box physical done complete
  have queues := Multiset.coe_eq_coe.mpr state.pending
  have issued := Multiset.coe_eq_coe.mpr
    (fires.flatMap_right (fun event => route event.1 event.2))
  have balance := candidate.token_balance.trans
    ((congrArg (fun m : Multiset (Delivery n) => (s.pending : Multiset (Delivery n)) + m)
      issued).trans reference.token_balance.symm)
  apply Multiset.coe_eq_coe.mp
  exact add_left_cancel (by simpa only [queues] using balance)

/-- No event order, emission ledger, input ledger or transverse-contact
premise is imposed on the competing native execution. It must be complete
through the same declared date as the constructed reference execution. -/
theorem complete_round_behavior {n θ ε route s u v T}
    (reference : @Execution n θ route s u) (candidate : Execution θ route s v)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (complete : CompleteThrough reference T) (done : CompleteThrough candidate T) :
    v.ObservationalEq u ∧
      (∀ i, candidate.emissionTimes i = reference.emissionTimes i) ∧
      candidate.deliveries.Perm reference.deliveries ∧
      candidate.deliveries.length = reference.deliveries.length := by
  have receipts := complete_round_deliveries reference candidate box physical complete done
  exact ⟨(candidate.observational_unique reference box physical done complete).1,
    fun i => candidate.emissionTimes_unique reference box physical done complete i,
    receipts, receipts.length_eq⟩

/-- Any endpoint invariant that ignores pending-list presentation transfers
to every competing complete execution, with no new existence assumption. -/
theorem complete_round_invariant {n θ ε route s u v T} {invariant : Snapshot n → Prop}
    (reference : @Execution n θ route s u) (candidate : Execution θ route s v)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (complete : CompleteThrough reference T) (done : CompleteThrough candidate T)
    (preserved : ∀ {a b}, Snapshot.ObservationalEq a b → invariant a → invariant b)
    (endpoint : invariant u) : invariant v :=
  preserved (reference.observational_unique candidate box physical complete done).1 endpoint

/-- The same guarantee for complete geometric-crossing executions. Their
native representatives retain the actual weak steps; causality and the
constructed reference's transversal contacts discharge the refinement. -/
theorem complete_round_crossing_behavior {n θ ε route s u v T}
    (reference : @Execution n θ route s u) (candidate : CrossingExecution θ route s v)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (initial : InitiallyBelowReady s) (causal : StrictCausalRouter route)
    (complete : CompleteThrough reference T) (positive : reference.ContactsTransversal)
    (done : CrossingCompleteThrough candidate T) :
    ∃ native : Execution θ route s v, native.toWeak = candidate.execution ∧
      v.ObservationalEq u ∧
      (∀ i, candidate.execution.emissionTimes i = reference.emissionTimes i) ∧
      native.deliveries.Perm reference.deliveries ∧
      native.deliveries.length = reference.deliveries.length := by
  obtain ⟨native, same⟩ := candidate.execution.toNative_of_transverse_completion reference causal
    box physical complete positive (le_of_eq done.1)
  have weak := done.toWeak_of_native candidate native same initial box physical
  obtain ⟨state, fires⟩ := reference.observational_unique_weak box candidate.execution physical
    complete positive weak
  have ledger : native.ledger = candidate.execution.ledger := by rw [← same, Execution.toWeak_ledger]
  have queues := Multiset.coe_eq_coe.mpr state.symm.pending
  have issued := Multiset.coe_eq_coe.mpr
    (fires.symm.flatMap_right (fun event => route event.1 event.2))
  have balance := native.token_balance.trans
    ((congrArg (fun m : Multiset (Delivery n) => (s.pending : Multiset (Delivery n)) + m)
      (by simpa only [ledger] using issued)).trans reference.token_balance.symm)
  have receipts : native.deliveries.Perm reference.deliveries := by
    apply Multiset.coe_eq_coe.mp
    exact add_left_cancel (by simpa only [queues] using balance)
  exact ⟨native, same, state.symm,
    fun i => (reference.emissionTimes_unique_weak candidate.execution box physical complete positive weak i).symm,
    receipts, receipts.length_eq⟩

/-- The already constructed finite re-preparation prefix has a literal
unique endpoint because its endpoint queue is empty. Its existential
initial calendar is unchanged by this result; this is not autonomous reuse. -/
theorem ReadReprepared.every_complete {θ ε s delay high final}
    (run : ReadReprepared θ s delay high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s)
    (candidate : Execution θ (reprepareRouter run.time delay)
      (withFuture s [reprepareIgnition run.time]) final)
    (done : CompleteThrough candidate run.preparation.final.time) :
    final = run.preparation.final ∧
      candidate.emissionTimes 0 = run.execution.emissionTimes 0 ∧
      candidate.deliveries.Perm run.execution.deliveries ∧
      candidate.deliveries.length = 3 := by
  have initial : PhysicalInvariant θ (withFuture s [reprepareIgnition run.time]) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  obtain ⟨state, fires, inputs, cost⟩ :=
    complete_round_behavior run.execution candidate box initial run.complete done
  exact ⟨snapshot_eq_of_observational_empty state run.preparation.prepared.empty,
    fires 0, inputs, cost.trans run.pulse_cost⟩

end RecursiveLearning.Native
