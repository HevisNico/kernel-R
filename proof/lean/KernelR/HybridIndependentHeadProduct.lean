import KernelR.HybridCausalHeadSignals
import KernelR.HybridPhysicalInvariant
import KernelR.HybridInputs

/-! Independent physical executions with real external input queues and real
FIREs on both sides. This is the zero-contact specialization of the existing
causal weaver, not a neutral-execution product. No emission or delivery is
required to vanish. -/
namespace KernelR.Hybrid

/-- Real external head sources precede the shifted real external tail sources.
There are no future unissued contact tokens in this independent product. -/
def independentHeadQueue {n} (tail : Snapshot n) (head : Snapshot 1) : List (Delivery (n+1)) :=
  head.pending.map (Delivery.head (n:=n)) ++ tail.pending.map Delivery.succ

theorem Execution.independent_future_wires {n θ route s u}
    (tail : @Execution n θ route s u) : tail.futureHeadWires (fun _ _ => [])=[] := by
  simp [Execution.futureHeadWires]

theorem HeadQueueBalance.independent {n θ route s u}
    (tail : @Execution n θ route s u) (head : Snapshot 1) :
    HeadQueueBalance tail head (independentHeadQueue s head) (fun _ _ => []) := by
  unfold HeadQueueBalance
  rw [tail.independent_future_wires]
  simp only [independentHeadQueue,←Multiset.coe_add,Multiset.coe_nil,add_zero]
  exact add_comm _ _

abbrev IndependentHeadProduct {n θ θH route s u a b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b) :=
  CausalHeadWeave tail head (independentHeadQueue s a) (fun _ _ => [])

/-- Weave actual finite paths, retaining every source and every actual FIRE.
Only equal initial and terminal clocks are required. -/
theorem Execution.prepend_independent_exists {n θ θH route s u a b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b)
    (hstart : s.time=a.time) (hfinish : u.time=b.time) :
    Nonempty (IndependentHeadProduct tail head) := by
  exact tail.prepend_causal_result head hstart hfinish (fun _ _ => [])
    (by intro i t token hm; contradiction) (independentHeadQueue s a)
    (HeadQueueBalance.independent tail a)

/-- Both real complete horizons yield a complete independent product. -/
theorem Execution.prepend_independent_complete {n θ θH route s u a b T}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b)
    (hstart : s.time=a.time) (ht : CompleteThrough tail T) (hh : CompleteThrough head T) :
    ∃ product : IndependentHeadProduct tail head, CompleteThrough product.execution T := by
  obtain ⟨product⟩ := tail.prepend_independent_exists head hstart (ht.1.trans hh.1.symm)
  exact ⟨product,product.complete ht hh⟩

namespace IndependentHeadProduct
variable {n θ θH route s u a b}
  {tail : @Execution n θ route s u} {head : @Execution 1 θH (fun _ _ => []) a b}
  (product : IndependentHeadProduct tail head)

/-- The exact operational initial queue includes both real external queues. -/
theorem source_queue : (s.prependQueued a (independentHeadQueue s a)).pending=
    a.pending.map (Delivery.head (n:=n)) ++ s.pending.map Delivery.succ := rfl

theorem source_queue_length :
    (s.prependQueued a (independentHeadQueue s a)).pending.length=a.pending.length+s.pending.length := by
  simp only [source_queue,List.length_append,List.length_map]

/-- All retained physical endpoint coordinates, including energy and memory. -/
theorem head_values : (u.prependQueued b product.pending).x 0=b.x 0 := rfl

theorem tail_values (i : Fin n) : (u.prependQueued b product.pending).x i.succ=u.x i := rfl

theorem head_main : (u.prependQueued b product.pending).main 0=b.main 0 := rfl

theorem tail_main (i : Fin n) : (u.prependQueued b product.pending).main i.succ=u.main i := rfl

theorem head_raw (q : Port) : (u.prependQueued b product.pending).raw 0 q=b.raw 0 q := rfl

theorem tail_raw (i : Fin n) (q : Port) : (u.prependQueued b product.pending).raw i.succ q=u.raw i q := rfl

theorem emission_count : product.execution.ledger.emissions.length=
    tail.ledger.emissions.length+head.ledger.emissions.length := product.trace.total_emission_count

theorem delivery_count : product.execution.deliveries.length=
    tail.deliveries.length+head.deliveries.length := product.trace.total_delivery_count

theorem physical (ht : PhysicalInvariant θ u) (hh : PhysicalInvariant θH b) :
    PhysicalInvariant (prependParameters θH θ) (u.prependQueued b product.pending) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact hh.region 0
    | succ i => exact ht.region i
  · intro i q
    cases i using Fin.cases with
    | zero => exact hh.gain_cap 0 q
    | succ i => exact ht.gain_cap i q
  · intro i
    cases i using Fin.cases with
    | zero => exact hh.recovery_cap 0
    | succ i => exact ht.recovery_cap i
  · intro i
    cases i using Fin.cases with
    | zero => exact hh.reserve 0
    | succ i => exact ht.reserve i

theorem raw_valid (hfinish : u.time=b.time) (ht : RawValid u) (hh : RawValid b) :
    RawValid (u.prependQueued b product.pending) := by
  intro i q origin hr
  cases i using Fin.cases with
  | zero =>
    have h := hh 0 q origin hr
    change origin≤u.time ∧ u.time≤origin+1
    simpa only [←hfinish] using h
  | succ i => exact ht i q origin hr

theorem ready (ht : ∀ i, ReadyCoordinates u i) (hh : ReadyCoordinates b 0) :
    ∀ i, ReadyCoordinates (u.prependQueued b product.pending) i := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hh.ready,hh.charge,hh.auxiliary⟩
  | succ i => exact ⟨(ht i).ready,(ht i).charge,(ht i).auxiliary⟩

end IndependentHeadProduct
end KernelR.Hybrid
