import KernelR.HybridNeutralHeadExecutionProduct
import KernelR.HybridEvents

/-! Queue algebra for a feed-forward routed product. Future head inputs are
obtained from the remaining tail execution's actual emissions. They are proof
data only: the operational queue contains each wire only after its real FIRE.
This module does not yet construct the whole routed execution product. -/
namespace KernelR.Hybrid

/-- Embed a one-cell receiver token at the new head cell. -/
def Delivery.head {n} (d : Delivery 1) : Delivery (n + 1) :=
  ⟨0,d.port,d.due⟩

abbrev HeadRoutes (n : ℕ) := Fin n → ℝ → List (Delivery 1)

/-- Tail contacts are retained; additional tokens target only the new head.
The head's outgoing contact is closed in this feed-forward extension. -/
def prependRouted {n} (tail : Router n) (head : HeadRoutes n) : Router (n + 1) :=
  Fin.cases (fun _ => [])
    (fun i t => (tail i t).map Delivery.succ ++ (head i t).map (Delivery.head (n := n)))

def StrictHeadRoutes {n} (head : HeadRoutes n) : Prop :=
  ∀ i t d, d ∈ head i t → t < d.due

/-- Change only the queue used by a constructed local flow. -/
def Snapshot.requeue {n} (s : Snapshot n) (Q : List (Delivery n)) : Snapshot n :=
  {s with pending := Q}

/-- The physical field, work and guard equations do not observe pending
tokens. The replacement queue must satisfy its own true urgency bound. -/
def Flow.requeue {n θ s u} (f : @Flow n θ s u) (Q : List (Delivery n))
    (hp : ∀ d ∈ Q, u.time ≤ d.due) :
    Flow θ (s.requeue Q) (u.requeue Q) where
  positive := f.positive
  path := f.path
  initial := f.initial
  final := f.final
  main_fixed := f.main_fixed
  aux_fixed := f.aux_fixed
  raw_fixed := f.raw_fixed
  queue_fixed := rfl
  continuous := f.continuous
  integrable := f.integrable
  mark_integrable := f.mark_integrable
  integral_eq := f.integral_eq
  guards := f.guards
  raw_support := f.raw_support
  pending_urgent := hp

/-- Physical head/tail coordinates with the actual shared operational queue. -/
noncomputable def Snapshot.prependQueued {n} (tail : Snapshot n) (head : Snapshot 1)
    (Q : List (Delivery (n + 1))) : Snapshot (n + 1) :=
  (tail.prependQuiet head).requeue Q

/-- Combine the very same local flow paths while retaining a separate
operational queue, rather than inserting the local analysis queues. -/
noncomputable def Flow.prependQueued {n θ θH s u a b}
    (tail : @Flow n θ s u) (head : @Flow 1 θH a b)
    (hstart : s.time = a.time) (hfinish : u.time = b.time)
    (Q : List (Delivery (n + 1))) (hp : ∀ d ∈ Q, u.time ≤ d.due) :
    Flow (prependParameters θH θ) (s.prependQueued a Q) (u.prependQueued b Q) :=
  (tail.prependQuiet head hstart hfinish).requeue Q hp

/-- An opaque existence interface avoids expanding every field of the product
flow when a later dependent execution witness is type checked. -/
theorem Flow.prependQueued_exists {n θ θH s u a b}
    (tail : @Flow n θ s u) (head : @Flow 1 θH a b)
    (hstart : s.time = a.time) (hfinish : u.time = b.time)
    (Q : List (Delivery (n + 1))) (hp : ∀ d ∈ Q, u.time ≤ d.due) :
    ∃ flow : Flow (prependParameters θH θ) (s.prependQueued a Q) (u.prependQueued b Q),
      flow.path = fun t => Fin.cases (head.path t 0) (tail.path t) :=
  ⟨tail.prependQueued head hstart hfinish Q hp,rfl⟩

/-- Retain both exact pieces of an actual flow behind an opaque witness.
This keeps later dependent execution conversions from expanding the complete
integral-equation proofs carried by the suffix value. -/
theorem Flow.cut_pair_exists {n θ s u t} (flow : @Flow n θ s u)
    (hstart : s.time < t) (hend : t < u.time) :
    ∃ (beforeFlow : Flow θ s (flow.at t)) (afterFlow : Flow θ (flow.at t) u),
      beforeFlow.path = flow.path ∧ afterFlow.path = flow.path :=
  ⟨flow.prefix hstart hend.le,flow.suffix hstart.le hend,rfl,rfl⟩

/-- Additional head wires from actual FIREs still present in the tail.
This list is never inserted into an operational state by this definition. -/
noncomputable def Execution.futureHeadWires {n θ route s u}
    (e : @Execution n θ route s u) (head : HeadRoutes n) : List (Delivery (n + 1)) :=
  e.ledger.emissions.flatMap (fun event => (head event.1 event.2).map (Delivery.head (n := n)))

/-- The isolated receiver's analysis input queue, derived from actual tail
emissions and the declared contacts. This is not a global pending queue. -/
noncomputable def Execution.headInputQueue {n θ route s u}
    (e : @Execution n θ route s u) (head : HeadRoutes n) : List (Delivery 1) :=
  e.ledger.emissions.flatMap (fun event => head event.1 event.2)

theorem Execution.futureHeadWires_map {n θ route s u}
    (e : @Execution n θ route s u) (head : HeadRoutes n) :
    e.futureHeadWires head = (e.headInputQueue head).map (Delivery.head (n := n)) := by
  simp only [futureHeadWires,headInputQueue,List.map_flatMap]

theorem Execution.causal_flow_emissions {n θ route s v u}
    (flow : @Flow n θ s v) (rest : Execution θ route v u) :
    (Execution.cons (.flow flow) rest).ledger.emissions = rest.ledger.emissions := rfl

theorem Execution.causal_flow_deliveries {n θ route s v u}
    (flow : @Flow n θ s v) (rest : Execution θ route v u) :
    (Execution.cons (.flow flow) rest).deliveries = rest.deliveries := rfl

theorem Execution.causal_flow_future {n θ route s v u}
    (flow : @Flow n θ s v) (rest : Execution θ route v u) (head : HeadRoutes n) :
    (Execution.cons (.flow flow) rest).futureHeadWires head = rest.futureHeadWires head := rfl

theorem Execution.causal_flow_count {n θ route s v u}
    (flow : @Flow n θ s v) (rest : Execution θ route v u) :
    (Execution.cons (.flow flow) rest).moveCount = rest.moveCount + 1 := rfl

theorem Execution.futureHeadWires_append {n θ route s v u}
    (first : @Execution n θ route s v) (rest : Execution θ route v u)
    (head : HeadRoutes n) :
    (first.append rest).futureHeadWires head =
      first.futureHeadWires head ++ rest.futureHeadWires head := by
  simp only [futureHeadWires,Execution.emissions_append,List.flatMap_append]

theorem Execution.futureHeadWires_future {n θ route s u}
    (e : @Execution n θ route s u) (head : HeadRoutes n) (hhead : StrictHeadRoutes head) :
    ∀ d ∈ e.futureHeadWires head, s.time < d.due := by
  intro d hd
  obtain ⟨event,he,hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨token,htoken,rfl⟩ := List.mem_map.mp hd
  exact (e.emission_time_bounds event he).1.trans_lt (hhead event.1 event.2 token htoken)

/-- Exact occurrence balance, with addition rather than truncated subtraction.
The ghost pool contains only unissued wires; it is absent from globalQ. -/
def HeadQueueBalance {n θ route s u} (tail : @Execution n θ route s u)
    (head : Snapshot 1) (globalQ : List (Delivery (n + 1))) (contacts : HeadRoutes n) : Prop :=
  (globalQ : Multiset (Delivery (n + 1))) + (tail.futureHeadWires contacts : Multiset (Delivery (n + 1))) =
    (s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (head.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1)))

theorem HeadQueueBalance.initial {n θ route s u}
    (tail : @Execution n θ route s u) (head : Snapshot 1) (contacts : HeadRoutes n)
    (hhead : head.pending = tail.headInputQueue contacts) :
    HeadQueueBalance tail head (s.pending.map Delivery.succ) contacts := by
  change (s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (tail.futureHeadWires contacts : Multiset (Delivery (n + 1))) = _
  rw [tail.futureHeadWires_map,hhead]

theorem HeadQueueBalance.operational_mem {n θ route s u}
    {tail : @Execution n θ route s u} {head : Snapshot 1}
    {globalQ : List (Delivery (n + 1))} {contacts : HeadRoutes n}
    (h : HeadQueueBalance tail head globalQ contacts)
    {d : Delivery (n + 1)} (hd : d ∈ globalQ) :
    d ∈ s.pending.map Delivery.succ ∨ d ∈ head.pending.map (Delivery.head (n := n)) := by
  have hm : d ∈ (globalQ : Multiset (Delivery (n + 1))) + (tail.futureHeadWires contacts : Multiset (Delivery (n + 1))) :=
    Multiset.mem_add.mpr (Or.inl hd)
  rw [h] at hm
  exact Multiset.mem_add.mp hm

/-- A local token due now cannot belong to the strictly future unissued pool.
It therefore has an actual occurrence in the operational queue. -/
theorem HeadQueueBalance.available_now {n θ route s u}
    {tail : @Execution n θ route s u} {head : Snapshot 1}
    {globalQ : List (Delivery (n + 1))} {contacts : HeadRoutes n}
    (h : HeadQueueBalance tail head globalQ contacts) (hcontacts : StrictHeadRoutes contacts)
    {d : Delivery (n + 1)}
    (hd : d ∈ s.pending.map Delivery.succ ∨ d ∈ head.pending.map (Delivery.head (n := n)))
    (hdate : d.due = s.time) : d ∈ globalQ := by
  have hm : d ∈ (s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (head.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1))) := Multiset.mem_add.mpr hd
  rw [← h] at hm
  rcases Multiset.mem_add.mp hm with hQ | hfuture
  · exact hQ
  · have ht := tail.futureHeadWires_future contacts hcontacts d hfuture
    rw [hdate] at ht
    exact (lt_irrefl _ ht).elim

/-- Consuming the same actual occurrence on both sides preserves the balance,
even when equal-valued tokens have multiplicity greater than one. -/
theorem causal_head_balance_remove {α : Type*} {Q Q' inputs inputs' future : Multiset α}
    (token : α) (h : Q + future = inputs)
    (hQ : Q = {token} + Q') (hlocal : inputs = {token} + inputs') :
    Q' + future = inputs' := by
  apply add_left_cancel (a := ({token} : Multiset α))
  calc
    {token} + (Q' + future) = Q + future := by rw [hQ]; ac_rfl
    _ = inputs := h
    _ = {token} + inputs' := hlocal

/-- A genuine tail FIRE appends its internal and head contacts. The matching
head contacts leave the ghost pool at that very jump. -/
theorem causal_head_balance_issue {α : Type*}
    {Q tail head internal issued future : Multiset α}
    (h : Q + (issued + future) = tail + head) :
    (Q + (internal + issued)) + future = (tail + internal) + head := by
  calc
    (Q + (internal + issued)) + future = (Q + (issued + future)) + internal := by ac_rfl
    _ = (tail + head) + internal := by rw [h]
    _ = (tail + internal) + head := by ac_rfl

/-- Actual local/global token balances transport the ghost invariant across
any jump, including repeated equal-valued delivery occurrences. -/
theorem causal_head_balance_transport {α : Type*}
    {Q Q' inputs inputs' ghost ghost' delivered internal issued : Multiset α}
    (hbefore : Q + ghost = inputs)
    (hlocal : inputs' + delivered = inputs + internal)
    (hglobal : Q' + delivered = Q + (internal + issued))
    (hghost : ghost = issued + ghost') : Q' + ghost' = inputs' := by
  apply add_right_cancel (b := delivered)
  calc
    (Q' + ghost') + delivered = (Q' + delivered) + ghost' := by ac_rfl
    _ = (Q + (internal + issued)) + ghost' := by rw [hglobal]
    _ = (Q + ghost) + internal := by rw [hghost]; ac_rfl
    _ = inputs + internal := by rw [hbefore]
    _ = inputs' + delivered := hlocal.symm

end KernelR.Hybrid
