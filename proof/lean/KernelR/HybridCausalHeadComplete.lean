import KernelR.HybridCausalHeadExecution

/-! Complete finite horizons of a causal feed-forward product. Terminal
saturation comes from the two genuine local terminal states and queue balance. -/
namespace KernelR.Hybrid

theorem Snapshot.prependQueued_no_jump {n} (tail : Snapshot n) (head : Snapshot 1)
    (Q : List (Delivery (n + 1))) (global : Router (n + 1))
    (tailRoute : Router n) (headRoute : Router 1) (hclock : tail.time = head.time)
    (htail : ∀ v, IsEmpty (Jump tailRoute tail v))
    (hhead : ∀ v, IsEmpty (Jump headRoute head v))
    (hfuture : ∀ d ∈ Q, tail.time < d.due) (v : Snapshot (n + 1)) :
    IsEmpty (Jump global (tail.prependQueued head Q) v) := by
  constructor
  intro j
  cases j with
  | fire i hm hq =>
    cases i using Fin.cases with
    | zero => exact (hhead _).false (.fire head 0 hm hq)
    | succ i => exact (htail _).false (.fire tail i hm hq)
  | fastEnd i hm hq =>
    cases i using Fin.cases with
    | zero => exact (hhead _).false (.fastEnd head 0 hm hq)
    | succ i => exact (htail _).false (.fastEnd tail i hm hq)
  | reopen i hm hq =>
    cases i using Fin.cases with
    | zero => exact (hhead _).false (.reopen head 0 hm hq)
    | succ i => exact (htail _).false (.reopen tail i hm hq)
  | mark i p hm hq =>
    cases i using Fin.cases with
    | zero => exact (hhead _).false (.mark head 0 p hm hq)
    | succ i => exact (htail _).false (.mark tail i p hm hq)
  | silent i p hm hq =>
    cases i using Fin.cases with
    | zero => exact (hhead _).false (.silent head 0 p hm hq)
    | succ i => exact (htail _).false (.silent tail i p hm hq)
  | error i p hm hq =>
    cases i using Fin.cases with
    | zero => exact (hhead _).false (.error head 0 p hm hq)
    | succ i => exact (htail _).false (.error tail i p hm hq)
  | auxReady i p hm hq =>
    cases i using Fin.cases with
    | zero => exact (hhead _).false (.auxReady head 0 p hm hq)
    | succ i => exact (htail _).false (.auxReady tail i p hm hq)
  | rawEnd i p origin hr ht =>
    cases i using Fin.cases with
    | zero => exact (hhead _).false (.rawEnd head 0 p origin hr (hclock.symm.trans ht))
    | succ i => exact (htail _).false (.rawEnd tail i p origin hr ht)
  | arrive d before after hqueue hdue hfree =>
    have hm : d ∈ Q := by change d ∈ (tail.prependQueued head Q).pending; rw [hqueue]; simp
    have ht := hfuture d hm
    change d.due = tail.time at hdue
    rw [hdue] at ht
    exact lt_irrefl _ ht

theorem CausalHeadWeave.complete {n θ θH route s u a b T}
    {tail : @Execution n θ route s u} {head : @Execution 1 θH (fun _ _ => []) a b}
    {Q : List (Delivery (n + 1))} {contacts : HeadRoutes n}
    (weave : CausalHeadWeave tail head Q contacts)
    (htail : CompleteThrough tail T) (hhead : CompleteThrough head T) :
    CompleteThrough weave.execution T := by
  have hfinish : u.time = b.time := htail.1.trans hhead.1.symm
  have hfuture : ∀ d ∈ weave.pending, u.time < d.due := by
    intro d hd
    have hm : d ∈ (weave.pending : Multiset (Delivery (n + 1))) := hd
    rw [weave.terminal] at hm
    rcases Multiset.mem_add.mp hm with ht | hh
    · obtain ⟨token,htoken,rfl⟩ := List.mem_map.mp ht
      rw [htail.1]
      exact htail.2.2 token htoken
    · obtain ⟨token,htoken,rfl⟩ := List.mem_map.mp hh
      rw [htail.1]
      exact hhead.2.2 token htoken
  refine ⟨htail.1,fun v => u.prependQueued_no_jump b weave.pending (prependRouted route contacts)
    route (fun _ _ => []) hfinish htail.2.1 hhead.2.1 hfuture v,?_⟩
  intro d hd
  rw [← htail.1]
  exact hfuture d hd

theorem Execution.prepend_causal_complete {n θ θH route s u a b T}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b)
    (hstart : s.time = a.time) (htail : CompleteThrough tail T) (hhead : CompleteThrough head T)
    (contacts : HeadRoutes n) (hcontacts : StrictHeadRoutes contacts)
    (Q : List (Delivery (n + 1))) (hbalance : HeadQueueBalance tail a Q contacts) :
    ∃ (Q' : List (Delivery (n + 1)))
      (global : Execution (prependParameters θH θ) (prependRouted route contacts)
        (s.prependQueued a Q) (u.prependQueued b Q')),
      CompleteThrough global T ∧
      (Q' : Multiset (Delivery (n + 1))) =
        (u.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
          (b.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1))) ∧
      CausalTraceBalance global.ledger.emissions global.deliveries
        tail.ledger.emissions tail.deliveries head.ledger.emissions head.deliveries := by
  have hfinish : u.time = b.time := htail.1.trans hhead.1.symm
  obtain ⟨weave⟩ := tail.prepend_causal_result head hstart hfinish contacts hcontacts Q hbalance
  exact ⟨weave.pending,weave.execution,weave.complete htail hhead,weave.terminal,weave.trace⟩

theorem CausalHeadWeave.pending_empty {n θ θH route s u a b}
    {tail : @Execution n θ route s u} {head : @Execution 1 θH (fun _ _ => []) a b}
    {Q : List (Delivery (n + 1))} {contacts : HeadRoutes n}
    (weave : CausalHeadWeave tail head Q contacts)
    (htail : u.pending = []) (hhead : b.pending = []) : weave.pending = [] := by
  apply (Multiset.coe_eq_zero _).mp
  simpa only [htail,hhead,List.map_nil,Multiset.coe_nil,zero_add] using weave.terminal

end KernelR.Hybrid
