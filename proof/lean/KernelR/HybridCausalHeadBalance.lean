import KernelR.HybridCausalHeadJump

/-! Preservation of the occurrence balance across genuine lifted jumps.
The local and global conservation equations supply the algebra uniformly. -/
namespace KernelR.Hybrid

theorem prependRouted_tail_issued {n} (route : Router n) (contacts : HeadRoutes n)
    (events : List (Fin n × ℝ)) :
    ((events.map (fun ev => (ev.1.succ,ev.2))).flatMap
      (fun ev => prependRouted route contacts ev.1 ev.2) : Multiset (Delivery (n + 1))) =
      ((events.flatMap (fun ev => route ev.1 ev.2)).map Delivery.succ : Multiset (Delivery (n + 1))) +
      (events.flatMap (fun ev => (contacts ev.1 ev.2).map (Delivery.head (n := n))) : Multiset (Delivery (n + 1))) := by
  induction events with
  | nil => simp
  | cons ev rest ih =>
    rw [show ((ev :: rest).map (fun e => (e.1.succ,e.2))).flatMap
        (fun e => prependRouted route contacts e.1 e.2) =
        ((route ev.1 ev.2).map Delivery.succ ++
          (contacts ev.1 ev.2).map (Delivery.head (n := n))) ++
        (rest.map (fun e => (e.1.succ,e.2))).flatMap
          (fun e => prependRouted route contacts e.1 e.2) by rfl]
    simp only [List.flatMap_cons,List.map_append,← Multiset.coe_add]
    rw [ih]
    ac_rfl

theorem prependRouted_head_issued {n} (route : Router n) (contacts : HeadRoutes n)
    (events : List (Fin 1 × ℝ)) :
    (events.map (fun ev => ((0 : Fin (n + 1)),ev.2))).flatMap
      (fun ev => prependRouted route contacts ev.1 ev.2) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro ev hev
  obtain ⟨event,hevent,rfl⟩ := List.mem_map.mp hev
  rfl

theorem HeadQueueBalance.urgent_to {n θ route s u}
    {tail : @Execution n θ route s u} {head : Snapshot 1}
    {Q : List (Delivery (n + 1))} {contacts : HeadRoutes n}
    (h : HeadQueueBalance tail head Q contacts) {T : ℝ}
    (htail : ∀ d ∈ s.pending, T ≤ d.due)
    (hhead : ∀ d ∈ head.pending, T ≤ d.due) : ∀ d ∈ Q, T ≤ d.due := by
  intro d hd
  rcases h.operational_mem hd with ht | hh
  · obtain ⟨token,htoken,rfl⟩ := List.mem_map.mp ht
    exact htail token htoken
  · obtain ⟨token,htoken,rfl⟩ := List.mem_map.mp hh
    exact hhead token htoken

theorem HeadQueueBalance.rebase {n θ route s u v z}
    {first : @Execution n θ route s u} {second : Execution θ route v z}
    {a b : Snapshot 1} {Q : List (Delivery (n + 1))} {contacts : HeadRoutes n}
    (h : HeadQueueBalance first a Q contacts)
    (htail : v.pending = s.pending) (hhead : b.pending = a.pending)
    (hghost : second.futureHeadWires contacts = first.futureHeadWires contacts) :
    HeadQueueBalance second b Q contacts := by
  change (Q : Multiset (Delivery (n + 1))) +
    (second.futureHeadWires contacts : Multiset (Delivery (n + 1))) = _
  rw [hghost,htail,hhead]
  exact h

theorem HeadQueueBalance.after_tail_jump {n θ route s v u}
    (j : @Jump n route s v) (rest : Execution θ route v u) (a : Snapshot 1)
    (Q Q' : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    (g : Jump (prependRouted route contacts) (s.prependQueued a Q) (v.prependQueued a Q'))
    (he : g.ledger.emissions = j.ledger.emissions.map (fun ev => (ev.1.succ,ev.2)))
    (hd : g.deliveries = j.deliveries.map Delivery.succ)
    (h : HeadQueueBalance (.cons (.jump j) rest) a Q contacts) :
    HeadQueueBalance rest a Q' contacts := by
  let D : Multiset (Delivery (n + 1)) := j.deliveries.map Delivery.succ
  let U : Multiset (Delivery (n + 1)) :=
    (j.ledger.emissions.flatMap (fun ev => route ev.1 ev.2)).map Delivery.succ
  let H : Multiset (Delivery (n + 1)) :=
    j.ledger.emissions.flatMap (fun ev => (contacts ev.1 ev.2).map (Delivery.head (n := n)))
  have ht := congrArg (Multiset.map Delivery.succ) j.token_balance
  simp only [Multiset.map_add,Multiset.map_coe] at ht
  have hlocal : ((v.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (a.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1)))) + D =
      ((s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (a.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1)))) + U := by
    calc
      _ = ((v.pending.map Delivery.succ : Multiset (Delivery (n + 1))) + D) +
          (a.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1))) := by ac_rfl
      _ = ((s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) + U) +
          (a.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1))) := by rw [ht]
      _ = _ := by ac_rfl
  have hg := g.token_balance
  rw [hd,he,prependRouted_tail_issued] at hg
  have hglobal : (Q' : Multiset (Delivery (n + 1))) + D =
      (Q : Multiset (Delivery (n + 1))) + (U + H) := hg
  have hghost :
      ((Execution.cons (.jump j) rest).futureHeadWires contacts : Multiset (Delivery (n + 1))) =
        H + (rest.futureHeadWires contacts : Multiset (Delivery (n + 1))) := by
    simp only [Execution.futureHeadWires,Execution.ledger,Move.ledger,Ledger.add,List.flatMap_append,
      ← Multiset.coe_add]
    rfl
  exact causal_head_balance_transport h hlocal hglobal hghost

theorem HeadQueueBalance.after_head_jump {n θ route s u}
    (tail : @Execution n θ route s u) {headRoute : Router 1} {a b : Snapshot 1}
    (j : Jump headRoute a b) (hroute : ∀ i t, headRoute i t = [])
    (Q Q' : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    (g : Jump (prependRouted route contacts) (s.prependQueued a Q) (s.prependQueued b Q'))
    (he : g.ledger.emissions = j.ledger.emissions.map (fun ev => ((0 : Fin (n + 1)),ev.2)))
    (hd : g.deliveries = j.deliveries.map (Delivery.head (n := n)))
    (h : HeadQueueBalance tail a Q contacts) : HeadQueueBalance tail b Q' contacts := by
  let D : Multiset (Delivery (n + 1)) := j.deliveries.map (Delivery.head (n := n))
  have hissued : j.ledger.emissions.flatMap (fun ev => headRoute ev.1 ev.2) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun ev _ => hroute ev.1 ev.2)
  have ht := congrArg (Multiset.map (Delivery.head (n := n))) j.token_balance
  simp only [Multiset.map_add,Multiset.map_coe,hissued,Multiset.coe_nil,add_zero] at ht
  have hlocal : ((s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (b.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1)))) + D =
      ((s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (a.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1)))) + 0 := by
    calc
      _ = (s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
          ((b.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1))) + D) := by ac_rfl
      _ = _ := by rw [ht,add_zero]
  have hg := g.token_balance
  rw [hd,he,prependRouted_head_issued] at hg
  have hglobal : (Q' : Multiset (Delivery (n + 1))) + D =
      (Q : Multiset (Delivery (n + 1))) + (0 + 0) := by
    change (Q' : Multiset (Delivery (n + 1))) + D =
      (Q : Multiset (Delivery (n + 1))) + (0 : Multiset (Delivery (n + 1))) at hg
    simpa only [zero_add] using hg
  exact causal_head_balance_transport h hlocal hglobal (zero_add _).symm

end KernelR.Hybrid
