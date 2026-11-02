import KernelR.HybridCausalHeadComplete

/-! Ordered local emission streams are retained by causal weaving. Their
multiset balance and genuine execution chronology determine each exact list. -/
namespace KernelR.Hybrid

theorem CausalTraceBalance.total_emission_count {n gE gD tE tD hE hD}
    (h : @CausalTraceBalance n gE gD tE tD hE hD) : gE.length = tE.length + hE.length := by
  have hc := congrArg Multiset.card h.emissions
  simpa only [Multiset.coe_card,Multiset.card_add,List.length_map] using hc

theorem CausalTraceBalance.total_delivery_count {n gE gD tE tD hE hD}
    (h : @CausalTraceBalance n gE gD tE tD hE hD) : gD.length = tD.length + hD.length := by
  have hc := congrArg Multiset.card h.deliveries
  simpa only [Multiset.coe_card,Multiset.card_add,List.length_map] using hc

theorem CausalTraceBalance.head_dates {n gE gD tE tD hE hD}
    (h : @CausalTraceBalance n gE gD tE tD hE hD) :
    (((gE.filter (fun ev => ev.1 = 0)).map Prod.snd) : Multiset ℝ) =
      (hE.map Prod.snd : Multiset ℝ) := by
  classical
  have he := congrArg (fun events : Multiset (Fin (n + 1) × ℝ) =>
    (events.filter (fun ev => ev.1 = 0)).map Prod.snd) h.emissions
  simpa only [Multiset.filter_add,Multiset.filter_coe,Multiset.map_add,Multiset.map_coe,
    List.filter_map,Fin.succ_ne_zero,decide_false,decide_true,List.filter_false,List.filter_true,
    List.map_nil,Multiset.coe_nil,zero_add,List.map_map,Function.comp_def] using he

theorem CausalTraceBalance.tail_dates {n gE gD tE tD hE hD}
    (h : @CausalTraceBalance n gE gD tE tD hE hD) (i : Fin n) :
    (((gE.filter (fun ev => ev.1 = i.succ)).map Prod.snd) : Multiset ℝ) =
      (((tE.filter (fun ev => ev.1 = i)).map Prod.snd) : Multiset ℝ) := by
  classical
  have hzero : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have he := congrArg (fun events : Multiset (Fin (n + 1) × ℝ) =>
    (events.filter (fun ev => ev.1 = i.succ)).map Prod.snd) h.emissions
  simpa only [Multiset.filter_add,Multiset.filter_coe,Multiset.map_add,Multiset.map_coe,
    List.filter_map,Fin.succ_inj,hzero,decide_false,List.filter_false,List.map_nil,
    Multiset.coe_nil,add_zero,List.map_map,Function.comp_def] using he

theorem CausalHeadWeave.head_emission_times {n θ θH route s u a b}
    {tail : @Execution n θ route s u} {head : @Execution 1 θH (fun _ _ => []) a b}
    {Q : List (Delivery (n + 1))} {contacts : HeadRoutes n}
    (weave : CausalHeadWeave tail head Q contacts) :
    weave.execution.emissionTimes 0 = head.emissionTimes 0 := by
  have hh : head.ledger.emissions.filter (fun ev => ev.1 = 0) = head.ledger.emissions :=
    List.filter_eq_self.mpr (fun ev _ => by simp only [decide_eq_true_eq]; exact Subsingleton.elim _ _)
  have he := weave.trace.head_dates
  change (weave.execution.emissionTimes 0 : Multiset ℝ) =
    (head.ledger.emissions.map Prod.snd : Multiset ℝ) at he
  have hright : (head.ledger.emissions.map Prod.snd : Multiset ℝ) =
      (head.emissionTimes 0 : Multiset ℝ) := by
    rw [Execution.emissionTimes,hh]
  have hp : (weave.execution.emissionTimes 0).Perm (head.emissionTimes 0) :=
    Quotient.exact (he.trans hright)
  exact List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ => le_antisymm)
    (weave.execution.emissionTimes_chronological 0) (head.emissionTimes_chronological 0) hp

theorem CausalHeadWeave.tail_emission_times {n θ θH route s u a b}
    {tail : @Execution n θ route s u} {head : @Execution 1 θH (fun _ _ => []) a b}
    {Q : List (Delivery (n + 1))} {contacts : HeadRoutes n}
    (weave : CausalHeadWeave tail head Q contacts) (i : Fin n) :
    weave.execution.emissionTimes i.succ = tail.emissionTimes i := by
  have hp : (weave.execution.emissionTimes i.succ).Perm (tail.emissionTimes i) :=
    Quotient.exact (weave.trace.tail_dates i)
  exact List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ => le_antisymm)
    (weave.execution.emissionTimes_chronological i.succ) (tail.emissionTimes_chronological i) hp

end KernelR.Hybrid
