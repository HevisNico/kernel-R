import KernelR.HybridCausalHeadBalance
import KernelR.HybridCausalTransversality
import KernelR.HybridCausalSectionRuns

/-! Constructive feed-forward weaving. Local head calendars are proof data
derived from actual tail FIREs. The resulting execution issues each wire only
at the genuine global FIRE and consumes only already-issued occurrences. -/
namespace KernelR.Hybrid

structure CausalTraceBalance {n}
    (globalEvents : List (Fin (n + 1) × ℝ)) (globalDeliveries : List (Delivery (n + 1)))
    (tailEvents : List (Fin n × ℝ)) (tailDeliveries : List (Delivery n))
    (headEvents : List (Fin 1 × ℝ)) (headDeliveries : List (Delivery 1)) : Prop where
  emissions : (globalEvents : Multiset (Fin (n + 1) × ℝ)) =
    (tailEvents.map (fun ev => (ev.1.succ,ev.2)) : Multiset (Fin (n + 1) × ℝ)) +
      (headEvents.map (fun ev => ((0 : Fin (n + 1)),ev.2)) : Multiset (Fin (n + 1) × ℝ))
  deliveries : (globalDeliveries : Multiset (Delivery (n + 1))) =
    (tailDeliveries.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (headDeliveries.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1)))

theorem CausalTraceBalance.prepend_tail {n gE gD tE tD hE hD}
    (h : @CausalTraceBalance n gE gD tE tD hE hD)
    (events : List (Fin n × ℝ)) (deliveries : List (Delivery n)) :
    CausalTraceBalance ((events.map (fun ev => (ev.1.succ,ev.2))) ++ gE)
      (deliveries.map Delivery.succ ++ gD) (events ++ tE) (deliveries ++ tD) hE hD := by
  constructor
  · simp only [List.map_append,← Multiset.coe_add]
    rw [h.emissions]
    ac_rfl
  · simp only [List.map_append,← Multiset.coe_add]
    rw [h.deliveries]
    ac_rfl

theorem CausalTraceBalance.prepend_head {n gE gD tE tD hE hD}
    (h : @CausalTraceBalance n gE gD tE tD hE hD)
    (events : List (Fin 1 × ℝ)) (deliveries : List (Delivery 1)) :
    CausalTraceBalance ((events.map (fun ev => ((0 : Fin (n + 1)),ev.2))) ++ gE)
      (deliveries.map (Delivery.head (n := n)) ++ gD) tE tD (events ++ hE) (deliveries ++ hD) := by
  constructor
  · simp only [List.map_append,← Multiset.coe_add]
    rw [h.emissions]
    ac_rfl
  · simp only [List.map_append,← Multiset.coe_add]
    rw [h.deliveries]
    ac_rfl

/-- A concrete shared execution. Only physical snapshots and observable
lists index this result, so kernel checking does not compare full local traces. -/
structure CausalHeadResult {n} (θ : Fin n → Parameters) (θH : Fin 1 → Parameters)
    (route : Router n) (s u : Snapshot n) (a b : Snapshot 1)
    (Q : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    (tailEvents : List (Fin n × ℝ)) (tailDeliveries : List (Delivery n))
    (headEvents : List (Fin 1 × ℝ)) (headDeliveries : List (Delivery 1)) where
  pending : List (Delivery (n + 1))
  execution : Execution (prependParameters θH θ) (prependRouted route contacts)
    (s.prependQueued a Q) (u.prependQueued b pending)
  terminal : (pending : Multiset (Delivery (n + 1))) =
    (u.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
      (b.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1)))
  trace : CausalTraceBalance execution.ledger.emissions execution.deliveries
    tailEvents tailDeliveries headEvents headDeliveries

/-- The concrete weave preserves contact transversality and section runs from
the supplied local histories. Open runs retain their phase across foreign jumps
and flow subdivisions, so complete covers survive asynchronous interleaving. -/
structure CausalHeadWeave {n θ θH route s u a b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b)
    (Q : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    extends CausalHeadResult θ θH route s u a b Q contacts
      tail.ledger.emissions tail.deliveries head.ledger.emissions head.deliveries where
  contacts_transversal : tail.ContactsTransversal → head.ContactsTransversal →
    execution.ContactsTransversal
  tail_sections : ∀ kind i p first last count,
    SectionRun kind i p tail first last count →
      SectionRun kind i.succ p execution first last count
  head_sections : ∀ kind p first last count,
    SectionRun kind 0 p head first last count →
      SectionRun kind 0 p execution first last count

theorem CausalHeadWeave.prepend_tail_jump {n θ θH route s v u a b}
    (j : @Jump n route s v) (rest : Execution θ route v u)
    (head : @Execution 1 θH (fun _ _ => []) a b)
    (Q Qnext : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    (g : Jump (prependRouted route contacts) (s.prependQueued a Q) (v.prependQueued a Qnext))
    (he : g.ledger.emissions = j.ledger.emissions.map (fun ev => (ev.1.succ,ev.2)))
    (hd : g.deliveries = j.deliveries.map Delivery.succ)
    (hrest : Nonempty (CausalHeadWeave rest head Qnext contacts)) :
    Nonempty (CausalHeadWeave (.cons (.jump j) rest) head Q contacts) := by
  obtain ⟨w⟩ := hrest
  refine ⟨{
    pending := w.pending, execution := .cons (.jump g) w.execution
    terminal := w.terminal, trace := ?_, contacts_transversal := ?_
    tail_sections := ?_, head_sections := ?_
  }⟩
  · simpa only [Execution.ledger,Move.ledger,Ledger.add,Execution.deliveries,Move.deliveries,
      he,hd] using w.trace.prepend_tail j.ledger.emissions j.deliveries
  · intro ht hh
    exact ⟨j.prependQueued_tail_contactTransversal ht.1 a Q Qnext contacts g,
      w.contacts_transversal ht.2 hh⟩
  · intro kind i p first last count run
    obtain ⟨middle,stepCount,tailCount,rfl,step,tailRun⟩ := SectionRun.cons_iff.mp run
    exact .cons (step.prependQueued_tail_jump a Q Qnext contacts g)
      (w.tail_sections kind i p middle last tailCount tailRun)
  · intro kind p first last count run
    simpa only [zero_add] using SectionRun.cons
      (SectionStep.prependQueued_idle_head run.initial_valid Q Qnext contacts g)
      (w.head_sections kind p first last count run)

theorem CausalHeadWeave.prepend_head_jump {n θ θH route s u a v b}
    (tail : @Execution n θ route s u) (j : Jump (fun _ _ => []) a v)
    (rest : Execution θH (fun _ _ => []) v b) (hclock : s.time = a.time)
    (Q Qnext : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    (g : Jump (prependRouted route contacts) (s.prependQueued a Q) (s.prependQueued v Qnext))
    (he : g.ledger.emissions = j.ledger.emissions.map (fun ev => ((0 : Fin (n + 1)),ev.2)))
    (hd : g.deliveries = j.deliveries.map (Delivery.head (n := n)))
    (hrest : Nonempty (CausalHeadWeave tail rest Qnext contacts)) :
    Nonempty (CausalHeadWeave tail (.cons (.jump j) rest) Q contacts) := by
  obtain ⟨w⟩ := hrest
  refine ⟨{
    pending := w.pending, execution := .cons (.jump g) w.execution
    terminal := w.terminal, trace := ?_, contacts_transversal := ?_
    tail_sections := ?_, head_sections := ?_
  }⟩
  · simpa only [Execution.ledger,Move.ledger,Ledger.add,Execution.deliveries,Move.deliveries,
      he,hd] using w.trace.prepend_head j.ledger.emissions j.deliveries
  · intro ht hh
    exact ⟨j.prependQueued_head_contactTransversal hh.1 s hclock Q Qnext contacts g,
      w.contacts_transversal ht hh.2⟩
  · intro kind i p first last count run
    simpa only [zero_add] using SectionRun.cons
      (SectionStep.prependQueued_idle_tail run.initial_valid Q Qnext contacts g)
      (w.tail_sections kind i p first last count run)
  · intro kind p first last count run
    obtain ⟨middle,stepCount,tailCount,rfl,step,tailRun⟩ := SectionRun.cons_iff.mp run
    exact .cons (step.prependQueued_head_jump s Q Qnext contacts g)
      (w.head_sections kind p middle last tailCount tailRun)

theorem CausalHeadWeave.prepend_flow {n θ θH route s v u a c b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b)
    (tailRest : Execution θ route v u) (headRest : Execution θH (fun _ _ => []) c b)
    (Q : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    (flow : Flow (prependParameters θH θ) (s.prependQueued a Q) (v.prependQueued c Q))
    (het : tailRest.ledger.emissions = tail.ledger.emissions)
    (hdt : tailRest.deliveries = tail.deliveries)
    (heh : headRest.ledger.emissions = head.ledger.emissions)
    (hdh : headRest.deliveries = head.deliveries)
    (htail : tail.ContactsTransversal → tailRest.ContactsTransversal)
    (hhead : head.ContactsTransversal → headRest.ContactsTransversal)
    (tailSections : ∀ kind i p first last count,
      SectionRun kind i p tail first last count →
        SectionStep (route := prependRouted route contacts) kind i.succ p (.flow flow) first first 0 ∧
          SectionRun kind i p tailRest first last count)
    (headSections : ∀ kind p first last count,
      SectionRun kind 0 p head first last count →
        SectionStep (route := prependRouted route contacts) kind 0 p (.flow flow) first first 0 ∧
          SectionRun kind 0 p headRest first last count)
    (hrest : Nonempty (CausalHeadWeave tailRest headRest Q contacts)) :
    Nonempty (CausalHeadWeave tail head Q contacts) := by
  obtain ⟨w⟩ := hrest
  refine ⟨{
    pending := w.pending, execution := .cons (.flow flow) w.execution
    terminal := w.terminal, trace := ?_, contacts_transversal := ?_
    tail_sections := ?_, head_sections := ?_
  }⟩
  · change CausalTraceBalance w.execution.ledger.emissions w.execution.deliveries
      tail.ledger.emissions tail.deliveries head.ledger.emissions head.deliveries
    rw [← het,← hdt,← heh,← hdh]
    exact w.trace
  · intro ht hh
    exact w.contacts_transversal (htail ht) (hhead hh)
  · intro kind i p first last count run
    obtain ⟨step,rest⟩ := tailSections kind i p first last count run
    simpa only [zero_add] using SectionRun.cons step
      (w.tail_sections kind i p first last count rest)
  · intro kind p first last count run
    obtain ⟨step,rest⟩ := headSections kind p first last count run
    simpa only [zero_add] using SectionRun.cons step
      (w.head_sections kind p first last count rest)

/-- One strictly smaller pair of local paths, together with a genuine prefix
that lifts any completed product of those remaining paths. -/
structure CausalHeadStep {n} (θ : Fin n → Parameters) (θH : Fin 1 → Parameters)
    (route : Router n) (u : Snapshot n) (b : Snapshot 1) (contacts : HeadRoutes n)
    (bound : ℕ) (target : Type) where
  tailState : Snapshot n
  headState : Snapshot 1
  tail : Execution θ route tailState u
  head : Execution θH (fun _ _ => []) headState b
  pending : List (Delivery (n + 1))
  decrease : tail.moveCount + head.moveCount < bound
  clock : tailState.time = headState.time
  balance : HeadQueueBalance tail headState pending contacts
  lift : Nonempty (CausalHeadWeave tail head pending contacts) → Nonempty target

theorem CausalHeadStep.pack {n θ θH route u b contacts bound v c} {target : Type}
    (left : @Execution n θ route v u) (right : @Execution 1 θH (fun _ _ => []) c b)
    (hdec : left.moveCount + right.moveCount < bound) (hsync : v.time = c.time)
    (Qnext : List (Delivery (n + 1))) (hnext : HeadQueueBalance left c Qnext contacts)
    (lift : Nonempty (CausalHeadWeave left right Qnext contacts) → Nonempty target) :
    Nonempty (CausalHeadStep θ θH route u b contacts bound target) :=
  ⟨⟨v,c,left,right,Qnext,hdec,hsync,hnext,lift⟩⟩

theorem Execution.causal_tail_jump_step {n θ θH route s vT u a b N}
    (jT : @Jump n route s vT) (restT : Execution θ route vT u)
    (eH : @Execution 1 θH (fun _ _ => []) a b) (hstart : s.time = a.time)
    (contacts : HeadRoutes n) (hcontacts : StrictHeadRoutes contacts)
    (Q : List (Delivery (n + 1)))
    (hbalance : HeadQueueBalance (.cons (.jump jT) restT) a Q contacts)
    (hsize : (Execution.cons (.jump jT) restT).moveCount + eH.moveCount = N) :
    Nonempty (CausalHeadStep θ θH route u b contacts N
      (CausalHeadWeave (.cons (.jump jT) restT) eH Q contacts)) := by
  have havailable : ∀ d ∈ jT.deliveries, d.succ ∈ Q := by
    intro d hd
    apply hbalance.available_now hcontacts (Or.inl (List.mem_map.mpr
      ⟨d,jT.delivery_from_queue d hd,rfl⟩))
    exact jT.delivery_due d hd
  obtain ⟨Qnext,g,heG,hdG⟩ := jT.prependQueued_tail a Q contacts havailable
  have hnext := HeadQueueBalance.after_tail_jump jT restT a Q Qnext contacts g heG hdG hbalance
  exact CausalHeadStep.pack restT eH (by simp only [Execution.moveCount] at hsize ⊢; omega)
    (jT.time_unchanged.trans hstart) Qnext hnext
    (fun result => CausalHeadWeave.prepend_tail_jump jT restT eH Q Qnext contacts g heG hdG result)

theorem Execution.causal_head_jump_step {n θ θH route s u a vH b N}
    (eT : @Execution n θ route s u) (jH : Jump (fun _ _ => []) a vH)
    (restH : @Execution 1 θH (fun _ _ => []) vH b) (hstart : s.time = a.time)
    (contacts : HeadRoutes n) (hcontacts : StrictHeadRoutes contacts)
    (Q : List (Delivery (n + 1))) (hbalance : HeadQueueBalance eT a Q contacts)
    (hsize : eT.moveCount + (Execution.cons (.jump jH) restH).moveCount = N) :
    Nonempty (CausalHeadStep θ θH route u b contacts N
      (CausalHeadWeave eT (.cons (.jump jH) restH) Q contacts)) := by
  have havailable : ∀ d ∈ jH.deliveries, Delivery.head (n := n) d ∈ Q := by
    intro d hd
    apply hbalance.available_now hcontacts (Or.inr (List.mem_map.mpr
      ⟨d,jH.delivery_from_queue d hd,rfl⟩))
    exact (jH.delivery_due d hd).trans hstart.symm
  obtain ⟨Qnext,g,heG,hdG⟩ := jH.prependQueued_head (fun _ _ => rfl) s hstart Q route contacts havailable
  have hnext := HeadQueueBalance.after_head_jump eT
    jH (fun _ _ => rfl) Q Qnext contacts g heG hdG hbalance
  exact CausalHeadStep.pack eT restH (by simp only [Execution.moveCount] at hsize ⊢; omega)
    (hstart.trans jH.time_unchanged.symm) Qnext hnext
    (fun result => CausalHeadWeave.prepend_head_jump eT jH restH hstart Q Qnext contacts g heG hdG result)

theorem Execution.causal_flow_short_step {n θ θH route s vT u a vH b N}
    (fT : @Flow n θ s vT) (restT : Execution θ route vT u)
    (fH : @Flow 1 θH a vH) (restH : Execution θH (fun _ _ => []) vH b)
    (hstart : s.time = a.time) (contacts : HeadRoutes n) (Q : List (Delivery (n + 1)))
    (hbalance : HeadQueueBalance (.cons (.flow fT) restT) a Q contacts)
    (hsize : (Execution.cons (.flow fT) restT).moveCount +
      (Execution.cons (.flow fH) restH).moveCount = N) (hshort : vT.time < vH.time) :
    Nonempty (CausalHeadStep θ θH route u b contacts N
      (CausalHeadWeave (.cons (.flow fT) restT) (.cons (.flow fH) restH) Q contacts)) := by
  have hprefix : a.time < vT.time := by rw [← hstart]; exact fT.positive
  obtain ⟨prefixH,suffixH,hPrefixPath,hSuffixPath⟩ := fH.cut_pair_exists hprefix hshort
  let remainingH : Execution θH (fun _ _ => []) (fH.at vT.time) b := .cons (.flow suffixH) restH
  obtain ⟨combined,hCombinedPath⟩ := fT.prependQueued_exists prefixH hstart rfl Q
    (hbalance.urgent_to fT.pending_urgent prefixH.pending_urgent)
  have hnext : HeadQueueBalance restT (fH.at vT.time) Q contacts :=
    hbalance.rebase fT.queue_fixed prefixH.queue_fixed (Execution.causal_flow_future fT restT contacts).symm
  exact CausalHeadStep.pack restT remainingH (by simp only [remainingH,Execution.causal_flow_count] at hsize ⊢; omega)
    rfl Q hnext (fun result => CausalHeadWeave.prepend_flow (.cons (.flow fT) restT)
      (.cons (.flow fH) restH) restT remainingH Q contacts combined
      (Execution.causal_flow_emissions fT restT).symm (Execution.causal_flow_deliveries fT restT).symm
      ((Execution.causal_flow_emissions suffixH restH).trans (Execution.causal_flow_emissions fH restH).symm)
      ((Execution.causal_flow_deliveries suffixH restH).trans (Execution.causal_flow_deliveries fH restH).symm)
      (fun h => h) (fun h => h)
      (by
        intro kind i p first last count run
        obtain ⟨step,tail⟩ := run.flow_cons
        exact ⟨step.prependQueued_tail_flow Q contacts combined
          (by intro t c; rw [hCombinedPath]; rfl),tail⟩)
      (by
        intro kind p first last count run
        obtain ⟨step,tail⟩ := run.flow_cons
        have before := step.flow_cut_prefix hprefix hshort prefixH hPrefixPath
        have after := step.flow_cut_suffix hprefix hshort suffixH hSuffixPath
        refine ⟨before.prependQueued_head_flow hstart rfl Q contacts combined
          (by intro t c; rw [hCombinedPath]; rfl),?_⟩
        simpa only [zero_add] using SectionRun.cons after tail)
      result)

theorem Execution.causal_flow_equal_step {n θ θH route s vT u a vH b N}
    (fT : @Flow n θ s vT) (restT : Execution θ route vT u)
    (fH : @Flow 1 θH a vH) (restH : Execution θH (fun _ _ => []) vH b)
    (hstart : s.time = a.time) (contacts : HeadRoutes n) (Q : List (Delivery (n + 1)))
    (hbalance : HeadQueueBalance (.cons (.flow fT) restT) a Q contacts)
    (hsize : (Execution.cons (.flow fT) restT).moveCount +
      (Execution.cons (.flow fH) restH).moveCount = N) (hequal : vT.time = vH.time) :
    Nonempty (CausalHeadStep θ θH route u b contacts N
      (CausalHeadWeave (.cons (.flow fT) restT) (.cons (.flow fH) restH) Q contacts)) := by
  obtain ⟨combined,hCombinedPath⟩ := fT.prependQueued_exists fH hstart hequal Q
    (hbalance.urgent_to fT.pending_urgent (by simpa only [hequal] using fH.pending_urgent))
  have hnext : HeadQueueBalance restT vH Q contacts :=
    hbalance.rebase fT.queue_fixed fH.queue_fixed (Execution.causal_flow_future fT restT contacts).symm
  exact CausalHeadStep.pack restT restH (by simp only [Execution.moveCount] at hsize ⊢; omega)
    hequal Q hnext (fun result => CausalHeadWeave.prepend_flow (.cons (.flow fT) restT)
      (.cons (.flow fH) restH) restT restH Q contacts combined
      (Execution.causal_flow_emissions fT restT).symm (Execution.causal_flow_deliveries fT restT).symm
      (Execution.causal_flow_emissions fH restH).symm (Execution.causal_flow_deliveries fH restH).symm
      (fun h => h) (fun h => h)
      (by
        intro kind i p first last count run
        obtain ⟨step,tail⟩ := run.flow_cons
        exact ⟨step.prependQueued_tail_flow Q contacts combined
          (by intro t c; rw [hCombinedPath]; rfl),tail⟩)
      (by
        intro kind p first last count run
        obtain ⟨step,tail⟩ := run.flow_cons
        exact ⟨step.prependQueued_head_flow hstart hequal Q contacts combined
          (by intro t c; rw [hCombinedPath]; rfl),tail⟩)
      result)

theorem Execution.causal_flow_long_step {n θ θH route s vT u a vH b N}
    (fT : @Flow n θ s vT) (restT : Execution θ route vT u)
    (fH : @Flow 1 θH a vH) (restH : Execution θH (fun _ _ => []) vH b)
    (hstart : s.time = a.time) (contacts : HeadRoutes n) (Q : List (Delivery (n + 1)))
    (hbalance : HeadQueueBalance (.cons (.flow fT) restT) a Q contacts)
    (hsize : (Execution.cons (.flow fT) restT).moveCount +
      (Execution.cons (.flow fH) restH).moveCount = N) (hlong : vH.time < vT.time) :
    Nonempty (CausalHeadStep θ θH route u b contacts N
      (CausalHeadWeave (.cons (.flow fT) restT) (.cons (.flow fH) restH) Q contacts)) := by
  have hprefix : s.time < vH.time := by rw [hstart]; exact fH.positive
  obtain ⟨prefixT,suffixT,hPrefixPath,hSuffixPath⟩ := fT.cut_pair_exists hprefix hlong
  let remainingT : Execution θ route (fT.at vH.time) u := .cons (.flow suffixT) restT
  obtain ⟨combined,hCombinedPath⟩ := prefixT.prependQueued_exists fH hstart rfl Q
    (hbalance.urgent_to prefixT.pending_urgent fH.pending_urgent)
  have hnext : HeadQueueBalance remainingT vH Q contacts :=
    hbalance.rebase prefixT.queue_fixed fH.queue_fixed ((Execution.causal_flow_future suffixT restT contacts).trans (Execution.causal_flow_future fT restT contacts).symm)
  exact CausalHeadStep.pack remainingT restH (by simp only [remainingT,Execution.causal_flow_count] at hsize ⊢; omega)
    rfl Q hnext (fun result => CausalHeadWeave.prepend_flow (.cons (.flow fT) restT)
      (.cons (.flow fH) restH) remainingT restH Q contacts combined
      ((Execution.causal_flow_emissions suffixT restT).trans (Execution.causal_flow_emissions fT restT).symm)
      ((Execution.causal_flow_deliveries suffixT restT).trans (Execution.causal_flow_deliveries fT restT).symm)
      (Execution.causal_flow_emissions fH restH).symm (Execution.causal_flow_deliveries fH restH).symm
      (fun h => h) (fun h => h)
      (by
        intro kind i p first last count run
        obtain ⟨step,tail⟩ := run.flow_cons
        have before := step.flow_cut_prefix hprefix hlong prefixT hPrefixPath
        have after := step.flow_cut_suffix hprefix hlong suffixT hSuffixPath
        refine ⟨before.prependQueued_tail_flow Q contacts combined
          (by intro t c; rw [hCombinedPath]; rfl),?_⟩
        simpa only [zero_add] using SectionRun.cons after tail)
      (by
        intro kind p first last count run
        obtain ⟨step,tail⟩ := run.flow_cons
        exact ⟨step.prependQueued_head_flow hstart rfl Q contacts combined
          (by intro t c; rw [hCombinedPath]; rfl),tail⟩)
      result)

theorem Execution.causal_flow_step {n θ θH route s vT u a vH b N}
    (fT : @Flow n θ s vT) (restT : Execution θ route vT u)
    (fH : @Flow 1 θH a vH) (restH : Execution θH (fun _ _ => []) vH b)
    (hstart : s.time = a.time) (contacts : HeadRoutes n) (Q : List (Delivery (n + 1)))
    (hbalance : HeadQueueBalance (.cons (.flow fT) restT) a Q contacts)
    (hsize : (Execution.cons (.flow fT) restT).moveCount +
      (Execution.cons (.flow fH) restH).moveCount = N) :
    Nonempty (CausalHeadStep θ θH route u b contacts N
      (CausalHeadWeave (.cons (.flow fT) restT) (.cons (.flow fH) restH) Q contacts)) := by
  rcases lt_trichotomy vT.time vH.time with hshort | hequal | hlong
  · exact Execution.causal_flow_short_step fT restT fH restH hstart contacts Q hbalance hsize hshort
  · exact Execution.causal_flow_equal_step fT restT fH restH hstart contacts Q hbalance hsize hequal
  · exact Execution.causal_flow_long_step fT restT fH restH hstart contacts Q hbalance hsize hlong

theorem Execution.causal_head_step {n θ θH route s u a b N}
    (eT : @Execution n θ route s u) (eH : @Execution 1 θH (fun _ _ => []) a b)
    (hstart : s.time = a.time) (hfinish : u.time = b.time)
    (contacts : HeadRoutes n) (hcontacts : StrictHeadRoutes contacts)
    (Q : List (Delivery (n + 1))) (hbalance : HeadQueueBalance eT a Q contacts)
    (hsize : eT.moveCount + eH.moveCount = N) (hpositive : 0 < N) :
    Nonempty (CausalHeadStep θ θH route u b contacts N (CausalHeadWeave eT eH Q contacts)) := by
  cases eT with
  | nil =>
    cases eH with
    | nil => exact False.elim (by simp only [Execution.moveCount] at hsize; omega)
    | cons mH restH =>
      cases mH with
      | flow fH => exact False.elim (by linarith [fH.positive,restH.time_monotone])
      | jump jH => exact Execution.causal_head_jump_step (.nil s) jH restH hstart contacts hcontacts Q hbalance hsize
  | cons mT restT =>
    cases mT with
    | jump jT => exact Execution.causal_tail_jump_step jT restT eH hstart contacts hcontacts Q hbalance hsize
    | flow fT =>
      cases eH with
      | nil => exact False.elim (by linarith [fT.positive,restT.time_monotone])
      | cons mH restH =>
        cases mH with
        | jump jH => exact Execution.causal_head_jump_step (.cons (.flow fT) restT) jH restH hstart contacts hcontacts Q hbalance hsize
        | flow fH => exact Execution.causal_flow_step fT restT fH restH hstart contacts Q hbalance hsize

theorem Execution.prepend_causal_zero {n θ θH route s u a b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b)
    (Q : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    (hbalance : HeadQueueBalance tail a Q contacts) (hzero : tail.moveCount + head.moveCount = 0) :
    Nonempty (CausalHeadWeave tail head Q contacts) := by
  cases tail with
  | nil =>
    cases head with
    | nil =>
      refine ⟨{
        pending := Q, execution := .nil _, terminal := ?_, trace := ?_
        contacts_transversal := fun _ _ => True.intro
        tail_sections := ?_, head_sections := ?_
      }⟩
      · simpa only [HeadQueueBalance,Execution.futureHeadWires,Execution.ledger,Ledger.zero,
          List.flatMap_nil,Multiset.coe_nil,add_zero] using hbalance
      · constructor <;> rfl
      · intro kind i p first last count run
        cases run with
        | nil _ active valid => exact .nil _ _ valid
      · intro kind p first last count run
        cases run with
        | nil _ active valid => exact .nil _ _ valid
    | cons => simp only [Execution.moveCount] at hzero; omega
  | cons => simp only [Execution.moveCount] at hzero; omega

/-- Strong induction composes the already checked one-step path selection.
It introduces no event word or reaching-execution premise. -/
theorem Execution.prepend_causal_result {n θ θH route s u a b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b)
    (hstart : s.time = a.time) (hfinish : u.time = b.time)
    (contacts : HeadRoutes n) (hcontacts : StrictHeadRoutes contacts)
    (Q : List (Delivery (n + 1))) (hbalance : HeadQueueBalance tail a Q contacts) :
    Nonempty (CausalHeadWeave tail head Q contacts) := by
  suffices aux : ∀ N : ℕ, ∀ {v : Snapshot n} {c : Snapshot 1}
      (left : Execution θ route v u) (right : Execution θH (fun _ _ => []) c b),
      left.moveCount + right.moveCount = N → v.time = c.time →
      ∀ Q : List (Delivery (n + 1)), HeadQueueBalance left c Q contacts →
      Nonempty (CausalHeadWeave left right Q contacts) by
    exact aux _ tail head rfl hstart Q hbalance
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro v c left right hsize hsync Q hbalance
    by_cases hz : N = 0
    · exact left.prepend_causal_zero right Q contacts hbalance (hsize.trans hz)
    · obtain ⟨step⟩ := left.causal_head_step right hsync hfinish contacts hcontacts Q hbalance
        hsize (Nat.pos_of_ne_zero hz)
      exact step.lift (ih _ step.decrease step.tail step.head rfl step.clock step.pending step.balance)

/-- Public existential form of the concrete causal product. -/
theorem Execution.prepend_causal {n θ θH route s u a b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _ => []) a b)
    (hstart : s.time = a.time) (hfinish : u.time = b.time)
    (contacts : HeadRoutes n) (hcontacts : StrictHeadRoutes contacts)
    (Q : List (Delivery (n + 1))) (hbalance : HeadQueueBalance tail a Q contacts) :
    ∃ (Q' : List (Delivery (n + 1)))
      (global : Execution (prependParameters θH θ) (prependRouted route contacts)
        (s.prependQueued a Q) (u.prependQueued b Q')),
      (Q' : Multiset (Delivery (n + 1))) =
        (u.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
          (b.pending.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1))) ∧
      CausalTraceBalance global.ledger.emissions global.deliveries
        tail.ledger.emissions tail.deliveries head.ledger.emissions head.deliveries := by
  obtain ⟨result⟩ := tail.prepend_causal_result head hstart hfinish contacts hcontacts Q hbalance
  exact ⟨result.pending,result.execution,result.terminal,result.trace⟩

end KernelR.Hybrid
