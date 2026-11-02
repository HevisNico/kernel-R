import KernelR.HybridNeutralExecutionProduct

/-! Append a frame to a genuine non-emitting execution. This is transport of
an existing path, not an arrival or issuance event: callers must identify the
framed source with their actual state after a real FIRE. Queue order is exact. -/
namespace KernelR.Hybrid

/-- Suffix framing preserves the order produced by an actual FIRE append. -/
def appendPending {n} (s : Snapshot n) (future : List (Delivery n)) : Snapshot n :=
  {s with pending := s.pending ++ future}

noncomputable def Flow.appendFuture {n θ s u} (f : @Flow n θ s u)
    (future : List (Delivery n)) (hf : ∀ d ∈ future, u.time ≤ d.due) :
    Flow θ (appendPending s future) (appendPending u future) where
  positive := f.positive
  path := f.path
  initial := f.initial
  final := f.final
  main_fixed := f.main_fixed
  aux_fixed := f.aux_fixed
  raw_fixed := f.raw_fixed
  queue_fixed := by simp only [appendPending,f.queue_fixed]
  continuous := f.continuous
  integrable := f.integrable
  mark_integrable := f.mark_integrable
  integral_eq := f.integral_eq
  guards := f.guards
  raw_support := f.raw_support
  pending_urgent := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact f.pending_urgent d hd
    · exact hf d hd

theorem Flow.appendFuture_ledger {n θ s u} (f : @Flow n θ s u)
    (future : List (Delivery n)) (hf : ∀ d ∈ future, u.time ≤ d.due) :
    (f.appendFuture future hf).ledger = f.ledger := rfl

/-- All non-FIRE jumps transport the same frame, including arrivals from
inside the old queue. Every delivered token remains its original occurrence. -/
theorem Jump.appendFuture_neutral {n route s u} (j : @Jump n route s u)
    (he : j.ledger.emissions = []) (future : List (Delivery n)) :
    ∃ lifted : Jump route (appendPending s future) (appendPending u future),
      lifted.ledger = j.ledger ∧ lifted.deliveries = j.deliveries := by
  cases j with
  | fire i hm hq =>
    change [(i,s.time)] = [] at he
    contradiction
  | fastEnd i hm hq => exact ⟨.fastEnd _ i hm hq,rfl,rfl⟩
  | reopen i hm hq => exact ⟨.reopen _ i hm hq,rfl,rfl⟩
  | mark i p hm hq => exact ⟨.mark _ i p hm hq,rfl,rfl⟩
  | silent i p hm hq => exact ⟨.silent _ i p hm hq,rfl,rfl⟩
  | error i p hm hq => exact ⟨.error _ i p hm hq,rfl,rfl⟩
  | auxReady i p hm hq => exact ⟨.auxReady _ i p hm hq,rfl,rfl⟩
  | rawEnd i p origin hr ht => exact ⟨.rawEnd _ i p origin hr ht,rfl,rfl⟩
  | arrive d before after hqueue hd hf =>
    have htarget : appendPending ({setRaw s d.cell d.port (some s.time) with pending := before ++ after} : Snapshot n) future =
        {setRaw (appendPending s future) d.cell d.port (some s.time) with pending := before ++ (after ++ future)} := by
      simp only [appendPending,setRaw,List.append_assoc]
    rw [htarget]
    refine ⟨.arrive _ d before (after ++ future) ?_ hd hf,rfl,?_⟩
    · change s.pending ++ future = before ++ d :: (after ++ future)
      rw [hqueue,List.append_assoc,List.cons_append]
    · simp only [Jump.deliveries]

/-- Frame a future suffix along the same finite actual paths. No FIRE is
allowed, since a FIRE must append its true routed tokens in operational order.
The complete physical ledger and every actual delivery are preserved. -/
theorem Execution.appendFuture_neutral {n θ route s u} (e : @Execution n θ route s u)
    (he : e.ledger.emissions = []) (future : List (Delivery n))
    (hf : ∀ d ∈ future, u.time ≤ d.due) :
    ∃ lifted : Execution θ route (appendPending s future) (appendPending u future),
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  induction e with
  | nil => exact ⟨.nil _,rfl,rfl⟩
  | @cons s v u move rest ih =>
    have hparts : move.ledger.emissions = [] ∧ rest.ledger.emissions = [] :=
      List.append_eq_nil_iff.mp he
    obtain ⟨tail,hledger,hdel⟩ := ih hparts.2 hf
    cases move with
    | flow f =>
      let g := f.appendFuture future (fun d hd => rest.time_monotone.trans (hf d hd))
      refine ⟨.cons (.flow g) tail,?_,?_⟩
      · change g.ledger.add tail.ledger = f.ledger.add rest.ledger
        rw [hledger,f.appendFuture_ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [hdel]
    | jump j =>
      obtain ⟨g,hgL,hgD⟩ := j.appendFuture_neutral hparts.1 future
      refine ⟨.cons (.jump g) tail,?_,?_⟩
      · change g.ledger.add tail.ledger = j.ledger.add rest.ledger
        rw [hgL,hledger]
      · change g.deliveries ++ tail.deliveries = j.deliveries ++ rest.deliveries
        rw [hgD,hdel]

end KernelR.Hybrid
