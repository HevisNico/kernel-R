import KernelR.HybridLocalFutureFrame

/-! Restrict an isolated source program before constructing its run. The
transport changes both endpoints' pending programs, preserving the complete
physical path and ledger. It is not an operation erasing a live network queue. -/
namespace KernelR.Hybrid
attribute [local instance] Classical.propDecidable

noncomputable def retainSourcesThrough {n} (cutoff : ℝ) (s : Snapshot n) : Snapshot n :=
  { s with pending := s.pending.filter (fun d => decide (d.due ≤ cutoff)) }

def Flow.retainSourcesThrough {n θ s u} (f : @Flow n θ s u) (cutoff : ℝ) :
    Flow θ (retainSourcesThrough cutoff s) (retainSourcesThrough cutoff u) where
  positive := f.positive
  path := f.path
  initial := f.initial
  final := f.final
  main_fixed := f.main_fixed
  aux_fixed := f.aux_fixed
  raw_fixed := f.raw_fixed
  queue_fixed := by change u.pending.filter _ = s.pending.filter _; rw [f.queue_fixed]
  continuous := f.continuous
  integrable := f.integrable
  mark_integrable := f.mark_integrable
  integral_eq := f.integral_eq
  guards := f.guards
  raw_support := f.raw_support
  pending_urgent := by
    intro d hd
    exact f.pending_urgent d (List.mem_filter.mp hd).1

@[simp] theorem Flow.retainSourcesThrough_ledger {n θ s u} (f : @Flow n θ s u) (cutoff : ℝ) :
    (f.retainSourcesThrough cutoff).ledger = f.ledger := rfl

theorem Jump.retainSourcesThrough_emptyRoute {n s u}
    (j : @Jump n (fun _ _ => []) s u) (cutoff : ℝ) (ht : s.time ≤ cutoff) :
    ∃ lifted : Jump (fun _ _ => []) (retainSourcesThrough cutoff s) (retainSourcesThrough cutoff u),
      lifted.ledger = j.ledger ∧ lifted.deliveries = j.deliveries := by
  cases j with
  | fire i hm hq =>
    have htarget : retainSourcesThrough cutoff
        ({setMain s i .fast with pending := s.pending ++ []} : Snapshot n) =
        {setMain (retainSourcesThrough cutoff s) i .fast with
          pending := (retainSourcesThrough cutoff s).pending ++ []} := by
      simp only [retainSourcesThrough,setMain,List.append_nil]
    rw [htarget]
    exact ⟨.fire _ i hm hq,rfl,rfl⟩
  | fastEnd i hm hq => exact ⟨.fastEnd _ i hm hq,rfl,rfl⟩
  | reopen i hm hq => exact ⟨.reopen _ i hm hq,rfl,rfl⟩
  | mark i p hm hq => exact ⟨.mark _ i p hm hq,rfl,rfl⟩
  | silent i p hm hq => exact ⟨.silent _ i p hm hq,rfl,rfl⟩
  | error i p hm hq => exact ⟨.error _ i p hm hq,rfl,rfl⟩
  | auxReady i p hm hq => exact ⟨.auxReady _ i p hm hq,rfl,rfl⟩
  | rawEnd i p origin hr htime => exact ⟨.rawEnd _ i p origin hr htime,rfl,rfl⟩
  | arrive d before after hqueue hd hf =>
    have hin : decide (d.due ≤ cutoff) = true := by simp only [decide_eq_true_eq]; rw [hd]; exact ht
    have htarget : retainSourcesThrough cutoff
        ({setRaw s d.cell d.port (some s.time) with pending := before ++ after} : Snapshot n) =
        {setRaw (retainSourcesThrough cutoff s) d.cell d.port (some s.time) with
          pending := before.filter (fun d => decide (d.due ≤ cutoff)) ++
            after.filter (fun d => decide (d.due ≤ cutoff))} := by
      simp only [retainSourcesThrough,setRaw,List.filter_append]
    rw [htarget]
    refine ⟨.arrive _ d (before.filter (fun d => decide (d.due ≤ cutoff)))
      (after.filter (fun d => decide (d.due ≤ cutoff))) ?_ hd hf,rfl,?_⟩
    · change s.pending.filter _ = _
      rw [hqueue,List.filter_append,List.filter_cons,hin]
      rfl
    · simp only [Jump.deliveries]

/-- Every retained arrival occurred by the cutoff in the original execution.
Both executions have exactly the same physical trajectory and ledger. -/
theorem Execution.retainSourcesThrough_emptyRoute {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u) (cutoff : ℝ) (ht : u.time ≤ cutoff) :
    ∃ lifted : Execution θ (fun _ _ => [])
      (retainSourcesThrough cutoff s) (retainSourcesThrough cutoff u),
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  induction e with
  | nil => exact ⟨.nil _,rfl,rfl⟩
  | @cons s v u move rest ih =>
    obtain ⟨tail,hledger,hdel⟩ := ih ht
    cases move with
    | flow f =>
      let g := f.retainSourcesThrough cutoff
      refine ⟨.cons (.flow g) tail,?_,?_⟩
      · change g.ledger.add tail.ledger = f.ledger.add rest.ledger
        rw [hledger,f.retainSourcesThrough_ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [hdel]
    | jump j =>
      have hstart : s.time ≤ cutoff := by rw [← j.time_unchanged]; exact rest.time_monotone.trans ht
      obtain ⟨g,hgL,hgD⟩ := j.retainSourcesThrough_emptyRoute cutoff hstart
      refine ⟨.cons (.jump g) tail,?_,?_⟩
      · change g.ledger.add tail.ledger = j.ledger.add rest.ledger
        rw [hgL,hledger]
      · change g.deliveries ++ tail.deliveries = j.deliveries ++ rest.deliveries
        rw [hgD,hdel]

end KernelR.Hybrid
