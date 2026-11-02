import KernelR.HybridNeutralFutureFrame

/-! Suffix framing for actual local executions with empty routing. Their true
FIRE events are retained in the complete ledger, while no routed token is
issued locally. Framed queues are tools for local construction: global wire
issuance and provenance still require the actual routed FIRE reconstruction. -/
namespace KernelR.Hybrid

/-- Empty routing makes an actual FIRE commute with suffix framing. Every
other jump retains its original queue occurrence and physical state. -/
theorem Jump.appendFuture_emptyRoute {n s u} (j : @Jump n (fun _ _ => []) s u) (future : List (Delivery n)) :
    ∃ lifted : Jump (fun _ _ => []) (appendPending s future) (appendPending u future),
      lifted.ledger = j.ledger ∧ lifted.deliveries = j.deliveries := by
  cases j with
  | fire i hm hq =>
    have htarget : appendPending
        ({setMain s i .fast with pending := s.pending ++ []} : Snapshot n) future =
        {setMain (appendPending s future) i .fast with pending := (appendPending s future).pending ++ []} := by
      simp only [appendPending,setMain,List.append_nil]
    rw [htarget]
    exact ⟨.fire _ i hm hq,rfl,rfl⟩
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


/-- Carry a future local queue suffix along exactly the same physical path,
including its actual FIRE events and their unchanged ledger entries. -/
theorem Execution.appendFuture_emptyRoute {n θ s u} (e : @Execution n θ (fun _ _ => []) s u) (future : List (Delivery n))
    (hf : ∀ d ∈ future, u.time ≤ d.due) :
    ∃ lifted : Execution θ (fun _ _ => []) (appendPending s future) (appendPending u future),
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  induction e with
  | nil => exact ⟨.nil _,rfl,rfl⟩
  | @cons s v u move rest ih =>
    obtain ⟨tail,hledger,hdel⟩ := ih hf
    cases move with
    | flow f =>
      let g := f.appendFuture future (fun d hd => rest.time_monotone.trans (hf d hd))
      refine ⟨.cons (.flow g) tail,?_,?_⟩
      · change g.ledger.add tail.ledger = f.ledger.add rest.ledger
        rw [hledger,f.appendFuture_ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [hdel]
    | jump j =>
      obtain ⟨g,hgL,hgD⟩ := j.appendFuture_emptyRoute future
      refine ⟨.cons (.jump g) tail,?_,?_⟩
      · change g.ledger.add tail.ledger = j.ledger.add rest.ledger
        rw [hgL,hledger]
      · change g.deliveries ++ tail.deliveries = j.deliveries ++ rest.deliveries
        rw [hgD,hdel]

end KernelR.Hybrid
