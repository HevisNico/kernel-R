import KernelR.HybridQuietHeadExecutionProduct

/-! A neutral active network can be prepended with a physical quiet head under
any global router. No FIRE occurs, so open contacts require no compatibility
with the local router. The active queue and every actual delivery are retained. -/
namespace KernelR.Hybrid

/-- Transport an actual non-emitting jump under arbitrary global contacts. -/
theorem Jump.prependQuiet_neutral {n route s u} (j : @Jump n route s u)
    (he : j.ledger.emissions = []) (a : Snapshot 1) (global : Router (n + 1)) :
    ∃ lifted : Jump global (s.prependQuiet a) (u.prependQuiet a),
      lifted.ledger.emissions = [] ∧
      lifted.deliveries = j.deliveries.map Delivery.succ := by
  cases j with
  | fire i hm hq =>
    change [(i,s.time)] = [] at he
    contradiction
  | fastEnd i hm hq =>
    rw [Snapshot.prependQuiet_setMain]
    exact ⟨.fastEnd _ i.succ hm hq, rfl, rfl⟩
  | reopen i hm hq =>
    rw [Snapshot.prependQuiet_setMain]
    exact ⟨.reopen _ i.succ hm hq, rfl, rfl⟩
  | mark i p hm hq =>
    rw [Snapshot.prependQuiet_setAux]
    exact ⟨.mark _ i.succ p hm hq, rfl, rfl⟩
  | silent i p hm hq =>
    rw [Snapshot.prependQuiet_setAux]
    exact ⟨.silent _ i.succ p hm hq, rfl, rfl⟩
  | error i p hm hq =>
    rw [Snapshot.prependQuiet_setAux]
    exact ⟨.error _ i.succ p hm hq, rfl, rfl⟩
  | auxReady i p hm hq =>
    rw [Snapshot.prependQuiet_setAux]
    exact ⟨.auxReady _ i.succ p hm hq, rfl, rfl⟩
  | arrive d before after hq hd hf =>
    have heq : ({ setRaw s d.cell d.port (some s.time) with pending := before ++ after } : Snapshot n).prependQuiet a =
        { setRaw (s.prependQuiet a) d.cell.succ d.port (some s.time) with
          pending := before.map Delivery.succ ++ after.map Delivery.succ } := by
      simp only [Snapshot.prependQuiet, setRaw, List.map_append]
      congr 1
      funext k
      refine Fin.cases ?_ (fun l => ?_) k <;> simp [Function.update_apply, Fin.succ_ne_zero, eq_comm]
    rw [heq]
    refine ⟨.arrive _ d.succ (before.map Delivery.succ) (after.map Delivery.succ) ?_ hd hf, rfl, ?_⟩
    · change s.pending.map Delivery.succ = _
      rw [hq, List.map_append, List.map_cons]
    · simp only [Jump.deliveries, List.map_cons, List.map_nil]
  | rawEnd i p origin hr ht =>
    rw [Snapshot.prependQuiet_setRaw]
    exact ⟨.rawEnd _ i.succ p origin hr ht, rfl, rfl⟩

private theorem execution_cast_target_events {n θ route s u v} (e : @Execution n θ route s u)
    (h : u = v) : ∃ out : Execution θ route s v,
      out.ledger.emissions = e.ledger.emissions ∧ out.deliveries = e.deliveries := by
  subst v
  exact ⟨e, rfl, rfl⟩

/-- Lift a non-emitting execution beside a genuine quiet head path. The
emission-free premise is about the actual ledger, not a supplied case word. -/
theorem Execution.prepend_quiet_neutral {n θ route s u} (e : @Execution n θ route s u)
    (he : e.ledger.emissions = [])
    (θA : Fin 1 → Parameters) (a : Snapshot 1) (hstart : s.time = a.time)
    (ha : ∀ i, ReadyCoordinates a i) (hr : ∀ i p, a.raw i p = none) (hq : a.pending = [])
    (global : Router (n + 1)) :
    ∃ lifted : Execution (prependParameters θA θ) global (s.prependQuiet a)
        (u.prependQuiet (quietAt a u.time)),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = e.deliveries.map Delivery.succ := by
  induction e generalizing a with
  | nil s =>
    rw [hstart, quietAt_self]
    exact ⟨.nil _, rfl, rfl⟩
  | @cons s v u m rest ih =>
    have heParts : m.ledger.emissions = [] ∧ rest.ledger.emissions = [] :=
      List.append_eq_nil_iff.mp he
    cases m with
    | flow f =>
      have ht : a.time < v.time := by rw [← hstart]; exact f.positive
      let g := quietFlow (θ := θA) a ht (fun i => (ha i).ready)
        (fun i p => ((ha i).auxiliary p).1) hr
        (fun i => by linarith [(ha i).charge.2])
        (fun i p => by linarith [((ha i).auxiliary p).2.2])
        (by intro d hd; rw [hq] at hd; contradiction)
      obtain ⟨tail₀, he₀, hd₀⟩ := ih heParts.2 (quietAt a v.time) rfl
        (fun i => quietAt_ready_coordinates a i (ha i) ht.le) hr hq
      have target : u.prependQuiet (quietAt (quietAt a v.time) u.time) =
          u.prependQuiet (quietAt a u.time) := congrArg (fun b => u.prependQuiet b)
            (quietAt_quietAt a v.time u.time)
      obtain ⟨tail, heT, hdT⟩ := execution_cast_target_events tail₀ target
      have heTail := heT.trans he₀
      have hdTail := hdT.trans hd₀
      let lifted := Execution.cons (.flow (f.prependQuiet g hstart rfl)) tail
      refine ⟨lifted, ?_, ?_⟩
      · simpa only [lifted, Execution.ledger, Ledger.add, Move.ledger, Flow.ledger,
          List.nil_append] using heTail
      · simpa only [lifted, Execution.deliveries, Move.deliveries,
          List.nil_append, List.map_nil] using hdTail
    | jump j =>
      obtain ⟨step, heS, hdS⟩ := j.prependQuiet_neutral heParts.1 a global
      obtain ⟨tail, heTail, hdTail⟩ := ih heParts.2 a (j.time_unchanged.trans hstart) ha hr hq
      let lifted := Execution.cons (.jump step) tail
      refine ⟨lifted, ?_, ?_⟩
      · change step.ledger.emissions ++ tail.ledger.emissions = []
        rw [heS, heTail, List.nil_append]
      · change step.deliveries ++ tail.deliveries = _
        rw [hdS, hdTail]
        exact List.map_append.symm

end KernelR.Hybrid
