import KernelR.HybridBirthSourceTrain
import KernelR.HybridFlowCuts
import KernelR.HybridDueSources
import KernelR.HybridBoundaryIdle
import KernelR.HybridStagedBirth
/-! First physical preparation inside a larger source queue and execution. -/
namespace KernelR.Hybrid

/-- The preparation at 128 is part of the supplied execution. The remaining
execution and future source queue are retained; no later pulse cases are fixed. -/
structure BirthPreparation {n θ route born u} (e : @Execution n θ route born u)
    (i : Fin n) (p : Port) where
  state : Snapshot n
  date : state.time = 128
  span : Execution θ route born state
  is_prefix : e.IsPrefix span
  continuation : e.Continuation span
  train : BirthSourceTrain span i p
  calendar : span.deliveries = sourceTrain i p 0 8 16

/-- The first sixteen sources prepare the cell even when its initial queue
already contains later sources. Pending urgency consumes every strict-past
source, without assuming `CompleteThrough` for the supplied execution. -/
theorem Execution.birth_low_train_prefix {n θ ε route born u} (e : @Execution n θ route born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready) (later : List (Delivery n))
    (hq : born.pending = sourceTrain i p 0 8 16 ++ later)
    (hlater : ∀ d ∈ later, 128 < d.due) (hr : ∀ i t, route i t = [])
    (ht : 128 ≤ u.time) : Nonempty (BirthPreparation e i p) := by
  obtain ⟨v,cut,hcut,hdate⟩ := e.prefix_at 128 (by rw [hborn.1]; norm_num) ht
  have hfuture : PendingFuture born := by
    intro d hd
    rw [hq] at hd
    rw [hborn.1]
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      positivity
    · linarith [hlater d hd]
  have hcausal : CausalRouter route := by simp [CausalRouter,hr]
  have hcalendar : cut.deliveries = sourceTrain i p 0 8 16 := by
    apply cut.deliveries_due_prefix_exact (sourceTrain i p 0 8 16) later hq
      ?_ ?_ (cut.pending_future hcausal hfuture) hr i p ?_ ?_
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      rw [hdate]
      have hk : (k.val : ℝ) < 16 := by exact_mod_cast k.isLt
      dsimp
      linarith
    · simpa only [hdate] using hlater
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨rfl,rfl⟩
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
      dsimp
      linarith
  obtain ⟨train⟩ := cut.birth_low_train hborn hb i p hp ha hcalendar (by rw [hdate])
  obtain ⟨continuation⟩ := hcut.continuation
  exact ⟨⟨v,hdate,cut,hcut,continuation,train,hcalendar⟩⟩

/-- The declared two trains at 0..120 and 160..280 yield the same physical
preparation at 128. The second train remains present in the initial queue. -/
theorem Execution.birth_low_two_trains_prefix {n θ ε route born u} (e : @Execution n θ route born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready)
    (hq : born.pending = sourceTrain i p 0 8 16 ++ sourceTrain i p 160 8 16)
    (hr : ∀ i t, route i t = []) (ht : 128 ≤ u.time) : Nonempty (BirthPreparation e i p) := by
  apply e.birth_low_train_prefix hborn hb i p hp ha (sourceTrain i p 160 8 16) hq ?_ hr ht
  intro d hd
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
  dsimp
  have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  linarith

/-- Physical preparation at the date of the second train. Its first token can
still be pending or already delivered; the raw-state alternatives retain both. -/
structure BirthPreparedBoundary {n θ route born u} (e : @Execution n θ route born u)
    (i : Fin n) (p : Port) where
  emissions : (e.emissionTimes i).length = 12
  error_target : e.ledger.error i p = 9 / 5
  error_other : ∀ q, q ≠ p → e.ledger.error i q = 0
  mark_target : e.ledger.mark i p = 1 / 10
  mark_other : ∀ q, q ≠ p → e.ledger.mark i q = 0
  gain_target : u.x i (.z p) = born.x i (.z p) + 9 / 5
  gain_other : ∀ q, q ≠ p → u.x i (.z q) = born.x i (.z q)
  recovery_gain : u.x i .b = born.x i .b + 1 / 10
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  raw_target : u.raw i p = none ∨ u.raw i p = some u.time
  raw_other : ∀ q, q ≠ p → u.raw i q = none

/-- At 160 the first physical phase is prepared even with all 32 sources in
the original queue. There is no priority assumption for the source due at 160,
and no existence or progress premise is replaced by this conditional result. -/
theorem Execution.birth_prepared_at_second_train {n θ ε route born u} (e : @Execution n θ route born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready)
    (hq : born.pending = sourceTrain i p 0 8 16 ++ sourceTrain i p 160 8 16)
    (hr : ∀ i t, route i t = []) (ht : u.time = 160) : Nonempty (BirthPreparedBoundary e i p) := by
  obtain ⟨prep⟩ := e.birth_low_two_trains_prefix hborn hb i p hp ha hq hr (by rw [ht]; norm_num)
  have hpending := prep.span.pending_perm_of_prefix _ _ hq (by rw [prep.calendar]) hr
  have hdates : ∀ d ∈ prep.continuation.tail.deliveries, d.due = u.time := by
    intro d hd
    have hs : d ∈ prep.state.pending := by
      rcases prep.continuation.tail.delivery_provenance d hd with h | ⟨event,he,hroute⟩
      · exact h
      · simp only [hr,List.not_mem_nil] at hroute
    have hm := hpending.mem_iff.mp hs
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hm
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    have hu := (prep.continuation.tail.delivery_time_bounds _ hd).2
    rw [ht] at hu ⊢
    dsimp at hu ⊢
    linarith
  obtain ⟨idle⟩ := prep.continuation.tail.idle_prepared_boundary i prep.train.prepared
    prep.train.charge_rest prep.train.raw_finished hdates
  have hztarget : u.x i (.z p) = born.x i (.z p) + 9 / 5 := by
    rw [idle.gain_preserved,prep.train.gain_target]
  have hzother : ∀ q, q ≠ p → u.x i (.z q) = born.x i (.z q) := by
    intro q hq
    rw [idle.gain_preserved,prep.train.gain_other q hq]
  have hbgain : u.x i .b = born.x i .b + 1 / 10 := by
    rw [idle.recovery_preserved,prep.train.recovery_gain]
  have hmarkother : ∀ q, q ≠ p → e.ledger.mark i q = 0 := by
    intro q hq'
    have hno : NoArrivalAt e i q := by
      intro d hd
      rcases e.delivery_provenance d hd with h | ⟨event,he,hroute⟩
      · rw [hq] at h
        rcases List.mem_append.mp h with h | h
        all_goals obtain ⟨k,rfl⟩ := List.mem_ofFn.mp h; exact Or.inr (Ne.symm hq')
      · simp only [hr,List.not_mem_nil] at hroute
    have hm := e.aux_ready_without_input_band i q (ha q)
      ((hborn.ready_coordinates i ha).auxiliary q).2.2 (hborn.2.1 i q) hno
    exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hm)
  have hmark : e.ledger.mark i p = 1 / 10 := by
    have hsum : e.ledger.recovery i = e.ledger.mark i p := by
      rw [e.recovery_sum_marks i]
      exact Finset.sum_eq_single p (fun q _ hq => hmarkother q hq) (by simp)
    have hbalance := e.recovery_balance i
    rw [hsum] at hbalance
    linarith
  refine ⟨⟨?_,?_,?_,hmark,hmarkother,hztarget,hzother,hbgain,idle.prepared,idle.charge_rest,
    prep.continuation.tail.raw_none_or_terminal i p (prep.train.raw_finished p) hdates,?_⟩⟩
  · rw [prep.continuation.emissionTimes i,idle.emissions,List.append_nil]
    exact prep.train.emissions
  · have h := e.gain_balance i p
    linarith
  · intro q hq
    have h := e.gain_balance i q
    rw [hzother q hq] at h
    linarith
  · intro q hq'
    apply (prep.continuation.tail.raw_absent_of_no_arrival i q (prep.train.raw_finished q) ?_).1
    intro d hd
    have hs : d ∈ prep.state.pending := by
      rcases prep.continuation.tail.delivery_provenance d hd with h | ⟨event,he,hroute⟩
      · exact h
      · simp only [hr,List.not_mem_nil] at hroute
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (hpending.mem_iff.mp hs)
    exact Or.inr (Ne.symm hq')

/-- The existing cell retains its proved physical preparation across the
scheduled birth. The fresh cell still uses its separate newborn family. -/
structure StagedPreparation {n θ fresh routeBefore routeAfter born u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter born u) (i : Fin n) (p : Port) where
  first_phase : BirthPreparedBoundary e.before i p
  date : e.afterBirth.time = 160
  prepared : PreparedSection e.afterBirth i.castSucc
  charge_rest : e.afterBirth.x i.castSucc .q = 1 / 10
  gain_target : e.afterBirth.x i.castSucc (.z p) = born.x i (.z p) + 9 / 5
  gain_other : ∀ q, q ≠ p → e.afterBirth.x i.castSucc (.z q) = born.x i (.z q)
  recovery_gain : e.afterBirth.x i.castSucc .b = born.x i .b + 1 / 10
  raw_target : e.afterBirth.raw i.castSucc p = none ∨ e.afterBirth.raw i.castSucc p = some e.afterBirth.time
  raw_other : ∀ q, q ≠ p → e.afterBirth.raw i.castSucc q = none

/-- The complete first source phase is connected to a real birth at 160,
without resetting the old cell or choosing an order for the boundary source. -/
theorem StagedExecution.preparation_at_birth {n θ fresh ε routeBefore routeAfter born u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready)
    (hq : born.pending = sourceTrain i p 0 8 16 ++ sourceTrain i p 160 8 16)
    (hr : ∀ i t, routeBefore i t = []) (ht : e.beforeBirth.time = 160) :
    Nonempty (StagedPreparation e i p) := by
  obtain ⟨phase⟩ := e.before.birth_prepared_at_second_train hborn hb i p hp ha hq hr ht
  refine ⟨⟨phase,e.birth.time_unchanged.trans ht,e.birth.old_prepared i phase.prepared,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [e.birth.old_coordinates]; exact phase.charge_rest
  · rw [e.birth.old_coordinates]; exact phase.gain_target
  · intro q hq
    rw [e.birth.old_coordinates]; exact phase.gain_other q hq
  · rw [e.birth.old_coordinates]; exact phase.recovery_gain
  · rw [e.birth.old_raw,e.birth.time_unchanged]; exact phase.raw_target
  · intro q hq
    rw [e.birth.old_raw]; exact phase.raw_other q hq

end KernelR.Hybrid
