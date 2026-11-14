import SynchronizedProduct

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid NativeStrong Set MeasureTheory
open scoped BigOperators

/-- Translate a receipt from its isolated leg into the physical queue. -/
def receiptAt (i : Fin N) (receipt : Delivery 1) : Delivery N :=
  ⟨i, receipt.port, receipt.due⟩

private noncomputable def remainingReceipts {θ : Fin N → KernelR.Hybrid.Parameters}
    {b : Fin N → Snapshot 1} (c : ∀ i, Cursor (θ i) (b i)) : List (Delivery N) :=
  (List.finRange N).flatMap fun i => (c i).run.deliveries.map (receiptAt i)

private theorem remaining_at {θ : Fin N → KernelR.Hybrid.Parameters}
    {b : Fin N → Snapshot 1} (c : ∀ i, Cursor (θ i) (b i))
    (i : Fin N) (l : List (Delivery 1)) (new : Cursor (θ i) (b i))
    (changeAt : (c i).run.deliveries = l ++ new.run.deliveries) :
    (remainingReceipts c).Perm (l.map (receiptAt i) ++ remainingReceipts (Function.update c i new)) := by
  classical
  obtain ⟨before, after, split⟩ :=
    List.append_of_mem (List.mem_finRange i)
  have absent : i ∉ before ++ after := by
    have unique := List.nodup_finRange N
    rw [split] at unique
    have perm : (before ++ i :: after).Perm (i :: (before ++ after)) := List.perm_middle
    exact (List.nodup_cons.mp (perm.nodup_iff.mp unique)).1
  have same (w : List (Fin N)) (outside : i ∉ w) :
      (w.flatMap fun j => (Function.update c i new j).run.deliveries.map (receiptAt j)) =
        w.flatMap fun j => (c j).run.deliveries.map (receiptAt j) := by
    apply List.flatMap_congr
    intro j mem
    have ne : j ≠ i := fun eq => outside (eq ▸ mem)
    have state : Function.update c i new j = c j := Function.update_of_ne ne _ _
    exact congrArg (fun d => d.run.deliveries.map (receiptAt j)) state
  have selected : (Function.update c i new i).run.deliveries = new.run.deliveries :=
    congrArg (fun d : Cursor (θ i) (b i) => d.run.deliveries) (Function.update_self _ _ _)
  have beforeSame := same before (fun h => absent (List.mem_append_left _ h))
  have afterSame := same after (fun h => absent (List.mem_append_right _ h))
  have swap := (List.perm_append_comm (l₁ := before.flatMap fun j =>
    (c j).run.deliveries.map (receiptAt j)) (l₂ := l.map (receiptAt i))).append_right
      (new.run.deliveries.map (receiptAt i) ++ after.flatMap fun j =>
        (c j).run.deliveries.map (receiptAt j))
  simpa only [remainingReceipts, split, List.flatMap_append, List.flatMap_cons,
    beforeSame, afterSame, selected, changeAt, List.map_append, List.append_assoc] using swap

private theorem delivery_in_remaining {θ : Fin N → KernelR.Hybrid.Parameters}
    {b : Fin N → Snapshot 1} {c : ∀ i, Cursor (θ i) (b i)}
    {i : Fin N} {d : Delivery 1} (mem : d ∈ (c i).run.deliveries) :
    receiptAt i d ∈ remainingReceipts c := by
  exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map_of_mem mem⟩

private theorem silent_lift {route : Router N} {t : ℝ}
    {c : Fin N → Snapshot 1} (i : Fin N) {v : Snapshot 1}
    (clock : (c i).time = t) (q : List (Delivery N))
    (j : Jump (EmptyRouter 1) (c i) v) (fires : j.ledger.emissions = [])
    (future : ∀ d ∈ j.deliveries, receiptAt i d ∈ q) :
    ∃ (out : List (Delivery N)) (k : Jump route (assemble t c q)
      (assemble t (Function.update c i v) out)),
      k.ledger.emissions = [] ∧ k.deliveries = j.deliveries.map (receiptAt i) ∧
      q.Perm (k.deliveries ++ out) := by
  classical
  by_cases no : j.deliveries = []
  · obtain ⟨lifted, em, delivered⟩ := parallelJump (route := route) i clock q j no
    have empty : q ++ issuedBy route i j.ledger.emissions = q := by
      simp [issuedBy, fires]
    obtain ⟨k, ledger, hk⟩ := cast_jump lifted (congrArg (assemble t (Function.update c i v)) empty)
    refine ⟨q, k, ?_, ?_, ?_⟩
    · rw [ledger, em, fires]; rfl
    · rw [hk, delivered, no]; rfl
    · rw [hk, delivered]; exact .rfl
  · have single : ∃ d, j.deliveries = [d] := by
      cases j with
      | arrive d => exact ⟨d, rfl⟩
      | _ => exact (no rfl).elim
    obtain ⟨receipt, delivers⟩ := single
    have member := future receipt (delivers ▸ List.mem_singleton_self receipt)
    obtain ⟨before, after, split⟩ := List.append_of_mem member
    obtain ⟨lifted, em, delivered⟩ :=
      parallel_arrival (route := route) i clock q j receipt delivers before after split
    refine ⟨before ++ after, lifted, em, ?_, ?_⟩
    · rw [delivered, delivers]; rfl
    · rw [delivered, split]
      exact List.perm_middle

/-- Synchronize overlapping local legs that can consume scheduled receipts.
The queue consists of the union of their remaining deliveries. The
induction cuts at the earliest head flow endpoint or executes one head
jump immediately, including ties between independently addressed cells. -/
theorem synchronized_receipt_execution
    {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N} {t T : ℝ}
    (a b : Fin N → Snapshot 1)
    (legs : ∀ i, Execution (fun _ => θ i) (EmptyRouter 1) (a i) (b i))
    (start : ∀ i, (a i).time = t) (finish : ∀ i, (b i).time = T) (interval : t ≤ T)
    (silent : ∀ i, (legs i).ledger.emissions = []) (queue : List (Delivery N))
    (schedule : queue.Perm ((List.finRange N).flatMap fun i => (legs i).deliveries.map (receiptAt i))) :
    ∃ run : Execution θ route (assemble t a queue) (assemble T b []),
      run.ledger.emissions = [] ∧ queue.Perm run.deliveries ∧
      (∀ i p, run.ledger.mark i p = (legs i).ledger.mark 0 p) := by
  classical
  let init : ∀ i, Cursor (θ i) (b i) := fun i => ⟨a i, legs i⟩
  suffices loop : ∀ n (c : ∀ i, Cursor (θ i) (b i)) (date : ℝ)
      (q : List (Delivery N)),
      (∑ i, (c i).run.moveCount) = n → date ≤ T →
      (∀ i, (c i).start.time = date) → (∀ i, (c i).run.ledger.emissions = []) →
      q.Perm (remainingReceipts c) →
      ∃ run : Execution θ route (assemble date (fun i => (c i).start) q) (assemble T b []),
        run.ledger.emissions = [] ∧ q.Perm run.deliveries ∧
        (∀ i p, run.ledger.mark i p = (c i).run.ledger.mark 0 p) from
    loop _ init t queue rfl interval start silent schedule
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c date q size dateLe clocks quiet queued
    let current := fun i => (c i).start
    by_cases jump : ∃ i, startsWithJump (c i)
    · obtain ⟨i, v, j, rest, head⟩ := jump
      have silentStep : j.ledger.emissions = [] ∧ rest.ledger.emissions = [] := by
        have h := quiet i
        rw [head] at h
        exact List.append_eq_nil_iff.mp h
      let next := Function.update c i ⟨v, rest⟩
      have nextAt : next i = ⟨v, rest⟩ := Function.update_self _ _ _
      have others (k : Fin N) (h : k ≠ i) : next k = c k := Function.update_of_ne h _ _
      have starts : (fun k => (next k).start) = Function.update current i v := by
        funext k
        by_cases h : k = i
        · subst k; simp [nextAt]
        · simp [others k h, current, h]
      have member (d : Delivery 1) (mem : d ∈ j.deliveries) : receiptAt i d ∈ q := by
        apply queued.symm.subset
        apply delivery_in_remaining (c := c)
        rw [head]
        exact List.mem_append_left _ mem
      obtain ⟨qNext, k, kFire, kArrival, kQueue⟩ :=
        silent_lift (route := route) (c := current) i (clocks i) q j silentStep.1 member
      obtain ⟨lifted, liftLedger, liftArrival⟩ := cast_jump k
        (congrArg (fun states => assemble date states qNext) starts.symm)
      have liftedFire := (congrArg Ledger.emissions liftLedger).trans kFire
      have countAt : (next i).run.moveCount = rest.moveCount :=
        congrArg (fun d => d.run.moveCount) nextAt
      have countOther (k : Fin N) (h : k ≠ i) :
          (next k).run.moveCount = (c k).run.moveCount :=
        congrArg (fun d => d.run.moveCount) (others k h)
      have firesAt : (next i).run.ledger.emissions = rest.ledger.emissions :=
        congrArg (fun d => d.run.ledger.emissions) nextAt
      have firesOther (k : Fin N) (h : k ≠ i) :
          (next k).run.ledger.emissions = (c k).run.ledger.emissions :=
        congrArg (fun d => d.run.ledger.emissions) (others k h)
      have smaller : (∑ k, (next k).run.moveCount) < n := by
        rw [← size]
        apply Finset.sum_lt_sum
        · intro k _
          by_cases h : k = i
          · subst k; rw [countAt, head]; exact Nat.le_succ _
          · exact (countOther k h).le
        · exact ⟨i, Finset.mem_univ _, by rw [countAt, head]; exact Nat.lt_succ_self _⟩
      have nextClock (k : Fin N) : (next k).start.time = date := by
        by_cases h : k = i
        · subst k; simpa [nextAt, j.time_unchanged] using clocks i
        · simpa [others k h] using clocks k
      have nextSilence (k : Fin N) : (next k).run.ledger.emissions = [] := by
        by_cases atCell : k = i
        · subst k; exact firesAt.trans silentStep.2
        · exact (firesOther k atCell).trans (quiet k)
      have nextQueue : qNext.Perm (remainingReceipts next) := by
        have balance := queued.trans (remaining_at c i j.deliveries ⟨v, rest⟩ (by rw [head]; rfl))
        rw [← kArrival] at balance
        exact (List.perm_append_left_iff _).mp (kQueue.symm.trans balance)
      obtain ⟨tail, tailFire, tailQueue, tailMark⟩ :=
        ih _ smaller next date qNext rfl dateLe nextClock nextSilence nextQueue
      refine ⟨.cons (.jump lifted) tail, ?_, ?_, ?_⟩
      · change lifted.ledger.emissions ++ tail.ledger.emissions = []
        rw [liftedFire, tailFire]
        rfl
      · change q.Perm (lifted.deliveries ++ tail.deliveries)
        rw [liftArrival]
        exact kQueue.trans (tailQueue.append_left k.deliveries)
      · intro k p
        change lifted.ledger.mark k p + tail.ledger.mark k p = _
        rw [Jump.mark_zero, zero_add, tailMark]
        by_cases atCell : k = i
        · subst k
          have dose := congrArg (fun d => d.run.ledger.mark 0 p) nextAt
          simpa [head, Execution.ledger, Move.ledger, Ledger.add, Jump.mark_zero] using dose
        · exact congrArg (fun d => d.run.ledger.mark 0 p) (others k atCell)
    · by_cases terminal : date = T
      · have done (i : Fin N) : c i = ⟨b i, .nil (b i)⟩ :=
          cursor_done (c i) ((clocks i).trans (terminal.trans (finish i).symm))
            (fun h => jump ⟨i, h⟩)
        have allDone : c = fun i => ⟨b i, .nil (b i)⟩ := funext done
        subst date
        subst c
        have empty : q = [] := by
          have nil : (List.finRange N).flatMap (fun (_ : Fin N) => ([] : List (Delivery N))) = [] :=
            List.flatMap_eq_nil_iff.mpr (by simp)
          change q.Perm ((List.finRange N).flatMap (fun (_ : Fin N) => ([] : List (Delivery N)))) at queued
          rw [nil] at queued
          exact queued.eq_nil
        subst q
        exact ⟨.nil _, rfl, .rfl, fun _ _ => rfl⟩
      · have beforeEnd : date < T := lt_of_le_of_ne dateLe terminal
        have available (i : Fin N) : Nonempty (FlowHead (θ i) (b i) (c i)) :=
          cursor_flow (c i) (by rw [clocks i, finish i]; exact beforeEnd) (fun h => jump ⟨i, h⟩)
        by_cases cells : Nonempty (Fin N)
        · let _ : Nonempty (Fin N) := cells
          let head (i : Fin N) := Classical.choice (available i)
          obtain ⟨first, earliest⟩ := Finite.exists_min (fun i => (head i).endState.time)
          let cut := (head first).endState.time
          have advance : date < cut := by
            have h := (head first).flow.positive
            rwa [clocks first] at h
          have cutLe : cut ≤ T := by
            have h := (head first).tail.time_monotone
            rwa [finish first] at h
          have steps (i : Fin N) := advance_exists (head i)
            (show (c i).start.time < cut by rw [clocks i]; exact advance) (earliest i)
          let step (i : Fin N) := Classical.choose (steps i)
          let next := fun i => (step i).next
          have smaller : (∑ i, (next i).run.moveCount) < n := by
            rw [← size]
            exact Finset.sum_lt_sum (fun i _ => (step i).count)
              ⟨first, Finset.mem_univ _, (Classical.choose_spec (steps first)).2 rfl⟩
          have urgent (d : Delivery N) (mem : d ∈ q) : cut ≤ d.due := by
            obtain ⟨i, _, member⟩ := List.mem_flatMap.mp (queued.subset mem)
            obtain ⟨token, delivered, rfl⟩ := List.mem_map.mp member
            have inTail : token ∈ (head i).tail.deliveries := by
              rw [(head i).unfoldRun] at delivered
              exact delivered
            exact (earliest i).trans ((head i).tail.delivery_time_bounds token inTail).1
          let flow := parallelFlow clocks (fun i => (step i).clock) advance (fun i => (step i).flow) q urgent
          have sameQueue : remainingReceipts next = remainingReceipts c := by
            apply List.flatMap_congr
            intro i _
            exact congrArg (List.map (receiptAt i)) (step i).arrivals
          obtain ⟨tail, tailFire, tailQueue, tailMark⟩ := ih _ smaller next cut q rfl cutLe
            (fun i => (step i).clock) (fun i => (step i).fires.trans (quiet i)) (sameQueue ▸ queued)
          refine ⟨.cons (.flow flow) tail, tailFire, tailQueue, ?_⟩
          intro i p
          change flow.ledger.mark i p + tail.ledger.mark i p = _
          rw [tailMark]
          have markEq : flow.ledger.mark i p = (step i).flow.ledger.mark 0 p := by
            change (∫ v in date..cut, markAct θ (assemble date current q)
              (fun j => (step j).flow.path v 0) i p) = _
            simp only [Flow.ledger, markAct, assemble, current, clocks i, (step i).clock]
            rfl
          rw [markEq]
          exact (step i).marks p
        · have empty (i : Fin N) : False := cells ⟨i⟩
          have nilQueue : q = [] := by
            have emptyRange : List.finRange N = [] :=
              List.eq_nil_iff_forall_not_mem.mpr (fun i _ => empty i)
            rw [remainingReceipts, emptyRange] at queued
            exact queued.eq_nil
          subst q
          let allFlows (i : Fin N) : Flow (fun _ => θ i) (c i).start (b i) := (empty i).elim
          let flow := parallelFlow clocks finish beforeEnd allFlows [] (by simp)
          exact ⟨.cons (.flow flow) (.nil _), rfl, .rfl, fun i => (empty i).elim⟩

end NetworkStability.NativeMultiToken
