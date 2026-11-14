import ReciprocalLearning

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid

/-- Expose the per-occurrence cuts used inside the native reverse-entry
factory. This retains the exact wire and next-source boundaries instead
of projecting them directly to aggregate dose and FIRE counts. -/
theorem reverse_entry_transaction_rows {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) (hb : PhysicalBox θ ε)
    (hzA : Real.log (3 / 10) - 1 / 100000 ≤ r.final.x 0 (.z 2) ∧
      r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hGB : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2)
    (hback : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    ∃ (n2 : FirstReverseNextWire p)
      (s360 : ReverseWeakStep n2.wire reversePending360)
      (n3 : ReverseWeakNextWire f.parametersA f.parametersB forward backward s360.final)
      (s368 : ReverseWeakStep n3.wire reversePending368)
      (n4 : ReverseWeakNextWire f.parametersA f.parametersB forward backward s368.final)
      (s376 : ReverseLearnedNextSource n4.wire reversePending376),
      s360.final.time = 360 ∧ s368.final.time = 368 ∧ s376.final.time = 376 ∧
      n2.wire.final.time = n2.cycle.fire.final.time + backward n2.cycle.fire.final.time ∧
      n3.wire.final.time = n3.senderCycle.fire.final.time + backward n3.senderCycle.fire.final.time ∧
      n4.wire.final.time = n4.senderCycle.fire.final.time + backward n4.senderCycle.fire.final.time ∧
      s360.final.x 0 (.z 2) = n2.wire.final.x 0 (.z 2) + 3 / 5 ∧
      s368.final.x 0 (.z 2) = n3.wire.final.x 0 (.z 2) + 3 / 5 ∧
      s376.final.x 0 (.z 2) = n4.wire.final.x 0 (.z 2) := by
  have hbP : PhysicalBox (extendParameters f.parametersA (f.parametersB 0)) ε := by
    rw [f.parameters_product]
    exact hb
  have hgP : 9 / 5 ≤ Real.exp (p.final.x 1 (.z 2)) ∧ Real.exp (p.final.x 1 (.z 2)) ≤ 2 := by
    rw [p.b_gains]
    exact hGB
  obtain ⟨n2⟩ := first_reverse_next_wire_exists p hb hzA.2
    ⟨hGB.1,by linarith [hGB.2]⟩ hback
  have hz2 : n2.wire.final.x 0 (.z 2) = r.final.x 0 (.z 2) + (3 / 5) * (1 : ℕ) := by
    rw [n2.wire.gains,p.a_gain_target hb hzA.2]
    norm_num
  have hw2 := (own_birth_weak_gain_bounds hzA.2 (by norm_num : (1 : ℕ) ≤ 2) hz2).2
  have hqueue2 : p.final.pending = ⟨1,2,p.final.time + 8⟩ :: reversePending360 := by
    rw [p.pending,p.date]
    dsimp [firstReverseInterleavedPending,reversePending360]
    rw [sourceTrain_succ]
    norm_num
  have hfuture360 : ∀ d ∈ reversePending360, (360 : ℝ) < d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨s360⟩ := reverse_weak_step_exists n2.wire hbP n2.a_prepared n2.a_charge_lower
    hw2.2 hw2.1 reversePending360 hqueue2 (by rw [p.date]; norm_num; exact hfuture360)
  have ht360 : s360.final.time = 360 := by rw [s360.date,p.date]; norm_num
  have hQ360 : ∀ d ∈ s360.final.pending, s360.final.time + 8 ≤ d.due := by
    intro d hd
    rw [s360.pending] at hd
    rw [ht360]
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨n3⟩ := s360.next_wire_exists hbP (by rw [ht360]; norm_num) hgP p.b_charge hQ360 hback
  have hz3 : n3.wire.final.x 0 (.z 2) = r.final.x 0 (.z 2) + (3 / 5) * (2 : ℕ) := by
    rw [n3.wire.gains,s360.a_gain_target,n2.wire.gains,p.a_gain_target hb hzA.2]
    norm_num
    ring
  have hw3 := (own_birth_weak_gain_bounds hzA.2 (by norm_num : (2 : ℕ) ≤ 2) hz3).2
  have hqueue3 : s360.final.pending = ⟨1,2,s360.final.time + 8⟩ :: reversePending368 := by
    rw [s360.pending,ht360]
    dsimp [reversePending360,reversePending368]
    rw [sourceTrain_succ]
    norm_num
  have hfuture368 : ∀ d ∈ reversePending368, (368 : ℝ) < d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨s368⟩ := reverse_weak_step_exists n3.wire hbP n3.receiver_prepared n3.receiver_charge_lower
    hw3.2 hw3.1 reversePending368 hqueue3 (by rw [ht360]; norm_num; exact hfuture368)
  have ht368 : s368.final.time = 368 := by rw [s368.date,ht360]; norm_num
  have hg360 : 9 / 5 ≤ Real.exp (s360.final.x 1 (.z 2)) ∧ Real.exp (s360.final.x 1 (.z 2)) ≤ 2 := by
    rw [s360.b_gains,n2.wire.gains]
    exact hgP
  have hQ368 : ∀ d ∈ s368.final.pending, s368.final.time + 8 ≤ d.due := by
    intro d hd
    rw [s368.pending] at hd
    rw [ht368]
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨n4⟩ := s368.next_wire_exists hbP (by rw [ht368]; norm_num) hg360 s360.b_charge hQ368 hback
  have hz4 : n4.wire.final.x 0 (.z 2) = r.final.x 0 (.z 2) + 9 / 5 := by
    rw [n4.wire.gains,s368.a_gain_target,n3.wire.gains,s360.a_gain_target,
      n2.wire.gains,p.a_gain_target hb hzA.2]
    ring
  have hg4 := learned_gain_bounds (z := n4.wire.final.x 0 (.z 2))
    (by rw [hz4]; linarith [hzA.1]) (by rw [hz4]; linarith [hzA.2])
  have hqueue4 : s368.final.pending = ⟨1,2,s368.final.time + 8⟩ :: reversePending376 := by
    rw [s368.pending,ht368]
    dsimp [reversePending368,reversePending376]
    rw [sourceTrain_succ]
    norm_num
  have hfuture376 : ∀ d ∈ reversePending376, (376 : ℝ) < d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨s376⟩ := reverse_learned_next_source_exists n4.wire hbP (by rw [ht368]; norm_num)
    n4.receiver_prepared ⟨hg4.1,by linarith [hg4.2]⟩ reversePending376 hqueue4
    (by intro d hd; rw [ht368]; norm_num; exact (hfuture376 d hd).le)
  exact ⟨n2, s360, n3, s368, n4, s376, ht360, ht368, by rw [s376.date, ht368]; norm_num,
    n2.wire.date, n3.wire.date, n4.wire.date, s360.a_gain_target, s368.a_gain_target, s376.gains 0 2⟩


/-- A single post-birth source boundary keeps the two newly recovered
reverse weak writes and the first reverse A FIRE on the same execution. -/
theorem reverse_entry_exact_boundary {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) (box : PhysicalBox θ ε)
    (low : Real.log (3 / 10) - 1 / 100000 ≤ r.final.x 0 (.z 2) ∧
      r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (high : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2)
    (delay : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    ∃ (finish : Snapshot 2) (run : Execution θ (reciprocalEntryRouter forward backward) p.final finish)
      (f352 f360 f368 aFire : ℝ),
      finish.time = 376 ∧
      run.deliveries =
        [⟨0, 2, f352 + backward f352⟩, ⟨1, 2, 360⟩,
          ⟨0, 2, f360 + backward f360⟩, ⟨1, 2, 368⟩,
          ⟨0, 2, f368 + backward f368⟩, ⟨1, 2, 376⟩] ∧
      run.ledger.emissions = [(1, f352), (1, f360), (1, f368), (0, aFire)] ∧
      finish.pending = reversePending376 ∧
      finish.x 0 (.z 2) = p.final.x 0 (.z 2) + 6 / 5 := by
  obtain ⟨n2, s360, n3, s368, n4, s376, date360, date368, _, wire2, wire3, wire4,
    dose2, dose3, dose4⟩ := reverse_entry_transaction_rows p box low high delay
  let rest := (((s360.execution.append n3.wire.execution).append s368.execution).append
    n4.wire.execution).append s376.execution
  let run := n2.execution.append (rest.cast_parameters f.parameters_product)
  refine ⟨_, run, n2.cycle.fire.final.time, n3.senderCycle.fire.final.time, n4.senderCycle.fire.final.time,
    s376.returned.receiver.fire.final.time, by rw [s376.date, date368]; norm_num, ?_, ?_, s376.pending, ?_⟩
  · simp only [run, rest, Execution.deliveries_append, Execution.cast_parameters_deliveries,
      n2.deliveries, s360.deliveries, n3.wire.deliveries, s368.deliveries, n4.wire.deliveries,
      s376.deliveries, List.cons_append, List.nil_append]
    change ([⟨0, 2, n2.wire.final.time⟩, ⟨1, 2, p.final.time + 8⟩,
      ⟨0, 2, n3.wire.final.time⟩, ⟨1, 2, s360.final.time + 8⟩,
      ⟨0, 2, n4.wire.final.time⟩, ⟨1, 2, s368.final.time + 8⟩] : List (Delivery 2)) = _
    rw [wire2, wire3, wire4, p.date, date360, date368]
    norm_num
  · simp only [run, rest, Execution.emissions_append, Execution.cast_parameters_ledger,
      n2.emissions, s360.emissions, n3.wire.emissions, s368.emissions, n4.wire.emissions,
      s376.emissions, List.cons_append, List.nil_append]
  · rw [dose4, n4.wire.gains, dose3, n3.wire.gains, dose2, n2.wire.gains]
    ring

end NetworkStability.NativeReciprocal
