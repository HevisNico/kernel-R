import KernelR.HybridFirstReverseNextWire
import KernelR.HybridReverseWeakNextWire
import KernelR.HybridReverseLearnedReturn
import KernelR.HybridBirthWeakSources

/-! Finish the three own weak doses on Aport2 and construct its first
learned reverse response. Every B wire comes from its actual source FIRE. -/
namespace KernelR.Hybrid

noncomputable def reversePending360 : List (Delivery 2) :=
  sourceTrain 1 2 368 8 10 ++ sourceTrain 1 2 480 8 16
noncomputable def reversePending368 : List (Delivery 2) :=
  sourceTrain 1 2 376 8 9 ++ sourceTrain 1 2 480 8 16
noncomputable def reversePending376 : List (Delivery 2) :=
  sourceTrain 1 2 384 8 8 ++ sourceTrain 1 2 480 8 16

structure ReverseEntryCompletion {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) where
  final : Snapshot 2
  execution : Execution θ (reciprocalEntryRouter forward backward) p.final final
  date : final.time = 376
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_active : final.raw 1 2 = some final.time
  raw_other : ∀ i q, i ≠ 1 ∨ q ≠ 2 → final.raw i q = none
  pending : final.pending = reversePending376
  a_gain_target : final.x 0 (.z 2) = p.final.x 0 (.z 2) + 6 / 5
  a_gain_other : ∀ q, q ≠ 2 → final.x 0 (.z q) = p.final.x 0 (.z q)
  b_gains : ∀ q, final.x 1 (.z q) = p.final.x 1 (.z q)
  recovery : ∀ i, final.x i .b = p.final.x i .b
  a_emission_count : (execution.emissionTimes 0).length = 1
  b_emission_count : (execution.emissionTimes 1).length = 3
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution 376

theorem reverse_entry_completion_exists {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) (hb : PhysicalBox θ ε)
    (hzA : Real.log (3 / 10) - 1 / 100000 ≤ r.final.x 0 (.z 2) ∧
      r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hGB : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2)
    (hback : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReverseEntryCompletion p) := by
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
  let after : Execution (extendParameters f.parametersA (f.parametersB 0))
      (reciprocalEntryRouter forward backward) n2.wire.final s376.final :=
    ((((s360.execution.append n3.wire.execution).append s368.execution).append n4.wire.execution).append s376.execution)
  let trace := n2.execution.append (after.cast_parameters f.parameters_product)
  have htarget : s376.final.x 0 (.z 2) = p.final.x 0 (.z 2) + 6 / 5 := by
    rw [s376.gains,n4.wire.gains,s368.a_gain_target,n3.wire.gains,s360.a_gain_target,n2.wire.gains]
    ring
  have hother : ∀ q, q ≠ 2 → s376.final.x 0 (.z q) = p.final.x 0 (.z q) := by
    intro q hq
    rw [s376.gains,n4.wire.gains,s368.a_gain_other q hq,n3.wire.gains,
      s360.a_gain_other q hq,n2.wire.gains]
  have hB : ∀ q, s376.final.x 1 (.z q) = p.final.x 1 (.z q) := by
    intro q
    rw [s376.gains,n4.wire.gains,s368.b_gains,n3.wire.gains,s360.b_gains,n2.wire.gains]
  have hrec : ∀ i, s376.final.x i .b = p.final.x i .b := by
    intro i
    rw [s376.recovery,n4.wire.recovery,s368.recovery,n3.wire.recovery,s360.recovery,n2.wire.recovery]
  have he : trace.ledger.emissions = [(1,n2.cycle.fire.final.time),
      (1,n3.senderCycle.fire.final.time),(1,n4.senderCycle.fire.final.time),
      (0,s376.returned.receiver.fire.final.time)] := by
    simp only [trace,after,Execution.emissions_append,Execution.cast_parameters_ledger,
      n2.emissions,s360.emissions,n3.wire.emissions,s368.emissions,n4.wire.emissions,
      s376.emissions,List.nil_append,List.append_nil,List.cons_append]
  refine ⟨{
    final := s376.final, execution := trace
    date := by rw [s376.date,ht368]; norm_num
    prepared := s376.prepared, charge := s376.charge
    raw_active := s376.raw_active, raw_other := s376.raw_other, pending := s376.pending
    a_gain_target := htarget, a_gain_other := hother, b_gains := hB, recovery := hrec
    a_emission_count := by simp [Execution.emissionTimes,he]
    b_emission_count := by simp [Execution.emissionTimes,he]
    physical := by simpa only [f.parameters_product] using s376.physical
    raw_valid := s376.raw_valid
    complete := ?_
  }⟩
  have hc := s376.complete (by rw [ht368]; norm_num; exact hfuture376)
  simpa only [CompleteThrough,ht368,show (368 : ℝ) + 8 = 376 by norm_num] using hc

end KernelR.Hybrid
