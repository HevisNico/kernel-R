import KernelR.HybridTeachingQueueClosure
import KernelR.HybridFeedbackEpoch
import KernelR.HybridFeedbackQueueClosure
/-! Physical reciprocal entry through 459.9, retaining both complete source epochs. -/
namespace KernelR.Hybrid

structure ReciprocalEntry {θ fresh routeBefore born s u}
    (forward backward : ℝ → ℝ)
    (teaching : @StagedExecution 1 θ fresh routeBefore (reciprocalEntryRouter forward backward) born s)
    (following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u) where
  teaching_phase : StagedTeaching teaching
  feedback_phase : FeedbackEpoch following
  a_emissions : (teaching.before.emissionTimes 0).length + (teaching.after.emissionTimes 0).length +
    (following.emissionTimes 0).length = 38
  b_emissions : (teaching.after.emissionTimes 1).length + (following.emissionTimes 1).length = 27
  gain_a_initial : u.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5
  gain_a_return : u.x 0 (.z 2) = born.x 0 (.z 2) + 9 / 5
  gain_a_other : u.x 0 (.z 1) = born.x 0 (.z 1)
  gain_b_fast : u.x 1 (.z 1) = teaching.birth.newborn.x (.z 1) + 3 / 5
  gain_b_return : u.x 1 (.z 2) = teaching.birth.newborn.x (.z 2) + 9 / 5
  gain_b_other : u.x 1 (.z 0) = teaching.birth.newborn.x (.z 0)
  recovery_a : u.x 0 .b = born.x 0 .b + 1 / 10
  recovery_b : u.x 1 .b = teaching.birth.newborn.x .b + 1 / 10
  physical : PhysicalInvariant (extendParameters θ fresh) u
  raw_valid : RawValid u
  pending_future : PendingFuture u
  a_pending_empty : u.pending.filter (fun d => d.cell = 0) = []
  b_pending_sources : (u.pending.filter (fun d => d.cell = 1)).Perm
    (teaching.birth.sources.filter (fun d => u.time < d.due))

/-- The actual teaching prefix and return execution yield A38/B27. Both cells
retain their own memories and every case/calendar/count comes from the physical
trace. Only the initial source queues, contacts and reaching executions are given. -/
theorem StagedExecution.reciprocal_entry {θ fresh ε routeBefore born s u}
    (forward backward : ℝ → ℝ)
    (e : @StagedExecution 1 θ fresh routeBefore (reciprocalEntryRouter forward backward) born s)
    (following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u)
    (hborn : BirthState born) (hb : PhysicalBox (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbefore : ∀ i t, routeBefore i t = [])
    (hbirth : e.beforeBirth.time = 160) (hteaching : s.time = 3199 / 10) (hend : u.time = 4599 / 10)
    (later : List (Delivery 2))
    (hsources : e.birth.sources = sourceTrain 1 2 320 8 16 ++ later)
    (hlater : ∀ d ∈ later, (4599 / 10 : ℝ) < d.due)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReciprocalEntry forward backward e following) := by
  have hsourceLower : ∀ d ∈ e.birth.sources, (320 : ℝ) ≤ d.due := by
    intro d hd
    rw [hsources] at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
      change (320 : ℝ) ≤ 320 + 8 * (k.val : ℝ)
      linarith
    · linarith [hlater d hd]
  obtain ⟨teach⟩ := StagedExecution.reciprocal_teaching_epoch forward backward e hborn hb ha hqueue
    hbefore hbirth hteaching hsourceLower hforward hbackward
  have closure := StagedExecution.teaching_queue_closure forward backward e hborn hqueue hbefore
    hteaching hsourceLower hforward hbackward
  have hbqueue : (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 320 8 16 ++ later) := by
    rw [← hsources]
    exact closure.b_sources
  have hfi := e.physical_invariant hb (hborn.physical_invariant hb.extend_old)
  have hvalid := e.raw_valid hborn.raw_valid
  have hcausal := reciprocalEntryRouter.causal forward backward
    (fun t => by linarith [(hforward t).1]) (fun t => by linarith [(hbackward t).1])
  have hbeforeCausal : CausalRouter routeBefore := by simp [CausalRouter,hbefore]
  have hinitial : PendingFuture born := by
    intro d hd
    rw [hqueue] at hd
    rw [hborn.1]
    rcases List.mem_append.mp hd with hd | hd
    all_goals obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd; dsimp; positivity
  have hpf : PendingFuture s := e.pending_future hbeforeCausal hcausal hinitial
  have hza : Real.log (3 / 10) - 1 / 100000 ≤ s.x 0 (.z 2) ∧
      s.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [teach.gain_a_other 2 (by decide)]
    simpa [nominalGain] using ((hborn.2.2 0).2.2.2.2 (2 : Port)).1
  have hzb : Real.log (3 / 10) - 1 / 100000 ≤ s.x 1 (.z 2) ∧
      s.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [teach.gain_b_other 2 (by decide)]
    simpa [nominalGain] using e.birth.newborn.gain (2 : Port)
  obtain ⟨feedback⟩ := Execution.feedback_epoch forward backward following hb hfi hvalid
    teach.teaching.a_train.prepared teach.teaching.a_train.charge_rest hza teach.teaching.a_train.raw_finished
    teach.teaching.b_phase.prepared teach.teaching.b_phase.charge_rest hzb teach.teaching.b_phase.raw_finished
    later closure.a_empty hbqueue (by simpa only [hend] using hlater) hteaching hend hpf hforward hbackward
  have hG : 9 / 5 ≤ Real.exp (s.x 1 (.z 2) + 9 / 5) ∧
      Real.exp (s.x 1 (.z 2) + 9 / 5) ≤ 12 / 5 := by
    have hlog : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 1 (.z 2) + 9 / 5 ∧
        s.x 1 (.z 2) + 9 / 5 ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
      constructor <;> linarith [hzb.1,hzb.2]
    have h := learned_gain_bounds hlog.1 hlog.2
    exact ⟨h.1,by linarith [h.2]⟩
  have finalQueue := following.feedback_queue_closure forward backward feedback.b_sender later
    closure.a_empty hbqueue (by simpa only [hend] using hlater) hteaching hend
    (following.pending_future hcausal hpf) (restLatency_spec hG).2.1 (fun t => (hbackward t).2)
  have hfiltered : e.birth.sources.filter (fun d => u.time < d.due) = later := by
    rw [hsources,List.filter_append]
    have hfirst : (sourceTrain (1 : Fin 2) 2 320 8 16).filter (fun d => u.time < d.due) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
      simp only [decide_eq_true_eq]
      rw [hend]
      change ¬ (4599 / 10 : ℝ) < 320 + 8 * (k.val : ℝ)
      linarith
    have hlast : later.filter (fun d => u.time < d.due) = later := by
      apply List.filter_eq_self.mpr
      intro d hd
      exact decide_eq_true (by simpa only [hend] using hlater d hd)
    rw [hfirst,hlast,List.nil_append]
  refine ⟨⟨teach,feedback,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    following.physical_invariant hb hfi,following.raw_valid hvalid,
    following.pending_future hcausal hpf,finalQueue.a_empty,?_⟩⟩
  · rw [teach.a_emissions,feedback.a_learning.emissions]
  · rw [teach.b_emissions,feedback.b_learning.emissions]
  · rw [feedback.a_learning.gain_other 0 (by decide),teach.gain_a_target]
  · rw [feedback.a_learning.gain_target,teach.gain_a_other 2 (by decide)]
  · rw [feedback.a_learning.gain_other 1 (by decide),teach.gain_a_other 1 (by decide)]
  · rw [feedback.b_learning.gain_other 1 (by decide),teach.gain_b_target]
  · rw [feedback.b_learning.gain_target,teach.gain_b_other 2 (by decide)]
  · rw [feedback.b_learning.gain_other 0 (by decide),teach.gain_b_other 0 (by decide)]
  · rw [feedback.a_learning.recovery_preserved,teach.recovery_a]
  · rw [feedback.b_learning.recovery_preserved,teach.recovery_b]
  · rw [hfiltered]
    exact finalQueue.b_sources

/-- Keep the later B teaching train at 480..600 in the same birth queue while
deriving the complete physical reciprocal entry at 459.9. -/
theorem StagedExecution.reciprocal_entry_two_trains {θ fresh ε routeBefore born s u}
    (forward backward : ℝ → ℝ)
    (e : @StagedExecution 1 θ fresh routeBefore (reciprocalEntryRouter forward backward) born s)
    (following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u)
    (hborn : BirthState born) (hb : PhysicalBox (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbefore : ∀ i t, routeBefore i t = [])
    (hbirth : e.beforeBirth.time = 160) (hteaching : s.time = 3199 / 10) (hend : u.time = 4599 / 10)
    (hsources : e.birth.sources = sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 16)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReciprocalEntry forward backward e following) := by
  apply StagedExecution.reciprocal_entry forward backward e following hborn hb ha hqueue hbefore hbirth
    hteaching hend (sourceTrain 1 2 480 8 16) hsources ?_ hforward hbackward
  intro d hd
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
  have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  change (4599 / 10 : ℝ) < 480 + 8 * (k.val : ℝ)
  linarith

end KernelR.Hybrid
