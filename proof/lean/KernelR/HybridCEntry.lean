import KernelR.HybridReciprocalEntry
import KernelR.HybridStagedCIntroduction
/-! Physical A38/B43/C14 from the original A birth through C's introduction. -/
namespace KernelR.Hybrid

structure CEntry {θ freshB freshC routeBefore born s u v}
    (forward backward delay : ℝ → ℝ)
    (teaching : @StagedExecution 1 θ freshB routeBefore (reciprocalEntryRouter forward backward) born s)
    (following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u)
    (introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v) where
  reciprocal : ReciprocalEntry forward backward teaching following
  c_introduction : StagedCIntroduction forward backward delay introduction
  a_emissions : (teaching.before.emissionTimes 0).length + (teaching.after.emissionTimes 0).length +
    (following.emissionTimes 0).length + (introduction.before.emissionTimes 0).length +
    (introduction.after.emissionTimes 0).length = 38
  b_emissions : (teaching.after.emissionTimes 1).length + (following.emissionTimes 1).length +
    (introduction.before.emissionTimes 1).length + (introduction.after.emissionTimes 1).length = 43
  c_emissions : (introduction.after.emissionTimes 2).length = 14
  gain_a_initial : v.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5
  gain_a_return : v.x 0 (.z 2) = born.x 0 (.z 2) + 9 / 5
  gain_a_other : v.x 0 (.z 1) = born.x 0 (.z 1)
  gain_b_fast : v.x 1 (.z 1) = teaching.birth.newborn.x (.z 1) + 3 / 5
  gain_b_return : v.x 1 (.z 2) = teaching.birth.newborn.x (.z 2) + 9 / 5
  gain_b_other : v.x 1 (.z 0) = teaching.birth.newborn.x (.z 0)
  recovery_a : v.x 0 .b = born.x 0 .b + 1 / 10
  recovery_b : v.x 1 .b = teaching.birth.newborn.x .b + 1 / 10

/-- The future part of the original B birth queue is exactly its second
sixteen-source train at the reciprocal handoff. -/
theorem ReciprocalEntry.b_teaching_queue {θ fresh routeBefore born s u forward backward}
    {teaching : @StagedExecution 1 θ fresh routeBefore (reciprocalEntryRouter forward backward) born s}
    {following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u}
    (entry : ReciprocalEntry forward backward teaching following)
    (hsources : teaching.birth.sources = sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 16)
    (hu : u.time = 4599 / 10) :
    (u.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 480 8 16) := by
  have hfirst : (sourceTrain (1 : Fin 2) 2 320 8 16).filter (fun d => u.time < d.due) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
    simp only [decide_eq_true_eq]
    rw [hu]
    change ¬ (4599 / 10 : ℝ) < 320 + 8 * (k.val : ℝ)
    linarith
  have hlast : (sourceTrain (1 : Fin 2) 2 480 8 16).filter (fun d => u.time < d.due) =
      sourceTrain 1 2 480 8 16 := by
    apply List.filter_eq_self.mpr
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    apply decide_eq_true
    rw [hu]
    change (4599 / 10 : ℝ) < 480 + 8 * (k.val : ℝ)
    linarith
  simpa only [hsources,List.filter_append,hfirst,hlast,List.nil_append] using entry.b_pending_sources

/-- The already-derived reciprocal state feeds a genuine C birth and the
actual B-to-C teaching execution. No new source calendar or desired output
count is assumed at this handoff. -/
theorem ReciprocalEntry.c_entry {θ freshB freshC ε routeBefore born s u v}
    (forward backward delay : ℝ → ℝ)
    {teaching : @StagedExecution 1 θ freshB routeBefore (reciprocalEntryRouter forward backward) born s}
    {following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u}
    (entry : ReciprocalEntry forward backward teaching following)
    (introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v)
    (hb : PhysicalBox (extendParameters (extendParameters θ freshB) freshC) ε)
    (hsourcesB : teaching.birth.sources = sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 16)
    (hu : u.time = 4599 / 10) (hbirth : introduction.beforeBirth.time = 480)
    (hv : v.time = 6399 / 10) (hsourcesC : ∀ d ∈ introduction.birth.sources, 640 ≤ d.due)
    (hforward : ∀ t, 0 ≤ forward t) (hbackward : ∀ t, 0 ≤ backward t)
    (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) :
    Nonempty (CEntry forward backward delay teaching following introduction) := by
  have hlog : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ u.x 1 (.z 2) ∧
      u.x 1 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    have hz := teaching.birth.newborn.gain (2 : Port)
    norm_num [nominalGain] at hz
    rw [entry.gain_b_return]
    constructor <;> linarith [hz.1,hz.2]
  have hgain := learned_gain_bounds hlog.1 hlog.2
  have hG : 9 / 5 ≤ Real.exp (u.x 1 (.z 2)) ∧ Real.exp (u.x 1 (.z 2)) ≤ 12 / 5 :=
    ⟨hgain.1,by linarith [hgain.2]⟩
  obtain ⟨phase⟩ := introduction.c_introduction forward backward delay hb entry.physical entry.raw_valid
    entry.feedback_phase.a_learning.prepared entry.feedback_phase.a_learning.charge_rest
    entry.feedback_phase.a_learning.raw_finished entry.feedback_phase.b_learning.prepared
    entry.feedback_phase.b_learning.charge_rest entry.feedback_phase.b_learning.raw_finished hG
    entry.a_pending_empty (entry.b_teaching_queue hsourcesB hu) hu hbirth hv hsourcesC
    entry.pending_future hforward hbackward hdelay
  refine ⟨⟨entry,phase,?_,?_,phase.c_emissions,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · have h := entry.a_emissions
    have hc := phase.a_emissions
    omega
  · have h := entry.b_emissions
    have hc := phase.b_emissions
    omega
  · rw [phase.gain_a 0,entry.gain_a_initial]
  · rw [phase.gain_a 2,entry.gain_a_return]
  · rw [phase.gain_a 1,entry.gain_a_other]
  · rw [phase.gain_b 1,entry.gain_b_fast]
  · rw [phase.gain_b 2,entry.gain_b_return]
  · rw [phase.gain_b 0,entry.gain_b_other]
  · rw [phase.recovery_a,entry.recovery_a]
  · rw [phase.recovery_b,entry.recovery_b]

/-- From A's READY birth and both actual dimension-changing births, derive
physical A38/B43/C14 through 639.9. Existence of the reaching executions is
still supplied explicitly; case words, received calendars and counts are not. -/
theorem StagedExecution.reciprocal_c_entry {θ freshB freshC ε routeBefore born s u v}
    (forward backward delay : ℝ → ℝ)
    (teaching : @StagedExecution 1 θ freshB routeBefore (reciprocalEntryRouter forward backward) born s)
    (following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u)
    (introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v)
    (hborn : BirthState born)
    (hb : PhysicalBox (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbefore : ∀ i t, routeBefore i t = [])
    (hbirthB : teaching.beforeBirth.time = 160) (hteaching : s.time = 3199 / 10)
    (hreturn : u.time = 4599 / 10) (hbirthC : introduction.beforeBirth.time = 480)
    (hend : v.time = 6399 / 10)
    (hsourcesB : teaching.birth.sources = sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 16)
    (hsourcesC : ∀ d ∈ introduction.birth.sources, 640 ≤ d.due)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5)
    (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) :
    Nonempty (CEntry forward backward delay teaching following introduction) := by
  obtain ⟨entry⟩ := teaching.reciprocal_entry_two_trains forward backward following hborn hb.extend_old
    ha hqueue hbefore hbirthB hteaching hreturn hsourcesB hforward hbackward
  exact entry.c_entry forward backward delay introduction hb hsourcesB hreturn hbirthC hend hsourcesC
    (fun t => by linarith [(hforward t).1]) (fun t => by linarith [(hbackward t).1]) hdelay

/-- The external period-four C sources remain in the same original newborn
queue. This retains all twenty-five input tokens; their fast responses are
not asserted by the present teaching theorem. -/
theorem CEntry.cadence_sources {θ freshB freshC routeBefore born s u v forward backward delay}
    {teaching : @StagedExecution 1 θ freshB routeBefore (reciprocalEntryRouter forward backward) born s}
    {following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u}
    {introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v}
    (entry : CEntry forward backward delay teaching following introduction)
    (hsources : introduction.birth.sources = sourceTrain 2 0 640 4 25) :
    (v.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 25) := by
  rw [← hsources]
  exact entry.c_introduction.c_sources

end KernelR.Hybrid
