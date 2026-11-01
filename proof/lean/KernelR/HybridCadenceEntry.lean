import KernelR.HybridCadenceCascade
/-! Physical cumulative A54/B61/C34 with each cell's own acquired memories. -/
namespace KernelR.Hybrid

structure CadenceEntry {θ freshB freshC routeBefore born s u v w}
    {forward backward delay : ℝ → ℝ}
    {teaching : @StagedExecution 1 θ freshB routeBefore (reciprocalEntryRouter forward backward) born s}
    {following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u}
    {introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v}
    (entry : CEntry forward backward delay teaching following introduction)
    (nextForward nextBackward : ℝ → ℝ)
    (next : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cadenceRouter nextForward nextBackward) v w) where
  cascade : CadenceCascade next
  a_emissions : (teaching.before.emissionTimes 0).length + (teaching.after.emissionTimes 0).length +
    (following.emissionTimes 0).length + (introduction.before.emissionTimes 0).length +
    (introduction.after.emissionTimes 0).length + (next.emissionTimes 0).length = 54
  b_emissions : (teaching.after.emissionTimes 1).length + (following.emissionTimes 1).length +
    (introduction.before.emissionTimes 1).length + (introduction.after.emissionTimes 1).length +
    (next.emissionTimes 1).length = 61
  c_emissions : (introduction.after.emissionTimes 2).length + (next.emissionTimes 2).length = 34
  gain_a_initial : w.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5
  gain_a_return : w.x 0 (.z 2) = born.x 0 (.z 2) + 12 / 5
  gain_a_other : w.x 0 (.z 1) = born.x 0 (.z 1)
  gain_b_fast : w.x 1 (.z 1) = teaching.birth.newborn.x (.z 1) + 3 / 5
  gain_b_return : w.x 1 (.z 2) = teaching.birth.newborn.x (.z 2) + 12 / 5
  gain_b_other : w.x 1 (.z 0) = teaching.birth.newborn.x (.z 0)
  gain_c_initial : w.x 2 (.z 0) = introduction.birth.newborn.x (.z 0) + 12 / 5
  gain_c_fast : w.x 2 (.z 1) = introduction.birth.newborn.x (.z 1) + 3 / 5
  gain_c_other : w.x 2 (.z 2) = introduction.birth.newborn.x (.z 2)
  recovery_a : w.x 0 .b = born.x 0 .b + 3 / 10
  recovery_b : w.x 1 .b = teaching.birth.newborn.x .b + 3 / 10
  recovery_c : w.x 2 .b = introduction.birth.newborn.x .b + 3 / 10

/-- The original READY A birth, actual earlier births and physical C-entry
state feed the complete cadence cascade. The actual reaching execution is
given; its calendars, pulse cases, doses and counts are all derived. -/
theorem CEntry.cadence_entry {θ freshB freshC ε routeBefore born s u v w}
    {forward backward delay : ℝ → ℝ}
    {teaching : @StagedExecution 1 θ freshB routeBefore (reciprocalEntryRouter forward backward) born s}
    {following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u}
    {introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v}
    (entry : CEntry forward backward delay teaching following introduction)
    (hborn : BirthState born) (nextForward nextBackward : ℝ → ℝ)
    (next : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cadenceRouter nextForward nextBackward) v w)
    (hb : PhysicalBox (extendParameters (extendParameters θ freshB) freshC) ε)
    (hsources : introduction.birth.sources = sourceTrain 2 0 640 4 25)
    (hw : w.time = 7899 / 10)
    (hforward : ∀ t, 3 / 10 ≤ nextForward t ∧ nextForward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ nextBackward t ∧ nextBackward t ≤ 2 / 5) :
    Nonempty (CadenceEntry entry nextForward nextBackward next) := by
  have hs : ∀ i, PreparedSection v i := by
    intro i
    fin_cases i
    · exact entry.c_introduction.phase.a_idle.prepared
    · exact entry.c_introduction.phase.b_train.prepared
    · exact entry.c_introduction.phase.c_phase.prepared
  have hq : ∀ i, v.x i .q = 1 / 10 := by
    intro i
    fin_cases i
    · exact entry.c_introduction.phase.a_idle.charge_rest
    · exact entry.c_introduction.phase.b_train.charge_rest
    · exact entry.c_introduction.phase.c_phase.charge_rest
  have hr : ∀ i p, v.raw i p = none := by
    intro i p
    fin_cases i
    · exact entry.c_introduction.a_raw p
    · exact entry.c_introduction.phase.b_train.raw_finished p
    · exact entry.c_introduction.phase.c_phase.raw_finished p
  have hza : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ v.x 0 (.z 2) ∧
      v.x 0 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    have hz : Real.log (3 / 10) - 1 / 100000 ≤ born.x 0 (.z 2) ∧
        born.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
      simpa [nominalGain] using ((hborn.2.2 0).2.2.2.2 (2 : Port)).1
    rw [entry.gain_a_return]
    constructor <;> linarith [hz.1,hz.2]
  have hzb : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ v.x 1 (.z 2) ∧
      v.x 1 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    have hz := teaching.birth.newborn.gain (2 : Port)
    norm_num [nominalGain] at hz
    rw [entry.gain_b_return]
    constructor <;> linarith [hz.1,hz.2]
  have hzc : Real.log (3 / 10) - 1 / 100000 ≤ v.x 2 (.z 0) ∧
      v.x 2 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [entry.c_introduction.gain_c_other 0 (by decide)]
    simpa [nominalGain] using introduction.birth.newborn.gain (0 : Port)
  obtain ⟨cascade⟩ := next.cadence_cascade nextForward nextBackward hb
    entry.c_introduction.physical entry.c_introduction.raw_valid hs hq hr hza hzb hzc
    entry.c_introduction.queues.a_empty entry.c_introduction.queues.b_empty (entry.cadence_sources hsources)
    hw entry.c_introduction.pending_future hforward hbackward
  refine ⟨⟨cascade,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · have hp := entry.a_emissions
    have hc := cascade.a_emissions
    omega
  · have hp := entry.b_emissions
    have hc := cascade.b_emissions
    omega
  · rw [entry.c_emissions,cascade.c_emissions]
  · rw [cascade.gain_a_other 0 (by decide),entry.gain_a_initial]
  · rw [cascade.gain_a,entry.gain_a_return]
    ring
  · rw [cascade.gain_a_other 1 (by decide),entry.gain_a_other]
  · rw [cascade.gain_b_other 1 (by decide),entry.gain_b_fast]
  · rw [cascade.gain_b,entry.gain_b_return]
    ring
  · rw [cascade.gain_b_other 0 (by decide),entry.gain_b_other]
  · rw [cascade.gain_c,entry.c_introduction.gain_c_other 0 (by decide)]
  · rw [cascade.gain_c_other 1 (by decide),entry.c_introduction.gain_c_target]
  · rw [cascade.gain_c_other 2 (by decide),entry.c_introduction.gain_c_other 2 (by decide)]
  · rw [cascade.recovery 0,entry.recovery_a]
    ring
  · rw [cascade.recovery 1,entry.recovery_b]
    ring
  · rw [cascade.recovery 2,entry.c_introduction.recovery_c]
    ring

/-- One complete physical contract from A's birth queue through both fresh
births and the final cascade. Only the sources, contacts, physical family and
actual reaching traces are supplied; all intermediate proof packages follow. -/
theorem StagedExecution.reciprocal_cadence_entry {θ freshB freshC ε routeBefore born s u v w}
    (forward backward delay nextForward nextBackward : ℝ → ℝ)
    (teaching : @StagedExecution 1 θ freshB routeBefore (reciprocalEntryRouter forward backward) born s)
    (following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u)
    (introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v)
    (next : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cadenceRouter nextForward nextBackward) v w)
    (hborn : BirthState born)
    (hb : PhysicalBox (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbefore : ∀ i t, routeBefore i t = [])
    (hbirthB : teaching.beforeBirth.time = 160) (hteaching : s.time = 3199 / 10)
    (hreturn : u.time = 4599 / 10) (hbirthC : introduction.beforeBirth.time = 480)
    (hintro : v.time = 6399 / 10) (hend : w.time = 7899 / 10)
    (hsourcesB : teaching.birth.sources = sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 16)
    (hsourcesC : introduction.birth.sources = sourceTrain 2 0 640 4 25)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5)
    (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hnextForward : ∀ t, 3 / 10 ≤ nextForward t ∧ nextForward t ≤ 2 / 5)
    (hnextBackward : ∀ t, 3 / 10 ≤ nextBackward t ∧ nextBackward t ≤ 2 / 5) :
    ∃ entry : CEntry forward backward delay teaching following introduction,
      CadenceEntry entry nextForward nextBackward next := by
  have hsourceFuture : ∀ d ∈ introduction.birth.sources, (640 : ℝ) ≤ d.due := by
    rw [hsourcesC]
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    change (640 : ℝ) ≤ 640 + 4 * (k.val : ℝ)
    linarith
  obtain ⟨entry⟩ := teaching.reciprocal_c_entry forward backward delay following introduction hborn hb ha
    hqueue hbefore hbirthB hteaching hreturn hbirthC hintro hsourcesB hsourceFuture hforward hbackward hdelay
  obtain ⟨complete⟩ := entry.cadence_entry hborn nextForward nextBackward next hb hsourcesC hend
    hnextForward hnextBackward
  exact ⟨entry,complete⟩

end KernelR.Hybrid
