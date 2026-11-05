import KernelR.HybridLocalCadenceBudgetReceiver
import KernelR.HybridMarkSectionCovers
import KernelR.HybridErrorSectionCovers
import KernelR.HybridInactiveSectionCovers
import KernelR.HybridSectionGates
import KernelR.HybridCompleteSectionCovers

/-! Actual section covers of the autonomous cadence receiver. The framed
executions are classified physically; ledger equality is used only to establish
absence of arrivals, never to transfer an active section. -/
namespace KernelR.Hybrid

theorem Execution.deliveries_length_eq_delivered {n θ route s u}
    (e : @Execution n θ route s u) : e.deliveries.length = e.ledger.delivered := by
  induction e with
  | nil => rfl
  | cons move rest ih =>
    cases move with
    | flow f => simpa [Execution.deliveries,Move.deliveries,Execution.ledger,
        Move.ledger,Flow.ledger,Ledger.add] using ih
    | jump j => cases j <;> simpa [Execution.deliveries,Move.deliveries,
        Jump.deliveries,Execution.ledger,Move.ledger,Jump.ledger,Ledger.add,Ledger.zero,Nat.add_comm] using ih

theorem Execution.noArrivalAt_of_emptyRoute_ledger {n θ s u s' u'}
    (e : @Execution n θ (fun _ _ => []) s u)
    (offline : Execution θ (fun _ _ => []) s' u')
    (initial : s'.pending = []) (ledger : e.ledger = offline.ledger)
    (i : Fin n) (p : Port) : NoArrivalAt e i p := by
  have empty : offline.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    rcases offline.delivery_provenance d hd with hd | ⟨event,_,hd⟩
    · simp [initial] at hd
    · simp at hd
  have count : e.deliveries.length = 0 := by
    rw [e.deliveries_length_eq_delivered,ledger,← offline.deliveries_length_eq_delivered,empty]
    rfl
  have empty' : e.deliveries = [] := List.length_eq_zero_iff.mp count
  simp [NoArrivalAt,empty']

/-- The physical MARK phase is reconstructed on the actual queued execution. -/
theorem CadenceMarkOnlyJitterNextSource.mark_section_covers {θ ε s p H later}
    (c : CadenceMarkOnlyJitterNextSource θ s p H later)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : s.main 0 = .slow) (hq : 11 / 100 ≤ s.x 0 .q)
    (hrec : s.x 0 .b ≤ 3 / 10)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hgap : s.time + 419 / 300 ≤ H) (gates : LearningGatesOpen c.execution) :
    ∀ q, Nonempty (MarkSectionCover 0 q c.execution) := by
  have hno (q : Port) : NoArrivalAt c.framed 0 q :=
    c.framed.noArrivalAt_of_emptyRoute_ledger c.offline rfl c.framed_ledger 0 q
  have date : c.before.time = H := c.arrival.time_unchanged.symm.trans c.date
  obtain ⟨pulse⟩ := c.framed.short_mark_pulse_of_invariant hb hf hv 0 p hm hq hrec ha hr ho hno
    (by rw [date]; exact hgap)
  intro q
  by_cases same : q = p
  · subst q
    obtain ⟨cover,_⟩ := pulse.mark_section_cover hb hf hv hr (hno p) (by linarith)
    rw [c.reconstruct]
    exact ⟨cover.append (.inactive (.jump c.arrival) (.nil _) trivial (.nil _))⟩
  · obtain ⟨cover,_⟩ := c.execution.mark_cover_of_zero_open hb gates 0 q (c.mark_other q same)
    exact ⟨cover⟩

theorem CadenceMixedFullJitterNextSource.section_covers {θ ε s p H later}
    (c : CadenceMixedFullJitterNextSource θ s p H later)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : s.main 0 = .slow)
    (hq : 59 / 500 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 71 / 500)
    (hrec : 27999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 28001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hgap : s.time + 37 / 10 ≤ H) (gates : LearningGatesOpen c.execution) :
    (∀ q, Nonempty (ErrorSectionCover 0 q c.execution)) ∧
    (∀ q, Nonempty (MarkSectionCover 0 q c.execution)) := by
  have hno (q : Port) : NoArrivalAt c.framed 0 q :=
    c.framed.noArrivalAt_of_emptyRoute_ledger c.offline rfl c.framed_ledger 0 q
  have date : c.before.time = H := c.arrival.time_unchanged.symm.trans c.date
  obtain ⟨pulse⟩ := c.framed.cadence_mixed_full_pulse hb hf hv 0 p hm hq hrec ha hz hr ho hno
    (by rw [date]; exact hgap)
  constructor
  · intro q
    by_cases same : q = p
    · subst q
      have headroom : s.x 0 (.z p) + 3 / 5 < Real.log ((θ 0).cap p) :=
        lt_of_le_of_lt (by linarith [hz.2]) (hb.low_gain_headroom 0 p)
      obtain ⟨cover,_⟩ := pulse.mark_case.cycle.error_cover_of_ready_error hb hf hv
        pulse.error_ready headroom hr (hno p)
      rw [c.reconstruct]
      exact ⟨cover.append (.inactive (.jump c.arrival) (.nil _) trivial (.nil _))⟩
    · obtain ⟨cover,_⟩ := c.execution.error_cover_of_zero_open hb gates 0 q (c.error_other q same)
      exact ⟨cover⟩
  · intro q
    by_cases same : q = p
    · subst q
      obtain ⟨cover,_⟩ := pulse.mark_case.mark_section_cover hb hf hv hr (hno p) (by linarith [hrec.2])
      rw [c.reconstruct]
      exact ⟨cover.append (.inactive (.jump c.arrival) (.nil _) trivial (.nil _))⟩
    · obtain ⟨cover,_⟩ := c.execution.mark_cover_of_zero_open hb gates 0 q (c.mark_other q same)
      exact ⟨cover⟩

/-- Covers are built by joining the actual retained receiver phases. -/
theorem LocalCadenceBudgetReceiver.section_covers_of_gates {θ ε s p m L J}
    {packet : KernelR.Chain.Packet m L J} {terminal}
    (r : LocalCadenceBudgetReceiver θ s p packet terminal)
    (hb : PhysicalBox θ ε) (gates : LearningGatesOpen r.execution) :
    (∀ q, Nonempty (ErrorSectionCover 0 q r.execution)) ∧
    (∀ q, Nonempty (MarkSectionCover 0 q r.execution)) := by
  have split := gates
  rw [r.reconstruct] at split
  simp only [LearningGatesOpen,Execution.allFlows_append] at split
  rcases split with ⟨g0,g1,g2,g3,g4,g5,g6⟩
  have prefixRec : r.learnedPrefix.final.x 0 .b = s.x 0 .b :=
    r.learnedPrefix.recovery.trans r.firstSource.recovery
  have markRec : r.firstStrong.final.x 0 .b ≤ 3 / 10 := by
    rw [r.firstStrong.recovery,prefixRec]
    linarith [r.initial_prepared.recovery.2]
  have markGap : r.firstStrong.final.time + 419 / 300 ≤ packet.actual (m + 1) := by
    rw [r.firstStrong.date]
    linarith [packet.full_budget_tail_gap r.jitter_bound m (by omega)]
  have markCovers := r.markOnly.mark_section_covers hb r.firstStrong.physical
    r.firstStrong.raw_valid r.firstStrong.main_slow (by linarith [r.firstStrong.charge.1])
    markRec (fun q => ⟨r.firstStrong.auxiliary 0 q,r.firstStrong.rest q⟩)
    (by rw [r.firstStrong.date]; exact r.firstStrong.raw_active) r.firstStrong.raw_other markGap g3
  have mixedRec : 27999 / 100000 ≤ r.secondStrong.final.x 0 .b ∧
      r.secondStrong.final.x 0 .b ≤ 28001 / 100000 := by
    rw [r.secondStrong.recovery]
    exact r.markOnly.recovery_band
  have mixedLog : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ r.secondStrong.final.x 0 (.z p) ∧
      r.secondStrong.final.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [r.secondStrong.gains,r.markOnly.gains,r.firstStrong.gains,r.prefix_gain]
    exact r.initial_log_gain
  have mixedGap : r.secondStrong.final.time + 37 / 10 ≤ packet.actual (m + 3) := by
    rw [r.secondStrong.date]
    linarith [packet.full_budget_tail_gap r.jitter_bound (m + 2) (by omega)]
  obtain ⟨mixedErrors,mixedMarks⟩ := r.mixed.section_covers hb r.secondStrong.physical
    r.secondStrong.raw_valid r.secondStrong.main_slow r.secondStrong.charge mixedRec
    (fun q => ⟨r.secondStrong.auxiliary 0 q,r.secondStrong.rest q⟩) mixedLog
    (by rw [r.secondStrong.date]; exact r.secondStrong.raw_active) r.secondStrong.raw_other mixedGap g5
  constructor
  · intro q
    obtain ⟨c0,_⟩ := r.firstSource.execution.error_cover_of_unchanged_gain hb g0 0 q (r.firstSource.gains q)
    obtain ⟨c1,_⟩ := r.learnedPrefix.execution.error_cover_of_unchanged_gain hb g1 0 q (r.learnedPrefix.gains q)
    obtain ⟨c2,_⟩ := r.firstStrong.execution.error_cover_of_zero_open hb g2 0 q (r.firstStrong.error_zero q)
    obtain ⟨c3,_⟩ := r.markOnly.execution.error_cover_of_zero_open hb g3 0 q (r.markOnly.error_zero q)
    obtain ⟨c4,_⟩ := r.secondStrong.execution.error_cover_of_zero_open hb g4 0 q (r.secondStrong.error_zero q)
    obtain ⟨c5⟩ := mixedErrors q
    obtain ⟨c6,_⟩ := r.high.execution.error_cover_of_unchanged_gain hb g6 0 q (r.high.gains 0 q)
    rw [r.reconstruct]
    exact ⟨c0.append (c1.append (c2.append (c3.append (c4.append (c5.append c6)))))⟩
  · intro q
    obtain ⟨c0,_⟩ := r.firstSource.execution.mark_cover_of_unchanged_recovery hb g0 0 q r.firstSource.recovery
    obtain ⟨c1,_⟩ := r.learnedPrefix.execution.mark_cover_of_unchanged_recovery hb g1 0 q r.learnedPrefix.recovery
    obtain ⟨c2,_⟩ := r.firstStrong.execution.mark_cover_of_zero_open hb g2 0 q (r.firstStrong.mark_zero q)
    obtain ⟨c3⟩ := markCovers q
    obtain ⟨c4,_⟩ := r.secondStrong.execution.mark_cover_of_zero_open hb g4 0 q (r.secondStrong.mark_zero q)
    obtain ⟨c5⟩ := mixedMarks q
    obtain ⟨c6,_⟩ := r.high.execution.mark_cover_of_unchanged_recovery hb g6 0 q (r.high.recovery 0)
    rw [r.reconstruct]
    exact ⟨c0.append (c1.append (c2.append (c3.append (c4.append (c5.append c6)))))⟩

/-- Only static initial headroom on unused ports is needed; the protocol's
numerical gain and recovery bounds open every gate on the actual trace. -/
theorem LocalCadenceBudgetReceiver.section_covers {θ ε s p m L J}
    {packet : KernelR.Chain.Packet m L J} {terminal}
    (r : LocalCadenceBudgetReceiver θ s p packet terminal)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (headroom : ∀ q, q ≠ p → s.x 0 (.z q) < Real.log ((θ 0).cap q)) :
    (∀ q, Nonempty (ErrorSectionCover 0 q r.execution)) ∧
    (∀ q, Nonempty (MarkSectionCover 0 q r.execution)) := by
  apply r.section_covers_of_gates hb
  apply r.execution.learningGatesOpen_of_final_headroom hb hf
  · intro i q
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    by_cases same : q = p
    · subst q
      rw [r.gain_target]
      exact lt_of_le_of_lt (by linarith [r.initial_log_gain.2]) (hb.low_gain_headroom 0 p)
    · rw [r.gain_other q same]
      exact headroom q same
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [r.recovery_gain]
    linarith [r.initial_prepared.recovery.2]

theorem LocalCadenceBudgetReceiver.sectionCovered {θ ε s p m L J}
    {packet : KernelR.Chain.Packet m L J} {terminal}
    (r : LocalCadenceBudgetReceiver θ s p packet terminal)
    (hb : PhysicalBox θ ε) (gates : LearningGatesOpen r.execution) :
    r.execution.SectionCovered := by
  obtain ⟨errors,marks⟩ := r.section_covers_of_gates hb gates
  constructor
  · intro i q
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact errors q
  · intro i q
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact marks q

/-- Exact local cadence counts follow after constructing the actual covers. -/
theorem LocalCadenceBudgetReceiver.section_counts {θ ε s p m L J}
    {packet : KernelR.Chain.Packet m L J} {terminal}
    (r : LocalCadenceBudgetReceiver θ s p packet terminal)
    (hb : PhysicalBox θ ε) (gates : LearningGatesOpen r.execution) :
    ∃ errors : ∀ i q, ErrorSectionCover i q r.execution,
    ∃ marks : ∀ i q, MarkSectionCover i q r.execution,
      (errors 0 p).count = 1 ∧ (∑ q : Port, (marks 0 q).count) = 2 := by
  classical
  have covered := r.sectionCovered hb gates
  let errors := fun i q => Classical.choice (covered.1 i q)
  let marks := fun i q => Classical.choice (covered.2 i q)
  obtain ⟨gain,recovery⟩ := r.execution.memory_of_section_covers errors marks
  refine ⟨errors,marks,?_,?_⟩
  · have count : ((errors 0 p).count : ℝ) = 1 := by
      have equation := gain 0 p
      rw [r.gain_target] at equation
      linarith
    exact_mod_cast count
  · have count : ((∑ q : Port, (marks 0 q).count : ℕ) : ℝ) = 2 := by
      have equation := recovery 0
      rw [r.recovery_gain] at equation
      linarith
    exact_mod_cast count

#print axioms CadenceMarkOnlyJitterNextSource.mark_section_covers
#print axioms LocalCadenceBudgetReceiver.section_covers
#print axioms LocalCadenceBudgetReceiver.section_counts

end KernelR.Hybrid
