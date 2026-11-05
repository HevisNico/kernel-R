import KernelR.HybridCadenceWeakSectionCovers
import KernelR.HybridMarkSectionCovers
import KernelR.HybridLocalCadenceTailK

/-! Covers of the actual mixed tail of the leaf. The second strong response,
high train and final wait have structurally inactive flows under open gates. -/
namespace KernelR.Hybrid

theorem CadenceMixedResponse.section_covers {θ ε s p}
    (c : CadenceMixedResponse θ s p) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (raw : RawValid s)
    (active : s.raw 0 p = some s.time)
    (gates : LearningGatesOpen c.execution) (q : Port) :
    Nonempty (ErrorSectionCover 0 q c.execution) ∧
      Nonempty (MarkSectionCover 0 q c.execution) := by
  have noArrival : NoArrivalAt c.execution 0 p := by simp [NoArrivalAt, c.deliveries]
  constructor
  · by_cases same : q = p
    · subst q
      exact c.pulse.mark_case.cycle.error_cover_of_ready_gates gates raw active
        noArrival c.pulse.error_ready
    · obtain ⟨cover, _⟩ := c.execution.error_cover_of_unchanged_gain box gates 0 q (c.gain_other q same)
      exact ⟨cover⟩
  · by_cases same : q = p
    · subst q
      obtain ⟨cover, _⟩ := c.pulse.mark_case.mark_section_cover box physical raw active noArrival
        (by rw [← c.recovery_gain]; linarith [c.recovery_band.2])
      exact ⟨cover⟩
    · obtain ⟨cover, _⟩ := c.execution.mark_cover_of_zero_open box gates 0 q
        (c.pulse.mark_case.mark_other q same)
      exact ⟨cover⟩

theorem CadenceMixedNextSource.section_covers {θ ε s p later}
    {mixed : CadenceMixedResponse θ s p}
    (c : CadenceMixedNextSource mixed later) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (raw : RawValid s)
    (active : s.raw 0 p = some s.time)
    (gates : LearningGatesOpen c.execution) (q : Port) :
    Nonempty (ErrorSectionCover 0 q c.execution) ∧
      Nonempty (MarkSectionCover 0 q c.execution) := by
  rw [c.reconstruct, learningGatesOpen_append] at gates
  obtain ⟨⟨error⟩, ⟨mark⟩⟩ := mixed.section_covers box physical raw active gates.1 q
  rw [c.reconstruct]
  exact ⟨⟨error.append (.inactive (.jump c.arrival) (.nil _) trivial (.nil _))⟩,
    ⟨mark.append (.inactive (.jump c.arrival) (.nil _) trivial (.nil _))⟩⟩

theorem LocalCadenceTailK.section_covers {θ ε source p n terminal}
    (c : LocalCadenceTailK θ source p n terminal) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen c.execution) (q : Port) :
    Nonempty (ErrorSectionCover 0 q c.execution) ∧
      Nonempty (MarkSectionCover 0 q c.execution) := by
  rw [c.reconstruct, learningGatesOpen_append, learningGatesOpen_append,
    learningGatesOpen_append] at gates
  obtain ⟨e₁, _⟩ := c.second.execution.error_cover_of_unchanged_gain box gates.1 0 q (c.second.gains 0 q)
  obtain ⟨m₁, _⟩ := c.second.execution.mark_cover_of_unchanged_recovery box gates.1 0 q (c.second.recovery 0)
  obtain ⟨⟨e₂⟩, ⟨m₂⟩⟩ := c.sourceHigh.section_covers box c.second.physical
    c.second.raw_valid c.second.raw_active gates.2.1 q
  obtain ⟨e₃, _⟩ := c.high.execution.error_cover_of_unchanged_gain box gates.2.2.1 0 q (c.high.gains 0 q)
  obtain ⟨m₃, _⟩ := c.high.execution.mark_cover_of_unchanged_recovery box gates.2.2.1 0 q (c.high.recovery 0)
  obtain ⟨e₄, _⟩ := c.wait.error_cover_of_unchanged_gain box gates.2.2.2 0 q
    (by rw [c.final_state]; rfl)
  obtain ⟨m₄, _⟩ := c.wait.mark_cover_of_unchanged_recovery box gates.2.2.2 0 q
    (by rw [c.final_state]; rfl)
  rw [c.reconstruct]
  exact ⟨⟨e₁.append (e₂.append (e₃.append e₄))⟩, ⟨m₁.append (m₂.append (m₃.append m₄))⟩⟩

#print axioms LocalCadenceTailK.section_covers
end KernelR.Hybrid
