import KernelR.HybridSectionRuns

/-! Complete sections on traces whose learning mode has uniform exposure.
The automaton follows real auxiliary entries and exits; no dose identity is
used to establish that a section exists. -/
namespace KernelR.Hybrid
attribute [local instance] Classical.propDecidable

theorem Execution.protected_flows_of_mainFlows {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (mode : MainMode)
    (different : mode ≠ .ready) (modes : e.MainFlows i mode) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) => v.main i ≠ .ready) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | jump j => exact ih modes
    | flow f => exact ⟨fun h => different (modes.1.symm.trans h), ih modes.2⟩

theorem LearningSection.uniform_run {n θ route s u} (kind : LearningSection)
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (exposed : e.AllFlows (fun {v w} (f : Flow θ v w) =>
      v.aux i p = kind.mode → kind.Open f i p)) :
    ∃ count, SectionRun kind i p e (decide (s.aux i p = kind.mode))
      (decide (u.aux i p = kind.mode)) count := by
  induction e with
  | nil s =>
    exact ⟨0, .nil s _ (by simp [LearningSection.Valid])⟩
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      obtain ⟨k, tail⟩ := ih exposed.2
      have same : v.aux i p = s.aux i p := congrFun (congrFun f.aux_fixed i) p
      by_cases active : s.aux i p = kind.mode
      · have step : SectionStep (route := route) kind i p (.flow f) true true 0 := .flow f (exposed.1 active)
        refine ⟨k, ?_⟩
        simpa [active, same] using SectionRun.cons step (by simpa [same, active] using tail)
      · have inactive : kind.Inactive (Move.flow (route := route) f) i p := by
          cases kind <;> exact Or.inl active
        have step : SectionStep (route := route) kind i p (.flow f) false false 0 := .inactive _ inactive
        refine ⟨k, ?_⟩
        simpa [active, same] using SectionRun.cons step (by simpa [same, active] using tail)
    | jump j =>
      obtain ⟨k, tail⟩ := ih exposed
      by_cases before : s.aux i p = kind.mode <;>
        by_cases after : v.aux i p = kind.mode
      · exact ⟨k, by simpa [before, after] using
          SectionRun.cons (SectionStep.jump j before after) (by simpa [after] using tail)⟩
      · exact ⟨1+k, by simpa [before, after] using
          SectionRun.cons (SectionStep.exit j before after) (by simpa [after] using tail)⟩
      · exact ⟨k, by simpa [before, after] using
          SectionRun.cons (SectionStep.enter j before after) (by simpa [after] using tail)⟩
      · have inactive : kind.Inactive (Move.jump (θ := θ) j) i p := by cases kind <;> trivial
        exact ⟨k, by simpa [before, after] using
          SectionRun.cons (SectionStep.inactive _ inactive) (by simpa [after] using tail)⟩

theorem Execution.error_cover_of_uniform_ready {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (gates : LearningGatesOpen e) (ready : e.MainFlows i .ready)
    (initial : s.aux i p ≠ .error) (final : u.aux i p ≠ .error) :
    Nonempty (ErrorSectionCover i p e) := by
  have exposed : e.AllFlows (fun {v w} (f : Flow θ v w) =>
      v.aux i p = LearningSection.error.mode → LearningSection.error.Open f i p) := by
    clear initial final
    induction e with
    | nil => trivial
    | cons move rest ih =>
      cases move with
      | jump j => exact ih gates ready
      | flow f =>
        refine ⟨fun h => ⟨h, ready.1, ?_⟩, ih gates.2 ready.2⟩
        intro t ht
        exact ⟨(gates.1 t ht i).1, (gates.1 t ht i).2.2 p⟩
  obtain ⟨count, run⟩ := LearningSection.error.uniform_run e i p exposed
  have closed : SectionRun .error i p e false false count := by
    simpa [LearningSection.mode, initial, final] using run
  obtain ⟨cover, _⟩ := error_section_run_iff.mp closed
  exact ⟨cover⟩

theorem Execution.mark_cover_of_uniform_protected {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (gates : LearningGatesOpen e)
    (protectedModes : e.AllFlows (fun {v w} (_ : Flow θ v w) => v.main i ≠ .ready))
    (initial : s.aux i p ≠ .mark) (final : u.aux i p ≠ .mark) :
    Nonempty (MarkSectionCover i p e) := by
  have exposed : e.AllFlows (fun {v w} (f : Flow θ v w) =>
      v.aux i p = LearningSection.mark.mode → LearningSection.mark.Open f i p) := by
    clear initial final
    induction e with
    | nil => trivial
    | cons move rest ih =>
      cases move with
      | jump j => exact ih gates protectedModes
      | flow f =>
        refine ⟨fun h => ⟨h, protectedModes.1, ?_⟩, ih gates.2 protectedModes.2⟩
        intro t ht
        exact ⟨(gates.1 t ht i).1, (gates.1 t ht i).2.1⟩
  obtain ⟨count, run⟩ := LearningSection.mark.uniform_run e i p exposed
  have closed : SectionRun .mark i p e false false count := by
    simpa [LearningSection.mode, initial, final] using run
  obtain ⟨cover, _⟩ := mark_section_run_iff.mp closed
  exact ⟨cover⟩

#print axioms Execution.error_cover_of_uniform_ready
#print axioms Execution.mark_cover_of_uniform_protected

end KernelR.Hybrid
