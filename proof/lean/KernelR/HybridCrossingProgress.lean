import KernelR.HybridCrossingCorrespondence
import KernelR.HybridChainProgress
import KernelR.HybridContactTransversalityCuts

/-! Finite crossing progress at every horizon. Earlier references are actual
cuts of the constructed protocol; later references append its source-free
quiet flow. Exact weak-prefix refinement therefore has no horizon restriction
relative to the protocol's original terminal date. -/
namespace KernelR.Hybrid
namespace ConstructedBirthCadenceChain
variable {n θ bornCells K sigma centre delay T ε}
  (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)

/-- Every horizon at or after birth has a complete transverse reference,
constructed from the original protocol and its quiet continuation. -/
theorem transverse_horizon (H : ℝ)
    (afterBirth : (familyPreparationBornSource bornCells K).time ≤ H) :
    ∃ v, ∃ reference : Execution θ chain.router (familyPreparationBornSource bornCells K) v,
      CompleteThrough reference H ∧ reference.ContactsTransversal := by
  by_cases earlier : H < T
  · obtain ⟨v, cut, isCut, complete⟩ :=
      chain.execution.complete_prefix_at H afterBirth (by rw [chain.date]; exact earlier)
    exact ⟨v, cut, complete, isCut.contacts_transversal chain.contacts_transversal⟩
  · by_cases equal : H = T
    · subst H
      exact ⟨chain.final, chain.execution, chain.complete, chain.contacts_transversal⟩
    · have later : T < H := lt_of_le_of_ne (le_of_not_gt earlier) (Ne.symm equal)
      have mainReady : ∀ i, chain.final.main i = .ready := fun i => (chain.ready i).ready
      have auxReady : ∀ i p, chain.final.aux i p = .ready :=
        fun i p => ((chain.ready i).auxiliary p).1
      have chargeBelow : ∀ i, chain.final.x i .q < 1 := by
        intro i; rw [chain.charge i]; norm_num
      have auxBelow : ∀ i p, chain.final.x i (.m p) < 1 := by
        intro i p
        have bound := ((chain.ready i).auxiliary p).2.2
        linarith
      have future : ∀ d ∈ chain.final.pending, H < d.due := by
        intro d member
        rw [chain.pending] at member
        simp at member
      have afterFinal : chain.final.time < H := by rw [chain.date]; exact later
      let waiting : Flow θ chain.final (quietAt chain.final H) :=
        quietFlow chain.final afterFinal mainReady auxReady chain.raw_none chargeBelow auxBelow
          (fun d member => (future d member).le)
      let quiet : Execution θ chain.router chain.final (quietAt chain.final H) :=
        .cons (.flow waiting) (.nil _)
      have completeQuiet : CompleteThrough quiet H := by
        refine ⟨rfl, ?_, future⟩
        intro u
        apply ready_no_jump (quietAt chain.final H) mainReady auxReady chain.raw_none
        · intro i
          exact relax_lt (by norm_num) afterFinal.le (chargeBelow i) (by norm_num)
        · intro i p
          exact relax_lt (by norm_num) afterFinal.le (auxBelow i p) (by norm_num)
        · exact future
      refine ⟨quietAt chain.final H, chain.execution.append quiet, completeQuiet, ?_⟩
      exact (Execution.contactsTransversal_append chain.execution quiet).mpr
        ⟨chain.contacts_transversal, trivial⟩

/-- Every finite weak prefix, including one ending after the protocol's
terminal date, has exactly the same paths and jumps as a native execution. -/
theorem weak_prefix_native (box : PhysicalBox θ ε) {u}
    (candidate : WeakExecution θ chain.router (familyPreparationBornSource bornCells K) u) :
    ∃ native : Execution θ chain.router (familyPreparationBornSource bornCells K) u,
      native.toWeak = candidate := by
  obtain ⟨v, reference, complete, positive⟩ :=
    chain.transverse_horizon u.time candidate.time_monotone
  exact candidate.toNative_of_transverse_completion reference chain.strict_causal_router box
    (chain.source_birth.physical_invariant box) complete positive le_rfl

/-- A finite weak prefix can be continued from its actual endpoint to any
chosen later horizon by a transverse native tail. -/
theorem extend_weak_execution (box : PhysicalBox θ ε) {u}
    (candidate : WeakExecution θ chain.router (familyPreparationBornSource bornCells K) u)
    (H : ℝ) (later : u.time ≤ H) :
    ∃ v, ∃ tail : Execution θ chain.router u v,
      CompleteThrough tail H ∧ tail.ContactsTransversal := by
  obtain ⟨v, reference, complete, positive⟩ :=
    chain.transverse_horizon H (candidate.time_monotone.trans later)
  exact candidate.continue_to_transverse_complete reference box
    (chain.source_birth.physical_invariant box) complete positive later

/-- Extend any finite model history to a chosen later horizon while retaining
its exact historical prefix. The appended native tail has genuine geometric
crossings relative to that same executed history. -/
theorem extend_crossing_execution (box : PhysicalBox θ ε) {u}
    (candidate : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) u)
    (H : ℝ) (later : u.time ≤ H) :
    ∃ v, ∃ tail : Execution θ chain.router u v,
      ∃ extended : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) v,
        extended.execution = candidate.execution.append tail.toWeak ∧
        CrossingCompleteThrough extended H ∧ tail.ContactsTransversal := by
  obtain ⟨nativePast, same⟩ := chain.weak_prefix_native box candidate.execution
  obtain ⟨v, tail, complete, positive⟩ :=
    chain.extend_weak_execution box candidate.execution H later
  have futureCrossings : tail.toWeak.CrossingFrom candidate.execution := by
    rw [← same]
    exact tail.toWeak_crossingFrom nativePast chain.source_birth.initiallyBelowReady box
      (chain.source_birth.physical_invariant box) positive
  let extended : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) v := {
    execution := candidate.execution.append tail.toWeak
    crossings := (WeakExecution.crossingFrom_append candidate.execution tail.toWeak (.nil _)).mpr
      ⟨candidate.crossings, futureCrossings⟩
  }
  refine ⟨v, tail, extended, rfl, ?_, positive⟩
  exact ⟨complete.1, fun w jump => False.elim ((complete.2.1 w).false jump), complete.2.2⟩

/-- Every finite crossing history has a genuine extension by one unit of
model time; its existing paths and events remain an exact prefix. -/
theorem crossing_progress_one_time_unit (box : PhysicalBox θ ε) {u}
    (candidate : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) u) :
    ∃ v, ∃ tail : Execution θ chain.router u v,
      ∃ extended : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) v,
        extended.execution = candidate.execution.append tail.toWeak ∧
        v.time = u.time + 1 ∧ CrossingCompleteThrough extended (u.time + 1) := by
  obtain ⟨v, tail, extended, retained, complete, _⟩ :=
    chain.extend_crossing_execution box candidate (u.time + 1) (by linarith)
  exact ⟨v, tail, extended, retained, complete.1, complete⟩

end ConstructedBirthCadenceChain

#print axioms ConstructedBirthCadenceChain.transverse_horizon
#print axioms ConstructedBirthCadenceChain.weak_prefix_native
#print axioms ConstructedBirthCadenceChain.extend_weak_execution
#print axioms ConstructedBirthCadenceChain.extend_crossing_execution
#print axioms ConstructedBirthCadenceChain.crossing_progress_one_time_unit

end KernelR.Hybrid
