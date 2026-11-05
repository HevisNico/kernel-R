import KernelR.HybridDoseCountingTools
import KernelR.HybridSectionRuns

/-! Existence of actual complete section covers, with no prescribed counts. -/
namespace KernelR.Hybrid

def Execution.SectionCovered {n θ route s u} (e : @Execution n θ route s u) : Prop :=
  (∀ i p, Nonempty (ErrorSectionCover i p e)) ∧
    ∀ i p, Nonempty (MarkSectionCover i p e)

theorem Execution.SectionCovered.append {n θ route s v u}
    {e : @Execution n θ route s v} {f : Execution θ route v u}
    (left : e.SectionCovered) (right : f.SectionCovered) :
    (e.append f).SectionCovered := by
  constructor
  · intro i p
    obtain ⟨a⟩ := left.1 i p
    obtain ⟨b⟩ := right.1 i p
    exact ⟨a.append b⟩
  · intro i p
    obtain ⟨a⟩ := left.2 i p
    obtain ⟨b⟩ := right.2 i p
    exact ⟨a.append b⟩

/-- A preservation theorem for actual runs carries cover existence. -/
theorem Execution.SectionCovered.of_runs {n m θ θ' route route' s u s' u'}
    {e : @Execution n θ route s u} {f : @Execution m θ' route' s' u'}
    (source : Fin m → Fin n) (covered : e.SectionCovered)
    (transport : ∀ kind i p count,
      SectionRun kind (source i) p e false false count →
        SectionRun kind i p f false false count) : f.SectionCovered := by
  constructor
  · intro i p
    obtain ⟨cover⟩ := covered.1 (source i) p
    obtain ⟨mapped, _⟩ := error_section_run_iff.mp
      (transport .error i p cover.count cover.sectionRun)
    exact ⟨mapped⟩
  · intro i p
    obtain ⟨cover⟩ := covered.2 (source i) p
    obtain ⟨mapped, _⟩ := mark_section_run_iff.mp
      (transport .mark i p cover.count cover.sectionRun)
    exact ⟨mapped⟩

end KernelR.Hybrid
