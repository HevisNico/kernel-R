import KernelR.HybridDoseCountingTransport
import KernelR.HybridSectionRuns
import KernelR.HybridContactTransversalityTransport

/-! A router change retains complete-section automata on the exact actual
moves. Neither the physical paths nor the mode-changing events are replaced. -/
namespace KernelR.Hybrid

theorem SectionStep.routerCopy {n θ route route' s u kind i p first last count}
    {move : @Move n θ route s u} {mapped : Move θ route' s u}
    (step : SectionStep kind i p move first last count)
    (copy : Move.RouterCopy move mapped) : SectionStep kind i p mapped first last count := by
  cases copy with
  | flow f =>
    cases step with
    | inactive _ h => exact .inactive (.flow f) h
    | flow _ exposed => exact .flow f exposed
  | jump j j' =>
    cases step with
    | inactive _ h =>
      apply SectionStep.inactive
      cases kind <;> trivial
    | enter _ before after => exact .enter j' before after
    | jump _ before after => exact .jump j' before after
    | exit _ before after => exact .exit j' before after

theorem SectionRun.routerCopy {n θ route s u kind i p first last count}
    {e : @Execution n θ route s u} (run : SectionRun kind i p e first last count)
    {route' : Router n} {mapped : Execution θ route' s u}
    (copy : Execution.RouterCopy e mapped) : SectionRun kind i p mapped first last count := by
  induction run generalizing route' with
  | nil s active valid =>
    cases copy
    exact .nil s active valid
  | cons step tail ih =>
    cases copy with
    | cons stepCopy tailCopy => exact .cons (step.routerCopy stepCopy) (ih tailCopy)

theorem Execution.RouterCopy.contactsTransversal {n θ route route' s u}
    {e : @Execution n θ route s u} {mapped : Execution θ route' s u}
    (copy : RouterCopy e mapped) : mapped.ContactsTransversal ↔ e.ContactsTransversal := by
  induction copy with
  | nil => rfl
  | cons step tail ih =>
    cases step with
    | flow f => exact ih
    | jump j j' =>
      have hc : j'.ContactTransversal θ ↔ j.ContactTransversal θ := by
        rw [j'.contactTransversal_iff_departures, j.contactTransversal_iff_departures]
      exact and_congr hc ih

end KernelR.Hybrid
