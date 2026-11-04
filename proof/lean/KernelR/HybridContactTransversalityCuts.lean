import KernelR.HybridContactTransversality
import KernelR.HybridFlowCuts

/-! Cutting an actual execution retains its transverse physical jumps. -/
namespace KernelR.Hybrid

theorem Execution.IsPrefix.contacts_transversal {n θ route s u v}
    {execution : @Execution n θ route s u} {cutExecution : Execution θ route s v}
    (cut : execution.IsPrefix cutExecution) (positive : execution.ContactsTransversal) :
    cutExecution.ContactsTransversal := by
  induction cut with
  | nil => trivial
  | flowCut => trivial
  | step move rest cut hp ih =>
    cases move with
    | flow flow => exact ih positive
    | jump jump => exact ⟨positive.1, ih positive.2⟩

end KernelR.Hybrid
