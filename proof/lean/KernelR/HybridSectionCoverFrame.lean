import KernelR.HybridDoseCountingQueueTransport
import KernelR.HybridContactTransversalityFrame

/-! Queue-framed cover witnesses retain the actual contact certificate. -/
namespace KernelR.Hybrid

theorem Execution.RequeueCopy.appendFuture_contacts
    {n θ route route' s u} {future : List (Delivery n)}
    {e : @Execution n θ route s u}
    {e' : Execution θ route' ((appendPendingRequeue future).apply s)
      ((appendPendingRequeue future).apply u)}
    (copy : RequeueCopy (appendPendingRequeue future) e e') :
    e'.ContactsTransversal ↔ e.ContactsTransversal := by
  induction copy with
  | nil => rfl
  | cons step tail ih =>
    cases step with
    | flow f g path => exact ih
    | jump j j' =>
      have hj := j.contactTransversal_requeue (θ := θ) j'
      exact Iff.and hj.symm ih

end KernelR.Hybrid
