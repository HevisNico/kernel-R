import KernelR.HybridContactTransversality
import KernelR.HybridObservationalTransport

/-! Contact transversality depends on the physical source and the mode
change, so queue re-presentations preserve it. -/
namespace KernelR.Hybrid

private theorem Jump.contactTransversal_main_departure {n θ route s u}
    (jump : @Jump n route s u) (positive : jump.ContactTransversal θ)
    (i : Fin n) (ready : s.main i = .ready) (changed : u.main i ≠ s.main i) :
    0 < field θ s s.x s.time i .q := by
  cases jump <;> simp_all [Jump.ContactTransversal, setMain, setAux, setRaw, Function.update_apply]

private theorem Jump.contactTransversal_aux_departure {n θ route s u}
    (jump : @Jump n route s u) (positive : jump.ContactTransversal θ)
    (i : Fin n) (p : Port) (ready : s.aux i p = .ready)
    (changed : u.aux i p ≠ s.aux i p) :
    0 < field θ s s.x s.time i (.m p) := by
  cases jump <;> simp_all [Jump.ContactTransversal, setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

/-- A jump is transverse precisely at its departures from READY modes. -/
theorem Jump.contactTransversal_iff_departures {n θ route s u}
    (jump : @Jump n route s u) :
    jump.ContactTransversal θ ↔
      (∀ i, s.main i = .ready → u.main i ≠ s.main i →
        0 < field θ s s.x s.time i .q) ∧
      (∀ i p, s.aux i p = .ready → u.aux i p ≠ s.aux i p →
        0 < field θ s s.x s.time i (.m p)) := by
  constructor
  · intro positive
    exact ⟨jump.contactTransversal_main_departure positive,
      jump.contactTransversal_aux_departure positive⟩
  · rintro ⟨main, aux⟩
    cases jump with
    | fire i mode guard =>
      exact main i mode (by simp [setMain, mode])
    | mark i p mode guard =>
      exact aux i p mode (by simp [setAux, mode])
    | _ => trivial

/-- Source and endpoint observations retain the exact READY departures and
the differential field. The two routed queues may have different presentations. -/
theorem Jump.contactTransversal_of_observational {n θ route route' s u s' u'}
    (jump : @Jump n route s u) (jump' : @Jump n route' s' u')
    (source : s.ObservationalEq s') (target : u.ObservationalEq u') :
    jump.ContactTransversal θ ↔ jump'.ContactTransversal θ := by
  rw [jump.contactTransversal_iff_departures, jump'.contactTransversal_iff_departures]
  rw [← source.field]
  simp only [← source.main, ← target.main, ← source.aux, ← target.aux,
    ← source.values, ← source.time]

/-- Changing only the two pending queues preserves the contact field and
both READY departures, independently of routed-token presentation. -/
theorem Jump.contactTransversal_requeue {n θ route route' s u Q R}
    (jump : @Jump n route s u)
    (jump' : @Jump n route' {s with pending := Q} {u with pending := R}) :
    jump.ContactTransversal θ ↔ jump'.ContactTransversal θ := by
  rw [jump.contactTransversal_iff_departures, jump'.contactTransversal_iff_departures]
  rfl

end KernelR.Hybrid
