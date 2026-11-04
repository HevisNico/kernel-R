import KernelR.HybridContactTransversalityTransport
import KernelR.HybridCausalHeadJump

/-! Transversality is local to the firing or marking cell. A causal weave
retains that cell's entire physical state while changing only its queue. -/
namespace KernelR.Hybrid

theorem Jump.contactTransversal_main {n route s u} (jump : @Jump n route s u)
    {θ} (positive : jump.ContactTransversal θ) (i : Fin n)
    (before : s.main i = .ready) (after : u.main i = .fast) :
    0 < field θ s s.x s.time i .q := by
  exact (jump.contactTransversal_iff_departures.mp positive).1 i before
    (by
      rw [before, after]
      decide)

theorem Jump.contactTransversal_aux {n route s u} (jump : @Jump n route s u)
    {θ} (positive : jump.ContactTransversal θ) (i : Fin n) (p : Port)
    (before : s.aux i p = .ready) (after : u.aux i p = .mark) :
    0 < field θ s s.x s.time i (.m p) := by
  exact (jump.contactTransversal_iff_departures.mp positive).2 i p before
    (by
      rw [before, after]
      decide)

theorem Jump.contactTransversal_of_departures {n route s u}
    (jump : @Jump n route s u) {θ}
    (main : ∀ i, s.main i = .ready → u.main i = .fast →
      0 < field θ s s.x s.time i .q)
    (aux : ∀ i p, s.aux i p = .ready → u.aux i p = .mark →
      0 < field θ s s.x s.time i (.m p)) : jump.ContactTransversal θ := by
  cases jump with
  | fire i hm hq => exact main i hm (by simp [setMain])
  | mark i p hm hq => exact aux i p hm (by simp [setAux])
  | _ => trivial

theorem field_prependQueued_tail {n θ θH} (s : Snapshot n) (a : Snapshot 1)
    (Q : List (Delivery (n+1))) (i : Fin n) (c : Coord) (t : ℝ) :
    field (prependParameters θH θ) (s.prependQueued a Q)
      (s.prependQueued a Q).x t i.succ c = field θ s s.x t i c := by
  cases c <;> rfl

theorem field_prependQueued_head {n θ θH} (s : Snapshot n) (a : Snapshot 1)
    (Q : List (Delivery (n+1))) (c : Coord) (t : ℝ) :
    field (prependParameters θH θ) (s.prependQueued a Q)
      (s.prependQueued a Q).x t 0 c = field θH a a.x t 0 c := by
  cases c <;> rfl

theorem Jump.prependQueued_tail_contactTransversal {n θ θH route s u}
    (jump : @Jump n route s u) (positive : jump.ContactTransversal θ)
    (a : Snapshot 1) (Q Q' : List (Delivery (n+1))) (contacts : HeadRoutes n)
    (global : Jump (prependRouted route contacts)
      (s.prependQueued a Q) (u.prependQueued a Q')) :
    global.ContactTransversal (prependParameters θH θ) := by
  apply global.contactTransversal_of_departures
  · intro i before after
    cases i using Fin.cases with
    | zero =>
      have conflict : MainMode.ready = .fast := before.symm.trans after
      cases conflict
    | succ i =>
      rw [field_prependQueued_tail]
      exact jump.contactTransversal_main positive i before after
  · intro i p before after
    cases i using Fin.cases with
    | zero =>
      have conflict : AuxMode.ready = .mark := before.symm.trans after
      cases conflict
    | succ i =>
      rw [field_prependQueued_tail]
      exact jump.contactTransversal_aux positive i p before after

theorem Jump.prependQueued_head_contactTransversal {n θ θH route a b}
    (jump : @Jump 1 (fun _ _ => []) a b) (positive : jump.ContactTransversal θH)
    (s : Snapshot n) (clock : s.time = a.time)
    (Q Q' : List (Delivery (n+1))) (contacts : HeadRoutes n)
    (global : Jump (prependRouted route contacts)
      (s.prependQueued a Q) (s.prependQueued b Q')) :
    global.ContactTransversal (prependParameters θH θ) := by
  apply global.contactTransversal_of_departures
  · intro i before after
    cases i using Fin.cases with
    | zero =>
      rw [field_prependQueued_head]
      change 0 < field θH a a.x s.time 0 .q
      rw [clock]
      exact jump.contactTransversal_main positive 0 before after
    | succ i =>
      have conflict : MainMode.ready = .fast := before.symm.trans after
      cases conflict
  · intro i p before after
    cases i using Fin.cases with
    | zero =>
      rw [field_prependQueued_head]
      change 0 < field θH a a.x s.time 0 (.m p)
      rw [clock]
      exact jump.contactTransversal_aux positive 0 p before after
    | succ i =>
      have conflict : AuxMode.ready = .mark := before.symm.trans after
      cases conflict

end KernelR.Hybrid
