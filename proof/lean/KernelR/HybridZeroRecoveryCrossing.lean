import KernelR.HybridZeroRecovery
import KernelR.HybridCrossingExecution

/-! The zero-recovery obstruction directly in the weak integral envelope and
the model's upward-crossing semantics. No weak-to-native conversion, chain
protocol, transverse-contact theorem or complete reference run is assumed. -/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- The only missing learning mechanism is MARK on this cell's actual flow
pieces. Other cells, input deliveries and non-MARK sensor modes are unrestricted. -/
def WeakExecution.NoMarkFlows {n θ route s u} (i : Fin n) :
    @WeakExecution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow _) rest => (∀ p, s.aux i p ≠ .mark) ∧ rest.NoMarkFlows i
  | .cons (.jump _) rest => rest.NoMarkFlows i

/-- The actual weak-flow path remains at the unrecovering values. -/
def WeakFlow.ZeroRecoveryLockedPaths {n θ s u} (f : @WeakFlow n θ s u) (i : Fin n) : Prop :=
  ∀ t ∈ Icc s.time u.time, f.path t i .q = 1 / 4 ∧ f.path t i .b = 0

/-- A conclusion recording the locked state at every discrete snapshot and
the fixed coordinates throughout every intervening weak integral flow. -/
def WeakExecution.ZeroRecoveryLocked {n θ route s u} (i : Fin n) :
    @WeakExecution n θ route s u → Prop
  | .nil _ => s.main i = .slow ∧ s.x i .q = 1 / 4 ∧ s.x i .b = 0
  | .cons (.flow f) rest =>
      (s.main i = .slow ∧ s.x i .q = 1 / 4 ∧ s.x i .b = 0) ∧
      f.ZeroRecoveryLockedPaths i ∧
      rest.ZeroRecoveryLocked i
  | .cons (.jump _) rest =>
      (s.main i = .slow ∧ s.x i .q = 1 / 4 ∧ s.x i .b = 0) ∧ rest.ZeroRecoveryLocked i

theorem WeakFlow.recovery_without_mark {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (hmark : ∀ p, s.aux i p ≠ .mark) :
    ∀ t ∈ Icc s.time u.time, f.path t i .b = s.x i .b := by
  have hg (v : ℝ) : field θ s (f.path v) v i .b = 0 := by
    simp only [field]
    apply Finset.sum_eq_zero
    intro p _
    simp [markAct,hmark p]
  intro t ht
  simpa only [hg,intervalIntegral.integral_zero,add_zero] using f.integral_eq t ht i .b

theorem WeakFlow.zero_recovery_locked_paths {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4)
    (hb : s.x i .b = 0) (hmark : ∀ p, s.aux i p ≠ .mark) :
    ∀ t ∈ Icc s.time u.time, f.path t i .q = 1 / 4 ∧ f.path t i .b = 0 := by
  have hz : ∀ t ∈ Icc s.time u.time, f.path t i .b = 0 := by
    intro t ht
    rw [f.recovery_without_mark i hmark t ht,hb]
  intro t ht
  have hi : (∫ v in s.time..t, field θ s (f.path v) v i .q) = 0 := by
    calc
      _ = ∫ _v in s.time..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hv' : v ∈ Icc s.time u.time := by
          rw [uIcc_of_le ht.1] at hv
          exact ⟨hv.1,hv.2.trans ht.2⟩
        simp only [field,hm,hz v hv',neg_zero,zero_mul]
      _ = 0 := by simp
  refine ⟨?_,hz t ht⟩
  simpa only [hi,add_zero,hq] using f.integral_eq t ht i .q

/-- At the unchanged SLOW charge a jump cannot be the reopening transition. -/
theorem Jump.slow_stays_at_quarter {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) :
    u.main i = .slow := by
  by_contra h
  have hg := j.slow_departure_guard i hm h
  linarith

/-- A direct induction over the weak execution proves the obstruction even
when unrelated READY coordinates are allowed to touch their thresholds. -/
theorem WeakExecution.zero_recovery_lock {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n)
    (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b = 0)
    (hmark : e.NoMarkFlows i) : e.ZeroRecoveryLocked i ∧ e.emissionTimes i = [] := by
  induction e with
  | nil => exact ⟨⟨hm,hq,hb⟩,rfl⟩
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      have hp := f.zero_recovery_locked_paths i hm hq hb hmark.1
      have hv := hp v.time ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hv
      have hrest := ih (by simpa only [f.main_fixed] using hm) hv.1 hv.2 hmark.2
      refine ⟨⟨⟨hm,hq,hb⟩,hp,hrest.1⟩,?_⟩
      simpa only [WeakExecution.emissionTimes,WeakExecution.ledger,WeakMove.ledger,
        WeakFlow.ledger,Ledger.add,List.nil_append] using hrest.2
    | jump j =>
      have hrest := ih (j.slow_stays_at_quarter i hm hq)
        (by simpa only [j.physical_continuous] using hq)
        (by simpa only [j.physical_continuous] using hb) hmark
      refine ⟨⟨⟨hm,hq,hb⟩,hrest.1⟩,?_⟩
      have hj := j.no_emissions_if_not_ready i (by rw [hm]; decide)
      simpa only [WeakExecution.emissionTimes,WeakExecution.ledger,WeakMove.ledger,
        Ledger.add,List.filter_append,hj,List.nil_append] using hrest.2

/-- The upward-crossing model inherits the directly proved weak-execution
obstruction, for any router and network size, with no protocol restriction. -/
theorem CrossingExecution.zero_recovery_lock {n θ route s u}
    (e : @CrossingExecution n θ route s u) (i : Fin n)
    (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b = 0)
    (hmark : e.execution.NoMarkFlows i) :
    e.execution.ZeroRecoveryLocked i ∧ e.execution.emissionTimes i = [] :=
  e.execution.zero_recovery_lock i hm hq hb hmark

/-- Arbitrarily long complete crossing executions witness the locked regime,
independently of the native-to-crossing protocol correspondence. -/
theorem zeroRecoveryIdle_crossing_complete {n} (θ : Fin n → Parameters) (route : Router n)
    (start finish : ℝ) (ht : start < finish) :
    ∃ e : CrossingExecution θ route (zeroRecoveryIdle n start) (zeroRecoveryIdle n finish),
      CrossingCompleteThrough e finish ∧ ∀ i, e.execution.emissionTimes i = [] := by
  let e : CrossingExecution θ route (zeroRecoveryIdle n start) (zeroRecoveryIdle n finish) :=
    ⟨.cons (.flow (zeroRecoveryIdleFlow θ start finish ht).toWeak) (.nil _),trivial⟩
  refine ⟨e,⟨rfl,?_,?_⟩,?_⟩
  · intro v jump
    exact False.elim ((zeroRecoveryIdle_no_jump route finish v).false jump)
  · intro d hd; simp [zeroRecoveryIdle] at hd
  · intro i; rfl

#print axioms WeakExecution.zero_recovery_lock
#print axioms CrossingExecution.zero_recovery_lock
#print axioms zeroRecoveryIdle_crossing_complete

end KernelR.Hybrid
