import KernelR.HybridSlowMarkReturn

/-!
# Zero recovery and the role of protected learning

These statements concern actual native integral executions, with arbitrary
networks and routers. A SLOW cell with zero recovery cannot reopen while no
MARK phase acts on it. The no-MARK condition can be derived from quiet READY
sensors and absence of actual input deliveries. It cannot be inferred merely
from zero initial recovery or from the absence of new pulses.

Zero recovery is allowed by `PhysicalInvariant`, but not by `BirthState`.
No existence or infinite-progress conclusion is hidden in the finite-trace
statements; a separate constant physical flow witnesses non-vacuity.
-/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- Zero recovery makes the actual SLOW charge constant throughout a flow. -/
theorem Flow.slow_charge_constant_of_zero_recovery {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (hm : s.main i = .slow)
    (hb : ∀ t ∈ Icc s.time u.time, f.path t i .b = 0) :
    ∀ t ∈ Icc s.time u.time, f.path t i .q = s.x i .q := by
  intro t ht
  have hi : (∫ v in s.time..t, f.path v i .b) = 0 := by
    calc
      _ = ∫ _v in s.time..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        exact hb v (by
          rw [uIcc_of_le ht.1] at hv
          exact ⟨hv.1,hv.2.trans ht.2⟩)
      _ = 0 := by simp
  simpa only [hi, neg_zero, Real.exp_zero, mul_one] using f.slow_solution i hm t ht

/-- The zero-recovery obstruction is proved from an actual first mode
departure, rather than assumed as a protected-mode premise. -/
theorem Execution.slow_forever_of_zero_recovery {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n)
    (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b = 0)
    (hmark : e.NoMarkFlows i) : e.AllStates (fun v => v.main i = .slow) := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hm with h |
      ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hsegment : segment.NoMarkFlows i := by
      unfold Execution.NoMarkFlows at hmark ⊢
      rw [he,Execution.allFlows_append] at hmark
      exact hmark.1
    have hconstant := (segment.recovery_without_mark i hsegment).2
    have hacc := segment.accumulatedRecovery_of_constant i (s.x i .b) hconstant
    have hsol := segment.slow_solution i (segment.allStates_main_flows i .slow hstates)
    rw [hacc,hb,hq,zero_mul,neg_zero,Real.exp_zero,mul_one] at hsol
    have hguard := exit.slow_departure_guard i hv hw
    linarith

/-- At every discrete snapshot of such an execution both continuous
coordinates remain fixed; no claim about the rest of the network is made. -/
theorem Execution.zero_recovery_locked_states {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n)
    (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b = 0)
    (hmark : e.NoMarkFlows i) :
    e.AllStates (fun v => v.main i = .slow ∧ v.x i .q = 1 / 4 ∧ v.x i .b = 0) := by
  have hslow := e.slow_forever_of_zero_recovery i hm hq hb hmark
  induction e with
  | nil => exact ⟨hm,hq,hb⟩
  | @cons s v u move rest ih =>
    refine ⟨⟨hm,hq,hb⟩,?_⟩
    cases move with
    | flow f =>
      have hr := f.recovery_without_mark i hmark.1
      have hz : ∀ t ∈ Icc s.time v.time, f.path t i .b = 0 := by
        intro t ht; rw [hr t ht,hb]
      have hqv := f.slow_charge_constant_of_zero_recovery i hm hz v.time
        ⟨f.positive.le,le_rfl⟩
      have hbv := hz v.time ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hqv hbv
      exact ih (rest.allStates_initial hslow.2) (hqv.trans hq) hbv hmark.2 hslow.2
    | jump j =>
      exact ih (rest.allStates_initial hslow.2)
        (by simpa only [j.physical_continuous] using hq)
        (by simpa only [j.physical_continuous] using hb) hmark hslow.2

/-- The same constancy holds inside every actual positive-duration piece. -/
theorem Execution.zero_recovery_locked_paths {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n)
    (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b = 0)
    (hmark : e.NoMarkFlows i) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time,
      f.path t i .q = 1 / 4 ∧ f.path t i .b = 0) := by
  have hs := e.zero_recovery_locked_states i hm hq hb hmark
  induction e with
  | nil => trivial
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      refine ⟨?_,ih (rest.allStates_initial hs.2).1
        (rest.allStates_initial hs.2).2.1 (rest.allStates_initial hs.2).2.2 hmark.2 hs.2⟩
      have hr := f.recovery_without_mark i hmark.1
      have hz : ∀ t ∈ Icc s.time v.time, f.path t i .b = 0 := by
        intro t ht; rw [hr t ht,hb]
      intro t ht
      exact ⟨(f.slow_charge_constant_of_zero_recovery i hm hz t ht).trans hq,hz t ht⟩
    | jump j =>
      exact ih (rest.allStates_initial hs.2).1
        (rest.allStates_initial hs.2).2.1 (rest.allStates_initial hs.2).2.2 hmark hs.2

/-- Uniform over every finite execution satisfying no protected MARK: no
further firing is possible, without assuming completeness at a horizon. -/
theorem Execution.no_firing_of_zero_recovery {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n)
    (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b = 0)
    (hmark : e.NoMarkFlows i) : e.emissionTimes i = [] := by
  apply e.no_emissions_if_not_ready i
  exact e.allStates_mono (fun _ h => by rw [h]; decide)
    (e.slow_forever_of_zero_recovery i hm hq hb hmark)

/-- Explicit quiet-sensor data justify the no-MARK hypothesis. The absence
of new arrivals alone would not exclude a previously active sensor. -/
theorem Execution.no_mark_of_quiet_sensors {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n)
    (ha : ∀ p, s.aux i p = .ready) (hx : ∀ p, s.x i (.m p) ≤ 1 / 40)
    (hr : ∀ p, s.raw i p = none) (hno : ∀ p, NoArrivalAt e i p) :
    e.NoMarkFlows i := by
  apply e.no_mark_flows_of_ready_aux i
  intro p
  exact e.allStates_aux_flows i p .ready
    (e.aux_ready_without_input i p (ha p) (hx p) (hr p) (hno p))

/-- A SLOW cell with zero recovery and quiet unforced sensors remains locked
through every supplied finite execution, independently of other cells. -/
theorem Execution.zero_recovery_quiet_lock {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n)
    (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b = 0)
    (ha : ∀ p, s.aux i p = .ready) (hx : ∀ p, s.x i (.m p) ≤ 1 / 40)
    (hr : ∀ p, s.raw i p = none) (hno : ∀ p, NoArrivalAt e i p) :
    e.AllStates (fun v => v.main i = .slow ∧ v.x i .q = 1 / 4 ∧ v.x i .b = 0) ∧
      e.emissionTimes i = [] := by
  have hmark := e.no_mark_of_quiet_sensors i ha hx hr hno
  exact ⟨e.zero_recovery_locked_states i hm hq hb hmark,
    e.no_firing_of_zero_recovery i hm hq hb hmark⟩

/-- In contrast, an actual fully exposed isolated MARK section repairs zero
recovery to 0.1. Existence and exposure of that section are explicit premises. -/
theorem Execution.zero_recovery_repaired_by_mark {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) (hother : e.OtherMarkClosed i p)
    (hb : s.x i .b = 0) (hs : s.x i (.m p) = 1) (hu : u.x i (.m p) = 4 / 5) :
    u.x i .b = 1 / 10 := by
  have h := e.isolated_mark_conservation i p ho hother
  rw [hb,hs,hu] at h
  linarith

/-- Constant coordinates for a genuinely unrecovering cell. The reserve is
the exact equilibrium for the SLOW work rate 1.1. -/
noncomputable def zeroRecoveryIdleValues (n : ℕ) : Values n := fun _ c =>
  match c with
  | .q => 1 / 4
  | .m _ => 1 / 40
  | .z _ => 0
  | .b => 0
  | .energy => 9989 / 100

noncomputable def zeroRecoveryIdle (n : ℕ) (time : ℝ) : Snapshot n where
  time := time
  x := zeroRecoveryIdleValues n
  main := fun _ => .slow
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := []

theorem zeroRecoveryIdle_field {n} (θ : Fin n → Parameters) (start t : ℝ)
    (i : Fin n) (c : Coord) :
    field θ (zeroRecoveryIdle n start) (zeroRecoveryIdleValues n) t i c = 0 := by
  cases c <;>
    norm_num [field,zeroRecoveryIdle,zeroRecoveryIdleValues,markAct,errorAct,
      work,current,auxDrain]

/-- An actual legal constant flow, for any positive duration, network size
and fixed parameters. No pre-existing complete execution is assumed. -/
noncomputable def zeroRecoveryIdleFlow {n} (θ : Fin n → Parameters) (start finish : ℝ)
    (ht : start < finish) : Flow θ (zeroRecoveryIdle n start) (zeroRecoveryIdle n finish) where
  positive := ht
  path := fun _ => zeroRecoveryIdleValues n
  initial := rfl
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun _ _ => continuousOn_const
  integrable := by
    intro i c
    simp_rw [zeroRecoveryIdle_field]
    exact intervalIntegrable_const
  mark_integrable := by
    intro i p
    simp only [zeroRecoveryIdle,markAct,reduceCtorEq,false_and,ite_false]
    exact intervalIntegrable_const
  integral_eq := by
    intro t ht i c
    simp only [zeroRecoveryIdle_field,intervalIntegral.integral_zero,add_zero]
    rfl
  guards := by
    intro t ht
    constructor
    · intro i; norm_num [BeforeGuards,zeroRecoveryIdle,zeroRecoveryIdleValues]
    · intro i p; norm_num [zeroRecoveryIdle,zeroRecoveryIdleValues]
  raw_support := by
    intro i p origin h
    simp [zeroRecoveryIdle] at h
  pending_urgent := by
    intro d hd
    simp [zeroRecoveryIdle] at hd

theorem zeroRecoveryIdle_no_jump {n} (route : Router n) (time : ℝ) (u : Snapshot n) :
    IsEmpty (Jump route (zeroRecoveryIdle n time) u) := by
  refine ⟨fun j => ?_⟩
  cases j <;> simp_all [zeroRecoveryIdle,zeroRecoveryIdleValues]

/-- The locked regime has complete finite witnesses through arbitrarily
late horizons; silence is not obtained by excluding all positive flows. -/
theorem zeroRecoveryIdle_complete {n} (θ : Fin n → Parameters) (route : Router n)
    (start finish : ℝ) (ht : start < finish) :
    ∃ e : Execution θ route (zeroRecoveryIdle n start) (zeroRecoveryIdle n finish),
      CompleteThrough e finish ∧ ∀ i, e.emissionTimes i = [] := by
  let e : Execution θ route (zeroRecoveryIdle n start) (zeroRecoveryIdle n finish) :=
    .cons (.flow (zeroRecoveryIdleFlow θ start finish ht)) (.nil _)
  refine ⟨e,⟨rfl,zeroRecoveryIdle_no_jump route finish,?_⟩,?_⟩
  · intro d hd; simp [zeroRecoveryIdle] at hd
  · intro i; rfl

/-- Zero recovery lies in the current physical-state bounds whenever the
gain caps are at least one; it is not a nominal birth state. -/
theorem zeroRecoveryIdle_physical {n} (θ : Fin n → Parameters) (time : ℝ)
    (hcap : ∀ i p, 1 ≤ (θ i).cap p) : PhysicalInvariant θ (zeroRecoveryIdle n time) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i; norm_num [UpperRegion,zeroRecoveryIdle,zeroRecoveryIdleValues,auxUpper]
  · intro i p
    simpa only [zeroRecoveryIdle,zeroRecoveryIdleValues] using Real.log_nonneg (hcap i p)
  · intro i; norm_num [zeroRecoveryIdle,zeroRecoveryIdleValues]
  · intro i; norm_num [zeroRecoveryIdle,zeroRecoveryIdleValues]

/-- In particular the witness is physically admissible for either declared
fabrication box; zero recovery itself does not violate current state bounds. -/
theorem zeroRecoveryIdle_physical_of_box {n θ ε} (box : @PhysicalBox n θ ε) (time : ℝ) :
    PhysicalInvariant θ (zeroRecoveryIdle n time) := by
  apply zeroRecoveryIdle_physical θ time
  intro i p
  have h := (box.2 i p).1.1
  rcases box.1 with hε | hε
  all_goals rw [hε] at h
  all_goals norm_num at h
  all_goals linarith

#print axioms Execution.zero_recovery_quiet_lock
#print axioms Execution.zero_recovery_repaired_by_mark
#print axioms zeroRecoveryIdle_complete

end KernelR.Hybrid
