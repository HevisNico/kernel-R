import KernelR.HybridWeakFiniteProgress

/-! Under strictly delayed routing, a transverse complete reference rules out
all merely touching READY contacts in every competing weak flow. Refinement
retains the competing execution's exact paths and physical jumps. -/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- Every issued input is strictly later than the FIRE issuing it. -/
def StrictCausalRouter {n} (route : Router n) : Prop :=
  ∀ i t d, d ∈ route i t → t < d.due

theorem Jump.pending_strict {n route s u} (jump : @Jump n route s u)
    (routing : StrictCausalRouter route)
    (pending : ∀ d ∈ s.pending, s.time < d.due) :
    ∀ d ∈ u.pending, u.time < d.due := by
  cases jump with
  | fire i mode guard =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact pending d hd
    · exact routing i s.time d hd
  | arrive d before after queue due free =>
    intro e he
    apply pending e
    rw [queue]
    simp only [List.mem_append, List.mem_cons] at he ⊢
    tauto
  | _ => exact pending

/-- With no due input, a legal jump cannot change the instantaneous current.
At a raw expiry the half-open pulse is already zero before its removal. -/
theorem Jump.current_at_eq_of_pending_strict {n route s u}
    (jump : @Jump n route s u)
    (pending : ∀ d ∈ s.pending, s.time < d.due) (i : Fin n) (p : Port) :
    current s i p s.time = current u i p u.time := by
  cases jump with
  | arrive d before after queue due free =>
    have strict := pending d (by rw [queue]; simp)
    exact False.elim (by linarith)
  | rawEnd k q origin active due =>
    by_cases hi : i=k
    · subst i
      by_cases hp : p=q
      · subst p; simp [current, setRaw, active, pulse, due]
      · simp [current, setRaw, hp]
    · simp [current, setRaw, hi]
  | _ => rfl

theorem Jump.ready_field_eq_of_pending_strict {n θ route s u}
    (jump : @Jump n route s u) (pending : ∀ d ∈ s.pending, s.time < d.due)
    (i : Fin n) (ready : s.main i = .ready) (unchanged : u.main i = s.main i) :
    field θ s s.x s.time i .q = field θ u u.x u.time i .q := by
  simp only [field, ready, unchanged, jump.physical_continuous]
  congr 1
  unfold drive
  apply Finset.sum_congr rfl
  intro p _
  rw [jump.current_at_eq_of_pending_strict pending i p]

theorem Jump.aux_ready_field_eq_of_pending_strict {n θ route s u}
    (jump : @Jump n route s u) (pending : ∀ d ∈ s.pending, s.time < d.due)
    (i : Fin n) (p : Port) (ready : s.aux i p = .ready)
    (unchanged : u.aux i p = s.aux i p) :
    field θ s s.x s.time i (.m p) = field θ u u.x u.time i (.m p) := by
  simp only [field, ready, unchanged, jump.physical_continuous, ite_true]
  rw [jump.current_at_eq_of_pending_strict pending i p]

/-- A READY threshold already reached at a state with no due input has a
positive field whenever that state has a complete transverse continuation.
The argument follows that real continuation until this coordinate departs. -/
theorem Execution.positive_ready_fields_of_transverse_completion {n θ route s u T}
    (execution : @Execution n θ route s u) (routing : StrictCausalRouter route)
    (complete : CompleteThrough execution T) (positive : execution.ContactsTransversal)
    (pending : ∀ d ∈ s.pending, s.time < d.due) :
    (∀ i, s.main i = .ready → s.x i .q = 1 → 0 < field θ s s.x s.time i .q) ∧
    (∀ i p, s.aux i p = .ready → s.x i (.m p) = 1 →
      0 < field θ s s.x s.time i (.m p)) := by
  induction execution with
  | nil s =>
    constructor
    · intro i mode threshold
      exact False.elim ((complete.2.1 _).false (Jump.fire (route := route) s i mode threshold))
    · intro i p mode threshold
      exact False.elim ((complete.2.1 _).false (Jump.mark (route := route) s i p mode threshold))
  | @cons s a u move rest ih =>
    cases move with
    | flow flow =>
      constructor
      · intro i mode threshold
        exact False.elim ((flow.no_initial_jump _).false (Jump.fire (route := route) s i mode threshold))
      · intro i p mode threshold
        exact False.elim ((flow.no_initial_jump _).false (Jump.mark (route := route) s i p mode threshold))
    | jump jump =>
      have next := ih complete positive.2 (jump.pending_strict routing pending)
      have contact := jump.contactTransversal_iff_departures.mp positive.1
      constructor
      · intro i ready threshold
        by_cases unchanged : a.main i = s.main i
        · rw [jump.ready_field_eq_of_pending_strict pending i ready unchanged]
          exact next.1 i (unchanged.trans ready)
            (by simpa only [jump.physical_continuous] using threshold)
        · exact contact.1 i ready unchanged
      · intro i p ready threshold
        by_cases unchanged : a.aux i p = s.aux i p
        · rw [jump.aux_ready_field_eq_of_pending_strict pending i p ready unchanged]
          exact next.2 i p (unchanged.trans ready)
            (by simpa only [jump.physical_continuous] using threshold)
        · exact contact.2 i p ready unchanged

/-- A positive prefix of the same weak integral path. -/
noncomputable def WeakFlow.prefix {n θ s u} (flow : @WeakFlow n θ s u) {t : ℝ}
    (after : s.time < t) (before : t ≤ u.time) : WeakFlow θ s (flow.at t) where
  positive := after
  path := flow.path
  initial := flow.initial
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun i c => (flow.continuous i c).mono (Icc_subset_Icc le_rfl before)
  integrable := fun i c => (flow.integrable i c).mono_set (by
    dsimp only [WeakFlow.at]
    rw [uIcc_of_le after.le, uIcc_of_le flow.positive.le]
    exact Icc_subset_Icc le_rfl before)
  mark_integrable := fun i p => (flow.mark_integrable i p).mono_set (by
    dsimp only [WeakFlow.at]
    rw [uIcc_of_le after.le, uIcc_of_le flow.positive.le]
    exact Icc_subset_Icc le_rfl before)
  integral_eq := fun v hv i c => flow.integral_eq v ⟨hv.1, hv.2.trans before⟩ i c
  guards := fun v hv => flow.guards v ⟨hv.1, hv.2.trans_le before⟩
  raw_support := fun i p origin active =>
    ⟨(flow.raw_support i p origin active).1, before.trans (flow.raw_support i p origin active).2⟩
  pending_urgent := fun d hd => before.trans (flow.pending_urgent d hd)

theorem WeakFlow.at_initial {n θ s u} (flow : @WeakFlow n θ s u) : flow.at s.time = s := by
  cases s
  simp only [WeakFlow.at, flow.initial]

noncomputable def WeakFlow.prefixExecution {n θ route s u} (flow : @WeakFlow n θ s u)
    {t : ℝ} (after : s.time ≤ t) (before : t ≤ u.time) :
    WeakExecution θ route s (flow.at t) := by
  by_cases strict : s.time < t
  · exact .cons (.flow (flow.prefix strict before)) (.nil _)
  · have equal : t = s.time := le_antisymm (le_of_not_gt strict) after
    subst t
    rw [flow.at_initial]
    exact .nil _

/-- Weak READY guards are strict along every positive competing flow before
this complete reference's horizon. Tangencies cannot be inserted into the
protocol trajectory. -/
theorem WeakFlow.strict_guards_of_transverse_completion {n θ ε route s u v T}
    (flow : @WeakFlow n θ s u) (reference : Execution θ route s v)
    (routing : StrictCausalRouter route) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (complete : CompleteThrough reference T)
    (positive : reference.ContactsTransversal) (before : u.time ≤ T) :
    ∀ t ∈ Ico s.time u.time, BeforeGuards s (flow.path t) := by
  intro t ht
  have initialPart := flow.prefixExecution (route := route) ht.1 ht.2.le
  obtain ⟨w, tail, tailComplete, tailPositive⟩ :=
    initialPart.continue_to_transverse_complete reference box physical complete positive (ht.2.le.trans before)
  have pending : ∀ d ∈ (flow.at t).pending, (flow.at t).time < d.due := by
    intro d hd
    exact ht.2.trans_le (flow.pending_urgent d hd)
  have fieldPositive := tail.positive_ready_fields_of_transverse_completion routing
    tailComplete tailPositive pending
  have remainingFlow := flow.suffix ht.1 ht.2
  have guards := flow.guards t ht
  constructor
  · intro i
    cases mode : s.main i with
    | ready =>
      have upper : flow.path t i .q ≤ 1 := by simpa only [mode] using guards.1 i
      apply lt_of_le_of_ne upper
      intro threshold
      have hp := fieldPositive.1 i mode threshold
      let jump := Jump.fire (route := route) (flow.at t) i mode threshold
      exact remainingFlow.no_initial_transverse_jump _ jump hp
    | fast => simpa only [mode] using guards.1 i
    | slow => simpa only [mode] using guards.1 i
  · intro i p
    cases mode : s.aux i p with
    | ready =>
      have upper : flow.path t i (.m p) ≤ 1 := by simpa only [mode] using guards.2 i p
      apply lt_of_le_of_ne upper
      intro threshold
      have hp := fieldPositive.2 i p mode threshold
      let jump := Jump.mark (route := route) (flow.at t) i p mode threshold
      exact remainingFlow.no_initial_transverse_jump _ jump hp
    | mark => simpa only [mode] using guards.2 i p
    | silent => simpa only [mode] using guards.2 i p
    | error => simpa only [mode] using guards.2 i p

/-- Refine the guards while retaining this exact integral path. -/
noncomputable def WeakFlow.toNative {n θ ε route s u v T}
    (flow : @WeakFlow n θ s u) (reference : Execution θ route s v)
    (routing : StrictCausalRouter route) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (complete : CompleteThrough reference T)
    (positive : reference.ContactsTransversal) (before : u.time ≤ T) : Flow θ s u where
  positive := flow.positive
  path := flow.path
  initial := flow.initial
  final := flow.final
  main_fixed := flow.main_fixed
  aux_fixed := flow.aux_fixed
  raw_fixed := flow.raw_fixed
  queue_fixed := flow.queue_fixed
  continuous := flow.continuous
  integrable := flow.integrable
  mark_integrable := flow.mark_integrable
  integral_eq := flow.integral_eq
  guards := flow.strict_guards_of_transverse_completion reference routing box physical complete positive before
  raw_support := flow.raw_support
  pending_urgent := flow.pending_urgent

@[simp] theorem WeakFlow.toNative_toWeak {n θ ε route s u v T}
    (flow : @WeakFlow n θ s u) (reference : Execution θ route s v)
    (routing : StrictCausalRouter route) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (complete : CompleteThrough reference T)
    (positive : reference.ContactsTransversal) (before : u.time ≤ T) :
    (flow.toNative reference routing box physical complete positive before).toWeak = flow := rfl

/-- Every competing finite weak prefix before the reference horizon already
has native strict guards. Equality after forgetting those guards preserves
all original paths, physical jumps, snapshots, and event interleavings. -/
theorem WeakExecution.toNative_of_transverse_completion {n θ ε route s u v T}
    (candidate : @WeakExecution n θ route s u) (reference : Execution θ route s v)
    (routing : StrictCausalRouter route) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (complete : CompleteThrough reference T)
    (positive : reference.ContactsTransversal) (before : u.time ≤ T) :
    ∃ native : Execution θ route s u, native.toWeak = candidate := by
  induction candidate generalizing v with
  | nil s => exact ⟨.nil s, rfl⟩
  | @cons s a u move rest ih =>
    have stepBefore : a.time ≤ T := rest.time_monotone.trans before
    cases move with
    | jump jump =>
      obtain ⟨v', reference', _, complete', _, _, positive'⟩ :=
        reference.strip_initial_jump_transversal box complete positive jump
      have nextPhysical : PhysicalInvariant θ a :=
        (Execution.cons (.jump jump) (.nil a) : Execution θ route s a).physical_invariant box physical
      obtain ⟨nativeRest, same⟩ := ih reference' nextPhysical complete' positive' before
      exact ⟨.cons (.jump jump) nativeRest, by simp only [Execution.toWeak, same]⟩
    | flow flow =>
      let nativeFlow := flow.toNative reference routing box physical complete positive stepBefore
      let initialPart : WeakExecution θ route s a := .cons (.flow flow) (.nil a)
      obtain ⟨v', reference', complete', positive'⟩ :=
        initialPart.continue_to_transverse_complete reference box physical complete positive stepBefore
      obtain ⟨nativeRest, same⟩ := ih reference' (flow.physical_invariant box physical)
        complete' positive' before
      refine ⟨.cons (.flow nativeFlow) nativeRest, ?_⟩
      simp only [Execution.toWeak, nativeFlow, WeakFlow.toNative_toWeak, same]

#print axioms Execution.positive_ready_fields_of_transverse_completion
#print axioms WeakFlow.strict_guards_of_transverse_completion
#print axioms WeakExecution.toNative_of_transverse_completion

end KernelR.Hybrid
