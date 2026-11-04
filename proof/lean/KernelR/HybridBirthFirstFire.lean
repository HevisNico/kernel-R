import KernelR.HybridBirthWeakPrefix
import KernelR.HybridFirstLearnedFireExistence

namespace KernelR.Hybrid

structure BirthFirstFire (θ : Fin 1 → Parameters) (route : Router 1) (born : Snapshot 1) where
  weak : BirthWeakPrefix θ route born
  fire : FirstLearnedFire θ route weak.final 0 0

noncomputable def BirthFirstFire.final {θ route born} (c : BirthFirstFire θ route born) : Snapshot 1 := c.fire.final

noncomputable def BirthFirstFire.execution {θ route born} (c : BirthFirstFire θ route born) :
    Execution θ route born c.final := c.weak.execution.append c.fire.execution

@[simp] theorem BirthFirstFire.contacts_transversal {θ route born}
    (c : BirthFirstFire θ route born) : c.execution.ContactsTransversal := by
  change (c.weak.execution.append c.fire.execution).ContactsTransversal
  exact (Execution.contactsTransversal_append _ _).2
    ⟨c.weak.contacts_transversal, c.fire.contacts_transversal⟩

theorem birth_protocol_first_fire_exists {θ ε route born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    Nonempty (BirthFirstFire θ route born) := by
  obtain ⟨w⟩ := birth_protocol_weak_prefix_exists (route := route) hborn hb ha hqueue
  obtain ⟨f⟩ := first_learned_fire_exists (route := route) w.final hb w.physical w.raw_valid 0 0
    w.ready w.learned_gain w.raw_active w.raw_other (by
      intro d hd; rw [w.pending] at hd; rw [w.date]
      have hl := a_source_tail_future 32 32 12 (by norm_num) (by norm_num) d hd
      change (24 : ℝ) + 8 ≤ d.due; linarith)
  exact ⟨⟨w,f⟩⟩

theorem BirthFirstFire.date_bounds {θ route born} (c : BirthFirstFire θ route born) :
    (243 / 10 : ℝ) < c.final.time ∧ c.final.time < 249 / 10 := by
  change (243 / 10 : ℝ) < c.fire.final.time ∧ c.fire.final.time < 249 / 10
  rw [c.fire.date,c.weak.date]
  constructor <;> linarith [c.fire.early,c.fire.deadline]

theorem BirthFirstFire.emissions {θ route born} (c : BirthFirstFire θ route born) :
    c.execution.ledger.emissions = [(0,c.final.time)] := by
  change (c.weak.execution.append c.fire.execution).ledger.emissions = [(0,c.fire.final.time)]
  rw [Execution.emissions_append,c.weak.emissions,c.fire.emissions]
  simp only [List.nil_append,c.fire.date]

theorem BirthFirstFire.deliveries {θ route born} (c : BirthFirstFire θ route born) :
    c.execution.deliveries = sourceTrain 0 0 0 8 4 := by
  change (c.weak.execution.append c.fire.execution).deliveries = _
  rw [Execution.deliveries_append,c.weak.deliveries,c.fire.deliveries,List.append_nil]

theorem BirthFirstFire.pending {θ route born} (c : BirthFirstFire θ route born) :
    c.final.pending = (sourceTrain 0 0 32 8 12 ++ sourceTrain 0 0 160 8 16) ++ route 0 c.final.time := by
  change c.fire.final.pending = _
  rw [c.fire.pending,c.weak.pending,← c.fire.date]
  rfl

theorem BirthFirstFire.gain_target {θ route born} (c : BirthFirstFire θ route born) :
    c.final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5 := by
  change c.fire.final.x 0 (.z 0) = _
  rw [c.fire.gain_preserved,c.weak.gain_target]

theorem BirthFirstFire.recovery {θ route born} (c : BirthFirstFire θ route born) :
    c.final.x 0 .b = born.x 0 .b := by
  change c.fire.final.x 0 .b = _
  rw [c.fire.recovery_preserved,c.weak.recovery]

theorem BirthFirstFire.error_dose {θ route born} (c : BirthFirstFire θ route born) :
    c.execution.ledger.error 0 0 = 9 / 5 := by
  have h := c.execution.gain_balance 0 0
  rw [c.gain_target] at h
  linarith


/-- Saturation after the first output requires its newly routed tokens to be
strictly future. The actual pre-birth contact is closed and discharges this. -/
theorem BirthFirstFire.complete {θ route born} (c : BirthFirstFire θ route born)
    (hrouted : ∀ d ∈ route 0 c.final.time, c.final.time < d.due) :
    CompleteThrough c.execution c.final.time := by
  have hguard : BeforeGuards c.final c.final.x := by
    constructor
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hm : c.final.main 0 = .fast := c.fire.main_fast
      have hq : c.final.x 0 .q = 1 := c.fire.charge
      rw [hm,hq]; norm_num
    · intro j p
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hp : p = 0
      · subst p
        have hm : c.final.aux 0 0 = .silent := c.fire.aux_silent
        rw [hm]; exact c.fire.sensor_above
      · have hno : NoArrivalAt c.fire.execution 0 p := by simp [NoArrivalAt,c.fire.deliveries]
        have h := c.fire.execution.aux_no_input_rest_band 0 p ((c.weak.ready 0).auxiliary p).1
          ((c.weak.ready 0).auxiliary p).2 (c.weak.raw_other 0 p (Or.inr hp)) hno
        have hm : c.final.aux 0 p = .ready := h.1.1
        rw [hm]
        have hu : c.final.x 0 (.m p) ≤ 1 / 40 + 1 / 100000 := h.1.2.2
        linarith
  have hpending : ∀ d ∈ c.final.pending, c.final.time < d.due := by
    intro d hd
    rw [c.pending] at hd
    rcases List.mem_append.mp hd with hd | hd
    · have hl := a_source_tail_future 32 32 12 (by norm_num) (by norm_num) d hd
      linarith [c.date_bounds.2]
    · exact hrouted d hd
  refine ⟨rfl,?_,hpending⟩
  intro u
  apply hguard.no_jump
  · intro j p origin hraw
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    by_cases hp : p = 0
    · subst p
      have hr : c.final.raw 0 0 = some c.weak.final.time := c.fire.raw_active
      have he : origin = c.weak.final.time := Option.some.inj (hraw.symm.trans hr)
      rw [he,c.weak.date]
      linarith [c.date_bounds.2]
    · have hr : c.final.raw 0 p = none := c.fire.raw_other 0 p (Or.inr hp)
      rw [hr] at hraw; contradiction
  · exact hpending

theorem birth_protocol_first_fire_complete_exists {θ ε born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    ∃ c : BirthFirstFire θ (fun _ _ => []) born, CompleteThrough c.execution c.final.time := by
  obtain ⟨c⟩ := birth_protocol_first_fire_exists (route := fun _ _ => []) hborn hb ha hqueue
  exact ⟨c,c.complete (by simp)⟩

end KernelR.Hybrid
