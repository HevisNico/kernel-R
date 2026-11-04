import KernelR.HybridFlowCuts
import KernelR.HybridFirstSlowSource
import KernelR.HybridBirthFirstFastEnd
import KernelR.HybridSlowInputMarkExistence

namespace KernelR.Hybrid

structure BirthProtectedMark (θ : Fin 1 → Parameters) (born : Snapshot 1) where
  initial_aux : ∀ p, born.aux 0 p = .ready
  first : BirthFirstFire θ (fun _ _ => []) born
  fast : BirthFirstFastEnd first
  arrival : FirstSlowSource θ (fun _ _ => []) fast.final
  mark : SlowInputMark θ (fun _ _ => []) arrival.final 0

noncomputable def BirthProtectedMark.final {θ born} (c : BirthProtectedMark θ born) : Snapshot 1 := c.mark.final

noncomputable def BirthProtectedMark.markTrace {θ born} (c : BirthProtectedMark θ born) :
    Execution θ (fun _ _ => []) (firstSlowSourceFinal θ c.fast.final) c.mark.final :=
  c.mark.execution.cast_source rfl

theorem BirthProtectedMark.markTrace_ledger {θ born} (c : BirthProtectedMark θ born) :
    c.markTrace.ledger = c.mark.execution.ledger := c.mark.execution.cast_source_ledger rfl

theorem BirthProtectedMark.markTrace_deliveries {θ born} (c : BirthProtectedMark θ born) :
    c.markTrace.deliveries = c.mark.execution.deliveries := c.mark.execution.cast_source_deliveries rfl

noncomputable def BirthProtectedMark.execution {θ born} (c : BirthProtectedMark θ born) :
    Execution θ (fun _ _ => []) born c.final :=
  ((c.first.execution.append c.fast.execution).append c.arrival.execution).append c.markTrace

@[simp] theorem BirthProtectedMark.contacts_transversal {θ born}
    (c : BirthProtectedMark θ born) : c.execution.ContactsTransversal := by
  change (((c.first.execution.append c.fast.execution).append c.arrival.execution).append
    c.mark.execution).ContactsTransversal
  exact (Execution.contactsTransversal_append _ _).2
    ⟨(Execution.contactsTransversal_append _ _).2
      ⟨(Execution.contactsTransversal_append _ _).2
        ⟨c.first.contacts_transversal, c.fast.contacts_transversal⟩,
        c.arrival.contacts_transversal⟩, c.mark.contacts_transversal⟩

/-- The actual first main return remains SLOW at source32. That source then
constructs the protected MARK, using its own unchanged birth recovery. -/
theorem birth_protocol_protected_mark_exists {θ ε born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    Nonempty (BirthProtectedMark θ born) := by
  obtain ⟨c⟩ := birth_protocol_first_fire_exists (route := fun _ _ => []) hborn hb ha hqueue
  obtain ⟨fast⟩ := c.first_fast_end_exists hb
  have hdate : c.final.time = c.weak.final.time + c.fire.latency := c.fire.date
  have hfire : 24 + 2 / 5 < c.final.time ∧ c.final.time < 24 + 9 / 10 := by
    have hl := readyPulse_root_after_four_tenths (c.weak.ready 0).charge.2 c.weak.learned_gain.2
      (by linarith [c.fire.early] : c.weak.final.time ≤ c.weak.final.time + c.fire.latency) c.fire.response_root
    rw [← hdate,c.weak.date] at hl
    exact ⟨hl,by linarith [c.date_bounds.2]⟩
  have hfast_b : fast.final.x 0 .b = born.x 0 .b := (fast.recovery 0).trans c.recovery
  have hband : 7999 / 100000 ≤ fast.final.x 0 .b ∧ fast.final.x 0 .b ≤ 8001 / 100000 := by
    rw [hfast_b]
    have h := (hborn.2.2 0).2.2.1
    constructor <;> linarith [h.1,h.2]
  have hpending : fast.final.pending = sourceTrain 0 0 32 8 12 ++ sourceTrain 0 0 160 8 16 := by
    rw [fast.pending,c.pending]
    simp
  obtain ⟨arrival⟩ := first_slow_source_exists (route := fun _ _ => []) hb fast.final c.final.time
    fast.physical fast.raw_valid fast.date hfire fast.main_slow fast.charge hband fast.auxiliary
    fast.raw_none fast.sensor_charge fast.rest hpending
  have harrival_b : arrival.final.x 0 .b = fast.final.x 0 .b := arrival.recovery_preserved
  have harrival_band : 7999 / 100000 ≤ arrival.final.x 0 .b ∧ arrival.final.x 0 .b ≤ 8001 / 100000 := by
    rw [harrival_b]; exact hband
  have hraw : arrival.final.raw 0 0 = some arrival.final.time := by
    rw [arrival.date]
    exact arrival.raw_active
  obtain ⟨mark⟩ := slow_input_mark_exists (route := fun _ _ => []) hb arrival.final 0
    arrival.physical arrival.raw_valid arrival.main_slow ⟨arrival.charge.1.le,arrival.charge.2.le⟩ harrival_band
    (fun p => ⟨arrival.aux_ready 0 p,arrival.rest p⟩) hraw (fun p hp => arrival.raw_other p hp) (by
      intro d hd
      rw [arrival.pending] at hd
      rw [arrival.date]
      have hl := a_source_tail_future 40 40 11 (by norm_num) (by norm_num) d hd
      change (32 : ℝ) + 8 ≤ d.due
      linarith)
  exact ⟨⟨ha,c,fast,arrival,mark⟩⟩

theorem BirthProtectedMark.date_bounds {θ born} (c : BirthProtectedMark θ born) :
    (3201 / 100 : ℝ) < c.final.time ∧ c.final.time < 641 / 20 := by
  have hl := c.mark.early
  have hu := c.mark.deadline
  rw [c.arrival.date] at hl hu
  change (3201 / 100 : ℝ) < c.mark.final.time ∧ c.mark.final.time < 641 / 20
  constructor <;> linarith

theorem BirthProtectedMark.gain_target {θ born} (c : BirthProtectedMark θ born) :
    c.final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5 := by
  change c.mark.final.x 0 (.z 0) = _
  rw [c.mark.gain_preserved]
  have h : c.arrival.final.x 0 (.z 0) = c.fast.final.x 0 (.z 0) := c.arrival.gain_preserved 0
  rw [h,c.fast.gains,c.first.gain_target]

theorem BirthProtectedMark.recovery {θ born} (c : BirthProtectedMark θ born) :
    c.final.x 0 .b = born.x 0 .b + 1 / 10 := by
  change c.mark.final.x 0 .b = _
  rw [c.mark.recovery_gain]
  have h : c.arrival.final.x 0 .b = c.fast.final.x 0 .b := c.arrival.recovery_preserved
  rw [h,c.fast.recovery,c.first.recovery]

theorem BirthProtectedMark.pending {θ born} (c : BirthProtectedMark θ born) :
    c.final.pending = sourceTrain 0 0 40 8 11 ++ sourceTrain 0 0 160 8 16 := by
  change c.mark.final.pending = _
  rw [c.mark.pending,c.arrival.pending]

theorem BirthProtectedMark.error_dose {θ born} (c : BirthProtectedMark θ born) :
    c.execution.ledger.error 0 0 = 9 / 5 := by
  have h := c.execution.gain_balance 0 0
  rw [c.gain_target] at h
  linarith

theorem BirthProtectedMark.emissions {θ born} (c : BirthProtectedMark θ born) :
    c.execution.ledger.emissions = [(0,c.first.final.time)] := by
  change (((c.first.execution.append c.fast.execution).append c.arrival.execution).append c.markTrace).ledger.emissions = _
  simp only [Execution.emissions_append,c.first.emissions,c.fast.emissions,c.arrival.emissions,c.markTrace_ledger,c.mark.emissions,List.append_nil]

theorem BirthProtectedMark.deliveries {θ born} (c : BirthProtectedMark θ born) :
    c.execution.deliveries = sourceTrain 0 0 0 8 5 := by
  change (((c.first.execution.append c.fast.execution).append c.arrival.execution).append c.markTrace).deliveries = _
  simp only [Execution.deliveries_append,c.first.deliveries,c.fast.deliveries,c.arrival.deliveries,c.markTrace_deliveries,c.mark.deliveries,List.append_nil]
  norm_num [sourceTrain,List.ofFn_succ]


theorem BirthProtectedMark.mark_other_zero {θ born} (c : BirthProtectedMark θ born)
    (p : Port) (hp : p ≠ 0) : c.execution.ledger.mark 0 p = 0 := by
  have hno : NoArrivalAt c.execution 0 p := by
    intro d hd
    rw [c.deliveries] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    exact Or.inr (Ne.symm hp)
  have hs := c.first.weak.birth.ready_coordinates 0 c.initial_aux
  have hstates := c.execution.aux_ready_without_input_band 0 p (c.initial_aux p)
    ((hs.auxiliary p).2.2) (c.first.weak.birth.2.1 0 p) hno
  exact c.execution.mark_zero_aux 0 p .ready (by decide)
    (c.execution.allStates_aux_flows 0 p .ready hstates)

theorem BirthProtectedMark.mark_dose {θ born} (c : BirthProtectedMark θ born) :
    c.execution.ledger.mark 0 0 = 1 / 10 := by
  have hr := c.execution.recovery_balance 0
  rw [c.recovery] at hr
  have hsum := c.execution.recovery_sum_marks 0
  have hs : (∑ p : Port, c.execution.ledger.mark 0 p) = c.execution.ledger.mark 0 0 :=
    Finset.sum_eq_single 0 (fun p _ hp => c.mark_other_zero p hp) (by simp)
  rw [hs] at hsum
  linarith

theorem BirthProtectedMark.complete {θ born} (c : BirthProtectedMark θ born) :
    CompleteThrough c.execution c.final.time := by
  have hguard : BeforeGuards c.final c.final.x := by
    constructor
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hm : c.final.main 0 = .slow := c.mark.main_slow
      have hq : 17 / 125 ≤ c.final.x 0 .q := c.mark.charge.1
      rw [hm]; linarith
    · intro j p
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hp : p = 0
      · subst p
        have hm : c.final.aux 0 0 = .silent := c.mark.aux_silent
        have hx : c.final.x 0 (.m 0) = 4 / 5 := c.mark.sensor_charge
        rw [hm,hx]; norm_num
      · have hm : c.final.aux 0 p = .ready := (c.mark.auxiliary_other p hp).1
        have hx : c.final.x 0 (.m p) ≤ 1 / 40 + 1 / 100000 := (c.mark.auxiliary_other p hp).2.2
        rw [hm]; linarith
  have hfuture : ∀ d ∈ c.final.pending, c.final.time < d.due := by
    intro d hd
    rw [c.pending] at hd
    have hl := a_source_tail_future 40 40 11 (by norm_num) (by norm_num) d hd
    linarith [c.date_bounds.2]
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply hguard.no_jump
  · intro j p origin hraw
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    by_cases hp : p = 0
    · subst p
      have hr : c.final.raw 0 0 = some 32 := by
        have h := c.mark.raw_active
        rw [c.arrival.date] at h
        exact h
      have he : origin = (32 : ℝ) := Option.some.inj (hraw.symm.trans hr)
      rw [he]; linarith [c.date_bounds.2]
    · have hr : c.final.raw 0 p = none := c.mark.raw_other p hp
      rw [hr] at hraw; contradiction
  · exact hfuture

end KernelR.Hybrid
