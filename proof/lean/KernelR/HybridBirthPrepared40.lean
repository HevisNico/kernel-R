import KernelR.HybridBirthProtectedMark
import KernelR.HybridQuietSourceArrival
import KernelR.HybridProtectedAuxReturn
import KernelR.HybridSlowReopenExistence

namespace KernelR.Hybrid

/-- The original birth execution, extended through the protected return and
the actual next source. This record retains the physical suffix itself. -/
structure BirthPrepared40 (θ : Fin 1 → Parameters) (born : Snapshot 1) where
  mark : BirthProtectedMark θ born
  final : Snapshot 1
  suffix : Execution θ (fun _ _ => []) mark.final final
  suffix_contacts_transversal : suffix.ContactsTransversal
  date : final.time = 40
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_active : final.raw 0 0 = some 40
  raw_other : ∀ p, p ≠ 0 → final.raw 0 p = none
  pending : final.pending = sourceTrain 0 0 48 8 10 ++ sourceTrain 0 0 160 8 16
  gains : ∀ p, final.x 0 (.z p) = mark.final.x 0 (.z p)
  recovery_preserved : final.x 0 .b = mark.final.x 0 .b
  deliveries_suffix : suffix.deliveries = [⟨0,0,40⟩]
  emissions_suffix : suffix.ledger.emissions = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

noncomputable def BirthPrepared40.execution {θ born} (c : BirthPrepared40 θ born) :
    Execution θ (fun _ _ => []) born c.final := c.mark.execution.append c.suffix

@[simp] theorem BirthPrepared40.contacts_transversal {θ born}
    (c : BirthPrepared40 θ born) : c.execution.ContactsTransversal := by
  rw [BirthPrepared40.execution, Execution.contactsTransversal_append]
  exact ⟨c.mark.contacts_transversal, c.suffix_contacts_transversal⟩

theorem BirthPrepared40.gain_target {θ born} (c : BirthPrepared40 θ born) :
    c.final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5 := by
  rw [c.gains,c.mark.gain_target]

theorem BirthPrepared40.recovery {θ born} (c : BirthPrepared40 θ born) :
    c.final.x 0 .b = born.x 0 .b + 1 / 10 := by
  rw [c.recovery_preserved,c.mark.recovery]

theorem BirthPrepared40.prepared {θ born} (c : BirthPrepared40 θ born) :
    PreparedSection c.final 0 := by
  refine ⟨(c.ready 0).ready,(c.ready 0).charge,?_,(c.ready 0).auxiliary⟩
  rw [c.recovery]
  have h := (c.mark.first.weak.birth.2.2 0).2.2.1
  constructor <;> linarith [h.1,h.2]

theorem BirthPrepared40.emissions {θ born} (c : BirthPrepared40 θ born) :
    c.execution.ledger.emissions = [(0,c.mark.first.final.time)] := by
  simp only [BirthPrepared40.execution,Execution.emissions_append,c.mark.emissions,
    c.emissions_suffix,List.append_nil]

theorem BirthPrepared40.deliveries {θ born} (c : BirthPrepared40 θ born) :
    c.execution.deliveries = sourceTrain 0 0 0 8 6 := by
  simp only [BirthPrepared40.execution,Execution.deliveries_append,c.mark.deliveries,
    c.deliveries_suffix]
  norm_num [sourceTrain,List.ofFn_succ]

theorem BirthPrepared40.error_dose {θ born} (c : BirthPrepared40 θ born) :
    c.execution.ledger.error 0 0 = 9 / 5 := by
  have h := c.execution.gain_balance 0 0
  rw [c.gain_target] at h
  linarith

theorem BirthPrepared40.mark_other_zero {θ born} (c : BirthPrepared40 θ born)
    (p : Port) (hp : p ≠ 0) : c.execution.ledger.mark 0 p = 0 := by
  have hno : NoArrivalAt c.execution 0 p := by
    intro d hd
    rw [c.deliveries] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    exact Or.inr (Ne.symm hp)
  have hs := c.mark.first.weak.birth.ready_coordinates 0 c.mark.initial_aux
  have hstates := c.execution.aux_ready_without_input_band 0 p (c.mark.initial_aux p)
    ((hs.auxiliary p).2.2) (c.mark.first.weak.birth.2.1 0 p) hno
  exact c.execution.mark_zero_aux 0 p .ready (by decide)
    (c.execution.allStates_aux_flows 0 p .ready hstates)

theorem BirthPrepared40.mark_dose {θ born} (c : BirthPrepared40 θ born) :
    c.execution.ledger.mark 0 0 = 1 / 10 := by
  have hr := c.execution.recovery_balance 0
  rw [c.recovery] at hr
  have hsum := c.execution.recovery_sum_marks 0
  have hs : (∑ p : Port, c.execution.ledger.mark 0 p) = c.execution.ledger.mark 0 0 :=
    Finset.sum_eq_single 0 (fun p _ hp => c.mark_other_zero p hp) (by simp)
  rw [hs] at hsum
  linarith

theorem BirthPrepared40.complete {θ born} (c : BirthPrepared40 θ born) :
    CompleteThrough c.execution 40 := by
  have hfuture : ∀ d ∈ c.final.pending, (40 : ℝ) < d.due := by
    intro d hd
    rw [c.pending] at hd
    have hl := a_source_tail_future 48 48 10 (by norm_num) (by norm_num) d hd
    linarith
  refine ⟨c.date,?_,hfuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro j
      rw [(c.ready j).ready]
      linarith [(c.ready j).charge.2]
    · intro j p
      rw [((c.ready j).auxiliary p).1]
      linarith [((c.ready j).auxiliary p).2.2]
  · intro j p origin hraw
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    by_cases hp : p = 0
    · subst p
      have he : origin = (40 : ℝ) := Option.some.inj (hraw.symm.trans c.raw_active)
      rw [he,c.date]
      norm_num
    · rw [c.raw_other p hp] at hraw
      contradiction
  · intro d hd
    rw [c.date]
    exact hfuture d hd

/-- Extend the constructed protected MARK through both genuine guard returns,
then consume source40. No reaching execution or requested pulse outcome is
an additional premise. -/
theorem BirthProtectedMark.prepared40_exists {θ ε born}
    (c : BirthProtectedMark θ born) (hb : PhysicalBox θ ε) :
    Nonempty (BirthPrepared40 θ born) := by
  have hband : 17999 / 100000 ≤ c.final.x 0 .b ∧ c.final.x 0 .b ≤ 18001 / 100000 := by
    rw [c.recovery]
    have h := (c.first.weak.birth.2.2 0).2.2.1
    constructor <;> linarith [h.1,h.2]
  have hp : ∀ d ∈ c.final.pending, (40 : ℝ) ≤ d.due := by
    intro d hd
    rw [c.pending] at hd
    exact a_source_tail_future 40 40 11 (by norm_num) (by norm_num) d hd
  have hr : c.final.raw 0 0 = some 32 := by
    have h := c.mark.raw_active
    rw [c.arrival.date] at h
    exact h
  obtain ⟨aux⟩ := protected_aux_return_exists (route := fun _ _ => []) hb c.final c.mark.physical c.mark.raw_valid
    c.date_bounds c.mark.main_slow c.mark.aux_silent c.mark.sensor_charge c.mark.charge
    hband c.mark.auxiliary_other hr c.mark.raw_other hp
  have hauxB : 17999 / 100000 ≤ aux.final.x 0 .b ∧ aux.final.x 0 .b ≤ 18001 / 100000 := by
    rw [aux.recovery]
    exact hband
  have hauxP : ∀ d ∈ aux.final.pending, (40 : ℝ) ≤ d.due := by
    intro d hd
    rw [aux.pending] at hd
    exact hp d hd
  obtain ⟨ret⟩ := slow_reopen_exists (route := fun _ _ => []) hb aux.final aux.physical aux.raw_valid aux.main_slow
    aux.charge hauxB (fun p => ⟨aux.auxiliary 0 p,aux.rest p⟩) aux.raw_none
    (by linarith [aux.time_bounds.2]) hauxP
  let later : List (Delivery 1) := sourceTrain 0 0 48 8 10 ++ sourceTrain 0 0 160 8 16
  have hhead : ret.final.pending = (⟨0,0,40⟩ : Delivery 1) :: later := by
    rw [ret.pending,aux.pending,c.pending,sourceTrain_succ]
    norm_num [later]
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) hb ret.final (⟨0,0,40⟩ : Delivery 1) later
    ret.physical ret.raw_valid ret.ready ret.raw_none (by linarith [ret.deadline]) hhead (by
      intro d hd
      have h := a_source_tail_future 48 48 10 (by norm_num) (by norm_num) d hd
      change (40 : ℝ) ≤ d.due
      linarith)
  let suffix := (aux.execution.append ret.execution).append arrival.execution
  refine ⟨{
    mark := c
    final := arrival.final
    suffix := suffix
    suffix_contacts_transversal := by
      simp [suffix, aux.contacts_transversal, ret.contacts_transversal, arrival.contacts_transversal]
    date := arrival.date
    ready := arrival.ready
    charge := ?_
    raw_active := ?_
    raw_other := fun p hp => arrival.raw_other 0 p (Or.inr hp)
    pending := arrival.pending
    gains := fun p => (arrival.gain_preserved 0 p).trans ((ret.gains 0 p).trans (aux.gains 0 p))
    recovery_preserved := (arrival.recovery_preserved 0).trans ((ret.recovery 0).trans (aux.recovery 0))
    deliveries_suffix := ?_
    emissions_suffix := ?_
    physical := arrival.physical
    raw_valid := arrival.raw_valid
  }⟩
  · rw [arrival.values]
    simp [quietValues,ret.charge,relax]
  · have ht : arrival.final.time = (40 : ℝ) := arrival.date
    simpa only [ht] using arrival.raw_active
  · simp only [suffix,Execution.deliveries_append,aux.deliveries,ret.deliveries,
      arrival.deliveries,List.nil_append]
  · simp only [suffix,Execution.emissions_append,aux.emissions,ret.emissions,
      arrival.emissions,List.nil_append]

theorem birth_protocol_prepared40_exists {θ ε born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    Nonempty (BirthPrepared40 θ born) := by
  obtain ⟨c⟩ := birth_protocol_protected_mark_exists hborn hb ha hqueue
  exact c.prepared40_exists hb

end KernelR.Hybrid
