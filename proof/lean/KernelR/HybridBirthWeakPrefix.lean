import KernelR.HybridBirthFirstWeakCycle
import KernelR.HybridWeakInputCycleExistence
import KernelR.HybridQuietSourceArrival
import KernelR.HybridBirthWeakSources

namespace KernelR.Hybrid

private theorem ready_flows_append {n θ route s v u}
    (e : @Execution n θ route s v) (f : Execution θ route v u) (i : Fin n)
    (left : e.MainFlows i .ready) (right : f.MainFlows i .ready) :
    (e.append f).MainFlows i .ready := by
  induction e with
  | nil => exact right
  | cons move rest ih =>
    cases move with
    | jump j => exact ih f left right
    | flow g => exact ⟨left.1, ih f left.2 right⟩

theorem readyCoordinates_one_all {s : Snapshot 1} (h : ReadyCoordinates s 0) :
    ∀ j, ReadyCoordinates s j := by
  intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact h

theorem rawNone_one_all {s : Snapshot 1} (h : ∀ q, s.raw 0 q = none) :
    ∀ j q, s.raw j q = none := by
  intro j q; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact h q

theorem a_source_tail_future (start bound : ℝ) (count : ℕ)
    (hs : bound ≤ start) (hl : bound ≤ 160) :
    ∀ d ∈ sourceTrain (0 : Fin 1) 0 start 8 count ++ sourceTrain 0 0 160 8 16, bound ≤ d.due := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  all_goals
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    dsimp
    have hk : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    linarith

structure BirthWeakPrefix (θ : Fin 1 → Parameters) (route : Router 1) (born : Snapshot 1) where
  birth : BirthState born
  sources : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16
  final : Snapshot 1
  execution : Execution θ route born final
  ready_flows : execution.MainFlows 0 .ready
  contacts_transversal : execution.ContactsTransversal
  date : final.time = 24
  complete : CompleteThrough execution 24
  ready : ∀ j, ReadyCoordinates final j
  raw_active : final.raw 0 0 = some final.time
  raw_other : ∀ j q, j ≠ 0 ∨ q ≠ 0 → final.raw j q = none
  pending : final.pending = sourceTrain 0 0 32 8 12 ++ sourceTrain 0 0 160 8 16
  deliveries : execution.deliveries = sourceTrain 0 0 0 8 4
  emissions : execution.ledger.emissions = []
  gain_target : final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5
  gain_other : ∀ p, p ≠ 0 → final.x 0 (.z p) = born.x 0 (.z p)
  recovery : final.x 0 .b = born.x 0 .b
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- Construct three weak inputs and the fresh fourth source from the whole
birth queue. No reaching execution, output count or gain outcome is assumed. -/
theorem birth_protocol_weak_prefix_exists {θ ε route born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    Nonempty (BirthWeakPrefix θ route born) := by
  obtain ⟨c0⟩ := birth_protocol_first_weak_cycle_exists (route := route) hborn hb ha hqueue
  obtain ⟨a8⟩ := quiet_source_arrival_exists (route := route) hb c0.final (⟨0,0,8⟩ : Delivery 1)
    (sourceTrain 0 0 16 8 14 ++ sourceTrain 0 0 160 8 16) c0.physical c0.raw_valid
    (readyCoordinates_one_all c0.pulse.coordinates) (rawNone_one_all c0.pulse.raw_finished)
    (by rw [c0.date]; norm_num) (by rw [c0.pending,sourceTrain_eight_head]; rfl)
    (a_source_tail_future 16 8 14 (by norm_num) (by norm_num))
  have hg8 : a8.final.x 0 (.z 0) = born.x 0 (.z 0) + 3 / 5 := by
    rw [a8.gain_preserved,c0.gain_target]
  have hb8 := hborn.own_low_port_weak_gain_bounds 0 0 (by decide) 1 (by norm_num)
  have hg8bounds : Real.exp (a8.final.x 0 (.z 0)) ≤ 7 / 6 ∧
      a8.final.x 0 (.z 0) ≤ Real.log (6 / 5) + 1 / 1000 := by
    rw [hg8]; simpa using hb8
  obtain ⟨c1⟩ := weak_input_cycle_exists (route := route) a8.final hb a8.physical a8.raw_valid 0 0 a8.ready
    hg8bounds.1 hg8bounds.2 a8.raw_active a8.raw_other (by
      intro d hd; rw [a8.pending] at hd; rw [a8.date]
      have hl := a_source_tail_future 16 16 14 (by norm_num) (by norm_num) d hd
      change (8 : ℝ) + 8 ≤ d.due; linarith)
  obtain ⟨a16⟩ := quiet_source_arrival_exists (route := route) hb c1.final (⟨0,0,16⟩ : Delivery 1)
    (sourceTrain 0 0 24 8 13 ++ sourceTrain 0 0 160 8 16) c1.physical c1.raw_valid
    (readyCoordinates_one_all c1.pulse.coordinates) (rawNone_one_all c1.pulse.raw_finished)
    (by rw [c1.date,a8.date]; norm_num) (by rw [c1.pending,a8.pending,sourceTrain_sixteen_head]; rfl)
    (a_source_tail_future 24 16 13 (by norm_num) (by norm_num))
  have hg16 : a16.final.x 0 (.z 0) = born.x 0 (.z 0) + 6 / 5 := by
    rw [a16.gain_preserved,c1.pulse.gain_target,hg8]; ring
  have hb16 := hborn.own_low_port_weak_gain_bounds 0 0 (by decide) 2 (by norm_num)
  have hg16bounds : Real.exp (a16.final.x 0 (.z 0)) ≤ 7 / 6 ∧
      a16.final.x 0 (.z 0) ≤ Real.log (6 / 5) + 1 / 1000 := by
    rw [hg16]; norm_num at hb16 ⊢; exact hb16
  obtain ⟨c2⟩ := weak_input_cycle_exists (route := route) a16.final hb a16.physical a16.raw_valid 0 0 a16.ready
    hg16bounds.1 hg16bounds.2 a16.raw_active a16.raw_other (by
      intro d hd; rw [a16.pending] at hd; rw [a16.date]
      have hl := a_source_tail_future 24 24 13 (by norm_num) (by norm_num) d hd
      change (16 : ℝ) + 8 ≤ d.due; linarith)
  obtain ⟨a24⟩ := quiet_source_arrival_exists (route := route) hb c2.final (⟨0,0,24⟩ : Delivery 1)
    (sourceTrain 0 0 32 8 12 ++ sourceTrain 0 0 160 8 16) c2.physical c2.raw_valid
    (readyCoordinates_one_all c2.pulse.coordinates) (rawNone_one_all c2.pulse.raw_finished)
    (by rw [c2.date,a16.date]; norm_num) (by rw [c2.pending,a16.pending,sourceTrain_twenty_four_head]; rfl)
    (a_source_tail_future 32 24 12 (by norm_num) (by norm_num))
  let e := ((((c0.execution.append a8.execution).append c1.execution).append a16.execution).append
    c2.execution).append a24.execution
  have hcomplete : CompleteThrough a24.execution 24 := by
    have h := a24.complete (by
      intro d hd
      have hl := a_source_tail_future 32 32 12 (by norm_num) (by norm_num) d hd
      norm_num; linarith)
    simpa only [a24.date] using h
  refine ⟨{
    birth := hborn
    sources := hqueue
    final := a24.final
    execution := e
    ready_flows := by
      have h0 := c0.continuation.allStates_main_flows 0 .ready c0.pulse.ready_states
      have h1 := c1.execution.allStates_main_flows 0 .ready c1.pulse.ready_states
      have h2 := c2.execution.allStates_main_flows 0 .ready c2.pulse.ready_states
      exact ready_flows_append _ _ 0
        (ready_flows_append _ _ 0
          (ready_flows_append _ _ 0
            (ready_flows_append _ _ 0
              (ready_flows_append _ _ 0 h0 (a8.ready_flows 0)) h1)
            (a16.ready_flows 0)) h2) (a24.ready_flows 0)
    contacts_transversal := by
      simp [e, c0.contacts_transversal, c1.contacts_transversal, c2.contacts_transversal,
        a8.contacts_transversal, a16.contacts_transversal, a24.contacts_transversal]
    date := a24.date
    complete := hcomplete
    ready := a24.ready
    raw_active := a24.raw_active
    raw_other := a24.raw_other
    pending := a24.pending
    deliveries := ?_
    emissions := ?_
    gain_target := ?_
    gain_other := ?_
    recovery := ?_
    physical := a24.physical
    raw_valid := a24.raw_valid
  }⟩
  · simp only [e,Execution.deliveries_append,c0.deliveries,a8.deliveries,c1.deliveries,
      a16.deliveries,c2.deliveries,a24.deliveries,List.append_nil]
    norm_num [sourceTrain,List.ofFn_succ]
  · simp [e,Execution.emissions_append,c0.emissions,a8.emissions,c1.emissions,a16.emissions,c2.emissions,a24.emissions]
  · rw [a24.gain_preserved,c2.pulse.gain_target,hg16]; ring
  · intro p hp
    rw [a24.gain_preserved,c2.pulse.gain_other p hp,a16.gain_preserved,c1.pulse.gain_other p hp,
      a8.gain_preserved,c0.gain_other p hp]
  · rw [a24.recovery_preserved,c2.pulse.recovery_preserved,a16.recovery_preserved,
      c1.pulse.recovery_preserved,a8.recovery_preserved,c0.recovery_preserved]

theorem BirthWeakPrefix.error_dose {θ route born} (w : BirthWeakPrefix θ route born) :
    w.execution.ledger.error 0 0 = 9 / 5 := by
  have h := w.execution.gain_balance 0 0
  rw [w.gain_target] at h
  linarith

theorem BirthWeakPrefix.learned_gain {θ route born} (w : BirthWeakPrefix θ route born) :
    9 / 5 ≤ Real.exp (w.final.x 0 (.z 0)) ∧ Real.exp (w.final.x 0 (.z 0)) ≤ 2 := by
  have hz := ((w.birth.2.2 0).2.2.2.2 (0 : Port)).1
  simp only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] at hz
  apply learned_gain_bounds
  · rw [w.gain_target]; linarith [hz.1]
  · rw [w.gain_target]; linarith [hz.2]

end KernelR.Hybrid
