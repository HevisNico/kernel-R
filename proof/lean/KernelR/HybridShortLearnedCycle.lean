import KernelR.HybridMidLearnedFire
import KernelR.HybridMidLearnedFastEnd
import KernelR.HybridShortPreparedReturn

/-! A complete learned pulse is constructed at its current port and gains,
including its true FIRE, FAST completion and short prepared return. -/
namespace KernelR.Hybrid
open MeasureTheory

structure ShortLearnedCycle (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port) where
  fire : FirstLearnedFire θ (fun _ _ => []) s 0 p
  fast : MidLearnedFastEnd fire
  returned : ShortPreparedReturn θ (fun _ _ => []) fast.final s.time
  execution : Execution θ (fun _ _ => []) s returned.final
  reconstruct : execution = (fire.execution.append fast.execution).append returned.execution
  contacts_transversal : execution.ContactsTransversal
  date : returned.final.time = s.time + 69 / 10
  ready : ∀ j, ReadyCoordinates returned.final j
  prepared : ∀ j, PreparedSection returned.final j
  charge : returned.final.x 0 .q = 1 / 10
  raw_none : ∀ j q, returned.final.raw j q = none
  gains : ∀ j q, returned.final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, returned.final.x j .b = s.x j .b
  pending : returned.final.pending = s.pending
  deliveries : execution.deliveries = []
  fire_bounds : s.time + 2 / 5 < fire.final.time ∧ fire.final.time < s.time + 7 / 10
  emissions : execution.ledger.emissions = [(0,fire.final.time)]
  error_zero : ∀ q, execution.ledger.error 0 q = 0
  mark_zero : ∀ q, execution.ledger.mark 0 q = 0
  physical : PhysicalInvariant θ returned.final
  raw_valid : RawValid returned.final
  complete : CompleteThrough execution (s.time + 69 / 10)

noncomputable def ShortLearnedCycle.final {θ s p} (c : ShortLearnedCycle θ s p) : Snapshot 1 := c.returned.final

noncomputable def ShortLearnedCycle.fire_time {θ s p} (c : ShortLearnedCycle θ s p) : ℝ := c.fire.final.time

theorem ShortLearnedCycle.final_eq {θ s p} (c : ShortLearnedCycle θ s p) : c.final = c.returned.final := rfl

/-- No reaching execution, firing date or pulse-case/count outcome is supplied.
All modes, roots and exact ledgers follow from the constructed three phases. -/
theorem short_learned_cycle_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : PreparedSection s 0)
    (hg : 9 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 11 / 5)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 31 / 4 ≤ d.due) :
    Nonempty (ShortLearnedCycle θ s p) := by
  have hready : ∀ j, ReadyCoordinates s j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ⟨hs.ready,hs.charge,hs.auxiliary⟩
  have hrawOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho q (by simpa using h)
  obtain ⟨fire⟩ := first_mid_learned_fire_exists (route := fun _ _ => []) s hb hf hv 0 p hready hg hr hrawOther hp
  obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists hb (hready 0) hg.2 ho hp
  have hdeadline : fire.latency < 7 / 10 := fire.deadline_seven_tenths hs.charge hg
  have hfastB : 17999 / 100000 ≤ fast.final.x 0 .b ∧ fast.final.x 0 .b ≤ 18001 / 100000 := by
    rw [fast.recovery,fire.recovery_preserved]
    exact hs.recovery
  have hfastTime : fast.final.time = s.time + fire.latency + 1 := by rw [fast.date,fire.date]
  have hfastPending : ∀ d ∈ fast.final.pending, s.time + 31 / 4 ≤ d.due := by
    intro d hd
    rw [fast.pending,fire.pending] at hd
    simp only [List.append_nil] at hd
    exact hp d hd
  obtain ⟨ret⟩ := short_prepared_return_exists (route := fun _ _ => []) hb fast.final s.time fire.latency
    fast.physical fast.raw_valid fast.main_slow fast.charge hfastB
    (fun q => ⟨fast.auxiliary 0 q,fast.rest q⟩) fast.raw_none hfastTime
    ⟨by linarith [fire.early],hdeadline⟩ hfastPending
  let trace := (fire.execution.append fast.execution).append ret.execution
  have hgains : ∀ j q, ret.final.x j (.z q) = s.x j (.z q) := fun j q =>
    (ret.gains j q).trans ((fast.gains j q).trans (fire.gain_preserved j q))
  have hrecovery : ∀ j, ret.final.x j .b = s.x j .b := fun j =>
    (ret.recovery j).trans ((fast.recovery j).trans (fire.recovery_preserved j))
  have herror : ∀ q, trace.ledger.error 0 q = 0 := by
    intro q
    have h := trace.gain_balance 0 q
    rw [hgains] at h
    linarith
  have hsum : (∑ q : Port, trace.ledger.mark 0 q) = 0 := by
    have h := trace.recovery_balance 0
    rw [hrecovery,trace.recovery_sum_marks] at h
    linarith
  have hdeliveries : trace.deliveries = [] := by
    simp only [trace,Execution.deliveries_append,fire.deliveries,fast.deliveries,ret.deliveries,List.append_nil]
  have hother : ∀ q, q ≠ p → trace.ledger.mark 0 q = 0 := by
    intro q hq
    have hno : NoArrivalAt trace 0 q := by simp [NoArrivalAt,hdeliveries]
    have hstates := trace.aux_ready_without_input_band 0 q (hs.auxiliary q).1
      (hs.auxiliary q).2.2 (ho q hq) hno
    exact trace.mark_zero_aux 0 q .ready (by decide) (trace.allStates_aux_flows 0 q .ready hstates)
  have hsumOnly : (∑ q : Port, trace.ledger.mark 0 q) = trace.ledger.mark 0 p :=
    Finset.sum_eq_single p (fun q _ hq => hother q hq) (by simp)
  have hpzero : trace.ledger.mark 0 p = 0 := by rw [hsumOnly] at hsum; exact hsum
  have hmark : ∀ q, trace.ledger.mark 0 q = 0 := by
    intro q
    by_cases hq : q = p
    · subst q; exact hpzero
    · exact hother q hq
  refine ⟨{
    fire := fire
    fast := fast
    returned := ret
    execution := trace
    reconstruct := rfl
    contacts_transversal := by
      simp [trace, fire.contacts_transversal, fast.contacts_transversal, ret.contacts_transversal]
    date := ret.date
    ready := ret.ready
    prepared := ret.prepared
    charge := ret.charge
    raw_none := ret.raw_none
    gains := hgains
    recovery := hrecovery
    pending := ?_
    deliveries := ?_
    fire_bounds := ?_
    emissions := ?_
    error_zero := herror
    mark_zero := hmark
    physical := ret.physical
    raw_valid := ret.raw_valid
    complete := ret.complete
  }⟩
  · rw [ret.pending,fast.pending,fire.pending]
    simp
  · simp only [trace,Execution.deliveries_append,fire.deliveries,fast.deliveries,ret.deliveries,List.append_nil]
  · have hl := readyPulse_mid_root_after_four_tenths hs.charge.2 hg.2
      (by linarith [fire.early] : s.time ≤ s.time + fire.latency) fire.response_root
    rw [fire.date]
    exact ⟨hl,by linarith⟩
  · simp only [trace,Execution.emissions_append,fire.emissions,fast.emissions,ret.emissions,List.append_nil,fire.date]

theorem ShortLearnedCycle.emission_count {θ s p} (c : ShortLearnedCycle θ s p) :
    c.execution.ledger.emissions.length = 1 := by rw [c.emissions]; rfl

end KernelR.Hybrid
