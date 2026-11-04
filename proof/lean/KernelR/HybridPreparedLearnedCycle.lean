import KernelR.HybridBirthPrepared40
import KernelR.HybridLearnedFastEnd
import KernelR.HybridPreparedSlowReturn

namespace KernelR.Hybrid

structure PreparedLearnedCycle (θ : Fin 1 → Parameters) (s : Snapshot 1) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  contacts_transversal : execution.ContactsTransversal
  date : final.time = s.time + 15 / 2
  ready : ∀ j, ReadyCoordinates final j
  prepared : ∀ j, PreparedSection final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j p, final.raw j p = none
  gains : ∀ j p, final.x j (.z p) = s.x j (.z p)
  recovery : ∀ j, final.x j .b = s.x j .b
  pending : final.pending = s.pending
  deliveries : execution.deliveries = []
  fire_time : ℝ
  fire_bounds : s.time + 2 / 5 < fire_time ∧ fire_time < s.time + 9 / 10
  emissions : execution.ledger.emissions = [(0,fire_time)]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (s.time + 15 / 2)

/-- Build a whole learned pulse from the current prepared coordinates. Its
firing root and all later returns are constructed, not supplied as a trace. -/
theorem prepared_learned_cycle_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : ∀ j, PreparedSection s j)
    (hg : 9 / 5 ≤ Real.exp (s.x 0 (.z 0)) ∧ Real.exp (s.x 0 (.z 0)) ≤ 2)
    (hr : s.raw 0 0 = some s.time) (ho : ∀ p, p ≠ 0 → s.raw 0 p = none)
    (hp : ∀ d ∈ s.pending, s.time + 8 ≤ d.due) : Nonempty (PreparedLearnedCycle θ s) := by
  have hready : ∀ j, ReadyCoordinates s j := fun j =>
    ⟨(hs j).ready,(hs j).charge,(hs j).auxiliary⟩
  have hrawOther : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ 0 → s.raw j p = none := by
    intro j p h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho p (by simpa using h)
  obtain ⟨fire⟩ := first_learned_fire_exists (route := fun _ _ => []) s hb hf hv 0 0
    hready hg hr hrawOther hp
  obtain ⟨fast⟩ := fire.learned_fast_end_exists hb (hready 0) hg.2 ho hp
  have hfastB : 17999 / 100000 ≤ fast.final.x 0 .b ∧ fast.final.x 0 .b ≤ 18001 / 100000 := by
    rw [fast.recovery,fire.recovery_preserved]
    exact (hs 0).recovery
  have hfastTime : fast.final.time = s.time + fire.latency + 1 := by
    rw [fast.date,fire.date]
  have hfastPending : ∀ d ∈ fast.final.pending, s.time + 8 ≤ d.due := by
    intro d hd
    rw [fast.pending,fire.pending] at hd
    simp only [List.append_nil] at hd
    exact hp d hd
  obtain ⟨ret⟩ := prepared_slow_return_exists (route := fun _ _ => []) hb fast.final s.time fire.latency
    fast.physical fast.raw_valid fast.main_slow fast.charge hfastB
    (fun p => ⟨fast.auxiliary 0 p,fast.rest p⟩) fast.raw_none hfastTime
    ⟨by linarith [fire.early],fire.deadline⟩ hfastPending
  let trace := (fire.execution.append fast.execution).append ret.execution
  have hfireLower : s.time + 2 / 5 < fire.final.time :=
    readyPulse_root_after_four_tenths (hs 0).charge.2 hg.2
      (by rw [fire.date]; linarith [fire.early]) fire.response_root
  refine ⟨{
    final := ret.final
    execution := trace
    contacts_transversal := by
      simp [trace, fire.contacts_transversal, fast.contacts_transversal, ret.contacts_transversal]
    date := ret.date
    ready := ret.ready
    prepared := ret.prepared
    charge := ret.charge
    raw_none := ret.raw_none
    gains := fun j p => (ret.gains j p).trans ((fast.gains j p).trans (fire.gain_preserved j p))
    recovery := fun j => (ret.recovery j).trans ((fast.recovery j).trans (fire.recovery_preserved j))
    pending := ?_
    deliveries := ?_
    fire_time := fire.final.time
    fire_bounds := ⟨hfireLower,by rw [fire.date]; linarith [fire.deadline]⟩
    emissions := ?_
    physical := ret.physical
    raw_valid := ret.raw_valid
    complete := ret.complete
  }⟩
  · rw [ret.pending,fast.pending,fire.pending]
    simp
  · simp only [trace,Execution.deliveries_append,fire.deliveries,fast.deliveries,
      ret.deliveries,List.append_nil]
  · simp only [trace,Execution.emissions_append,fire.emissions,fast.emissions,
      ret.emissions,List.append_nil,fire.date]

theorem PreparedLearnedCycle.error_zero {θ s} (c : PreparedLearnedCycle θ s) (p : Port) :
    c.execution.ledger.error 0 p = 0 := by
  have h := c.execution.gain_balance 0 p
  rw [c.gains] at h
  linarith

theorem PreparedLearnedCycle.recovery_zero {θ s} (c : PreparedLearnedCycle θ s) :
    c.execution.ledger.recovery 0 = 0 := by
  have h := c.execution.recovery_balance 0
  rw [c.recovery] at h
  linarith

end KernelR.Hybrid
