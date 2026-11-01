import KernelR.HybridLearnedFastEnd
import KernelR.HybridPrefixBeforeFlow
import KernelR.HybridPreparedSlowReturn

/-! Resume the actual retained sender suffix, then its prepared return and
quiet interval up to the next eight-gap source clock. -/
namespace KernelR.Hybrid

structure LearnedSenderReturnAtNext {θ : Fin 1 → Parameters} {s0 : Snapshot 1}
    (f : FirstLearnedFire θ (fun _ _ => []) s0 0 0) (fast : LearnedFastEnd f)
    {H : ℝ} (cut : fast.execution.BeforeFlowCut H) where
  returned : PreparedSlowReturn θ (fun _ _ => []) fast.final s0.time
  final : Snapshot 1
  wait : Execution θ (fun _ _ => []) returned.final final
  execution : Execution θ (fun _ _ => []) cut.state final
  reconstruct : execution = (Execution.cons (.flow cut.flow) cut.rest).append (returned.execution.append wait)
  final_eq : final = quietAt returned.final (s0.time + 8)
  date : final.time = s0.time + 8
  ready : ∀ j, ReadyCoordinates final j
  prepared : ∀ j, PreparedSection final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j p, final.raw j p = none
  pending : final.pending = []
  gains : ∀ j p, final.x j (.z p) = cut.state.x j (.z p)
  recovery : ∀ j, final.x j .b = cut.state.x j .b
  gains_source : ∀ j p, final.x j (.z p) = s0.x j (.z p)
  recovery_source : ∀ j, final.x j .b = s0.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (s0.time + 8)

/-- Local input/output tokens are empty here; the synchronous weave maintains
its separate exact global queue. No stronger firing deadline is required. -/
theorem learned_sender_return_at_next_exists {θ ε} {s0 : Snapshot 1}
    (hb : PhysicalBox θ ε) (f : FirstLearnedFire θ (fun _ _ => []) s0 0 0)
    (fast : LearnedFastEnd f) {H : ℝ} (cut : fast.execution.BeforeFlowCut H)
    (hs : PreparedSection s0 0) (hqueue : s0.pending = []) :
    Nonempty (LearnedSenderReturnAtNext f fast cut) := by
  let tail : Execution θ (fun _ _ => []) cut.state fast.final := .cons (.flow cut.flow) cut.rest
  have heTail : tail.ledger.emissions = [] := by
    have h : cut.cut.ledger.emissions ++ cut.rest.ledger.emissions = [] := cut.emissions.symm.trans fast.emissions
    change [] ++ cut.rest.ledger.emissions = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hdTail : tail.deliveries = [] := by
    have h : cut.cut.deliveries ++ cut.rest.deliveries = [] := cut.deliveries.symm.trans fast.deliveries
    change [] ++ cut.rest.deliveries = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hcutPhysical := cut.cut.physical_invariant hb f.physical
  have hcutRaw := cut.cut.raw_valid f.raw_valid
  have hcutGain : ∀ j p, cut.state.x j (.z p) = fast.final.x j (.z p) := by
    intro j p
    have h1 := cut.cut.gain_nondecreasing hb j p
    have h2 := tail.gain_nondecreasing hb j p
    have h3 := fast.gains j p
    linarith
  have hcutRecovery : ∀ j, cut.state.x j .b = fast.final.x j .b := by
    intro j
    have h1 := cut.cut.recovery_nondecreasing hb j
    have h2 := tail.recovery_nondecreasing hb j
    have h3 := fast.recovery j
    linarith
  have hB : 17999 / 100000 ≤ fast.final.x 0 .b ∧ fast.final.x 0 .b ≤ 18001 / 100000 := by
    rw [fast.recovery,f.recovery_preserved]
    exact hs.recovery
  have htime : fast.final.time = s0.time + f.latency + 1 := by rw [fast.date,f.date]
  have hpending : fast.final.pending = [] := by rw [fast.pending,f.pending,hqueue]; rfl
  obtain ⟨ret⟩ := prepared_slow_return_exists (route := fun _ _ => []) hb fast.final s0.time f.latency
    fast.physical fast.raw_valid fast.main_slow fast.charge hB
    (fun p => ⟨fast.auxiliary 0 p,fast.rest p⟩) fast.raw_none htime
    ⟨by linarith [f.early],f.deadline⟩ (by intro d hd; rw [hpending] at hd; contradiction)
  have hwait : ret.final.time < s0.time + 8 := by rw [ret.date]; linarith
  have hretPending : ret.final.pending = [] := ret.pending.trans hpending
  let waitFlow : Flow θ ret.final (quietAt ret.final (s0.time + 8)) := quietFlow ret.final hwait
    (fun j => (ret.ready j).ready) (fun j p => ((ret.ready j).auxiliary p).1) ret.raw_none
    (fun j => by linarith [(ret.ready j).charge.2])
    (fun j p => by linarith [((ret.ready j).auxiliary p).2.2])
    (by intro d hd; rw [hretPending] at hd; contradiction)
  let wait : Execution θ (fun _ _ => []) ret.final (quietAt ret.final (s0.time + 8)) := .cons (.flow waitFlow) (.nil _)
  let final := quietAt ret.final (s0.time + 8)
  let e := tail.append (ret.execution.append wait)
  have hfinalReady : ∀ j, ReadyCoordinates final j := fun j => quietAt_ready_coordinates ret.final j (ret.ready j) hwait.le
  have hfinalRaw : ∀ j p, final.raw j p = none := ret.raw_none
  have hfinalPending : final.pending = [] := hretPending
  have hcomplete : CompleteThrough e (s0.time + 8) := by
    refine ⟨rfl,?_,?_⟩
    · intro u
      apply ready_no_jump final (fun j => (hfinalReady j).ready)
        (fun j p => ((hfinalReady j).auxiliary p).1) hfinalRaw
      · intro j; linarith [(hfinalReady j).charge.2]
      · intro j p; linarith [((hfinalReady j).auxiliary p).2.2]
      · intro d hd; rw [hfinalPending] at hd; contradiction
    · intro d hd; rw [hfinalPending] at hd; contradiction
  refine ⟨{
    returned := ret
    final := final
    wait := wait
    execution := e
    reconstruct := rfl
    final_eq := rfl
    date := rfl
    ready := hfinalReady
    prepared := fun j => ⟨(hfinalReady j).ready,(hfinalReady j).charge,(ret.prepared j).recovery,(hfinalReady j).auxiliary⟩
    charge := ?_
    raw_none := hfinalRaw
    pending := hfinalPending
    gains := fun j p => (ret.gains j p).trans (hcutGain j p).symm
    recovery := fun j => (ret.recovery j).trans (hcutRecovery j).symm
    gains_source := fun j p => (ret.gains j p).trans ((fast.gains j p).trans (f.gain_preserved j p))
    recovery_source := fun j => (ret.recovery j).trans ((fast.recovery j).trans (f.recovery_preserved j))
    emissions := ?_
    deliveries := ?_
    physical := e.physical_invariant hb hcutPhysical
    raw_valid := e.raw_valid hcutRaw
    complete := hcomplete
  }⟩
  · change relax (1 / 2) (1 / 10) (ret.final.x 0 .q) ret.final.time (s0.time + 8) = 1 / 10
    rw [ret.charge]
    simp [relax]
  · simp only [e,wait,Execution.emissions_append,heTail,ret.emissions,Execution.ledger,Move.ledger,Flow.ledger,Ledger.zero,Ledger.add,List.nil_append]
  · simp only [e,wait,Execution.deliveries_append,hdTail,ret.deliveries,Execution.deliveries,Move.deliveries,List.nil_append]

end KernelR.Hybrid
