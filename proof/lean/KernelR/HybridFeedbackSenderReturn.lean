import KernelR.HybridFeedbackFireProjection
import KernelR.HybridPortFastCompletion
import KernelR.HybridPreparedSlowReturn

/-! The first reciprocal sender completes its actual SLOW return, reopens
at exact rest and waits physically until the next source clock352. -/
namespace KernelR.Hybrid

structure FeedbackSenderReturn {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    (f : FeedbackFirstFire w)
    (fast : PortFastCompletion f.parametersB (fun _ _ => []) f.localB 2) where
  returned : PreparedSlowReturn f.parametersB (fun _ _ => []) fast.final 344
  final : Snapshot 1
  wait : Execution f.parametersB (fun _ _ => []) returned.final final
  execution : Execution f.parametersB (fun _ _ => []) fast.final final
  reconstruct : execution = returned.execution.append wait
  final_eq : final = quietAt returned.final 352
  date : final.time = 352
  ready : ∀ j, ReadyCoordinates final j
  prepared : ∀ j, PreparedSection final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j p, final.raw j p = none
  pending : final.pending = []
  gains : ∀ j p, final.x j (.z p) = fast.final.x j (.z p)
  recovery : ∀ j, final.x j .b = fast.final.x j .b
  gains_fire : ∀ j p, final.x j (.z p) = f.localB.x j (.z p)
  recovery_fire : ∀ j, final.x j .b = f.localB.x j .b
  gains_weak : ∀ j p, final.x j (.z p) = w.final.x 1 (.z p)
  recovery_own : ∀ j, final.x j .b = start.x 1 .b
  gain_target : final.x 0 (.z 2) = start.x 1 (.z 2) + 9 / 5
  gain_other : ∀ p, p ≠ 2 → final.x 0 (.z p) = start.x 1 (.z p)
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant f.parametersB final
  raw_valid : RawValid final
  complete : CompleteThrough execution 352

/-- Construct the SLOW flow and real reopen from the sender's actual FAST
endpoint. Only the already proved first-FIRE bracket is needed. -/
theorem FeedbackFirstFire.sender_return_exists {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    (f : FeedbackFirstFire w) (hb : PhysicalBox θ ε)
    (fast : PortFastCompletion f.parametersB (fun _ _ => []) f.localB 2) :
    Nonempty (FeedbackSenderReturn f fast) := by
  have htime : fast.final.time = 344 + f.firing.latency + 1 := by
    rw [fast.date,f.localB_clock,f.date]
  have hB : 17999 / 100000 ≤ fast.final.x 0 .b ∧ fast.final.x 0 .b ≤ 18001 / 100000 := by
    rw [fast.recovery]
    exact f.localB_recovery_prepared 0
  have hqueue : fast.final.pending = [] := fast.pending.trans f.localB_pending
  obtain ⟨ret⟩ := prepared_slow_return_exists (route := fun _ _ => []) (f.localB_box hb) fast.final
    344 f.firing.latency fast.physical fast.raw_valid fast.main_slow fast.charge hB
    (fun p => ⟨fast.auxiliary 0 p,fast.rest p⟩) fast.raw_none htime
    ⟨by linarith [f.firing.early],f.firing.deadline⟩
    (by intro d hd; rw [hqueue] at hd; contradiction)
  have hwait : ret.final.time < (352 : ℝ) := by rw [ret.date]; norm_num
  have hpending : ret.final.pending = [] := ret.pending.trans hqueue
  let waitFlow : Flow f.parametersB ret.final (quietAt ret.final 352) :=
    quietFlow ret.final hwait (fun j => (ret.ready j).ready)
      (fun j p => ((ret.ready j).auxiliary p).1) ret.raw_none
      (fun j => by linarith [(ret.ready j).charge.2])
      (fun j p => by linarith [((ret.ready j).auxiliary p).2.2])
      (by intro d hd; rw [hpending] at hd; contradiction)
  let wait : Execution f.parametersB (fun _ _ => []) ret.final (quietAt ret.final 352) :=
    .cons (.flow waitFlow) (.nil _)
  let final := quietAt ret.final 352
  let e := ret.execution.append wait
  have hready : ∀ j, ReadyCoordinates final j :=
    fun j => quietAt_ready_coordinates ret.final j (ret.ready j) hwait.le
  have hraw : ∀ j p, final.raw j p = none := ret.raw_none
  have hfinalPending : final.pending = [] := hpending
  have hcharge : final.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (ret.final.x 0 .q) ret.final.time 352 = 1 / 10
    rw [ret.charge]
    simp [relax]
  have hgain : ∀ j p, final.x j (.z p) = fast.final.x j (.z p) := ret.gains
  have hrec : ∀ j, final.x j .b = fast.final.x j .b := ret.recovery
  have hcomplete : CompleteThrough e 352 := by
    refine ⟨rfl,?_,?_⟩
    · intro u
      apply ready_no_jump final (fun j => (hready j).ready)
        (fun j p => ((hready j).auxiliary p).1) hraw
      · intro j; linarith [(hready j).charge.2]
      · intro j p; linarith [((hready j).auxiliary p).2.2]
      · intro d hd; rw [hfinalPending] at hd; contradiction
    · intro d hd; rw [hfinalPending] at hd; contradiction
  refine ⟨{
    returned := ret, final := final, wait := wait, execution := e, reconstruct := rfl
    final_eq := rfl, date := rfl, ready := hready
    prepared := fun j => ⟨(hready j).ready,(hready j).charge,(ret.prepared j).recovery,(hready j).auxiliary⟩
    charge := hcharge, raw_none := hraw, pending := hfinalPending, gains := hgain, recovery := hrec
    gains_fire := fun j p => (hgain j p).trans (fast.gains j p)
    recovery_fire := fun j => (hrec j).trans (fast.recovery j)
    gains_weak := fun j p => (hgain j p).trans ((fast.gains j p).trans (f.localB_gains j p))
    recovery_own := fun j => (hrec j).trans ((fast.recovery j).trans (f.localB_recovery j))
    gain_target := (hgain 0 2).trans ((fast.gains 0 2).trans (f.localB_gain_target 0))
    gain_other := fun p hp => (hgain 0 p).trans ((fast.gains 0 p).trans (f.localB_gain_other 0 p hp))
    emissions := ?_, deliveries := ?_
    physical := e.physical_invariant (f.localB_box hb) fast.physical
    raw_valid := e.raw_valid fast.raw_valid, complete := hcomplete
  }⟩
  · change (ret.execution.append wait).ledger.emissions = []
    rw [Execution.emissions_append,ret.emissions]
    rfl
  · change (ret.execution.append wait).deliveries = []
    rw [Execution.deliveries_append,ret.deliveries]
    rfl

end KernelR.Hybrid
