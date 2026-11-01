import KernelR.HybridFirstWiredArrival
import KernelR.HybridPreparedSlowReturn

namespace KernelR.Hybrid

/-- Exact list preservation, rather than only multiset balance, when no real
FIRE or arrival occurs in an actual execution. -/
theorem Execution.pending_eq_of_empty_events {n θ route s u} (e : @Execution n θ route s u)
    (he : e.ledger.emissions = []) (hd : e.deliveries = []) : u.pending = s.pending := by
  induction e with
  | nil => rfl
  | @cons s v u move rest ih =>
    change move.ledger.emissions ++ rest.ledger.emissions = [] at he
    change move.deliveries ++ rest.deliveries = [] at hd
    obtain ⟨heM,heR⟩ := List.append_eq_nil_iff.mp he
    obtain ⟨hdM,hdR⟩ := List.append_eq_nil_iff.mp hd
    rw [ih heR hdR]
    cases move with
    | flow f => exact f.queue_fixed
    | jump j =>
      cases j <;> simp_all [Move.ledger,Move.deliveries,Jump.ledger,Jump.deliveries,Ledger.zero,setMain,setAux,setRaw]

structure FirstSenderReturn {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (r : FirstWiredArrival b) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) r.cut.state final
  date : final.time = 168
  ready : ∀ j, ReadyCoordinates final j
  prepared : ∀ j, PreparedSection final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j p, final.raw j p = none
  pending : final.pending = sourceTrain 0 0 168 8 15
  gains : ∀ j p, final.x j (.z p) = r.cut.state.x j (.z p)
  recovery : ∀ j, final.x j .b = r.cut.state.x j .b
  gains_initial : ∀ p, final.x 0 (.z p) = b.final.x 0 (.z p)
  recovery_initial : final.x 0 .b = b.final.x 0 .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- Resume the actual sender flow retained at the wire cut, complete its FAST
phase and true SLOW return, then wait to the still-pending source168. -/
theorem FirstWiredArrival.first_sender_return_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (r : FirstWiredArrival b) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) :
    Nonempty (FirstSenderReturn r) := by
  let tail : Execution θ (fun _ _ => []) r.cut.state r.fast.final :=
    .cons (.flow r.cut.flow) r.cut.rest
  have heTail : tail.ledger.emissions = [] := by
    have h : r.cut.cut.ledger.emissions ++ r.cut.rest.ledger.emissions = [] :=
      r.cut.emissions.symm.trans r.fast.emissions
    change [] ++ r.cut.rest.ledger.emissions = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hdTail : tail.deliveries = [] := by
    have h : r.cut.cut.deliveries ++ r.cut.rest.deliveries = [] :=
      r.cut.deliveries.symm.trans r.fast.deliveries
    change [] ++ r.cut.rest.deliveries = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hcutPhysical := r.cut.cut.physical_invariant hb.extend_old r.fire.firelocal.physical
  have hcutRaw := r.cut.cut.raw_valid r.fire.firelocal.raw_valid
  have hcutGain : ∀ j p, r.cut.state.x j (.z p) = r.fast.final.x j (.z p) := by
    intro j p
    have h1 := r.cut.cut.gain_nondecreasing hb.extend_old j p
    have h2 := tail.gain_nondecreasing hb.extend_old j p
    have h3 := r.fast.gains j p
    linarith
  have hcutRecovery : ∀ j, r.cut.state.x j .b = r.fast.final.x j .b := by
    intro j
    have h1 := r.cut.cut.recovery_nondecreasing hb.extend_old j
    have h2 := tail.recovery_nondecreasing hb.extend_old j
    have h3 := r.fast.recovery j
    linarith
  have hB : 17999 / 100000 ≤ r.fast.final.x 0 .b ∧ r.fast.final.x 0 .b ≤ 18001 / 100000 := by
    rw [r.fast.recovery,r.fire.firelocal.recovery_preserved]
    exact b.a_prepared.recovery
  have htime : r.fast.final.time = 160 + r.fire.firelocal.latency + 1 := by
    rw [r.fast.date,r.fire.firelocal.date]
    change b.final.time + r.fire.firelocal.latency + 1 = _
    rw [b.date]
  have hfastPending : r.fast.final.pending = sourceTrain 0 0 168 8 15 := by
    rw [r.fast.pending,r.fire.firelocal.pending]
    simp only [List.append_nil]
    rfl
  have hfuture : ∀ d ∈ r.fast.final.pending, (160 : ℝ) + 8 ≤ d.due := by
    intro d hd
    rw [hfastPending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change (160 : ℝ) + 8 ≤ 168 + 8 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨ret⟩ := prepared_slow_return_exists (route := fun _ _ => []) hb.extend_old r.fast.final
    160 r.fire.firelocal.latency r.fast.physical r.fast.raw_valid r.fast.main_slow r.fast.charge hB
    (fun p => ⟨r.fast.auxiliary 0 p,r.fast.rest p⟩) r.fast.raw_none htime
    ⟨by linarith [r.fire.firelocal.early],r.fire.firelocal.deadline⟩ hfuture
  have hwait : ret.final.time < (168 : ℝ) := by rw [ret.date]; norm_num
  have hwaitFuture : ∀ d ∈ ret.final.pending, (168 : ℝ) ≤ d.due := by
    intro d hd
    rw [ret.pending] at hd
    have h := hfuture d hd
    norm_num at h
    exact h
  let waitFlow : Flow θ ret.final (quietAt ret.final 168) := quietFlow ret.final hwait
    (fun j => (ret.ready j).ready) (fun j p => ((ret.ready j).auxiliary p).1) ret.raw_none
    (fun j => by linarith [(ret.ready j).charge.2])
    (fun j p => by linarith [((ret.ready j).auxiliary p).2.2]) hwaitFuture
  let wait : Execution θ (fun _ _ => []) ret.final (quietAt ret.final 168) :=
    .cons (.flow waitFlow) (.nil _)
  let final := quietAt ret.final 168
  let e := tail.append (ret.execution.append wait)
  have hfinalReady : ∀ j, ReadyCoordinates final j :=
    fun j => quietAt_ready_coordinates ret.final j (ret.ready j) hwait.le
  refine ⟨{
    final := final
    execution := e
    date := rfl
    ready := hfinalReady
    prepared := fun j => ⟨(hfinalReady j).ready,(hfinalReady j).charge,(ret.prepared j).recovery,(hfinalReady j).auxiliary⟩
    charge := ?_
    raw_none := ret.raw_none
    pending := ret.pending.trans hfastPending
    gains := fun j p => (ret.gains j p).trans (hcutGain j p).symm
    recovery := fun j => (ret.recovery j).trans (hcutRecovery j).symm
    gains_initial := ?_
    recovery_initial := ?_
    emissions := ?_
    deliveries := ?_
    physical := e.physical_invariant hb.extend_old hcutPhysical
    raw_valid := e.raw_valid hcutRaw
  }⟩
  · change relax (1 / 2) (1 / 10) (ret.final.x 0 .q) ret.final.time 168 = 1 / 10
    rw [ret.charge]
    simp [relax]
  · intro p
    change ret.final.x 0 (.z p) = b.final.x 0 (.z p)
    rw [ret.gains,r.fast.gains,r.fire.firelocal.gain_preserved]
    rfl
  · change ret.final.x 0 .b = b.final.x 0 .b
    rw [ret.recovery,r.fast.recovery,r.fire.firelocal.recovery_preserved]
    rfl
  · simp only [e,wait,Execution.emissions_append,heTail,ret.emissions,Execution.ledger,
      Move.ledger,Flow.ledger,Ledger.zero,Ledger.add,List.nil_append]
  · simp only [e,wait,Execution.deliveries_append,hdTail,ret.deliveries,Execution.deliveries,
      Move.deliveries,List.nil_append]

end KernelR.Hybrid
