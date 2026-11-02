import KernelR.HybridTerminalHighContinuation
import KernelR.HybridIndexedWireDelay

/-! Connected finite reuse of two actual learned cells. The external queue
contains only leaf inputs. Receiver inputs are extracted from actual leaf
FIREs and issued globally by the causal weaver. Fixed positive wire delay
preserves arbitrary input spacing; no new local physical law is assumed.
-/
namespace KernelR.Hybrid

structure TwoCellHighRest (θ : Fin 2 → Parameters) (s : Snapshot 2) : Prop where
  physical : PhysicalInvariant θ s
  pending : s.pending = []
  cells : ∀ i, IsolatedHighRest (fun _ : Fin 1 => θ i) (cadenceActivePort 1 i)
    (s.autonomousView i)

noncomputable def twoCellHighLatency (s : Snapshot 2) (delay : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then highRestLatency (Real.exp (s.x 1 (.z 0))) + delay +
    highRestLatency (Real.exp (s.x 0 (.z 2)))
  else highRestLatency (Real.exp (s.x 1 (.z 0)))

noncomputable def twoCellHighSource (s : Snapshot 2) (first : ℝ) (later : List ℝ) : Snapshot 2 :=
  withFuture s ((first :: later).map (fun t => (⟨1,0,t⟩ : Delivery 2)))

/-- The learned leaf routes every genuine FIRE to the root; the root has no
outgoing wire. The positive fixed delay is independent of future input dates. -/
noncomputable def twoCellHighRouter (delay : ℝ) : Router 2 :=
  prependRouted (fun _ _ => []) (indexedHeadContact (0 : Fin 1) 2 (fun _ => delay))

private theorem high_schedule_terminal_mono {first later a b}
    (h : CadenceHighBudgetSchedule first later a) (hab : a ≤ b) :
    CadenceHighBudgetSchedule first later b := by
  induction later generalizing first with
  | nil => change first + 37 / 10 ≤ b; change first + 37 / 10 ≤ a at h; linarith
  | cons next later ih => exact ⟨h.1,ih h.2⟩

private theorem high_schedule_shift {first later terminal} (shift : ℝ)
    (h : CadenceHighBudgetSchedule first later (terminal-shift)) :
    CadenceHighBudgetSchedule (first+shift) (later.map (fun t => t+shift)) terminal := by
  induction later generalizing first with
  | nil => change first+shift+37/10≤terminal; change first+37/10≤terminal-shift at h; linarith
  | cons next later ih =>
    refine ⟨by change first+shift+37/10≤next+shift; linarith [h.1],ih h.2⟩

private theorem two_snapshot_eq {s u : Snapshot 2}
    (ht : s.time=u.time) (hx : s.x=u.x) (hm : s.main=u.main)
    (ha : s.aux=u.aux) (hr : s.raw=u.raw) (hp : s.pending=u.pending) : s=u := by
  cases s; cases u; simp_all only

structure TwoCellHighContinuation (θ : Fin 2 → Parameters) (s : Snapshot 2)
    (delay first : ℝ) (later : List ℝ) (terminal : ℝ) where
  final : Snapshot 2
  execution : Execution θ (twoCellHighRouter delay) (twoCellHighSource s first later) final
  date : final.time=terminal
  ready : ∀ i, ReadyCoordinates final i
  charge : ∀ i, final.x i .q=1/10
  raw_none : ∀ i p, final.raw i p=none
  pending : final.pending=[]
  gains : ∀ i p, final.x i (.z p)=s.x i (.z p)
  recovery : ∀ i, final.x i .b=s.x i .b
  calendar : ∀ i, execution.emissionTimes i=
    (first::later).map (fun t => t+twoCellHighLatency s delay i)
  physical : PhysicalInvariant θ final
  complete : CompleteThrough execution terminal

/-- The connected pair returns to its actual reusable high section. Sensor
residues and reserve are its evolved coordinates, never reference replacements. -/
theorem TwoCellHighContinuation.high_rest {θ s delay first later terminal}
    (c : TwoCellHighContinuation θ s delay first later terminal) (hs : TwoCellHighRest θ s) :
    TwoCellHighRest θ c.final := by
  refine ⟨c.physical,c.pending,?_⟩
  intro i
  refine ⟨Snapshot.autonomousView_physical c.physical i,?_,c.charge i,
    fun _ p => c.raw_none i p,?_,?_,?_⟩
  · intro j
    exact ⟨(c.ready i).ready,(c.ready i).charge,(c.ready i).auxiliary⟩
  · change cellQueue i c.final.pending=[]
    rw [c.pending]
    rfl
  · change 16/5≤Real.exp (c.final.x i (.z (cadenceActivePort 1 i))) ∧
      Real.exp (c.final.x i (.z (cadenceActivePort 1 i)))≤7/2
    rw [c.gains]
    exact (hs.cells i).gain
  · change 37999/100000≤c.final.x i .b ∧ c.final.x i .b≤38001/100000
    rw [c.recovery]
    exact (hs.cells i).recovery

/-- Every complete finite connected trace under the same fixed wire/router
has the constructed physical endpoint and the exact two response calendars. -/
theorem TwoCellHighContinuation.every_complete_execution {θ ε s delay first later terminal}
    (c : TwoCellHighContinuation θ s delay first later terminal)
    (hb : PhysicalBox θ ε) (hs : TwoCellHighRest θ s) {u}
    (e : Execution θ (twoCellHighRouter delay) (twoCellHighSource s first later) u)
    (hc : CompleteThrough e terminal) : c.final.ObservationalEq u ∧
      ∀ i, e.emissionTimes i=(first::later).map (fun t => t+twoCellHighLatency s delay i) := by
  have hf : PhysicalInvariant θ (twoCellHighSource s first later) :=
    ⟨hs.physical.region,hs.physical.gain_cap,hs.physical.recovery_cap,hs.physical.reserve⟩
  exact ⟨(c.execution.observational_unique e hb hf c.complete hc).1,
    fun i => (e.emissionTimes_unique c.execution hb hf hc c.complete i).trans (c.calendar i)⟩

/-- Both cells retain their actual terminal coordinates. Only the leaf has
external tokens; head analysis tokens are discharged by actual wire issuance.
The terminal budget includes the leaf latency and positive wire delay. -/
theorem two_cell_high_continuation_exists {θ ε s delay first later terminal}
    (hb : PhysicalBox θ ε) (hs : TwoCellHighRest θ s) (hd : 0<delay)
    (hfirst : s.time<first)
    (hSchedule : CadenceHighBudgetSchedule first later
      (terminal-(highRestLatency (Real.exp (s.x 1 (.z 0)))+delay))) :
    Nonempty (TwoCellHighContinuation θ s delay first later terminal) := by
  have hleaf : IsolatedHighRest (fun _ : Fin 1 => θ 1) 0 (s.autonomousView 1) := by
    simpa only [cadenceActivePort,Fin.val_one,ite_true] using hs.cells 1
  have hhead : IsolatedHighRest (fun _ : Fin 1 => θ 0) 2 (s.autonomousView 0) := by
    simpa only [cadenceActivePort,Fin.val_zero,show ¬(0=1 : Prop) by decide,ite_false] using hs.cells 0
  let latency := highRestLatency (Real.exp (s.x 1 (.z 0)))
  let shift := latency+delay
  have hlatency : 0<latency := by
    have h := (highRestLatency_spec hleaf.gain).1
    change 1/10<latency at h
    linarith
  have hshift : 0<shift := by dsimp [shift]; linarith
  have hleafSchedule : CadenceHighBudgetSchedule first later terminal :=
    high_schedule_terminal_mono hSchedule (by change terminal-shift≤terminal; linarith)
  obtain ⟨leaf⟩ := isolated_high_continuation_exists (autonomous_physical_box hb 1) hleaf
    hfirst hleafSchedule
  obtain ⟨head⟩ := isolated_high_continuation_exists (autonomous_physical_box hb 0) hhead
    (by change s.time<first+shift; linarith)
    (high_schedule_shift shift hSchedule)
  let leafSource := isolatedHighSource (s.autonomousView 1) 0 first later
  let headSource := isolatedHighSource (s.autonomousView 0) 2 (first+shift)
    (later.map (fun t => t+shift))
  let contacts := indexedHeadContact (0 : Fin 1) 2 (fun _ => delay)
  let Q := (first::later).map (fun t => (⟨1,0,t⟩ : Delivery 2))
  have hHeadQueue : headSource.pending=leaf.execution.headInputQueue contacts := by
    rw [Execution.headInputQueue_indexedContact,leaf.calendar]
    simp only [headSource,isolatedHighSource,withFuture,hhead.pending,List.append_nil,
      List.map_cons,List.map_map,Function.comp_def,Snapshot.autonomousView]
    congr 1
    · congr 1; dsimp [shift,latency]; ring
    · apply List.map_congr_left
      intro t ht
      congr 1
      dsimp [shift,latency]
      ring
  have hQ : leafSource.pending.map Delivery.succ=Q := by
    simp [leafSource,isolatedHighSource,withFuture,hleaf.pending,Q,List.map_map,
      Function.comp_def,Delivery.succ]
  have hbalance := HeadQueueBalance.initial leaf.execution headSource contacts hHeadQueue
  rw [hQ] at hbalance
  obtain ⟨weave⟩ := leaf.execution.prepend_causal_result head.execution rfl
    (leaf.date.trans head.date.symm) contacts (indexedHeadContact_strict 0 2 _ (fun _ => hd)) Q hbalance
  have hSource : leafSource.prependQueued headSource Q=twoCellHighSource s first later := by
    apply two_snapshot_eq
    · rfl
    · funext i p; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · funext i p; fin_cases i <;> rfl
    · funext i p; fin_cases i <;> rfl
    · simp [Snapshot.prependQueued,Snapshot.requeue,twoCellHighSource,withFuture,hs.pending,Q]
  have hParams : prependParameters (fun _ : Fin 1 => θ 0) (fun _ : Fin 1 => θ 1)=θ := by
    funext i
    fin_cases i <;> rfl
  let execution := (weave.execution.cast_source hSource.symm).cast_parameters hParams
  have hLedger : execution.ledger=weave.execution.ledger :=
    ((weave.execution.cast_source hSource.symm).cast_parameters_ledger hParams).trans
      (weave.execution.cast_source_ledger hSource.symm)
  have hTimes (i : Fin 2) : execution.emissionTimes i=weave.execution.emissionTimes i := by
    simp only [Execution.emissionTimes,hLedger]
  have hPending : weave.pending=[] := weave.pending_empty leaf.pending head.pending
  have hfinalPhysical : PhysicalInvariant θ (leaf.final.prependQueued head.final weave.pending) := by
    have hsourcePhysical : PhysicalInvariant θ (twoCellHighSource s first later) :=
      ⟨hs.physical.region,hs.physical.gain_cap,hs.physical.recovery_cap,hs.physical.reserve⟩
    exact execution.physical_invariant hb hsourcePhysical
  refine ⟨{
    final:=leaf.final.prependQueued head.final weave.pending,execution:=execution
    date:=leaf.date,ready:=?_,charge:=?_,raw_none:=?_,pending:=hPending
    gains:=?_,recovery:=?_,calendar:=?_,physical:=hfinalPhysical
    complete:=by simpa only [CompleteThrough,twoCellHighRouter] using weave.complete leaf.complete head.complete
  }⟩
  · intro i; fin_cases i
    · exact ⟨(head.ready 0).ready,(head.ready 0).charge,(head.ready 0).auxiliary⟩
    · exact ⟨(leaf.ready 0).ready,(leaf.ready 0).charge,(leaf.ready 0).auxiliary⟩
  · intro i; fin_cases i
    · exact head.charge
    · exact leaf.charge
  · intro i p; fin_cases i
    · exact head.raw_none 0 p
    · exact leaf.raw_none 0 p
  · intro i p; fin_cases i
    · exact head.gains 0 p
    · exact leaf.gains 0 p
  · intro i; fin_cases i
    · exact head.recovery 0
    · exact leaf.recovery 0
  · intro i; fin_cases i
    · rw [hTimes,weave.head_emission_times,head.calendar]
      simp only [List.map_cons,List.map_map,Function.comp_def,twoCellHighLatency,ite_true,
        Snapshot.autonomousView]
      congr 1
      · dsimp [shift,latency]; ring
      · apply List.map_congr_left
        intro t ht
        dsimp [shift,latency]
        ring
    · rw [hTimes,weave.tail_emission_times 0,leaf.calendar]
      rfl

/-- Actual common-birth two-cell endpoints supply the whole high section. -/
theorem ConstructedBirthCadenceChain.two_cell_high_rest {θ bornCells K sigma centre delay T}
    (c : @ConstructedBirthCadenceChain 1 θ bornCells K sigma centre delay T) :
    TwoCellHighRest θ c.final := ⟨c.physical,c.pending,c.terminal_high_rest⟩

/-- One fixed router can retain the entire earlier finite history and stay
connected for later high responses. This is a fixed function of clock time,
not a transition that resets or mutates any cell. -/
noncomputable def extendTwoCellRouter (old : Router 2) (cutoff delay : ℝ) : Router 2 :=
  fun i time => if time≤cutoff then old i time else twoCellHighRouter delay i time

private theorem two_high_latency_positive {θ s delay} (hs : TwoCellHighRest θ s)
    (hd : 0<delay) (i : Fin 2) : 0<twoCellHighLatency s delay i := by
  have hleaf : 16/5≤Real.exp (s.x 1 (.z 0)) ∧ Real.exp (s.x 1 (.z 0))≤7/2 := by
    simpa [cadenceActivePort,Snapshot.autonomousView] using (hs.cells 1).gain
  have hhead : 16/5≤Real.exp (s.x 0 (.z 2)) ∧ Real.exp (s.x 0 (.z 2))≤7/2 := by
    simpa [cadenceActivePort,Snapshot.autonomousView] using (hs.cells 0).gain
  have hl := (highRestLatency_spec hleaf).1
  have hh := (highRestLatency_spec hhead).1
  unfold twoCellHighLatency
  split_ifs <;> linarith

/-- All new FIREs are later than the original terminal clock. Hence this
connected continuation runs under the same fixed extended router as the
retargeted earlier birth history. -/
theorem TwoCellHighContinuation.extend_router_exists {θ s delay first later terminal}
    (c : TwoCellHighContinuation θ s delay first later terminal)
    (old : Router 2) (hs : TwoCellHighRest θ s) (hd : 0<delay)
    (hfirst : s.time<first) (hmin : ∀ t∈first::later, first≤t) :
    ∃ e : Execution θ (extendTwoCellRouter old s.time delay)
        (twoCellHighSource s first later) c.final,
      e.ledger=c.execution.ledger ∧ e.deliveries=c.execution.deliveries ∧
        CompleteThrough e terminal := by
  apply c.execution.retarget_router_complete _ _ c.complete
  intro event he
  have hmem : event.2∈c.execution.emissionTimes event.1 := by
    apply List.mem_map.mpr
    exact ⟨event,List.mem_filter.mpr ⟨he,by simp⟩,rfl⟩
  rw [c.calendar] at hmem
  obtain ⟨input,hi,hdate⟩ := List.mem_map.mp hmem
  have ht : s.time<event.2 := by
    have hp := two_high_latency_positive hs hd event.1
    linarith [hmin input hi]
  simp only [extendTwoCellRouter,show ¬event.2≤s.time by linarith,ite_false]

/-- An actual two-cell learned endpoint can be reused as a connected pair.
Only leaf inputs are externally queued, and both the old and new phases
admit the same fixed future-extended routing law. -/
theorem ConstructedBirthCadenceChain.connected_two_cell_high_continuation_exists
    {θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain 1 θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) (wire : ℝ) (hw : 0<wire)
    (first : ℝ) (later : List ℝ) (terminal : ℝ) (hfirst : c.final.time<first)
    (hSchedule : CadenceHighBudgetSchedule first later
      (terminal-(highRestLatency (Real.exp (c.final.x 1 (.z 0)))+wire))) :
    ∃ r : TwoCellHighContinuation θ c.final wire first later terminal,
      ∃ e : Execution θ (extendTwoCellRouter c.router c.final.time wire)
          (twoCellHighSource c.final first later) r.final,
        e.ledger=r.execution.ledger ∧ e.deliveries=r.execution.deliveries ∧
          CompleteThrough e terminal := by
  obtain ⟨r⟩ := two_cell_high_continuation_exists hb c.two_cell_high_rest hw hfirst hSchedule
  refine ⟨r,r.extend_router_exists c.router c.two_cell_high_rest hw hfirst ?_⟩
  intro time ht
  rcases List.mem_cons.mp ht with h | h
  · subst time; exact le_rfl
  · linarith [hSchedule.source_lower time h]

/-- Every actual old FIRE is at or before its proved endpoint, so extending
the future routing window preserves the entire birth-to-terminal history. -/
theorem ConstructedBirthCadenceChain.extended_two_cell_prefix_exists
    {θ bornCells K sigma centre delay T}
    (c : @ConstructedBirthCadenceChain 1 θ bornCells K sigma centre delay T) (wire : ℝ) :
    ∃ e : Execution θ (extendTwoCellRouter c.router c.final.time wire) c.source c.final,
      e.ledger=c.execution.ledger ∧ e.deliveries=c.execution.deliveries ∧ CompleteThrough e T := by
  apply c.execution.retarget_router_complete _ _ c.complete
  intro event he
  have ht := (c.execution.emission_time_bounds event he).2
  simp only [extendTwoCellRouter,ht,ite_true]

/-- One actual birth-to-new-terminal execution retains the original learned
history and then transmits the new irregular train through the connected pair.
Future external leaf tokens are present at birth, not inserted at the cut;
wire tokens are still issued only by the actual sending FIREs. -/
theorem ConstructedBirthCadenceChain.connected_two_cell_high_from_birth_exists
    {θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain 1 θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) (wire : ℝ) (hw : 0<wire)
    (first : ℝ) (later : List ℝ) (terminal : ℝ) (hfirst : c.final.time<first)
    (hSchedule : CadenceHighBudgetSchedule first later
      (terminal-(highRestLatency (Real.exp (c.final.x 1 (.z 0)))+wire))) :
    ∃ r : TwoCellHighContinuation θ c.final wire first later terminal,
      ∃ run : Execution θ (extendTwoCellRouter c.router c.final.time wire)
          (withFuture c.source ((first::later).map (fun t => (⟨1,0,t⟩ : Delivery 2)))) r.final,
        CompleteThrough run terminal ∧
          run.ledger=c.execution.ledger.add r.execution.ledger := by
  obtain ⟨prefix,hPrefix,_,_⟩ := c.extended_two_cell_prefix_exists wire
  obtain ⟨r,after,hAfter,_,hComplete⟩ :=
    c.connected_two_cell_high_continuation_exists hb wire hw first later terminal hfirst hSchedule
  let future := (first::later).map (fun t => (⟨1,0,t⟩ : Delivery 2))
  have hfuture : ∀ d∈future, c.final.time≤d.due := by
    intro d hd
    obtain ⟨time,ht,rfl⟩ := List.mem_map.mp hd
    change c.final.time≤time
    rcases List.mem_cons.mp ht with h | h
    · subst time; exact hfirst.le
    · linarith [hSchedule.source_lower time h]
  let before := prefix.withFuture future hfuture
  let run := before.append after
  refine ⟨r,run,by simpa only [CompleteThrough] using hComplete,?_⟩
  change (before.append after).ledger=_
  rw [Execution.append_ledger]
  change (prefix.withFuture future hfuture).ledger.add after.ledger=_
  rw [prefix.withFuture_ledger,hPrefix,hAfter]

#print axioms two_cell_high_continuation_exists
#print axioms ConstructedBirthCadenceChain.connected_two_cell_high_continuation_exists
#print axioms ConstructedBirthCadenceChain.extended_two_cell_prefix_exists
#print axioms ConstructedBirthCadenceChain.connected_two_cell_high_from_birth_exists

end KernelR.Hybrid
