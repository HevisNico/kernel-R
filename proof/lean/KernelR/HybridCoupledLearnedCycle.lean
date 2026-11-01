import KernelR.HybridTwoCellFirstFire
import KernelR.HybridRightClosedExecutionProduct
import KernelR.HybridLearnedSenderReturnAtNext
import KernelR.HybridShortLearnedCycle
import KernelR.HybridQuietWireArrival

/-! One fully constructed coupled teaching cycle, with independent own gains,
fresh contact jitter and an arbitrary exact future global queue. -/
namespace KernelR.Hybrid

noncomputable def coupledLocalA (s : Snapshot 2) : Snapshot 1 := s.cellProjection 0 []
noncomputable def coupledLocalB (s : Snapshot 2) : Snapshot 1 := s.cellProjection 1 []

private theorem coupled_prepared_projection {s : Snapshot 2} {i : Fin 2}
    (hs : PreparedSection s i) : PreparedSection (s.cellProjection i []) 0 :=
  ⟨hs.ready,hs.charge,hs.recovery,hs.auxiliary⟩

private theorem coupled_physical_old {θ fresh s} (hf : PhysicalInvariant (extendParameters θ fresh) s) :
    PhysicalInvariant θ (coupledLocalA s) := by
  have hθ : extendParameters θ fresh (0 : Fin 2) = θ (0 : Fin 1) := rfl
  refine ⟨fun j => hf.region 0,?_,fun j => hf.recovery_cap 0,fun j => hf.reserve 0⟩
  intro j p
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simpa only [coupledLocalA,Snapshot.cellProjection,hθ] using hf.gain_cap 0 p

private theorem coupled_physical_fresh {θ fresh s} (hf : PhysicalInvariant (extendParameters θ fresh) s) :
    PhysicalInvariant (fun _ : Fin 1 => fresh) (coupledLocalB s) := by
  have hθ : extendParameters θ fresh (1 : Fin 2) = fresh := rfl
  refine ⟨fun j => hf.region 1,?_,fun j => hf.recovery_cap 1,fun j => hf.reserve 1⟩
  intro j p
  have h := hf.gain_cap 1 p
  change s.x 1 (.z p) ≤ Real.log ((extendParameters θ fresh 1).cap p) at h
  rw [hθ] at h
  exact h

private theorem coupled_raw_projection {s : Snapshot 2} (hv : RawValid s) (i : Fin 2) :
    RawValid (s.cellProjection i []) := fun _ p origin h => hv i p origin h

private theorem coupled_snapshot_ext {n} (s u : Snapshot n)
    (ht : s.time = u.time) (hx : s.x = u.x) (hm : s.main = u.main)
    (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
  cases s
  cases u
  simp_all only

/-- Rebuild a real received state from its actual sender endpoint and the
receiver's current projection, without injecting either local queue. -/
theorem QuietWireArrival.product_receiver_projection {θA θB route sA sB uA Q p}
    (r : QuietWireArrival θA θB route sA sB uA Q p) :
    uA.product (r.final.cellProjection 1 []) Q = r.final := by
  apply coupled_snapshot_ext
  · exact r.date.symm
  · funext j
    by_cases hj : j = 0
    · subst j; exact r.sender_values.symm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; exact r.sender_main.symm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; funext q; exact (r.sender_aux q).symm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; funext q; exact (r.sender_raw q).symm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · exact r.pending.symm

structure CoupledLearnedCycle (θ : Fin 1 → Parameters) (fresh : Parameters)
    (forward backward : ℝ → ℝ) (source : Snapshot 2) where
  source_window : 184 ≤ source.time ∧ source.time ≤ 280
  source_charge : ∀ i, source.x i .q = 1 / 10
  senderFire : FirstLearnedFire θ (fun _ _ => []) (coupledLocalA source) 0 0
  senderFast : LearnedFastEnd senderFire
  cutH : senderFast.execution.BeforeFlowCut (senderFire.final.time + forward senderFire.final.time)
  wireReceipt : QuietWireArrival θ (fun _ : Fin 1 => fresh) (reciprocalEntryRouter forward backward)
    senderFire.final (quietAt (coupledLocalB source) senderFire.final.time) cutH.state source.pending 1
  senderReturn : LearnedSenderReturnAtNext senderFire senderFast cutH
  receiverCycle : ShortLearnedCycle (fun _ : Fin 1 => fresh) (wireReceipt.final.cellProjection 1 []) 1
  final : Snapshot 2
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) source final
  date : final.time = source.time + 8
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i p, final.raw i p = none
  pending : final.pending = source.pending
  gains : ∀ i p, final.x i (.z p) = source.x i (.z p)
  recovery : ∀ i, final.x i .b = source.x i .b
  sender_bounds : source.time + 2 / 5 < senderFire.final.time ∧ senderFire.final.time < source.time + 7 / 10
  emissions : execution.ledger.emissions = [(0,senderFire.final.time),(1,receiverCycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨1,1,cutH.state.time⟩]
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Construct one period-eight coupled response. The two outputs and the
single wire delivery are conclusions of the exhibited physical execution. -/
theorem coupled_learned_cycle_exists {θ fresh ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (source : Snapshot 2) (hf : PhysicalInvariant (extendParameters θ fresh) source) (hv : RawValid source)
    (htime : 184 ≤ source.time ∧ source.time ≤ 280)
    (hs : ∀ i, PreparedSection source i) (hq : ∀ i, source.x i .q = 1 / 10)
    (hGA : 9 / 5 ≤ Real.exp (source.x 0 (.z 0)) ∧ Real.exp (source.x 0 (.z 0)) ≤ 2)
    (hGB : 9 / 5 ≤ Real.exp (source.x 1 (.z 1)) ∧ Real.exp (source.x 1 (.z 1)) ≤ 11 / 5)
    (hr : source.raw 0 0 = some source.time)
    (ho : ∀ i p, i ≠ 0 ∨ p ≠ 0 → source.raw i p = none)
    (hp : ∀ d ∈ source.pending, source.time + 8 ≤ d.due)
    (forward backward : ℝ → ℝ)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (CoupledLearnedCycle θ fresh forward backward source) := by
  let sA := coupledLocalA source
  let sB := coupledLocalB source
  let route := reciprocalEntryRouter forward backward
  let Q := source.pending
  have hA : PreparedSection sA 0 := coupled_prepared_projection (hs 0)
  have hB : PreparedSection sB 0 := coupled_prepared_projection (hs 1)
  have hAr : ∀ j, ReadyCoordinates sA j := fun _ => ⟨hA.ready,hA.charge,hA.auxiliary⟩
  have hBr : ReadyCoordinates sB 0 := ⟨hB.ready,hB.charge,hB.auxiliary⟩
  have hrawA : sA.raw 0 0 = some sA.time := hr
  have hrawOtherA : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ 0 → sA.raw j p = none := by
    intro j p h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho 0 p (Or.inr (by simpa using h))
  have hrawB : ∀ p, sB.raw 0 p = none := fun p => ho 1 p (Or.inl (by decide))
  obtain ⟨a⟩ := first_learned_fire_exists (route := fun _ _ => []) sA hb.extend_old
    (coupled_physical_old hf) (coupled_raw_projection hv 0) 0 0 hAr hGA hrawA hrawOtherA
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  have hAupper : a.latency < 7 / 10 := a.deadline_seven_tenths hA.charge ⟨hGA.1,by
    change Real.exp (source.x 0 (.z 0)) ≤ 11 / 5
    linarith [hGA.2]⟩
  have hFA : a.final.time = source.time + a.latency := a.date
  have hFAearly : source.time + 2 / 5 < a.final.time :=
    readyPulse_root_after_four_tenths hA.charge.2 hGA.2 (by rw [hFA]; linarith [a.early]) a.response_root
  have hFAlate : a.final.time < source.time + 7 / 10 := by rw [hFA]; linarith
  have hQfire : ∀ d ∈ Q, a.before.time ≤ d.due := by
    intro d hd
    change a.final.time ≤ d.due
    linarith [hp d hd]
  have hsource : sA.product sB Q = source := source.cellProjection_product [] []
  obtain ⟨lifted,heL,hdL⟩ := a.beforeExecution.product_with_quiet_left (θB := fun _ : Fin 1 => fresh)
    a.before_emissions a.before_deliveries sB rfl hBr hrawB Q hQfire route
  let before := a.before.product (quietAt sB a.final.time) Q
  let after := a.final.product (quietAt sB a.final.time) (Q ++ route 0 a.final.time)
  let pre : Execution (extendParameters θ fresh) route source before := lifted.cast_source hsource.symm
  have hafter : after = {(setMain before 0 .fast) with pending := before.pending ++ route 0 before.time} := by
    dsimp [after,before]
    rw [a.final_empty,Snapshot.product_setMain_left]
    rfl
  let fire : Jump route before after := hafter.symm ▸ Jump.fire before 0 (a.firstSilent.main_ready 0) a.threshold
  have hFireEm : fire.ledger.emissions = [(0,a.final.time)] :=
    fire.ready_main_departure_emission 0 (a.firstSilent.main_ready 0) (by
      have hh : after.main 0 = .fast := a.main_fast
      rw [hh]; decide)
  have hFireDel : fire.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have h := fire.no_emissions_of_delivery d hd
    rw [hFireEm] at h
    contradiction
  let firing := pre.append (.cons (.jump fire) (.nil _))
  have hpreEm : pre.ledger.emissions = [] := by exact (congrArg (fun L : Ledger 2 => L.emissions) (lifted.cast_source_ledger hsource.symm)).trans heL
  have hpreDel : pre.deliveries = [] := (lifted.cast_source_deliveries hsource.symm).trans hdL
  have hfiringEm : firing.ledger.emissions = [(0,a.final.time)] := by
    simp only [firing,Execution.emissions_append,hpreEm,Execution.ledger,Move.ledger,hFireEm,Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
  have hfiringDel : firing.deliveries = [] := by
    simp only [firing,Execution.deliveries_append,hpreDel,Execution.deliveries,Move.deliveries,hFireDel,List.append_nil]
  obtain ⟨fast⟩ := a.learned_fast_end_exists hb.extend_old (hAr 0) hGA.2
    (fun p hp => hrawOtherA 0 p (Or.inr hp))
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let H := a.final.time + forward a.final.time
  obtain ⟨cut⟩ := fast.execution.before_flow_cut_exists H
    (by dsimp [H]; linarith [(hdelay a.final.time).1])
    (by rw [fast.date]; dsimp [H]; linarith [(hdelay a.final.time).2])
  have heCut : cut.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (cut.emissions.symm.trans fast.emissions)).1
  have hdCut : cut.cut.deliveries = [] := (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans fast.deliveries)).1
  have hBready := quietAt_ready_coordinates sB 0 hBr (by change source.time ≤ a.final.time; linarith)
  have hHupper : cut.state.time < source.time + 11 / 10 := by
    rw [cut.date]
    dsimp [H]
    linarith [(hdelay a.final.time).2]
  have hQH : ∀ d ∈ Q, cut.state.time ≤ d.due := by intro d hd; linarith [hp d hd]
  have hroute : route 0 a.final.time = [⟨1,1,cut.state.time⟩] := by
    classical
    change reciprocalEntryRouter forward backward 0 a.final.time = _
    rw [reciprocalEntryRouter.before_reverse forward backward 0 (by linarith [htime.2])]
    have hg : (160 : ℝ) ≤ a.final.time ∧ a.final.time < 310 := by constructor <;> linarith [htime.1,htime.2]
    rw [cut.date]
    simp [Contact.route,teachingContact,hg.1,hg.2,Contact.token,H]
  have hafterWire : after = a.final.product (quietAt sB a.final.time) (Q ++ [⟨1,1,cut.state.time⟩]) := by
    dsimp [after]
    rw [hroute]
  have hAfterPhys : PhysicalInvariant (extendParameters θ fresh)
      (a.final.product (quietAt sB a.final.time) (Q ++ [⟨1,1,cut.state.time⟩])) := by
    rw [← hafterWire]
    exact firing.physical_invariant hb hf
  have hAfterRaw : RawValid (a.final.product (quietAt sB a.final.time) (Q ++ [⟨1,1,cut.state.time⟩])) := by
    rw [← hafterWire]
    exact firing.raw_valid hv
  obtain ⟨receipt⟩ := quiet_wire_arrival_exists (θB := fun _ : Fin 1 => fresh) (route := route) hb
    cut.cut heCut hdCut (quietAt sB a.final.time) rfl hBready hrawB Q 1 hQH hAfterPhys hAfterRaw
  let inputB := receipt.final.cellProjection 1 []
  have hInputPhys : PhysicalInvariant (fun _ : Fin 1 => fresh) inputB := coupled_physical_fresh receipt.physical
  have hInputRaw : RawValid inputB := coupled_raw_projection receipt.raw_valid 1
  have hInputReady : ReadyCoordinates inputB 0 :=
    ⟨receipt.receiver_ready.ready,receipt.receiver_ready.charge,receipt.receiver_ready.auxiliary⟩
  have hInputRec : 17999 / 100000 ≤ inputB.x 0 .b ∧ inputB.x 0 .b ≤ 18001 / 100000 := by
    change 17999 / 100000 ≤ receipt.final.x 1 .b ∧ receipt.final.x 1 .b ≤ 18001 / 100000
    rw [receipt.receiver_values]
    exact hB.recovery
  have hInputPrepared : PreparedSection inputB 0 :=
    ⟨hInputReady.ready,hInputReady.charge,hInputRec,hInputReady.auxiliary⟩
  have hInputGain : 9 / 5 ≤ Real.exp (inputB.x 0 (.z 1)) ∧ Real.exp (inputB.x 0 (.z 1)) ≤ 11 / 5 := by
    change 9 / 5 ≤ Real.exp (receipt.final.x 1 (.z 1)) ∧ Real.exp (receipt.final.x 1 (.z 1)) ≤ 11 / 5
    rw [receipt.receiver_values]
    exact hGB
  have hInputFresh : inputB.raw 0 1 = some inputB.time := by
    change receipt.final.raw 1 1 = some receipt.final.time
    rw [receipt.date]
    exact receipt.raw_active
  have hInputOther : ∀ p, p ≠ 1 → inputB.raw 0 p = none := receipt.raw_other
  obtain ⟨bcycle⟩ := short_learned_cycle_exists hb.extend_new inputB 1 hInputPhys hInputRaw hInputPrepared
    hInputGain hInputFresh hInputOther (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  obtain ⟨returnedA⟩ := learned_sender_return_at_next_exists hb.extend_old a fast cut hA rfl
  have hBend : bcycle.returned.final.time < source.time + 8 := by
    rw [bcycle.date]
    change receipt.final.time + 69 / 10 < source.time + 8
    rw [receipt.date]
    linarith
  have hBpending : bcycle.returned.final.pending = [] := bcycle.pending
  let bWaitFlow : Flow (fun _ : Fin 1 => fresh) bcycle.returned.final (quietAt bcycle.returned.final (source.time + 8)) :=
    quietFlow bcycle.returned.final hBend (fun j => (bcycle.ready j).ready)
      (fun j p => ((bcycle.ready j).auxiliary p).1) bcycle.raw_none
      (fun j => by linarith [(bcycle.ready j).charge.2])
      (fun j p => by linarith [((bcycle.ready j).auxiliary p).2.2])
      (by intro d hd; rw [hBpending] at hd; contradiction)
  let bWait : Execution (fun _ : Fin 1 => fresh) (fun _ _ => []) bcycle.returned.final (quietAt bcycle.returned.final (source.time + 8)) :=
    .cons (.flow bWaitFlow) (.nil _)
  let bfinal := quietAt bcycle.returned.final (source.time + 8)
  let bexec := bcycle.execution.append bWait
  have heB : bexec.ledger.emissions = [(0,bcycle.fire.final.time)] := by
    change (bcycle.execution.append bWait).ledger.emissions = _
    rw [Execution.emissions_append,bcycle.emissions]
    rfl
  have hdB : bexec.deliveries = [] := by
    change (bcycle.execution.append bWait).deliveries = []
    rw [Execution.deliveries_append,bcycle.deliveries]
    rfl
  have hBfinalReady : ∀ j, ReadyCoordinates bfinal j :=
    fun j => quietAt_ready_coordinates bcycle.returned.final j (bcycle.ready j) hBend.le
  have hBfinalPrepared : PreparedSection bfinal 0 :=
    ⟨(hBfinalReady 0).ready,(hBfinalReady 0).charge,(bcycle.prepared 0).recovery,(hBfinalReady 0).auxiliary⟩
  have hBfinalCharge : bfinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (bcycle.returned.final.x 0 .q) bcycle.returned.final.time (source.time + 8) = _
    rw [bcycle.charge]
    simp [relax]
  have hstart : cut.state.time = inputB.time := receipt.date.symm
  have hfinish : returnedA.final.time = bfinal.time := returnedA.date
  have hQend : ∀ d ∈ Q, returnedA.final.time ≤ d.due := by rw [returnedA.date]; exact hp
  have hclosed : ∀ t, t ≤ bfinal.time → route 1 t = [] := by
    intro t ht
    change reciprocalEntryRouter forward backward 1 t = []
    rw [reciprocalEntryRouter.before_reverse forward backward 1 (by change t ≤ source.time + 8 at ht; linarith [htime.2])]
    simp [Contact.route,teachingContact]
  obtain ⟨woven,heW,hdW⟩ := returnedA.execution.product_right_closed bexec hstart hfinish
    returnedA.emissions returnedA.deliveries hdB Q hQend route hclosed
  let final := returnedA.final.product bfinal Q
  let tail : Execution (extendParameters θ fresh) route receipt.final final :=
    woven.cast_source receipt.product_receiver_projection.symm
  have heTail : tail.ledger.emissions = [(1,bcycle.fire.final.time)] := by
    have h := (congrArg (fun L : Ledger 2 => L.emissions)
      (woven.cast_source_ledger receipt.product_receiver_projection.symm)).trans heW
    rw [heB] at h
    exact h
  have hdTail : tail.deliveries = [] :=
    (woven.cast_source_deliveries receipt.product_receiver_projection.symm).trans hdW
  let wireTrace : Execution (extendParameters θ fresh) route after receipt.final :=
    receipt.execution.cast_source hafterWire
  have heWire : wireTrace.ledger.emissions = [] :=
    (congrArg (fun L : Ledger 2 => L.emissions) (receipt.execution.cast_source_ledger hafterWire)).trans receipt.emissions
  have hdWire : wireTrace.deliveries = [⟨1,1,cut.state.time⟩] :=
    (receipt.execution.cast_source_deliveries hafterWire).trans receipt.deliveries
  let trace := firing.append (wireTrace.append tail)
  have hem : trace.ledger.emissions = [(0,a.final.time),(1,bcycle.fire.final.time)] := by
    rw [Execution.emissions_append firing (wireTrace.append tail),hfiringEm,
      Execution.emissions_append wireTrace tail,heWire,heTail]
    rfl
  have hdel : trace.deliveries = [⟨1,1,cut.state.time⟩] := by
    rw [Execution.deliveries_append firing (wireTrace.append tail),hfiringDel,
      Execution.deliveries_append wireTrace tail,hdWire,hdTail]
    rfl
  refine ⟨{
    source_window := htime, source_charge := hq, senderFire := a, senderFast := fast, cutH := cut
    wireReceipt := receipt, senderReturn := returnedA, receiverCycle := bcycle
    final := final, execution := trace, date := returnedA.date
    prepared := ?_, charge := ?_, raw_none := ?_, pending := rfl
    gains := ?_, recovery := ?_, sender_bounds := ⟨hFAearly,hFAlate⟩
    emissions := hem, deliveries := hdel, physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv
  }⟩
  · intro i
    fin_cases i
    · exact ⟨(returnedA.prepared 0).ready,(returnedA.prepared 0).charge,(returnedA.prepared 0).recovery,(returnedA.prepared 0).auxiliary⟩
    · exact ⟨hBfinalPrepared.ready,hBfinalPrepared.charge,hBfinalPrepared.recovery,hBfinalPrepared.auxiliary⟩
  · intro i
    fin_cases i
    · exact returnedA.charge
    · exact hBfinalCharge
  · intro i p
    fin_cases i
    · exact returnedA.raw_none 0 p
    · exact bcycle.raw_none 0 p
  · intro i p
    fin_cases i
    · exact returnedA.gains_source 0 p
    · change bcycle.returned.final.x 0 (.z p) = source.x 1 (.z p)
      rw [bcycle.gains]
      change receipt.final.x 1 (.z p) = source.x 1 (.z p)
      rw [receipt.receiver_values]
      rfl
  · intro i
    fin_cases i
    · exact returnedA.recovery_source 0
    · change bcycle.returned.final.x 0 .b = source.x 1 .b
      rw [bcycle.recovery]
      change receipt.final.x 1 .b = source.x 1 .b
      rw [receipt.receiver_values]
      rfl

namespace CoupledLearnedCycle
variable {θ fresh forward backward source} (c : CoupledLearnedCycle θ fresh forward backward source)

noncomputable def wireTime : ℝ := c.cutH.state.time
noncomputable def fireA : ℝ := c.senderFire.final.time
noncomputable def fireB : ℝ := c.receiverCycle.fire.final.time

theorem wire_date : c.wireTime = c.fireA + forward c.fireA := c.cutH.date

theorem receiver_bounds : c.wireTime + 2 / 5 < c.fireB ∧ c.fireB < c.wireTime + 7 / 10 := by
  have h := c.receiverCycle.fire_bounds
  change c.wireReceipt.final.time + 2 / 5 < c.fireB ∧ c.fireB < c.wireReceipt.final.time + 7 / 10 at h
  rwa [c.wireReceipt.date] at h

theorem error_zero (i : Fin 2) (p : Port) : c.execution.ledger.error i p = 0 := by
  have h := c.execution.gain_balance i p
  rw [c.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : c.execution.ledger.recovery i = 0 := by
  have h := c.execution.recovery_balance i
  rw [c.recovery] at h
  linarith

/-- Saturation is deliberately conditional: a queued next A source due at
source+8 must still be consumed by the caller's genuine arrival jump. -/
theorem complete (hstrict : ∀ d ∈ source.pending, source.time + 8 < d.due) :
    CompleteThrough c.execution (source.time + 8) := by
  have hfuture : ∀ d ∈ c.final.pending, c.final.time < d.due := by
    intro d hd
    rw [c.pending] at hd
    rw [c.date]
    exact hstrict d hd
  refine ⟨c.date,?_,?_⟩
  · intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rw [(c.prepared i).ready,c.charge i]
        norm_num
      · intro i p
        rw [((c.prepared i).auxiliary p).1]
        linarith [((c.prepared i).auxiliary p).2.2]
    · intro i p origin hr
      rw [c.raw_none i p] at hr
      contradiction
    · exact hfuture
  · intro d hd
    rw [c.pending] at hd
    exact hstrict d hd

end CoupledLearnedCycle
end KernelR.Hybrid
