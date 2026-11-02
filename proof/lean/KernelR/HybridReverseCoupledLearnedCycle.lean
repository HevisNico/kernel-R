import KernelR.HybridCoupledLearnedCycle
import KernelR.HybridFirstReceiverFire
import KernelR.HybridIntervalClosedExecutionProduct
import KernelR.HybridQuietLeftWireArrival

/-! A constructed period-eight reverse cycle: Bport2 emits its actual token,
Aport2 receives it and responds, and both cells return before the next source. -/
namespace KernelR.Hybrid

private theorem reverse_prepared_projection {s : Snapshot 2} {i : Fin 2}
    (hs : PreparedSection s i) : PreparedSection (s.cellProjection i []) 0 :=
  ⟨hs.ready,hs.charge,hs.recovery,hs.auxiliary⟩

private theorem reverse_physical_old {θ fresh s} (hf : PhysicalInvariant (extendParameters θ fresh) s) :
    PhysicalInvariant θ (coupledLocalA s) := by
  refine ⟨fun _ => hf.region 0,?_,fun _ => hf.recovery_cap 0,fun _ => hf.reserve 0⟩
  intro j p
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact hf.gain_cap 0 p

private theorem reverse_physical_fresh {θ fresh s} (hf : PhysicalInvariant (extendParameters θ fresh) s) :
    PhysicalInvariant (fun _ : Fin 1 => fresh) (coupledLocalB s) := by
  refine ⟨fun _ => hf.region 1,?_,fun _ => hf.recovery_cap 1,fun _ => hf.reserve 1⟩
  intro j p
  exact hf.gain_cap 1 p

private theorem reverse_raw_projection {s : Snapshot 2} (hv : RawValid s) (i : Fin 2) :
    RawValid (s.cellProjection i []) := fun _ p origin h => hv i p origin h

/-- The receiver projection and actual sender cut reconstruct the whole
received state. Neither local queue is copied into the global queue. -/
theorem QuietLeftWireArrival.product_receiver_projection {θA θB route sA sB uB Q p}
    (r : QuietLeftWireArrival θA θB route sA sB uB Q p) :
    (r.final.cellProjection 0 []).product uB Q = r.final := by
  have extensionality {n} (s u : Snapshot n)
      (ht : s.time = u.time) (hx : s.x = u.x) (hm : s.main = u.main)
      (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
    cases s
    cases u
    simp_all only
  apply extensionality
  · rfl
  · funext j
    rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
    · rfl
    · exact r.sender_values.symm
  · funext j
    rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
    · rfl
    · exact r.sender_main.symm
  · funext j
    rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
    · rfl
    · funext q; exact (r.sender_aux q).symm
  · funext j
    rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
    · rfl
    · funext q; exact (r.sender_raw q).symm
  · exact r.pending.symm

structure ReverseCoupledLearnedCycle (θ : Fin 1 → Parameters) (fresh : Parameters)
    (forward backward : ℝ → ℝ) (source : Snapshot 2) where
  source_window : 376 ≤ source.time ∧ source.time ≤ 440
  source_charge : ∀ i, source.x i .q = 1 / 10
  senderCycle : ShortLearnedCycle (fun _ : Fin 1 => fresh) (coupledLocalB source) 2
  cutH : senderCycle.fast.execution.BeforeFlowCut
    (senderCycle.fire.final.time + backward senderCycle.fire.final.time)
  wireReceipt : QuietLeftWireArrival θ (fun _ : Fin 1 => fresh) (reciprocalEntryRouter forward backward)
    (quietAt (coupledLocalA source) senderCycle.fire.final.time) senderCycle.fire.final cutH.state source.pending 2
  receiverCycle : ShortLearnedCycle θ (wireReceipt.final.cellProjection 0 []) 2
  final : Snapshot 2
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) source final
  date : final.time = source.time + 8
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i p, final.raw i p = none
  pending : final.pending = source.pending
  gains : ∀ i p, final.x i (.z p) = source.x i (.z p)
  recovery : ∀ i, final.x i .b = source.x i .b
  sender_bounds : source.time + 2 / 5 < senderCycle.fire.final.time ∧
    senderCycle.fire.final.time < source.time + 7 / 10
  emissions : execution.ledger.emissions =
    [(1,senderCycle.fire.final.time),(0,receiverCycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨0,2,cutH.state.time⟩]
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- The supplied data are a current prepared physical section and its source
queue. Both firings, their wire and the returns are constructed from the ODE. -/
theorem reverse_coupled_learned_cycle_exists {θ fresh ε}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (source : Snapshot 2) (hf : PhysicalInvariant (extendParameters θ fresh) source) (hv : RawValid source)
    (htime : 376 ≤ source.time ∧ source.time ≤ 440)
    (hs : ∀ i, PreparedSection source i) (hq : ∀ i, source.x i .q = 1 / 10)
    (hGA : 9 / 5 ≤ Real.exp (source.x 0 (.z 2)) ∧ Real.exp (source.x 0 (.z 2)) ≤ 2)
    (hGB : 9 / 5 ≤ Real.exp (source.x 1 (.z 2)) ∧ Real.exp (source.x 1 (.z 2)) ≤ 2)
    (hr : source.raw 1 2 = some source.time)
    (ho : ∀ i p, i ≠ 1 ∨ p ≠ 2 → source.raw i p = none)
    (hp : ∀ d ∈ source.pending, source.time + 8 ≤ d.due)
    (forward backward : ℝ → ℝ)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReverseCoupledLearnedCycle θ fresh forward backward source) := by
  let sA := coupledLocalA source
  let sB := coupledLocalB source
  let route := reciprocalEntryRouter forward backward
  let Q := source.pending
  have hA : PreparedSection sA 0 := reverse_prepared_projection (hs 0)
  have hB : PreparedSection sB 0 := reverse_prepared_projection (hs 1)
  have hAr : ReadyCoordinates sA 0 := hA.ready_coordinates
  have hrawA : ∀ p, sA.raw 0 p = none := fun p => ho 0 p (Or.inl (by decide))
  have hrawB : sB.raw 0 2 = some sB.time := hr
  have hrawOtherB : ∀ p, p ≠ 2 → sB.raw 0 p = none := fun p hp => ho 1 p (Or.inr hp)
  obtain ⟨bcycle⟩ := short_learned_cycle_exists hb.extend_new sB 2
    (reverse_physical_fresh hf) (reverse_raw_projection hv 1) hB
    ⟨hGB.1,by change Real.exp (source.x 1 (.z 2)) ≤ 11 / 5; linarith [hGB.2]⟩ hrawB hrawOtherB
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let b := bcycle.fire
  have hFBearly : source.time + 2 / 5 < b.final.time := bcycle.fire_bounds.1
  have hFBlate : b.final.time < source.time + 7 / 10 := bcycle.fire_bounds.2
  have hFBstart : source.time < b.final.time := by linarith
  have hQfire : ∀ d ∈ Q, b.portBefore.time ≤ d.due := by
    intro d hd
    change b.final.time ≤ d.due
    linarith [hp d hd]
  let aquiet : Flow θ sA (quietAt sA b.final.time) := quietFlow sA hFBstart
    (by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hA.ready)
    (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact (hA.auxiliary p).1)
    (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hrawA p)
    (by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [hA.charge.2])
    (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hA.auxiliary p).2.2])
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let ae : Execution θ (fun _ _ => []) sA (quietAt sA b.final.time) := .cons (.flow aquiet) (.nil _)
  obtain ⟨lifted,heL,hdL⟩ := ae.product_neutral b.portBeforeExecution rfl rfl rfl rfl
    b.portBefore_emissions b.portBefore_deliveries Q hQfire route
  have hsource : sA.product sB Q = source := source.cellProjection_product [] []
  let before := (quietAt sA b.final.time).product b.portBefore Q
  let after := (quietAt sA b.final.time).product b.final (Q ++ route 1 b.final.time)
  let pre : Execution (extendParameters θ fresh) route source before := lifted.cast_source hsource.symm
  have hafter : after = {(setMain before 1 .fast) with pending := before.pending ++ route 1 before.time} := by
    dsimp [after,before]
    rw [b.port_final_empty,Snapshot.product_setMain_right]
    rfl
  let fire : Jump route before after := hafter.symm ▸ Jump.fire before 1 (b.firstSilent.main_ready 0) b.threshold
  have hFireEm : fire.ledger.emissions = [(1,b.final.time)] :=
    fire.ready_main_departure_emission 1 (b.firstSilent.main_ready 0) (by
      have hh : after.main 1 = .fast := b.main_fast
      rw [hh]; decide)
  have hFireDel : fire.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have h := fire.no_emissions_of_delivery d hd
    rw [hFireEm] at h
    contradiction
  let firing := pre.append (.cons (.jump fire) (.nil _))
  have hpreEm : pre.ledger.emissions = [] :=
    (congrArg (fun L : Ledger 2 => L.emissions) (lifted.cast_source_ledger hsource.symm)).trans heL
  have hpreDel : pre.deliveries = [] := (lifted.cast_source_deliveries hsource.symm).trans hdL
  have hfiringEm : firing.ledger.emissions = [(1,b.final.time)] := by
    simp only [firing,Execution.emissions_append,hpreEm,Execution.ledger,Move.ledger,hFireEm,
      Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
  have hfiringDel : firing.deliveries = [] := by
    simp only [firing,Execution.deliveries_append,hpreDel,Execution.deliveries,Move.deliveries,hFireDel,List.append_nil]
  let H := b.final.time + backward b.final.time
  obtain ⟨cut⟩ := bcycle.fast.execution.before_flow_cut_exists H
    (by dsimp [H]; linarith [(hdelay b.final.time).1])
    (by rw [bcycle.fast.date]; dsimp [H]; linarith [(hdelay b.final.time).2])
  have heCut : cut.cut.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (cut.emissions.symm.trans bcycle.fast.emissions)).1
  have hdCut : cut.cut.deliveries = [] :=
    (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans bcycle.fast.deliveries)).1
  have hAready := quietAt_ready_coordinates sA 0 hAr hFBstart.le
  have hHupper : cut.state.time < source.time + 11 / 10 := by
    rw [cut.date]
    dsimp [H]
    linarith [(hdelay b.final.time).2]
  have hQH : ∀ d ∈ Q, cut.state.time ≤ d.due := by intro d hd; linarith [hp d hd]
  have hroute : route 1 b.final.time = [⟨0,2,cut.state.time⟩] := by
    classical
    have ht : (320 : ℝ) ≤ b.final.time ∧ b.final.time < 470 := by
      constructor <;> linarith [htime.1,htime.2]
    rw [cut.date]
    simp [route,reciprocalEntryRouter,Contact.route,teachingContact,feedbackContact,Contact.token,ht.1,ht.2,H]
  have hafterWire : after = (quietAt sA b.final.time).product b.final (Q ++ [⟨0,2,cut.state.time⟩]) := by
    dsimp [after]
    rw [hroute]
  have hAfterPhys : PhysicalInvariant (extendParameters θ fresh)
      ((quietAt sA b.final.time).product b.final (Q ++ [⟨0,2,cut.state.time⟩])) := by
    rw [← hafterWire]
    exact firing.physical_invariant hb hf
  have hAfterRaw : RawValid ((quietAt sA b.final.time).product b.final (Q ++ [⟨0,2,cut.state.time⟩])) := by
    rw [← hafterWire]
    exact firing.raw_valid hv
  obtain ⟨receipt⟩ := quiet_left_wire_arrival_exists (θA := θ) (θB := fun _ : Fin 1 => fresh)
    (route := route) hb cut.cut heCut hdCut (quietAt sA b.final.time) rfl
    (by rw [cut.date]; dsimp [H]; linarith [(hdelay b.final.time).1])
    hAready hrawA rfl Q 2 hQH hAfterPhys hAfterRaw
  let inputA := receipt.final.cellProjection 0 []
  have hInputPhys : PhysicalInvariant θ inputA := reverse_physical_old receipt.physical
  have hInputRaw : RawValid inputA := reverse_raw_projection receipt.raw_valid 0
  have hInputReady : ReadyCoordinates inputA 0 :=
    ⟨receipt.receiver_ready.ready,receipt.receiver_ready.charge,receipt.receiver_ready.auxiliary⟩
  have hInputRec : 17999 / 100000 ≤ inputA.x 0 .b ∧ inputA.x 0 .b ≤ 18001 / 100000 := by
    change 17999 / 100000 ≤ receipt.final.x 0 .b ∧ receipt.final.x 0 .b ≤ 18001 / 100000
    rw [receipt.receiver_values]
    exact hA.recovery
  have hInputPrepared : PreparedSection inputA 0 :=
    ⟨hInputReady.ready,hInputReady.charge,hInputRec,hInputReady.auxiliary⟩
  have hInputGain : 9 / 5 ≤ Real.exp (inputA.x 0 (.z 2)) ∧ Real.exp (inputA.x 0 (.z 2)) ≤ 11 / 5 := by
    change 9 / 5 ≤ Real.exp (receipt.final.x 0 (.z 2)) ∧ Real.exp (receipt.final.x 0 (.z 2)) ≤ 11 / 5
    rw [receipt.receiver_values]
    exact ⟨hGA.1,by change Real.exp (source.x 0 (.z 2)) ≤ 11 / 5; linarith [hGA.2]⟩
  have hInputFresh : inputA.raw 0 2 = some inputA.time := by
    change receipt.final.raw 0 2 = some receipt.final.time
    rw [receipt.date]
    exact receipt.raw_active
  have hInputOther : ∀ p, p ≠ 2 → inputA.raw 0 p = none := receipt.raw_other
  obtain ⟨acycle⟩ := short_learned_cycle_exists hb.extend_old inputA 2 hInputPhys hInputRaw hInputPrepared
    hInputGain hInputFresh hInputOther (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let bTail : Execution (fun _ : Fin 1 => fresh) (fun _ _ => []) cut.state bcycle.fast.final :=
    .cons (.flow cut.flow) cut.rest
  have heBTail : bTail.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (cut.emissions.symm.trans bcycle.fast.emissions)).2
  have hdBTail : bTail.deliveries = [] :=
    (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans bcycle.fast.deliveries)).2
  have hBend : bcycle.returned.final.time < source.time + 8 := by rw [bcycle.date]; change source.time + 69 / 10 < _; linarith
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
  let bexec := bTail.append (bcycle.returned.execution.append bWait)
  have heB : bexec.ledger.emissions = [] := by
    rw [Execution.emissions_append,heBTail,Execution.emissions_append,bcycle.returned.emissions]
    rfl
  have hdB : bexec.deliveries = [] := by
    rw [Execution.deliveries_append,hdBTail,Execution.deliveries_append,bcycle.returned.deliveries]
    rfl
  have hAend : acycle.returned.final.time < source.time + 8 := by
    rw [acycle.date]
    change receipt.final.time + 69 / 10 < source.time + 8
    rw [receipt.date]
    linarith
  have hApending : acycle.returned.final.pending = [] := acycle.pending
  let aWaitFlow : Flow θ acycle.returned.final (quietAt acycle.returned.final (source.time + 8)) :=
    quietFlow acycle.returned.final hAend (fun j => (acycle.ready j).ready)
      (fun j p => ((acycle.ready j).auxiliary p).1) acycle.raw_none
      (fun j => by linarith [(acycle.ready j).charge.2])
      (fun j p => by linarith [((acycle.ready j).auxiliary p).2.2])
      (by intro d hd; rw [hApending] at hd; contradiction)
  let aWait : Execution θ (fun _ _ => []) acycle.returned.final (quietAt acycle.returned.final (source.time + 8)) :=
    .cons (.flow aWaitFlow) (.nil _)
  let afinal := quietAt acycle.returned.final (source.time + 8)
  let aexec := acycle.execution.append aWait
  have heA : aexec.ledger.emissions = [(0,acycle.fire.final.time)] := by
    rw [Execution.emissions_append,acycle.emissions]
    rfl
  have hdA : aexec.deliveries = [] := by
    rw [Execution.deliveries_append,acycle.deliveries]
    rfl
  have hstart : inputA.time = cut.state.time := receipt.date
  have hfinish : afinal.time = bfinal.time := rfl
  have hQend : ∀ d ∈ Q, afinal.time ≤ d.due := hp
  have hclosed : ∀ t, inputA.time ≤ t → t ≤ afinal.time → route 0 t = [] := by
    intro t hlo _
    have htimeA : (310 : ℝ) ≤ t := by
      change receipt.final.time ≤ t at hlo
      rw [receipt.date,cut.date] at hlo
      dsimp [H] at hlo
      linarith [htime.1,(hdelay b.final.time).1]
    classical
    have hn : ¬ t < (310 : ℝ) := by linarith
    simp [route,reciprocalEntryRouter,Contact.route,teachingContact,feedbackContact,hn]
  obtain ⟨woven,heW,hdW⟩ := aexec.product_left_closed_on bexec hstart hfinish hdA heB hdB Q hQend route hclosed
  let final := afinal.product bfinal Q
  let tail : Execution (extendParameters θ fresh) route receipt.final final :=
    woven.cast_source receipt.product_receiver_projection.symm
  have heTail : tail.ledger.emissions = [(0,acycle.fire.final.time)] := by
    have h := (congrArg (fun L : Ledger 2 => L.emissions)
      (woven.cast_source_ledger receipt.product_receiver_projection.symm)).trans heW
    rw [heA] at h
    exact h
  have hdTail : tail.deliveries = [] := (woven.cast_source_deliveries receipt.product_receiver_projection.symm).trans hdW
  let wireTrace : Execution (extendParameters θ fresh) route after receipt.final := receipt.execution.cast_source hafterWire
  have heWire : wireTrace.ledger.emissions = [] :=
    (congrArg (fun L : Ledger 2 => L.emissions) (receipt.execution.cast_source_ledger hafterWire)).trans receipt.emissions
  have hdWire : wireTrace.deliveries = [⟨0,2,cut.state.time⟩] :=
    (receipt.execution.cast_source_deliveries hafterWire).trans receipt.deliveries
  let trace := firing.append (wireTrace.append tail)
  have hem : trace.ledger.emissions = [(1,b.final.time),(0,acycle.fire.final.time)] := by
    rw [Execution.emissions_append firing (wireTrace.append tail),hfiringEm,
      Execution.emissions_append wireTrace tail,heWire,heTail]
    rfl
  have hdel : trace.deliveries = [⟨0,2,cut.state.time⟩] := by
    rw [Execution.deliveries_append firing (wireTrace.append tail),hfiringDel,
      Execution.deliveries_append wireTrace tail,hdWire,hdTail]
    rfl
  have hAreadyFinal : ∀ j, ReadyCoordinates afinal j :=
    fun j => quietAt_ready_coordinates acycle.returned.final j (acycle.ready j) hAend.le
  have hBreadyFinal : ∀ j, ReadyCoordinates bfinal j :=
    fun j => quietAt_ready_coordinates bcycle.returned.final j (bcycle.ready j) hBend.le
  have hAchargeFinal : afinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (acycle.returned.final.x 0 .q) acycle.returned.final.time (source.time + 8) = _
    rw [acycle.charge]
    simp [relax]
  have hBchargeFinal : bfinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (bcycle.returned.final.x 0 .q) bcycle.returned.final.time (source.time + 8) = _
    rw [bcycle.charge]
    simp [relax]
  refine ⟨{
    source_window := htime, source_charge := hq, senderCycle := bcycle, cutH := cut
    wireReceipt := receipt, receiverCycle := acycle, final := final, execution := trace
    date := rfl, prepared := ?_, charge := ?_, raw_none := ?_, pending := rfl
    gains := ?_, recovery := ?_, sender_bounds := bcycle.fire_bounds
    emissions := hem, deliveries := hdel, physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv
  }⟩
  · intro i
    fin_cases i
    · exact ⟨(hAreadyFinal 0).ready,(hAreadyFinal 0).charge,(acycle.prepared 0).recovery,(hAreadyFinal 0).auxiliary⟩
    · exact ⟨(hBreadyFinal 0).ready,(hBreadyFinal 0).charge,(bcycle.prepared 0).recovery,(hBreadyFinal 0).auxiliary⟩
  · intro i
    fin_cases i
    · exact hAchargeFinal
    · exact hBchargeFinal
  · intro i p
    fin_cases i
    · exact acycle.raw_none 0 p
    · exact bcycle.raw_none 0 p
  · intro i p
    fin_cases i
    · change acycle.returned.final.x 0 (.z p) = source.x 0 (.z p)
      rw [acycle.gains]
      change receipt.final.x 0 (.z p) = source.x 0 (.z p)
      rw [receipt.receiver_values]
      rfl
    · exact bcycle.gains 0 p
  · intro i
    fin_cases i
    · change acycle.returned.final.x 0 .b = source.x 0 .b
      rw [acycle.recovery]
      change receipt.final.x 0 .b = source.x 0 .b
      rw [receipt.receiver_values]
      rfl
    · exact bcycle.recovery 0

namespace ReverseCoupledLearnedCycle
variable {θ fresh forward backward source} (c : ReverseCoupledLearnedCycle θ fresh forward backward source)

noncomputable def wireTime : ℝ := c.cutH.state.time
noncomputable def fireB : ℝ := c.senderCycle.fire.final.time
noncomputable def fireA : ℝ := c.receiverCycle.fire.final.time

theorem wire_date : c.wireTime = c.fireB + backward c.fireB := c.cutH.date

theorem receiver_bounds : c.wireTime + 2 / 5 < c.fireA ∧ c.fireA < c.wireTime + 7 / 10 := by
  have h := c.receiverCycle.fire_bounds
  change c.wireReceipt.final.time + 2 / 5 < c.fireA ∧ c.fireA < c.wireReceipt.final.time + 7 / 10 at h
  rwa [c.wireReceipt.date] at h

theorem error_zero (i : Fin 2) (p : Port) : c.execution.ledger.error i p = 0 := by
  have h := c.execution.gain_balance i p
  rw [c.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : c.execution.ledger.recovery i = 0 := by
  have h := c.execution.recovery_balance i
  rw [c.recovery] at h
  linarith

theorem complete (hstrict : ∀ d ∈ source.pending, source.time + 8 < d.due) :
    CompleteThrough c.execution (source.time + 8) := by
  have hfuture : ∀ d ∈ c.final.pending, c.final.time < d.due := by
    intro d hd
    rw [c.pending,c.date] at *
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

end ReverseCoupledLearnedCycle
end KernelR.Hybrid
