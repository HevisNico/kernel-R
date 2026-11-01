import KernelR.HybridPortFirstLearnedCut
import KernelR.HybridSameGainLatency
import KernelR.HybridRecoveryTrace

/-! The next real sender FIRE contacts the receiver on its retained low-recovery
SLOW path. Its charge and energy are carried by the same held flow. -/
namespace KernelR.Hybrid
open Set MeasureTheory

namespace PortFirstLearnedCut
variable {θS θR route source pS cycle pR delay}
  {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
  (p : PortFirstLearnedCut r later)

/-- Exact SLOW clock at a cut of the retained flow, including its endpoint. -/
theorem held_charge_clock {ε} (hb : PhysicalBox θR ε) (t : ℝ)
    (ht : p.lowSpan.final.time ≤ t) (hend : t ≤ p.fullLowSpan.final.time) :
    (p.heldFlow.at t).x 0 .q = (1 / 4 : ℝ) * Real.exp
      (-r.receiverLocal.x 0 .b * (t - (r.receiverLocal.time + p.fire.latency + 1))) := by
  have hrec : p.fullLowSpan.final.x 0 .b = p.lowSpan.final.x 0 .b :=
    (p.fullLowSpan.recovery 0).trans (p.lowSpan.recovery 0).symm
  have hconstant := p.heldFlow.recovery_constant_of_end hb 0 hrec
  have hI : (∫ v in p.lowSpan.final.time..t, p.heldFlow.path v 0 .b) =
      p.lowSpan.final.x 0 .b * (t - p.lowSpan.final.time) := by
    calc
      _ = ∫ _v in p.lowSpan.final.time..t, p.lowSpan.final.x 0 .b := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hmem : v ∈ Icc p.lowSpan.final.time t := by
          simpa only [uIcc_of_le ht] using hv
        exact hconstant v ⟨hmem.1,hmem.2.trans hend⟩
      _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]; ring
  have hq := p.heldFlow.slow_solution 0 p.lowSpan.main_slow t ⟨ht,hend⟩
  have hbLow : p.lowSpan.final.x 0 .b = r.receiverLocal.x 0 .b :=
    (p.lowSpan.recovery 0).trans ((p.fast.recovery 0).trans (p.fire.recovery_preserved 0))
  change p.heldFlow.path t 0 .q = _
  rw [hI,p.lowSpan.charge_clock,hbLow] at hq
  rw [hq,mul_assoc,← Real.exp_add,p.lowSpan.date]
  congr 2
  ring

/-- The actual receiving gap, rather than a prescribed charge, yields the
strict protected band. -/
theorem held_near_charge {ε} (hb : PhysicalBox θR ε) (t : ℝ)
    (ht : p.lowSpan.final.time ≤ t) (hend : t ≤ p.fullLowSpan.final.time)
    (hgap : r.receiverLocal.time + 79 / 10 ≤ t ∧ t ≤ r.receiverLocal.time + 81 / 10) :
    7 / 50 < (p.heldFlow.at t).x 0 .q ∧ (p.heldFlow.at t).x 0 .q < 4 / 25 := by
  rw [p.held_charge_clock hb t ht hend]
  exact variable_gap_first_slow_charge p.lowSpan.initial_low_b p.lowSpan.firing_bounds hgap

end PortFirstLearnedCut

structure PortSlowWire {θS θR route source pS cycle pR delay}
    {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
    (p : PortFirstLearnedCut r later) where
  nextCycle : ShortLearnedCycle θS (portSourceSender p.final) pS
  senderCut : nextCycle.fast.execution.BeforeFlowCut
    (nextCycle.fire.final.time + delay nextCycle.fire.final.time)
  receiverFlow : Flow θR p.lowSpan.final
    (p.heldFlow.at (nextCycle.fire.final.time + delay nextCycle.fire.final.time))
  final : Snapshot 2
  execution : Execution (extendParameters θS (θR 0)) route p.final final
  date : final.time = nextCycle.fire.final.time + delay nextCycle.fire.final.time
  firing_gap : nextCycle.fire.final.time = cycle.fire.final.time + 8
  receiving_gap : r.final.time + 79 / 10 ≤ final.time ∧ final.time ≤ r.final.time + 81 / 10
  pending : final.pending = later
  sender_values : final.x 0 = senderCut.state.x 0
  sender_main : final.main 0 = senderCut.state.main 0
  sender_aux : ∀ q, final.aux 0 q = senderCut.state.aux 0 q
  sender_raw : ∀ q, final.raw 0 q = senderCut.state.raw 0 q
  receiver_values : final.x 1 = (p.heldFlow.at final.time).x 0
  receiver_main_slow : final.main 1 = .slow
  receiver_aux_rest : ∀ q, final.aux 1 q = .ready ∧ RestBand (final.x 1 (.m q))
  receiver_sensor_rest : final.x 1 (.m pR) = 1 / 40
  receiver_charge : 7 / 50 < final.x 1 .q ∧ final.x 1 .q < 4 / 25
  raw_active : final.raw 1 pR = some final.time
  raw_other_receiver : ∀ q, q ≠ pR → final.raw 1 q = none
  gains : ∀ i q, final.x i (.z q) = p.final.x i (.z q)
  recovery : ∀ i, final.x i .b = p.final.x i .b
  emissions : execution.ledger.emissions = [(0,nextCycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨1,pR,final.time⟩]
  physical : PhysicalInvariant (extendParameters θS (θR 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

/-- The new source constructs its own resting response. Two actual equal-gain
roots and two independently sampled delays control the receiving gap. The
receiver follows the original held SLOW flow through the actual wire date. -/
theorem port_slow_wire_exists {θS θR ε route source pS cycle pR delay}
    {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
    (p : PortFirstLearnedCut r later) (hb : PhysicalBox (extendParameters θS (θR 0)) ε)
    (hg : 9 / 5 ≤ Real.exp (p.final.x 0 (.z pS)) ∧ Real.exp (p.final.x 0 (.z pS)) ≤ 2)
    (hqOld : source.x 0 .q = 1 / 10)
    (hQ : ∀ d ∈ later, p.final.time + 8 ≤ d.due)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5)
    (hroute : ∀ F, p.final.time + 2 / 5 < F → F < p.final.time + 7 / 10 →
      route 0 F = [⟨1,pR,F + delay F⟩]) :
    Nonempty (PortSlowWire p) := by
  have hbR : PhysicalBox θR ε := by
    refine ⟨hb.1,?_⟩
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb.2 1 q
  let sS := portSourceSender p.final
  have hfS : PhysicalInvariant θS sS := by
    refine ⟨fun _ => p.physical.region 0,?_,fun _ => p.physical.recovery_cap 0,fun _ => p.physical.reserve 0⟩
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact p.physical.gain_cap 0 q
  have hvS : RawValid sS := fun _ q origin h => p.raw_valid 0 q origin h
  have hsS : PreparedSection sS 0 :=
    ⟨p.sender_prepared.ready,p.sender_prepared.charge,p.sender_prepared.recovery,p.sender_prepared.auxiliary⟩
  have hrS : sS.raw 0 pS = some sS.time := by
    change p.final.raw 0 pS = some p.final.time
    rw [p.date]
    exact p.raw_active
  have hoS : ∀ q, q ≠ pS → sS.raw 0 q = none := p.raw_other_sender
  obtain ⟨next⟩ := short_learned_cycle_exists hb.extend_old sS pS hfS hvS hsS
    ⟨hg.1,by change Real.exp (p.final.x 0 (.z pS)) ≤ 11 / 5; linarith [hg.2]⟩ hrS hoS
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let F := next.fire.final.time
  let H := F + delay F
  have hF : p.final.time + 2 / 5 < F ∧ F < p.final.time + 7 / 10 := next.fire_bounds
  have hz : (portSourceSender source).x 0 (.z pS) = sS.x 0 (.z pS) :=
    ((p.sender_gains pS).trans (r.gains 0 pS)).symm
  have hFireGap : F = cycle.fire.final.time + 8 :=
    cycle.fire.firing_gap_eight_of_rest_gain next.fire hqOld p.sender_charge hz p.date
  have hGap : r.final.time + 79 / 10 ≤ H ∧ H ≤ r.final.time + 81 / 10 := by
    have h := received_gap_eight_of_fire_gap hFireGap (hdelay cycle.fire.final.time) (hdelay F)
    rw [r.date]
    constructor <;> dsimp [H] <;> linarith [h.1,h.2]
  have hFH : F < H := by dsimp [H]; linarith [(hdelay F).1]
  have hCF : p.lowSpan.final.time < F := by rw [p.lowSpan.date,← p.date]; linarith [hF.1]
  have hCH : p.lowSpan.final.time < H := hCF.trans hFH
  have hHT : H ≤ p.fullLowSpan.final.time := by rw [p.fullLowSpan.date]; exact hGap.2
  have hFT : F ≤ p.fullLowSpan.final.time := hFH.le.trans hHT
  let flowRH := p.heldFlow.prefix hCH hHT
  let flowRF := p.heldFlow.prefix hCF hFT
  let flowFH := flowRH.suffix hCF.le hFH
  let receiverF := p.heldFlow.at F
  let receiverH := p.heldFlow.at H
  let preR : Execution θR (fun _ _ => []) p.lowSpan.final receiverF := .cons (.flow flowRF) (.nil _)
  have hSource : sS.product p.lowSpan.final later = p.final := by
    have h := p.final.cellProjection_product [] []
    change (portSourceSender p.final).product (portSourceReceiver p.final) p.final.pending = p.final at h
    rw [p.receiver_local,p.pending] at h
    exact h
  have hQF : ∀ d ∈ later, next.fire.portBefore.time ≤ d.due := by
    intro d hd
    change F ≤ d.due
    linarith [hQ d hd,hF.2]
  obtain ⟨lifted,heL,hdL⟩ := next.fire.portBeforeExecution.product_neutral preR
    (by change p.final.time = p.lowSpan.final.time; rw [p.date,p.lowSpan.date]) rfl
    next.fire.portBefore_emissions next.fire.portBefore_deliveries rfl rfl later hQF route
  let before := next.fire.portBefore.product receiverF later
  let after := next.fire.final.product receiverF (later ++ route 0 F)
  let pre : Execution (extendParameters θS (θR 0)) route p.final before := lifted.cast_source hSource.symm
  have hafter : after = {setMain before 0 .fast with pending := before.pending ++ route 0 before.time} := by
    dsimp [after,before]
    rw [next.fire.port_final_empty,Snapshot.product_setMain_left]
    rfl
  let fire : Jump route before after := hafter.symm ▸
    Jump.fire before 0 (next.fire.firstSilent.main_ready 0) next.fire.threshold
  have heFire : fire.ledger.emissions = [(0,F)] :=
    fire.ready_main_departure_emission 0 (next.fire.firstSilent.main_ready 0)
      (by have h : after.main 0 = .fast := next.fire.main_fast; rw [h]; decide)
  have hdFire : fire.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have h := fire.no_emissions_of_delivery d hd
    rw [heFire] at h
    contradiction
  let firing := pre.append (.cons (.jump fire) (.nil _))
  have hePre : pre.ledger.emissions = [] := by rw [Execution.cast_source_ledger]; exact heL
  have hdPre : pre.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdL
  have heFiring : firing.ledger.emissions = [(0,F)] := by
    simp only [firing,Execution.emissions_append,hePre,Execution.ledger,Move.ledger,heFire,
      Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
  have hdFiring : firing.deliveries = [] := by
    simp only [firing,Execution.deliveries_append,hdPre,Execution.deliveries,Move.deliveries,hdFire,List.append_nil]
  obtain ⟨cut⟩ := next.fast.execution.before_flow_cut_exists H hFH.le
    (by rw [next.fast.date]; dsimp [H,F]; linarith [(hdelay next.fire.final.time).2])
  have heCut : cut.cut.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (cut.emissions.symm.trans next.fast.emissions)).1
  have hdCut : cut.cut.deliveries = [] :=
    (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans next.fast.deliveries)).1
  have hrouteF : route 0 F = [⟨1,pR,H⟩] := hroute F hF.1 hF.2
  have hAfter : after = next.fire.final.product receiverF (later ++ [⟨1,pR,H⟩]) := by
    dsimp [after]
    rw [hrouteF]
  have hQH : ∀ d ∈ later, H < d.due := by
    intro d hd
    have hH : H < p.final.time + 11 / 10 := by dsimp [H]; linarith [hF.2,(hdelay F).2]
    linarith [hQ d hd]
  let tailR : Execution θR (fun _ _ => []) receiverF receiverH := .cons (.flow flowFH) (.nil _)
  have hfuture : ∀ d ∈ later ++ [⟨1,pR,H⟩], cut.state.time ≤ d.due := by
    intro d hd
    rw [cut.date]
    rcases List.mem_append.mp hd with hd | hd
    · exact (hQH d hd).le
    · have he : d = (⟨1,pR,H⟩ : Delivery 2) := List.mem_singleton.mp hd
      subst d
      exact le_rfl
  obtain ⟨wireSpan,heW,hdW⟩ := cut.cut.product_neutral tailR rfl cut.date
    heCut hdCut rfl rfl (later ++ [⟨1,pR,H⟩]) hfuture route
  let beforeWire := cut.state.product receiverH (later ++ [⟨1,pR,H⟩])
  let final : Snapshot 2 := {setRaw beforeWire 1 pR (some beforeWire.time) with pending := later ++ []}
  have hfree : beforeWire.raw 1 pR = none := p.lowSpan.raw_none 0 pR
  let arrival : Jump route beforeWire final := .arrive beforeWire ⟨1,pR,H⟩ later [] rfl cut.date.symm hfree
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨1,pR,H⟩] := rfl
  let wire := wireSpan.append (.cons (.jump arrival) (.nil _))
  let wireTrace : Execution (extendParameters θS (θR 0)) route after final := wire.cast_source hAfter
  have heWire : wireTrace.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger]
    simp only [wire,Execution.emissions_append,heW,Execution.ledger,Move.ledger,haEm,
      Ledger.add,Ledger.zero,List.nil_append]
  have hdWire : wireTrace.deliveries = [⟨1,pR,H⟩] := by
    rw [Execution.cast_source_deliveries]
    simp only [wire,Execution.deliveries_append,hdW,Execution.deliveries,Move.deliveries,haDel,
      List.nil_append,List.append_nil]
  let trace := firing.append wireTrace
  let eRH : Execution θR (fun _ _ => []) p.lowSpan.final receiverH := .cons (.flow flowRH) (.nil _)
  have hRest : ∀ q, receiverH.aux 0 q = .ready ∧ RestBand (receiverH.x 0 (.m q)) := by
    intro q
    exact (eRH.aux_no_input_rest_band 0 q (p.lowSpan.auxiliary 0 q) (p.lowSpan.rest q)
      (p.lowSpan.raw_none 0 q) (by simp [NoArrivalAt,eRH,Execution.deliveries,Move.deliveries])).1
  have hGainR : ∀ q, receiverH.x 0 (.z q) = p.final.x 1 (.z q) := by
    intro q
    have h := (eRH.aux_no_input_rest_band 0 q (p.lowSpan.auxiliary 0 q) (p.lowSpan.rest q)
      (p.lowSpan.raw_none 0 q) (by simp [NoArrivalAt,eRH,Execution.deliveries,Move.deliveries])).2
    exact h.trans (congrFun p.receiver_values (.z q)).symm
  have hRecR : receiverH.x 0 .b = p.final.x 1 .b := by
    have he : p.fullLowSpan.final.x 0 .b = p.lowSpan.final.x 0 .b :=
      (p.fullLowSpan.recovery 0).trans (p.lowSpan.recovery 0).symm
    exact (p.heldFlow.recovery_constant_of_end hbR 0 he H ⟨hCH.le,hHT⟩).trans
      (congrFun p.receiver_values .b).symm
  have hSensor : receiverH.x 0 (.m pR) = 1 / 40 := by
    change p.heldFlow.path H 0 (.m pR) = 1 / 40
    have h := p.heldFlow.aux_ready_no_current_solution 0 pR (p.lowSpan.auxiliary 0 pR)
      (p.lowSpan.raw_none 0 pR) H ⟨hCH.le,hHT⟩
    rw [p.lowSpan.trained_rest] at h
    simpa only [sub_self,zero_mul,add_zero] using h
  have hCharge : 7 / 50 < receiverH.x 0 .q ∧ receiverH.x 0 .q < 4 / 25 :=
    p.held_near_charge hbR H hCH.le hHT hGap
  have hGainS : ∀ q, final.x 0 (.z q) = p.final.x 0 (.z q) := by
    intro q
    have h := cut.isPrefix.gain_eq_of_final hb.extend_old 0 q (next.fast.gains 0 q)
    exact h.trans (next.fire.gain_preserved 0 q)
  have hRecS : final.x 0 .b = p.final.x 0 .b := by
    have h := cut.isPrefix.recovery_eq_of_final hb.extend_old 0 (next.fast.recovery 0)
    exact h.trans (next.fire.recovery_preserved 0)
  have hRawS : ∀ q, final.raw 0 q = cut.state.raw 0 q := by
    intro q
    have h : beforeWire.raw 0 q = cut.state.raw 0 q := rfl
    simpa [final,setRaw,Function.update_apply] using h
  have hRawR : final.raw 1 pR = some final.time := by
    simp [final,setRaw,beforeWire,Snapshot.product]
  have hRawOther : ∀ q, q ≠ pR → final.raw 1 q = none := by
    intro q hq
    have h : beforeWire.raw 1 q = none := p.lowSpan.raw_none 0 q
    simpa [final,setRaw,Function.update_apply,hq] using h
  have hComplete : CompleteThrough trace final.time := by
    refine ⟨rfl,?_,?_⟩
    · intro u
      apply BeforeGuards.no_jump
      · constructor
        · intro i
          fin_cases i
          · exact cut.before_guards.1 0
          · change match receiverH.main 0 with
              | .ready => receiverH.x 0 .q < 1
              | .fast => 1 / 4 < receiverH.x 0 .q
              | .slow => 1 / 10 < receiverH.x 0 .q
            have hm : receiverH.main 0 = .slow := p.lowSpan.main_slow
            rw [hm]; linarith [hCharge.1]
        · intro i q
          fin_cases i
          · exact cut.before_guards.2 0 q
          · change match receiverH.aux 0 q with
              | .ready => receiverH.x 0 (.m q) < 1
              | .mark => 4 / 5 < receiverH.x 0 (.m q)
              | .silent => 1 / 10 < receiverH.x 0 (.m q)
              | .error => 1 / 40 < receiverH.x 0 (.m q)
            rw [(hRest q).1]; linarith [(hRest q).2.2]
      · intro i q origin hr
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · rw [hRawS] at hr
          exact cut.flow.initial_raw_strict 0 q origin hr
        · by_cases hq : q = pR
          · subst q
            have ho : origin = final.time := Option.some.inj (hr.symm.trans hRawR)
            rw [ho]; linarith
          · rw [hRawOther q hq] at hr; contradiction
      · intro d hd
        change d ∈ later ++ [] at hd
        simp only [List.append_nil] at hd
        change cut.state.time < d.due
        rw [cut.date]
        exact hQH d hd
    · intro d hd
      change d ∈ later ++ [] at hd
      simp only [List.append_nil] at hd
      change cut.state.time < d.due
      rw [cut.date]
      exact hQH d hd
  refine ⟨{
    nextCycle := next, senderCut := cut, receiverFlow := flowRH
    final := final, execution := trace, date := cut.date, firing_gap := hFireGap
    receiving_gap := ?_, pending := by simp [final]
    sender_values := rfl, sender_main := rfl, sender_aux := fun _ => rfl, sender_raw := hRawS
    receiver_values := ?_, receiver_main_slow := p.lowSpan.main_slow
    receiver_aux_rest := hRest, receiver_sensor_rest := hSensor, receiver_charge := hCharge
    raw_active := hRawR, raw_other_receiver := hRawOther, gains := ?_, recovery := ?_
    emissions := ?_, deliveries := ?_, physical := trace.physical_invariant hb p.physical
    raw_valid := trace.raw_valid p.raw_valid, complete := hComplete
  }⟩
  · change r.final.time + 79 / 10 ≤ cut.state.time ∧ cut.state.time ≤ r.final.time + 81 / 10
    rw [cut.date]
    exact hGap
  · change receiverH.x 0 = (p.heldFlow.at cut.state.time).x 0
    rw [cut.date]
  · intro i q
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hGainS q
    · exact hGainR q
  · intro i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hRecS
    · exact hRecR
  · rw [Execution.emissions_append,heFiring,heWire,List.append_nil]
  · rw [Execution.deliveries_append,hdFiring,hdWire,List.nil_append]
    change [⟨1,pR,H⟩] = ([⟨1,pR,cut.state.time⟩] : List (Delivery 2))
    rw [cut.date]

namespace PortSlowWire
variable {θS θR route source pS cycle pR delay}
  {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
  {p : PortFirstLearnedCut r later} (w : PortSlowWire p)

noncomputable def receiverLocal : Snapshot 1 := w.final.cellProjection 1 []

theorem receiver_local_physical : PhysicalInvariant θR w.receiverLocal := by
  refine ⟨fun _ => w.physical.region 1,?_,fun _ => w.physical.recovery_cap 1,
    fun _ => w.physical.reserve 1⟩
  intro j q
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact w.physical.gain_cap 1 q

theorem receiver_local_raw_valid : RawValid w.receiverLocal :=
  fun _ q origin h => w.raw_valid 1 q origin h

theorem product_receiver_projection :
    w.senderCut.state.product w.receiverLocal later = w.final := by
  have extensionality {n} (s u : Snapshot n) (ht : s.time = u.time) (hx : s.x = u.x)
      (hm : s.main = u.main) (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
    cases s
    cases u
    simp_all only
  apply extensionality
  · exact w.senderCut.date.trans w.date.symm
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact w.sender_values.symm
    · rfl
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact w.sender_main.symm
    · rfl
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · funext q; exact (w.sender_aux q).symm
    · rfl
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · funext q; exact (w.sender_raw q).symm
    · rfl
  · exact w.pending.symm

theorem error_zero (i : Fin 2) (q : Port) : w.execution.ledger.error i q = 0 := by
  have h := w.execution.gain_balance i q
  rw [w.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : w.execution.ledger.recovery i = 0 := by
  have h := w.execution.recovery_balance i
  rw [w.recovery] at h
  linarith

end PortSlowWire
end KernelR.Hybrid
