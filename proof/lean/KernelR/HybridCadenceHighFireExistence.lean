import KernelR.HybridCadenceFirstStrongFireExistence
import KernelR.HybridCadenceHighTiming

/-! Construct high-gain cadence firing from its actual residual charge. The
high response has a different latency domain from FirstLearnedFire: it fires
before0.26, so it cannot inhabit that older type's latency>0.3 contract. -/
namespace KernelR.Hybrid
open Set

/-- Own four-dose log-gain supplies the high response's physical gain range. -/
theorem cadence_four_dose_gain_bounds {z : ℝ}
    (hz : Real.log (3 / 10) + 12 / 5 - 1 / 100000 ≤ z ∧
      z ≤ Real.log (3 / 10) + 12 / 5 + 1 / 100000) :
    16 / 5 ≤ Real.exp z ∧ Real.exp z ≤ 7 / 2 :=
  ⟨cadence_four_dose_gain_lower hz.1,
    (cadence_high_gain_bounds (by linarith [hz.1]) hz.2).2⟩

/-- The scalar crossing preserves the actual positive residual instead of
replacing it by the exact-rest reference. -/
theorem readyPulse_cadence_high_first_crossing {initial amplitude start : ℝ}
    (hq : 1 / 10 ≤ initial ∧ initial ≤ 8 / 25)
    (hg : 16 / 5 ≤ amplitude ∧ amplitude ≤ 7 / 2) :
    ∃ latency : ℝ, 4 / 25 < latency ∧ latency < 13 / 50 ∧
      readyPulse initial amplitude start (start + latency) = 1 ∧
      ∀ time ∈ Ico start (start + latency), readyPulse initial amplitude start time < 1 := by
  have hc : Continuous (fun time : ℝ => readyPulse initial amplitude start (start + time)) := by
    unfold readyPulse response
    fun_prop
  have hhigh : 1 < readyPulse initial amplitude start (start + 13 / 50) := by
    have hrest := readyPulse_high_rest_at_twenty_six hg.1
    have hmono := readyPulse_mono_initial (amplitude := amplitude) (start := start)
      (t := start + 13 / 50) hq.1
    have hshift : readyPulse (1 / 10) amplitude start (start + 13 / 50) =
        readyPulse (1 / 10) amplitude 0 (13 / 50) := by simp only [readyPulse,add_sub_cancel_left,sub_zero]
    rw [hshift] at hmono
    exact hrest.trans_le hmono
  obtain ⟨latency,hpos,hend,hroot,hprior⟩ := scalar_first_one_crossing hc
    (by norm_num : (0 : ℝ) < 13 / 50)
    (by rw [add_zero,readyPulse_initial]; linarith [hq.2]) hhigh
  have hearly : 4 / 25 < latency := by
    by_contra hn
    have hm := readyPulse_cadence_not_before_sixteen hq.2 hg.2
      (show start ≤ start + latency by linarith) (show start + latency ≤ start + 4 / 25 by linarith)
    rw [hroot] at hm
    exact lt_irrefl _ hm
  refine ⟨latency,hearly,hend,hroot,?_⟩
  intro time ht
  have h := hprior (time - start) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  simpa only [show start + (time - start) = time by ring] using h

/-- The high-gain contact is transverse with the actual residual charge. -/
theorem readyPulse_cadence_high_first_crossing_transversal {initial amplitude start : ℝ}
    (hq : 1 / 10 ≤ initial ∧ initial ≤ 8 / 25)
    (hg : 16 / 5 ≤ amplitude ∧ amplitude ≤ 7 / 2) :
    ∃ latency : ℝ, 4 / 25 < latency ∧ latency < 13 / 50 ∧
      readyPulse initial amplitude start (start + latency) = 1 ∧
      (∀ t ∈ Ico start (start + latency), readyPulse initial amplitude start t < 1) ∧
      0 < deriv (readyPulse initial amplitude start) (start + latency) := by
  obtain ⟨latency, early, deadline, root, prior⟩ :=
    readyPulse_cadence_high_first_crossing hq hg (start := start)
  have above : 1 < readyPulse initial amplitude start (start + 13 / 50) := by
    have higher := readyPulse_mono_initial (amplitude := amplitude) (start := start)
      (t := start + 13 / 50) hq.1
    have atRest := readyPulse_high_rest_at_twenty_six hg.1
    have shift : readyPulse (1 / 10) amplitude start (start + 13 / 50) =
        readyPulse (1 / 10) amplitude 0 (13 / 50) := by
      simp only [readyPulse, add_sub_cancel_left, sub_zero]
    rw [shift] at higher
    exact atRest.trans_le higher
  refine ⟨latency, early, deadline, root, prior, ?_⟩
  apply readyPulse_transversal_of_later_value (by linarith [hg.1] : 0 ≤ amplitude)
    (show start + latency < start + 13 / 50 by linarith)
  rwa [root]

#print axioms readyPulse_cadence_high_first_crossing_transversal

structure CadenceHighFire {n} (θ : Fin n → Parameters) (route : Router n)
    (s : Snapshot n) (i : Fin n) (p : Port) where
  firstMark : FirstInputMark θ s i p
  firstSilent : FirstInputSilent firstMark
  latency : ℝ
  early : 4 / 25 < latency
  deadline : latency < 13 / 50
  response_root : readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time (s.time + latency) = 1
  flow : Flow θ firstSilent.final (firstSilent.learnedFireBefore latency)
  threshold : (firstSilent.learnedFireBefore latency).x i .q = 1
  sensor_above_floor : 1 / 10 < (firstSilent.learnedFireBefore latency).x i (.m p)
  physical : PhysicalInvariant θ (firstSilent.learnedFireFinal route latency)
  raw_valid : RawValid (firstSilent.learnedFireFinal route latency)

noncomputable def CadenceHighFire.final {n θ route s i p} (c : @CadenceHighFire n θ route s i p) : Snapshot n :=
  c.firstSilent.learnedFireFinal route c.latency

noncomputable def CadenceHighFire.execution {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    Execution θ route s c.final :=
  (c.firstSilent.execution route).append (.cons (.flow c.flow)
    (.cons (.jump (.fire _ i (c.firstSilent.main_ready i) c.threshold)) (.nil _)))

theorem CadenceHighFire.date {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    c.final.time = s.time + c.latency := rfl

theorem CadenceHighFire.charge {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    c.final.x i .q = 1 := c.threshold

theorem CadenceHighFire.main_fast {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    c.final.main i = .fast := by simp [CadenceHighFire.final,FirstInputSilent.learnedFireFinal,setMain]

theorem CadenceHighFire.aux_silent {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    c.final.aux i p = .silent := c.firstSilent.aux_silent

theorem CadenceHighFire.main_other {n θ route s i p} (c : @CadenceHighFire n θ route s i p)
    (j : Fin n) (hj : j ≠ i) : c.final.main j = .ready := by
  simpa [CadenceHighFire.final,FirstInputSilent.learnedFireFinal,FirstInputSilent.learnedFireBefore,readyProtectedEnd,setMain,hj] using c.firstSilent.main_ready j

theorem CadenceHighFire.aux_other {n θ route s i p} (c : @CadenceHighFire n θ route s i p)
    (j : Fin n) (q : Port) (h : j ≠ i ∨ q ≠ p) : c.final.aux j q = .ready := c.firstSilent.aux_other j q h

theorem CadenceHighFire.sensor_above {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    1 / 10 < c.final.x i (.m p) := c.sensor_above_floor

theorem CadenceHighFire.pending {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    c.final.pending = s.pending ++ route i (s.time + c.latency) := rfl

theorem CadenceHighFire.gain_preserved {n θ route s i p} (c : @CadenceHighFire n θ route s i p)
    (j : Fin n) (q : Port) : c.final.x j (.z q) = s.x j (.z q) := rfl

theorem CadenceHighFire.recovery_preserved {n θ route s i p} (c : @CadenceHighFire n θ route s i p)
    (j : Fin n) : c.final.x j .b = s.x j .b := rfl

theorem CadenceHighFire.raw_active {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    c.final.raw i p = some s.time := c.firstSilent.raw_active

theorem CadenceHighFire.raw_other {n θ route s i p} (c : @CadenceHighFire n θ route s i p)
    (j : Fin n) (q : Port) (h : j ≠ i ∨ q ≠ p) : c.final.raw j q = none := c.firstSilent.raw_other j q h

theorem CadenceHighFire.emissions {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    c.execution.ledger.emissions = [(i,s.time + c.latency)] := by
  simp [CadenceHighFire.execution,FirstInputSilent.execution,FirstInputSilent.continuation,
    FirstInputMark.execution,Execution.emissions_append,Execution.ledger,Move.ledger,Flow.ledger,
    Jump.ledger,Ledger.add,Ledger.zero,FirstInputSilent.learnedFireBefore,readyProtectedEnd]

theorem CadenceHighFire.deliveries {n θ route s i p} (c : @CadenceHighFire n θ route s i p) :
    c.execution.deliveries = [] := by
  simp [CadenceHighFire.execution,FirstInputSilent.execution,FirstInputSilent.continuation,
    FirstInputMark.execution,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries]

theorem cadence_high_fire_exists {θ ε}
    (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (8 / 25))
    (hq : 1 / 10 ≤ s.x 0 .q)
    (hg : 16 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 7 / 2)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    Nonempty (CadenceHighFire θ (fun _ _ => []) s 0 p) := by
  have hm : ∀ j, s.main j = .ready := by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hs.ready
  have ha : ∀ j q, s.aux j q = .ready := by
    intro j q; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact (hs.auxiliary q).1
  have hq0 : ∀ j, s.x j .q < 1 := by
    intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [hs.charge.2]
  have hx0 : ∀ j q, s.x j (.m q) < 1 := by
    intro j q; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hs.auxiliary q).2.2]
  have hother : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.raw j q = none := by
    intro j q h; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact ho q (by simpa using h)
  have hmain : ∀ time, s.time ≤ time → time ≤ s.time + 1 / 10 →
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time time < 1 := by
    intro time hl hu
    exact readyPulse_cadence_not_before_sixteen hs.charge.2 hg.2 hl (by linarith)
  obtain ⟨f⟩ := first_input_mark_of_response_margin_until_exists s hb 0 p hm ha hr hother hq0 hx0
    hmain (hs.auxiliary p).2 (fun d hd => by linarith [hp d hd])
  obtain ⟨g⟩ := f.first_silent_of_response_margin_until_exists hb hmain
    (fun d hd => by linarith [hp d hd])
  obtain ⟨latency,hearly,hdeadline,hroot,hprior⟩ := readyPulse_cadence_high_first_crossing ⟨hq,hs.charge.2⟩ hg
  let T := s.time + latency
  have hT : g.final.time < T := by rw [g.date]; dsimp [T]; linarith [g.deadline]
  have hstart : s.time ≤ g.final.time := by
    have h := g.flow.positive
    change s.time + f.latency < g.final.time at h
    linarith [f.early]
  have hrawSupport : ∀ origin, some s.time = some origin → origin ≤ g.final.time ∧ T ≤ origin + 1 := by
    intro origin he
    have h := (Option.some.inj he).symm
    subst origin
    exact ⟨hstart,by dsimp [T]; linarith⟩
  have hq : ∀ time ∈ Ico g.final.time T, readyPulse (g.final.x 0 .q)
      (Real.exp (g.final.x 0 (.z p)) * rawInputScale (some s.time) g.final.time) g.final.time time < 1 := by
    intro time ht
    rw [g.response_restart]
    exact hprior time ⟨hstart.trans ht.1,ht.2⟩
  have hschedule := protected_decay_schedule (initial := (4 / 5 : ℝ)) (floor := (1 / 10 : ℝ))
    (by norm_num) (by norm_num) (hb.rates_positive 0 p).2.1
  have hratio : Real.log ((4 / 5 : ℝ) / (1 / 10)) / (θ 0).ls p = Real.log 8 / (θ 0).ls p := by norm_num
  have hguard : ∀ time ∈ Icc g.final.time T,
      1 / 10 < (4 / 5 : ℝ) * Real.exp (-(θ 0).ls p * (time - g.final.time)) := by
    intro time ht
    apply hschedule.2.2 (time - g.final.time) (by linarith [ht.1])
    rw [hratio]
    have he := (g.errorDate_bounds hb).1
    change s.time + 99 / 100 < g.final.time + Real.log 8 / (θ 0).ls p at he
    dsimp [T] at ht
    linarith [ht.2]
  have hx : ∀ time ∈ Ico g.final.time T, (if AuxMode.silent = .mark then (4 / 5 : ℝ) else 1 / 10) <
      g.final.x 0 (.m p) * Real.exp (-protectedReadyRate (θ 0) p .silent * (time - g.final.time)) := by
    intro time ht
    simpa only [reduceCtorEq,ite_false,g.sensor_charge,protectedReadyRate] using hguard time ⟨ht.1,ht.2.le⟩
  let flow := readyProtectedFlow g.final 0 p .silent (some s.time) hT (Or.inr rfl)
    g.main_ready g.aux_silent g.aux_other g.raw_active g.raw_other hrawSupport g.main_below g.aux_below hq hx
    (fun d hd => by change d ∈ s.pending at hd; dsimp [T]; linarith [hp d hd])
  have hthreshold : (g.learnedFireBefore latency).x 0 .q = 1 := by
    simp only [FirstInputSilent.learnedFireBefore,readyProtectedEnd,readyProtectedValues,protectedRawAmplitude,ite_true]
    rw [g.response_restart]
    exact hroot
  let endBefore := g.learnedFireBefore latency
  let endFinal := g.learnedFireFinal (fun _ _ => []) latency
  let execution : Execution θ (fun _ _ => []) s endFinal := (g.execution (fun _ _ => [])).append
    (.cons (.flow flow) (.cons (.jump (.fire endBefore 0 (g.main_ready 0) hthreshold)) (.nil _)))
  refine ⟨{
    firstMark := f, firstSilent := g, latency := latency
    early := by linarith, deadline := hdeadline, response_root := hroot
    flow := flow, threshold := hthreshold, sensor_above_floor := ?_
    physical := execution.physical_invariant hb hf, raw_valid := execution.raw_valid hv
  }⟩
  simpa [FirstInputSilent.learnedFireBefore,readyProtectedEnd,readyProtectedValues,protectedReadyRate,g.sensor_charge]
    using hguard T ⟨hT.le,le_rfl⟩

noncomputable def CadenceHighFire.portBefore {n θ s i p}
    (f : @CadenceHighFire n θ (fun _ _ => []) s i p) : Snapshot n :=
  f.firstSilent.learnedFireBefore f.latency

noncomputable def CadenceHighFire.portBeforeExecution {n θ s i p}
    (f : @CadenceHighFire n θ (fun _ _ => []) s i p) : Execution θ (fun _ _ => []) s f.portBefore :=
  (f.firstSilent.execution (fun _ _ => [])).append (.cons (.flow f.flow) (.nil _))

theorem CadenceHighFire.portBefore_emissions {n θ s i p}
    (f : @CadenceHighFire n θ (fun _ _ => []) s i p) :
    f.portBeforeExecution.ledger.emissions = [] := by
  simp [portBeforeExecution,FirstInputSilent.execution,FirstInputSilent.continuation,
    FirstInputMark.execution,Execution.emissions_append,Execution.ledger,Move.ledger,
    Flow.ledger,Jump.ledger,Ledger.add,Ledger.zero]

theorem CadenceHighFire.portBefore_deliveries {n θ s i p}
    (f : @CadenceHighFire n θ (fun _ _ => []) s i p) : f.portBeforeExecution.deliveries = [] := by
  simp [portBeforeExecution,FirstInputSilent.execution,FirstInputSilent.continuation,
    FirstInputMark.execution,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries]

theorem CadenceHighFire.port_final_empty {n θ s i p}
    (f : @CadenceHighFire n θ (fun _ _ => []) s i p) :
    f.final = setMain f.portBefore i .fast := by
  simp only [final,FirstInputSilent.learnedFireFinal,List.append_nil,portBefore]
  rfl

namespace CadenceHighFire
variable {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
  (fire : CadenceHighFire θ (fun _ _ => []) s 0 p)

theorem window : s.time + 4 / 25 < fire.final.time ∧ fire.final.time < s.time + 13 / 50 := by
  rw [fire.date]
  constructor <;> linarith [fire.early,fire.deadline]

theorem latency_le_rest (hq : 1 / 10 ≤ s.x 0 .q)
    (hg : 16 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 7 / 2) :
    fire.latency ≤ highRestLatency (Real.exp (s.x 0 (.z p))) := by
  have hsref := highRestLatency_spec hg
  have hshift : readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) 0 fire.latency = 1 := by
    simpa only [readyPulse,add_sub_cancel_left,sub_zero] using fire.response_root
  exact first_firing_le_rest_reference hq (by linarith [hg.1])
    ⟨by linarith [fire.early],by linarith [fire.deadline]⟩
    ⟨by linarith [hsref.1],by linarith [hsref.2.1]⟩ hshift hsref.2.2

theorem exact_rest_latency (hq : s.x 0 .q = 1 / 10)
    (hg : 16 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 7 / 2) :
    fire.latency = highRestLatency (Real.exp (s.x 0 (.z p))) := by
  apply highRestLatency_unique hg
  · constructor <;> linarith [fire.early,fire.deadline]
  · simpa only [hq,readyPulse,add_sub_cancel_left,sub_zero] using fire.response_root

theorem other_rest (hs : CadenceReadyCoordinates s 0 (8 / 25))
    (ho : ∀ q, q ≠ p → s.raw 0 q = none) (q : Port) (hq : q ≠ p) :
    RestBand (fire.final.x 0 (.m q)) :=
  (fire.execution.aux_no_input_rest_band 0 q (hs.auxiliary q).1 (hs.auxiliary q).2 (ho q hq)
    (by simp [NoArrivalAt,fire.deliveries])).1.2


theorem complete
    (hs : CadenceReadyCoordinates s 0 (8 / 25))
    (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    CompleteThrough fire.execution fire.final.time := by
  have hFuture : ∀ d ∈ fire.final.pending, fire.final.time < d.due := by
    intro d hd
    rw [fire.pending,List.append_nil] at hd
    rw [fire.date]
    linarith [hp d hd,fire.deadline]
  refine ⟨rfl,?_,hFuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [fire.main_fast,fire.charge]
      norm_num
    · intro j q
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hq : q = p
      · subst q
        rw [fire.aux_silent]
        exact fire.sensor_above
      · rw [fire.aux_other 0 q (Or.inr hq)]
        linarith [(fire.other_rest hs ho q hq).2]
  · intro j q origin hraw
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    by_cases hq : q = p
    · subst q
      have he : origin = s.time := Option.some.inj (hraw.symm.trans fire.raw_active)
      rw [he,fire.date]
      linarith [fire.deadline]
    · rw [fire.raw_other 0 q (Or.inr hq)] at hraw
      contradiction
  · exact hFuture

theorem error_zero (q : Port) : fire.execution.ledger.error 0 q = 0 := by
  have h := fire.execution.gain_balance 0 q
  rw [fire.gain_preserved] at h
  linarith

theorem recovery_zero : fire.execution.ledger.recovery 0 = 0 := by
  have h := fire.execution.recovery_balance 0
  rw [fire.recovery_preserved] at h
  linarith

theorem mark_zero (hs : CadenceReadyCoordinates s 0 (8 / 25))
    (ho : ∀ q, q ≠ p → s.raw 0 q = none) (q : Port) : fire.execution.ledger.mark 0 q = 0 := by
  have hother : ∀ r, r ≠ p → fire.execution.ledger.mark 0 r = 0 := by
    intro r hr
    have hquiet := fire.execution.aux_ready_without_input_band 0 r (hs.auxiliary r).1
      (hs.auxiliary r).2.2 (ho r hr) (by simp [NoArrivalAt,fire.deliveries])
    exact fire.execution.mark_zero_aux 0 r .ready (by decide)
      (fire.execution.allStates_aux_flows 0 r .ready hquiet)
  have hsum : (∑ r : Port, fire.execution.ledger.mark 0 r) = fire.execution.ledger.mark 0 p :=
    Finset.sum_eq_single p (fun r _ hr => hother r hr) (by simp)
  by_cases hq : q = p
  · subst q
    have h := fire.execution.recovery_sum_marks 0
    rw [fire.recovery_zero,hsum] at h
    exact h.symm
  · exact hother q hq

theorem emission_count : (fire.execution.emissionTimes 0).length = 1 := by
  simp [Execution.emissionTimes,fire.emissions]

end CadenceHighFire

end KernelR.Hybrid
