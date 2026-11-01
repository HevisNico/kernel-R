import KernelR.HybridErrorTailFlowExistence
import KernelR.HybridPhysicalInvariant
import KernelR.HybridGuardNoJump
import KernelR.HybridRawExpiryProgress
import KernelR.HybridFirstCycleSchedule

namespace KernelR.Hybrid
open Set

/-- A constructed completion of one ERROR phase, with the actual remaining
dose rather than an assumed full dose after a raw-expiry cut. -/
structure ErrorCompletion {n} (θ : Fin n → Parameters) (route : Router n)
    (s : Snapshot n) (i : Fin n) (p : Port) where
  final : Snapshot n
  execution : Execution θ route s final
  date : final.time = s.time + errorTailDuration θ s i p
  main_ready : ∀ j, final.main j = .ready
  aux_ready : ∀ j q, final.aux j q = .ready
  main_below : ∀ j, final.x j .q < 1
  aux_below : ∀ j q, final.x j (.m q) < 1
  sensor_rest : final.x i (.m p) = 1 / 40
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = s.pending
  pending_future : ∀ d ∈ s.pending, final.time < d.due
  gain_target : final.x i (.z p) = s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40)
  gain_other : ∀ j q, j ≠ i ∨ q ≠ p → final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final

theorem ErrorCompletion.complete {n θ route s i p} (c : @ErrorCompletion n θ route s i p) :
    CompleteThrough c.execution c.final.time := by
  refine ⟨rfl,?_,?_⟩
  · intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro j; simpa [c.main_ready j] using c.main_below j
      · intro j q; simpa [c.aux_ready j q] using c.aux_below j q
    · intro j q origin h; rw [c.raw_none j q] at h; contradiction
    · rw [c.pending]; exact c.pending_future
  · rw [c.pending]; exact c.pending_future

theorem ErrorCompletion.error_dose {n θ route s i p} (c : @ErrorCompletion n θ route s i p) :
    c.execution.ledger.error i p = 8 * (s.x i (.m p) - 1 / 40) := by
  have h := c.execution.gain_balance i p
  rw [c.gain_target] at h
  linarith

theorem ErrorCompletion.other_error_zero {n θ route s i p} (c : @ErrorCompletion n θ route s i p)
    (j : Fin n) (q : Port) (hother : j ≠ i ∨ q ≠ p) : c.execution.ledger.error j q = 0 := by
  have h := c.execution.gain_balance j q
  rw [c.gain_other j q hother] at h
  linarith

/-- When raw is absent, the remaining ERROR phase is constructed for every
sensor charge in (.025,.1], including a real intermediate raw-expiry cut. -/
theorem error_completion_without_raw {n θ ε route} (hb : @PhysicalBox n θ ε)
    (s : Snapshot n) (i : Fin n) (p : Port) (hs : PhysicalInvariant θ s)
    (hm : ∀ j, s.main j = .ready) (ha : s.aux i p = .error)
    (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : ∀ j q, s.raw j q = none)
    (hm0 : 1 / 40 < s.x i (.m p)) (hmu : s.x i (.m p) ≤ 1 / 10)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    (hq0 : ∀ j, s.x j .q < 1)
    (hx0 : ∀ j q, j ≠ i ∨ q ≠ p → s.x j (.m q) < 1)
    (hp : ∀ d ∈ s.pending, s.time + errorTailDuration θ s i p < d.due) :
    Nonempty (ErrorCompletion θ route s i p) := by
  let T := s.time + errorTailDuration θ s i p
  have hT : s.time < T := by dsimp [T]; linarith [errorTailDuration_positive hb s i p hm0]
  have hq : ∀ t ∈ Icc s.time T, errorTailMain θ s i p none t < 1 := by
    intro t ht
    have h := errorTailMain_le_readyPulse hb s i p hm0 hh none ht.1 ht.2
    simp only [rawInputScale,mul_zero,readyPulse_zero_eq_relax] at h
    exact h.trans_lt (relax_lt (by norm_num) ht.1 (hq0 i) (by norm_num))
  let flow : Flow θ s (errorTailEnd θ s i p none T) := errorTailFlow hb s i p none hT le_rfl
    hm ha hao (hr i p) (fun j q _ => hr j q) hm0 hmu (hs.reserve i) hh
    (by intros; contradiction) hq0 hx0 (fun t ht => hq t ⟨ht.1,ht.2.le⟩)
    (fun d hd => (hp d hd).le)
  let v := errorTailEnd θ s i p none T
  have hend : v.x i (.m p) = 1 / 40 := by
    simpa [v,errorTailEnd,errorTailValues] using errorTailSensor_endpoint hb s i p hm0
  let u := setAux v i p .ready
  let e : Execution θ route s u :=
    .cons (.flow flow) (.cons (.jump (.auxReady v i p ha hend)) (.nil _))
  have htarget : u.x i (.z p) = s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) := by
    have h : errorTailGain θ s i p (s.time + errorTailDuration θ s i p) =
        s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) := by
      unfold errorTailGain
      rw [errorTailSensor_endpoint hb s i p hm0]
    simpa [u,setAux,v,errorTailEnd,errorTailValues,T] using h
  refine ⟨{
    final := u
    execution := e
    date := rfl
    main_ready := hm
    aux_ready := ?_
    main_below := ?_
    aux_below := ?_
    sensor_rest := hend
    raw_none := hr
    pending := rfl
    pending_future := hp
    gain_target := htarget
    gain_other := ?_
    recovery := fun j => rfl
    emissions := rfl
    deliveries := rfl
    physical := e.physical_invariant hb hs
  }⟩
  · intro j q
    by_cases hj : j = i
    · subst j
      by_cases hq : q = p
      · subst q; simp [u,setAux]
      · simpa [u,setAux,v,errorTailEnd,hq] using hao i q (Or.inr hq)
    · simpa [u,setAux,v,errorTailEnd,hj] using hao j q (Or.inl hj)
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [u,setAux,v,errorTailEnd,errorTailValues] using hq T ⟨hT.le,le_rfl⟩
    · simpa [u,setAux,v,errorTailEnd,errorTailValues,hj] using
        relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hq0 j) (by norm_num : (1 / 10 : ℝ) < 1)
  · intro j q
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩; change v.x j (.m q) < 1; rw [hend]; norm_num
    · simpa [u,setAux,v,errorTailEnd,errorTailValues,h] using
        relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hx0 j q (by tauto))
          (by norm_num : (1 / 40 : ℝ) < 1)
  · intro j q h
    have hne : ¬ (j = i ∧ q = p) := by tauto
    simp [u,setAux,v,errorTailEnd,errorTailValues,hne]

theorem errorTail_cut_time {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (cut : ℝ) (hr : (θ i).le p ≠ 0) (hm : 0 < s.x i (.m p)) :
    let v := setRaw (errorTailEnd θ s i p origin cut) i p none
    v.time + errorTailDuration θ v i p = s.time + errorTailDuration θ s i p := by
  dsimp only
  have hlog : Real.log (40 * (s.x i (.m p) * Real.exp (-(θ i).le p * (cut - s.time)))) =
      Real.log (40 * s.x i (.m p)) - (θ i).le p * (cut - s.time) := by
    rw [show 40 * (s.x i (.m p) * Real.exp (-(θ i).le p * (cut - s.time))) =
      (40 * s.x i (.m p)) * Real.exp (-(θ i).le p * (cut - s.time)) by ring,
      Real.log_mul (by positivity : (40 : ℝ) * s.x i (.m p) ≠ 0) (Real.exp_ne_zero _),Real.log_exp]
    ring
  simp only [setRaw,errorTailEnd,errorTailDuration,errorTailValues,errorTailSensor,
    true_and,ite_true]
  rw [hlog]
  field_simp [hr]
  ring

theorem errorTail_cut_budget {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (cut : ℝ) :
    let v := setRaw (errorTailEnd θ s i p origin cut) i p none
    v.x i (.z p) + 8 * (v.x i (.m p) - 1 / 40) =
      s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) := by
  simp [setRaw,errorTailEnd,errorTailValues,errorTailGain]
  ring


/-- A genuine early ERROR span is split at its raw expiry. The second span
starts from its actual intermediate sensor charge and remaining learning dose. -/
theorem error_completion_with_raw_tail {n θ ε route} (hb : @PhysicalBox n θ ε)
    (s : Snapshot n) (i : Fin n) (p : Port) (hs : PhysicalInvariant θ s)
    (hm : ∀ j, s.main j = .ready) (ha : s.aux i p = .error)
    (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (origin : ℝ) (hr : s.raw i p = some origin)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hm0 : 1 / 40 < s.x i (.m p)) (hmu : s.x i (.m p) ≤ 1 / 10)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    (hlate : origin + 99 / 100 ≤ s.time) (hactive : s.time < origin + 1)
    (hfinish : origin + 1 < s.time + errorTailDuration θ s i p)
    (hqi : s.x i .q ≤ 24 / 25) (hq0 : ∀ j, s.x j .q < 1)
    (hx0 : ∀ j q, j ≠ i ∨ q ≠ p → s.x j (.m q) < 1)
    (hp : ∀ d ∈ s.pending, s.time + errorTailDuration θ s i p < d.due) :
    Nonempty (ErrorCompletion θ route s i p) := by
  let R := origin + 1
  have hrange : origin ≤ s.time := by linarith
  have hamp : (22 / 5 : ℝ) * rawInputScale (some origin) s.time ≤ 11 / 5 := by
    exact cap_raw_amplitude_tiny_error (by norm_num) (by linarith)
  have hq : ∀ t ∈ Icc s.time R, errorTailMain θ s i p (some origin) t < 1 := by
    intro t ht
    have h := errorTailMain_le_readyPulse hb s i p hm0 hh (some origin) ht.1 (ht.2.trans hfinish.le)
    exact h.trans_lt (readyPulse_tiny_error_guard hqi hamp ht.1 (by dsimp [R] at ht; linarith [ht.2])).2
  let flow : Flow θ s (errorTailEnd θ s i p (some origin) R) :=
    errorTailFlow hb s i p (some origin) hactive hfinish.le hm ha hao hr ho hm0 hmu
      (hs.reserve i) hh (by intro o he; cases Option.some.inj he; exact ⟨hrange,le_rfl⟩)
      hq0 hx0 (fun t ht => hq t ⟨ht.1,ht.2.le⟩) (fun d hd => (hfinish.trans (hp d hd)).le)
  let v := setRaw (errorTailEnd θ s i p (some origin) R) i p none
  let head : Execution θ route s v := .cons (.flow flow)
    (.cons (.jump (.rawEnd _ i p origin hr rfl)) (.nil _))
  have hremaining : v.time + errorTailDuration θ v i p = s.time + errorTailDuration θ s i p :=
    errorTail_cut_time s i p (some origin) R (ne_of_gt (hb.rates_positive i p).2.2) (by linarith)
  have hbudget : v.x i (.z p) + 8 * (v.x i (.m p) - 1 / 40) =
      s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) := errorTail_cut_budget s i p (some origin) R
  have hvraw : ∀ j q, v.raw j q = none := by
    intro j q
    by_cases hj : j = i
    · subst j
      by_cases hq : q = p
      · subst q; simp [v,setRaw]
      · simpa [v,setRaw,errorTailEnd,hq] using ho i q (Or.inr hq)
    · simpa [v,setRaw,errorTailEnd,hj] using ho j q (Or.inl hj)
  have hvm0 : 1 / 40 < v.x i (.m p) := by
    simpa [v,setRaw,errorTailEnd,errorTailValues] using
      errorTailSensor_strict_floor hb s i p hm0 hfinish
  have hvmu : v.x i (.m p) ≤ 1 / 10 := by
    have he : Real.exp (-(θ i).le p * (R - s.time)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [(hb.rates_positive i p).2.2])
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ s.x i (.m p) by linarith)
    have hu : s.x i (.m p) * Real.exp (-(θ i).le p * (R - s.time)) ≤ 1 / 10 := by linarith
    simpa [v,setRaw,errorTailEnd,errorTailValues,errorTailSensor] using hu
  have hvq : ∀ j, v.x j .q < 1 := by
    intro j
    by_cases hj : j = i
    · subst j; simpa [v,setRaw,errorTailEnd,errorTailValues] using hq R ⟨hactive.le,le_rfl⟩
    · simpa [v,setRaw,errorTailEnd,errorTailValues,hj] using
        relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hactive.le (hq0 j) (by norm_num : (1 / 10 : ℝ) < 1)
  have hvx : ∀ j q, j ≠ i ∨ q ≠ p → v.x j (.m q) < 1 := by
    intro j q h
    have hne : ¬ (j = i ∧ q = p) := by tauto
    simpa [v,setRaw,errorTailEnd,errorTailValues,hne] using
      relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hactive.le (hx0 j q h) (by norm_num : (1 / 40 : ℝ) < 1)
  obtain ⟨c⟩ := error_completion_without_raw hb v i p (head.physical_invariant hb hs) hm ha hao
    hvraw hvm0 hvmu (by rw [hbudget]; exact hh) hvq hvx (by intro d hd; rw [hremaining]; exact hp d hd)
  let e := head.append c.execution
  refine ⟨{
    final := c.final
    execution := e
    date := c.date.trans hremaining
    main_ready := c.main_ready
    aux_ready := c.aux_ready
    main_below := c.main_below
    aux_below := c.aux_below
    sensor_rest := c.sensor_rest
    raw_none := c.raw_none
    pending := c.pending
    pending_future := c.pending_future
    gain_target := c.gain_target.trans hbudget
    gain_other := ?_
    recovery := c.recovery
    emissions := ?_
    deliveries := ?_
    physical := c.physical
  }⟩
  · intro j q h
    rw [c.gain_other j q h]
    have hne : ¬ (j = i ∧ q = p) := by tauto
    simp [v,setRaw,errorTailEnd,errorTailValues,hne]
  · simp [e,head,Execution.emissions_append,Execution.ledger,Move.ledger,Flow.ledger,
      Jump.ledger,Ledger.add,Ledger.zero,c.emissions]
  · simp [e,head,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries,c.deliveries]

end KernelR.Hybrid
