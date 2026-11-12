import Teaching.SelectorRead
import KernelR.HybridRawFullTailNoFire

/-! Quantitative conditions for using the tail of a saturated work pulse as
a selector precharge. All dates are relative to admission of the work pulse. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- A full-strength capped pulse cannot provide a silent precharge from
READY rest. Its READY response has already exceeded threshold by 0.26. -/
theorem capped_work_full_pulse_above_threshold {n θ ε}
    (box : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    1 < readyPulse (1 / 10) ((θ i).cap p) 0 (13 / 50) := by
  apply readyPulse_high_rest_at_twenty_six
  have lower := (box.2 i p).1.1
  have eps := box.epsilon_bounds.2
  linarith

/-- The work pulse reaches READY only from the reopening date. -/
noncomputable def cappedWorkTail (cap reopen : ℝ) : ℝ → ℝ :=
  readyPulse (1 / 10) (cap * Real.exp (-a * reopen)) reopen

/-- A window that works in either fabrication box, with a wider option
    when fabrication errors are at most 0.3%. -/
def CappedWorkTiming (ε age : ℝ) : Prop :=
  (139 / 250 ≤ age ∧ age ≤ 11193 / 20000) ∨
    (ε = 3 / 1000 ∧ 53 / 100 ≤ age ∧ age ≤ 59 / 100)

private theorem CappedWorkTiming.coarse {ε age : ℝ} (timing : CappedWorkTiming ε age) :
    53 / 100 ≤ age ∧ age ≤ 59 / 100 := by
  rcases timing with full | ⟨_, narrow⟩
  · constructor <;> linarith [full.1, full.2]
  · exact narrow

/-- In the certified reopening window, the residual tail of a saturated
work pulse stays subthreshold through raw expiry. At age 1.4 the quiet
relaxation of that charge is in the selector read band. -/
theorem capped_work_tail_precharge {n θ ε}
    (box : @PhysicalBox n θ ε) (i : Fin n) (p : Port) {reopen : ℝ}
    (timing : CappedWorkTiming ε reopen) :
    (∀ t ∈ Icc reopen 1, cappedWorkTail ((θ i).cap p) reopen t < 1) ∧
    (13 / 20 ≤ relax (1 / 2) (1 / 10) (cappedWorkTail ((θ i).cap p) reopen 1) 1 (7 / 5) ∧
      relax (1 / 2) (1 / 10) (cappedWorkTail ((θ i).cap p) reopen 1) 1 (7 / 5) ≤ 39 / 50) := by
  let cap := (θ i).cap p
  have age := timing.coarse
  have arange : (138629 / 100000 : ℝ) ≤ a ∧ a ≤ 138630 / 100000 := by
    dsimp [a]
    constructor <;> linarith [KernelR.log_four_bounds.1, KernelR.log_four_bounds.2]
  have tailFormula :
      cappedWorkTail cap reopen 1 = 1 / 10 + cap * (a / (a - 1 / 2)) *
        (Real.exp (-(1 / 2) - (a - 1 / 2) * reopen) - 1 / 4) := by
    simp only [cappedWorkTail, readyPulse, sub_self, zero_mul, add_zero, response]
    rw [show -(1 / 2 : ℝ) - (a - 1 / 2) * reopen =
      -a * reopen + -(1 / 2) * (1 - reopen) by ring, Real.exp_add, ← exp_neg_a]
    rw [show Real.exp (-a) = Real.exp (-a * reopen) * Real.exp (-a * (1 - reopen)) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  let residual := Real.exp (-(1 / 2) - (a - 1 / 2) * reopen) - 1 / 4
  have capNonneg : 0 ≤ cap := (box.cap_positive i p).le
  have ratioNonneg : 0 ≤ a / (a - 1 / 2) := by
    linarith [selector_response_coefficient_bounds.1]
  have productBounds {capLo capHi expLo expHi : ℝ} (hc : capLo ≤ cap ∧ cap ≤ capHi)
      (he : expLo ≤ Real.exp (-(1 / 2) - (a - 1 / 2) * reopen) ∧
        Real.exp (-(1 / 2) - (a - 1 / 2) * reopen) ≤ expHi)
      (positive : 1 / 4 ≤ expLo) (capHiNonneg : 0 ≤ capHi) :
      capLo * (391 / 250) * (expLo - 1 / 4) ≤ cap * (a / (a - 1 / 2)) * residual ∧
        cap * (a / (a - 1 / 2)) * residual ≤ capHi * (7821 / 5000) * (expHi - 1 / 4) := by
    have low : expLo - 1 / 4 ≤ residual := sub_le_sub_right he.1 _
    have high : residual ≤ expHi - 1 / 4 := sub_le_sub_right he.2 _
    constructor
    · exact mul_le_mul (mul_le_mul hc.1 selector_response_coefficient_bounds.1
        (by norm_num) capNonneg) low (by linarith) (mul_nonneg capNonneg ratioNonneg)
    · exact mul_le_mul (mul_le_mul hc.2 selector_response_coefficient_bounds.2
        ratioNonneg capHiNonneg) high (by linarith) (by positivity)
  have product :
      (6719 / 10000 : ℝ) ≤ cap * (a / (a - 1 / 2)) * residual ∧
        cap * (a / (a - 1 / 2)) * residual ≤ 83 / 100 := by
    rcases timing with full | ⟨narrow, dates⟩
    · have capBounds : (18 / 5 : ℝ) ≤ cap ∧ cap ≤ 22 / 5 := by
        have bounds := (box.2 i p).1
        have eps := box.epsilon_bounds.2
        change 4 * (1 - ε) ≤ cap ∧ cap ≤ 4 * (1 + ε) at bounds
        constructor <;> linarith [bounds.1, bounds.2]
      have expBounds :
          (73869 / 200000 : ℝ) ≤ Real.exp (-(1 / 2) - (a - 1 / 2) * reopen) ∧
          Real.exp (-(1 / 2) - (a - 1 / 2) * reopen) ≤ 7411 / 20000 := by
        constructor
        · apply le_trans _ (Real.exp_le_exp.mpr (show
            -(99602 / 100000 : ℝ) ≤ -(1 / 2) - (a - 1 / 2) * reopen by
              have product := mul_le_mul (show a - 1 / 2 ≤ (88630 / 100000 : ℝ) by linarith [arange.2])
                full.2 (by linarith [full.1]) (by norm_num)
              linarith))
          have estimate := Real.exp_bound (x := -(99602 / 100000 : ℝ)) (n := 13) (by norm_num) (by norm_num)
          norm_num [Finset.sum_range_succ] at estimate
          linarith [(abs_sub_le_iff.mp estimate).2]
        · apply le_trans (Real.exp_le_exp.mpr (show
            -(1 / 2) - (a - 1 / 2) * reopen ≤ -(99277 / 100000 : ℝ) by
              have product := mul_le_mul (show (88629 / 100000 : ℝ) ≤ a - 1 / 2 by linarith [arange.1])
                full.1 (by norm_num) (by linarith [arange.1])
              linarith))
          have estimate := Real.exp_bound (x := -(99277 / 100000 : ℝ)) (n := 13) (by norm_num) (by norm_num)
          norm_num [Finset.sum_range_succ] at estimate
          linarith [(abs_sub_le_iff.mp estimate).1]
      have band := productBounds capBounds expBounds (by norm_num) (by norm_num)
      constructor <;> linarith [band.1, band.2]
    · have capBounds : (3988 / 1000 : ℝ) ≤ cap ∧ cap ≤ 4012 / 1000 := by
        have bounds := (box.2 i p).1
        change 4 * (1 - ε) ≤ cap ∧ cap ≤ 4 * (1 + ε) at bounds
        rw [narrow] at bounds
        constructor <;> linarith [bounds.1, bounds.2]
      have expBounds :
          (35950 / 100000 : ℝ) ≤ Real.exp (-(1 / 2) - (a - 1 / 2) * reopen) ∧
          Real.exp (-(1 / 2) - (a - 1 / 2) * reopen) ≤ 37920 / 100000 := by
        constructor
        · apply le_trans _ (Real.exp_le_exp.mpr (show
            -(1023 / 1000 : ℝ) ≤ -(1 / 2) - (a - 1 / 2) * reopen by
              have upper := mul_le_mul (show a - 1 / 2 ≤ (88630 / 100000 : ℝ) by linarith [arange.2])
                dates.2 (by linarith [dates.1]) (by norm_num)
              linarith))
          have half : (59959 / 100000 : ℝ) ≤ Real.exp (-(1023 / 2000 : ℝ)) := by
            have estimate := Real.exp_bound (x := -(1023 / 2000 : ℝ)) (n := 12)
              (by norm_num) (by norm_num)
            norm_num [Finset.sum_range_succ] at estimate
            linarith [(abs_sub_le_iff.mp estimate).2]
          rw [show -(1023 / 1000 : ℝ) = -(1023 / 2000) + -(1023 / 2000) by norm_num, Real.exp_add]
          exact (by norm_num : (35950 / 100000 : ℝ) ≤ (59959 / 100000) * (59959 / 100000)).trans
            (mul_le_mul half half (by norm_num) (Real.exp_pos _).le)
        · apply le_trans (Real.exp_le_exp.mpr (show
            -(1 / 2) - (a - 1 / 2) * reopen ≤ -(96973 / 100000 : ℝ) by
              have lower := mul_le_mul (show (88629 / 100000 : ℝ) ≤ a - 1 / 2 by linarith [arange.1])
                dates.1 (by norm_num) (by linarith [arange.1])
              linarith))
          have estimate := Real.exp_bound (x := -(96973 / 100000 : ℝ)) (n := 13)
            (by norm_num) (by norm_num)
          norm_num [Finset.sum_range_succ] at estimate
          linarith [(abs_sub_le_iff.mp estimate).1]
      have band := productBounds capBounds expBounds (by norm_num) (by norm_num)
      constructor <;> linarith [band.1, band.2]
  have quiet : (8187 / 10000 : ℝ) ≤ Real.exp (-(1 / 5 : ℝ)) ∧
      Real.exp (-(1 / 5 : ℝ)) ≤ 8188 / 10000 := by
    have estimate := Real.exp_bound (x := -(1 / 5 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at estimate
    constructor <;> linarith [(abs_sub_le_iff.mp estimate).1, (abs_sub_le_iff.mp estimate).2]
  constructor
  · intro t ht
    have respMono : MonotoneOn response (Icc 0 (9 / 10)) := by
      apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_).monotoneOn
      · unfold response
        fun_prop
      · intro age inside
        have range := interior_subset inside
        rw [(response_derivative age).deriv]
        linarith [response_derivative_lower range.1 range.2]
    have comparison := respMono
      (show t - reopen ∈ Icc 0 (9 / 10) from ⟨by linarith [ht.1], by linarith [ht.2, age.1]⟩)
      (show 1 - reopen ∈ Icc 0 (9 / 10) from ⟨by linarith [age.2], by linarith [age.1]⟩)
      (by linarith [ht.2])
    have monotone : cappedWorkTail cap reopen t ≤ cappedWorkTail cap reopen 1 := by
      unfold cappedWorkTail readyPulse
      simp only [sub_self, zero_mul, add_zero]
      exact add_le_add_right (mul_le_mul_of_nonneg_left comparison
        (mul_nonneg capNonneg (Real.exp_pos (-a * reopen)).le)) _
    exact monotone.trans_lt (by rw [tailFormula]; change (1 / 10 : ℝ) +
      cap * (a / (a - 1 / 2)) * residual < 1; linarith)
  · have nonnegative : 0 ≤ cap * (a / (a - 1 / 2)) * residual := by linarith [product.1]
    have lower := mul_le_mul product.1 quiet.1 (by norm_num) nonnegative
    have upper := mul_le_mul product.2 quiet.2 (by linarith [product.1]) (by norm_num)
    have formula : relax (1 / 2) (1 / 10) (cappedWorkTail cap reopen 1) 1 (7 / 5) =
        1 / 10 + cap * (a / (a - 1 / 2)) * residual * Real.exp (-(1 / 5)) := by
      rw [relax, tailFormula, show -(1 / 2 : ℝ) * ((7 / 5 : ℝ) - 1) = -(1 / 5) by norm_num]
      change 1 / 10 + (1 / 10 + cap * (a / (a - 1 / 2)) * residual - 1 / 10) * _ = _
      ring
    change (13 / 20 : ℝ) ≤ relax (1 / 2) (1 / 10) (cappedWorkTail cap reopen 1) 1 (7 / 5) ∧ _
    rw [formula]
    constructor <;> linarith

private theorem capped_gain_during_flows {n θ ε route s u} (e : @Execution n θ route s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port) (saturated : s.x i (.z p) = Real.log ((θ i).cap p)) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i (.z p) = Real.log ((θ i).cap p)) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f =>
      have fixed t (ht : t ∈ Icc _ _) := le_antisymm
        (f.gain_cap_on i p saturated.le t ht)
        ((f.gain_nondecreasing box i p t ht).trans' saturated.ge)
      exact ⟨fixed, ih (by rw [← f.final]; exact fixed _ ⟨f.positive.le, le_rfl⟩)⟩
    | jump j =>
      exact ih (by rw [j.physical_continuous]; exact saturated)

private theorem capped_raw_span_solution {n θ ε route s u} (e : @Execution n θ route s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port) (origin : ℝ)
    (main : e.MainFlows i .ready) (initial : s.x i .q = 1 / 10)
    (saturated : s.x i (.z p) = Real.log ((θ i).cap p))
    (active : e.AllFlows (fun {v _} _ => v.raw i p = some origin))
    (other : ∀ q, q ≠ p → s.raw i q = none) (noInput : ∀ q, NoArrivalAt e i q) :
    u.x i .q = cappedWorkTail ((θ i).cap p) (s.time - origin) (u.time - origin) := by
  let amp := (θ i).cap p * Real.exp (-a * (s.time - origin))
  have otherFlows : e.AllFlows (fun {v _} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply e.allFlows_forall (fun q {v _} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases h : q = p
    · exact e.allFlows_of (P := fun {v _} _ => q ≠ p → v.raw i q = none)
        (fun _ ne => False.elim (ne h))
    · exact e.allFlows_mono (fun _ absent _ => absent) (e.raw_absent_allFlows i q
        (e.raw_absent_of_no_arrival i q (other q h) (noInput q)).2)
  have drive : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t = amp * a * Real.exp (-a * (t - s.time))) := by
    refine e.allFlows_mono ?_ (e.allFlows_and active
      (e.allFlows_and otherFlows (capped_gain_during_flows e box i p saturated)))
    intro v w f h t ht
    unfold tailDrive
    rw [Finset.sum_eq_single p]
    · simp only [rawTail, h.1, h.2.2 t ⟨ht.1, ht.2.le⟩, Real.exp_log (box.cap_positive i p)]
      dsimp [amp]
      rw [show -a * (t - origin) = -a * (s.time - origin) + -a * (t - s.time) by ring, Real.exp_add]
      ring
    · intro q _ different
      simp [rawTail, h.2.1 q different]
    · simp
  have start : readyPulse (1 / 10) amp s.time s.time = s.x i .q := by
    rw [readyPulse_initial, initial]
  have upper := e.ready_drive_upper i main (1 / 10) amp s.time start.ge
    (e.allFlows_mono (fun _ h t ht => (h t ht).le) drive)
  have lower := e.ready_drive_lower i main (1 / 10) amp s.time start.le
    (e.allFlows_mono (fun _ h t ht => (h t ht).ge) drive)
  unfold cappedWorkTail readyPulse
  rw [show u.time - origin - (s.time - origin) = u.time - s.time by ring]
  exact le_antisymm upper lower

/-- After an actual READY reopening in the required window, any isolated
continuation to pulse age 1.4 silently supplies the selector charge band.
The conclusion uses the real expiry jump and allows the work sensor to
pass through ERROR with its gain already at the fabrication cap. -/
theorem capped_work_precharge_of_reopened {n θ ε route s u} (e : @Execution n θ route s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port) (origin : ℝ)
    (ready : s.main i = .ready) (initial : s.x i .q = 1 / 10)
    (saturated : s.x i (.z p) = Real.log ((θ i).cap p))
    (timing : CappedWorkTiming ε (s.time - origin))
    (active : s.raw i p = some origin) (other : ∀ q, q ≠ p → s.raw i q = none)
    (noInput : ∀ q, NoArrivalAt e i q) (finish : u.time = origin + 7 / 5) :
    u.main i = .ready ∧ e.emissionTimes i = [] ∧ (∀ q, u.raw i q = none) ∧
      (13 / 20 ≤ u.x i .q ∧ u.x i .q ≤ 39 / 50) ∧
      u.x i (.z p) = Real.log ((θ i).cap p) ∧
      ∀ q, q ≠ p → s.aux i q = .ready → RestBand (s.x i (.m q)) →
        (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) := by
  obtain ⟨d⟩ := e.raw_end_completion i p origin active (by linarith [timing.coarse.2]) (by linarith)
  have hp : e.IsPrefix d.span :=
    (congrArg (fun trace => trace.IsPrefix d.span) d.reconstruct).mpr (.append_left _ _)
  have dActive : d.span.AllFlows (fun {v _} _ => v.raw i p = some origin) := by
    have rawFlows {v w : Snapshot n} (trace : Execution θ route v w) :
        trace.ConstantFlows (fun a => a.raw i p) (some origin) →
          trace.AllFlows (fun {b _} _ => b.raw i p = some origin) := by
      induction trace with
      | nil => intro _; trivial
      | cons move rest ih =>
        cases move
        · intro h; exact ⟨h.1, ih h.2⟩
        · exact ih
    exact rawFlows d.span d.flows
  have bounds := capped_work_tail_precharge box i p timing
  have dReady : d.span.AllStates (fun v => v.main i = .ready) := by
    rcases d.span.first_state_change (fun v => v.main i) .ready
      (fun f => congrFun f.main_fixed i) ready with h | ⟨v, w, segment, exit, rest, split, states, hv, hw⟩
    · exact h
    · have prefixSpan : d.span.IsPrefix segment := by rw [split]; exact .append_left _ _
      have rawPrefix := prefixSpan.all_flows
        (fun {b _} _ => b.raw i p = some origin) (fun {_ _} _ {_} _ _ raw => raw) dActive
      have value := capped_raw_span_solution segment box i p origin
        (segment.allStates_main_flows i .ready states) initial saturated rawPrefix other
        (fun q => prefixSpan.no_arrival i q (hp.no_arrival i q (noInput q)))
      have vBefore : v.time ≤ origin + 1 := by
        rw [← d.date, ← exit.time_unchanged]
        exact rest.time_monotone
      have strict := bounds.1 (v.time - origin)
        ⟨by linarith [segment.time_monotone], by linarith⟩
      rw [(exit.ready_main_departure i hv hw).1] at value
      linarith
  have value := capped_raw_span_solution d.span box i p origin
    (d.span.allStates_main_flows i .ready dReady) initial saturated dActive other
    (fun q => hp.no_arrival i q (noInput q))
  rw [d.date, add_sub_cancel_left] at value
  have afterReady : d.afterEnd.main i = .ready := by
    rw [d.exit.main_unchanged_of_raw_departure i p origin d.raw_before d.raw_after]
    exact d.span.allStates_final dReady
  have afterRaw (q : Port) : d.afterEnd.raw i q = none := by
    by_cases same : q = p
    · subst q; exact d.raw_after
    · have states := e.raw_none_states i q (other q same) (noInput q)
      rw [d.reconstruct, Execution.allStates_append] at states
      exact d.rest.allStates_initial states.2.2
  have noLater (q : Port) : NoArrivalAt d.rest i q := by
    have h := noInput q
    rw [d.reconstruct, Execution.noArrivalAt_append] at h
    exact fun token member => h.2 token (List.mem_append_right _ member)
  have afterValue : d.afterEnd.x i .q =
      cappedWorkTail ((θ i).cap p) (s.time - origin) 1 := by
    simpa only [d.exit.physical_continuous] using value
  have restReady := d.rest.ready_without_input_subthreshold i afterReady
    (by rw [afterValue]; exact bounds.1 1 ⟨by linarith [timing.coarse.2], le_rfl⟩) afterRaw noLater
  have states : e.AllStates (fun v => v.main i = .ready) := by
    rw [d.reconstruct, Execution.allStates_append]
    exact ⟨dReady, d.span.allStates_final dReady, restReady⟩
  have absent (q : Port) := d.rest.raw_absent_of_no_arrival i q (afterRaw q) (noLater q)
  have finalValue := d.rest.ready_no_current_solution i (d.rest.allStates_main_flows i .ready restReady)
    (fun q => (absent q).2)
  rw [afterValue, d.exit.time_unchanged, d.date, finish,
    show origin + 7 / 5 - (origin + 1) = 7 / 5 - 1 by ring] at finalValue
  exact ⟨e.allStates_final states, e.no_emissions_of_ready_states i states, fun q => (absent q).1,
    by rw [finalValue]; exact bounds.2,
    le_antisymm (e.gain_cap i p saturated.le) (saturated.symm.le.trans (e.gain_nondecreasing box i p)),
    fun q distinct sensor band => e.aux_no_input_rest_band i q sensor band (other q distinct) (noInput q)⟩

end RecursiveLearning.Native
