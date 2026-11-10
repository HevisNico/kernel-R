import ErrorReadHandoff
import KernelR.HybridFirstInputError

/-! A two-pulse experiment. Training starts from a READY cell at rest.
The read is scheduled before the experiment and uses the actual learned
state. This construction covers raw expiry strictly before ERROR entry. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

noncomputable def trainingStart (time : ℝ) (gains : Port → ℝ) (p : Port) : Snapshot 1 :=
  { toleranceStartOn time gains p with
    raw := fun _ _ => none
    pending := [errorReadDelivery p time, errorReadDelivery p (time + 16)] }

noncomputable def trainingAdmitted (time : ℝ) (gains : Port → ℝ) (p : Port) : Snapshot 1 :=
  { setRaw (trainingStart time gains p) 0 p (some time) with
    pending := [errorReadDelivery p (time + 16)] }

noncomputable def trainingRawEnd (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    {f : FirstInputMark θ s 0 p} (g : FirstInputSilent f) : Snapshot 1 :=
  readyProtectedEnd θ g.final 0 p .silent (some s.time) (s.time + 1)

noncomputable def trainingExpired (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    {f : FirstInputMark θ s 0 p} (g : FirstInputSilent f) : Snapshot 1 :=
  setRaw (trainingRawEnd θ s p g) 0 p none

/-- The original SILENT field after expiry, with the realized ERROR entry
guard. All coordinates use one trajectory from the actual expiry state. -/
structure TrainingSilentTail (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    (upper level stop : ℝ) where
  positive : s.time < stop
  continuous : ∀ i c, ContinuousOn (fun t => readyProtectedValues θ s 0 p .silent none t i c)
    (Icc s.time stop)
  integrable : ∀ i c, IntervalIntegrable (fun t =>
    field θ s (readyProtectedValues θ s 0 p .silent none t) t i c) volume s.time stop
  integral : ∀ t ∈ Icc s.time stop, ∀ i c,
    readyProtectedValues θ s 0 p .silent none t i c =
      s.x i c + ∫ v in s.time..t, field θ s (readyProtectedValues θ s 0 p .silent none v) v i c
  main_guard : ∀ t ∈ Ico s.time stop, readyProtectedValues θ s 0 p .silent none t 0 .q < level
  sensor_guard : ∀ t ∈ Ico s.time stop, upper < readyProtectedValues θ s 0 p .silent none t 0 (.m p)
  other_guard : ∀ t ∈ Ico s.time stop, ∀ q ≠ p,
    readyProtectedValues θ s 0 p .silent none t 0 (.m q) < 1
  contact : readyProtectedValues θ s 0 p .silent none stop 0 (.m p) = upper
  pending : ∀ d ∈ s.pending, stop < d.due

/-- A single trajectory from the admitted training pulse to the read's
first FIRE. The two threshold changes are in the sensor's descending
phases, and the read's main threshold is fixed throughout the task. -/
structure TrainingRead (θ : Fin 1 → Parameters) (time : ℝ) (gains : Port → ℝ) (p : Port)
    (upper lower level : ℝ) where
  train : Jump (fun _ _ => []) (trainingStart time gains p) (trainingAdmitted time gains p)
  mark : FirstInputMark θ (trainingAdmitted time gains p) 0 p
  silent : FirstInputSilent mark
  rawLeg : Flow θ silent.final (trainingRawEnd θ (trainingAdmitted time gains p) p silent)
  expiry : Jump (fun _ _ => []) (trainingRawEnd θ (trainingAdmitted time gains p) p silent)
    (trainingExpired θ (trainingAdmitted time gains p) p silent)
  pre_mark : ∀ t ∈ Ico time (time + mark.latency), mark.flow.path t 0 .q < level
  pre_silent : ∀ t ∈ Ico mark.final.time silent.final.time, silent.flow.path t 0 .q < level
  pre_expiry : ∀ t ∈ Ico silent.final.time (time + 1),
    rawLeg.path t 0 .q < level ∧ upper < rawLeg.path t 0 (.m p)
  stop : ℝ
  tail : TrainingSilentTail θ (trainingExpired θ (trainingAdmitted time gains p) p silent) p upper level stop
  handoff : ErrorReadHandoff θ
    (setAux (readyProtectedEnd θ (trainingExpired θ (trainingAdmitted time gains p) p silent)
      0 p .silent none stop) 0 p .error) p upper lower level (time + 16)
  read_silent_guard : ∀ t ∈ Icc handoff.decision.silent.final.time handoff.decision.stop,
    upper < readyProtectedValues θ handoff.decision.silent.final 0 p .silent
      (some handoff.readStart.time) t 0 (.m p)
  read_date : handoff.readStart.time = time + 16
  dose_from_birth : handoff.learned = gains p + 8 * (upper - lower)

private theorem exp_two_bound : Real.exp 2 < (160 / 21 : ℝ) := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have h : Real.exp 1 ≤ 11 / 4 := by linarith [Real.exp_one_lt_d9]
  nlinarith [mul_le_mul h h (Real.exp_pos 1).le (by norm_num : (0 : ℝ) ≤ 11 / 4)]

private theorem silent_above_upper {rate elapsed : ℝ} (rp : 0 ≤ rate)
    (rateUpper : rate ≤ 2) (h : elapsed ≤ 1) :
    (21 / 200 : ℝ) < (4 / 5 : ℝ) * Real.exp (-rate * elapsed) := by
  have hx : -2 ≤ -rate * elapsed := by
    have hmul := mul_le_mul_of_nonneg_left h rp
    linarith
  have he := Real.exp_le_exp.mpr hx
  have low : (21 / 160 : ℝ) < Real.exp (-2) := by
    rw [Real.exp_neg, ← one_div]
    apply (lt_div_iff₀ (Real.exp_pos _)).2
    linarith [exp_two_bound]
  linarith

/-- The small fabrication box guarantees expiry before either admissible
ERROR entry level. The larger box can use the same result with this
single extra upper bound on the active sensor's SILENT rate. -/
theorem training_silent_rate_small_box {θ : Fin 1 → Parameters}
    (box : @PhysicalBox 1 θ (3 / 1000)) (p : Port) : (θ 0).ls p ≤ 2 := by
  have h := (box.2 0 p).2.2.1.2
  change (θ 0).ls p ≤ Real.log 8 / (53 / 50) * (1 + 3 / 1000) at h
  have logUpper : Real.log 8 ≤ 21 / 10 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  linarith

private theorem training_silent_rate_lower {θ ε} (box : @PhysicalBox 1 θ ε) (p : Port) :
    1 ≤ (θ 0).ls p := by
  have h := (box.2 0 p).2.2.1.1
  change Real.log 8 / (53 / 50) * (1 - ε) ≤ (θ 0).ls p at h
  have logLower : (3 / 2 : ℝ) < Real.log 8 := log_eight_lower
  have eps : (9 / 10 : ℝ) ≤ 1 - ε := by linarith [box.epsilon_bounds.2]
  have hmul := mul_le_mul (show (3 / 2 : ℝ) / (53 / 50) ≤ Real.log 8 / (53 / 50) by linarith)
    eps (by norm_num) (by linarith)
  linarith

/-- A scheduled pair of canonical pulses. The first stays below FIRE and
raises the gain, and the second produces a transverse FIRE. Both ERROR
endpoints and the main FIRE threshold may vary independently by 5%. -/
theorem training_read_exists {θ ε time gains p upper lower level}
    (box : @PhysicalBox 1 θ ε) (rateUpper : (θ 0).ls p ≤ 2)
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : |lower - 1 / 40| ≤ 1 / 800)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    Nonempty (TrainingRead θ time gains p upper lower level) := by
  let s := trainingAdmitted time gains p
  let d := errorReadDelivery p (time + 16)
  let route : Router 1 := fun _ _ => []
  have train : Jump route (trainingStart time gains p) s :=
    .arrive (trainingStart time gains p) (errorReadDelivery p time) [] [d] rfl rfl rfl
  have raw : s.raw 0 p = some s.time := by
    simp [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw]
  have otherRaw (i : Fin 1) (q : Port) (h : i ≠ 0 ∨ q ≠ p) : s.raw i q = none := by
    have hi : i = 0 := Subsingleton.elim _ _
    have hq := h.resolve_left (not_not_intro hi)
    simp [s, trainingAdmitted, trainingStart, setRaw, hi, hq]
  have margin (t : ℝ) (ht : s.time ≤ t) :
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t ≤ 9 / 10 := by
    have h := readyPulse_uniform_bound (initial := (1 / 10 : ℝ))
      (amplitude := Real.exp (gains p)) le_rfl le_rfl gain.2 (by norm_num) ht
    change readyPulse (1 / 10) (Real.exp (gains p)) s.time t ≤ 9 / 10
    linarith
  have ahead : ∀ v ∈ s.pending, s.time + 2 ≤ v.due := by
    norm_num [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw, errorReadDelivery]
  have below (t : ℝ) (ht : s.time ≤ t) (_ : t ≤ s.time + 1 / 10) :
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t < 1 := by linarith [margin t ht]
  obtain ⟨f⟩ := first_input_mark_of_response_margin_until_exists s box 0 p
    (fun _ => rfl) (fun _ _ => rfl) raw otherRaw
    (by intro i; norm_num [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw])
    (by intro i q; norm_num [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw])
    (fun t ht h => below t ht (by linarith))
    (by norm_num [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw, RestBand])
    (by intro v hv; linarith [ahead v hv])
  obtain ⟨g⟩ := f.first_silent_of_response_margin_until_exists box below
    (by intro v hv; linarith [ahead v hv])
  let edge := trainingRawEnd θ s p g
  let expired := trainingExpired θ s p g
  let rate := (θ 0).ls p
  have rp : 0 < rate := (box.rates_positive 0 p).2.1
  have gAfter : s.time ≤ g.final.time := by
    change s.time ≤ s.time + f.latency + Real.log (5 / 4) / (θ 0).lm p
    linarith [f.early, (box.aux_durations_positive 0 p).1]
  have gBefore : g.final.time < s.time + 1 := by
    change f.silentDate < s.time + 1
    linarith [g.deadline]
  have elapsed (t : ℝ) (ht : t ≤ s.time + 1) :
      (21 / 200 : ℝ) < (4 / 5 : ℝ) * Real.exp (-rate * (t - g.final.time)) :=
    silent_above_upper rp.le rateUpper (by linarith)
  let rawFlow : Flow θ g.final edge :=
    readyProtectedFlow g.final 0 p .silent (some s.time) gBefore (Or.inr rfl)
      g.main_ready g.aux_silent g.aux_other g.raw_active g.raw_other
      (by intro o h; obtain rfl := (Option.some.inj h).symm; exact ⟨gAfter, le_rfl⟩)
      g.main_below g.aux_below
      (by
        intro t ht
        rw [g.response_restart]
        linarith [margin t (gAfter.trans ht.1)])
      (by
        intro t ht
        simp only [protectedReadyRate, g.sensor_charge, reduceCtorEq, ite_false]
        change 1 / 10 < (4 / 5 : ℝ) * Real.exp (-rate * (t - g.final.time))
        linarith [elapsed t ht.2.le])
      (by
        intro v hv
        have h := ahead v (g.queue_preserved ▸ hv)
        linarith)
  have expiry : Jump route edge expired := rawExpiryJump edge 0 p s.time g.raw_active rfl
  have expiredMain : ∀ i, expired.main i = .ready := g.main_ready
  have expiredSilent : expired.aux 0 p = .silent := g.aux_silent
  have expiredOther : ∀ i q, i ≠ 0 ∨ q ≠ p → expired.aux i q = .ready := g.aux_other
  have expiredRaw (i : Fin 1) (q : Port) : expired.raw i q = none := by
    rw [Subsingleton.elim i 0]
    by_cases h : q = p
    · subst q; simp [expired, trainingExpired, setRaw]
    · exact (raw_update_other edge 0 p none 0 q (Or.inr h)).trans (g.raw_other 0 q (Or.inr h))
  have rawSensor (t : ℝ) : rawFlow.path t 0 (.m p) =
      (4 / 5 : ℝ) * Real.exp (-rate * (t - g.final.time)) := by
    change readyProtectedValues θ g.final 0 p .silent (some s.time) t 0 (.m p) = _
    simp [readyProtectedValues, protectedReadyRate, g.sensor_charge, rate]
  have sensorRawEnd : expired.x 0 (.m p) =
      (4 / 5 : ℝ) * Real.exp (-rate * (s.time + 1 - g.final.time)) := rawSensor _
  have expiredCharge : expired.x 0 .q = readyPulse (1 / 10) (Real.exp (gains p)) s.time (s.time + 1) := by
    change readyPulse (g.final.x 0 .q)
      (Real.exp (g.final.x 0 (.z p)) * rawInputScale (some s.time) g.final.time)
      g.final.time (s.time + 1) = _
    exact g.response_restart _
  have chargeBand : expired.x 0 .q ∈ Icc (1 / 10) (9 / 10) := by
    refine ⟨?_, ?_⟩
    · rw [expiredCharge]
      have h := mul_nonneg (Real.exp_pos (gains p)).le
        (response_nonnegative (show 0 ≤ s.time + 1 - s.time by linarith))
      simp only [readyPulse, sub_self, zero_mul, add_zero]
      linarith
    · rw [expiredCharge]
      exact margin (s.time + 1) (by linarith)
  have restOther (q : Port) (hq : q ≠ p) : expired.x 0 (.m q) = 1 / 40 := by
    simp [expired, trainingExpired, trainingRawEnd, setRaw, readyProtectedEnd, readyProtectedValues,
      FirstInputSilent.final, FirstInputMark.silentFinal, FirstInputMark.silentBefore,
      FirstInputMark.final, setAux, readyInputEnd, readyInputValues, readyInputAuxAmplitude,
      hq, s, trainingAdmitted, trainingStart, toleranceStartOn, relax, auxPulse, readyPulse]
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp hi
  have upos : 0 < upper := by linarith
  have aboveUpper : upper < expired.x 0 (.m p) := by
    rw [sensorRawEnd]
    linarith [elapsed (s.time + 1) le_rfl]
  have expiredSensorUpper : expired.x 0 (.m p) ≤ 4 / 5 := by
    rw [sensorRawEnd]
    exact decay_upper le_rfl (by norm_num) rp.le (by linarith)
  let stop := expired.time + Real.log (expired.x 0 (.m p) / upper) / rate
  let path := readyProtectedValues θ expired 0 p .silent none
  let beforeError := readyProtectedEnd θ expired 0 p .silent none stop
  let errorStart := setAux beforeError 0 p .error
  obtain ⟨decayPos, contact, strict⟩ := protected_decay_schedule upos aboveUpper rp
  have duration : expired.time < stop := lt_add_of_pos_right _ decayPos
  have dateBound : stop < s.time + 4 := by
    have ratio : expired.x 0 (.m p) / upper ≤ 9 := (div_le_iff₀ upos).2 (by linarith)
    have expLower : (9 : ℝ) < Real.exp 3 := by
      have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 4
      norm_num [Finset.sum_range_succ] at h
      linarith
    have logUpper : Real.log (expired.x 0 (.m p) / upper) < 3 := by
      apply Real.exp_lt_exp.mp
      rw [Real.exp_log (div_pos (upos.trans aboveUpper) upos)]
      exact ratio.trans_lt expLower
    have h := (div_lt_iff₀ rp).2 (show Real.log (expired.x 0 (.m p) / upper) < 3 * rate by
      linarith [training_silent_rate_lower box p])
    change s.time + 1 + _ < s.time + 4
    linarith
  have sensorPath (t : ℝ) :
      path t 0 (.m p) = expired.x 0 (.m p) * Real.exp (-rate * (t - expired.time)) := by
    simp [path, readyProtectedValues, protectedReadyRate, rate]
  have contactAt : path stop 0 (.m p) = upper := by
    rw [sensorPath, show stop - expired.time = Real.log (expired.x 0 (.m p) / upper) / rate by
      dsimp [stop]; ring]
    exact contact
  have chargePath (t : ℝ) (ht : expired.time ≤ t) :
      path t 0 .q ∈ Icc (1 / 10) (9 / 10) := by
    simp only [path, readyProtectedValues, protectedRawAmplitude, ite_true, rawInputScale,
      mul_zero, readyPulse_zero_eq_relax]
    exact relax_mem_band (by norm_num) ht chargeBand (by norm_num)
  have rhs (t : ℝ) (ht : expired.time ≤ t) (i : Fin 1) (c : Coord) :
      field θ expired (path t) t i c = readyProtectedRhs θ expired 0 p .silent none t i c :=
    readyProtected_field expired 0 p .silent none (Or.inr rfl) expiredMain expiredSilent
      expiredOther (expiredRaw 0 p) (fun i q _ => expiredRaw i q) t ht (by simp) i c
  let tail : TrainingSilentTail θ expired p upper level stop := {
    positive := duration
    continuous := fun i c => (continuous_iff_continuousAt.mpr fun t =>
      (readyProtectedValues_derivative (θ := θ) expired 0 p .silent none t i c).continuousAt).continuousOn
    integrable := by
      intro i c
      have hc := readyProtectedRhs_continuous (θ := θ) expired 0 p .silent none i c
      apply (hc.intervalIntegrable expired.time stop).congr_uIoo
      intro t ht
      rw [uIoo_of_lt duration] at ht
      exact (rhs t ht.1.le i c).symm
    integral := by
      intro t ht i c
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun v _ => readyProtectedValues_derivative (θ := θ) expired 0 p .silent none v i c)
        ((readyProtectedRhs_continuous (θ := θ) expired 0 p .silent none i c).intervalIntegrable expired.time t)
      rw [readyProtectedValues_initial] at h
      have eq : (∫ v in expired.time..t, field θ expired (path v) v i c) =
          ∫ v in expired.time..t, readyProtectedRhs θ expired 0 p .silent none v i c := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.1
        intro v hv
        exact rhs v hv.1.le i c
      rw [eq, h]
      change path t i c = _
      ring
    main_guard := fun t ht => by linarith [(chargePath t ht.1).2, threshold.1]
    sensor_guard := by
      intro t ht
      change upper < path t 0 (.m p)
      rw [sensorPath]
      have before := ht.2
      change t < stop at before
      dsimp [stop] at before
      exact strict _ (sub_nonneg.mpr ht.1) (by linarith)
    other_guard := by
      intro t _ q hq
      norm_num [readyProtectedValues, hq, restOther q hq, relax]
    contact := contactAt
    pending := by
      intro v hv
      change v ∈ s.pending at hv
      have hv' : v = d := by simpa [s, trainingAdmitted, d] using hv
      subst v
      change stop < s.time + 16
      linarith
  }
  have prepared : PhysicalInvariant θ s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      norm_num [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw, auxUpper]
    · intro i q
      rw [Subsingleton.elim i 0]
      exact caps q
    · intro i
      norm_num [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw]
    · intro i
      norm_num [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw]
  let before : Execution θ route s expired :=
    (g.execution route).append (.cons (.flow rawFlow) (.cons (.jump expiry) (.nil _)))
  have energyStart := ((before.physical_invariant box prepared).reserve 0)
  have energyEnd : 50 ≤ errorStart.x 0 .energy ∧ errorStart.x 0 .energy ≤ 100 := by
    let work := fun t => rate * expired.x 0 (.m p) * Real.exp (-rate * (t - expired.time))
    apply reserve_of_derivative duration.le (show Continuous work by dsimp [work]; fun_prop)
      (energy := fun t => path t 0 .energy)
    · intro t
      simpa [path, readyProtectedValues, readyProtectedRhs, protectedRawAmplitude,
        protectedAuxCoeff, protectedReadyRate, rawInputScale, work, rate] using
        readyProtectedValues_derivative (θ := θ) expired 0 p .silent none t 0 .energy
    · change path expired.time 0 .energy ∈ Icc (50 : ℝ) 100
      rw [show path expired.time = expired.x from readyProtectedValues_initial _ _ _ _ _]
      exact energyStart
    · intro t ht
      have h : Real.exp (-rate * (t - expired.time)) ≤ 1 := Real.exp_le_one_iff.mpr
        (by nlinarith [mul_nonneg rp.le (sub_nonneg.mpr ht.1)])
      have positive := mul_pos rp (upos.trans aboveUpper)
      have hcoeff := mul_le_mul rateUpper expiredSensorUpper (upos.trans aboveUpper).le (by norm_num)
      dsimp [work]
      exact ⟨mul_nonneg positive.le (Real.exp_pos _).le,
        (mul_le_mul_of_nonneg_left h positive.le).trans (by linarith)⟩
  have startGain (q : Port) : errorStart.x 0 (.z q) = gains q := g.gain_preserved 0 q
  obtain ⟨handoff⟩ := error_read_handoff (s := errorStart) box threshold hi lo
    (by rw [startGain]; exact gain) (fun q => by rw [startGain]; exact caps q)
    (by change (0 : ℝ) ≤ 2 / 25 ∧ (2 / 25 : ℝ) ≤ 11 / 10; norm_num)
    energyEnd (expiredMain 0) (chargePath stop duration.le)
    (by simp [errorStart, setAux]) contactAt
    (fun q hq => by
      refine ⟨?_, ?_⟩
      · simpa [errorStart, setAux, beforeError, readyProtectedEnd, hq] using expiredOther 0 q (Or.inr hq)
      · simp [errorStart, setAux, beforeError, readyProtectedEnd,
          readyProtectedValues, hq, restOther q hq, relax])
    (expiredRaw 0) (by change stop + 12 ≤ s.time + 16; linarith) rfl
  refine ⟨⟨train, f, g, rawFlow, expiry, ?_, ?_, ?_, stop, tail, handoff, ?_, handoff.read_date, ?_⟩⟩
  · intro t ht
    have eq := f.flow.ready_single_pulse_solution 0 p s.time (f.main_ready 0) raw
      (fun q h => otherRaw 0 q (Or.inr h)) (by rw [f.aux_ready]; decide) t ⟨ht.1, ht.2.le⟩
    rw [eq]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    linarith [margin t ht.1, threshold.1]
  · intro t ht
    have hm : f.final.aux 0 p = .mark := by simp [FirstInputMark.final, setAux]
    have eq := g.flow.ready_single_pulse_solution 0 p s.time (f.main_ready 0) f.raw_active
      (fun q h => f.raw_other 0 q (Or.inr h)) (by rw [hm]; decide) t ⟨ht.1, ht.2.le⟩
    rw [eq]
    have restart := f.protected_response_restart t
    change readyPulse (f.final.x 0 .q)
      (Real.exp (f.final.x 0 (.z p)) * Real.exp (-a * (f.final.time - s.time))) f.final.time t = _ at restart
    rw [restart]
    have ht' : s.time ≤ t := by
      have h : s.time + f.latency ≤ t := ht.1
      linarith [f.early]
    linarith [margin t ht', threshold.1]
  · intro t ht
    constructor
    · change readyProtectedValues θ g.final 0 p .silent (some s.time) t 0 .q < level
      simp only [readyProtectedValues, protectedRawAmplitude, ite_true]
      rw [g.response_restart]
      linarith [margin t (gAfter.trans ht.1), threshold.1]
    · rw [rawSensor]
      linarith [elapsed t ht.2.le]
  · intro t ht
    let read := handoff.decision
    have after : handoff.readStart.time ≤ read.silent.final.time := by
      change handoff.readStart.time ≤ handoff.readStart.time + read.mark.latency +
        Real.log (5 / 4) / (θ 0).lm p
      linarith [read.mark.early, (box.aux_durations_positive 0 p).1]
    have deadline := read.outcome.2.1
    have h := silent_above_upper (rate := rate) rp.le rateUpper
      (show t - read.silent.final.time ≤ 1 by linarith [ht.2])
    have eq : readyProtectedValues θ read.silent.final 0 p .silent
        (some handoff.readStart.time) t 0 (.m p) =
        (4 / 5 : ℝ) * Real.exp (-rate * (t - read.silent.final.time)) := by
      simp [readyProtectedValues, protectedReadyRate, read.silent.sensor_charge, rate]
    change upper < readyProtectedValues θ read.silent.final 0 p .silent
      (some handoff.readStart.time) t 0 (.m p)
    rw [eq]
    linarith
  · have h := handoff.span.dose
    rw [startGain] at h
    linarith

/-- The full small fabrication box needs no additional timing premise. -/
theorem training_read_small_box {θ time gains p upper lower level}
    (box : @PhysicalBox 1 θ (3 / 1000))
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : |lower - 1 / 40| ≤ 1 / 800)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    Nonempty (TrainingRead θ time gains p upper lower level) :=
  training_read_exists box (training_silent_rate_small_box box p) threshold hi lo gain caps

/-- At all three nominal thresholds, the entire two-pulse trajectory
embeds as an execution of the original kernel. -/
noncomputable def TrainingRead.nominalExecution {θ time gains p}
    (run : TrainingRead θ time gains p (1 / 10) (1 / 40) 1) :
    Execution θ (fun _ _ => []) (trainingStart time gains p) run.handoff.decision.final := by
  let edge := trainingRawEnd θ (trainingAdmitted time gains p) p run.silent
  let expired := trainingExpired θ (trainingAdmitted time gains p) p run.silent
  let boundary := readyProtectedEnd θ expired 0 p .silent none run.stop
  have mode : expired.aux 0 p = .silent := run.silent.aux_silent
  let flow : Flow θ expired boundary := {
    positive := run.tail.positive
    path := readyProtectedValues θ expired 0 p .silent none
    initial := readyProtectedValues_initial _ _ _ _ _
    final := rfl
    main_fixed := rfl
    aux_fixed := rfl
    raw_fixed := rfl
    queue_fixed := rfl
    continuous := run.tail.continuous
    integrable := run.tail.integrable
    mark_integrable := by intro i q; simp [markAct, show expired.main i = .ready from run.silent.main_ready i]
    integral_eq := run.tail.integral
    guards := by
      intro t ht
      constructor
      · intro i
        rw [Subsingleton.elim i 0, show expired.main 0 = .ready from run.silent.main_ready 0]
        exact run.tail.main_guard t ht
      · intro i q
        rw [Subsingleton.elim i 0]
        by_cases h : q = p
        · subst q
          rw [mode]
          exact run.tail.sensor_guard t ht
        · rw [show expired.aux 0 q = .ready from run.silent.aux_other 0 q (Or.inr h)]
          exact run.tail.other_guard t ht q h
    raw_support := by
      intro i q origin h
      rw [Subsingleton.elim i 0] at h
      by_cases hq : q = p
      · subst q
        simp [expired, trainingExpired, setRaw] at h
      · rw [show expired.raw 0 q = none from
          (raw_update_other edge 0 p none 0 q (Or.inr hq)).trans (run.silent.raw_other 0 q (Or.inr hq))] at h
        cases h
    pending_urgent := fun d hd => (run.tail.pending d hd).le
  }
  let suffix := Execution.cons (.flow run.rawLeg) (.cons (.jump run.expiry)
    (.cons (.flow flow) (.cons (.jump (.error boundary 0 p mode run.tail.contact))
      run.handoff.nominalExecution)))
  exact .cons (.jump run.train) ((run.silent.execution (fun _ _ => [])).append suffix)

end RecursiveLearning.Native
