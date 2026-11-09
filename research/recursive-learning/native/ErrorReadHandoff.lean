import TolerantErrorDose

/-! A single-cell handoff from an exposed ERROR segment to a scheduled
read on the same port. The charge, memories and energy are carried through
the sensor reopening, the quiet wait and the delivery. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid MeasureTheory Set

private theorem quiet_error_field {θ : Fin 1 → Parameters} {s : Snapshot 1} {p t}
    (main : s.main 0 = .ready) (aux : s.aux 0 p = .error)
    (other : ∀ q, q ≠ p → s.aux 0 q = .ready) (raw : ∀ q, s.raw 0 q = none)
    (power : 0 < errorTailEnergy θ s 0 p none t)
    (cap : errorTailGain θ s 0 p t < Real.log ((θ 0).cap p)) (c : Coord) :
    field θ s (errorTailValues θ s 0 p none t) t 0 c = errorTailRhs θ s 0 p none t 0 c := by
  have act (q : Port) : errorAct θ s (errorTailValues θ s 0 p none t) 0 q =
      if q = p then 8 * (θ 0).le p * errorTailSensor θ s 0 p t else 0 := by
    by_cases h : q = p
    · subst q; simp [errorAct, aux, main, errorTailValues, power, cap]
    · simp [errorAct, other q h, h]
  have drain (q : Port) :
      (if s.aux 0 q = .ready then 0
        else auxDrain (θ 0) (s.aux 0 q) q (errorTailValues θ s 0 p none t 0 (.m q))) =
      if q = p then (θ 0).le p * errorTailSensor θ s 0 p t else 0 := by
    by_cases h : q = p
    · subst q; simp [aux, auxDrain, errorTailValues]
    · simp [other q h, h]
  cases c with
  | q => simp [field, main, drive, current, raw, errorTailRhs, errorTailDrive, rawInputScale]
  | m q =>
    by_cases h : q = p
    · subst q; simp [field, aux, auxDrain, errorTailValues, errorTailRhs]
    · simp [field, other q h, current, raw, errorTailRhs, errorTailValues, h]
  | z q => simp [field, act, errorTailRhs]
  | b => simp [field, markAct, main, errorTailRhs]
  | energy =>
    simp [field, work, main, drive, current, raw, drain, act, markAct,
      errorTailRhs, errorTailWork, errorTailDrive, rawInputScale]
    ring

private theorem quiet_error_charge {θ : Fin 1 → Parameters} {s : Snapshot 1} {p t}
    (charge : s.x 0 .q = 1 / 10) :
    errorTailValues θ s 0 p none t 0 .q = 1 / 10 := by
  simp [errorTailValues, errorTailMain, errorTailDrive, rawInputScale, linearConvolution,
    relax, charge]

private theorem quiet_error_reserve {θ : Fin 1 → Parameters} {s : Snapshot 1} {p t}
    (rate : 0 < (θ 0).le p) (ht : s.time ≤ t)
    (upper : 0 ≤ s.x 0 (.m p)) (small : s.x 0 (.m p) ≤ 21 / 200)
    (energy : 51 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100) :
    50 ≤ errorTailEnergy θ s 0 p none t ∧ errorTailEnergy θ s 0 p none t ≤ 100 := by
  let forcing := errorTailWork θ s 0 p none
  let m := errorTailSensor θ s 0 p
  have work (v : ℝ) : forcing v = 9 * (θ 0).le p * m v := by
    simp [forcing, m, errorTailWork, errorTailDrive, rawInputScale]
  have pos (v : ℝ) : 0 ≤ forcing v := by
    rw [work]
    exact mul_nonneg (by positivity) (mul_nonneg upper (Real.exp_pos _).le)
  have continuous : Continuous forcing := errorTailWork_continuous s 0 p none
  have mass := linearConvolution_le_mass continuous (by norm_num : (0 : ℝ) ≤ 10) ht (fun v _ => pos v)
  have nonneg : 0 ≤ linearConvolution 10 forcing s.time t := by
    simpa [linearConvolution] using linearConvolution_mono (f := fun _ => 0) continuous_const continuous
      (rate := 10) ht (fun v _ => pos v)
  have hderiv (v : ℝ) : HasDerivAt (fun u => -9 * m u) (forcing v) v := by
    rw [work]
    convert (errorTailSensor_derivative (θ := θ) s 0 p v).const_mul (-9) using 1
    dsimp [m]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hderiv v)
    (continuous.intervalIntegrable s.time t)] at mass
  have m0 : m s.time = s.x 0 (.m p) := by simp [m, errorTailSensor]
  have mt : 0 ≤ m t := mul_nonneg upper (Real.exp_pos _).le
  have decay := Real.exp_le_one_iff.mpr (show -10 * (t - s.time) ≤ 0 by linarith)
  have carry := mul_le_mul_of_nonpos_left decay (sub_nonpos.mpr energy.2)
  have below : (s.x 0 .energy - 100) * Real.exp (-10 * (t - s.time)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr energy.2) (Real.exp_pos _).le
  rw [m0] at mass
  change 50 ≤ relax 10 100 (s.x 0 .energy) s.time t - linearConvolution 10 forcing s.time t ∧ _
  constructor <;> dsimp [errorTailEnergy, relax] <;> linarith

private theorem quiet_decay_bound {start finish : ℝ} (wait : start + 11 ≤ finish) :
    Real.exp (-(1 / 2) * (finish - start)) ≤ 1 / 125 := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 11 / 2 by norm_num) 9
  norm_num [Finset.sum_range_succ] at h
  have hex : (125 : ℝ) ≤ Real.exp (11 / 2) := by linarith
  calc
    _ ≤ Real.exp (-(11 / 2)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := by rw [Real.exp_neg]; simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hex

/-- The read delivery is fixed at the starting time plus twelve. -/
def errorReadDelivery (s : Snapshot 1) (p : Port) : Delivery 1 := ⟨0, p, s.time + 12⟩

/-- One continuous experiment. The changed ERROR exit is checked at the
realized lower charge. It changes only the sensor mode. The quiet flow
and arrival are native moves, and the read starts at their exact endpoint. -/
structure ErrorReadHandoff (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    (upper lower level : ℝ) where
  learned : ℝ
  span : ExposedErrorSpan θ p (s.x 0 (.z p)) learned upper lower
  start_eq : span.start = s
  error_main_guard : ∀ t ∈ Ico s.time span.stop, span.path t 0 .q < level
  error_other_guards : ∀ t ∈ Ico s.time span.stop, ∀ q, q ≠ p →
    s.aux 0 q = .ready ∧ span.path t 0 (.m q) < 1
  error_raw_empty : ∀ q, s.raw 0 q = none
  error_pending_later : ∀ d ∈ s.pending, span.stop < d.due
  quiet : Flow θ
    (setAux {s with time := span.stop, x := span.path span.stop} 0 p .ready)
    (quietAt (setAux {s with time := span.stop, x := span.path span.stop} 0 p .ready)
      (errorReadDelivery s p).due)
  quiet_main_guard : ∀ t ∈ Ico span.stop (errorReadDelivery s p).due, quiet.path t 0 .q < level
  readStart : Snapshot 1
  arrival : Jump (fun _ _ => [])
    (quietAt (setAux {s with time := span.stop, x := span.path span.stop} 0 p .ready)
      (errorReadDelivery s p).due) readStart
  learned_at_read : readStart.x 0 (.z p) = learned
  decision : TolerantSnapshotDecision θ readStart p true level

/-- A single already-exposed ERROR phase trains the port, then a scheduled
pulse reads it. The initial queue contains only that read pulse. The other
sensors are at rest and the main cell is READY at resting charge. -/
theorem error_read_handoff {θ ε s p upper lower level}
    (box : @PhysicalBox 1 θ ε) (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : |lower - 1 / 40| ≤ 1 / 800)
    (initialGain : 7 / 6 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 6 / 5)
    (gainCap : ∀ q, s.x 0 (.z q) ≤ Real.log ((θ 0).cap q))
    (recovery : 0 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 11 / 10)
    (energy : 51 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100)
    (main : s.main 0 = .ready) (charge : s.x 0 .q = 1 / 10)
    (aux : s.aux 0 p = .error) (sensor : s.x 0 (.m p) = upper)
    (other : ∀ q, q ≠ p → s.aux 0 q = .ready ∧ s.x 0 (.m q) = 1 / 40)
    (raw : ∀ q, s.raw 0 q = none) (queue : s.pending = [errorReadDelivery s p]) :
    Nonempty (ErrorReadHandoff θ s p upper lower level) := by
  let r := (θ 0).le p
  let stop := s.time + Real.log (upper / lower) / r
  let path := errorTailValues θ s 0 p none
  let learned := s.x 0 (.z p) + 8 * (upper - lower)
  have rpos : 0 < r := (box.rates_positive 0 p).2.2
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp hi
  obtain ⟨lo₁, lo₂⟩ := abs_le.mp lo
  have lowerPos : 0 < lower := by linarith
  have upperPos : 0 < upper := by linarith
  have ratio : 1 < upper / lower := (lt_div_iff₀ lowerPos).2 (by linarith)
  have duration : s.time < stop := by
    dsimp [stop]
    exact lt_add_of_pos_right _ (div_pos (Real.log_pos ratio) rpos)
  have durationUpper : stop < s.time + 1 := by
    have param := ((box.2 0 p).2.2.2.1).1
    change a / (3 / 20) * (1 - ε) ≤ r at param
    have rlower : (6 : ℝ) ≤ r := by
      have bound := mul_le_mul (show (1 : ℝ) / (3 / 20) ≤ a / (3 / 20) by
        gcongr; exact a_coarse_bounds.1.le) (show (9 / 10 : ℝ) ≤ 1 - ε by
          linarith [box.epsilon_bounds.2]) (by norm_num) (by linarith [a_coarse_bounds.1])
      norm_num at bound
      exact bound.trans param
    have rat : upper / lower ≤ 5 := (div_le_iff₀ lowerPos).2 (by linarith)
    have logBound := (Real.log_le_sub_one_of_pos (zero_lt_one.trans ratio)).trans (show upper / lower - 1 ≤ 4 by linarith)
    dsimp [stop]
    have h := (div_lt_iff₀ rpos).2 (show Real.log (upper / lower) < 1 * r by linarith)
    linarith
  have endpoint : errorTailSensor θ s 0 p stop = lower := by
    rw [errorTailSensor, sensor]
    change upper * Real.exp (-r * (stop - s.time)) = lower
    have hx : -r * (stop - s.time) = -Real.log (upper / lower) := by
      dsimp [stop]
      field_simp
      ring
    rw [hx, Real.exp_neg, Real.exp_log (div_pos upperPos lowerPos)]
    field_simp
  have sensorAbove (t : ℝ) (ht : t < stop) : lower < errorTailSensor θ s 0 p t := by
    rw [← endpoint]
    simp only [errorTailSensor, sensor]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by nlinarith [mul_pos rpos (sub_pos.mpr ht)])) upperPos
  have sensorFloor (t : ℝ) (ht : t ≤ stop) : lower ≤ errorTailSensor θ s 0 p t :=
    ht.eq_or_lt.elim (fun h => h ▸ endpoint.ge) (fun h => (sensorAbove t h).le)
  have learnedGain : 2 ≤ Real.exp learned ∧ Real.exp learned ≤ 12 / 5 :=
    one_error_dose_gain hi lo initialGain
  have learnedCap : learned < Real.log ((θ 0).cap p) := by
    have h := (box.2 0 p).1.1
    change 4 * (1 - ε) ≤ (θ 0).cap p at h
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (box.cap_positive 0 p)]
    linarith [box.epsilon_bounds.2, learnedGain.2]
  have reserve (t : ℝ) (ht : s.time ≤ t) :
      50 ≤ errorTailEnergy θ s 0 p none t ∧ errorTailEnergy θ s 0 p none t ≤ 100 :=
    quiet_error_reserve rpos ht (by rw [sensor]; linarith) (by rw [sensor]; linarith) energy
  have gates (t : ℝ) (ht : t ∈ Icc s.time stop) :
      0 < errorTailEnergy θ s 0 p none t ∧ errorTailGain θ s 0 p t < Real.log ((θ 0).cap p) := by
    refine ⟨by linarith [(reserve t ht.1).1], lt_of_le_of_lt ?_ learnedCap⟩
    dsimp [errorTailGain, learned]
    rw [sensor]
    linarith [sensorFloor t ht.2]
  have fieldEq (t : ℝ) (ht : t ∈ Icc s.time stop) (i : Fin 1) (c : Coord) :
      field θ s (path t) t i c = errorTailRhs θ s 0 p none t i c := by
    rw [Subsingleton.elim i 0]
    exact quiet_error_field main aux (fun q h => (other q h).1) raw
      (gates t ht).1 (gates t ht).2 c
  let span : ExposedErrorSpan θ p (s.x 0 (.z p)) learned upper lower := {
    start := s
    stop := stop
    path := path
    positive := duration
    ready := main
    error := aux
    gates := by
      intro t ht
      simpa [path, errorTailValues] using gates t ht
    initial := errorTailValues_initial (θ := θ) s 0 p none
    continuous := fun i c => (continuous_iff_continuousAt.mpr fun t =>
      (errorTailValues_derivative (θ := θ) s 0 p none t i c).continuousAt).continuousOn
    integrable := by
      intro i c
      apply ((errorTailRhs_continuous (θ := θ) s 0 p none i c).intervalIntegrable _ _).congr_uIoo
      intro t ht
      rw [uIoo_of_lt duration] at ht
      exact (fieldEq t ⟨ht.1.le, ht.2.le⟩ i c).symm
    sensor_guard := by intro t ht; simpa [path, errorTailValues] using sensorAbove t ht.2
    charge_in := sensor
    charge_out := by simpa [path, errorTailValues] using endpoint
    gain_in := rfl
    gain_out := by simp [path, learned, errorTailValues, errorTailGain, endpoint, sensor]
    integral_eq := by
      intro t ht i c
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun v _ => errorTailValues_derivative (θ := θ) s 0 p none v i c)
        ((errorTailRhs_continuous (θ := θ) s 0 p none i c).intervalIntegrable s.time t)
      rw [errorTailValues_initial] at h
      have eq : (∫ v in s.time..t, field θ s (path v) v i c) =
          ∫ v in s.time..t, errorTailRhs θ s 0 p none v i c := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.1
        intro v hv
        exact fieldEq v ⟨hv.1.le, hv.2.le.trans ht.2⟩ i c
      rw [eq, h]
      change path t i c = _
      ring
  }
  let reopened := setAux {s with time := stop, x := path stop} 0 p .ready
  let d := errorReadDelivery s p
  let beforeRead := quietAt reopened d.due
  let admitted := {setRaw beforeRead 0 p (some beforeRead.time) with pending := []}
  have wait : reopened.time + 11 ≤ d.due := by
    change stop + 11 ≤ s.time + 12
    linarith
  have ready (i : Fin 1) : reopened.main i = .ready := by
    rw [Subsingleton.elim i 0]
    exact main
  have sensors (i : Fin 1) (q : Port) : reopened.aux i q = .ready := by
    rw [Subsingleton.elim i 0]
    by_cases h : q = p
    · subst q; simp [reopened, setAux]
    · simp [reopened, setAux, h, (other q h).1]
  have noneRaw (i : Fin 1) (q : Port) : reopened.raw i q = none := by
    rw [Subsingleton.elim i 0]
    exact raw q
  have chargeRest (i : Fin 1) : reopened.x i .q = 1 / 10 := by
    rw [Subsingleton.elim i 0]
    exact quiet_error_charge charge
  have reopenedSensor (q : Port) : reopened.x 0 (.m q) = if q = p then lower else 1 / 40 := by
    by_cases h : q = p
    · subst q; simpa [reopened, path, setAux, errorTailValues] using endpoint
    · simp [reopened, path, setAux, errorTailValues, h, (other q h).2, relax]
  let quiet : Flow θ reopened beforeRead :=
    quietFlow reopened (by linarith) ready sensors noneRaw
      (fun i => by rw [chargeRest]; norm_num)
      (fun i q => by rw [Subsingleton.elim i 0, reopenedSensor]; split <;> linarith)
      (by change ∀ v ∈ s.pending, d.due ≤ v.due; simp [queue, d])
  have arrival : Jump (fun _ _ => []) beforeRead admitted :=
    .arrive beforeRead d [] [] queue rfl (noneRaw 0 p)
  have preserved (q : Port) : admitted.x 0 (.z q) = reopened.x 0 (.z q) := rfl
  have got : admitted.x 0 (.z p) = learned := span.gain_out
  have readReady : ReadoutReady admitted p := {
    main := ready
    charge := by
      change relax (1 / 2) (1 / 10) (reopened.x 0 .q) reopened.time d.due = _
      simp [chargeRest, relax]
    aux := sensors
    rest := by
      intro i q
      rw [Subsingleton.elim i 0]
      change RestBand (relax (1 / 2) (1 / 40) (reopened.x 0 (.m q)) reopened.time d.due)
      rw [reopenedSensor]
      by_cases h : q = p
      · rw [ite_eq_left h]
        have decay := quiet_decay_bound wait
        have nonneg := Real.exp_pos (-(1 / 2) * (d.due - reopened.time))
        have bound := mul_le_mul lo decay nonneg.le (by norm_num : (0 : ℝ) ≤ 1 / 800)
        rw [← abs_of_nonneg nonneg.le, ← abs_mul] at bound
        obtain ⟨low, high⟩ := abs_le.mp bound
        constructor <;> dsimp [relax] <;> linarith
      · norm_num [h, relax, RestBand]
    raw := by simp [admitted, setRaw]
    otherRaw := by
      intro i q h
      have hi : i = 0 := Subsingleton.elim _ _
      have hq : q ≠ p := h.resolve_left (not_not_intro hi)
      simpa [admitted, setRaw, hi, hq, beforeRead, quietAt] using noneRaw 0 q
    empty := rfl
  }
  have physical : PhysicalInvariant θ admitted := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [Subsingleton.elim i 0]
      refine ⟨recovery.1, by rw [readReady.charge]; norm_num, fun q => ?_⟩
      rw [readReady.aux]
      have h := (readReady.rest 0 q).2
      simp only [auxUpper]
      linarith
    · intro i q
      rw [Subsingleton.elim i 0, preserved]
      by_cases h : q = p
      · subst q
        rw [← preserved p, got]
        exact learnedCap.le
      · simpa [reopened, setAux, path, errorTailValues, h] using gainCap q
    · intro i
      rw [Subsingleton.elim i 0]
      exact recovery.2
    · intro i
      rw [Subsingleton.elim i 0]
      have he := reserve stop duration.le
      change 50 ≤ relax 10 100 (errorTailEnergy θ s 0 p none stop) reopened.time d.due ∧
        relax 10 100 (errorTailEnergy θ s 0 p none stop) reopened.time d.due ≤ 100
      have e0 := Real.exp_pos (-10 * (d.due - reopened.time))
      have e1 := Real.exp_le_one_iff.mpr (show -10 * (d.due - reopened.time) ≤ 0 by linarith)
      have h1 := mul_le_mul_of_nonpos_left e1 (sub_nonpos.mpr he.2)
      have h2 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr he.2) e0.le
      constructor <;> dsimp [relax] <;> linarith
  obtain ⟨read⟩ := tolerant_snapshot_readout (high := true) box physical readReady threshold
    (show 2 ≤ Real.exp (admitted.x 0 (.z p)) ∧ Real.exp (admitted.x 0 (.z p)) ≤ 12 / 5 by
      rw [got]; exact learnedGain)
  refine ⟨⟨learned, span, rfl, ?_, ?_, raw, ?_, quiet, ?_, admitted, arrival, got, read⟩⟩
  · intro t _
    change path t 0 .q < level
    rw [show path t 0 .q = 1 / 10 from quiet_error_charge charge]
    linarith [threshold.1]
  · intro t _ q hq
    refine ⟨(other q hq).1, ?_⟩
    change path t 0 (.m q) < 1
    norm_num [path, errorTailValues, hq, (other q hq).2, relax]
  · intro v hv
    rw [queue, List.mem_singleton] at hv
    subst v
    change stop < s.time + 12
    linarith
  · intro t _
    change relax (1 / 2) (1 / 10) (reopened.x 0 .q) reopened.time t < level
    rw [chargeRest]
    simp only [relax, sub_self, zero_mul, add_zero]
    linarith [threshold.1]

/-- At the nominal ERROR exit and FIRE thresholds the joined path is
an execution of the original kernel, from the same supplied ERROR state. -/
noncomputable def ErrorReadHandoff.nominalExecution {θ s p upper}
    (run : ErrorReadHandoff θ s p upper (1 / 40) 1) :
    Execution θ (fun _ _ => []) s run.decision.final := by
  let span := run.span
  let boundary : Snapshot 1 := {s with time := span.stop, x := span.path span.stop}
  have same : span.start = s := run.start_eq
  have main : s.main 0 = .ready := same ▸ span.ready
  have mode : s.aux 0 p = .error := same ▸ span.error
  let flow : Flow θ s boundary := {
    positive := same ▸ span.positive
    path := span.path
    initial := by simpa only [same] using span.initial
    final := rfl
    main_fixed := rfl
    aux_fixed := rfl
    raw_fixed := rfl
    queue_fixed := rfl
    continuous := by simpa only [same] using span.continuous
    integrable := by simpa only [same] using span.integrable
    mark_integrable := by
      intro i q
      rw [Subsingleton.elim i 0]
      simp [markAct, main]
    integral_eq := by simpa only [same] using span.integral_eq
    guards := by
      intro t ht
      constructor
      · intro i
        rw [Subsingleton.elim i 0, main]
        exact run.error_main_guard t ht
      · intro i q
        rw [Subsingleton.elim i 0]
        by_cases h : q = p
        · subst q
          rw [mode]
          exact span.sensor_guard t (same.symm ▸ ht)
        · obtain ⟨hm, hq⟩ := run.error_other_guards t ht q h
          rw [hm]
          exact hq
    raw_support := by intro i q origin h; rw [Subsingleton.elim i 0, run.error_raw_empty] at h; cases h
    pending_urgent := fun d hd => (run.error_pending_later d hd).le
  }
  exact .cons (.flow flow) (.cons (.jump (.auxReady boundary 0 p mode span.charge_out))
    (.cons (.flow run.quiet) (.cons (.jump run.arrival) run.decision.nominalExecution)))

end RecursiveLearning.Native
