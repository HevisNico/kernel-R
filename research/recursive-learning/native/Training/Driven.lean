import Training.TrainingLoop

/-! The cell before a FIRE, driven by any number of live pulses. While
the main cell is READY and no sensor is in ERROR, no gain is written and
the recovery rate is constant. The main charge sums the live pulses, and
each sensor follows its own pulse or its own decay. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- The main cell is READY and no sensor is in ERROR. -/
structure Driven (s : Snapshot 1) : Prop where
  main : s.main 0 = .ready
  no_error : ∀ q, s.aux 0 q ≠ .error

/-- The remaining fraction of the pulse on port `q`, zero without pulse. -/
noncomputable def rawScale (s : Snapshot 1) (q : Port) : ℝ :=
  rawInputScale (s.raw 0 q) s.time

/-- The live pulses weighted by their gains. -/
noncomputable def drivenAmplitude (s : Snapshot 1) : ℝ :=
  ∑ q : Port, Real.exp (s.x 0 (.z q)) * rawScale s q

noncomputable def drivenSensor (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) (t : ℝ) : ℝ :=
  if s.aux 0 q = .ready then
    auxPulse (s.x 0 (.m q)) ((θ 0).inputGain q * rawScale s q) s.time t
  else s.x 0 (.m q) * Real.exp (-sensorRate θ s q * (t - s.time))

noncomputable def drivenWork (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) : ℝ :=
  drivenAmplitude s * a * Real.exp (-a * (t - s.time)) +
  ∑ q : Port, if s.aux 0 q = .ready then
      (θ 0).inputGain q * (rawScale s q * a * Real.exp (-a * (t - s.time)))
    else sensorRate θ s q * drivenSensor θ s q t

noncomputable def drivenEnergy (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) : ℝ :=
  relax 10 100 (s.x 0 .energy) s.time t - linearConvolution 10 (drivenWork θ s) s.time t

noncomputable def drivenValues (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) : Values 1 :=
  fun _ c => match c with
  | .q => readyPulse (s.x 0 .q) (drivenAmplitude s) s.time t
  | .m q => drivenSensor θ s q t
  | .z q => s.x 0 (.z q)
  | .b => s.x 0 .b
  | .energy => drivenEnergy θ s t

noncomputable def drivenAt (θ : Fin 1 → Parameters) (s : Snapshot 1) (T : ℝ) : Snapshot 1 :=
  {s with time := T, x := drivenValues θ s T}

noncomputable def drivenRhs (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) : Coord → ℝ
  | .q => (1 / 2) * (1 / 10 - readyPulse (s.x 0 .q) (drivenAmplitude s) s.time t) +
      drivenAmplitude s * a * Real.exp (-a * (t - s.time))
  | .m q => if s.aux 0 q = .ready then
      (1 / 2) * (1 / 40 - drivenSensor θ s q t) +
        (θ 0).inputGain q * rawScale s q * a * Real.exp (-a * (t - s.time))
      else -sensorRate θ s q * drivenSensor θ s q t
  | .z _ => 0
  | .b => 0
  | .energy => 10 * (100 - drivenEnergy θ s t) - drivenWork θ s t

theorem drivenSensor_derivative (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) (t : ℝ) :
    HasDerivAt (drivenSensor θ s q) (drivenRhs θ s t (.m q)) t := by
  by_cases hr : s.aux 0 q = .ready
  · have h := auxPulse_derivative (s.x 0 (.m q)) ((θ 0).inputGain q * rawScale s q) s.time t
    have f : drivenSensor θ s q =
        auxPulse (s.x 0 (.m q)) ((θ 0).inputGain q * rawScale s q) s.time := by
      funext v
      simp [drivenSensor, hr]
    rw [f]
    simpa [drivenRhs, drivenSensor, hr] using h
  · have h := ((((hasDerivAt_id t).sub_const s.time).const_mul (-sensorRate θ s q)).exp).const_mul
      (s.x 0 (.m q))
    have f : drivenSensor θ s q =
        fun v => s.x 0 (.m q) * Real.exp (-sensorRate θ s q * (id v - s.time)) := by
      funext v
      simp [drivenSensor, hr]
    rw [f]
    convert h using 1
    simp only [drivenRhs, drivenSensor, hr, ite_false, id_eq]
    ring

theorem drivenSensor_continuous (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) :
    Continuous (drivenSensor θ s q) :=
  continuous_iff_continuousAt.mpr fun t => (drivenSensor_derivative θ s q t).continuousAt

theorem drivenWork_continuous (θ : Fin 1 → Parameters) (s : Snapshot 1) :
    Continuous (drivenWork θ s) := by
  unfold drivenWork
  apply Continuous.add
  · fun_prop
  · apply continuous_finsetSum
    intro q _
    by_cases h : s.aux 0 q = .ready
    · simp only [h, ite_true]
      fun_prop
    · simp only [h, ite_false]
      exact continuous_const.mul (drivenSensor_continuous θ s q)

theorem drivenEnergy_derivative (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ) :
    HasDerivAt (drivenEnergy θ s) (10 * (100 - drivenEnergy θ s t) - drivenWork θ s t) t := by
  exact ((relax_derivative 10 100 (s.x 0 .energy) s.time t).sub
    (linearConvolution_derivative (drivenWork_continuous θ s) 10 s.time t)).congr_deriv
      (by dsimp only [drivenEnergy]; ring)

theorem drivenValues_derivative (θ : Fin 1 → Parameters) (s : Snapshot 1) (t : ℝ)
    (i : Fin 1) (c : Coord) :
    HasDerivAt (fun v => drivenValues θ s v i c) (drivenRhs θ s t c) t := by
  cases c with
  | q => exact readyPulse_derivative _ _ _ _
  | m q => exact drivenSensor_derivative θ s q t
  | z q => exact hasDerivAt_const t (s.x 0 (.z q))
  | b => exact hasDerivAt_const t (s.x 0 .b)
  | energy => exact drivenEnergy_derivative θ s t

theorem drivenRhs_continuous (θ : Fin 1 → Parameters) (s : Snapshot 1) (c : Coord) :
    Continuous (fun t => drivenRhs θ s t c) := by
  have sensor := drivenSensor_continuous θ s
  have work := drivenWork_continuous θ s
  have energy : Continuous (drivenEnergy θ s) :=
    continuous_iff_continuousAt.mpr fun t => (drivenEnergy_derivative θ s t).continuousAt
  have charge : Continuous (readyPulse (s.x 0 .q) (drivenAmplitude s) s.time) :=
    continuous_iff_continuousAt.mpr fun t => (readyPulse_derivative _ _ _ t).continuousAt
  cases c with
  | q =>
    simp only [drivenRhs]
    exact (continuous_const.mul (continuous_const.sub charge)).add (by fun_prop)
  | m q =>
    by_cases h : s.aux 0 q = .ready
    · simp only [drivenRhs, h, ite_true]
      exact (continuous_const.mul (continuous_const.sub (sensor q))).add (by fun_prop)
    · simp only [drivenRhs, h, ite_false]
      exact continuous_const.mul (sensor q)
  | z q => simp only [drivenRhs]; fun_prop
  | b => simp only [drivenRhs]; fun_prop
  | energy =>
    simp only [drivenRhs]
    exact (continuous_const.mul (continuous_const.sub energy)).sub work

theorem drivenValues_initial (θ : Fin 1 → Parameters) (s : Snapshot 1) :
    drivenValues θ s s.time = s.x := by
  funext j c
  rw [Subsingleton.elim j 0]
  cases c with
  | q => simp [drivenValues, readyPulse_initial]
  | m q =>
    by_cases h : s.aux 0 q = .ready <;>
      simp [drivenValues, drivenSensor, h, auxPulse_initial]
  | z q => rfl
  | b => rfl
  | energy => simp [drivenValues, drivenEnergy, relax_initial, linearConvolution_initial]

/-- A live pulse seen from the start of the flow. -/
theorem driven_current {s : Snapshot 1} {q : Port} {t : ℝ}
    (live : ∀ o, s.raw 0 q = some o → o ≤ t ∧ t < o + 1) :
    current s 0 q t = rawScale s q * a * Real.exp (-a * (t - s.time)) := by
  rcases h : s.raw 0 q with _ | o
  · simp [current, rawScale, rawInputScale, h]
  · have inside := live o h
    simp only [current, h, pulse, inside.1, inside.2, and_self, ite_true, rawScale, rawInputScale]
    rw [mul_comm _ a, mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- Inside the support of the live pulses, the kernel field is the
explicit one. -/
theorem driven_field {θ : Fin 1 → Parameters} {s : Snapshot 1} (hs : Driven s) {t : ℝ}
    (live : ∀ q o, s.raw 0 q = some o → o ≤ t ∧ t < o + 1) (i : Fin 1) (c : Coord) :
    field θ s (drivenValues θ s t) t i c = drivenRhs θ s t c := by
  rw [Subsingleton.elim i 0]
  have cur (q : Port) := driven_current (live q)
  have noError (q : Port) : errorAct θ s (drivenValues θ s t) 0 q = 0 := by
    simp [errorAct, hs.no_error q]
  have noMark (q : Port) : markAct θ s (drivenValues θ s t) 0 q = 0 := by
    simp [markAct, hs.main]
  have driveEq : drive s (drivenValues θ s t) 0 t =
      drivenAmplitude s * a * Real.exp (-a * (t - s.time)) := by
    simp only [drive, cur, drivenValues, drivenAmplitude, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have drain (q : Port) :
      (if s.aux 0 q = .ready then (θ 0).inputGain q * current s 0 q t
        else auxDrain (θ 0) (s.aux 0 q) q (drivenValues θ s t 0 (.m q))) =
      if s.aux 0 q = .ready then
        (θ 0).inputGain q * (rawScale s q * a * Real.exp (-a * (t - s.time)))
      else sensorRate θ s q * drivenSensor θ s q t := by
    by_cases h : s.aux 0 q = .ready
    · simp [h, cur q]
    · simp only [h, ite_false]
      rcases hm : s.aux 0 q with _ | _ | _ | _
      · exact absurd hm h
      · simp [auxDrain, sensorRate, protectedReadyRate, hm, drivenValues]
      · simp [auxDrain, sensorRate, protectedReadyRate, hm, drivenValues]
      · exact absurd hm (hs.no_error q)
  cases c with
  | q => simp [field, hs.main, driveEq, drivenRhs, drivenValues]
  | m q =>
    by_cases h : s.aux 0 q = .ready
    · simp only [field, h, ite_true, cur q, drivenRhs, drivenValues]
      ring
    · have d := drain q
      simp only [h, ite_false] at d
      simp only [field, h, ite_false, drivenRhs, d]
      ring
  | z q => simp [field, noError, drivenRhs]
  | b => simp [field, noMark, drivenRhs]
  | energy =>
    have w : work θ s (drivenValues θ s t) 0 t = drivenWork θ s t := by
      simp only [work, hs.main, driveEq, drivenWork, noError, noMark, drain,
        Finset.sum_const_zero, add_zero]
    simp [field, w, drivenRhs, drivenValues]

/-- The explicit flow of the driven regime. No threshold is attached. -/
noncomputable def drivenDynamics {θ : Fin 1 → Parameters} (s : Snapshot 1) {T : ℝ}
    (ht : s.time < T) (hs : Driven s)
    (support : ∀ q o, s.raw 0 q = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) : FlowDynamics θ s (drivenAt θ s T) where
  positive := ht
  path := drivenValues θ s
  initial := drivenValues_initial θ s
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun i c => (continuous_iff_continuousAt.mpr fun t =>
    (drivenValues_derivative θ s t i c).continuousAt).continuousOn
  integrable := by
    intro i c
    apply ((drivenRhs_continuous θ s c).intervalIntegrable _ _).congr_uIoo
    intro t ht'
    rw [uIoo_of_lt (show s.time < (drivenAt θ s T).time from ht)] at ht'
    exact (driven_field hs (fun q o h =>
      ⟨(support q o h).1.trans ht'.1.le, ht'.2.trans_le (support q o h).2⟩) i c).symm
  mark_integrable := by
    intro i q
    rw [Subsingleton.elim i 0]
    simp [markAct, hs.main]
  integral_eq := by
    intro t ht' i c
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => drivenValues_derivative θ s v i c)
      ((drivenRhs_continuous θ s c).intervalIntegrable s.time t)
    rw [drivenValues_initial] at h
    have eq : (∫ v in s.time..t, field θ s (drivenValues θ s v) v i c) =
        ∫ v in s.time..t, drivenRhs θ s v c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht'.1
      intro v hv
      exact driven_field hs (fun q o h =>
        ⟨(support q o h).1.trans hv.1.le, (hv.2.trans_le ht'.2).trans_le (support q o h).2⟩) i c
    rw [eq, h]
    ring
  raw_support := by
    intro i q o h
    rw [Subsingleton.elim i 0] at h
    exact support q o h
  pending_urgent := hp

/-! ### Restarting the flow -/

theorem drivenSensor_ready {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q = .ready) (t : ℝ) : drivenSensor θ s q t =
      auxPulse (s.x 0 (.m q)) ((θ 0).inputGain q * rawScale s q) s.time t := by
  simp [drivenSensor, h]

theorem drivenSensor_mark {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q = .mark) (t : ℝ) : drivenSensor θ s q t =
      s.x 0 (.m q) * Real.exp (-(θ 0).lm q * (t - s.time)) := by
  simp [drivenSensor, sensorRate, protectedReadyRate, h]

theorem drivenSensor_silent {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port}
    (h : s.aux 0 q = .silent) (t : ℝ) : drivenSensor θ s q t =
      s.x 0 (.m q) * Real.exp (-(θ 0).ls q * (t - s.time)) := by
  simp [drivenSensor, sensorRate, protectedReadyRate, h]

theorem rawScale_at (θ : Fin 1 → Parameters) (s : Snapshot 1) (τ : ℝ) (q : Port) :
    rawScale (drivenAt θ s τ) q = rawScale s q * Real.exp (-a * (τ - s.time)) := by
  show rawInputScale (s.raw 0 q) τ = rawInputScale (s.raw 0 q) s.time * _
  rcases s.raw 0 q with _ | o
  · simp [rawInputScale]
  · simp only [rawInputScale]
    rw [← Real.exp_add]
    congr 1
    ring

theorem drivenAmplitude_at (θ : Fin 1 → Parameters) (s : Snapshot 1) (τ : ℝ) :
    drivenAmplitude (drivenAt θ s τ) = drivenAmplitude s * Real.exp (-a * (τ - s.time)) := by
  unfold drivenAmplitude
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [rawScale_at]
  show Real.exp (s.x 0 (.z q)) * _ = _
  ring

theorem drivenCharge_at (θ : Fin 1 → Parameters) (s : Snapshot 1) (τ t : ℝ) :
    readyPulse ((drivenAt θ s τ).x 0 .q) (drivenAmplitude (drivenAt θ s τ)) τ t =
      readyPulse (s.x 0 .q) (drivenAmplitude s) s.time t := by
  rw [drivenAmplitude_at]
  exact readyPulse_restart _ _ _ _ _

theorem drivenSensor_at (θ : Fin 1 → Parameters) (s : Snapshot 1) (τ : ℝ) (q : Port) (t : ℝ) :
    drivenSensor θ (drivenAt θ s τ) q t = drivenSensor θ s q t := by
  have value : (drivenAt θ s τ).x 0 (.m q) = drivenSensor θ s q τ := rfl
  have date : (drivenAt θ s τ).time = τ := rfl
  rcases hm : s.aux 0 q with _ | _ | _ | _
  · rw [drivenSensor_ready (s := drivenAt θ s τ) hm, drivenSensor_ready hm, value,
      drivenSensor_ready hm, rawScale_at, date, ← mul_assoc]
    exact auxPulse_restart _ _ _ _ _
  · rw [drivenSensor_mark (s := drivenAt θ s τ) hm, drivenSensor_mark hm, value,
      drivenSensor_mark hm, date, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · rw [drivenSensor_silent (s := drivenAt θ s τ) hm, drivenSensor_silent hm, value,
      drivenSensor_silent hm, date, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · have rate : sensorRate θ (drivenAt θ s τ) q = sensorRate θ s q := rfl
    have busy : s.aux 0 q ≠ .ready := by rw [hm]; decide
    have busy' : (drivenAt θ s τ).aux 0 q ≠ .ready := busy
    simp only [drivenSensor, busy, busy', ite_false, rate]
    rw [value]
    simp only [drivenSensor, busy, ite_false]
    rw [date, mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-! ### The sensor events before the FIRE -/

/-- A sensor that will be SILENT at the horizon. -/
def Busy (s : Snapshot 1) (q : Port) : Prop := s.aux 0 q ≠ .ready ∨ s.raw 0 q ≠ none

/-- The charge of a busy sensor at the horizon `H`, when it enters MARK
at the planned date `M q`. -/
noncomputable def silentEnd (θ : Fin 1 → Parameters) (s : Snapshot 1) (M : Port → ℝ) (q : Port)
    (H : ℝ) : ℝ :=
  match s.aux 0 q with
  | .ready => (4 / 5) * Real.exp (-(θ 0).ls q * (H - (M q + decayTime 1 (4 / 5) ((θ 0).lm q))))
  | .mark => (4 / 5) * Real.exp (-(θ 0).ls q *
      (H - (s.time + decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q))))
  | _ => s.x 0 (.m q) * Real.exp (-(θ 0).ls q * (H - s.time))

theorem silentEnd_ready {θ : Fin 1 → Parameters} {s : Snapshot 1} {M : Port → ℝ} {q : Port}
    (h : s.aux 0 q = .ready) (H : ℝ) : silentEnd θ s M q H =
      (4 / 5) * Real.exp (-(θ 0).ls q * (H - (M q + decayTime 1 (4 / 5) ((θ 0).lm q)))) := by
  simp [silentEnd, h]

theorem silentEnd_mark {θ : Fin 1 → Parameters} {s : Snapshot 1} {M : Port → ℝ} {q : Port}
    (h : s.aux 0 q = .mark) (H : ℝ) : silentEnd θ s M q H =
      (4 / 5) * Real.exp (-(θ 0).ls q *
        (H - (s.time + decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q)))) := by
  simp [silentEnd, h]

theorem silentEnd_silent {θ : Fin 1 → Parameters} {s : Snapshot 1} {M : Port → ℝ} {q : Port}
    (h : s.aux 0 q = .silent) (H : ℝ) : silentEnd θ s M q H =
      s.x 0 (.m q) * Real.exp (-(θ 0).ls q * (H - s.time)) := by
  simp [silentEnd, h]

/-- A driven state whose sensor contacts are planned. Up to the horizon
`H` the main charge stays below the FIRE level, the live pulses last and
no delivery is due. A busy sensor that is SILENT stays above its ERROR
entry threshold up to the later date `K`. -/
structure Plan (θ : Fin 1 → Parameters) (s : Snapshot 1) (M : Port → ℝ) (H K level : ℝ) :
    Prop where
  driven : Driven s
  time : s.time ≤ H
  horizon : H ≤ K
  fire : (θ 0).thresholds.fire = level
  mark : ∀ q, (θ 0).thresholds.mark q = 1
  silent : ∀ q, (θ 0).thresholds.silent q = 4 / 5
  charge : ∀ t ∈ Ico s.time H, readyPulse (s.x 0 .q) (drivenAmplitude s) s.time t < level
  raw : ∀ q o, s.raw 0 q = some o → o ≤ s.time ∧ H ≤ o + 1
  pending : ∀ d ∈ s.pending, H ≤ d.due
  quiet : ∀ q, s.aux 0 q = .ready → s.raw 0 q = none → s.x 0 (.m q) < 1
  ready : ∀ q, s.aux 0 q = .ready → s.raw 0 q ≠ none →
    s.time ≤ M q ∧ (∀ t ∈ Ico s.time (M q), drivenSensor θ s q t < 1) ∧
    drivenSensor θ s q (M q) = 1
  marked : ∀ q, s.aux 0 q = .mark → 4 / 5 ≤ s.x 0 (.m q)
  silenced : ∀ q, s.aux 0 q = .silent → 0 ≤ s.x 0 (.m q)
  above : ∀ q, Busy s q → (θ 0).thresholds.error q < silentEnd θ s M q K

/-- Every busy sensor is SILENT before the date `H`. -/
structure Complete (θ : Fin 1 → Parameters) (s : Snapshot 1) (M : Port → ℝ) (H : ℝ) : Prop where
  ready : ∀ q, s.aux 0 q = .ready → s.raw 0 q ≠ none →
    M q + decayTime 1 (4 / 5) ((θ 0).lm q) < H
  marked : ∀ q, s.aux 0 q = .mark →
    s.time + decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q) < H

/-- Two states on the same driven timeline. -/
structure DSame (θ : Fin 1 → Parameters) (s s' : Snapshot 1) (M : Port → ℝ) : Prop where
  charge : ∀ t, readyPulse (s'.x 0 .q) (drivenAmplitude s') s'.time t =
    readyPulse (s.x 0 .q) (drivenAmplitude s) s.time t
  raw : s'.raw = s.raw
  queue : s'.pending = s.pending
  gains : ∀ q, s'.x 0 (.z q) = s.x 0 (.z q)
  recovery : s'.x 0 .b = s.x 0 .b
  busy : ∀ q, Busy s' q ↔ Busy s q
  ends : ∀ q, Busy s q → ∀ T, silentEnd θ s' M q T = silentEnd θ s M q T
  idle : ∀ q, ¬ Busy s q → ∀ t, drivenSensor θ s' q t = drivenSensor θ s q t

theorem DSame.refl (θ : Fin 1 → Parameters) (s : Snapshot 1) (M : Port → ℝ) : DSame θ s s M :=
  ⟨fun _ => rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem DSame.trans {θ : Fin 1 → Parameters} {s s' s'' : Snapshot 1} {M : Port → ℝ}
    (h : DSame θ s s' M) (k : DSame θ s' s'' M) : DSame θ s s'' M :=
  ⟨fun t => (k.charge t).trans (h.charge t), k.raw.trans h.raw, k.queue.trans h.queue,
    fun q => (k.gains q).trans (h.gains q), k.recovery.trans h.recovery,
    fun q => (k.busy q).trans (h.busy q),
    fun q hq T => (k.ends q ((h.busy q).mpr hq) T).trans (h.ends q hq T),
    fun q hq t => (k.idle q (fun hb => hq ((h.busy q).mp hb)) t).trans (h.idle q hq t)⟩

/-- The state at the horizon, with every busy sensor SILENT. -/
structure DrivenEnd (θ : Fin 1 → Parameters) (s : Snapshot 1) (M : Port → ℝ) (H : ℝ)
    (u : Snapshot 1) : Prop where
  time : u.time = H
  main : u.main 0 = .ready
  charge : u.x 0 .q = readyPulse (s.x 0 .q) (drivenAmplitude s) s.time H
  raw : u.raw = s.raw
  queue : u.pending = s.pending
  gains : ∀ q, u.x 0 (.z q) = s.x 0 (.z q)
  recovery : u.x 0 .b = s.x 0 .b
  busy : ∀ q, Busy s q → u.aux 0 q = .silent ∧ u.x 0 (.m q) = silentEnd θ s M q H
  idle : ∀ q, ¬ Busy s q → u.aux 0 q = .ready ∧ u.x 0 (.m q) = drivenSensor θ s q H

theorem DrivenEnd.of_same {θ : Fin 1 → Parameters} {s s' u : Snapshot 1} {M : Port → ℝ} {H : ℝ}
    (h : DSame θ s s' M) (e : DrivenEnd θ s' M H u) : DrivenEnd θ s M H u :=
  ⟨e.time, e.main, e.charge.trans (h.charge H), e.raw.trans h.raw, e.queue.trans h.queue,
    fun q => (e.gains q).trans (h.gains q), e.recovery.trans h.recovery,
    fun q hq => by
      obtain ⟨mode, value⟩ := e.busy q ((h.busy q).mpr hq)
      exact ⟨mode, value.trans (h.ends q hq H)⟩,
    fun q hq => by
      obtain ⟨mode, value⟩ := e.idle q (fun hb => hq ((h.busy q).mp hb))
      exact ⟨mode, value.trans (h.idle q hq H)⟩⟩

theorem drivenSensor_congr {θ : Fin 1 → Parameters} {s s' : Snapshot 1} {q : Port}
    (hx : s'.x = s.x) (ht : s'.time = s.time) (hr : s'.raw 0 q = s.raw 0 q)
    (ha : s'.aux 0 q = s.aux 0 q) : drivenSensor θ s' q = drivenSensor θ s q := by
  funext t
  unfold drivenSensor sensorRate rawScale
  rw [hx, ht, hr, ha]

theorem silentEnd_congr {θ : Fin 1 → Parameters} {s s' : Snapshot 1} {M : Port → ℝ} {q : Port}
    (hx : s'.x = s.x) (ht : s'.time = s.time) (ha : s'.aux 0 q = s.aux 0 q) (H : ℝ) :
    silentEnd θ s' M q H = silentEnd θ s M q H := by
  unfold silentEnd
  rw [hx, ht, ha]

theorem rawScale_none {s : Snapshot 1} {q : Port} (h : s.raw 0 q = none) : rawScale s q = 0 := by
  simp [rawScale, h, rawInputScale]

/-- The cell flows up to any date that precedes its pending contacts. -/
theorem plan_advance {θ ε} {s : Snapshot 1} {M : Port → ℝ} {H K level τ : ℝ}
    (box : @PhysicalBox 1 θ ε) (plan : Plan θ s M H K level) (lt : s.time < τ) (le : τ ≤ H)
    (ready : ∀ q, s.aux 0 q = .ready → s.raw 0 q ≠ none → τ ≤ M q)
    (marked : ∀ q, s.aux 0 q = .mark →
      τ ≤ s.time + decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q)) :
    Nonempty (ParameterFlow θ s (drivenAt θ s τ)) ∧ Plan θ (drivenAt θ s τ) M H K level ∧
      DSame θ s (drivenAt θ s τ) M ∧
      ∀ H', Complete θ s M H' → Complete θ (drivenAt θ s τ) M H' := by
  have date : (drivenAt θ s τ).time = τ := rfl
  have value (q : Port) : (drivenAt θ s τ).x 0 (.m q) = drivenSensor θ s q τ := rfl
  have endEq (q : Port) (T : ℝ) :
      silentEnd θ (drivenAt θ s τ) M q T = silentEnd θ s M q T := by
    have rates := box.rates_positive 0 q
    rcases hm : s.aux 0 q with _ | _ | _ | _
    · rw [silentEnd_ready (s := drivenAt θ s τ) hm, silentEnd_ready hm]
    · rw [silentEnd_mark (s := drivenAt θ s τ) hm, silentEnd_mark hm, value, drivenSensor_mark hm,
        decayTime_shift (lt_of_lt_of_le (by norm_num) (plan.marked q hm)) (by norm_num) rates.1,
        date]
      congr 2
      ring
    · rw [silentEnd_silent (s := drivenAt θ s τ) hm, silentEnd_silent hm, value,
        drivenSensor_silent hm, date, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · exact absurd hm (plan.driven.no_error q)
  have flow : ParameterFlow θ s (drivenAt θ s τ) := {
    toFlowDynamics := drivenDynamics s lt plan.driven
      (fun q o h => ⟨(plan.raw q o h).1, le.trans (plan.raw q o h).2⟩)
      (fun d hd => le.trans (plan.pending d hd))
    guards := by
      intro t ht
      have ht₁ : s.time ≤ t := ht.1
      have ht₂ : t < τ := ht.2
      constructor
      · intro i
        rw [Subsingleton.elim i 0]
        rcases hmain : s.main 0 with _ | _ | _
        · show readyPulse (s.x 0 .q) (drivenAmplitude s) s.time t < (θ 0).thresholds.fire
          rw [plan.fire]
          exact plan.charge t ⟨ht₁, ht₂.trans_le le⟩
        · rw [plan.driven.main] at hmain; cases hmain
        · rw [plan.driven.main] at hmain; cases hmain
      · intro i q
        rw [Subsingleton.elim i 0]
        have rates := box.rates_positive 0 q
        rcases hm : s.aux 0 q with _ | _ | _ | _
        · show drivenSensor θ s q t < (θ 0).thresholds.mark q
          rw [plan.mark]
          rcases hr : s.raw 0 q with _ | o
          · rw [drivenSensor_ready hm, rawScale_none hr, mul_zero, auxPulse_zero_eq_relax]
            exact relax_lt_one ht₁ (plan.quiet q hm hr)
          · have live : s.raw 0 q ≠ none := by rw [hr]; simp
            exact (plan.ready q hm live).2.1 t ⟨ht₁, ht₂.trans_le (ready q hm live)⟩
        · show (θ 0).thresholds.silent q < drivenSensor θ s q t
          rw [plan.silent, drivenSensor_mark hm]
          exact decay_above (lt_of_lt_of_le (by norm_num) (plan.marked q hm)) (by norm_num)
            rates.1 (by linarith [marked q hm])
        · show (θ 0).thresholds.error q < drivenSensor θ s q t
          have ab := plan.above q (Or.inl (by rw [hm]; decide))
          rw [silentEnd_silent hm] at ab
          rw [drivenSensor_silent hm]
          refine lt_of_lt_of_le ab (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
            (plan.silenced q hm))
          nlinarith [mul_nonneg rates.2.1.le
            (sub_nonneg.mpr ((ht₂.le.trans le).trans plan.horizon))]
        · exact absurd hm (plan.driven.no_error q) }
  refine ⟨⟨flow⟩, ?_, ⟨fun t => drivenCharge_at θ s τ t, rfl, rfl, fun _ => rfl, rfl,
    fun _ => Iff.rfl, fun q _ T => endEq q T, fun q _ t => drivenSensor_at θ s τ q t⟩, ?_⟩
  · exact {
      driven := ⟨plan.driven.main, plan.driven.no_error⟩
      time := le
      horizon := plan.horizon
      fire := plan.fire
      mark := plan.mark
      silent := plan.silent
      charge := fun t ht => by
        show readyPulse ((drivenAt θ s τ).x 0 .q) (drivenAmplitude (drivenAt θ s τ)) τ t < level
        rw [drivenCharge_at]
        exact plan.charge t ⟨lt.le.trans ht.1, ht.2⟩
      raw := fun q o h => ⟨(plan.raw q o h).1.trans lt.le, (plan.raw q o h).2⟩
      pending := plan.pending
      quiet := fun q hm hr => by
        rw [value, drivenSensor_ready (s := s) hm, rawScale_none (s := s) hr, mul_zero,
          auxPulse_zero_eq_relax]
        exact relax_lt_one lt.le (plan.quiet q hm hr)
      ready := fun q hm hr => by
        obtain ⟨_, below, contact⟩ := plan.ready q hm hr
        refine ⟨ready q hm hr, fun t ht => ?_, ?_⟩
        · rw [drivenSensor_at]
          exact below t ⟨lt.le.trans ht.1, ht.2⟩
        · rw [drivenSensor_at]
          exact contact
      marked := fun q hm => by
        have rates := box.rates_positive 0 q
        have pos : 0 < s.x 0 (.m q) := lt_of_lt_of_le (by norm_num) (plan.marked q hm)
        rw [value, drivenSensor_mark (s := s) hm]
        exact decay_ge pos (by norm_num) rates.1 (by linarith [marked q hm])
      silenced := fun q hm => by
        rw [value, drivenSensor_silent (s := s) hm]
        exact mul_nonneg (plan.silenced q hm) (Real.exp_pos _).le
      above := fun q hb => by
        rw [endEq]
        exact plan.above q hb }
  · intro H' complete
    refine ⟨complete.ready, fun q hm => ?_⟩
    have rates := box.rates_positive 0 q
    have pos : 0 < s.x 0 (.m q) := lt_of_lt_of_le (by norm_num) (plan.marked q hm)
    rw [value, drivenSensor_mark (s := s) hm, decayTime_shift pos (by norm_num) rates.1]
    show τ + _ < H'
    linarith [complete.marked q hm]

/-- A sensor contact changes the mode of one busy sensor only. -/
theorem plan_step {θ : Fin 1 → Parameters} {s : Snapshot 1} {M : Port → ℝ} {H K level : ℝ}
    {q : Port} {mode : AuxMode} (plan : Plan θ s M H K level) (busy : Busy s q)
    (new : mode = .mark ∨ mode = .silent)
    (marked : mode = .mark → 4 / 5 ≤ s.x 0 (.m q))
    (silenced : mode = .silent → 0 ≤ s.x 0 (.m q))
    (endQ : ∀ T, silentEnd θ (setAux s 0 q mode) M q T = silentEnd θ s M q T) :
    Plan θ (setAux s 0 q mode) M H K level ∧ DSame θ s (setAux s 0 q mode) M := by
  have hs' := setAux_same s q mode
  have other (q' : Port) (h : q' ≠ q) := setAux_other s mode h
  have notReady : mode ≠ .ready := by rcases new with rfl | rfl <;> decide
  have sensorOther (q' : Port) (h : q' ≠ q) :
      drivenSensor θ (setAux s 0 q mode) q' = drivenSensor θ s q' :=
    drivenSensor_congr rfl rfl rfl (other q' h)
  have busyIff (q' : Port) : Busy (setAux s 0 q mode) q' ↔ Busy s q' := by
    by_cases h : q' = q
    · subst q'
      exact ⟨fun _ => busy, fun _ => Or.inl (by rw [hs']; exact notReady)⟩
    · unfold Busy
      rw [other q' h]
      exact Iff.rfl
  constructor
  · exact {
      driven := ⟨plan.driven.main, fun q' => by
        by_cases h : q' = q
        · subst q'; rw [hs']; rcases new with rfl | rfl <;> decide
        · rw [other q' h]; exact plan.driven.no_error q'⟩
      time := plan.time
      horizon := plan.horizon
      fire := plan.fire
      mark := plan.mark
      silent := plan.silent
      charge := plan.charge
      raw := plan.raw
      pending := plan.pending
      quiet := fun q' hm hr => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at hm; exact absurd hm notReady
        · rw [other q' h] at hm; exact plan.quiet q' hm hr
      ready := fun q' hm hr => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at hm; exact absurd hm notReady
        · rw [other q' h] at hm
          rw [sensorOther q' h]
          exact plan.ready q' hm hr
      marked := fun q' hm => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at hm; exact marked hm
        · rw [other q' h] at hm; exact plan.marked q' hm
      silenced := fun q' hm => by
        by_cases h : q' = q
        · subst q'; rw [hs'] at hm; exact silenced hm
        · rw [other q' h] at hm; exact plan.silenced q' hm
      above := fun q' hb => by
        by_cases h : q' = q
        · subst q'; rw [endQ]; exact plan.above q busy
        · rw [silentEnd_congr (s := s) (s' := setAux s 0 q mode) rfl rfl (other q' h)]
          exact plan.above q' ((busyIff q').mp hb) }
  · exact ⟨fun _ => rfl, rfl, rfl, fun _ => rfl, rfl, busyIff,
      fun q' _ T => by
        by_cases h : q' = q
        · subst q'; exact endQ T
        · exact silentEnd_congr (s := s) (s' := setAux s 0 q mode) rfl rfl (other q' h) T,
      fun q' hb t => by
        by_cases h : q' = q
        · subst q'; exact absurd busy hb
        · rw [sensorOther q' h]⟩

theorem complete_step {θ : Fin 1 → Parameters} {s : Snapshot 1} {M : Port → ℝ} {H : ℝ}
    {q : Port} {mode : AuxMode} (complete : Complete θ s M H)
    (new : mode = .mark ∨ mode = .silent)
    (marked : mode = .mark →
      s.time + decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q) < H) :
    Complete θ (setAux s 0 q mode) M H := by
  have hs' := setAux_same s q mode
  have other (q' : Port) (h : q' ≠ q) := setAux_other s mode h
  have notReady : mode ≠ .ready := by rcases new with rfl | rfl <;> decide
  refine ⟨fun q' hm hr => ?_, fun q' hm => ?_⟩
  · by_cases h : q' = q
    · subst q'; rw [hs'] at hm; exact absurd hm notReady
    · rw [other q' h] at hm; exact complete.ready q' hm hr
  · by_cases h : q' = q
    · subst q'; rw [hs'] at hm; exact marked hm
    · rw [other q' h] at hm; exact complete.marked q' hm

/-- The sensor contacts still ahead: two for a READY sensor under a live
pulse, one for a sensor in MARK. -/
def planWeight (s : Snapshot 1) (q : Port) : ℕ :=
  match s.aux 0 q with
  | .ready => 2 * rawCount (s.raw 0 q)
  | .mark => 1
  | _ => 0

def planCount (s : Snapshot 1) : ℕ := ∑ q : Port, planWeight s q

theorem planCount_setAux_lt {s : Snapshot 1} {q : Port} {mode : AuxMode}
    (h : planWeight (setAux s 0 q mode) q < planWeight s q) :
    planCount (setAux s 0 q mode) < planCount s := by
  apply Finset.sum_lt_sum
  · intro q' _
    by_cases e : q' = q
    · subst q'; exact h.le
    · unfold planWeight
      rw [setAux_other s mode e]
      exact le_rfl
  · exact ⟨q, Finset.mem_univ q, h⟩

theorem plan_mark {θ : Fin 1 → Parameters} {s : Snapshot 1} {M : Port → ℝ} {H K level : ℝ}
    {q : Port} (plan : Plan θ s M H K level) (hm : s.aux 0 q = .ready) (hr : s.raw 0 q ≠ none)
    (due : M q = s.time) :
    Runs θ s (setAux s 0 q .mark) 0 ∧ Plan θ (setAux s 0 q .mark) M H K level ∧
      DSame θ s (setAux s 0 q .mark) M ∧ planCount (setAux s 0 q .mark) < planCount s ∧
      ∀ H', Complete θ s M H' → Complete θ (setAux s 0 q .mark) M H' := by
  obtain ⟨_, _, contact⟩ := plan.ready q hm hr
  rw [due, drivenSensor_ready hm, auxPulse_initial] at contact
  have hs' := setAux_same s q .mark
  have endQ (T : ℝ) : silentEnd θ (setAux s 0 q .mark) M q T = silentEnd θ s M q T := by
    rw [silentEnd_mark hs', silentEnd_ready hm]
    show (4 / 5 : ℝ) * Real.exp (-(θ 0).ls q *
      (T - (s.time + decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q)))) = _
    rw [contact, due]
  obtain ⟨plan', same⟩ := plan_step (mode := .mark) plan (Or.inr hr) (Or.inl rfl)
    (fun _ => by rw [contact]; norm_num) (fun h => by cases h) endQ
  refine ⟨Runs.jump (.mark s 0 q hm (by rw [plan.mark]; exact contact)) rfl, plan', same, ?_, ?_⟩
  · apply planCount_setAux_lt
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hr
    simp [planWeight, hs', hm, ho, rawCount]
  · intro H' complete
    exact complete_step complete (Or.inl rfl)
      (fun _ => by rw [contact, ← due]; exact complete.ready q hm hr)

theorem plan_silent {θ ε} {s : Snapshot 1} {M : Port → ℝ} {H K level : ℝ} {q : Port}
    (box : @PhysicalBox 1 θ ε) (plan : Plan θ s M H K level) (hm : s.aux 0 q = .mark)
    (due : decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q) = 0) :
    Runs θ s (setAux s 0 q .silent) 0 ∧ Plan θ (setAux s 0 q .silent) M H K level ∧
      DSame θ s (setAux s 0 q .silent) M ∧ planCount (setAux s 0 q .silent) < planCount s ∧
      ∀ H', Complete θ s M H' → Complete θ (setAux s 0 q .silent) M H' := by
  have pos : 0 < s.x 0 (.m q) := lt_of_lt_of_le (by norm_num) (plan.marked q hm)
  have contact : s.x 0 (.m q) = 4 / 5 :=
    decayTime_zero pos (by norm_num) (box.rates_positive 0 q).1 due
  have hs' := setAux_same s q .silent
  have endQ (T : ℝ) : silentEnd θ (setAux s 0 q .silent) M q T = silentEnd θ s M q T := by
    rw [silentEnd_silent hs', silentEnd_mark hm, due, add_zero]
    show s.x 0 (.m q) * _ = _
    rw [contact]
    rfl
  obtain ⟨plan', same⟩ := plan_step (mode := .silent) plan (Or.inl (by rw [hm]; decide))
    (Or.inr rfl) (fun h => by cases h) (fun _ => pos.le) endQ
  refine ⟨Runs.jump (.silent s 0 q hm (by rw [plan.silent]; exact contact)) rfl, plan', same,
    ?_, ?_⟩
  · apply planCount_setAux_lt
    simp [planWeight, hs', hm]
  · intro H' complete
    exact complete_step complete (Or.inr rfl) (fun h => by cases h)

theorem drivenSensor_initial (θ : Fin 1 → Parameters) (s : Snapshot 1) (q : Port) :
    drivenSensor θ s q s.time = s.x 0 (.m q) :=
  congrFun (congrFun (drivenValues_initial θ s) 0) (.m q)

/-- A sensor with a contact ahead. -/
def HasEvent (s : Snapshot 1) (q : Port) : Prop :=
  (s.aux 0 q = .ready ∧ s.raw 0 q ≠ none) ∨ s.aux 0 q = .mark

/-- The date of its next contact. -/
noncomputable def eventDate (θ : Fin 1 → Parameters) (s : Snapshot 1) (M : Port → ℝ)
    (q : Port) : ℝ :=
  if s.aux 0 q = .ready then M q
  else s.time + decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q)

theorem event_min (θ : Fin 1 → Parameters) (s : Snapshot 1) (M : Port → ℝ)
    (some : ∃ q, HasEvent s q) :
    ∃ q, HasEvent s q ∧ ∀ q', HasEvent s q' → eventDate θ s M q ≤ eventDate θ s M q' := by
  classical
  let events : Finset Port := Finset.univ.filter (fun q => HasEvent s q)
  obtain ⟨q₀, h₀⟩ := some
  obtain ⟨q, hq, least⟩ := Finset.exists_min_image events (eventDate θ s M)
    ⟨q₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₀⟩⟩
  exact ⟨q, (Finset.mem_filter.mp hq).2,
    fun q' h' => least q' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)⟩

/-- The earliest pending contact, taken as one move. -/
theorem plan_event {θ ε} {s : Snapshot 1} {M : Port → ℝ} {H K level : ℝ} {q : Port}
    (box : @PhysicalBox 1 θ ε) (plan : Plan θ s M H K level) (hq : HasEvent s q)
    (least : ∀ q', HasEvent s q' → eventDate θ s M q ≤ eventDate θ s M q')
    (before : eventDate θ s M q < H) :
    ∃ s₂, Runs θ s s₂ 0 ∧ Plan θ s₂ M H K level ∧ DSame θ s s₂ M ∧
      planCount s₂ < planCount s ∧ ∀ H', Complete θ s M H' → Complete θ s₂ M H' := by
  have rates := box.rates_positive 0 q
  have readyLe (q' : Port) (hm : s.aux 0 q' = .ready) (hr : s.raw 0 q' ≠ none) :
      eventDate θ s M q ≤ M q' := by
    have h := least q' (Or.inl ⟨hm, hr⟩)
    simpa [eventDate, hm] using h
  have markLe (q' : Port) (hm : s.aux 0 q' = .mark) :
      eventDate θ s M q ≤ s.time + decayTime (s.x 0 (.m q')) (4 / 5) ((θ 0).lm q') := by
    have h := least q' (Or.inr hm)
    simpa [eventDate, hm] using h
  have dateReady (hm : s.aux 0 q = .ready) : eventDate θ s M q = M q := by simp [eventDate, hm]
  have dateMark (hm : s.aux 0 q = .mark) : eventDate θ s M q =
      s.time + decayTime (s.x 0 (.m q)) (4 / 5) ((θ 0).lm q) := by simp [eventDate, hm]
  have startLe : s.time ≤ eventDate θ s M q := by
    rcases hq with ⟨hm, hr⟩ | hm
    · rw [dateReady hm]
      exact (plan.ready q hm hr).1
    · rw [dateMark hm]
      linarith [decayTime_nonneg (by norm_num) rates.1 (plan.marked q hm)]
  obtain ⟨s₁, pre, plan₁, same₁, count₁, keep₁, due⟩ :
      ∃ s₁, Runs θ s s₁ 0 ∧ Plan θ s₁ M H K level ∧ DSame θ s s₁ M ∧
        planCount s₁ = planCount s ∧ (∀ H', Complete θ s M H' → Complete θ s₁ M H') ∧
        ((s₁.aux 0 q = .ready ∧ s₁.raw 0 q ≠ none ∧ M q = s₁.time) ∨
          (s₁.aux 0 q = .mark ∧
            decayTime (s₁.x 0 (.m q)) (4 / 5) ((θ 0).lm q) = 0)) := by
    rcases startLe.eq_or_lt with now | later
    · refine ⟨s, Runs.nil s, plan, DSame.refl θ s M, rfl, fun _ c => c, ?_⟩
      rcases hq with ⟨hm, hr⟩ | hm
      · exact Or.inl ⟨hm, hr, by rw [← dateReady hm]; exact now.symm⟩
      · refine Or.inr ⟨hm, ?_⟩
        rw [dateMark hm] at now
        linarith
    · obtain ⟨⟨flow⟩, plan₁, same, keep⟩ := plan_advance box plan later before.le readyLe markLe
      refine ⟨drivenAt θ s (eventDate θ s M q), Runs.flow flow, plan₁, same, rfl, keep, ?_⟩
      rcases hq with ⟨hm, hr⟩ | hm
      · exact Or.inl ⟨hm, hr, (dateReady hm).symm⟩
      · refine Or.inr ⟨hm, ?_⟩
        show decayTime (drivenSensor θ s q (eventDate θ s M q)) (4 / 5) ((θ 0).lm q) = 0
        rw [drivenSensor_mark hm, decayTime_shift
          (lt_of_lt_of_le (by norm_num) (plan.marked q hm)) (by norm_num) rates.1, dateMark hm]
        ring
  rcases due with ⟨hm, hr, d⟩ | ⟨hm, d⟩
  · obtain ⟨jump, plan₂, same₂, less, keep₂⟩ := plan_mark plan₁ hm hr d
    exact ⟨_, pre.append jump, plan₂, same₁.trans same₂, by omega,
      fun H' c => keep₂ H' (keep₁ H' c)⟩
  · obtain ⟨jump, plan₂, same₂, less, keep₂⟩ := plan_silent box plan₁ hm d
    exact ⟨_, pre.append jump, plan₂, same₁.trans same₂, by omega,
      fun H' c => keep₂ H' (keep₁ H' c)⟩

/-- Without pending contact the cell flows to the horizon. -/
theorem plan_finish {θ ε} {s : Snapshot 1} {M : Port → ℝ} {H K level : ℝ}
    (box : @PhysicalBox 1 θ ε) (plan : Plan θ s M H K level) (none : ¬ ∃ q, HasEvent s q) :
    ∃ u, Runs θ s u 0 ∧ DrivenEnd θ s M H u := by
  have noReady (q : Port) (hm : s.aux 0 q = .ready) : s.raw 0 q = Option.none := by
    by_contra hr
    exact none ⟨q, Or.inl ⟨hm, hr⟩⟩
  have noMark (q : Port) : s.aux 0 q ≠ .mark := fun hm => none ⟨q, Or.inr hm⟩
  have modeOf (q : Port) (hb : Busy s q) : s.aux 0 q = .silent := by
    rcases hm : s.aux 0 q with _ | _ | _ | _
    · rcases hb with h | h
      · exact absurd hm h
      · exact absurd (noReady q hm) h
    · exact absurd hm (noMark q)
    · rfl
    · exact absurd hm (plan.driven.no_error q)
  have idleOf (q : Port) (hb : ¬ Busy s q) : s.aux 0 q = .ready := by
    by_contra h
    exact hb (Or.inl h)
  rcases plan.time.eq_or_lt with now | later
  · refine ⟨s, Runs.nil s, ⟨now, plan.driven.main, ?_, rfl, rfl, fun _ => rfl, rfl, ?_, ?_⟩⟩
    · rw [← now, readyPulse_initial]
    · intro q hb
      refine ⟨modeOf q hb, ?_⟩
      rw [silentEnd_silent (modeOf q hb), ← now]
      simp
    · intro q hb
      exact ⟨idleOf q hb, by rw [← now, drivenSensor_initial]⟩
  · obtain ⟨⟨flow⟩, _, _, _⟩ := plan_advance box plan later le_rfl
      (fun q hm hr => absurd (noReady q hm) hr) (fun q hm => absurd hm (noMark q))
    refine ⟨drivenAt θ s H, Runs.flow flow, ⟨rfl, plan.driven.main, rfl, rfl, rfl, fun _ => rfl,
      rfl, ?_, ?_⟩⟩
    · intro q hb
      refine ⟨modeOf q hb, ?_⟩
      rw [silentEnd_silent (modeOf q hb)]
      exact drivenSensor_silent (modeOf q hb) H
    · intro q hb
      exact ⟨idleOf q hb, rfl⟩

/-- The driven period as an execution. From a READY cell under any
number of live pulses, the cell runs to the horizon. The MARK and SILENT
entries of the sensors are taken in their time order, whatever it is. No
gain and no recovery rate changes, and the main charge sums the pulses. -/
theorem driven_run_exists {θ ε} (box : @PhysicalBox 1 θ ε) (M : Port → ℝ) (H K level : ℝ)
    (s : Snapshot 1) (plan : Plan θ s M H K level) (complete : Complete θ s M H) :
    ∃ u, Runs θ s u 0 ∧ DrivenEnd θ s M H u := by
  generalize hn : planCount s = n
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases some : ∃ q, HasEvent s q
    · obtain ⟨q, hq, least⟩ := event_min θ s M some
      have rates := box.rates_positive 0 q
      have before : eventDate θ s M q < H := by
        rcases hq with ⟨hm, hr⟩ | hm
        · have span := decayTime_nonneg (x := 1) (thr := 4 / 5) (by norm_num) rates.1 (by norm_num)
          simp only [eventDate, hm, ite_true]
          linarith [complete.ready q hm hr]
        · have ne : s.aux 0 q ≠ .ready := by rw [hm]; decide
          simp only [eventDate, ne, ite_false]
          exact complete.marked q hm
      obtain ⟨s₂, pre, plan₂, same, less, keep⟩ := plan_event box plan hq least before
      obtain ⟨u, run, done⟩ := ih _ (by omega) _ plan₂ (keep H complete) rfl
      exact ⟨u, pre.append run, done.of_same same⟩
    · exact plan_finish box plan some

/-- The driven period up to a date at which sensors may still be on
their way. The contacts due before `H` are taken in their time order. The
plan holds again at `H`, for any later horizon. -/
theorem driven_until_exists {θ ε} (box : @PhysicalBox 1 θ ε) (M : Port → ℝ) (H K level : ℝ)
    (s : Snapshot 1) (plan : Plan θ s M H K level) :
    ∃ u, Runs θ s u 0 ∧ u.time = H ∧ Plan θ u M H K level ∧ DSame θ s u M ∧
      ∀ H', Complete θ s M H' → Complete θ u M H' := by
  generalize hn : planCount s = n
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases due : ∃ q, HasEvent s q ∧ eventDate θ s M q < H
    · obtain ⟨q₀, h₀, before₀⟩ := due
      obtain ⟨q, hq, least⟩ := event_min θ s M ⟨q₀, h₀⟩
      obtain ⟨s₂, pre, plan₂, same, less, keep⟩ :=
        plan_event box plan hq least ((least q₀ h₀).trans_lt before₀)
      obtain ⟨u, run, date, planEnd, sameEnd, keepEnd⟩ := ih _ (by omega) _ plan₂ rfl
      exact ⟨u, pre.append run, date, planEnd, same.trans sameEnd,
        fun H' c => keepEnd H' (keep H' c)⟩
    · have late (q : Port) (hq : HasEvent s q) : H ≤ eventDate θ s M q := by
        by_contra h
        exact due ⟨q, hq, not_le.mp h⟩
      rcases plan.time.eq_or_lt with now | later
      · exact ⟨s, Runs.nil s, now, plan, DSame.refl θ s M, fun _ c => c⟩
      · obtain ⟨⟨flow⟩, planEnd, same, keep⟩ := plan_advance box plan later le_rfl
          (fun q hm hr => by
            have h := late q (Or.inl ⟨hm, hr⟩)
            simpa [eventDate, hm] using h)
          (fun q hm => by
            have h := late q (Or.inr hm)
            simpa [eventDate, hm] using h)
        exact ⟨drivenAt θ s H, Runs.flow flow, rfl, planEnd, same, keep⟩

end RecursiveLearning.Native
