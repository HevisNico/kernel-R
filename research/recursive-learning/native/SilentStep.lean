import ParameterTraining
import StopLearningLatency

/-! A training pulse that leaves the cell silent, in the regime where the
ERROR entry threshold is low enough for the write to start after the pulse
has ended. The construction starts from any rested state and uses the
realized thresholds of the cell. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- A READY sensor without input relaxes toward its rest charge and stays
below the MARK threshold. -/
theorem relax_lt_one {initial start t : ℝ} (ht : start ≤ t) (below : initial < 1) :
    relax (1 / 2) (1 / 40) initial start t < 1 := by
  have pos := Real.exp_pos (-(1 / 2) * (t - start))
  have unit : Real.exp (-(1 / 2) * (t - start)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  dsimp [relax]
  rcases le_total initial (1 / 40) with h | h
  · have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) pos.le
    linarith
  · have := mul_le_mul_of_nonneg_left unit (sub_nonneg.mpr h)
    linarith

/-- A SILENT leg under a main-charge margin. The gain of the pulsed port is
bounded by the gain cap only. -/
theorem silent_leg_of_margin {θ ε s p origin upper level stop}
    (box : @PhysicalBox 1 θ ε)
    (positive : s.time < stop)
    (main : ∀ i, s.main i = .ready) (mode : s.aux 0 p = .silent)
    (other : ∀ i q, i ≠ 0 ∨ q ≠ p → s.aux i q = .ready)
    (rest : ∀ q ≠ p, s.x 0 (.m q) < 1)
    (raw : s.raw 0 p = origin) (otherRaw : ∀ i q, i ≠ 0 ∨ q ≠ p → s.raw i q = none)
    (support : ∀ o, origin = some o → o ≤ s.time ∧ stop ≤ o + 1)
    (pending : ∀ d ∈ s.pending, stop ≤ d.due)
    (charge : ∀ t ∈ Icc s.time stop,
      readyProtectedValues θ s 0 p .silent origin t 0 .q < level)
    (sensor : ∀ t ∈ Ico s.time stop,
      upper < readyProtectedValues θ s 0 p .silent origin t 0 (.m p))
    (sensorIn : s.x 0 (.m p) ∈ Icc 0 (4 / 5))
    (gain : Real.exp (s.x 0 (.z p)) ≤ 22 / 5)
    (energy : 50 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100) :
    Nonempty (TrainingSilentLeg θ s p origin upper level stop) := by
  let path := readyProtectedValues θ s 0 p .silent origin
  have fieldEq (t : ℝ) (ht : t ∈ Ico s.time stop) (i : Fin 1) (c : Coord) :
      field θ s (path t) t i c = readyProtectedRhs θ s 0 p .silent origin t i c :=
    readyProtected_field s 0 p .silent origin (Or.inr rfl) main mode other raw otherRaw t ht.1
      (fun o h => ⟨(support o h).1, ht.2.trans_le (support o h).2⟩) i c
  have qbound (t : ℝ) (ht : t ∈ Ico s.time stop) : path t 0 .q < level :=
    charge t ⟨ht.1, ht.2.le⟩
  have mbound (t : ℝ) (ht : s.time ≤ t) (q : Port) (hq : q ≠ p) : path t 0 (.m q) < 1 := by
    have value : path t 0 (.m q) = relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t := by
      simp [path, readyProtectedValues, hq]
    rw [value]
    exact relax_lt_one ht (rest q hq)
  refine ⟨⟨positive, main, mode, fun q h => other 0 q (Or.inr h), raw, otherRaw,
    ?_, ?_, ?_, qbound, sensor, fun t ht => mbound t ht.1, support, pending, ?_, ?_⟩⟩
  · intro i c
    exact (continuous_iff_continuousAt.mpr fun t =>
      (readyProtectedValues_derivative (θ := θ) s 0 p .silent origin t i c).continuousAt).continuousOn
  · intro i c
    have hc := readyProtectedRhs_continuous (θ := θ) s 0 p .silent origin i c
    apply (hc.intervalIntegrable s.time stop).congr_uIoo
    intro t ht
    rw [uIoo_of_lt positive] at ht
    exact (fieldEq t ⟨ht.1.le, ht.2⟩ i c).symm
  · intro t ht i c
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => readyProtectedValues_derivative (θ := θ) s 0 p .silent origin v i c)
      ((readyProtectedRhs_continuous (θ := θ) s 0 p .silent origin i c).intervalIntegrable s.time t)
    rw [readyProtectedValues_initial] at h
    have eq : (∫ v in s.time..t, field θ s (path v) v i c) =
        ∫ v in s.time..t, readyProtectedRhs θ s 0 p .silent origin v i c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact fieldEq v ⟨hv.1.le, hv.2.trans_le ht.2⟩ i c
    rw [eq, h]
    change path t i c = _
    ring
  · intro hu hl
    have startCharge : s.x 0 .q < 1 := by
      have h := charge s.time ⟨le_rfl, positive.le⟩
      rw [show readyProtectedValues θ s 0 p .silent origin s.time 0 .q = s.x 0 .q from
        congrFun (congrFun (readyProtectedValues_initial (θ := θ) s 0 p .silent origin) 0) .q,
        hl] at h
      exact h
    exact readyProtectedFlow s 0 p .silent origin positive (Or.inr rfl) main mode other raw otherRaw support
      (fun i => by rw [Subsingleton.elim i 0]; exact startCharge)
      (fun i q h => by
        rw [Subsingleton.elim i 0]
        exact rest q (h.resolve_left (not_not_intro (Subsingleton.elim i 0))))
      (fun t ht => by
        simpa only [path, readyProtectedValues, protectedRawAmplitude, ite_true, hl] using qbound t ht)
      (fun t ht => by
        simpa only [readyProtectedValues, and_self, ite_true, protectedReadyRate, reduceCtorEq,
          ite_false, hu] using sensor t ht) pending
  · let A := protectedRawAmplitude s 0 p origin 0
    let r := (θ 0).ls p
    let W := fun t => A * a * Real.exp (-a * (t - s.time)) +
      r * s.x 0 (.m p) * Real.exp (-r * (t - s.time))
    apply reserve_of_derivative positive.le (show Continuous W by dsimp [W]; fun_prop)
      (energy := fun t => path t 0 .energy)
    · intro t
      simpa [path, W, A, r, readyProtectedRhs, protectedAuxCoeff, protectedReadyRate, sub_sub] using
        readyProtectedValues_derivative (θ := θ) s 0 p .silent origin t 0 .energy
    · rw [show path s.time = s.x from readyProtectedValues_initial _ _ _ _ _]
      exact energy
    · intro t ht
      have aPos : 0 ≤ a := by linarith [a_coarse_bounds.1]
      have rp := (box.rates_positive 0 p).2.1
      have rawBound : rawInputScale origin s.time ≤ 1 := by
        cases origin with
        | none => norm_num [rawInputScale]
        | some o =>
          exact Real.exp_le_one_iff.mpr
            (by nlinarith [mul_nonneg aPos (sub_nonneg.mpr (support o rfl).1)])
      have ARange : 0 ≤ A ∧ A ≤ 22 / 5 := by
        change 0 ≤ (if (0 : Fin 1) = 0 then _ else _) ∧ (if (0 : Fin 1) = 0 then _ else _) ≤ _
        simp only [ite_true]
        exact ⟨mul_nonneg (Real.exp_pos _).le (rawInputScale_nonnegative _ _),
          by simpa using mul_le_mul gain rawBound (rawInputScale_nonnegative _ _) (by norm_num)⟩
      have h₁ := decay_upper (mul_le_mul ARange.2 a_coarse_bounds.2.le aPos
        (by norm_num : (0 : ℝ) ≤ 22 / 5)) (by norm_num) aPos (sub_nonneg.mpr ht.1)
      have h₂ := decay_upper (mul_le_mul (box.coarse_upper 0 p).2.2.1 sensorIn.2 sensorIn.1
        (by norm_num : (0 : ℝ) ≤ 3)) (by norm_num) rp.le (sub_nonneg.mpr ht.1)
      dsimp [W]
      constructor
      · exact add_nonneg (mul_nonneg (mul_nonneg ARange.1 aPos) (Real.exp_pos _).le)
          (mul_nonneg (mul_nonneg rp.le sensorIn.1) (Real.exp_pos _).le)
      · linarith

/-- A resting sensor stays in the rest band while it relaxes. -/
theorem relax_restBand {initial start t : ℝ} (ht : start ≤ t) (h : RestBand initial) :
    RestBand (relax (1 / 2) (1 / 40) initial start t) :=
  relax_mem_band (low := 1 / 40 - 1 / 100000) (high := 1 / 40 + 1 / 100000)
    (by norm_num) ht h ⟨by norm_num, by norm_num⟩

theorem readyProtectedValues_other {θ : Fin 1 → Parameters} {s : Snapshot 1} {p q : Port}
    {mode : AuxMode} {origin : Option ℝ} {t : ℝ} (hq : q ≠ p) :
    readyProtectedValues θ s 0 p mode origin t 0 (.m q) =
      relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t := by
  simp [readyProtectedValues, hq]

theorem readyInputValues_other {θ : Fin 1 → Parameters} {s : Snapshot 1} {p q : Port}
    {t : ℝ} (hq : q ≠ p) :
    readyInputValues θ s 0 p t 0 (.m q) = relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t := by
  simp [readyInputValues, readyInputAuxAmplitude, hq, auxPulse_zero_eq_relax]

/-- The SILENT rate of every cell in the fabrication box. -/
theorem silent_rate_bounds {θ ε} (box : @PhysicalBox 1 θ ε) (p : Port) :
    5 / 3 ≤ (θ 0).ls p ∧ (θ 0).ls p ≤ 109 / 50 := by
  have lower := (box.2 0 p).2.2.1.1
  have upper := (box.2 0 p).2.2.1.2
  change Real.log 8 / (53 / 50) * (1 - ε) ≤ (θ 0).ls p at lower
  change (θ 0).ls p ≤ Real.log 8 / (53 / 50) * (1 + ε) at upper
  have log8 : 2 ≤ Real.log 8 ∧ Real.log 8 ≤ 21 / 10 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  obtain ⟨e₀, e₁⟩ := box.epsilon_bounds
  constructor
  · have h := mul_le_mul (show (2 : ℝ) / (53 / 50) ≤ Real.log 8 / (53 / 50) by linarith [log8.1])
      (show (9 / 10 : ℝ) ≤ 1 - ε by linarith) (by norm_num) (by linarith [log8.1])
    linarith
  · have h := mul_le_mul (show Real.log 8 / (53 / 50) ≤ (21 / 10 : ℝ) / (53 / 50) by linarith [log8.2])
      (show 1 + ε ≤ (11 / 10 : ℝ) by linarith) (by linarith) (by norm_num)
    linarith

/-- With an ERROR entry threshold of at most 2/25, SILENT lasts longer than
the pulse. The write therefore starts after the pulse has ended. -/
theorem low_entry_silent_duration {θ ε upper} (box : @PhysicalBox 1 θ ε) (p : Port)
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25) :
    1 < Real.log ((4 / 5) / upper) / (θ 0).ls p ∧
      Real.log ((4 / 5) / upper) / (θ 0).ls p ≤ 31 / 20 := by
  obtain ⟨rl, ru⟩ := silent_rate_bounds box p
  have rp : 0 < (θ 0).ls p := by linarith
  have up : 0 < upper := by linarith [entry.1]
  have log8 : Real.log 8 ≤ 21 / 10 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have log2 : (2 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  constructor
  · apply (lt_div_iff₀ rp).2
    have ten : Real.log 10 ≤ Real.log ((4 / 5) / upper) :=
      Real.log_le_log (by norm_num) ((le_div_iff₀ up).2 (by linarith [entry.2]))
    have split : Real.log 10 = Real.log 8 + Real.log (5 / 4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have quarter := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    norm_num at quarter
    linarith
  · apply (div_le_iff₀ rp).2
    have wide : Real.log ((4 / 5) / upper) ≤ Real.log (80 / 7) :=
      Real.log_le_log (div_pos (by norm_num) up) ((div_le_iff₀ up).2 (by linarith [entry.1]))
    have split : Real.log (80 / 7) = Real.log 8 + Real.log (10 / 7) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have small := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 7 by norm_num)
    linarith

/-- The cell at ERROR entry after a training pulse that did not fire it.
`before` is the state at the contact with the entry threshold. -/
structure SilentEntry (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    (upper lower level : ℝ) where
  mark : FirstInputMark θ s 0 p
  silent : FirstInputSilent mark
  pre_mark : ∀ t ∈ Ico s.time (s.time + mark.latency), mark.flow.path t 0 .q < level
  pre_silent : ∀ t ∈ Ico mark.final.time silent.final.time, silent.flow.path t 0 .q < level
  before : Snapshot 1
  trace : TrainingTrace θ p upper lower level silent.final (setAux before 0 p .error)
  after_pulse : s.time + 1 < before.time
  deadline : before.time < s.time + 8 / 5
  main : before.main 0 = .ready
  mode : before.aux 0 p = .silent
  other_modes : ∀ q ≠ p, before.aux 0 q = .ready
  sensor : before.x 0 (.m p) = upper
  other_sensors : ∀ q ≠ p, RestBand (before.x 0 (.m q))
  charge : before.x 0 .q = relax (1 / 2) (1 / 10)
    (readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time (s.time + 1)) (s.time + 1) before.time
  gains : ∀ q, before.x 0 (.z q) = s.x 0 (.z q)
  recovery : before.x 0 .b = s.x 0 .b
  energy : 50 ≤ before.x 0 .energy ∧ before.x 0 .energy ≤ 100
  raw : ∀ q, before.raw 0 q = none
  queue : before.pending = s.pending

/-- A pulse that keeps the main charge below the FIRE level brings the
pulsed sensor to its ERROR entry threshold after the pulse has ended. The
start state is any admitted pulse on a rested cell. -/
theorem silent_entry_exists {θ ε s p upper lower level}
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ s)
    (threshold : 19 / 20 ≤ level)
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25)
    (main : ∀ i, s.main i = .ready) (aux : ∀ i q, s.aux i q = .ready)
    (raw : s.raw 0 p = some s.time) (otherRaw : ∀ i q, i ≠ 0 ∨ q ≠ p → s.raw i q = none)
    (sensors : ∀ q, RestBand (s.x 0 (.m q)))
    (gain : Real.exp (s.x 0 (.z p)) ≤ 22 / 5)
    (start : ∀ t, s.time ≤ t → t ≤ s.time + 1 / 10 →
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t < 1)
    (margin : ∀ t ∈ Icc s.time (s.time + 1),
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t < level)
    (ahead : ∀ d ∈ s.pending, s.time + 8 / 5 ≤ d.due) :
    Nonempty (SilentEntry θ s p upper lower level) := by
  have charge : s.x 0 .q < 1 := by
    have h := start s.time le_rfl (by linarith)
    rwa [readyPulse_initial] at h
  obtain ⟨f⟩ := first_input_mark_of_response_margin_until_exists s box 0 p main aux raw otherRaw
    (fun i => by rw [Subsingleton.elim i 0]; exact charge)
    (fun i q => by rw [Subsingleton.elim i 0]; exact lt_of_le_of_lt (sensors q).2 (by norm_num))
    start (sensors p) (by intro d hd; linarith [ahead d hd])
  obtain ⟨g⟩ := f.first_silent_of_response_margin_until_exists box start
    (by intro d hd; linarith [ahead d hd])
  have gAfter : s.time ≤ g.final.time := by
    change s.time ≤ s.time + f.latency + Real.log (5 / 4) / (θ 0).lm p
    linarith [f.early, (box.aux_durations_positive 0 p).1]
  have gBefore : g.final.time < s.time + 1 / 20 := g.deadline
  have preMark : ∀ t ∈ Ico s.time (s.time + f.latency), f.flow.path t 0 .q < level := by
    intro t ht
    have eq := f.flow.ready_single_pulse_solution 0 p s.time (f.main_ready 0) raw
      (fun q h => otherRaw 0 q (Or.inr h)) (by rw [f.aux_ready]; decide) t ⟨ht.1, ht.2.le⟩
    rw [eq]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    exact margin t ⟨ht.1, by linarith [ht.2, f.deadline]⟩
  have preSilent : ∀ t ∈ Ico f.final.time g.final.time, g.flow.path t 0 .q < level := by
    intro t ht
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
    exact margin t ⟨ht', by linarith [ht.2]⟩
  let rate := (θ 0).ls p
  let T := g.final.time + Real.log ((4 / 5) / upper) / rate
  let expiry := s.time + 1
  let edge := readyProtectedEnd θ g.final 0 p .silent (some s.time) expiry
  have rp : 0 < rate := (box.rates_positive 0 p).2.1
  obtain ⟨long, short⟩ := low_entry_silent_duration box p entry
  have late : expiry < T := by
    dsimp only [T, expiry, rate]
    linarith
  have Tlate : T < s.time + 8 / 5 := by
    dsimp only [T, rate]
    linarith
  have up : 0 < upper := by linarith [entry.1]
  obtain ⟨_, sensorContact, sensorStrict⟩ :=
    protected_decay_schedule up (show upper < (4 / 5 : ℝ) by linarith [entry.2]) rp
  let sensor := fun t : ℝ => (4 / 5 : ℝ) * Real.exp (-rate * (t - g.final.time))
  have atT : sensor T = upper := by
    dsimp [sensor, T]
    rw [add_sub_cancel_left]
    exact sensorContact
  have aboveT (t : ℝ) (hs : g.final.time ≤ t) (ht : t < T) : upper < sensor t := by
    apply sensorStrict _ (sub_nonneg.mpr hs)
    dsimp [T] at ht
    linarith
  have edgeSensor : edge.x 0 (.m p) = sensor expiry := by
    simp [edge, readyProtectedEnd, readyProtectedValues, protectedReadyRate, g.sensor_charge, rate, sensor]
  have restSilent (q : Port) (hq : q ≠ p) : RestBand (g.final.x 0 (.m q)) := by
    have h₁ : f.final.x 0 (.m q) =
        relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time (s.time + f.latency) :=
      readyInputValues_other hq
    have h₂ : g.final.x 0 (.m q) =
        relax (1 / 2) (1 / 40) (f.final.x 0 (.m q)) f.final.time f.silentDate :=
      readyProtectedValues_other (origin := some s.time) hq
    rw [h₂, h₁]
    refine relax_restBand ?_ (relax_restBand (by linarith [f.early]) (sensors q))
    change s.time + f.latency ≤ s.time + f.latency + Real.log (5 / 4) / (θ 0).lm p
    linarith [(box.aux_durations_positive 0 p).1]
  have rawCharge (t : ℝ) :
      readyProtectedValues θ g.final 0 p .silent (some s.time) t 0 .q =
        readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t := by
    simp only [readyProtectedValues, protectedRawAmplitude, ite_true]
    exact g.response_restart t
  have silentEnergy := ((g.execution (fun _ _ => [])).physical_invariant box physical).reserve 0
  obtain ⟨rawLeg⟩ := silent_leg_of_margin (upper := upper) (level := level) box
    (show g.final.time < expiry by dsimp only [expiry]; linarith)
    g.main_ready g.aux_silent g.aux_other
    (fun q hq => lt_of_le_of_lt (restSilent q hq).2 (by norm_num)) g.raw_active g.raw_other
    (by intro o h; obtain rfl := (Option.some.inj h).symm; exact ⟨gAfter, le_rfl⟩)
    (by
      intro v hv
      have h := ahead v (show v ∈ s.pending from hv)
      dsimp only [expiry]
      linarith)
    (fun t ht => by rw [rawCharge t]; exact margin t ⟨gAfter.trans ht.1, ht.2⟩)
    (by
      intro t ht
      simp only [readyProtectedValues, and_self, ite_true, protectedReadyRate, g.sensor_charge]
      exact aboveT t ht.1 (ht.2.trans late))
    (by rw [g.sensor_charge]; norm_num) (by rw [g.gain_preserved]; exact gain) silentEnergy
  have edgeCharge : edge.x 0 .q =
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time expiry := rawCharge expiry
  have edgeBelow : edge.x 0 .q < level := by
    rw [edgeCharge]
    exact margin expiry ⟨by dsimp only [expiry]; linarith, le_rfl⟩
  have edgeOther (q : Port) (hq : q ≠ p) : RestBand (edge.x 0 (.m q)) := by
    have value : edge.x 0 (.m q) =
        relax (1 / 2) (1 / 40) (g.final.x 0 (.m q)) g.final.time expiry :=
      readyProtectedValues_other (origin := some s.time) hq
    rw [value]
    exact relax_restBand (by dsimp only [expiry]; linarith) (restSilent q hq)
  have edgeRaw : edge.raw 0 p = some s.time := g.raw_active
  let expired := setRaw edge 0 p none
  have expiredRaw (i : Fin 1) (q : Port) : expired.raw i q = none := by
    rw [Subsingleton.elim i 0]
    by_cases hq : q = p
    · subst q; simp [expired, setRaw]
    · exact (raw_update_other edge 0 p none 0 q (Or.inr hq)).trans (g.raw_other 0 q (Or.inr hq))
  let path := readyProtectedValues θ expired 0 p .silent none
  let boundary := readyProtectedEnd θ expired 0 p .silent none T
  have mPath (t : ℝ) : path t 0 (.m p) = sensor t := by
    simp only [path, readyProtectedValues, and_self, ite_true, protectedReadyRate]
    change edge.x 0 (.m p) * Real.exp (-rate * (t - expiry)) = sensor t
    rw [edgeSensor]
    dsimp [sensor]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have qPath (t : ℝ) : path t 0 .q = relax (1 / 2) (1 / 10) (edge.x 0 .q) expiry t := by
    simp only [path, readyProtectedValues, protectedRawAmplitude, ite_true, rawInputScale,
      mul_zero, readyPulse_zero_eq_relax]
    rfl
  have qBelow (t : ℝ) (ht : expiry ≤ t) : path t 0 .q < level := by
    rw [qPath]
    have h := relax_mem_band (rate := 1 / 2) (target := 1 / 10)
      (low := min (edge.x 0 .q) (1 / 10)) (high := max (edge.x 0 .q) (1 / 10))
      (by norm_num) ht ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
    exact h.2.trans_lt (max_lt edgeBelow (by linarith))
  have sensorIn : expired.x 0 (.m p) ∈ Icc (0 : ℝ) (4 / 5) := by
    change edge.x 0 (.m p) ∈ _
    rw [edgeSensor]
    exact ⟨mul_nonneg (by norm_num) (Real.exp_pos _).le,
      decay_upper le_rfl (by norm_num) rp.le (by dsimp only [expiry]; linarith)⟩
  obtain ⟨tail⟩ := silent_leg_of_margin (s := expired) (upper := upper) (level := level) box
    (show expired.time < T from late) g.main_ready g.aux_silent g.aux_other
    (fun q hq => lt_of_le_of_lt (edgeOther q hq).2 (by norm_num))
    (expiredRaw 0 p) (fun i q _ => expiredRaw i q) (by simp)
    (by
      intro v hv
      have h := ahead v (show v ∈ s.pending from hv)
      linarith)
    (fun t ht => qBelow t ht.1)
    (by
      intro t h
      change upper < path t 0 (.m p)
      rw [mPath]
      have after : expiry ≤ t := h.1
      exact aboveT t (by dsimp only [expiry] at after; linarith) h.2)
    sensorIn (by change Real.exp (s.x 0 (.z p)) ≤ _; exact gain) rawLeg.energy
  have contact : boundary.x 0 (.m p) = upper := (mPath T).trans atT
  refine ⟨{
    mark := f
    silent := g
    pre_mark := preMark
    pre_silent := preSilent
    before := boundary
    trace := .silent rawLeg (.expire edgeRaw rfl (.silent tail (.enter g.aux_silent contact (.nil _))))
    after_pulse := late
    deadline := Tlate
    main := g.main_ready 0
    mode := g.aux_silent
    other_modes := fun q hq => g.aux_other 0 q (Or.inr hq)
    sensor := contact
    other_sensors := ?_
    charge := ?_
    gains := fun q => g.gain_preserved 0 q
    recovery := g.recovery_preserved 0
    energy := tail.energy
    raw := expiredRaw 0
    queue := g.queue_preserved }⟩
  · intro q hq
    have value : boundary.x 0 (.m q) = relax (1 / 2) (1 / 40) (edge.x 0 (.m q)) expiry T :=
      readyProtectedValues_other (origin := none) hq
    rw [value]
    exact relax_restBand late.le (edgeOther q hq)
  · change path T 0 .q = _
    rw [qPath, edgeCharge]
    rfl

end RecursiveLearning.Native
