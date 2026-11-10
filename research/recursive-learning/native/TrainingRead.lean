import LiveErrorExpiry
import KernelR.HybridFirstInputError

/-! A two-pulse experiment. Training starts from a READY cell at rest.
The read is scheduled before the experiment and uses the actual learned
state. The construction covers every ordering of raw expiry and ERROR entry. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

noncomputable def trainingStart (time : ℝ) (gains : Port → ℝ) (p : Port) (delay : ℝ := 16) : Snapshot 1 :=
  { toleranceStartOn time gains p with
    raw := fun _ _ => none
    pending := [errorReadDelivery p time, errorReadDelivery p (time + delay)] }

noncomputable def trainingAdmitted (time : ℝ) (gains : Port → ℝ) (p : Port) (delay : ℝ := 16) : Snapshot 1 :=
  { setRaw (trainingStart time gains p delay) 0 p (some time) with
    pending := [errorReadDelivery p (time + delay)] }

/-- A SILENT piece with a realized exit guard. The pulse origin, when
present, is carried through unchanged. -/
structure TrainingSilentLeg (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    (origin : Option ℝ) (upper level stop : ℝ) where
  positive : s.time < stop
  main : ∀ i, s.main i = .ready
  mode : s.aux 0 p = .silent
  other_modes : ∀ q ≠ p, s.aux 0 q = .ready
  raw : s.raw 0 p = origin
  other_raw : ∀ i q, i ≠ 0 ∨ q ≠ p → s.raw i q = none
  continuous : ∀ i c, ContinuousOn (fun t => readyProtectedValues θ s 0 p .silent origin t i c)
    (Icc s.time stop)
  integrable : ∀ i c, IntervalIntegrable (fun t =>
    field θ s (readyProtectedValues θ s 0 p .silent origin t) t i c) volume s.time stop
  integral : ∀ t ∈ Icc s.time stop, ∀ i c,
    readyProtectedValues θ s 0 p .silent origin t i c =
      s.x i c + ∫ v in s.time..t, field θ s (readyProtectedValues θ s 0 p .silent origin v) v i c
  main_guard : ∀ t ∈ Ico s.time stop, readyProtectedValues θ s 0 p .silent origin t 0 .q < level
  sensor_guard : ∀ t ∈ Ico s.time stop, upper < readyProtectedValues θ s 0 p .silent origin t 0 (.m p)
  other_guard : ∀ t ∈ Ico s.time stop, ∀ q ≠ p,
    readyProtectedValues θ s 0 p .silent origin t 0 (.m q) < 1
  raw_support : ∀ o, origin = some o → o ≤ s.time ∧ stop ≤ o + 1
  pending : ∀ d ∈ s.pending, stop ≤ d.due
  nominal : upper = 1 / 10 → level = 1 →
    Flow θ s (readyProtectedEnd θ s 0 p .silent origin stop)
  energy : 50 ≤ (readyProtectedEnd θ s 0 p .silent origin stop).x 0 .energy ∧
    (readyProtectedEnd θ s 0 p .silent origin stop).x 0 .energy ≤ 100

/-- The portion between SILENT entry and the start of the no-current
ERROR tail. Only the original mode update is used at the realized
upper threshold. The expiry constructor removes the original raw tag. -/
inductive TrainingTrace (θ : Fin 1 → Parameters) (p : Port) (upper lower level : ℝ) :
    Snapshot 1 → Snapshot 1 → Type
  | nil (s) : TrainingTrace θ p upper lower level s s
  | silent {s u origin stop} (leg : TrainingSilentLeg θ s p origin upper level stop)
      (rest : TrainingTrace θ p upper lower level (readyProtectedEnd θ s 0 p .silent origin stop) u) :
      TrainingTrace θ p upper lower level s u
  | enter {s u} (mode : s.aux 0 p = .silent) (contact : s.x 0 (.m p) = upper)
      (rest : TrainingTrace θ p upper lower level (setAux s 0 p .error) u) :
      TrainingTrace θ p upper lower level s u
  | expire {s u origin} (active : s.raw 0 p = some origin) (due : s.time = origin + 1)
      (rest : TrainingTrace θ p upper lower level (setRaw s 0 p none) u) :
      TrainingTrace θ p upper lower level s u
  | liveError {s u origin} (leg : LiveErrorExpiry θ s p origin lower level)
      (rest : TrainingTrace θ p upper lower level (errorTailEnd θ s 0 p (some origin) (origin + 1)) u) :
      TrainingTrace θ p upper lower level s u

noncomputable def TrainingTrace.nominalExecution {θ p lower s u}
    (trace : TrainingTrace θ p (1 / 10) lower 1 s u) :
    Execution θ (fun _ _ => []) s u := by
  induction trace with
  | nil s => exact .nil s
  | silent leg _ ih => exact .cons (.flow (leg.nominal rfl rfl)) ih
  | enter mode contact _ ih => exact .cons (.jump (.error _ 0 p mode contact)) ih
  | expire active due _ ih => exact .cons (.jump (.rawEnd _ 0 p _ active due)) ih
  | liveError leg _ ih => exact .cons (.flow leg.flow) ih

/-- A single trajectory from before training delivery through the read's
first FIRE, with every continuous coordinate carried across each cut. -/
structure TrainingRead (θ : Fin 1 → Parameters) (time : ℝ) (gains : Port → ℝ) (p : Port)
    (upper lower level : ℝ) (delay : ℝ := 16) where
  train : Jump (fun _ _ => []) (trainingStart time gains p delay) (trainingAdmitted time gains p delay)
  mark : FirstInputMark θ (trainingAdmitted time gains p delay) 0 p
  silent : FirstInputSilent mark
  pre_mark : ∀ t ∈ Ico time (time + mark.latency), mark.flow.path t 0 .q < level
  pre_silent : ∀ t ∈ Ico mark.final.time silent.final.time, silent.flow.path t 0 .q < level
  errorStart : Snapshot 1
  trace : TrainingTrace θ p upper lower level silent.final errorStart
  handoff : ErrorReadHandoff θ errorStart p (errorStart.x 0 (.m p)) lower level (time + delay)
  read_silent_guard : ∀ t ∈ Icc handoff.decision.silent.final.time handoff.decision.stop,
    upper < readyProtectedValues θ handoff.decision.silent.final 0 p .silent
      (some handoff.readStart.time) t 0 (.m p)
  read_date : handoff.readStart.time = time + delay
  dose_from_birth : handoff.learned = gains p + 8 * (upper - lower)
  read_charge_bound : handoff.readStart.x 0 .q ≤
    1 / 10 + (21 / 25) * Real.exp (-(1 / 2) * (delay - 159 / 100))
  other_gains_at_read : ∀ q ≠ p, handoff.readStart.x 0 (.z q) = gains q

private theorem silentRateLower {θ ε} (box : @PhysicalBox 1 θ ε) (p : Port) :
    5 / 3 ≤ (θ 0).ls p := by
  have h := (box.2 0 p).2.2.1.1
  change Real.log 8 / (53 / 50) * (1 - ε) ≤ (θ 0).ls p at h
  have logLower : (2 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  have eps : (9 / 10 : ℝ) ≤ 1 - ε := by linarith [box.epsilon_bounds.2]
  have hmul := mul_le_mul (show (2 : ℝ) / (53 / 50) ≤ Real.log 8 / (53 / 50) by linarith)
    eps (by norm_num) (by linarith)
  linarith

private theorem silent_duration {θ ε upper} (box : @PhysicalBox 1 θ ε) (p : Port)
    (hi : |upper - 1 / 10| ≤ 1 / 200) :
    let r := (θ 0).ls p
    0 < Real.log ((4 / 5) / upper) / r ∧
    Real.log 8 / r - Real.log ((4 / 5) / upper) / r ≤ 3 / 100 ∧
    Real.log ((4 / 5) / upper) / r - Real.log 8 / r ≤ 1 / 25 := by
  dsimp only
  obtain ⟨hl, hu⟩ := abs_le.mp hi
  have up : 0 < upper := by linarith
  have rp := (box.rates_positive 0 p).2.1
  have rlower := silentRateLower box p
  have ratio : 1 < (4 / 5) / upper := (lt_div_iff₀ up).2 (by linarith)
  have h : Real.log 8 - Real.log ((4 / 5) / upper) = Real.log (upper / (1 / 10)) := by
    rw [Real.log_div (by norm_num) (ne_of_gt up), Real.log_div (ne_of_gt up) (by norm_num)]
    have h8 : Real.log (4 / 5 : ℝ) - Real.log (1 / 10) = Real.log 8 := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    linarith
  refine ⟨div_pos (Real.log_pos ratio) rp, ?_, ?_⟩
  · rw [← sub_div]
    apply (div_le_iff₀ rp).2
    rw [h]
    have hlog := Real.log_le_sub_one_of_pos (div_pos up (by norm_num : (0 : ℝ) < 1 / 10))
    linarith
  · rw [← sub_div]
    apply (div_le_iff₀ rp).2
    have hreverse : Real.log ((4 / 5) / upper) - Real.log 8 = Real.log ((1 / 10) / upper) := by
      rw [show Real.log ((4 / 5) / upper) - Real.log 8 = -(Real.log 8 - Real.log ((4 / 5) / upper)) by ring,
        h, ← Real.log_inv]
      congr 1
      rw [inv_div]
    rw [hreverse]
    have hlog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 1 / 10) up)
    have hratio : (1 / 10) / upper ≤ 20 / 19 := (div_le_iff₀ up).2 (by linarith)
    linarith

private theorem makeSilentLeg {θ ε s p origin upper level stop}
    (box : @PhysicalBox 1 θ ε) (threshold : 19 / 20 ≤ level)
    (positive : s.time < stop)
    (main : ∀ i, s.main i = .ready) (mode : s.aux 0 p = .silent)
    (other : ∀ i q, i ≠ 0 ∨ q ≠ p → s.aux i q = .ready)
    (rest : ∀ q ≠ p, s.x 0 (.m q) = 1 / 40)
    (raw : s.raw 0 p = origin) (otherRaw : ∀ i q, i ≠ 0 ∨ q ≠ p → s.raw i q = none)
    (support : ∀ o, origin = some o → o ≤ s.time ∧ stop ≤ o + 1)
    (pending : ∀ d ∈ s.pending, stop ≤ d.due)
    (charge : ∀ t ∈ Icc s.time stop,
      readyProtectedValues θ s 0 p .silent origin t 0 .q ∈ Icc (1 / 10) (217 / 250))
    (sensor : ∀ t ∈ Ico s.time stop,
      upper < readyProtectedValues θ s 0 p .silent origin t 0 (.m p))
    (sensorIn : s.x 0 (.m p) ∈ Icc 0 (4 / 5))
    (gain : Real.exp (s.x 0 (.z p)) ≤ 6 / 5)
    (energy : 50 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100) :
    Nonempty (TrainingSilentLeg θ s p origin upper level stop) := by
  let path := readyProtectedValues θ s 0 p .silent origin
  have fieldEq (t : ℝ) (ht : t ∈ Ico s.time stop) (i : Fin 1) (c : Coord) :
      field θ s (path t) t i c = readyProtectedRhs θ s 0 p .silent origin t i c :=
    readyProtected_field s 0 p .silent origin (Or.inr rfl) main mode other raw otherRaw t ht.1
      (fun o h => ⟨(support o h).1, ht.2.trans_le (support o h).2⟩) i c
  have qbound (t : ℝ) (ht : t ∈ Ico s.time stop) : path t 0 .q < level := by
    linarith [(charge t ⟨ht.1, ht.2.le⟩).2]
  have mbound (t : ℝ) (q : Port) (hq : q ≠ p) : path t 0 (.m q) < 1 := by
    norm_num [path, readyProtectedValues, hq, rest q hq, relax]
  refine ⟨⟨positive, main, mode, fun q h => other 0 q (Or.inr h), raw, otherRaw,
    ?_, ?_, ?_, qbound, sensor, fun t _ => mbound t, support, pending, ?_, ?_⟩⟩
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
    exact readyProtectedFlow s 0 p .silent origin positive (Or.inr rfl) main mode other raw otherRaw support
      (fun i => by rw [Subsingleton.elim i 0, ← congrFun (congrFun (readyProtectedValues_initial
        (θ := θ) s 0 p .silent origin) 0) .q]; linarith [(charge s.time ⟨le_rfl, positive.le⟩).2])
      (fun i q h => by rw [Subsingleton.elim i 0, rest q (h.resolve_left (not_not_intro (Subsingleton.elim i 0)))]; norm_num)
      (fun t ht => by simpa only [path, readyProtectedValues, protectedRawAmplitude, ite_true, hl] using qbound t ht)
      (fun t ht => by
        simpa only [readyProtectedValues, and_self, ite_true, protectedReadyRate, reduceCtorEq, ite_false, hu]
          using sensor t ht) pending
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
      have ARange : 0 ≤ A ∧ A ≤ 6 / 5 := by
        change 0 ≤ (if (0 : Fin 1) = 0 then _ else _) ∧ (if (0 : Fin 1) = 0 then _ else _) ≤ _
        simp only [ite_true]
        exact ⟨mul_nonneg (Real.exp_pos _).le (rawInputScale_nonnegative _ _),
          by simpa using mul_le_mul gain rawBound (rawInputScale_nonnegative _ _) (by norm_num)⟩
      have h₁ := decay_upper (mul_le_mul ARange.2 a_coarse_bounds.2.le aPos
        (by norm_num : (0 : ℝ) ≤ 6 / 5)) (by norm_num) aPos (sub_nonneg.mpr ht.1)
      have h₂ := decay_upper (mul_le_mul (box.coarse_upper 0 p).2.2.1 sensorIn.2 sensorIn.1
        (by norm_num : (0 : ℝ) ≤ 3)) (by norm_num) rp.le (sub_nonneg.mpr ht.1)
      dsimp [W]
      constructor
      · exact add_nonneg (mul_nonneg (mul_nonneg ARange.1 aPos) (Real.exp_pos _).le)
          (mul_nonneg (mul_nonneg rp.le sensorIn.1) (Real.exp_pos _).le)
      · linarith


/-- The scheduled two-pulse task works for either full fabrication box.
ERROR entry and pulse expiry are both realized at their actual dates. -/
theorem training_read_exists_in_band {θ ε time gains p upper lower level delay}
    (box : @PhysicalBox 1 θ ε)
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : 7 / 800 ≤ lower)
    (dose : 11 / 20 ≤ 8 * (upper - lower) ∧ 8 * (upper - lower) ≤ 77 / 100)
    (delayMin : 16 ≤ delay)
    (settled : |lower - 1 / 40| * Real.exp (-(1 / 2) * (delay - 159 / 100)) ≤ 1 / 100000)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    Nonempty (TrainingRead θ time gains p upper lower level delay) := by
  let s := trainingAdmitted time gains p delay
  let d := errorReadDelivery p (time + delay)
  let route : Router 1 := fun _ _ => []
  have train : Jump route (trainingStart time gains p delay) s :=
    .arrive (trainingStart time gains p delay) (errorReadDelivery p time) [] [d] rfl rfl rfl
  have raw : s.raw 0 p = some s.time := by
    simp [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw]
  have otherRaw (i : Fin 1) (q : Port) (h : i ≠ 0 ∨ q ≠ p) : s.raw i q = none := by
    have hi : i = 0 := Subsingleton.elim _ _
    have hq := h.resolve_left (not_not_intro hi)
    simp [s, trainingAdmitted, trainingStart, setRaw, hi, hq]
  have margin (t : ℝ) (ht : s.time ≤ t) :
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t ≤ 217 / 250 := by
    have h := readyPulse_uniform_bound (initial := (1 / 10 : ℝ))
      (amplitude := Real.exp (gains p)) le_rfl le_rfl gain.2 (by norm_num) ht
    change readyPulse (1 / 10) (Real.exp (gains p)) s.time t ≤ 217 / 250
    linarith
  have ahead : ∀ v ∈ s.pending, s.time + 2 ≤ v.due := by
    norm_num [s, trainingAdmitted, trainingStart, toleranceStartOn, setRaw, errorReadDelivery]
    linarith
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
  have preMark : ∀ t ∈ Ico time (time + f.latency), f.flow.path t 0 .q < level := by
    intro t ht
    have eq := f.flow.ready_single_pulse_solution 0 p s.time (f.main_ready 0) raw
      (fun q h => otherRaw 0 q (Or.inr h)) (by rw [f.aux_ready]; decide) t ⟨ht.1, ht.2.le⟩
    rw [eq]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    linarith [margin t ht.1, threshold.1]
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
    linarith [margin t ht', threshold.1]
  let rate := (θ 0).ls p
  let T := g.final.time + Real.log ((4 / 5) / upper) / rate
  let expiry := s.time + 1
  let cut := min T expiry
  let edge := readyProtectedEnd θ g.final 0 p .silent (some s.time) cut
  have rp : 0 < rate := (box.rates_positive 0 p).2.1
  have gAfter : s.time ≤ g.final.time := by
    change s.time ≤ s.time + f.latency + Real.log (5 / 4) / (θ 0).lm p
    linarith [f.early, (box.aux_durations_positive 0 p).1]
  have gBefore : g.final.time < s.time + 1 / 20 := g.deadline
  obtain ⟨duration, shift, shiftLate⟩ := silent_duration box p hi
  have Tpos : g.final.time < T := lt_add_of_pos_right _ duration
  have Tearly : s.time + 24 / 25 < T := by
    have h := (g.errorDate_bounds box).1
    change s.time + 99 / 100 < g.final.time + Real.log 8 / rate at h
    dsimp only [T]
    linarith
  have Tlate : T < time + 127 / 100 := by
    have late := (g.errorDate_bounds box).2
    change g.final.time + Real.log 8 / rate < time + 123 / 100 at late
    dsimp only [T]
    linarith
  have cutPos : g.final.time < cut := lt_min Tpos (by dsimp [expiry]; linarith)
  have cutLate : cut ≤ s.time + 1 := min_le_right _ _
  have cutLe : cut ≤ T := min_le_left _ _
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp hi
  have up : 0 < upper := by linarith
  obtain ⟨_, sensorContact, sensorStrict⟩ :=
    protected_decay_schedule up (show upper < (4 / 5 : ℝ) by linarith) rp
  let sensor := fun t : ℝ => (4 / 5 : ℝ) * Real.exp (-rate * (t - g.final.time))
  have atT : sensor T = upper := by
    dsimp [sensor, T]
    rw [add_sub_cancel_left]
    exact sensorContact
  have aboveT (t : ℝ) (hs : g.final.time ≤ t) (ht : t < T) : upper < sensor t := by
    apply sensorStrict _ (sub_nonneg.mpr hs)
    dsimp [T] at ht
    linarith
  have edgeSensor : edge.x 0 (.m p) = sensor cut := by
    simp [edge, readyProtectedEnd, readyProtectedValues, protectedReadyRate, g.sensor_charge, rate, sensor]
  have restSilent (q : Port) (hq : q ≠ p) : g.final.x 0 (.m q) = 1 / 40 := by
    simp [FirstInputSilent.final, FirstInputMark.silentFinal, FirstInputMark.silentBefore,
      readyProtectedEnd, readyProtectedValues, FirstInputMark.final, setAux,
      readyInputEnd, readyInputValues, readyInputAuxAmplitude, hq, s, trainingAdmitted,
      trainingStart, toleranceStartOn, setRaw, relax, auxPulse, readyPulse]
  have scalarLower (t : ℝ) (ht : s.time ≤ t) :
      1 / 10 ≤ readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t := by
    change 1 / 10 ≤ readyPulse (1 / 10) (Real.exp (gains p)) s.time t
    have h := mul_nonneg (Real.exp_pos (gains p)).le (response_nonnegative (sub_nonneg.mpr ht))
    simp only [readyPulse, sub_self, zero_mul, add_zero]
    linarith
  have rawCharge (t : ℝ) (ht : g.final.time ≤ t) :
      readyProtectedValues θ g.final 0 p .silent (some s.time) t 0 .q ∈ Icc (1 / 10) (217 / 250) := by
    simp only [readyProtectedValues, protectedRawAmplitude, ite_true]
    rw [g.response_restart]
    exact ⟨scalarLower t (gAfter.trans ht), margin t (gAfter.trans ht)⟩
  have startPhysical : PhysicalInvariant θ s := by
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
  have silentEnergy := ((g.execution route).physical_invariant box startPhysical).reserve 0
  obtain ⟨rawLeg⟩ := makeSilentLeg box threshold.1 cutPos g.main_ready g.aux_silent g.aux_other
    restSilent g.raw_active g.raw_other
    (by intro o h; obtain rfl := (Option.some.inj h).symm; exact ⟨gAfter, cutLate⟩)
    (by intro v hv; have h := ahead v (g.queue_preserved ▸ hv); linarith)
    (fun t ht => rawCharge t ht.1)
    (by
      intro t ht
      simp only [readyProtectedValues, and_self, ite_true, protectedReadyRate, g.sensor_charge]
      exact aboveT t ht.1 (ht.2.trans_le cutLe))
    (by rw [g.sensor_charge]; norm_num) (by rw [g.gain_preserved]; exact gain.2) silentEnergy
  have edgeCharge : edge.x 0 .q ∈ Icc (1 / 10) (217 / 250) := rawCharge cut cutPos.le
  have edgeOther (q : Port) (hq : q ≠ p) : edge.x 0 (.m q) = 1 / 40 := by
    simp [edge, readyProtectedEnd, readyProtectedValues, hq, restSilent q hq, relax]
  have edgeRaw : edge.raw 0 p = some s.time := g.raw_active
  have edgePending : edge.pending = [d] := g.queue_preserved
  have finish (e : Snapshot 1) (trace : TrainingTrace θ p upper lower level g.final e)
      (lead : e.time ≤ time + 127 / 100)
      (em : e.main 0 = .ready) (ea : e.aux 0 p = .error)
      (eqBand : e.x 0 .q ∈ Icc (1 / 10) (47 / 50))
      (energy : 50 ≤ e.x 0 .energy ∧ e.x 0 .energy ≤ 100)
      (es : lower < e.x 0 (.m p) ∧ e.x 0 (.m p) ≤ 21 / 200)
      (other : ∀ q ≠ p, e.aux 0 q = .ready ∧ e.x 0 (.m q) = 1 / 40)
      (eraw : ∀ q, e.raw 0 q = none) (queue : e.pending = [d])
      (b : e.x 0 .b = 2 / 25) (otherGain : ∀ q ≠ p, e.x 0 (.z q) = gains q)
      (balance : e.x 0 (.z p) + 8 * (e.x 0 (.m p) - lower) = gains p + 8 * (upper - lower)) :
      Nonempty (TrainingRead θ time gains p upper lower level delay) := by
    have output : 2 ≤ Real.exp (e.x 0 (.z p) + 8 * (e.x 0 (.m p) - lower)) ∧
        Real.exp (e.x 0 (.z p) + 8 * (e.x 0 (.m p) - lower)) ≤ 13 / 5 := by
      rw [balance]
      exact wide_error_dose_gain dose gain
    have cap (q : Port) : e.x 0 (.z q) ≤ Real.log ((θ 0).cap q) := by
      by_cases h : q = p
      · subst q
        have hcap := (box.2 0 p).1.1
        change 4 * (1 - ε) ≤ (θ 0).cap p at hcap
        apply Real.exp_le_exp.mp
        rw [Real.exp_log (box.cap_positive 0 p)]
        have leGain := Real.exp_le_exp.mpr
          (show e.x 0 (.z p) ≤ e.x 0 (.z p) + 8 * (e.x 0 (.m p) - lower) by linarith [es.1])
        linarith [leGain, output.2, box.epsilon_bounds.2]
      · rw [otherGain q h]
        exact caps q
    have rest : |lower - 1 / 40| * Real.exp (-(1 / 2) * (time + delay - (e.time + 8 / 25))) ≤
        1 / 100000 := by
      apply le_trans _ settled
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg _)
    obtain ⟨h⟩ := error_read_handoff_of_gain box threshold es lo output cap
      (by rw [b]; norm_num) energy em eqBand ea rfl other eraw (by linarith) rest queue
    refine ⟨⟨train, f, g, preMark, preSilent, e, trace, h, ?_, h.read_date, ?_, ?_, ?_⟩⟩
    · intro t ht
      let read := h.decision
      have deadline := read.outcome.2.1
      let Tread := read.silent.final.time + Real.log ((4 / 5) / upper) / rate
      have hdate := (read.silent.errorDate_bounds box).1
      change h.readStart.time + 99 / 100 < read.silent.final.time + Real.log 8 / rate at hdate
      have early : h.readStart.time + 24 / 25 < Tread := by dsimp [Tread]; linarith
      have before : t < Tread := by
        have ht' := ht.2
        change t ≤ read.stop at ht'
        linarith
      change upper < readyProtectedValues θ read.silent.final 0 p .silent
        (some h.readStart.time) t 0 (.m p)
      simp only [readyProtectedValues, and_self, ite_true, protectedReadyRate, read.silent.sensor_charge]
      exact sensorStrict _ (sub_nonneg.mpr ht.1) (by dsimp [Tread] at before; linarith)
    · linarith [h.span.dose, balance]
    · refine h.read_charge_bound.trans (add_le_add_right ?_ _)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    · intro q neq
      exact (h.other_gains_at_read q neq).trans (otherGain q neq)
  by_cases early : T < expiry
  · have same : cut = T := min_eq_left early.le
    have entrySensor : edge.x 0 (.m p) = upper := by rw [edgeSensor, same, atT]
    let e := setAux edge 0 p .error
    have eSensor : e.x 0 (.m p) = upper := entrySensor
    have eGain : e.x 0 (.z p) = gains p := g.gain_preserved 0 p
    have eOther (q : Port) (hq : q ≠ p) : e.aux 0 q = .ready ∧ e.x 0 (.m q) = 1 / 40 := by
      refine ⟨?_, edgeOther q hq⟩
      simpa [e, setAux, hq, edge, readyProtectedEnd] using g.aux_other 0 q (Or.inr hq)
    have timeEq : e.time = T := same
    obtain ⟨live⟩ := live_error_expiry (s := e) (origin := s.time) (lower := lower) box threshold.1
      (by rw [timeEq]; exact ⟨Tearly.le, early⟩) (by linarith [dose.1])
      (by rw [eSensor]; constructor <;> linarith)
      (by rw [eGain, eSensor]; exact (wide_error_dose_gain dose gain).2)
      edgeCharge rawLeg.energy (g.main_ready 0) (by simp [e, setAux])
      eOther edgeRaw (fun q hq => g.raw_other 0 q (Or.inr hq))
      (by
        intro v hv
        change v ∈ edge.pending at hv
        have h := ahead v (g.queue_preserved ▸ hv)
        linarith)
    let boundary := errorTailEnd θ e 0 p (some s.time) expiry
    let expired := setRaw boundary 0 p none
    have em : expired.x 0 (.m p) = errorTailSensor θ e 0 p expiry := by
      simp [expired, setRaw, boundary, errorTailEnd, errorTailValues]
    have ez : expired.x 0 (.z p) = gains p + 8 * (upper - expired.x 0 (.m p)) := by
      rw [em]
      simp [expired, setRaw, boundary, errorTailEnd, errorTailValues, errorTailGain, eGain, eSensor]
    have expiredOther (q : Port) (hq : q ≠ p) :
        expired.aux 0 q = .ready ∧ expired.x 0 (.m q) = 1 / 40 := by
      refine ⟨(eOther q hq).1, ?_⟩
      simp [expired, setRaw, boundary, errorTailEnd, errorTailValues, hq, (eOther q hq).2, relax]
    have expiredRaw (q : Port) : expired.raw 0 q = none := by
      by_cases hq : q = p
      · subst q; simp [expired, setRaw]
      · exact (raw_update_other boundary 0 p none 0 q (Or.inr hq)).trans (g.raw_other 0 q (Or.inr hq))
    apply finish expired
      (.silent rawLeg (.enter g.aux_silent entrySensor (.liveError live (.expire edgeRaw rfl (.nil _)))))
      (by change time + 1 ≤ time + 127 / 100; linarith)
      (g.main_ready 0) (by change e.aux 0 p = .error; simp [e, setAux])
      live.charge live.energy
      ⟨live.above_lower, ?_⟩ expiredOther expiredRaw edgePending rfl
      (fun q hq => by
        simp [expired, setRaw, boundary, errorTailEnd, errorTailValues, hq,
          show e.x 0 (.z q) = gains q from g.gain_preserved 0 q])
      (by rw [ez]; ring)
    rw [em]
    apply decay_upper (by rw [eSensor]; linarith) (by norm_num)
      (box.rates_positive 0 p).2.2.le
    rw [timeEq]
    exact sub_nonneg.mpr early.le
  · have late : expiry ≤ T := le_of_not_gt early
    have same : cut = expiry := min_eq_right late
    let expired := setRaw edge 0 p none
    have expiredDate : expired.time = expiry := same
    have expiredRaw (i : Fin 1) (q : Port) : expired.raw i q = none := by
      rw [Subsingleton.elim i 0]
      by_cases hq : q = p
      · subst q; simp [expired, setRaw]
      · exact (raw_update_other edge 0 p none 0 q (Or.inr hq)).trans (g.raw_other 0 q (Or.inr hq))
    have reach (before : Snapshot 1)
        (date : before.time = T)
        (bc : before.x 0 .q ∈ Icc (1 / 10) (217 / 250))
        (en : 50 ≤ before.x 0 .energy ∧ before.x 0 .energy ≤ 100)
        (sensorAt : before.x 0 (.m p) = upper)
        (bm : before.main 0 = .ready)
        (bo : ∀ q ≠ p, before.aux 0 q = .ready ∧ before.x 0 (.m q) = 1 / 40)
        (br : ∀ q, before.raw 0 q = none)
        (queue : before.pending = [d])
        (b : before.x 0 .b = 2 / 25) (gainsBefore : ∀ q, before.x 0 (.z q) = gains q)
        (entered : TrainingTrace θ p upper lower level g.final (setAux before 0 p .error)) :
        Nonempty (TrainingRead θ time gains p upper lower level delay) := by
      let e := setAux before 0 p .error
      apply finish e entered (by change before.time ≤ time + 127 / 100; rw [date]; linarith)
        bm (by simp [e, setAux]) ⟨bc.1, bc.2.trans (by norm_num)⟩ en
        (by change lower < before.x 0 (.m p) ∧ before.x 0 (.m p) ≤ 21 / 200
            rw [sensorAt]; constructor <;> linarith)
        (fun q hq => ⟨by simpa [e, setAux, hq] using (bo q hq).1, (bo q hq).2⟩)
        br queue b (fun q _ => gainsBefore q)
      change before.x 0 (.z p) + 8 * (before.x 0 (.m p) - lower) = _
      rw [gainsBefore, sensorAt]
    by_cases equal : expiry = T
    · have sensorAt : expired.x 0 (.m p) = upper := by
        change edge.x 0 (.m p) = _
        rw [edgeSensor, same, equal, atT]
      exact reach expired (same.trans equal)
        edgeCharge rawLeg.energy sensorAt (g.main_ready 0)
        (fun q hq => ⟨g.aux_other 0 q (Or.inr hq), edgeOther q hq⟩) (expiredRaw 0) edgePending
        rfl (g.gain_preserved 0)
        (.silent rawLeg (.expire edgeRaw same (.enter g.aux_silent sensorAt (.nil _))))
    · have ht : expired.time < T := by rw [expiredDate]; exact lt_of_le_of_ne late equal
      let path := readyProtectedValues θ expired 0 p .silent none
      let boundary := readyProtectedEnd θ expired 0 p .silent none T
      have mPath (t : ℝ) : path t 0 (.m p) = sensor t := by
        simp only [path, readyProtectedValues, and_self, ite_true, protectedReadyRate]
        change edge.x 0 (.m p) * Real.exp (-rate * (t - expired.time)) = sensor t
        rw [edgeSensor, same, expiredDate]
        dsimp [sensor]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      have qPath (t : ℝ) (h : expired.time ≤ t) : path t 0 .q ∈ Icc (1 / 10) (217 / 250) := by
        simp only [path, readyProtectedValues, protectedRawAmplitude, ite_true, rawInputScale,
          mul_zero, readyPulse_zero_eq_relax]
        exact relax_mem_band (by norm_num) h edgeCharge (by norm_num)
      have sensorIn : expired.x 0 (.m p) ∈ Icc 0 (4 / 5) := by
        change edge.x 0 (.m p) ∈ _
        rw [edgeSensor, same]
        exact ⟨mul_nonneg (by norm_num) (Real.exp_pos _).le,
          decay_upper le_rfl (by norm_num) rp.le (by dsimp [expiry]; linarith)⟩
      obtain ⟨tail⟩ := makeSilentLeg (s := expired) box threshold.1 ht g.main_ready
        g.aux_silent g.aux_other edgeOther (expiredRaw 0 p) (fun i q _ => expiredRaw i q)
        (by simp)
        (by intro v hv; change v ∈ s.pending at hv; simp [s, trainingAdmitted] at hv; subst v
            change T ≤ time + delay; linarith)
        (fun t ht => qPath t ht.1)
        (by
          intro t h
          change upper < path t 0 (.m p)
          rw [mPath]
          have after : expiry ≤ t := expiredDate ▸ h.1
          exact aboveT t (by dsimp [expiry] at after; linarith) h.2)
        sensorIn (by change Real.exp (gains p) ≤ _; exact gain.2) rawLeg.energy
      have contact : boundary.x 0 (.m p) = upper := (mPath T).trans atT
      exact reach boundary rfl
        (qPath T ht.le) tail.energy contact (g.main_ready 0)
        (fun q hq => ⟨g.aux_other 0 q (Or.inr hq), by
          simp [boundary, readyProtectedEnd, readyProtectedValues, hq,
            show expired.x 0 (.m q) = 1 / 40 from edgeOther q hq, relax]⟩)
        (expiredRaw 0) edgePending rfl (g.gain_preserved 0)
        (.silent rawLeg (.expire edgeRaw same (.silent tail (.enter g.aux_silent contact (.nil _)))))

/-- At nominal thresholds, the entire trajectory is a native R execution. -/
noncomputable def TrainingRead.nominalExecution {θ time gains p}
    (run : TrainingRead θ time gains p (1 / 10) (1 / 40) 1) :
    Execution θ (fun _ _ => []) (trainingStart time gains p) run.handoff.decision.final :=
  .cons (.jump run.train) ((run.silent.execution (fun _ _ => [])).append
    (run.trace.nominalExecution.append run.handoff.nominalExecution))

/-- The original 16-unit training and read schedule. -/
theorem training_read_exists {θ ε time gains p upper lower level}
    (box : @PhysicalBox 1 θ ε)
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : |lower - 1 / 40| ≤ 1 / 800)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    Nonempty (TrainingRead θ time gains p upper lower level) := by
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp hi
  obtain ⟨lo₁, lo₂⟩ := abs_le.mp lo
  apply training_read_exists_in_band box threshold hi (by linarith)
    ⟨by linarith, by linarith⟩ (by norm_num) _ gain caps
  have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 13 / 2 by norm_num) 8
  norm_num [Finset.sum_range_succ] at series
  have decay : Real.exp (-(1 / 2) * (16 - 159 / 100 : ℝ)) ≤ 1 / 125 := by
    calc
      _ ≤ Real.exp (-(13 / 2)) := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ _ := by
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num)
          (show (125 : ℝ) ≤ Real.exp (13 / 2) by linarith)
  exact (mul_le_mul lo decay (Real.exp_pos _).le (by norm_num)).trans (by norm_num)

end RecursiveLearning.Native
