import ParameterTraining
import StopLearningLatency

/-! A training pulse that leaves the cell silent, in the regime where the
ERROR entry threshold is low enough for the write to start after the pulse
has ended. The construction starts from any rested state and uses the
realized thresholds of the cell. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

theorem execution_emissions_append {n θ route} {s u v : Snapshot n}
    (e : ParameterExecution θ route s u) (f : ParameterExecution θ route u v) :
    (e.append f).emissions = e.emissions ++ f.emissions := by
  induction e with
  | nil _ => rfl
  | cons m rest ih => simp [ParameterExecution.append, ih]

/-- An execution of the single cell from `s` to `u` with exactly `n`
FIRE events. -/
def Runs (θ : Fin 1 → Parameters) (s u : Snapshot 1) (n : ℕ) : Prop :=
  ∃ e : ParameterExecution θ (fun _ _ => []) s u, e.emissions.length = n

theorem Runs.nil {θ : Fin 1 → Parameters} (s : Snapshot 1) : Runs θ s s 0 := ⟨.nil s, rfl⟩

theorem Runs.flow {θ : Fin 1 → Parameters} {s u : Snapshot 1} (f : ParameterFlow θ s u) :
    Runs θ s u 0 := ⟨.cons (.flow f) (.nil _), rfl⟩

theorem Runs.jump {θ : Fin 1 → Parameters} {s u : Snapshot 1} {n : ℕ}
    (j : ParameterJump θ (fun _ _ => []) s u) (h : j.emissions.length = n) : Runs θ s u n :=
  ⟨.cons (.jump j) (.nil _), by simpa [ParameterExecution.emissions] using h⟩

theorem Runs.append {θ : Fin 1 → Parameters} {s u v : Snapshot 1} {n m : ℕ}
    (first : Runs θ s u n) (second : Runs θ u v m) : Runs θ s v (n + m) := by
  obtain ⟨e, he⟩ := first
  obtain ⟨f, hf⟩ := second
  exact ⟨e.append f, by rw [execution_emissions_append, List.length_append, he, hf]⟩

/-- The thresholds seen by a pulse on port `p`. The main thresholds and
the MARK and SILENT levels are nominal. Port `p` enters ERROR at `upper`
and leaves it at `lower`. The other ports keep any ordered ERROR levels,
so one cell can satisfy this for several ports. -/
structure PortConfig (θ : Fin 1 → Parameters) (p : Port) (upper lower level : ℝ) : Prop where
  fire : (θ 0).thresholds.fire = level
  fastEnd : (θ 0).thresholds.fastEnd = 1 / 4
  reopen : (θ 0).thresholds.reopen = 1 / 10
  mark : ∀ q, (θ 0).thresholds.mark q = 1
  silent : ∀ q, (θ 0).thresholds.silent q = 4 / 5
  error : (θ 0).thresholds.error p = upper
  auxReady : (θ 0).thresholds.auxReady p = lower
  ordered : ∀ q, 0 < (θ 0).thresholds.auxReady q ∧
    (θ 0).thresholds.auxReady q ≤ (θ 0).thresholds.error q ∧ (θ 0).thresholds.error q < 1

/-- The single-port configuration of the earlier modules is an instance. -/
theorem PortConfig.of_training {θ : Fin 1 → Parameters} {p upper lower level}
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (bounds : 0 < lower ∧ lower ≤ upper ∧ upper < 1) : PortConfig θ p upper lower level := by
  refine ⟨by rw [config]; rfl, by rw [config]; rfl, by rw [config]; rfl,
    fun q => by rw [config]; rfl, fun q => by rw [config]; rfl,
    by rw [config]; simp [trainingThresholds], by rw [config]; simp [trainingThresholds],
    fun q => ?_⟩
  rw [config]
  by_cases h : q = p
  · subst q
    simp only [trainingThresholds, Function.update_self]
    exact bounds
  · norm_num [trainingThresholds, Function.update_of_ne h]

theorem port_guards {θ : Fin 1 → Parameters} {s : Snapshot 1} {x : Values 1}
    {p upper lower level} (config : PortConfig θ p upper lower level)
    (main : s.main 0 = .ready) (charge : x 0 .q < level)
    (sensor : ∀ q, match s.aux 0 q with
      | .ready => x 0 (.m q) < 1
      | .mark => 4 / 5 < x 0 (.m q)
      | .silent => q = p ∧ upper < x 0 (.m q)
      | .error => q = p ∧ lower < x 0 (.m q)) :
    ThresholdGuards (fun i => (θ i).thresholds) s x := by
  constructor
  · intro i
    rw [Subsingleton.elim i 0]
    simpa [main, config.fire] using charge
  · intro i q
    rw [Subsingleton.elim i 0]
    cases mode : s.aux 0 q
    · simpa [mode, config.mark] using sensor q
    · simpa [mode, config.silent] using sensor q
    · have h : q = p ∧ upper < x 0 (.m q) := by simpa [mode] using sensor q
      obtain ⟨rfl, h⟩ := h
      simpa [config.error] using h
    · have h : q = p ∧ lower < x 0 (.m q) := by simpa [mode] using sensor q
      obtain ⟨rfl, h⟩ := h
      simpa [config.auxReady] using h

theorem port_aux_guards {s : Snapshot 1} {x : Values 1} {p : Port} {upper lower : ℝ}
    (stock : BeforeGuards s x) (others : ∀ q ≠ p, s.aux 0 q = .ready)
    (silent : s.aux 0 p = .silent → upper < x 0 (.m p))
    (error : s.aux 0 p = .error → lower < x 0 (.m p)) :
    ∀ q, match s.aux 0 q with
      | .ready => x 0 (.m q) < 1
      | .mark => 4 / 5 < x 0 (.m q)
      | .silent => q = p ∧ upper < x 0 (.m q)
      | .error => q = p ∧ lower < x 0 (.m q) := by
  intro q
  have h := stock.2 0 q
  by_cases hq : q = p
  · subst q
    cases mode : s.aux 0 p <;> simp_all
  · simpa [others q hq] using h

theorem runs_mark_silent {θ : Fin 1 → Parameters} {s : Snapshot 1} {p upper lower level}
    {f : FirstInputMark θ s 0 p} (g : FirstInputSilent f)
    (config : PortConfig θ p upper lower level)
    (first : ∀ t ∈ Ico s.time (s.time + f.latency), f.flow.path t 0 .q < level)
    (second : ∀ t ∈ Ico f.final.time g.final.time, g.flow.path t 0 .q < level) :
    Runs θ s g.final 0 := by
  let f₁ : ParameterFlow θ s (readyInputEnd θ s 0 p (s.time + f.latency)) := {
    toFlowDynamics := f.flow.toFlowDynamics
    guards := fun t ht => port_guards config (f.main_ready 0) (first t ht)
      (port_aux_guards (f.flow.guards t ht) (fun q _ => f.aux_ready 0 q)
        (by rw [f.aux_ready]; simp) (by rw [f.aux_ready]; simp)) }
  have mode : f.final.aux 0 p = .mark := by simp [FirstInputMark.final, setAux]
  have others : ∀ q ≠ p, f.final.aux 0 q = .ready := fun q hq => by
    simp [FirstInputMark.final, setAux, readyInputEnd, hq, f.aux_ready]
  let f₂ : ParameterFlow θ f.final f.silentBefore := {
    toFlowDynamics := g.flow.toFlowDynamics
    guards := fun t ht => port_guards config (f.main_ready 0) (second t ht)
      (port_aux_guards (g.flow.guards t ht) others (by rw [mode]; simp) (by rw [mode]; simp)) }
  let mark : ParameterJump θ (fun _ _ => [])
      (readyInputEnd θ s 0 p (s.time + f.latency)) f.final :=
    .mark _ 0 p (f.aux_ready 0 p) (by rw [config.mark]; exact f.sensor_threshold)
  let silent : ParameterJump θ (fun _ _ => []) f.silentBefore g.final :=
    .silent _ 0 p mode (by rw [config.silent]; exact g.threshold)
  exact (Runs.flow f₁).append ((Runs.jump mark rfl).append
    ((Runs.flow f₂).append (Runs.jump silent rfl)))

noncomputable def portSilentLeg {θ s p origin upper level stop}
    (leg : TrainingSilentLeg θ s p origin upper level stop) {lower}
    (config : PortConfig θ p upper lower level) :
    ParameterFlow θ s (readyProtectedEnd θ s 0 p .silent origin stop) where
  positive := leg.positive
  path := readyProtectedValues θ s 0 p .silent origin
  initial := readyProtectedValues_initial _ _ _ _ _
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := leg.continuous
  integrable := leg.integrable
  integral_eq := leg.integral
  mark_integrable := by intro i q; simp [markAct, leg.main]
  guards := by
    intro t ht
    apply port_guards config (leg.main 0) (leg.main_guard t ht)
    intro q
    by_cases hq : q = p
    · subst q
      simpa [leg.mode] using leg.sensor_guard t ht
    · simpa [leg.other_modes q hq] using leg.other_guard t ht q hq
  raw_support := by
    intro i q o h
    by_cases address : i = 0 ∧ q = p
    · obtain ⟨rfl, rfl⟩ := address
      exact leg.raw_support o (leg.raw.symm.trans h)
    · rw [leg.other_raw i q (by tauto)] at h
      cases h
  pending_urgent := leg.pending

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
    (charge : ∀ t ∈ Ico s.time stop,
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
    charge t ht
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
      have h := charge s.time ⟨le_rfl, positive⟩
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
  run : Runs θ silent.final (setAux before 0 p .error) 0
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
    (box : @PhysicalBox 1 θ ε) (config : PortConfig θ p upper lower level)
    (physical : PhysicalInvariant θ s) (threshold : 19 / 20 ≤ level)
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
    (fun t ht => by rw [rawCharge t]; exact margin t ⟨gAfter.trans ht.1, ht.2.le⟩)
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
    run := (Runs.flow (portSilentLeg rawLeg config)).append
      ((Runs.jump (.rawEnd edge 0 p s.time edgeRaw rfl) rfl).append
        ((Runs.flow (portSilentLeg tail config)).append
          (Runs.jump (.error boundary 0 p g.aux_silent (by rw [config.error]; exact contact))
            rfl)))
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

/-- A cell at rest between two training pulses. Gains, rest charges and
the energy reserve are free within their bands. -/
structure RestState (θ : Fin 1 → Parameters) (s : Snapshot 1) : Prop where
  main : s.main 0 = .ready
  aux : ∀ q, s.aux 0 q = .ready
  raw : ∀ q, s.raw 0 q = none
  charge : 1 / 10 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 1 / 10 + 1 / 10000
  sensors : ∀ q, RestBand (s.x 0 (.m q))
  recovery : 0 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 11 / 10
  energy : 50 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100
  caps : ∀ q, s.x 0 (.z q) ≤ Real.log ((θ 0).cap q)

theorem exp_neg_long_wait : Real.exp (-(19 / 2 : ℝ)) ≤ 1 / 9500 := by
  have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 19 / 2 by norm_num) 17
  norm_num [Finset.sum_range_succ] at series
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num)
    (show (9500 : ℝ) ≤ Real.exp (19 / 2) by linarith)

/-- The quiet dynamics of a READY cell without input. No threshold is
attached: the guards are checked by the caller at the realized levels. -/
noncomputable def quietDynamics {θ : Fin 1 → Parameters} (s : Snapshot 1) {T : ℝ}
    (ht : s.time < T) (hm : ∀ i, s.main i = .ready) (ha : ∀ i p, s.aux i p = .ready)
    (hn : ∀ i p, s.raw i p = none) (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    FlowDynamics θ s (quietAt s T) where
  positive := ht
  path := quietValues s
  initial := quietValues_initial s
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by
    intro i c
    exact (continuous_iff_continuousAt.mpr (fun t =>
      (quietValues_derivative (θ := θ) s hm ha hn t i c).continuousAt)).continuousOn
  integrable := by
    intro i c
    have hc : Continuous (fun t => field θ s (quietValues s t) t i c) := by
      cases c <;> simp [field, work, drive, current, errorAct, markAct, hm, ha, hn,
        quietValues, relax] <;> fun_prop
    exact hc.intervalIntegrable _ _
  mark_integrable := by intro i p; simp [markAct, ha]
  integral_eq := by
    intro t ht i c
    have hc : Continuous (fun t => field θ s (quietValues s t) t i c) := by
      cases c <;> simp [field, work, drive, current, errorAct, markAct, hm, ha, hn,
        quietValues, relax] <;> fun_prop
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => quietValues_derivative (θ := θ) s hm ha hn v i c)
      (hc.intervalIntegrable s.time t)
    rw [quietValues_initial] at he
    linarith
  raw_support := by intro i p origin ho; simp [hn] at ho
  pending_urgent := hp

/-- The write of a silent training pulse and the return to rest. The cell
enters ERROR with no input current. Its gain moves by eight times the
distance between the two realized thresholds, whatever its ERROR rate. -/
theorem silent_write_exists {θ ε e p upper lower level rest}
    (box : @PhysicalBox 1 θ ε)
    (config : PortConfig θ p upper lower level)
    (bounds : 1 / 200 ≤ lower ∧ lower < upper ∧ upper ≤ 2 / 25)
    (room : Real.exp (e.x 0 (.z p) + 8 * (upper - lower)) ≤ 7 / 2)
    (caps : ∀ q, e.x 0 (.z q) ≤ Real.log ((θ 0).cap q))
    (recovery : 0 ≤ e.x 0 .b ∧ e.x 0 .b ≤ 11 / 10)
    (energy : 50 ≤ e.x 0 .energy ∧ e.x 0 .energy ≤ 100)
    (main : e.main 0 = .ready)
    (charge : 1 / 10 ≤ e.x 0 .q ∧ e.x 0 .q < level) (fire : level ≤ 21 / 20)
    (aux : e.aux 0 p = .error) (sensor : e.x 0 (.m p) = upper)
    (other : ∀ q, q ≠ p → e.aux 0 q = .ready ∧ RestBand (e.x 0 (.m q)))
    (raw : ∀ q, e.raw 0 q = none) (wait : e.time + 20 ≤ rest)
    (pending : ∀ d ∈ e.pending, rest ≤ d.due) :
    ∃ u, Runs θ e u 0 ∧ RestState θ u ∧ u.time = rest ∧
      u.pending = e.pending ∧ u.x 0 (.z p) = e.x 0 (.z p) + 8 * (upper - lower) ∧
      (∀ q ≠ p, u.x 0 (.z q) = e.x 0 (.z q)) ∧ u.x 0 .b = e.x 0 .b := by
  let r := (θ 0).le p
  let stop := e.time + Real.log (upper / lower) / r
  let path := errorTailValues θ e 0 p none
  let learned := e.x 0 (.z p) + 8 * (upper - lower)
  have rpos : 0 < r := (box.rates_positive 0 p).2.2
  obtain ⟨lowerFloor, above, upperBound⟩ := bounds
  have lowerPos : 0 < lower := by linarith
  have upperPos : 0 < upper := by linarith
  have ratio : 1 < upper / lower := (lt_div_iff₀ lowerPos).2 (by linarith)
  have duration : e.time < stop := by
    dsimp [stop]
    exact lt_add_of_pos_right _ (div_pos (Real.log_pos ratio) rpos)
  have durationUpper : stop < e.time + 3 / 8 := by
    have param := ((box.2 0 p).2.2.2.1).1
    change a / (3 / 20) * (1 - ε) ≤ r at param
    have rlower : (8 : ℝ) ≤ r := by
      have bound := mul_le_mul (show (4 / 3 : ℝ) / (3 / 20) ≤ a / (3 / 20) by
        dsimp [a]; linarith [KernelR.log_four_bounds.1]) (show (9 / 10 : ℝ) ≤ 1 - ε by
          linarith [box.epsilon_bounds.2]) (by norm_num) (by linarith [a_coarse_bounds.1])
      norm_num at bound
      exact bound.trans param
    have rat : upper / lower ≤ 16 := (div_le_iff₀ lowerPos).2 (by linarith)
    have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 8
    norm_num [Finset.sum_range_succ] at series
    have expBound : (16 : ℝ) < Real.exp 3 := by linarith
    have logBound := (Real.log_lt_iff_lt_exp (zero_lt_one.trans ratio)).2 (rat.trans_lt expBound)
    dsimp [stop]
    have h := (div_lt_iff₀ rpos).2 (show Real.log (upper / lower) < (3 / 8) * r by linarith)
    linarith
  have endpoint : errorTailSensor θ e 0 p stop = lower := by
    rw [errorTailSensor, sensor]
    change upper * Real.exp (-r * (stop - e.time)) = lower
    have hx : -r * (stop - e.time) = -Real.log (upper / lower) := by
      dsimp [stop]
      field_simp
      ring
    rw [hx, Real.exp_neg, Real.exp_log (div_pos upperPos lowerPos)]
    field_simp
  have sensorAbove (t : ℝ) (ht : t < stop) : lower < errorTailSensor θ e 0 p t := by
    rw [← endpoint]
    simp only [errorTailSensor, sensor]
    exact mul_lt_mul_of_pos_left
      (Real.exp_lt_exp.mpr (by nlinarith [mul_pos rpos (sub_pos.mpr ht)])) upperPos
  have sensorFloor (t : ℝ) (ht : t ≤ stop) : lower ≤ errorTailSensor θ e 0 p t :=
    ht.eq_or_lt.elim (fun h => h ▸ endpoint.ge) (fun h => (sensorAbove t h).le)
  have learnedRoom : Real.exp learned ≤ 7 / 2 := room
  have learnedCap : learned < Real.log ((θ 0).cap p) := by
    have h := (box.2 0 p).1.1
    change 4 * (1 - ε) ≤ (θ 0).cap p at h
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (box.cap_positive 0 p)]
    linarith [box.epsilon_bounds.2]
  have reserve (t : ℝ) (ht : e.time ≤ t) :
      50 ≤ errorTailEnergy θ e 0 p none t ∧ errorTailEnergy θ e 0 p none t ≤ 100 := by
    apply reserve_of_derivative ht (errorTailWork_continuous e 0 p none)
      (errorTailEnergy_derivative e 0 p none)
    · simpa [errorTailEnergy, linearConvolution_initial, relax_initial] using energy
    · intro v hv
      have hm : 0 ≤ errorTailSensor θ e 0 p v :=
        mul_nonneg (by rw [sensor]; exact upperPos.le) (Real.exp_pos _).le
      have hcap : errorTailSensor θ e 0 p v ≤ 21 / 200 :=
        decay_upper (by rw [sensor]; linarith) (by norm_num) rpos.le (sub_nonneg.mpr hv.1)
      have product := mul_le_mul (box.coarse_upper 0 p).2.2.2.1 hcap hm (by norm_num)
      simp only [errorTailWork, errorTailDrive, rawInputScale, mul_zero, zero_mul, add_zero]
      exact ⟨mul_nonneg (mul_nonneg (by norm_num) rpos.le) hm, by nlinarith⟩
  have gates (t : ℝ) (ht : t ∈ Icc e.time stop) :
      0 < errorTailEnergy θ e 0 p none t ∧ errorTailGain θ e 0 p t < Real.log ((θ 0).cap p) := by
    refine ⟨by linarith [(reserve t ht.1).1], lt_of_le_of_lt ?_ learnedCap⟩
    dsimp [errorTailGain, learned]
    rw [sensor]
    linarith [sensorFloor t ht.2]
  have fieldEq (t : ℝ) (ht : t ∈ Icc e.time stop) (i : Fin 1) (c : Coord) :
      field θ e (path t) t i c = errorTailRhs θ e 0 p none t i c := by
    rw [Subsingleton.elim i 0]
    exact error_path_field main aux (fun q h => (other q h).1) (fun q _ => raw q)
      (by simp [current, raw, rawInputScale]) (gates t ht).1 (gates t ht).2 c
  have qPath (t : ℝ) : path t 0 .q = relax (1 / 2) (1 / 10) (e.x 0 .q) e.time t := by
    simp [path, errorTailValues, errorTailMain, errorTailDrive, rawInputScale, linearConvolution]
  have otherPath (t : ℝ) (q : Port) (h : q ≠ p) :
      path t 0 (.m q) = relax (1 / 2) (1 / 40) (e.x 0 (.m q)) e.time t := by
    simp [path, errorTailValues, h]
  have chargeOut : path stop 0 (.m p) = lower := by
    simpa [path, errorTailValues] using endpoint
  have gainOut : path stop 0 (.z p) = learned := by
    simp [path, learned, errorTailValues, errorTailGain, endpoint, sensor]
  have qBand (t : ℝ) (ht : e.time ≤ t) : path t 0 .q ∈ Icc (1 / 10) (e.x 0 .q) := by
    rw [qPath]
    exact relax_mem_band (by norm_num) ht ⟨charge.1, le_rfl⟩ ⟨le_rfl, charge.1⟩
  let boundary : Snapshot 1 := {e with time := stop, x := path stop}
  let flow : ParameterFlow θ e boundary := {
    positive := duration
    path := path
    initial := errorTailValues_initial (θ := θ) e 0 p none
    final := rfl
    main_fixed := rfl
    aux_fixed := rfl
    raw_fixed := rfl
    queue_fixed := rfl
    continuous := fun i c => (continuous_iff_continuousAt.mpr fun t =>
      (errorTailValues_derivative (θ := θ) e 0 p none t i c).continuousAt).continuousOn
    integrable := by
      intro i c
      change IntervalIntegrable _ volume e.time stop
      apply ((errorTailRhs_continuous (θ := θ) e 0 p none i c).intervalIntegrable _ _).congr_uIoo
      intro t ht
      rw [uIoo_of_lt duration] at ht
      exact (fieldEq t ⟨ht.1.le, ht.2.le⟩ i c).symm
    mark_integrable := by intro i q; rw [Subsingleton.elim i 0]; simp [markAct, main]
    integral_eq := by
      intro t ht i c
      change t ∈ Icc e.time stop at ht
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun v _ => errorTailValues_derivative (θ := θ) e 0 p none v i c)
        ((errorTailRhs_continuous (θ := θ) e 0 p none i c).intervalIntegrable e.time t)
      rw [errorTailValues_initial] at h
      have eq : (∫ v in e.time..t, field θ e (path v) v i c) =
          ∫ v in e.time..t, errorTailRhs θ e 0 p none v i c := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.1
        intro v hv
        exact fieldEq v ⟨hv.1.le, hv.2.le.trans ht.2⟩ i c
      rw [eq, h]
      change path t i c = _
      ring
    guards := by
      intro t ht
      have ht₁ : e.time ≤ t := ht.1
      have ht₂ : t < stop := ht.2
      apply port_guards config main ((qBand t ht₁).2.trans_lt charge.2)
      intro q
      by_cases eq : q = p
      · subst q
        have h : lower < path t 0 (.m p) := by
          simpa [path, errorTailValues] using sensorAbove t ht₂
        simpa [aux] using h
      · have h : path t 0 (.m q) < 1 := by
          rw [otherPath t q eq]
          exact lt_of_le_of_lt (relax_restBand ht₁ (other q eq).2).2 (by norm_num)
        simpa [(other q eq).1] using h
    raw_support := by intro i q o h; rw [Subsingleton.elim i 0, raw] at h; cases h
    pending_urgent := fun d hd => by
      have h := pending d hd
      change stop ≤ d.due
      linarith
  }
  let reopened := setAux boundary 0 p .ready
  let reopen : ParameterJump θ (fun _ _ => []) boundary reopened :=
    .auxReady _ 0 p aux (by rw [config.auxReady]; exact chargeOut)
  have ready (i : Fin 1) : reopened.main i = .ready := by
    rw [Subsingleton.elim i 0]
    exact main
  have sensors (i : Fin 1) (q : Port) : reopened.aux i q = .ready := by
    rw [Subsingleton.elim i 0]
    by_cases h : q = p
    · subst q; simp [reopened, setAux]
    · simp [reopened, boundary, setAux, h, (other q h).1]
  have noneRaw (i : Fin 1) (q : Port) : reopened.raw i q = none := by
    rw [Subsingleton.elim i 0]
    exact raw q
  have stopRest : stop < rest := by linarith
  let u := quietAt reopened rest
  have stopSensor (q : Port) : path stop 0 (.m q) < 1 := by
    by_cases h : q = p
    · subst q; rw [chargeOut]; linarith
    · rw [otherPath stop q h]
      exact lt_of_le_of_lt (relax_restBand duration.le (other q h).2).2 (by norm_num)
  let waitFlow : ParameterFlow θ reopened u := {
    toFlowDynamics := quietDynamics reopened stopRest ready sensors noneRaw
      (fun d hd => pending d hd)
    guards := by
      intro t ht
      have ht₁ : stop ≤ t := ht.1
      apply port_guards config (ready 0)
      · change relax (1 / 2) (1 / 10) (path stop 0 .q) stop t < level
        have h := relax_mem_band (rate := 1 / 2) (target := 1 / 10) (by norm_num) ht₁
          (qBand stop duration.le) ⟨le_rfl, charge.1⟩
        exact h.2.trans_lt charge.2
      · intro q
        have h : relax (1 / 2) (1 / 40) (path stop 0 (.m q)) stop t < 1 :=
          relax_lt_one ht₁ (stopSensor q)
        simp only [sensors 0 q]
        exact h
  }
  have longWait : Real.exp (-(1 / 2) * (rest - stop)) ≤ 1 / 9500 :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_neg_long_wait
  have pos := Real.exp_pos (-(1 / 2) * (rest - stop))
  have uCharge : 1 / 10 ≤ u.x 0 .q ∧ u.x 0 .q ≤ 1 / 10 + 1 / 10000 := by
    have c := qBand stop duration.le
    change 1 / 10 ≤ relax (1 / 2) (1 / 10) (path stop 0 .q) stop rest ∧
      relax (1 / 2) (1 / 10) (path stop 0 .q) stop rest ≤ _
    have h₁ := mul_nonneg (sub_nonneg.mpr c.1) pos.le
    have h₂ := mul_le_mul (show path stop 0 .q - 1 / 10 ≤ 19 / 20 by linarith [c.2, charge.2])
      longWait pos.le (by norm_num)
    constructor <;> dsimp only [relax] <;> linarith
  have uSensors (q : Port) : RestBand (u.x 0 (.m q)) := by
    change RestBand (relax (1 / 2) (1 / 40) (path stop 0 (.m q)) stop rest)
    by_cases h : q = p
    · subst q
      rw [chargeOut]
      have hi := mul_le_mul (show lower - 1 / 40 ≤ 11 / 200 by linarith) longWait pos.le (by norm_num)
      have lo := mul_le_mul (show 1 / 40 - lower ≤ 11 / 200 by linarith) longWait pos.le (by norm_num)
      refine ⟨?_, ?_⟩ <;> dsimp only [relax] <;> linarith
    · rw [otherPath stop q h]
      exact relax_restBand stopRest.le (relax_restBand duration.le (other q h).2)
  have uEnergy : 50 ≤ u.x 0 .energy ∧ u.x 0 .energy ≤ 100 := by
    change relax 10 100 (path stop 0 .energy) stop rest ∈ Icc (50 : ℝ) 100
    have start : path stop 0 .energy ∈ Icc (50 : ℝ) 100 := by
      simpa [path, errorTailValues] using reserve stop duration.le
    exact relax_mem_band (by norm_num) stopRest.le start ⟨by norm_num, le_rfl⟩
  have otherGain (q : Port) (h : q ≠ p) : path stop 0 (.z q) = e.x 0 (.z q) := by
    simp [path, errorTailValues, h]
  have uCaps (q : Port) : u.x 0 (.z q) ≤ Real.log ((θ 0).cap q) := by
    change path stop 0 (.z q) ≤ _
    by_cases h : q = p
    · subst q; rw [gainOut]; exact learnedCap.le
    · rw [otherGain q h]; exact caps q
  exact ⟨u, (Runs.flow flow).append ((Runs.jump reopen rfl).append (Runs.flow waitFlow)),
    ⟨ready 0, sensors 0, noneRaw 0, uCharge, uSensors, recovery, uEnergy, uCaps⟩,
    rfl, rfl, gainOut, otherGain, rfl⟩

/-- One silent training step. A pulse that keeps the main charge below
the realized FIRE level takes a rested cell back to rest with the gain of
the pulsed port moved by one dose. Nothing else is assumed of the gain. -/
theorem silent_step_exists {θ ε s p upper lower level rest} {later : List (Delivery 1)}
    (box : @PhysicalBox 1 θ ε)
    (config : PortConfig θ p upper lower level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25) (exit : 1 / 200 ≤ lower ∧ lower < upper)
    (state : RestState θ s)
    (queue : s.pending = (⟨0, p, s.time⟩ : Delivery 1) :: later)
    (wait : s.time + 22 ≤ rest) (laterDue : ∀ d ∈ later, rest ≤ d.due)
    (silent : ∀ t ∈ Icc s.time (s.time + 1),
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t < level)
    (room : Real.exp (s.x 0 (.z p) + 8 * (upper - lower)) ≤ 7 / 2) :
    ∃ u, Runs θ s u 0 ∧ RestState θ u ∧ u.time = rest ∧
      u.pending = later ∧ u.x 0 (.z p) = s.x 0 (.z p) + 8 * (upper - lower) ∧
      (∀ q ≠ p, u.x 0 (.z q) = s.x 0 (.z q)) ∧ u.x 0 .b = s.x 0 .b := by
  let d : Delivery 1 := ⟨0, p, s.time⟩
  let admitted : Snapshot 1 := { (setRaw s d.cell d.port (some s.time)) with pending := [] ++ later }
  let arrive : ParameterJump θ (fun _ _ => []) s admitted :=
    .arrive s d [] later queue rfl (state.raw p)
  have gainBound : Real.exp (s.x 0 (.z p)) ≤ 22 / 5 := by
    have cap := (box.2 0 p).1.2
    change (θ 0).cap p ≤ 4 * (1 + ε) at cap
    have h := Real.exp_le_exp.mpr (state.caps p)
    rw [Real.exp_log (box.cap_positive 0 p)] at h
    linarith [box.epsilon_bounds.2]
  have start : ∀ t, admitted.time ≤ t → t ≤ admitted.time + 1 / 10 →
      readyPulse (admitted.x 0 .q) (Real.exp (admitted.x 0 (.z p))) admitted.time t < 1 := by
    intro t h₀ h₁
    change s.time ≤ t at h₀
    change t ≤ s.time + 1 / 10 at h₁
    change readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t < 1
    have resp := response_upper (sub_nonneg.mpr h₀)
    have respPos := response_nonnegative (sub_nonneg.mpr h₀)
    have small : response (t - s.time) ≤ 7 / 50 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr a_coarse_bounds.2.le) (sub_nonneg.mpr h₀),
        a_coarse_bounds.1]
    have drive := mul_le_mul gainBound small respPos (by norm_num)
    have decay := decay_upper (show s.x 0 .q - 1 / 10 ≤ 1 / 10000 by linarith [state.charge.2])
      (by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (sub_nonneg.mpr h₀)
    dsimp only [readyPulse]
    linarith
  have physical : PhysicalInvariant θ admitted := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [Subsingleton.elim i 0]
      refine ⟨state.recovery.1, state.charge.2.trans (by norm_num), fun q => ?_⟩
      rw [show admitted.aux 0 q = .ready from state.aux q]
      exact le_of_lt (lt_of_le_of_lt (state.sensors q).2 (by norm_num [auxUpper]))
    · intro i q; rw [Subsingleton.elim i 0]; exact state.caps q
    · intro i; rw [Subsingleton.elim i 0]; exact state.recovery.2
    · intro i; rw [Subsingleton.elim i 0]; exact state.energy
  obtain ⟨run⟩ := silent_entry_exists (s := admitted) (p := p) (upper := upper) (lower := lower)
    (level := level) box config physical fire.1 entry
    (fun i => by rw [Subsingleton.elim i 0]; exact state.main)
    (fun i q => by rw [Subsingleton.elim i 0]; exact state.aux q)
    (by simp [admitted, setRaw, d])
    (fun i q h => by
      have hi : i = 0 := Subsingleton.elim _ _
      have hq := h.resolve_left (not_not_intro hi)
      subst hi
      exact (raw_update_other s 0 p (some s.time) 0 q (Or.inr hq)).trans (state.raw q))
    state.sensors gainBound start silent
    (fun v hv => by
      have h := laterDue v (by simpa [admitted] using hv)
      change s.time + 8 / 5 ≤ v.due
      linarith)
  let e := setAux run.before 0 p .error
  have gains (q : Port) : e.x 0 (.z q) = s.x 0 (.z q) := run.gains q
  let P := readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time (s.time + 1)
  have pulseHigh : P < level := silent (s.time + 1) ⟨by linarith, le_rfl⟩
  have pulseLow : 1 / 10 ≤ P := by
    have h₁ := mul_nonneg (sub_nonneg.mpr state.charge.1)
      (Real.exp_pos (-(1 / 2) * (s.time + 1 - s.time))).le
    have h₂ := mul_nonneg (Real.exp_pos (s.x 0 (.z p))).le
      (response_nonnegative (show (0 : ℝ) ≤ s.time + 1 - s.time by linarith))
    dsimp only [P, readyPulse]
    linarith
  have eCharge : 1 / 10 ≤ e.x 0 .q ∧ e.x 0 .q < level := by
    have h := relax_mem_band (rate := 1 / 2) (target := 1 / 10) (t := run.before.time)
      (start := s.time + 1) (by norm_num) run.after_pulse.le ⟨pulseLow, le_rfl⟩ ⟨le_rfl, pulseLow⟩
    rw [show e.x 0 .q = _ from run.charge]
    exact ⟨h.1, h.2.trans_lt pulseHigh⟩
  obtain ⟨u, write, rested, date, queueOut, learned, others, recovery⟩ :=
    silent_write_exists (e := e) (rest := rest) box config ⟨exit.1, exit.2, entry.2⟩
      (by rw [gains p]; exact room) (fun q => by rw [gains q]; exact state.caps q)
      (by rw [show e.x 0 .b = s.x 0 .b from run.recovery]; exact state.recovery)
      run.energy run.main eCharge fire.2 (by simp [e, setAux]) run.sensor
      (fun q hq => ⟨by simpa [e, setAux, hq] using run.other_modes q hq, run.other_sensors q hq⟩)
      run.raw
      (by
        have h : run.before.time < s.time + 8 / 5 := run.deadline
        change run.before.time + 20 ≤ rest
        linarith)
      (fun v hv => laterDue v (by
        have h : v ∈ run.before.pending := hv
        rw [run.queue] at h
        simpa [admitted] using h))
  refine ⟨u, (Runs.jump arrive rfl).append
    ((runs_mark_silent run.silent config run.pre_mark run.pre_silent).append
      (run.run.append write)), rested, date, ?_, ?_, ?_, ?_⟩
  · rw [queueOut]
    change run.before.pending = later
    rw [run.queue]
    rfl
  · rw [learned, gains p]
  · intro q hq
    rw [others q hq, gains q]
  · rw [recovery]
    exact run.recovery

end RecursiveLearning.Native
