import Thresholds.ParameterTraining
import KernelR.HybridFrozen

/-! After the read FIRE, the main cell remains protected through the
observation horizon. The FAST, sensor and raw clocks are independent
and can hit at the same date. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

private noncomputable def protectedParameterFlow {n θ s} (h : @FrozenModes n s) {T : ℝ}
    (hT : s.time < T)
    (hguard : ∀ t ∈ Ico s.time T, ThresholdGuards (fun i => (θ i).thresholds) s (frozenValues θ s t))
    (hraw : ∀ i p origin, s.raw i p = some origin → origin ≤ s.time ∧ T ≤ origin+1)
    (hpending : ∀ d ∈ s.pending, T ≤ d.due) : ParameterFlow θ s (frozenAt θ s T) := by
  have heq (t : ℝ) (ht : t ∈ Ico s.time T) (i : Fin n) (c : Coord) :
      extendedField θ s (frozenValues θ s t) t i c = field θ s (frozenValues θ s t) t i c := by
    apply extendedField_eq_field h
    intro j p
    cases hr : s.raw j p with
    | none => simp [extendedCurrent, current, hr]
    | some origin =>
      have hb := hraw j p origin hr
      have hs : origin ≤ t ∧ t < origin+1 := ⟨hb.1.trans ht.1, ht.2.trans_le hb.2⟩
      simp [extendedCurrent, current, pulse, hr, hs]
  refine {
    positive := hT
    path := frozenValues θ s
    initial := frozenValues_initial θ s
    final := rfl
    main_fixed := rfl
    aux_fixed := rfl
    raw_fixed := rfl
    queue_fixed := rfl
    continuous := fun i c => (frozenValues_continuous θ s i c).continuousOn
    integrable := ?_
    mark_integrable := ?_
    integral_eq := ?_
    guards := hguard
    raw_support := hraw
    pending_urgent := hpending }
  · intro i c
    apply (extendedField_continuous θ s i c).intervalIntegrable s.time T |>.congr_uIoo
    intro t ht
    rw [uIoo_of_le hT.le] at ht
    exact heq t ⟨ht.1.le, ht.2⟩ i c
  · intro i p
    change IntervalIntegrable (fun t => markAct θ s (frozenValues θ s t) i p) volume s.time T
    simpa only [h.mark_zero] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume s.time T)
  · intro t ht i c
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => frozenValues_derivative θ s i c v)
      ((extendedField_continuous θ s i c).intervalIntegrable s.time t)
    have hc : (∫ v in s.time..t, extendedField θ s (frozenValues θ s v) v i c) =
        ∫ v in s.time..t, field θ s (frozenValues θ s v) v i c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact heq v ⟨hv.1.le, hv.2.trans_le ht.2⟩ i c
    rw [frozenValues_initial, hc] at hftc
    linarith

private inductive SensorTail
  | silent | error | ready
  deriving DecidableEq

private def SensorTail.mode : SensorTail → AuxMode
  | .silent => .silent
  | .error => .error
  | .ready => .ready

private def SensorTail.count : SensorTail → ℕ
  | .silent => 2
  | .error => 1
  | .ready => 0

private structure TailCalendar (θ : Fin 1 → Parameters) (p : Port) where
  origin : ℝ
  fastDate : ℝ
  errorDate : ℝ
  readyDate : ℝ
  horizon : ℝ
  recovery : ℝ
  fastQ : ℝ → ℝ
  slowQ : ℝ → ℝ
  silentM : ℝ → ℝ
  errorM : ℝ → ℝ
  fastRestart : ∀ x t, fastQ x * Real.exp (-a * (t - x)) = fastQ t
  slowRestart : ∀ x t, slowQ x * Real.exp (-recovery * (t - x)) = slowQ t
  silentRestart : ∀ x t, silentM x * Real.exp (-(θ 0).ls p * (t - x)) = silentM t
  errorRestart : ∀ x t, errorM x * Real.exp (-(θ 0).le p * (t - x)) = errorM t
  fastBefore : ∀ t < fastDate, (θ 0).thresholds.fastEnd < fastQ t
  slowBefore : ∀ t ≤ horizon, (θ 0).thresholds.reopen < slowQ t
  silentBefore : ∀ t < errorDate, (θ 0).thresholds.error p < silentM t
  errorBefore : ∀ t < readyDate, (θ 0).thresholds.auxReady p < errorM t
  fastHit : fastQ fastDate = (θ 0).thresholds.fastEnd
  slowStart : slowQ fastDate = (θ 0).thresholds.fastEnd
  silentHit : silentM errorDate = (θ 0).thresholds.error p
  errorStart : errorM errorDate = (θ 0).thresholds.error p
  errorHit : errorM readyDate = (θ 0).thresholds.auxReady p
  exitBelow : (θ 0).thresholds.auxReady p < 1
  markNominal : ∀ q, (θ 0).thresholds.mark q = 1
  rawBeforeHorizon : origin + 1 < horizon
  fastBeforeHorizon : fastDate < horizon
  errorBeforeReady : errorDate < readyDate
  readyBeforeHorizon : readyDate < horizon
  rawBeforeReady : origin + 1 < readyDate

private def TailCalendar.mainDate {θ p} (c : TailCalendar θ p) (fast : Bool) : ℝ :=
  if fast then c.fastDate else c.horizon

private def TailCalendar.rawDate {θ p} (c : TailCalendar θ p) (live : Bool) : ℝ :=
  if live then c.origin + 1 else c.horizon

private def TailCalendar.sensorDate {θ p} (c : TailCalendar θ p) : SensorTail → ℝ
  | .silent => c.errorDate
  | .error => c.readyDate
  | .ready => c.horizon

private def TailCalendar.next {θ p} (c : TailCalendar θ p) (live fast : Bool) (phase : SensorTail) : ℝ :=
  min (c.rawDate live) (min (c.mainDate fast) (c.sensorDate phase))

private def tailCount (live fast : Bool) (phase : SensorTail) : ℕ :=
  live.toNat + fast.toNat + phase.count

private structure TailAt {θ : Fin 1 → Parameters} {p : Port} (c : TailCalendar θ p)
    (live fast : Bool) (phase : SensorTail) (s : Snapshot 1) : Prop where
  date : s.time ≤ c.horizon
  rawClock : live = true → c.origin ≤ s.time ∧ s.time ≤ c.origin + 1
  fastClock : s.time ≤ c.mainDate fast
  sensorClock : s.time ≤ c.sensorDate phase
  main : s.main 0 = if fast then .fast else .slow
  mainValue : s.x 0 .q = if fast then c.fastQ s.time else c.slowQ s.time
  recovery : s.x 0 .b = c.recovery
  mode : s.aux 0 p = phase.mode
  sensorValue : match phase with
    | .silent => s.x 0 (.m p) = c.silentM s.time
    | .error => s.x 0 (.m p) = c.errorM s.time
    | .ready => s.x 0 (.m p) < 1
  raw : s.raw 0 p = if live then some c.origin else none
  passive : ∀ q ≠ p, s.aux 0 q = .ready ∧ s.raw 0 q = none ∧ s.x 0 (.m q) < 1
  queue : s.pending = []
  noReadyRaw : phase = .ready → live = false

private theorem TailAt.next_le_horizon {θ p c live fast phase s}
    (h : @TailAt θ p c live fast phase s) : c.next live fast phase ≤ c.horizon := by
  apply (min_le_left _ _).trans
  cases live
  · exact le_rfl
  · exact c.rawBeforeHorizon.le

private theorem TailAt.time_le_next {θ p c live fast phase s}
    (h : @TailAt θ p c live fast phase s) : s.time ≤ c.next live fast phase := by
  apply le_min _ (le_min h.fastClock h.sensorClock)
  cases live
  · exact h.date
  · exact (h.rawClock rfl).2

private theorem TailAt.frozenModes {θ p c live fast phase s} (h : @TailAt θ p c live fast phase s) :
    FrozenModes s := by
  have protectedMain : s.main 0 ≠ .ready := by rw [h.main]; cases fast <;> decide
  constructor
  · intro i q hm
    rw [Subsingleton.elim i 0] at hm
    exact (protectedMain hm).elim
  · intro i q hm
    rw [Subsingleton.elim i 0] at hm ⊢
    by_cases eq : q = p
    · subst q
      rw [h.mode] at hm
      cases phase <;> cases hm
    · rw [(h.passive q eq).1] at hm
      cases hm

private theorem TailAt.frozen_q {θ p c live fast phase s}
    (h : @TailAt θ p c live fast phase s) (t : ℝ) :
    frozenValues θ s t 0 .q = if fast then c.fastQ t else c.slowQ t := by
  cases fast
  · simpa only [frozenValues, frozenBody, frozenMain, h.main, h.mainValue, h.recovery,
      Bool.false_eq_true, ite_false] using c.slowRestart s.time t
  · simpa only [frozenValues, frozenBody, frozenMain, h.main, h.mainValue,
      ite_true] using c.fastRestart s.time t

private theorem protected_sensor_value {θ : Fin 1 → Parameters} {s : Snapshot 1} {p mode}
    (h : s.aux 0 p = mode) (different : mode ≠ .ready) (t : ℝ) :
    frozenValues θ s t 0 (.m p) = s.x 0 (.m p) *
      Real.exp (-auxRate (θ 0) p mode * (t - s.time)) := by
  simp [frozenValues, frozenBody, frozenAux, h, different]

private theorem idle_sensor_value {θ : Fin 1 → Parameters} {s : Snapshot 1} {p}
    (mode : s.aux 0 p = .ready) (raw : s.raw 0 p = none) (t : ℝ) :
    frozenValues θ s t 0 (.m p) = relax (1 / 2) (1 / 40) (s.x 0 (.m p)) s.time t := by
  simp [frozenValues, frozenBody, frozenAux, mode, frozenRawAmplitude, raw, auxPulse, readyPulse, relax]
  ring

private theorem TailAt.frozen_m {θ p c live fast phase s}
    (h : @TailAt θ p c live fast phase s) {t : ℝ} (ht : s.time ≤ t) :
    match phase with
    | .silent => frozenValues θ s t 0 (.m p) = c.silentM t
    | .error => frozenValues θ s t 0 (.m p) = c.errorM t
    | .ready => frozenValues θ s t 0 (.m p) < 1 := by
  cases phase
  · have mode : s.aux 0 p = .silent := h.mode
    rw [protected_sensor_value mode (by decide) t]
    have x : s.x 0 (.m p) = c.silentM s.time := h.sensorValue
    simpa [x, auxRate] using c.silentRestart s.time t
  · have mode : s.aux 0 p = .error := h.mode
    rw [protected_sensor_value mode (by decide) t]
    have x : s.x 0 (.m p) = c.errorM s.time := h.sensorValue
    simpa [x, auxRate] using c.errorRestart s.time t
  · have noRaw : s.raw 0 p = none := by rw [h.raw, h.noReadyRaw rfl]; rfl
    rw [idle_sensor_value h.mode noRaw t]
    exact relax_lt (by norm_num) ht h.sensorValue (by norm_num)

private theorem TailAt.frozen_passive {θ p c live fast phase s}
    (h : @TailAt θ p c live fast phase s) {t : ℝ} (ht : s.time ≤ t)
    (q : Port) (neq : q ≠ p) :
    frozenValues θ s t 0 (.m q) < 1 := by
  obtain ⟨mode, raw, charge⟩ := h.passive q neq
  rw [idle_sensor_value mode raw t]
  exact relax_lt (by norm_num) ht charge (by norm_num)

private theorem TailAt.frozen_guards {θ p c live fast phase s}
    (h : @TailAt θ p c live fast phase s) {t : ℝ}
    (ht : s.time ≤ t) (before : t < c.next live fast phase) :
    ThresholdGuards (fun i => (θ i).thresholds) s (frozenValues θ s t) := by
  constructor
  · intro i
    rw [Subsingleton.elim i 0, h.main, h.frozen_q]
    cases fast
    · exact c.slowBefore t (before.le.trans h.next_le_horizon)
    · exact c.fastBefore t (before.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  · intro i q
    rw [Subsingleton.elim i 0]
    by_cases eq : q = p
    · subst q
      rw [h.mode]
      have value := h.frozen_m ht
      have limit := before.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      cases phase
      · change (θ 0).thresholds.error p < frozenValues θ s t 0 (.m p)
        rw [value]
        exact c.silentBefore t limit
      · change (θ 0).thresholds.auxReady p < frozenValues θ s t 0 (.m p)
        rw [value]
        exact c.errorBefore t limit
      · change frozenValues θ s t 0 (.m p) < (θ 0).thresholds.mark p
        rwa [c.markNominal]
    · rw [(h.passive q eq).1]
      change frozenValues θ s t 0 (.m q) < (θ 0).thresholds.mark q
      rw [c.markNominal]
      exact h.frozen_passive ht q eq

private theorem TailAt.advance {θ p c live fast phase s}
    (h : @TailAt θ p c live fast phase s) {t : ℝ} (ht : s.time ≤ t)
    (limit : t ≤ c.next live fast phase) :
    TailAt c live fast phase (frozenAt θ s t) ∧
    Nonempty (ParameterExecution θ (fun _ _ => []) s (frozenAt θ s t)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨limit.trans h.next_le_horizon, fun on => ⟨(h.rawClock on).1.trans ht,
        limit.trans (min_le_left _ _) |>.trans (by simp [TailCalendar.rawDate, on])⟩,
      limit.trans ((min_le_right _ _).trans (min_le_left _ _)),
      limit.trans ((min_le_right _ _).trans (min_le_right _ _)),
      h.main, h.frozen_q t, h.recovery, h.mode, ?_, h.raw,
      fun q neq => ⟨(h.passive q neq).1, (h.passive q neq).2.1, h.frozen_passive ht q neq⟩,
      h.queue, h.noReadyRaw⟩
    cases phase <;> exact h.frozen_m ht
  · rcases ht.eq_or_lt with same | later
    · subst t
      have eq : frozenAt θ s s.time = s := by simp [frozenAt, frozenValues_initial]
      rw [eq]
      exact ⟨.nil _⟩
    · have rawSupport (i : Fin 1) (q : Port) (o : ℝ) (active : s.raw i q = some o) :
          o ≤ s.time ∧ t ≤ o + 1 := by
        rw [Subsingleton.elim i 0] at active
        by_cases eq : q = p
        · subst q
          rw [h.raw] at active
          cases on : live
          · simp [on] at active
          · have eq := Option.some.inj (by simpa [on] using active : some c.origin = some o)
            subst o
            exact ⟨(h.rawClock on).1, limit.trans (min_le_left _ _) |>.trans
              (by simp [TailCalendar.rawDate, on])⟩
        · rw [(h.passive q eq).2.1] at active
          cases active
      exact ⟨.cons (.flow (protectedParameterFlow h.frozenModes later
        (fun v hv => h.frozen_guards hv.1 (hv.2.trans_le limit)) rawSupport
        (by simp [h.queue]))) (.nil _)⟩


private theorem TailAt.expire {θ p c fast phase s}
    (h : @TailAt θ p c true fast phase s) (due : s.time = c.origin + 1) :
    TailAt c false fast phase (setRaw s 0 p none) ∧
    Nonempty (ParameterJump θ (fun _ _ => []) s (setRaw s 0 p none)) := by
  refine ⟨⟨h.date, by simp, h.fastClock, h.sensorClock, h.main, h.mainValue, h.recovery, h.mode,
    ?_, by simp [setRaw], ?_, h.queue, fun _ => rfl⟩,
    ⟨.rawEnd s 0 p c.origin h.raw due⟩⟩
  · cases phase <;> exact h.sensorValue
  · intro q neq
    obtain ⟨mode, raw, below⟩ := h.passive q neq
    exact ⟨mode, by simpa [setRaw, neq] using raw, below⟩

private theorem TailAt.fastEnd {θ p c live phase s}
    (h : @TailAt θ p c live true phase s) (due : s.time = c.fastDate) :
    TailAt c live false phase (setMain s 0 .slow) ∧
    Nonempty (ParameterJump θ (fun _ _ => []) s (setMain s 0 .slow)) := by
  have contact : s.x 0 .q = (θ 0).thresholds.fastEnd := by
    rw [h.mainValue, due]
    exact c.fastHit
  refine ⟨⟨h.date, h.rawClock, h.date, h.sensorClock, by simp [setMain], ?_,
    h.recovery, h.mode, ?_, h.raw, h.passive, h.queue, h.noReadyRaw⟩,
    ⟨.fastEnd s 0 h.main contact⟩⟩
  · change s.x 0 .q = c.slowQ s.time
    rw [due, c.slowStart]
    exact contact
  · cases phase <;> exact h.sensorValue

private theorem TailAt.error {θ p c live fast s}
    (h : @TailAt θ p c live fast .silent s) (due : s.time = c.errorDate) :
    TailAt c live fast .error (setAux s 0 p .error) ∧
    Nonempty (ParameterJump θ (fun _ _ => []) s (setAux s 0 p .error)) := by
  have contact : s.x 0 (.m p) = (θ 0).thresholds.error p := by
    have value : s.x 0 (.m p) = c.silentM s.time := h.sensorValue
    rw [value, due]
    exact c.silentHit
  refine ⟨⟨h.date, h.rawClock, h.fastClock, ?_, h.main, h.mainValue, h.recovery,
    by simp [setAux, SensorTail.mode], ?_, h.raw, ?_, h.queue, by intro impossible; cases impossible⟩,
    ⟨.error s 0 p h.mode contact⟩⟩
  · change s.time ≤ c.readyDate
    rw [due]
    exact c.errorBeforeReady.le
  · change s.x 0 (.m p) = c.errorM s.time
    rw [due, c.errorStart]
    exact contact
  · intro q neq
    obtain ⟨mode, raw, below⟩ := h.passive q neq
    exact ⟨by simpa [setAux, neq] using mode, raw, below⟩

private theorem TailAt.auxReady {θ p c live fast s}
    (h : @TailAt θ p c live fast .error s) (due : s.time = c.readyDate) :
    TailAt c live fast .ready (setAux s 0 p .ready) ∧
    Nonempty (ParameterJump θ (fun _ _ => []) s (setAux s 0 p .ready)) := by
  have contact : s.x 0 (.m p) = (θ 0).thresholds.auxReady p := by
    have eq : s.x 0 (.m p) = c.errorM s.time := h.sensorValue
    rw [eq, due]
    exact c.errorHit
  have expired : live = false := by
    cases live
    · rfl
    · exfalso
      linarith [(h.rawClock rfl).2, c.rawBeforeReady]
  refine ⟨⟨h.date, h.rawClock, h.fastClock, h.date, h.main, h.mainValue, h.recovery,
    by simp [setAux, SensorTail.mode], ?_, h.raw, ?_, h.queue, fun _ => expired⟩,
    ⟨.auxReady s 0 p h.mode contact⟩⟩
  · change s.x 0 (.m p) < 1
    rw [contact]
    exact c.exitBelow
  · intro q neq
    obtain ⟨mode, raw, below⟩ := h.passive q neq
    exact ⟨by simpa [setAux, neq] using mode, raw, below⟩

private theorem TailAt.complete {θ p c s}
    (h : @TailAt θ p c false false .ready s) (date : s.time = c.horizon) :
    ParameterCompleteThrough (.nil (θ := θ) (route := fun _ _ => []) s) c.horizon := by
  have guards : ThresholdGuards (fun i => (θ i).thresholds) s s.x := by
    constructor
    · intro i
      rw [Subsingleton.elim i 0, h.main]
      change (θ 0).thresholds.reopen < s.x 0 .q
      rw [show s.x 0 .q = c.slowQ s.time from h.mainValue]
      exact c.slowBefore _ h.date
    · intro i q
      rw [Subsingleton.elim i 0]
      by_cases eq : q = p
      · subst q
        rw [h.mode]
        change s.x 0 (.m p) < (θ 0).thresholds.mark p
        rw [c.markNominal]
        exact h.sensorValue
      · rw [(h.passive q eq).1]
        change s.x 0 (.m q) < (θ 0).thresholds.mark q
        rw [c.markNominal]
        exact (h.passive q eq).2.2
  refine ⟨date, s.no_parameter_jump guards (by simp [h.queue]) ?_, by simp [h.queue]⟩
  intro i q o active
  rw [Subsingleton.elim i 0] at active
  by_cases eq : q = p
  · subst q
    have none : s.raw 0 p = none := h.raw
    simp [none] at active
  · simp [(h.passive q eq).2.1] at active

private theorem next_choice (r f e : ℝ) :
    min r (min f e) = r ∨ min r (min f e) = f ∨ min r (min f e) = e := by
  rcases le_total r (min f e) with h | h
  · exact .inl (min_eq_left h)
  · rw [min_eq_right h]
    rcases le_total f e with h | h
    · exact .inr (.inl (min_eq_left h))
    · exact .inr (.inr (min_eq_right h))

/-- Always process a least pending date. Other events due at that date are
processed without inserting a zero-duration flow. -/
private theorem TailAt.finish {θ p c live fast phase s}
    (h : @TailAt θ p c live fast phase s) :
    ∃ u, ∃ run : ParameterExecution θ (fun _ _ => []) s u,
      ParameterCompleteThrough run c.horizon := by
  suffices all : ∀ n : ℕ, ∀ {live fast phase s},
      tailCount live fast phase = n → TailAt c live fast phase s →
      ∃ u, ∃ run : ParameterExecution θ (fun _ _ => []) s u,
        ParameterCompleteThrough run c.horizon by
    exact all _ rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro live fast phase s count h
    let t := c.next live fast phase
    obtain ⟨edge, ⟨wait⟩⟩ := h.advance h.time_le_next le_rfl
    have recur {live' fast' phase' v} (jump : ParameterJump θ (fun _ _ => []) (frozenAt θ s t) v)
        (profile : TailAt c live' fast' phase' v) (smaller : tailCount live' fast' phase' < n) :
        ∃ u, ∃ run : ParameterExecution θ (fun _ _ => []) s u,
          ParameterCompleteThrough run c.horizon := by
      obtain ⟨u, suffix, done⟩ := ih _ smaller rfl profile
      exact ⟨u, wait.append (.cons (.jump jump) suffix), done⟩
    by_cases final : t = c.horizon
    · have r : live = false := by
        cases live
        · rfl
        · have hmin : t ≤ c.origin + 1 := min_le_left _ _
          linarith [c.rawBeforeHorizon]
      have f : fast = false := by
        cases fast
        · rfl
        · have hmin : t ≤ c.fastDate := (min_le_right _ _).trans (min_le_left _ _)
          linarith [c.fastBeforeHorizon]
      have e : phase = .ready := by
        cases phase
        · have hmin : t ≤ c.errorDate := (min_le_right _ _).trans (min_le_right _ _)
          linarith [c.errorBeforeReady, c.readyBeforeHorizon]
        · have hmin : t ≤ c.readyDate := (min_le_right _ _).trans (min_le_right _ _)
          linarith [c.readyBeforeHorizon]
        · rfl
      subst live
      subst fast
      subst phase
      exact ⟨_, wait, edge.complete final⟩
    · have chosen := next_choice (c.rawDate live) (c.mainDate fast) (c.sensorDate phase)
      change t = c.rawDate live ∨ t = c.mainDate fast ∨ t = c.sensorDate phase at chosen
      rcases chosen with raw | main | sensor
      · cases live
        · exact (final raw).elim
        · obtain ⟨p, ⟨j⟩⟩ := edge.expire raw
          exact recur j p (by rw [← count]; simp [tailCount])
      · cases fast
        · exact (final main).elim
        · obtain ⟨p, ⟨j⟩⟩ := edge.fastEnd main
          exact recur j p (by rw [← count]; simp [tailCount])
      · cases phase
        · obtain ⟨p, ⟨j⟩⟩ := edge.error sensor
          exact recur j p (by rw [← count]; simp [tailCount, SensorTail.count])
        · obtain ⟨p, ⟨j⟩⟩ := edge.auxReady sensor
          exact recur j p (by rw [← count]; simp [tailCount, SensorTail.count])
        · exact (final sensor).elim

private theorem decay_before_date {value rate origin deadline t target : ℝ}
    (valuePos : 0 < value) (ratePos : 0 < rate) (before : t < deadline)
    (hit : value * Real.exp (-rate * (deadline - origin)) = target) :
    target < value * Real.exp (-rate * (t - origin)) := by
  rw [← hit]
  apply mul_lt_mul_of_pos_left _ valuePos
  exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos ratePos (sub_pos.mpr before)])

/-- Continue the actual trained-port FIRE to time 20. All three physical
clocks use their realized guard values, including simultaneous events. -/
theorem TrainingRead.protected_complete_at_twenty {θ ε gains p upper lower level readTime}
    (run : TrainingRead θ 0 gains p upper lower level readTime)
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (fire : level ∈ Icc (19 / 20 : ℝ) (21 / 20))
    (entry : |upper - 1 / 10| ≤ 1 / 200)
    (exit : lower ∈ Icc (7 / 800 : ℝ) (9 / 800))
    (read : readTime ∈ Icc (333 / 20 : ℝ) (347 / 20)) :
    ∃ u, ∃ tail : ParameterExecution θ (fun _ _ => []) run.handoff.decision.final u,
      ParameterCompleteThrough tail 20 := by
  let decision := run.handoff.decision
  let start := run.handoff.readStart
  let g := decision.silent
  let s := decision.final
  let R := start.time
  let F := decision.stop
  let P := g.final.time
  let rs := (θ 0).ls p
  let re := (θ 0).le p
  let fastDate := F + Real.log (level / (1 / 4)) / a
  let errorDate := P + Real.log ((4 / 5) / upper) / rs
  let readyDate := errorDate + Real.log (upper / lower) / re
  let fastQ := fun t : ℝ => level * Real.exp (-a * (t - F))
  let slowQ := fun t : ℝ => (1 / 4 : ℝ) * Real.exp (-(2 / 25) * (t - fastDate))
  let silentM := fun t : ℝ => (4 / 5 : ℝ) * Real.exp (-rs * (t - P))
  let errorM := fun t : ℝ => upper * Real.exp (-re * (t - errorDate))
  have rDate : R = readTime := by dsimp [R, start]; rw [run.read_date]; ring
  have fireWindow : R + 3 / 10 < F ∧ F < R + 9 / 10 := ⟨decision.outcome.1, decision.outcome.2.1⟩
  have fireMin : 19 / 20 ≤ level := fire.1
  have fireMax : level ≤ 21 / 20 := fire.2
  have upperMin := (abs_le.mp entry).1
  have upperMax := (abs_le.mp entry).2
  have lowerMin := exit.1
  have lowerMax := exit.2
  have aPos : 0 < a := a_coarse_bounds.1.trans' (by norm_num)
  have rsPos : 0 < rs := (box.rates_positive 0 p).2.1
  have rePos : 0 < re := (box.rates_positive 0 p).2.2
  obtain ⟨fastPos, fastHit, _⟩ := protected_decay_schedule
    (show (0 : ℝ) < 1 / 4 by norm_num) (show 1 / 4 < level by linarith) aPos
  obtain ⟨_, silentHit, _⟩ := protected_decay_schedule (show 0 < upper by linarith)
    (show upper < (4 / 5 : ℝ) by linarith) rsPos
  obtain ⟨errorPos, errorHit, _⟩ := protected_decay_schedule (show 0 < lower by linarith)
    (show lower < upper by linarith) rePos
  have fastAfter : F < fastDate := lt_add_of_pos_right _ fastPos
  have fastBefore : fastDate < 20 := by
    have eq : Real.log (level / (1 / 4)) = a + Real.log level := by
      rw [show level / (1 / 4) = 4 * level by ring, Real.log_mul (by norm_num) (by linarith)]
      rfl
    have delay : Real.log (level / (1 / 4)) / a < 11 / 10 := by
      rw [eq]
      apply (div_lt_iff₀ aPos).2
      linarith [Real.log_le_sub_one_of_pos (show 0 < level by linarith), a_coarse_bounds.1]
    dsimp [fastDate]
    linarith [fireWindow.2, read.2]
  have errorWindow : R + 24 / 25 < errorDate ∧ errorDate < R + 127 / 100 := by
    have nominal := g.errorDate_bounds box
    change R + 99 / 100 < P + Real.log 8 / rs ∧ P + Real.log 8 / rs < R + 123 / 100 at nominal
    obtain ⟨_, early, late⟩ := training_silent_duration box p entry
    dsimp [errorDate]
    constructor <;> linarith [nominal.1, nominal.2]
  have ratioPos : 0 < upper / lower := div_pos (by linarith) (by linarith)
  have durationLower : 1 / 20 < Real.log (upper / lower) / re := by
    have ratio : (2 : ℝ) ≤ upper / lower := (le_div_iff₀ (by linarith)).2 (by linarith)
    have logBound := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ratio
    have reMax : re ≤ 11 := (box.coarse_upper 0 p).2.2.2.1
    apply (lt_div_iff₀ rePos).2
    linarith [Real.log_two_gt_d9]
  have durationUpper : Real.log (upper / lower) / re < 1 / 2 := by
    have ratio : upper / lower ≤ 12 := (div_le_iff₀ (by linarith)).2 (by linarith)
    have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 5
    norm_num [Finset.sum_range_succ] at series
    have logBound := (Real.log_lt_iff_lt_exp ratioPos).2
      (ratio.trans_lt (show (12 : ℝ) < Real.exp 3 by linarith))
    have param := ((box.2 0 p).2.2.2.1).1
    change a / (3 / 20) * (1 - ε) ≤ re at param
    have rateFloor : (6 : ℝ) ≤ re := by
      have prod := mul_le_mul
        (show (1 : ℝ) / (3 / 20) ≤ a / (3 / 20) by linarith [a_coarse_bounds.1])
        (show (9 / 10 : ℝ) ≤ 1 - ε by linarith [box.epsilon_bounds.2])
        (by norm_num) (div_nonneg aPos.le (by norm_num))
      linarith
    exact (div_lt_iff₀ rePos).2 (by linarith)
  have readyAfterRaw : R + 1 < readyDate := by
    dsimp [readyDate]
    linarith [errorWindow.1]
  have readyBefore : readyDate < 20 := by
    dsimp [readyDate]
    linarith [errorWindow.2, read.2]
  have fastEndValue : (θ 0).thresholds.fastEnd = 1 / 4 := by rw [config]; rfl
  have reopenValue : (θ 0).thresholds.reopen = 1 / 10 := by rw [config]; rfl
  have entryValue : (θ 0).thresholds.error p = upper := by rw [config]; simp [trainingThresholds]
  have exitValue : (θ 0).thresholds.auxReady p = lower := by rw [config]; simp [trainingThresholds]
  have fastEndpoint : fastQ fastDate = (θ 0).thresholds.fastEnd := by
    rw [fastEndValue]
    simpa only [fastQ, fastDate, add_sub_cancel_left] using fastHit
  have silentEndpoint : silentM errorDate = (θ 0).thresholds.error p := by
    rw [entryValue]
    simpa only [silentM, errorDate, add_sub_cancel_left] using silentHit
  have errorEndpoint : errorM readyDate = (θ 0).thresholds.auxReady p := by
    rw [exitValue]
    simpa only [errorM, readyDate, add_sub_cancel_left] using errorHit
  let calendar : TailCalendar θ p := {
    origin := R
    fastDate := fastDate
    errorDate := errorDate
    readyDate := readyDate
    horizon := 20
    recovery := 2 / 25
    fastQ := fastQ
    slowQ := slowQ
    silentM := silentM
    errorM := errorM
    fastRestart := by intro x t; simp only [fastQ, mul_assoc, attenuation_split]
    slowRestart := by intro x t; simp only [slowQ, mul_assoc, attenuation_split]
    silentRestart := by intro x t; simp only [silentM, mul_assoc, rs, attenuation_split]
    errorRestart := by intro x t; simp only [errorM, mul_assoc, re, attenuation_split]
    fastBefore := fun _ ht => decay_before_date (by linarith) aPos ht fastEndpoint
    slowBefore := by
      intro t ht
      rw [reopenValue]
      have htime : t - fastDate ≤ 4 := by linarith [fireWindow.1, read.1]
      dsimp [slowQ]
      linarith [Real.add_one_le_exp (-(2 / 25 : ℝ) * (t - fastDate))]
    silentBefore := fun _ ht => decay_before_date (by norm_num) rsPos ht silentEndpoint
    errorBefore := fun _ ht => decay_before_date (by linarith) rePos ht errorEndpoint
    fastHit := fastEndpoint
    slowStart := by rw [fastEndValue]; simp [slowQ]
    silentHit := silentEndpoint
    errorStart := by rw [entryValue]; simp [errorM]
    errorHit := errorEndpoint
    exitBelow := by rw [exitValue]; linarith
    markNominal := by intro q; rw [config]; rfl
    rawBeforeHorizon := by linarith [read.2]
    fastBeforeHorizon := fastBefore
    errorBeforeReady := lt_add_of_pos_right _ errorPos
    readyBeforeHorizon := readyBefore
    rawBeforeReady := readyAfterRaw
  }
  have h : TailAt calendar true true .silent s := by
    refine ⟨by change F ≤ 20; linarith [fireWindow.2, read.2],
      fun _ => ⟨by change R ≤ F; linarith [fireWindow.1],
        by change F ≤ R + 1; linarith [fireWindow.2]⟩, fastAfter.le, ?_,
      by simp [s, decision, TolerantSnapshotDecision.final, setMain], ?_, ?_, g.aux_silent, ?_,
      g.raw_active, ?_, decision.leg.empty, by decide⟩
    · change F ≤ errorDate
      linarith [fireWindow.2, errorWindow.1]
    · change s.x 0 .q = fastQ F
      simpa [s, TolerantSnapshotDecision.final, setMain, fastQ, F] using decision.outcome.2.2.1
    · change g.final.x 0 .b = 2 / 25
      exact (g.recovery_preserved 0).trans run.recovery_at_read
    · change readyProtectedValues θ g.final 0 p .silent (some R) F 0 (.m p) = silentM F
      simp [readyProtectedValues, protectedReadyRate, g.sensor_charge, silentM, P, rs]
    · intro q neq
      have guard := decision.leg.aux_guards F ⟨decision.leg.positive.le, le_rfl⟩ 0 q
      rw [g.aux_other 0 q (Or.inr neq)] at guard
      exact ⟨g.aux_other 0 q (Or.inr neq), g.raw_other 0 q (Or.inr neq), guard⟩
  exact h.finish

end RecursiveLearning.Native
