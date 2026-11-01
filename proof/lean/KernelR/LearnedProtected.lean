import KernelR.LearnedFiring
import KernelR.HybridPulseSpans

/-! Actual FAST continuations with a protected auxiliary. The raw endpoint is
processed as a physical jump, including a zero-duration cut at a phase boundary.
Every new segment starts from the actual preceding state and reserve. -/
namespace KernelR.Hybrid
open Set

structure LearnedFastPhase (theta : Fin 1 → Parameters) (reference : Snapshot 1)
    (port : Port) where
  fireTime : ℝ
  sensorOrigin : ℝ
  initial : ℝ
  mode : AuxMode
  not_ready : mode ≠ .ready
  no_mark : mode ≠ .mark
  initial_pos : 0 < initial
  rate_pos : 0 < auxRate (theta 0) port mode

noncomputable def LearnedFastPhase.deadline {theta reference port}
    (phase : LearnedFastPhase theta reference port) : ℝ :=
  phase.sensorOrigin + Real.log (phase.initial / protectedFloor phase.mode) /
    auxRate (theta 0) port phase.mode

structure FastProtectedProfile {theta reference port}
    (phase : LearnedFastPhase theta reference port) (live : Bool) (current : Snapshot 1) : Prop where
  main : current.main 0 = .fast
  auxiliary : current.aux 0 port = phase.mode
  passive_mode : ∀ p, p ≠ port → current.aux 0 p = .ready
  raw : ∀ p, current.raw 0 p = if live then (if p = port then some reference.time else none) else none
  pending : current.pending = []
  memory : SameMemory reference current
  charge : current.x 0 .q = Real.exp (-a*(current.time-phase.fireTime))
  sensor : current.x 0 (.m port) = phase.initial *
    Real.exp (-auxRate (theta 0) port phase.mode*(current.time-phase.sensorOrigin))
  passive_sensor : ∀ p, p ≠ port → |current.x 0 (.m p)-1/40| ≤ 1/100000
  time_lower : reference.time ≤ current.time
  raw_time : live = true → current.time ≤ reference.time+1

theorem frozen_idle_sensor {theta current p}
    (hm : current.aux (0 : Fin 1) p = .ready) (hr : current.raw 0 p = none) (t : ℝ) :
    frozenValues theta current t 0 (.m p) =
      1/40 + (current.x 0 (.m p)-1/40)*Real.exp (-(1/2)*(t-current.time)) := by
  simp [frozenValues, frozenBody, frozenAux, hm, frozenRawAmplitude, hr, auxPulse, readyPulse]
  ring

theorem frozen_idle_sensor_bound {theta current p t}
    (hm : current.aux (0 : Fin 1) p = .ready) (hr : current.raw 0 p = none)
    (hi : |current.x 0 (.m p)-1/40| ≤ 1/100000) (ht : current.time ≤ t) :
    |frozenValues theta current t 0 (.m p)-1/40| ≤ 1/100000 := by
  have he : Real.exp (-(1/2:ℝ)*(t-current.time)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hh := mul_le_mul hi he (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1/100000)
  rw [frozen_idle_sensor hm hr]
  simpa [abs_mul, abs_of_pos (Real.exp_pos _)] using hh

theorem FastProtectedProfile.passive_raw {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current) {p} (hp : p ≠ port) :
    current.raw 0 p = none := by rw [h.raw]; cases live <;> simp [hp]

theorem FastProtectedProfile.main_solution {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current) (t : ℝ) :
    frozenValues theta current t 0 .q = Real.exp (-a*(t-phase.fireTime)) := by
  simp only [frozenValues, frozenBody, frozenMain, h.main]
  rw [h.charge, ← Real.exp_add]
  congr 1
  ring

theorem FastProtectedProfile.sensor_solution {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current) (t : ℝ) :
    frozenValues theta current t 0 (.m port) = phase.initial *
      Real.exp (-auxRate (theta 0) port phase.mode*(t-phase.sensorOrigin)) := by
  rw [frozen_protected_sensor h.auxiliary phase.not_ready, h.sensor, mul_assoc,
    attenuation_split]

theorem FastProtectedProfile.frozen {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current) {t : ℝ}
    (ht : current.time ≤ t) (hr : live = true → t ≤ reference.time+1) :
    FastProtectedProfile phase live (frozenAt theta current t) where
  main := h.main
  auxiliary := h.auxiliary
  passive_mode := h.passive_mode
  raw := h.raw
  pending := h.pending
  memory := h.memory
  charge := h.main_solution t
  sensor := h.sensor_solution t
  passive_sensor := fun p hp => frozen_idle_sensor_bound (theta := theta) (h.passive_mode p hp)
    (h.passive_raw hp) (h.passive_sensor p hp) ht
  time_lower := h.time_lower.trans ht
  raw_time := hr

theorem FastProtectedProfile.clearRaw {theta reference port phase current}
    (h : @FastProtectedProfile theta reference port phase true current) :
    FastProtectedProfile phase false (setRaw current 0 port none) where
  main := h.main
  auxiliary := h.auxiliary
  passive_mode := h.passive_mode
  raw := by intro p; by_cases hp : p = port <;> simp [setRaw, h.raw, hp]
  pending := h.pending
  memory := h.memory
  charge := h.charge
  sensor := h.sensor
  passive_sensor := h.passive_sensor
  time_lower := h.time_lower
  raw_time := by simp

theorem FastProtectedProfile.at_deadline {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current)
    (ht : current.time = phase.deadline) : current.x 0 (.m port) = protectedFloor phase.mode := by
  rw [h.sensor, ht]
  simp only [LearnedFastPhase.deadline, add_sub_cancel_left]
  exact decay_section_endpoint phase.initial_pos
    (protectedFloor_positive phase.mode phase.not_ready) phase.rate_pos

theorem FastProtectedProfile.enter {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current)
    (targetPhase : LearnedFastPhase theta reference port)
    (hf : targetPhase.fireTime = phase.fireTime) (ht : targetPhase.sensorOrigin = current.time)
    (hx : current.x 0 (.m port) = targetPhase.initial) :
    FastProtectedProfile targetPhase live (setAux current 0 port targetPhase.mode) where
  main := h.main
  auxiliary := by simp [setAux]
  passive_mode := by intro p hp; simpa [setAux, hp] using h.passive_mode p hp
  raw := h.raw
  pending := h.pending
  memory := h.memory
  charge := by simpa [setAux, hf] using h.charge
  sensor := by simp [setAux, ht, hx]
  passive_sensor := h.passive_sensor
  time_lower := h.time_lower
  raw_time := h.raw_time

theorem fast_exponential_before {t fire : ℝ} (ht : t < fire+1) :
    (1/4:ℝ) < Real.exp (-a*(t-fire)) := by
  rw [← exp_neg_a]
  apply Real.exp_lt_exp.mpr
  have ha : 0 < a := by linarith [a_coarse_bounds.1]
  have hh := mul_pos ha (show 0 < fire+1-t by linarith)
  nlinarith

noncomputable def FastProtectedProfile.flow {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current) {T : ℝ}
    (hT : current.time < T) (hf : T ≤ phase.fireTime+1) (ha : T ≤ phase.deadline)
    (hr : live = true → T ≤ reference.time+1) :
    Flow theta current (frozenAt theta current T) := by
  have hfrozen : FrozenModes current := by
    constructor
    · intro i p hm
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [h.main] at hm
      cases hm
    · intro i p hm
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      by_cases hp : p = port
      · subst p; exact False.elim (phase.no_mark (h.auxiliary.symm.trans hm))
      · rw [h.passive_mode p hp] at hm; cases hm
  apply frozenFlow hfrozen hT
  · intro t ht
    constructor
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [h.main]
      rw [h.main_solution]
      exact fast_exponential_before (ht.2.trans_le hf)
    · intro i p
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      by_cases hp : p = port
      · subst p
        have hdecay := decay_section_before phase.initial_pos
          (protectedFloor_positive phase.mode phase.not_ready) phase.rate_pos
          (show t-phase.sensorOrigin < Real.log (phase.initial/protectedFloor phase.mode) /
            auxRate (theta 0) port phase.mode by dsimp [LearnedFastPhase.deadline] at ha; linarith [ht.2])
        rw [← h.sensor_solution] at hdecay
        rw [h.auxiliary]
        cases hm : phase.mode with
        | ready => exact False.elim (phase.not_ready hm)
        | mark => exact False.elim (phase.no_mark hm)
        | silent => simpa [hm, protectedFloor] using hdecay
        | error => simpa [hm, protectedFloor] using hdecay
      · simp only [h.passive_mode p hp]
        have hh := (abs_le.mp (frozen_idle_sensor_bound (theta := theta) (h.passive_mode p hp)
          (h.passive_raw hp) (h.passive_sensor p hp) ht.1)).2
        linarith
  · intro i p origin hraw
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [h.raw] at hraw
    cases hl : live with
    | false => simp [hl] at hraw
    | true =>
      by_cases hp : p = port
      · simp [hl, hp] at hraw
        exact ⟨by linarith [h.time_lower], by linarith [hr hl]⟩
      · simp [hl, hp] at hraw
  · simp [h.pending]

structure FastPhaseSpan {theta reference port}
    (phase : LearnedFastPhase theta reference port) (live : Bool) (start : Snapshot 1) (T : ℝ) where
  last : Snapshot 1
  execution : Execution theta (fun _ _ => []) start last
  date : last.time = T
  profile : FastProtectedProfile phase live last
  emissions : execution.ledger.emissions = []

noncomputable def FastProtectedProfile.flowTo {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current) {T : ℝ}
    (hT : current.time ≤ T) (hf : T ≤ phase.fireTime+1) (ha : T ≤ phase.deadline)
    (hr : live = true → T ≤ reference.time+1) : FastPhaseSpan phase live current T := by
  by_cases he : current.time = T
  · exact ⟨current, .nil _, he, h, rfl⟩
  · let f := h.flow (lt_of_le_of_ne hT he) hf ha hr
    exact ⟨frozenAt theta current T, .cons (.flow f) (.nil _), rfl,
      h.frozen hT hr, rfl⟩

structure FastPhaseAdvance {theta reference port}
    (phase : LearnedFastPhase theta reference port) (start : Snapshot 1) (T : ℝ) where
  live : Bool
  last : Snapshot 1
  execution : Execution theta (fun _ _ => []) start last
  date : last.time = T
  profile : FastProtectedProfile phase live last
  emissions : execution.ledger.emissions = []
  raw_cleared : reference.time+1 ≤ T → live = false

/-- Actual raw-end processing covers raw-before-phase, phase-before-raw and
equal dates. Equality uses two legal zero-time jumps, without a positive flow. -/
noncomputable def FastProtectedProfile.advance {theta reference port phase live current}
    (h : @FastProtectedProfile theta reference port phase live current) {T : ℝ}
    (hT : current.time ≤ T) (hf : T ≤ phase.fireTime+1) (ha : T ≤ phase.deadline) :
    FastPhaseAdvance phase current T := by
  cases hl : live with
  | false =>
    have hp : FastProtectedProfile phase false current := by simpa [hl] using h
    let span := hp.flowTo hT hf ha (by simp)
    exact ⟨false, span.last, span.execution, span.date, span.profile, span.emissions, fun _ => rfl⟩
  | true =>
    have hp : FastProtectedProfile phase true current := by simpa [hl] using h
    by_cases he : reference.time+1 ≤ T
    · let before := hp.flowTo (hp.raw_time rfl) (he.trans hf) (he.trans ha) (fun _ => le_rfl)
      let ending : Jump (fun _ _ => []) before.last (setRaw before.last 0 port none) :=
        Jump.rawEnd _ 0 port reference.time (by simpa using before.profile.raw port) before.date
      have hclear := before.profile.clearRaw
      let after := hclear.flowTo (by change before.last.time ≤ T; rw [before.date]; exact he)
        hf ha (by simp)
      let run := before.execution.append (.cons (.jump ending) after.execution)
      refine ⟨false, after.last, run, after.date, after.profile, ?_, fun _ => rfl⟩
      change (before.execution.append _).ledger.emissions = []
      rw [Execution.append_ledger]
      change before.execution.ledger.emissions ++ (ending.ledger.emissions ++ after.execution.ledger.emissions) = []
      rw [before.emissions, after.emissions]
      rfl
    · let span := hp.flowTo hT hf ha (fun _ => (lt_of_not_ge he).le)
      exact ⟨true, span.last, span.execution, span.date, span.profile, span.emissions,
        fun hbad => False.elim (he hbad)⟩

end KernelR.Hybrid
