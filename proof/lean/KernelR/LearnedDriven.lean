import KernelR.LearnedCycleStart

/-! The live READY profile across the learned pulse's protected auxiliary
phases. Raw origins and the main response survive each physical flow cut;
passive sensors contract toward rest rather than being reset. -/
namespace KernelR.Hybrid
open Set

structure LearnedReadyProfile (reference : Snapshot 1) (port : Port)
    (current : Snapshot 1) : Prop where
  main : current.main 0 = .ready
  passive_mode : ∀ p, p ≠ port → current.aux 0 p = .ready
  raw : ∀ p, current.raw 0 p = if p = port then some reference.time else none
  pending : current.pending = []
  memory : SameMemory reference current
  charge : current.x 0 .q =
    learnedHead (Real.exp (reference.x 0 (.z port))) (current.time-reference.time)
  passive_sensor : ∀ p, p ≠ port → |current.x 0 (.m p)-1/40| ≤ 1/100000
  time_lower : reference.time ≤ current.time

theorem learnedHead_restart (gain start cut finish : ℝ) :
    readyPulse (learnedHead gain (cut-start))
      (gain*Real.exp (-a*(cut-start))) cut finish = learnedHead gain (finish-start) := by
  have hr (t : ℝ) : readyPulse (1/10) gain start t = learnedHead gain (t-start) := by
    simp [readyPulse, learnedHead]
  rw [← hr cut, readyPulse_compose, hr finish]

theorem LearnedReadyProfile.amplitude {reference port current}
    (h : LearnedReadyProfile reference port current) :
    mainAmplitude current 0 = Real.exp (reference.x 0 (.z port)) *
      Real.exp (-a*(current.time-reference.time)) := by
  unfold mainAmplitude
  rw [Finset.sum_eq_single port]
  · simp [frozenRawAmplitude, h.raw, (h.memory 0).2 port]
  · intro other _ hne
    simp [frozenRawAmplitude, h.raw, hne]
  · simp

theorem LearnedReadyProfile.main_solution {reference port current}
    (h : LearnedReadyProfile reference port current) (theta : Fin 1 → Parameters) (t : ℝ) :
    frozenValues theta current t 0 .q =
      learnedHead (Real.exp (reference.x 0 (.z port))) (t-reference.time) := by
  change frozenMain current 0 t = _
  simp only [frozenMain, h.main]
  rw [h.charge, h.amplitude, learnedHead_restart]

theorem LearnedReadyProfile.passive_solution {reference port current}
    (h : LearnedReadyProfile reference port current) (theta : Fin 1 → Parameters)
    (p : Port) (hp : p ≠ port) (t : ℝ) :
    frozenValues theta current t 0 (.m p) =
      1/40 + (current.x 0 (.m p)-1/40)*Real.exp (-(1/2)*(t-current.time)) := by
  simp [frozenValues, frozenBody, frozenAux, h.passive_mode p hp,
    frozenRawAmplitude, h.raw, hp, auxPulse, readyPulse]
  ring

theorem LearnedReadyProfile.passive_bound {reference port current}
    (h : LearnedReadyProfile reference port current) (theta : Fin 1 → Parameters)
    {t : ℝ} (ht : current.time ≤ t) (p : Port) (hp : p ≠ port) :
    |frozenValues theta current t 0 (.m p)-1/40| ≤ 1/100000 := by
  have he : Real.exp (-(1/2:ℝ)*(t-current.time)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hm := mul_le_mul (h.passive_sensor p hp) he (Real.exp_pos _).le
    (by norm_num : (0:ℝ) ≤ 1/100000)
  rw [h.passive_solution theta p hp]
  simpa [abs_mul, abs_of_pos (Real.exp_pos _)] using hm

theorem LearnedReadyProfile.frozen {reference port current}
    (h : LearnedReadyProfile reference port current) (theta : Fin 1 → Parameters)
    {t : ℝ} (ht : current.time ≤ t) :
    LearnedReadyProfile reference port (frozenAt theta current t) where
  main := h.main
  passive_mode := h.passive_mode
  raw := h.raw
  pending := h.pending
  memory := h.memory
  charge := h.main_solution theta t
  passive_sensor := h.passive_bound theta ht
  time_lower := h.time_lower.trans ht

theorem LearnedReadyProfile.setAux {reference port current}
    (h : LearnedReadyProfile reference port current) (mode : AuxMode) :
    LearnedReadyProfile reference port (Hybrid.setAux current 0 port mode) where
  main := h.main
  passive_mode := by intro p hp; simpa [Hybrid.setAux, hp] using h.passive_mode p hp
  raw := h.raw
  pending := h.pending
  memory := h.memory
  charge := h.charge
  passive_sensor := h.passive_sensor
  time_lower := h.time_lower

theorem LearnedReadyProfile.received {theta active reference}
    (hs : LearnedRest theta active reference) (port : Port) :
    LearnedReadyProfile reference port (receivedInput reference port) where
  main := hs.main 0
  passive_mode := fun p _ => hs.aux 0 p
  raw := by intro p; by_cases hp : p = port <;> simp [receivedInput, setRaw, hs.raw, hp]
  pending := rfl
  memory := by intro i; exact ⟨rfl, fun _ => rfl⟩
  charge := by simp [receivedInput, setRaw, hs.charge, learnedHead, response]
  passive_sensor := fun p _ => hs.sensor 0 p
  time_lower := le_rfl

theorem FirstMarkPrefix.ready_profile {theta reference port}
    (stage : FirstMarkPrefix theta reference port) {active}
    (hs : LearnedRest theta active reference) :
    LearnedReadyProfile reference port stage.last := by
  rw [stage.physical_state]
  apply LearnedReadyProfile.setAux
  apply (LearnedReadyProfile.received hs port).frozen theta
  change reference.time ≤ reference.time+stage.clock.auxiliary
  linarith [stage.clock.auxiliary_lower]

theorem FirstMarkPrefix.mark_charge {theta reference port}
    (stage : FirstMarkPrefix theta reference port) {active}
    (hs : LearnedRest theta active reference) : stage.last.x 0 (.m port) = 1 := by
  rw [stage.physical_state]
  change frozenValues theta (receivedInput reference port)
    (reference.time+stage.clock.auxiliary) 0 (.m port) = 1
  rw [receivedInput_active_charge hs port]
  simpa using stage.clock.auxiliary_value

theorem LearnedReadyProfile.frozen_modes {reference port current}
    (h : LearnedReadyProfile reference port current) (ha : current.aux 0 port ≠ .error) :
    FrozenModes current := by
  constructor
  · intro i p _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    by_cases hp : p = port
    · subst p; exact ha
    · rw [h.passive_mode p hp]; decide
  · intro i p _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h.main

/-- The main and passive guards follow from the live profile. Only the active
auxiliary's strict guard is supplied by its actual protected decay. -/
noncomputable def LearnedReadyProfile.flow {reference port current theta}
    (h : LearnedReadyProfile reference port current)
    (clock : LearnedClock (theta 0) port (Real.exp (reference.x 0 (.z port)))
      (reference.x 0 (.m port)))
    (ha : current.aux 0 port ≠ .error) {T : ℝ} (hT : current.time < T)
    (hf : T ≤ reference.time+clock.fire)
    (haux : ∀ t ∈ Ico current.time T, match current.aux 0 port with
      | .ready => frozenValues theta current t 0 (.m port) < 1
      | .mark => 4/5 < frozenValues theta current t 0 (.m port)
      | .silent => 1/10 < frozenValues theta current t 0 (.m port)
      | .error => 1/40 < frozenValues theta current t 0 (.m port)) :
    Flow theta current (frozenAt theta current T) := by
  apply frozenFlow (h.frozen_modes ha) hT
  · intro t ht
    constructor
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [h.main]
      rw [h.main_solution theta t]
      apply clock.fire_before
      constructor
      · linarith [h.time_lower, ht.1]
      · linarith [ht.2]
    · intro i p
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      by_cases hp : p = port
      · subst p; exact haux t ht
      · simp only [h.passive_mode p hp]
        have hh := (abs_le.mp (h.passive_bound theta ht.1 p hp)).2
        linarith
  · intro i p origin hr
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    by_cases hp : p = port
    · subst p
      have ho : origin = reference.time := by simpa [h.raw] using hr.symm
      subst origin
      exact ⟨h.time_lower, by linarith [clock.fire_upper]⟩
    · simp [h.raw, hp] at hr
  · simp [h.pending]

end KernelR.Hybrid
