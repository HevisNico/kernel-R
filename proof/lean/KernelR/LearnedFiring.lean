import KernelR.LearnedDriven

/-! Construction of the actual MARK-to-SILENT-to-main-fire continuation.
The two positive flows satisfy every physical guard and retain the live raw
origin. No reacting execution or desired event word is an input. -/
namespace KernelR.Hybrid
open Set

theorem frozen_protected_sensor {theta current port mode}
    (hm : current.aux (0 : Fin 1) port = mode) (hne : mode ≠ .ready) (t : ℝ) :
    frozenValues theta current t 0 (.m port) = current.x 0 (.m port) *
      Real.exp (-auxRate (theta 0) port mode*(t-current.time)) := by
  simp [frozenValues, frozenBody, frozenAux, hm, hne]

noncomputable def FirstMarkPrefix.silentState {theta reference port}
    (stage : FirstMarkPrefix theta reference port) : Snapshot 1 :=
  setAux (frozenAt theta stage.last (reference.time+stage.clock.markEnd)) 0 port .silent

noncomputable def FirstMarkPrefix.fireBefore {theta reference port}
    (stage : FirstMarkPrefix theta reference port) : Snapshot 1 :=
  frozenAt theta stage.silentState (reference.time+stage.clock.fire)

noncomputable def FirstMarkPrefix.firedState {theta reference port}
    (stage : FirstMarkPrefix theta reference port) : Snapshot 1 :=
  { (setMain stage.fireBefore 0 .fast) with pending := stage.fireBefore.pending ++ [] }

theorem FirstMarkPrefix.mark_elapsed {theta reference port}
    (stage : FirstMarkPrefix theta reference port) :
    reference.time+stage.clock.markEnd-stage.last.time =
      Real.log (5/4) / (theta 0).lm port := by
  rw [stage.date]
  dsimp [LearnedClock.markEnd]
  ring

noncomputable def FirstMarkPrefix.markFlow {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    Flow theta stage.last (frozenAt theta stage.last (reference.time+stage.clock.markEnd)) := by
  have order := stage.clock.chronology hb 0 port (hs.recovery 0)
  apply (stage.ready_profile hs).flow stage.clock
    (by rw [stage.auxiliary_mark]; decide)
  · rw [stage.date]; linarith [order.mark_span]
  · linarith [order.mark_before_fire]
  · intro t ht
    simp only [stage.auxiliary_mark]
    rw [frozen_protected_sensor stage.auxiliary_mark (by decide), stage.mark_charge hs]
    simp only [auxRate]
    apply decay_section_before (by norm_num) (by norm_num) (hb.rates_positive 0 port).1
    norm_num
    linarith [stage.mark_elapsed, ht.2]

theorem FirstMarkPrefix.silent_charge {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    stage.silentState.x 0 (.m port) = 4/5 := by
  change frozenValues theta stage.last (reference.time+stage.clock.markEnd) 0 (.m port) = _
  rw [frozen_protected_sensor stage.auxiliary_mark (by decide), stage.mark_charge hs,
    stage.mark_elapsed]
  simpa [auxRate] using decay_section_endpoint (initial := 1) (final := 4/5)
    (by norm_num) (by norm_num) (hb.rates_positive 0 port).1

theorem FirstMarkPrefix.silent_profile {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    LearnedReadyProfile reference port stage.silentState := by
  apply LearnedReadyProfile.setAux
  apply (stage.ready_profile hs).frozen theta
  exact stage.markFlow hs hb |>.positive.le

theorem FirstMarkPrefix.silent_mode {theta reference port}
    (stage : FirstMarkPrefix theta reference port) : stage.silentState.aux 0 port = .silent := by
  simp [silentState, setAux]

theorem FirstMarkPrefix.silent_guard {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon)
    {t : ℝ} (ht : t ≤ reference.time+stage.clock.fire) :
    1/10 < frozenValues theta stage.silentState t 0 (.m port) := by
  rw [frozen_protected_sensor stage.silent_mode (by decide), stage.silent_charge hs hb]
  simp only [auxRate]
  apply decay_section_before (by norm_num) (by norm_num) (hb.rates_positive 0 port).2.1
  norm_num
  have order := stage.clock.chronology hb 0 port (hs.recovery 0)
  have horder := order.fire_before_error
  change t-(reference.time+stage.clock.markEnd) < _
  dsimp [LearnedClock.errorStart] at horder
  linarith

noncomputable def FirstMarkPrefix.silentFlow {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    Flow theta stage.silentState stage.fireBefore := by
  have order := stage.clock.chronology hb 0 port (hs.recovery 0)
  apply (stage.silent_profile hs hb).flow stage.clock
    (by rw [stage.silent_mode]; decide)
  · change reference.time+stage.clock.markEnd < reference.time+stage.clock.fire
    linarith [order.mark_before_fire]
  · exact le_rfl
  · intro t ht
    simp only [stage.silent_mode]
    exact stage.silent_guard hs hb ht.2.le

theorem FirstMarkPrefix.fire_charge {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    stage.fireBefore.x 0 .q = 1 := by
  change frozenValues theta stage.silentState (reference.time+stage.clock.fire) 0 .q = 1
  rw [(stage.silent_profile hs hb).main_solution]
  simpa using stage.clock.fire_value

theorem FirstMarkPrefix.fired_pending {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    stage.firedState.pending = [] := by
  simpa [firedState, fireBefore, frozenAt, setMain] using
    (stage.silent_profile hs hb).pending

theorem FirstMarkPrefix.fired_guards {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    BeforeGuards stage.firedState stage.firedState.x := by
  constructor
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hq := stage.fire_charge hs hb
    change 1/4 < stage.fireBefore.x 0 .q
    linarith
  · intro i p
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (match stage.silentState.aux 0 p with
      | .ready => stage.fireBefore.x 0 (.m p) < 1
      | .mark => 4/5 < stage.fireBefore.x 0 (.m p)
      | .silent => 1/10 < stage.fireBefore.x 0 (.m p)
      | .error => 1/40 < stage.fireBefore.x 0 (.m p))
    by_cases hp : p = port
    · subst p
      rw [stage.silent_mode]
      exact stage.silent_guard hs hb le_rfl
    · rw [(stage.silent_profile hs hb).passive_mode p hp]
      have hh := (abs_le.mp ((stage.silent_profile hs hb).passive_bound theta
        (stage.silentFlow hs hb).positive.le p hp)).2
      change stage.fireBefore.x 0 (.m p)-1/40 ≤ 1/100000 at hh
      change stage.fireBefore.x 0 (.m p) < 1
      linarith

theorem FirstMarkPrefix.fired_no_jump {theta reference port active epsilon}
    (stage : FirstMarkPrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon)
    (u : Snapshot 1) : IsEmpty (Jump (fun _ _ => []) stage.firedState u) := by
  apply no_jump_interior (stage.fired_guards hs hb)
  · intro i p origin hr
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change stage.silentState.raw 0 p = some origin at hr
    rw [(stage.silent_profile hs hb).raw p] at hr
    by_cases hp : p = port
    · simp only [hp, ite_true, Option.some.injEq] at hr
      change reference.time+stage.clock.fire < origin+1
      linarith [stage.clock.fire_upper]
    · simp [hp] at hr
  · simp [stage.fired_pending hs hb]

structure FirstFirePrefix (theta : Fin 1 → Parameters) (reference : Snapshot 1) (port : Port) where
  mark : FirstMarkPrefix theta reference port
  execution : Execution theta (fun _ _ => [])
    (withFuture reference [sourceToken 0 port reference.time]) mark.firedState
  memory : SameMemory reference mark.firedState
  emissions : execution.ledger.emissions = [(0, reference.time+mark.clock.fire)]
  reserve : 50 ≤ mark.firedState.x 0 .energy ∧ mark.firedState.x 0 .energy ≤ 100
  complete : CompleteThrough execution (reference.time+mark.clock.fire)

noncomputable def FirstFirePrefix.last {theta reference port}
    (stage : FirstFirePrefix theta reference port) : Snapshot 1 := stage.mark.firedState

theorem FirstFirePrefix.date {theta reference port}
    (stage : FirstFirePrefix theta reference port) :
    stage.last.time = reference.time+stage.mark.clock.fire := rfl

theorem FirstFirePrefix.main_fast {theta reference port}
    (stage : FirstFirePrefix theta reference port) : stage.last.main 0 = .fast := by
  simp [last, FirstMarkPrefix.firedState, setMain]

theorem FirstFirePrefix.auxiliary_silent {theta reference port}
    (stage : FirstFirePrefix theta reference port) : stage.last.aux 0 port = .silent :=
  stage.mark.silent_mode

theorem learned_first_fire_prefix {theta reference active epsilon}
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    Nonempty (FirstFirePrefix theta reference (active 0)) := by
  obtain ⟨stage⟩ := learned_first_mark_prefix hs hb
  let markFlow := stage.markFlow hs hb
  let silentJump : Jump (fun _ _ => [])
      (frozenAt theta stage.last (reference.time+stage.clock.markEnd)) stage.silentState :=
    Jump.silent _ 0 (active 0) stage.auxiliary_mark (stage.silent_charge hs hb)
  let silentFlow := stage.silentFlow hs hb
  let fire : Jump (fun _ _ => []) stage.fireBefore stage.firedState :=
    Jump.fire _ 0 (stage.silent_profile hs hb).main (stage.fire_charge hs hb)
  let tail : Execution theta (fun _ _ => []) stage.last stage.firedState :=
    .cons (.flow markFlow) (.cons (.jump silentJump)
      (.cons (.flow silentFlow) (.cons (.jump fire) (.nil _))))
  let run := stage.execution.append tail
  refine ⟨⟨stage, run, ?_, ?_, ?_, ?_⟩⟩
  · exact ((stage.silent_profile hs hb).frozen theta silentFlow.positive.le).memory
  · change (stage.execution.append tail).ledger.emissions = _
    rw [Execution.append_ledger]
    change stage.execution.ledger.emissions ++ tail.ledger.emissions = _
    rw [stage.emissions]
    rfl
  · exact run.reserve_invariant 0 (hs.reserve 0)
      (run.actual_work_bound hb hs.upper_region hs.cap 0)
  · exact ⟨rfl, stage.fired_no_jump hs hb, by simp [stage.fired_pending hs hb]⟩

end KernelR.Hybrid
