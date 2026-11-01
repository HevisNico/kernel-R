import KernelR.LearnedProtected

/-! Construct the two protected auxiliary phases after the learned firing.
Raw-end cuts use the actual calendar and leave the reserve in the live state. -/
namespace KernelR.Hybrid
open Set

/-- Coincident ERROR entry and raw end commute as actual zero-time runs.
The two orders reach the same complete physical snapshot. -/
theorem error_raw_end_commute {theta : Fin 1 → Parameters} (current : Snapshot 1)
    (port : Port) (origin : ℝ) (hm : current.aux 0 port = .silent)
    (hx : current.x 0 (.m port) = 1/10) (hr : current.raw 0 port = some origin)
    (ht : current.time = origin+1) :
    ∃ left right : Execution theta (fun _ _ => []) current
        (setAux (setRaw current 0 port none) 0 port .error),
      left.ledger.emissions = [] ∧ right.ledger.emissions = [] := by
  let rawFirst : Jump (fun _ _ => []) current (setRaw current 0 port none) :=
    Jump.rawEnd _ 0 port origin hr ht
  let errorAfter : Jump (fun _ _ => []) (setRaw current 0 port none)
      (setAux (setRaw current 0 port none) 0 port .error) := Jump.error _ 0 port hm hx
  let errorFirst : Jump (fun _ _ => []) current (setAux current 0 port .error) := Jump.error _ 0 port hm hx
  let rawAfter : Jump (fun _ _ => []) (setAux current 0 port .error)
      (setAux (setRaw current 0 port none) 0 port .error) := Jump.rawEnd _ 0 port origin hr ht
  exact ⟨.cons (.jump rawFirst) (.cons (.jump errorAfter) (.nil _)),
    .cons (.jump errorFirst) (.cons (.jump rawAfter) (.nil _)), rfl, rfl⟩

noncomputable def FirstFirePrefix.silentPhase {theta reference port active epsilon}
    (stage : FirstFirePrefix theta reference port)
    (_hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    LearnedFastPhase theta reference port :=
  ⟨reference.time+stage.mark.clock.fire, reference.time+stage.mark.clock.markEnd,
    4/5, .silent, by decide, by decide, by norm_num, (hb.rates_positive 0 port).2.1⟩

noncomputable def FirstFirePrefix.errorPhase {theta reference port active epsilon}
    (stage : FirstFirePrefix theta reference port)
    (_hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    LearnedFastPhase theta reference port :=
  ⟨reference.time+stage.mark.clock.fire, reference.time+stage.mark.clock.errorStart,
    1/10, .error, by decide, by decide, by norm_num, (hb.rates_positive 0 port).2.2⟩

theorem FirstFirePrefix.silent_deadline {theta reference port active epsilon}
    (stage : FirstFirePrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    (stage.silentPhase hs hb).deadline = reference.time+stage.mark.clock.errorStart := by
  norm_num [LearnedFastPhase.deadline, silentPhase, auxRate, protectedFloor,
    LearnedClock.errorStart]
  ring

theorem FirstFirePrefix.error_deadline {theta reference port active epsilon}
    (stage : FirstFirePrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    (stage.errorPhase hs hb).deadline = reference.time+stage.mark.clock.auxiliaryEnd := by
  norm_num [LearnedFastPhase.deadline, errorPhase, auxRate, protectedFloor,
    LearnedClock.auxiliaryEnd, a]
  ring

theorem FirstFirePrefix.fast_profile {theta reference port active epsilon}
    (stage : FirstFirePrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    FastProtectedProfile (stage.silentPhase hs hb) true stage.last where
  main := stage.main_fast
  auxiliary := stage.auxiliary_silent
  passive_mode := (stage.mark.silent_profile hs hb).passive_mode
  raw := (stage.mark.silent_profile hs hb).raw
  pending := stage.mark.fired_pending hs hb
  memory := stage.memory
  charge := by
    change stage.mark.fireBefore.x 0 .q =
      Real.exp (-a*((reference.time+stage.mark.clock.fire)-(reference.time+stage.mark.clock.fire)))
    simpa using stage.mark.fire_charge hs hb
  sensor := by
    change frozenValues theta stage.mark.silentState (reference.time+stage.mark.clock.fire) 0 (.m port) = _
    rw [frozen_protected_sensor stage.mark.silent_mode (by decide), stage.mark.silent_charge hs hb]
    rfl
  passive_sensor := by
    intro p hp
    exact (stage.mark.silent_profile hs hb).passive_bound theta
      (stage.mark.silentFlow hs hb).positive.le p hp
  time_lower := by rw [stage.date]; linarith [stage.mark.clock.fire_lower]
  raw_time := by intro _; rw [stage.date]; linarith [stage.mark.clock.fire_upper]

structure AuxiliaryRecovered {theta reference port} (stage : FirstFirePrefix theta reference port) where
  last : Snapshot 1
  execution : Execution theta (fun _ _ => []) stage.last last
  date : last.time = reference.time+stage.mark.clock.auxiliaryEnd
  main : last.main 0 = .fast
  auxiliary : ∀ p, last.aux 0 p = .ready
  raw : ∀ p, last.raw 0 p = none
  pending : last.pending = []
  memory : SameMemory reference last
  charge : last.x 0 .q = Real.exp (-a*(last.time-(reference.time+stage.mark.clock.fire)))
  sensor : ∀ p, |last.x 0 (.m p)-1/40| ≤ 1/100000
  emissions : execution.ledger.emissions = []

noncomputable def FirstFirePrefix.recoverAuxiliary {theta reference port active epsilon}
    (stage : FirstFirePrefix theta reference port)
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    AuxiliaryRecovered stage := by
  have order := stage.mark.clock.chronology hb 0 port (hs.recovery 0)
  let silent := (stage.fast_profile hs hb).advance
    (T := reference.time+stage.mark.clock.errorStart)
    (by rw [stage.date]; linarith [order.fire_before_error])
    (by change reference.time+stage.mark.clock.errorStart ≤ reference.time+stage.mark.clock.fire+1
        linarith [order.error_span, order.auxiliary_end_before_fast_end])
    (le_of_eq (stage.silent_deadline hs hb).symm)
  have hsensor : silent.last.x 0 (.m port) = 1/10 := by
    have hh := silent.profile.at_deadline (silent.date.trans (stage.silent_deadline hs hb).symm)
    simpa [silentPhase, protectedFloor] using hh
  let errorEntry := setAux silent.last 0 port .error
  let errorJump : Jump (fun _ _ => []) silent.last errorEntry :=
    Jump.error _ 0 port silent.profile.auxiliary hsensor
  have hp : FastProtectedProfile (stage.errorPhase hs hb) silent.live errorEntry := by
    exact silent.profile.enter (stage.errorPhase hs hb) rfl silent.date.symm hsensor
  let finish := hp.advance
    (T := reference.time+stage.mark.clock.auxiliaryEnd)
    (by change silent.last.time ≤ _; rw [silent.date]; linarith [order.error_span])
    (by change reference.time+stage.mark.clock.auxiliaryEnd ≤ reference.time+stage.mark.clock.fire+1
        linarith [order.auxiliary_end_before_fast_end])
    (le_of_eq (stage.error_deadline hs hb).symm)
  have hfinish : FastProtectedProfile (stage.errorPhase hs hb) false finish.last := by
    simpa only [finish.raw_cleared (by linarith [order.raw_end_before_auxiliary_end])] using finish.profile
  have hrest : finish.last.x 0 (.m port) = 1/40 := by
    have hh := hfinish.at_deadline (finish.date.trans (stage.error_deadline hs hb).symm)
    simpa [errorPhase, protectedFloor] using hh
  let readyJump : Jump (fun _ _ => []) finish.last (setAux finish.last 0 port .ready) :=
    Jump.auxReady _ 0 port hfinish.auxiliary hrest
  let afterError : Execution theta (fun _ _ => []) errorEntry (setAux finish.last 0 port .ready) :=
    finish.execution.append (.cons (.jump readyJump) (.nil _))
  let run := silent.execution.append (.cons (.jump errorJump) afterError)
  refine ⟨setAux finish.last 0 port .ready, run, finish.date, hfinish.main, ?_, ?_,
    hfinish.pending, hfinish.memory, hfinish.charge, ?_, ?_⟩
  · intro p
    by_cases hp : p = port
    · subst p; simp [setAux]
    · simpa [setAux, hp] using hfinish.passive_mode p hp
  · intro p
    change finish.last.raw 0 p = none
    simpa using hfinish.raw p
  · intro p
    by_cases hp : p = port
    · subst p; change |finish.last.x 0 (.m port)-1/40| ≤ _; rw [hrest]; norm_num
    · exact hfinish.passive_sensor p hp
  · change (silent.execution.append _).ledger.emissions = []
    rw [Execution.append_ledger]
    change silent.execution.ledger.emissions ++ (errorJump.ledger.emissions ++ afterError.ledger.emissions) = []
    rw [silent.emissions]
    change [] ++ (errorJump.ledger.emissions ++ (finish.execution.append _).ledger.emissions) = []
    rw [Execution.append_ledger]
    change [] ++ (errorJump.ledger.emissions ++ (finish.execution.ledger.emissions ++ (readyJump.ledger.emissions ++ []))) = []
    rw [finish.emissions]
    rfl

end KernelR.Hybrid
