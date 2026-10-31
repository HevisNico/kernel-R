import KernelR.LearnedRecovery

/-! Physical FAST/SLOW completion after raw and auxiliary recovery. All sensor
charges and the reserve are carried from the preceding execution, not reset. -/
namespace KernelR.Hybrid
open Set

structure LearnedQuietProfile (reference current : Snapshot 1) : Prop where
  auxiliary : ∀ p, current.aux 0 p = .ready
  raw : ∀ p, current.raw 0 p = none
  pending : current.pending = []
  memory : SameMemory reference current
  sensor : ∀ p, |current.x 0 (.m p)-1/40| ≤ 1/100000

theorem LearnedQuietProfile.frozen {reference current}
    (h : LearnedQuietProfile reference current) (theta : Fin 1 → Parameters)
    {t : ℝ} (ht : current.time ≤ t) : LearnedQuietProfile reference (frozenAt theta current t) where
  auxiliary := h.auxiliary
  raw := h.raw
  pending := h.pending
  memory := h.memory
  sensor := fun p => frozen_idle_sensor_bound (theta := theta) (h.auxiliary p) (h.raw p) (h.sensor p) ht

theorem LearnedQuietProfile.setMain {reference current}
    (h : LearnedQuietProfile reference current) (mode : MainMode) :
    LearnedQuietProfile reference (Hybrid.setMain current 0 mode) :=
  ⟨h.auxiliary, h.raw, h.pending, h.memory, h.sensor⟩

noncomputable def LearnedQuietProfile.flow {reference current theta}
    (h : LearnedQuietProfile reference current) {T : ℝ} (hT : current.time < T)
    (hm : ∀ t ∈ Ico current.time T, match current.main 0 with
      | .ready => frozenValues theta current t 0 .q < 1
      | .fast => 1/4 < frozenValues theta current t 0 .q
      | .slow => 1/10 < frozenValues theta current t 0 .q) :
    Flow theta current (frozenAt theta current T) := by
  have hfrozen : FrozenModes current := by
    constructor
    · intro i p _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i; rw [h.auxiliary p]; decide
    · intro i p ha
      have hi : i = 0 := Subsingleton.elim _ _
      subst i; rw [h.auxiliary p] at ha; cases ha
  apply frozenFlow hfrozen hT
  · intro t ht
    constructor
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i; exact hm t ht
    · intro i p
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [h.auxiliary p]
      have hh := (abs_le.mp (frozen_idle_sensor_bound (theta := theta)
        (h.auxiliary p) (h.raw p) (h.sensor p) ht.1)).2
      linarith
  · intro i p origin hr
    have hi : i = 0 := Subsingleton.elim _ _
    subst i; rw [h.raw p] at hr; cases hr
  · simp [h.pending]

theorem AuxiliaryRecovered.quiet_profile {theta reference port stage}
    (recovered : @AuxiliaryRecovered theta reference port stage) :
    LearnedQuietProfile reference recovered.last :=
  ⟨recovered.auxiliary, recovered.raw, recovered.pending, recovered.memory, recovered.sensor⟩

theorem AuxiliaryRecovered.fast_solution {theta reference port stage}
    (recovered : @AuxiliaryRecovered theta reference port stage) (t : ℝ) :
    frozenValues theta recovered.last t 0 .q =
      Real.exp (-a*(t-(reference.time+stage.mark.clock.fire))) := by
  simp only [frozenValues, frozenBody, frozenMain, recovered.main]
  rw [recovered.charge, ← Real.exp_add]
  congr 1
  ring

structure LearnedReturn (theta : Fin 1 → Parameters) (active : Fin 1 → Port)
    (reference : Snapshot 1) (port : Port) where
  firing : FirstFirePrefix theta reference port
  last : Snapshot 1
  execution : Execution theta (fun _ _ => [])
    (withFuture reference [sourceToken 0 port reference.time]) last
  date : last.time = reference.time+firing.mark.clock.reopen (reference.x 0 .b)
  domain : LearnedDomain theta active reference last
  emissions : execution.ledger.emissions = [(0, reference.time+firing.mark.clock.fire)]

theorem learned_return_exists {theta reference active epsilon}
    (hs : LearnedRest theta active reference) (hb : PhysicalBox theta epsilon) :
    Nonempty (LearnedReturn theta active reference (active 0)) := by
  obtain ⟨stage⟩ := learned_first_fire_prefix hs hb
  let recovered := stage.recoverAuxiliary hs hb
  let quiet := recovered.quiet_profile
  have order := stage.mark.clock.chronology hb 0 (active 0) (hs.recovery 0)
  let fastTime := reference.time+stage.mark.clock.fire+1
  let fastFlow := quiet.flow (theta := theta) (T := fastTime)
    (by rw [recovered.date]; dsimp [fastTime]; linarith [order.auxiliary_end_before_fast_end])
    (by
      intro t ht
      simp only [recovered.main]
      rw [recovered.fast_solution]
      exact fast_exponential_before ht.2)
  let fastBefore := frozenAt theta recovered.last fastTime
  have hfast : fastBefore.x 0 .q = 1/4 := by
    change frozenValues theta recovered.last fastTime 0 .q = 1/4
    rw [recovered.fast_solution]
    simpa [fastTime, add_sub_assoc] using exp_neg_a
  let slowState := setMain fastBefore 0 .slow
  let fastExit : Jump (fun _ _ => []) fastBefore slowState :=
    Jump.fastEnd _ 0 recovered.main hfast
  let slowQuiet : LearnedQuietProfile reference slowState :=
    (quiet.frozen theta (t := fastTime) fastFlow.positive.le).setMain .slow
  have hslow : slowState.main 0 = .slow := by simp [slowState, setMain]
  have hstart : slowState.x 0 .q = 1/4 := hfast
  have hrate : slowState.x 0 .b = reference.x 0 .b := (slowQuiet.memory 0).1
  have hbpos : 0 < reference.x 0 .b := by linarith [(hs.recovery 0).1]
  let returnTime := reference.time+stage.mark.clock.reopen (reference.x 0 .b)
  have elapsed : returnTime-slowState.time = Real.log (5/2) / reference.x 0 .b := by
    change (reference.time+stage.mark.clock.reopen (reference.x 0 .b))-fastTime = _
    dsimp [LearnedClock.reopen, fastTime]
    ring
  let slowFlow := slowQuiet.flow (theta := theta) (T := returnTime)
    (by change fastTime < returnTime; dsimp [fastTime, returnTime]; linarith [order.fast_end_before_reopen])
    (by
      intro t ht
      simp only [hslow, frozenValues, frozenBody, frozenMain, hstart, hrate]
      apply decay_section_before (by norm_num) (by norm_num) hbpos
      norm_num
      linarith [ht.2, elapsed])
  let beforeReturn := frozenAt theta slowState returnTime
  have hreturn : beforeReturn.x 0 .q = 1/10 := by
    change frozenValues theta slowState returnTime 0 .q = _
    simp only [frozenValues, frozenBody, frozenMain, hslow, hstart, hrate]
    rw [elapsed]
    have he := decay_section_endpoint (initial := 1/4) (final := 1/10)
      (by norm_num) (by norm_num) hbpos
    norm_num at he ⊢
    exact he
  let reopening : Jump (fun _ _ => []) beforeReturn (setMain beforeReturn 0 .ready) :=
    Jump.reopen _ 0 hslow hreturn
  let last := setMain beforeReturn 0 .ready
  let finalQuiet : LearnedQuietProfile reference last :=
    (slowQuiet.frozen theta (t := returnTime) slowFlow.positive.le).setMain .ready
  let tail : Execution theta (fun _ _ => []) stage.last last :=
    recovered.execution.append (.cons (.flow fastFlow) (.cons (.jump fastExit)
      (.cons (.flow slowFlow) (.cons (.jump reopening) (.nil _)))))
  let run := stage.execution.append tail
  have hrest : LearnedRest theta active last := by
    constructor
    · intro i; have hi : i = 0 := Subsingleton.elim _ _; subst i; simp [last, setMain]
    · intro i p; have hi : i = 0 := Subsingleton.elim _ _; subst i; exact finalQuiet.auxiliary p
    · intro i p; have hi : i = 0 := Subsingleton.elim _ _; subst i; exact finalQuiet.raw p
    · exact finalQuiet.pending
    · intro i; have hi : i = 0 := Subsingleton.elim _ _; subst i; exact hreturn
    · intro i p; have hi : i = 0 := Subsingleton.elim _ _; subst i; exact finalQuiet.sensor p
    · intro i; have hi : i = 0 := Subsingleton.elim _ _; subst i
      exact run.reserve_invariant 0 (hs.reserve 0) (run.actual_work_bound hb hs.upper_region hs.cap 0)
    · intro i; rw [(finalQuiet.memory i).2 (active i)]; exact hs.gain i
    · intro i p; rw [(finalQuiet.memory i).2 p]; exact hs.cap i p
    · intro i; rw [(finalQuiet.memory i).1]; exact hs.recovery i
  refine ⟨⟨stage, last, run, rfl, ⟨hrest, finalQuiet.memory⟩, ?_⟩⟩
  have htail : tail.ledger.emissions = [] := by
    change (recovered.execution.append _).ledger.emissions = []
    rw [Execution.append_ledger]
    change recovered.execution.ledger.emissions ++ _ = []
    rw [recovered.emissions]
    rfl
  change (stage.execution.append tail).ledger.emissions = _
  calc
    _ = stage.execution.ledger.emissions ++ tail.ledger.emissions :=
      congrArg (fun ledger => ledger.emissions) (Execution.append_ledger stage.execution tail)
    _ = _ := by rw [stage.emissions, htail, List.append_nil]

end KernelR.Hybrid
