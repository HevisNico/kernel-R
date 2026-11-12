import Teaching.FrozenWorkFlow
import Teaching.TeacherStableClock

/-! Construct the physical work-pulse history with both learning gates closed
at their caps. The work sensor still makes its real MARK and SILENT jumps. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

structure CappedWorkFrame (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port) : Prop where
  recovery : s.x 0 .b = 11 / 10
  gain : s.x 0 (.z p) = Real.log ((θ 0).cap p)
  others : ∀ q, q ≠ p → s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)) ∧ s.raw 0 q = none
  empty : s.pending = []

private theorem work_aux_absent {θ : Fin 1 → Parameters} {s : Snapshot 1} {q : Port} {t : ℝ}
    (ready : s.aux 0 q = .ready) (raw : s.raw 0 q = none) :
    cellOrbitValues θ s t 0 (.m q) = relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t := by
  simp [cellOrbitValues, cellBaseValues, ready, cellAuxAmplitude, current, raw, auxPulse_zero_eq_relax]

private theorem work_aux_origin {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port} {t : ℝ}
    (ready : s.aux 0 p = .ready) (raw : s.raw 0 p = some s.time) :
    cellOrbitValues θ s t 0 (.m p) = auxPulse (s.x 0 (.m p)) ((θ 0).inputGain p) s.time t := by
  have nonzero : a ≠ 0 := by linarith [a_coarse_bounds.1]
  simp [cellOrbitValues, cellBaseValues, ready, cellAuxAmplitude, current, raw, pulse, nonzero]

private theorem work_aux_decay {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port} {t : ℝ}
    (modeCases : s.aux 0 p ≠ .ready) :
    cellOrbitValues θ s t 0 (.m p) =
      s.x 0 (.m p) * Real.exp (-protectedReadyRate (θ 0) p (s.aux 0 p) * (t - s.time)) := by
  simp [cellOrbitValues, cellBaseValues, modeCases]

private theorem work_slow_charge {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port} {t : ℝ}
    (frame : CappedWorkFrame θ s p) (slow : s.main 0 = .slow) :
    cellOrbitValues θ s t 0 .q = s.x 0 .q * Real.exp (-(11 / 10) * (t - s.time)) := by
  simp [cellOrbitValues, cellBaseValues, slow, frame.recovery]

private theorem CappedWorkFrame.at_flow_end {θ s p} (frame : CappedWorkFrame θ s p) {T : ℝ}
    (later : s.time ≤ T) : CappedWorkFrame θ (frozenWorkEnd θ s T) p := by
  refine ⟨frame.recovery, frame.gain, ?_, frame.empty⟩
  intro q different
  obtain ⟨ready, rest, raw⟩ := frame.others q different
  refine ⟨ready, ?_, raw⟩
  change RestBand (cellOrbitValues θ s T 0 (.m q))
  rw [work_aux_absent ready raw]
  exact relax_mem_Icc (by norm_num) later rest (by constructor <;> norm_num)

private theorem CappedWorkFrame.setAux {θ s p} (frame : CappedWorkFrame θ s p) (mode : AuxMode) :
    CappedWorkFrame θ (setAux s 0 p mode) p := by
  refine ⟨frame.recovery, frame.gain, ?_, frame.empty⟩
  intro q different
  simpa [KernelR.Hybrid.setAux, different] using frame.others q different

private theorem CappedWorkFrame.setMain {θ s p} (frame : CappedWorkFrame θ s p) (mode : MainMode) :
    CappedWorkFrame θ (setMain s 0 mode) p :=
  ⟨frame.recovery, frame.gain, frame.others, frame.empty⟩

private theorem CappedWorkFrame.expire {θ s p} (frame : CappedWorkFrame θ s p) :
    CappedWorkFrame θ (setRaw s 0 p none) p := by
  refine ⟨frame.recovery, frame.gain, ?_, frame.empty⟩
  intro q different
  simpa [setRaw, different] using frame.others q different

private noncomputable def CappedWorkFrame.leg {θ s p} (frame : CappedWorkFrame θ s p) {T : ℝ}
    (later : s.time < T)
    (support : ∀ origin, s.raw 0 p = some origin → origin ≤ s.time ∧ T ≤ origin + 1)
    (main : ∀ t ∈ Ico s.time T,
      match s.main 0 with
      | .ready => cellOrbitValues θ s t 0 .q < 1
      | .fast => 1 / 4 < cellOrbitValues θ s t 0 .q
      | .slow => 1 / 10 < cellOrbitValues θ s t 0 .q)
    (sensor : ∀ t ∈ Ico s.time T,
      match s.aux 0 p with
      | .ready => cellOrbitValues θ s t 0 (.m p) < 1
      | .mark => 4 / 5 < cellOrbitValues θ s t 0 (.m p)
      | .silent => 1 / 10 < cellOrbitValues θ s t 0 (.m p)
      | .error => 1 / 40 < cellOrbitValues θ s t 0 (.m p)) :
    Flow θ s (frozenWorkEnd θ s T) := by
  apply frozenWorkFlow s later ?_ ?_ ?_ ?_ (by simp [frame.empty])
  · intro i q
    rw [Subsingleton.elim i 0]
    by_cases eq : q = p
    · subst q; exact Or.inr (Or.inr frame.gain.ge)
    · exact Or.inr (Or.inl (by rw [(frame.others q eq).1]; decide))
  · intro i q
    rw [Subsingleton.elim i 0]
    exact Or.inr (Or.inr frame.recovery.ge)
  · intro i q origin raw
    rw [Subsingleton.elim i 0] at raw
    by_cases eq : q = p
    · subst q; exact support origin raw
    · rw [(frame.others q eq).2.2] at raw; contradiction
  · intro t ht
    constructor
    · intro i
      rw [Subsingleton.elim i 0]
      exact main t ht
    · intro i q
      rw [Subsingleton.elim i 0]
      by_cases eq : q = p
      · subst q; exact sensor t ht
      · obtain ⟨ready, rest, raw⟩ := frame.others q eq
        rw [ready, work_aux_absent ready raw]
        exact relax_lt (by norm_num) ht.1 (by linarith [rest.2]) (by norm_num)

structure CappedWorkReopening (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) (age : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  transverse : execution.ContactsTransversal
  date : final.time = s.time + age
  charge : final.x 0 .q = 1 / 10
  ready : final.main 0 = .ready
  frame : CappedWorkFrame θ final p
  active : final.raw 0 p = some s.time
  silent : final.aux 0 p = .silent
  silentStart : ℝ
  silentBounds : s.time < silentStart ∧ silentStart < s.time + 1 / 20
  errorBounds : s.time + 99 / 100 < silentStart + Real.log 8 / (θ 0).ls p ∧
    silentStart + Real.log 8 / (θ 0).ls p < s.time + 123 / 100
  cycleBounds : s.time + 1 < silentStart + Real.log 8 / (θ 0).ls p + Real.log 4 / (θ 0).le p ∧
    silentStart + Real.log 8 / (θ 0).ls p + Real.log 4 / (θ 0).le p < s.time + 419 / 300
  sensor : final.x 0 (.m p) = (4 / 5 : ℝ) *
    Real.exp (-(θ 0).ls p * (final.time - silentStart))
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  gains : ∀ q, final.x 0 (.z q) = s.x 0 (.z q)

/-- Starting at work admission, construct MARK at the recovery cap and
reopen at the exact SLOW guard, with the canonical work pulse still active. -/
theorem capped_work_reopening_exists {θ ε route s p age} (box : @PhysicalBox 1 θ ε)
    (frame : CappedWorkFrame θ s p) (slow : s.main 0 = .slow)
    (charge : s.x 0 .q = (1 / 10 : ℝ) * Real.exp ((11 / 10) * age))
    (timing : CappedWorkTiming ε age) (active : s.raw 0 p = some s.time)
    (ready : s.aux 0 p = .ready) (rest : RestBand (s.x 0 (.m p))) :
    Nonempty (CappedWorkReopening θ route s p age) := by
  have ageBand : 53 / 100 ≤ age ∧ age ≤ 59 / 100 := by
    rcases timing with h | ⟨_, h⟩
    · constructor <;> linarith [h.1, h.2]
    · exact h
  obtain ⟨latency, early, deadline, root, prior, slope⟩ :=
    box.first_sensor_crossing_transversal 0 p rest.1 rest.2
  let M := s.time + latency
  let P := M + Real.log (5 / 4) / (θ 0).lm p
  let W := s.time + age
  have mAfter : s.time < M := by dsimp [M]; linarith
  have pAfter : M < P := by dsimp [P]; linarith [(box.aux_durations_lower 0 p).1]
  have pBefore : P < s.time + 1 / 20 := by dsimp [P, M]; linarith [box.mark_duration_upper 0 p]
  have pBeforeW : P < W := by dsimp [W]; linarith [ageBand.1]
  have wBeforeExpiry : W < s.time + 1 := by dsimp [W]; linarith [ageBand.2]
  have clock (t : ℝ) :
      s.x 0 .q * Real.exp (-(11 / 10) * (t - s.time)) =
        (1 / 10 : ℝ) * Real.exp ((11 / 10) * (W - t)) := by
    rw [charge, mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [W]
    ring
  have above (t : ℝ) (before : t < W) : (1 / 10 : ℝ) <
      (1 / 10 : ℝ) * Real.exp ((11 / 10) * (W - t)) := by
    have h := Real.one_lt_exp_iff.mpr (show 0 < (11 / 10 : ℝ) * (W - t) by linarith)
    linarith
  have support (T : ℝ) (endBefore : T ≤ s.time + 1) (origin : ℝ)
      (raw : s.raw 0 p = some origin) : origin ≤ s.time ∧ T ≤ origin + 1 := by
    rw [active] at raw
    cases Option.some.inj raw
    exact ⟨le_rfl, endBefore⟩
  let m := frozenWorkEnd θ s M
  let f₁ : Flow θ s m := frame.leg mAfter (support M (by linarith))
    (fun t ht => by rw [slow, work_slow_charge frame slow, clock]; exact above t (ht.2.trans (pAfter.trans pBeforeW)))
    (fun t ht => by rw [ready, work_aux_origin ready active]; exact prior t ht)
  have hm : m.x 0 (.m p) = 1 := by
    change cellOrbitValues θ s M 0 (.m p) = 1
    rw [work_aux_origin ready active]
    exact root
  let marking := setAux m 0 p .mark
  let first : Execution θ route s marking :=
    .cons (.flow f₁) (.cons (.jump (.mark m 0 p ready hm)) (.nil _))
  have marked : marking.aux 0 p = .mark := by simp [marking, setAux]
  have fm : CappedWorkFrame θ marking p := (frame.at_flow_end mAfter.le).setAux _
  have markedQ : marking.x 0 .q = (1 / 10 : ℝ) * Real.exp ((11 / 10) * (W - M)) := by
    change cellOrbitValues θ s M 0 .q = _
    rw [work_slow_charge frame slow, clock]
  have clockM (t : ℝ) : cellOrbitValues θ marking t 0 .q =
      (1 / 10 : ℝ) * Real.exp ((11 / 10) * (W - t)) := by
    rw [work_slow_charge fm slow, markedQ, mul_assoc, ← Real.exp_add]
    congr 2
    change (11 / 10 : ℝ) * (W - M) + -(11 / 10) * (t - M) = _
    ring
  have markDecay := protected_decay_schedule (initial := (1 : ℝ)) (floor := (4 / 5 : ℝ))
    (by norm_num) (by norm_num) (box.rates_positive 0 p).1
  let mEnd := frozenWorkEnd θ marking P
  let f₂ : Flow θ marking mEnd := fm.leg pAfter
    (by intro o h; change s.raw 0 p = some o at h
        obtain ⟨lo, hi⟩ := support P (by linarith) o h
        exact ⟨lo.trans mAfter.le, hi⟩)
    (fun t ht => by rw [show marking.main 0 = .slow from slow, clockM]; exact above t (ht.2.trans pBeforeW))
    (fun t ht => by
      rw [marked, work_aux_decay (by rw [marked]; decide), marked]
      have markValue : marking.x 0 (.m p) = 1 := hm
      rw [markValue]
      change (4 / 5 : ℝ) < 1 * Real.exp (-(θ 0).lm p * (t - M))
      apply markDecay.2.2
      · exact sub_nonneg.mpr ht.1
      · have endBefore : t < M + Real.log (5 / 4) / (θ 0).lm p := ht.2
        have h : Real.log ((1 : ℝ) / (4 / 5)) = Real.log (5 / 4) := by norm_num
        rw [h]
        linarith)
  have mFloor : mEnd.x 0 (.m p) = 4 / 5 := by
    change cellOrbitValues θ marking P 0 (.m p) = _
    rw [work_aux_decay (by rw [marked]; decide), marked]
    have markValue : marking.x 0 (.m p) = 1 := hm
    rw [markValue]
    change 1 * Real.exp (-(θ 0).lm p * (P - M)) = _
    rw [show P - M = Real.log ((1 : ℝ) / (4 / 5)) / (θ 0).lm p by dsimp [P]; norm_num]
    exact markDecay.2.1
  let silenced := setAux mEnd 0 p .silent
  let second : Execution θ route marking silenced :=
    .cons (.flow f₂) (.cons (.jump (.silent mEnd 0 p marked mFloor)) (.nil _))
  have silentMode : silenced.aux 0 p = .silent := by simp [silenced, setAux]
  have fs : CappedWorkFrame θ silenced p := (fm.at_flow_end pAfter.le).setAux _
  have silentQ : silenced.x 0 .q = (1 / 10 : ℝ) * Real.exp ((11 / 10) * (W - P)) := clockM P
  have clockP (t : ℝ) : cellOrbitValues θ silenced t 0 .q =
      (1 / 10 : ℝ) * Real.exp ((11 / 10) * (W - t)) := by
    rw [work_slow_charge fs slow, silentQ, mul_assoc, ← Real.exp_add]
    congr 2
    change (11 / 10 : ℝ) * (W - P) + -(11 / 10) * (t - P) = _
    ring
  have silentDecay := protected_decay_schedule (initial := (4 / 5 : ℝ)) (floor := (1 / 10 : ℝ))
    (by norm_num) (by norm_num) (box.rates_positive 0 p).2.1
  let beforeReturn := frozenWorkEnd θ silenced W
  let f₃ : Flow θ silenced beforeReturn := fs.leg pBeforeW
    (by intro o h; change s.raw 0 p = some o at h
        obtain ⟨lo, hi⟩ := support W wBeforeExpiry.le o h
        exact ⟨lo.trans (mAfter.trans pAfter).le, hi⟩)
    (fun t ht => by rw [show silenced.main 0 = .slow from slow, clockP]; exact above t ht.2)
    (fun t ht => by
      rw [silentMode, work_aux_decay (by rw [silentMode]; decide), silentMode]
      have silentValue : silenced.x 0 (.m p) = 4 / 5 := mFloor
      rw [silentValue]
      change (1 / 10 : ℝ) < (4 / 5) * Real.exp (-(θ 0).ls p * (t - P))
      have range := (box.aux_durations_lower 0 p).2.1
      apply silentDecay.2.2
      · exact sub_nonneg.mpr ht.1
      · norm_num
        change P ≤ t ∧ t < W at ht
        have pStart : s.time < P := mAfter.trans pAfter
        dsimp [W] at ht
        linarith [ht.2, ageBand.2])
  have qFloor : beforeReturn.x 0 .q = 1 / 10 := by
    change cellOrbitValues θ silenced W 0 .q = _
    rw [clockP]
    simp
  let final := setMain beforeReturn 0 .ready
  let third : Execution θ route silenced final :=
    .cons (.flow f₃) (.cons (.jump (.reopen beforeReturn 0 slow qFloor)) (.nil _))
  let execution := (first.append second).append third
  have crossFirst : first.ContactsTransversal := by
    simp only [first, Execution.ContactsTransversal, Jump.ContactTransversal, and_true]
    exact f₁.aux_contact_field_positive 0 p ready active (pAfter.trans (pBeforeW.trans wBeforeExpiry))
      (by change 0 < deriv (auxPulse (s.x 0 (.m p)) ((θ 0).inputGain p) s.time) (s.time + latency); exact slope)
  have schedule := box.first_cycle_schedule 0 p ⟨early, deadline⟩
  refine ⟨⟨final, execution, ?_, rfl, qFloor, by simp [final, setMain],
    (fs.at_flow_end pBeforeW.le).setMain _, active, silentMode, P, ⟨mAfter.trans pAfter, pBefore⟩,
    ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩⟩
  · exact (Execution.contactsTransversal_append _ _).2
      ⟨(Execution.contactsTransversal_append _ _).2 ⟨crossFirst, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩
  · dsimp [P, M]
    constructor <;> linarith [schedule.2.2.1, schedule.2.2.2.1]
  · dsimp [P, M, auxCycleDuration] at *
    constructor <;> linarith [schedule.2.2.2.2.1, schedule.2.2.2.2.2]
  · change cellOrbitValues θ silenced W 0 (.m p) = _
    rw [work_aux_decay (by rw [silentMode]; decide), silentMode]
    have silentValue : silenced.x 0 (.m p) = 4 / 5 := mFloor
    rw [silentValue]
    rfl
  · simp [execution, first, second, third, Execution.emissions_append, Execution.ledger, Move.ledger,
      Flow.ledger, Jump.ledger, Ledger.add, Ledger.zero]
  · simp [execution, first, second, third, Execution.deliveries_append, Execution.deliveries,
      Move.deliveries, Jump.deliveries]

private noncomputable def rawWorkCharge (cap origin reopen t : ℝ) : ℝ :=
  readyPulse (1 / 10) (cap * Real.exp (-a * (reopen - origin))) reopen t

private noncomputable def workCharge (cap origin reopen t : ℝ) : ℝ :=
  if t < origin + 1 then rawWorkCharge cap origin reopen t
  else relax (1 / 2) (1 / 10) (rawWorkCharge cap origin reopen (origin + 1)) (origin + 1) t

private theorem raw_work_shift (cap origin reopen t : ℝ) :
    rawWorkCharge cap origin reopen t = cappedWorkTail cap (reopen - origin) (t - origin) := by
  unfold rawWorkCharge cappedWorkTail readyPulse
  rw [show t - origin - (reopen - origin) = t - reopen by ring]

private theorem workCharge_before_expiry (cap origin reopen t : ℝ) (ht : t ≤ origin + 1) :
    workCharge cap origin reopen t = rawWorkCharge cap origin reopen t := by
  rcases ht.eq_or_lt with rfl | before
  · simp [workCharge, relax_initial]
  · simp [workCharge, before]

private theorem work_charge_guard {θ ε origin reopen} (box : @PhysicalBox 1 θ ε) (p : Port)
    (timing : CappedWorkTiming ε (reopen - origin)) {t : ℝ} (after : reopen ≤ t) :
    workCharge ((θ 0).cap p) origin reopen t < 1 := by
  have estimate := capped_work_tail_precharge box 0 p timing
  by_cases before : t < origin + 1
  · rw [workCharge_before_expiry _ _ _ _ before.le, raw_work_shift]
    exact estimate.1 (t - origin) ⟨by linarith, by linarith⟩
  · rw [workCharge, ite_eq_right before]
    apply relax_lt (by norm_num) (le_of_not_gt before) _ (by norm_num)
    rw [raw_work_shift, add_sub_cancel_left]
    apply estimate.1
    constructor
    · rcases timing with h | ⟨_,h⟩ <;> linarith [h.2]
    · rfl

private theorem active_work_amplitude {θ ε s p origin} (box : @PhysicalBox 1 θ ε)
    (frame : CappedWorkFrame θ s p) (raw : s.raw 0 p = some origin)
    (valid : origin ≤ s.time ∧ s.time < origin + 1) :
    cellMainAmplitude s 0 = (θ 0).cap p * Real.exp (-a * (s.time - origin)) := by
  unfold cellMainAmplitude
  rw [Finset.sum_eq_single p]
  · simp [current, raw, pulse, valid, frame.gain, Real.exp_log (box.cap_positive 0 p)]
    have ha : a ≠ 0 := by linarith [a_coarse_bounds.1]
    field_simp [ha]
    simp
  · intro q _ different
    simp [current, (frame.others q different).2.2]
  · simp

private theorem no_work_amplitude {θ s p} (frame : CappedWorkFrame θ s p)
    (raw : s.raw 0 p = none) : cellMainAmplitude s 0 = 0 := by
  unfold cellMainAmplitude
  apply Finset.sum_eq_zero
  intro q _
  by_cases eq : q = p
  · subst q; simp [current, raw]
  · simp [current, (frame.others q eq).2.2]

private theorem ready_work_clock {θ ε s p origin reopen} (box : @PhysicalBox 1 θ ε)
    (frame : CappedWorkFrame θ s p) (ready : s.main 0 = .ready) (originBefore : origin ≤ s.time)
    (q : s.x 0 .q = workCharge ((θ 0).cap p) origin reopen s.time) {T : ℝ}
    (support : (s.raw 0 p = some origin ∧ s.time < origin + 1 ∧ T ≤ origin + 1) ∨
      (s.raw 0 p = none ∧ origin + 1 ≤ s.time))
    (t : ℝ) (range : t ∈ Icc s.time T) :
    cellOrbitValues θ s t 0 .q = workCharge ((θ 0).cap p) origin reopen t := by
  simp only [cellOrbitValues, cellBaseValues, ready]
  rw [q]
  rcases support with ⟨raw, before, last⟩ | ⟨raw, past⟩
  · rw [active_work_amplitude box frame raw ⟨originBefore, before⟩,
      workCharge_before_expiry _ _ _ _ before.le,
      workCharge_before_expiry _ _ _ _ (range.2.trans last)]
    unfold rawWorkCharge
    rw [show (θ 0).cap p * Real.exp (-a * (s.time - origin)) =
      ((θ 0).cap p * Real.exp (-a * (reopen - origin))) *
        Real.exp (-a * (s.time - reopen)) by rw [mul_assoc, attenuation_split]]
    exact readyPulse_restart _ _ _ _ _
  · rw [no_work_amplitude frame raw, readyPulse_zero_eq_relax]
    simp only [workCharge, ite_eq_right (not_lt.mpr (past.trans range.1)),
      ite_eq_right (not_lt.mpr past)]
    unfold relax
    simp only [add_sub_cancel_left]
    rw [mul_assoc, attenuation_split]

private noncomputable def workProtectedFloor (mode : AuxMode) : ℝ :=
  if mode = .silent then 1 / 10 else 1 / 40

private structure WorkAuxSpan (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) (origin reopen T anchor initial : ℝ) (mode : AuxMode) where
  final : Snapshot 1
  execution : Execution θ route s final
  date : final.time = T
  ready : final.main 0 = .ready
  frame : CappedWorkFrame θ final p
  aux : final.aux 0 p = mode
  charge : final.x 0 .q = workCharge ((θ 0).cap p) origin reopen T
  sensor : final.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (T - anchor))
  transverse : execution.ContactsTransversal
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  gains : ∀ q, final.x 0 (.z q) = s.x 0 (.z q)

private theorem work_aux_leg {θ ε route s p origin reopen T anchor initial mode}
    (box : @PhysicalBox 1 θ ε) (frame : CappedWorkFrame θ s p)
    (timing : CappedWorkTiming ε (reopen - origin))
    (ready : s.main 0 = .ready) (aux : s.aux 0 p = mode)
    (modeCases : mode = .silent ∨ mode = .error)
    (q : s.x 0 .q = workCharge ((θ 0).cap p) origin reopen s.time)
    (m : s.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (s.time - anchor)))
    (past : reopen ≤ s.time) (originPast : origin ≤ s.time) (anchorPast : anchor ≤ s.time)
    (later : s.time < T)
    (support : (s.raw 0 p = some origin ∧ s.time < origin + 1 ∧ T ≤ origin + 1) ∨
      (s.raw 0 p = none ∧ origin + 1 ≤ s.time))
    (initialAbove : workProtectedFloor mode < initial)
    (limit : T ≤ anchor + Real.log (initial / workProtectedFloor mode) / protectedReadyRate (θ 0) p mode) :
    ∃ span : WorkAuxSpan θ route s p origin reopen T anchor initial mode,
      span.final.raw 0 p = s.raw 0 p := by
  -- A leg may end at raw expiry with the old token still installed.  Its
  -- jump is handled by the enclosing phase constructor.
  have hfloor : 0 < workProtectedFloor mode := by rcases modeCases with rfl | rfl <;> norm_num [workProtectedFloor]
  have hrate : 0 < protectedReadyRate (θ 0) p mode := by
    rcases modeCases with rfl | rfl
    · exact (box.rates_positive 0 p).2.1
    · exact (box.rates_positive 0 p).2.2
  have notReady : s.aux 0 p ≠ .ready := by rw [aux]; rcases modeCases with rfl | rfl <;> decide
  have sensorClock (t : ℝ) : cellOrbitValues θ s t 0 (.m p) =
      initial * Real.exp (-protectedReadyRate (θ 0) p mode * (t - anchor)) := by
    rw [work_aux_decay notReady, aux, m, mul_assoc, attenuation_split]
  let flow := frame.leg later
    (by intro o h
        rcases support with ⟨raw, _, endBefore⟩ | ⟨raw, _⟩
        · rw [raw] at h; cases Option.some.inj h; exact ⟨originPast, endBefore⟩
        · rw [raw] at h; contradiction)
    (by intro t ht
        rw [ready, ready_work_clock box frame ready originPast q support t ⟨ht.1, ht.2.le⟩]
        exact work_charge_guard box p timing (past.trans ht.1))
    (by intro t ht
        have strict := (protected_decay_schedule hfloor initialAbove hrate).2.2 (t - anchor)
          (by linarith [ht.1]) (by linarith [ht.2])
        rw [aux, sensorClock]
        rcases modeCases with rfl | rfl <;> simpa [workProtectedFloor] using strict)
  let endState := frozenWorkEnd θ s T
  exact ⟨⟨endState, .cons (.flow flow) (.nil _), rfl, ready, frame.at_flow_end later.le,
    aux, ready_work_clock box frame ready originPast q support T ⟨later.le, le_rfl⟩,
    sensorClock T, trivial, rfl, rfl, fun _ => rfl⟩, rfl⟩

private noncomputable def WorkAuxSpan.expire {θ route s p origin reopen T anchor initial mode}
    (span : WorkAuxSpan θ route s p origin reopen T anchor initial mode)
    (raw : span.final.raw 0 p = some origin) (date : T = origin + 1) :
    WorkAuxSpan θ route s p origin reopen T anchor initial mode :=
  { span with
    final := setRaw span.final 0 p none
    execution := span.execution.append (.cons (.jump (.rawEnd _ 0 p origin raw (span.date.trans date))) (.nil _))
    frame := span.frame.expire
    transverse := (Execution.contactsTransversal_append _ _).2 ⟨span.transverse, trivial, trivial⟩
    emissions := by rw [Execution.emissions_append, span.emissions]; rfl
    deliveries := by rw [Execution.deliveries_append, span.deliveries]; rfl }

private noncomputable def WorkAuxSpan.append {θ route s p origin reopen M T anchor initial mode}
    (first : WorkAuxSpan θ route s p origin reopen M anchor initial mode)
    (last : WorkAuxSpan θ route first.final p origin reopen T anchor initial mode) :
    WorkAuxSpan θ route s p origin reopen T anchor initial mode :=
  { last with
    execution := first.execution.append last.execution
    transverse := (Execution.contactsTransversal_append _ _).2 ⟨first.transverse, last.transverse⟩
    emissions := by rw [Execution.emissions_append, first.emissions, last.emissions]; rfl
    deliveries := by rw [Execution.deliveries_append, first.deliveries, last.deliveries]; rfl
    gains := fun q => (last.gains q).trans (first.gains q) }

private theorem work_aux_phase {θ ε route s p origin reopen T anchor initial mode}
    (box : @PhysicalBox 1 θ ε) (frame : CappedWorkFrame θ s p)
    (timing : CappedWorkTiming ε (reopen - origin))
    (ready : s.main 0 = .ready) (aux : s.aux 0 p = mode)
    (modeCases : mode = .silent ∨ mode = .error)
    (q : s.x 0 .q = workCharge ((θ 0).cap p) origin reopen s.time)
    (m : s.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (s.time - anchor)))
    (past : reopen ≤ s.time) (originPast : origin ≤ s.time) (anchorPast : anchor ≤ s.time)
    (later : s.time < T)
    (raw : s.raw 0 p = if s.time < origin + 1 then some origin else none)
    (initialAbove : workProtectedFloor mode < initial)
    (limit : T ≤ anchor + Real.log (initial / workProtectedFloor mode) / protectedReadyRate (θ 0) p mode) :
    ∃ span : WorkAuxSpan θ route s p origin reopen T anchor initial mode,
      span.final.raw 0 p = if T < origin + 1 then some origin else none := by
  by_cases active : s.time < origin + 1
  · rw [ite_eq_left active] at raw
    by_cases before : T < origin + 1
    · obtain ⟨span, endRaw⟩ := work_aux_leg (route := route) box frame timing ready aux modeCases q m past originPast anchorPast
        later (Or.inl ⟨raw, active, before.le⟩) initialAbove limit
      exact ⟨span, by rw [endRaw, raw, ite_eq_left before]⟩
    · obtain ⟨first, firstRaw⟩ := work_aux_leg (route := route) box frame timing ready aux modeCases q m past originPast anchorPast
        active (Or.inl ⟨raw, active, le_rfl⟩) initialAbove (by linarith)
      let expired := first.expire (firstRaw.trans raw) rfl
      have expiredRaw : expired.final.raw 0 p = none := by simp [expired, WorkAuxSpan.expire, setRaw]
      rcases (le_of_not_gt before).eq_or_lt with eq | after
      · subst T
        exact ⟨expired, by simp [expiredRaw]⟩
      · obtain ⟨last, lastRaw⟩ := work_aux_leg (route := route) box expired.frame timing expired.ready expired.aux modeCases
          (by rw [expired.date]; exact expired.charge) (by rw [expired.date]; exact expired.sensor)
          (by rw [expired.date]; linarith) (by rw [expired.date]; linarith)
          (by rw [expired.date]; linarith) (by rw [expired.date]; exact after)
          (Or.inr ⟨expiredRaw, expired.date.ge⟩) initialAbove limit
        exact ⟨expired.append last, by simpa [WorkAuxSpan.append, before, expiredRaw] using lastRaw⟩
  · rw [ite_eq_right active] at raw
    obtain ⟨span, endRaw⟩ := work_aux_leg (route := route) box frame timing ready aux modeCases q m past originPast anchorPast
      later (Or.inr ⟨raw, le_of_not_gt active⟩) initialAbove limit
    exact ⟨span, by rw [endRaw, raw, ite_eq_right (by linarith)]⟩

structure CappedWorkPrecharge (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1)
    (p : Port) where
  final : Snapshot 1
  execution : Execution θ route s final
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution (s.time + 7 / 5)
  ready : final.main 0 = .ready
  frame : CappedWorkFrame θ final p
  auxiliary : ∀ q, final.aux 0 q = .ready ∧ RestBand (final.x 0 (.m q))
  rawNone : ∀ q, final.raw 0 q = none
  charge : 13 / 20 ≤ final.x 0 .q ∧ final.x 0 .q ≤ 39 / 50
  gains : ∀ q, final.x 0 (.z q) = s.x 0 (.z q)
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []

/-- A complete constructed work pulse at capped recovery and work gain.
RAW can expire before, during or exactly at the start of ERROR.
The precharge requires only the work pulse and has no FIRE. -/
theorem capped_work_precharge_exists {θ ε route s p age} (box : @PhysicalBox 1 θ ε)
    (frame : CappedWorkFrame θ s p) (slow : s.main 0 = .slow)
    (charge : s.x 0 .q = (1 / 10 : ℝ) * Real.exp ((11 / 10) * age))
    (timing : CappedWorkTiming ε age) (active : s.raw 0 p = some s.time)
    (ready : s.aux 0 p = .ready) (rest : RestBand (s.x 0 (.m p))) :
    Nonempty (CappedWorkPrecharge θ route s p) := by
  obtain ⟨reopen⟩ := capped_work_reopening_exists (route := route) box frame slow charge timing active ready rest
  let W := reopen.final.time
  let P := reopen.silentStart
  let E := P + Real.log 8 / (θ 0).ls p
  let R := E + Real.log 4 / (θ 0).le p
  let T := s.time + 7 / 5
  have ageBounds : 53 / 100 ≤ age ∧ age ≤ 59 / 100 := by
    rcases timing with h | ⟨_, h⟩
    · constructor <;> linarith [h.1, h.2]
    · exact h
  have date : W = s.time + age := reopen.date
  have relative : CappedWorkTiming ε (W - s.time) := by rw [date, add_sub_cancel_left]; exact timing
  have wBefore : W < s.time + 1 := by rw [date]; linarith [ageBounds.2]
  have wAfter : s.time ≤ W := by rw [date]; linarith [ageBounds.1]
  have pBefore : P ≤ W := by
    have h : P < s.time + 1 / 20 := reopen.silentBounds.2
    rw [date]
    linarith [ageBounds.1]
  have eLater : W < E := by
    have h : s.time + 99 / 100 < E := reopen.errorBounds.1
    rw [date]
    linarith [ageBounds.2]
  have rLater : E < R := by dsimp [R]; linarith [(box.aux_durations_lower 0 p).2.2]
  have rAfterExpiry : s.time + 1 < R := reopen.cycleBounds.1
  have rBefore : R < T := by
    have h : R < s.time + 419 / 300 := reopen.cycleBounds.2
    dsimp [T]
    linarith
  have initialQ : reopen.final.x 0 .q = workCharge ((θ 0).cap p) s.time W W := by
    rw [reopen.charge, workCharge_before_expiry _ _ _ _ wBefore.le, rawWorkCharge, readyPulse_initial]
  obtain ⟨silent, silentRaw⟩ := work_aux_phase (route := route) box reopen.frame relative reopen.ready reopen.silent (Or.inl rfl)
    initialQ (show reopen.final.x 0 (.m p) = (4 / 5 : ℝ) *
      Real.exp (-protectedReadyRate (θ 0) p .silent * (W - P)) from reopen.sensor)
    le_rfl wAfter pBefore eLater (by rw [ite_eq_left wBefore]; exact reopen.active)
    (by norm_num [workProtectedFloor])
    (by norm_num [E, workProtectedFloor, protectedReadyRate])
  have atError : silent.final.x 0 (.m p) = 1 / 10 := by
    rw [silent.sensor]
    exact silent_full_decay_end (start := P) (box.rates_positive 0 p).2.1.ne'
  let errorStart := setAux silent.final 0 p .error
  let errorJump : Execution θ route silent.final errorStart :=
    .cons (.jump (.error silent.final 0 p silent.aux atError)) (.nil _)
  have errorDate : errorStart.time = E := silent.date
  obtain ⟨error, errorRaw⟩ := work_aux_phase (route := route) box (silent.frame.setAux .error) relative silent.ready
    (by simp [setAux]) (Or.inr rfl)
    (by change silent.final.x 0 .q = workCharge ((θ 0).cap p) s.time W silent.final.time
        rw [silent.date]; exact silent.charge)
    (by change silent.final.x 0 (.m p) = (1 / 10 : ℝ) *
          Real.exp (-protectedReadyRate (θ 0) p .error * (errorStart.time - E))
        rw [atError, errorDate]; simp)
    (by rw [errorDate]; exact eLater.le) (by rw [errorDate]; exact wAfter.trans eLater.le)
    (by rw [errorDate]) (by rw [errorDate]; exact rLater)
    (by change silent.final.raw 0 p = _; rw [errorDate]; exact silentRaw)
    (by norm_num [workProtectedFloor])
    (by norm_num [R, workProtectedFloor, protectedReadyRate])
  have reset : error.final.x 0 (.m p) = 1 / 40 := by
    rw [error.sensor]
    have finish := (protected_decay_schedule (initial := (1 / 10 : ℝ)) (floor := (1 / 40 : ℝ))
      (by norm_num) (by norm_num) (box.rates_positive 0 p).2.2).2.1
    norm_num at finish
    simpa only [R, protectedReadyRate, add_sub_cancel_left, neg_mul] using finish
  let resting := setAux error.final 0 p .ready
  let returnJump : Execution θ route error.final resting :=
    .cons (.jump (.auxReady error.final 0 p error.aux reset)) (.nil _)
  have restingFrame := error.frame.setAux .ready
  have allAux (i : Fin 1) (q : Port) : resting.aux i q = .ready := by
    rw [Subsingleton.elim i 0]
    by_cases eq : q = p
    · subst q; simp [resting, setAux]
    · exact (restingFrame.others q eq).1
  have allRaw (i : Fin 1) (q : Port) : resting.raw i q = none := by
    rw [Subsingleton.elim i 0]
    by_cases eq : q = p
    · subst q; change error.final.raw 0 p = none
      rw [errorRaw, ite_eq_right (not_lt.mpr rAfterExpiry.le)]
    · exact (restingFrame.others q eq).2.2
  have allRest (q : Port) : RestBand (resting.x 0 (.m q)) := by
    by_cases eq : q = p
    · subst q; change RestBand (error.final.x 0 (.m p)); rw [reset]; norm_num [RestBand]
    · exact (restingFrame.others q eq).2.1
  have restingDate : resting.time = R := error.date
  have restingReady (i : Fin 1) : resting.main i = .ready := by rw [Subsingleton.elim i 0]; exact error.ready
  have restingCharge : resting.x 0 .q = workCharge ((θ 0).cap p) s.time W R := error.charge
  have qBelow (i : Fin 1) : resting.x i .q < 1 := by
    rw [Subsingleton.elim i 0, restingCharge]
    exact work_charge_guard box p relative (eLater.trans rLater).le
  have mBelow (i : Fin 1) (q : Port) : resting.x i (.m q) < 1 := by
    rw [Subsingleton.elim i 0]
    linarith [(allRest q).2]
  let final := quietAt resting T
  let quiet : Flow θ resting final := quietFlow resting (by rw [restingDate]; exact rBefore)
    restingReady allAux allRaw qBelow mBelow (by
      have empty : resting.pending = [] := restingFrame.empty
      simp [empty])
  let tail : Execution θ route resting final := .cons (.flow quiet) (.nil _)
  let execution := ((((reopen.execution.append silent.execution).append errorJump).append error.execution).append
    returnJump).append tail
  have finalCharge : final.x 0 .q = workCharge ((θ 0).cap p) s.time W T := by
    change relax (1 / 2) (1 / 10) (resting.x 0 .q) resting.time T = _
    rw [restingCharge, restingDate, workCharge, ite_eq_right (not_lt.mpr rAfterExpiry.le),
      workCharge, ite_eq_right (by dsimp [T]; linarith)]
    unfold relax
    simp only [add_sub_cancel_left]
    rw [mul_assoc, attenuation_split]
  have band := (capped_work_tail_precharge box 0 p relative).2
  have finalBand : 13 / 20 ≤ final.x 0 .q ∧ final.x 0 .q ≤ 39 / 50 := by
    rw [finalCharge, workCharge, ite_eq_right (by dsimp [T]; linarith), raw_work_shift, add_sub_cancel_left]
    unfold relax at *
    rw [show T - (s.time + 1) = 7 / 5 - 1 by dsimp [T]; ring]
    exact band
  have finalRest (q : Port) : RestBand (final.x 0 (.m q)) :=
    relax_mem_Icc (by norm_num) (by rw [restingDate]; exact rBefore.le) (allRest q)
      (by constructor <;> norm_num)
  have finalFrame : CappedWorkFrame θ final p :=
    ⟨restingFrame.recovery, restingFrame.gain, fun q _ => ⟨allAux 0 q, finalRest q, allRaw 0 q⟩,
      restingFrame.empty⟩
  have finalReady (i : Fin 1) : final.main i = .ready := restingReady i
  have finalAux (i : Fin 1) (q : Port) : final.aux i q = .ready := allAux i q
  have finalRaw (i : Fin 1) (q : Port) : final.raw i q = none := allRaw i q
  have complete : CompleteThrough execution T := by
    refine ⟨rfl, ?_, by simp [finalFrame.empty]⟩
    intro next
    exact ready_no_jump final finalReady finalAux finalRaw
      (fun i => by rw [Subsingleton.elim i 0]; linarith [finalBand.2])
      (fun i q => by rw [Subsingleton.elim i 0]; linarith [(finalRest q).2])
      (by simp [finalFrame.empty]) next
  refine ⟨⟨final, execution, ?_, complete, finalReady 0, finalFrame,
    fun q => ⟨finalAux 0 q, finalRest q⟩, finalRaw 0, finalBand, ?_, ?_, ?_⟩⟩
  · simp [execution, errorJump, returnJump, tail, Execution.contactsTransversal_append,
      Jump.ContactTransversal, reopen.transverse, silent.transverse, error.transverse]
  · intro q
    exact (error.gains q).trans ((silent.gains q).trans (reopen.gains q))
  · simp [execution, errorJump, returnJump, tail, Execution.emissions_append, Execution.ledger,
      Move.ledger, Flow.ledger, Jump.ledger, Ledger.add, Ledger.zero,
      reopen.emissions, silent.emissions, error.emissions]
  · simp [execution, errorJump, returnJump, tail, Execution.deliveries_append, Execution.deliveries,
      Move.deliveries, Jump.deliveries, reopen.deliveries, silent.deliveries, error.deliveries]

/-- The read source is due at the fixed end of the work-pulse window. -/
noncomputable def cappedWorkReadToken (s : Snapshot 1) : Delivery 1 :=
  ⟨0, 2, s.time + 7 / 5⟩

structure CappedWorkRead (θ : Fin 1 → Parameters) (s : Snapshot 1) (high : Bool) where
  admitted : Snapshot 1
  lead : Execution θ (fun _ _ => []) (withFuture s [cappedWorkReadToken s]) admitted
  transverse : lead.ContactsTransversal
  admission : admitted.time = (cappedWorkReadToken s).due
  read : SelectorReadRun θ admitted high
  silent : lead.ledger.emissions = []
  gains : ∀ q, admitted.x 0 (.z q) = s.x 0 (.z q)

/-- The real work pulse is followed by one prequeued read delivery. The
work port is distinct from the selector, and the read takes its gain
from the actual endpoint. -/
theorem capped_work_read_exists {θ ε s p age high} (box : @PhysicalBox 1 θ ε)
    (frame : CappedWorkFrame θ s p)
    (slow : s.main 0 = .slow) (charge : s.x 0 .q = (1 / 10 : ℝ) * Real.exp ((11 / 10) * age))
    (timing : CappedWorkTiming ε age) (active : s.raw 0 p = some s.time)
    (ready : s.aux 0 p = .ready) (rest : RestBand (s.x 0 (.m p)))
    (gain : s.x 0 (.z 2) = selectorReadLogGain high) :
    Nonempty (CappedWorkRead θ s high) := by
  obtain ⟨work⟩ := capped_work_precharge_exists (route := fun _ _ => []) box frame slow
    charge timing active ready rest
  let token := cappedWorkReadToken s
  have due : work.final.time = token.due := work.complete.1
  let lead := work.execution.withFuture [token]
    (by intro d hd; simpa using (List.mem_singleton.mp hd) ▸ due.le)
  let before := withFuture work.final [token]
  let admitted : Snapshot 1 := { (setRaw before token.cell token.port (some before.time)) with pending := [] }
  let arrival : Jump (fun _ _ => []) before admitted :=
    .arrive _ token [] [] (by simp [before, withFuture, work.frame.empty]) due.symm (work.rawNone 2)
  let jump : Execution θ (fun _ _ => []) before admitted :=
    .cons (.jump arrival) (.nil _)
  have gains (q : Port) : admitted.x 0 (.z q) = s.x 0 (.z q) := work.gains q
  have recovery : admitted.x 0 .b = 11 / 10 := work.frame.recovery
  have prepared : SelectorReadPrepared admitted high := by
    refine ⟨work.ready, work.charge, (gains 2).trans gain, ?_, work.auxiliary, ?_, ?_, rfl⟩
    · rw [recovery]; norm_num
    · simp [admitted, token, cappedWorkReadToken, setRaw]
    · intro q ne
      simpa [admitted, token, cappedWorkReadToken, setRaw, before, withFuture, ne] using work.rawNone q
  obtain ⟨read⟩ := selector_read_run_exists box prepared
  have positive : lead.ContactsTransversal :=
    teacher_future_transverse work.execution token due.le work.transverse
  have silent : lead.ledger.emissions = [] := by
    rw [Execution.withFuture_ledger, work.emissions]
  refine ⟨⟨admitted, lead.append jump,
    (Execution.contactsTransversal_append _ _).2 ⟨positive, ⟨trivial, trivial⟩⟩,
    due, read, ?_, gains⟩⟩
  rw [Execution.emissions_append, silent]
  rfl

noncomputable def CappedWorkRead.execution {θ s high} (run : CappedWorkRead θ s high) :
    Execution θ (fun _ _ => []) (withFuture s [cappedWorkReadToken s]) run.read.final :=
  run.lead.append run.read.execution

theorem CappedWorkRead.only_fire {θ s high} (run : CappedWorkRead θ s high) :
    run.execution.ledger.emissions = [(0, s.time + 7 / 5 + run.read.latency)] := by
  rw [CappedWorkRead.execution, Execution.emissions_append, run.silent, run.read.emissions, run.admission]
  rfl

theorem CappedWorkRead.preserves_gains {θ s high} (run : CappedWorkRead θ s high) (q : Port) :
    run.read.final.x 0 (.z q) = s.x 0 (.z q) := (run.read.gains q).trans (run.gains q)

/-- The entire work/read continuation has a genuine upward-crossing version,
including the MARK on the work port and the read's FIRE. -/
theorem CappedWorkRead.crossing_exists {θ ε s high} (run : CappedWorkRead θ s high)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s) (initial : InitiallyBelowReady s) :
    ∃ crossing : CrossingExecution θ (fun _ _ => []) (withFuture s [cappedWorkReadToken s]) run.read.final,
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing run.read.horizon := by
  have pf : PhysicalInvariant θ (withFuture s [cappedWorkReadToken s]) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  have init : InitiallyBelowReady (withFuture s [cappedWorkReadToken s]) := initial
  have transverse : run.execution.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2 ⟨run.transverse, run.read.transversal⟩
  exact ⟨run.execution.toCrossing init box pf transverse, rfl,
    run.read.complete.toCrossing run.execution init box pf transverse⟩

/-- The charge expected at work admission is the residual of ordinary
SLOW decay from the teacher's own FAST exit, at the realized local delay. -/
theorem capped_work_admission_charge (delay : ℝ) :
    (1 / 4 : ℝ) * Real.exp (-(11 / 10) * (delay - 1)) =
      (1 / 10 : ℝ) * Real.exp ((11 / 10) * (cappedTeacherPeriod - delay)) := by
  have exponent : (11 / 10 : ℝ) * (cappedTeacherPeriod - delay) =
      Real.log (5 / 2) + -(11 / 10) * (delay - 1) := by
    unfold cappedTeacherPeriod
    ring
  rw [exponent, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]
  ring

/-- At the common completed work/read horizon, competing native executions
have the same endpoint and sole read spike. -/
theorem CappedWorkRead.every_complete {θ ε s high final} (run : CappedWorkRead θ s high)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (e : Execution θ (fun _ _ => []) (withFuture s [cappedWorkReadToken s]) final)
    (complete : CompleteThrough e run.read.horizon) :
    final.ObservationalEq run.read.final ∧
      e.ledger.emissions = [(0, s.time + 7 / 5 + run.read.latency)] := by
  have pf : PhysicalInvariant θ (withFuture s [cappedWorkReadToken s]) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  obtain ⟨endpoint, fires⟩ := e.observational_unique run.execution box pf complete run.read.complete
  rw [run.only_fire] at fires
  exact ⟨endpoint, List.perm_singleton.mp fires⟩

/-- The same comparison holds for complete upward-crossing executions. -/
theorem CappedWorkRead.every_crossing_complete {θ ε s high final} (run : CappedWorkRead θ s high)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s) (initial : InitiallyBelowReady s)
    (crossing : CrossingExecution θ (fun _ _ => []) (withFuture s [cappedWorkReadToken s]) final)
    (complete : CrossingCompleteThrough crossing run.read.horizon) :
    final.ObservationalEq run.read.final ∧
      crossing.execution.ledger.emissions = [(0, s.time + 7 / 5 + run.read.latency)] := by
  have pf : PhysicalInvariant θ (withFuture s [cappedWorkReadToken s]) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  have init : InitiallyBelowReady (withFuture s [cappedWorkReadToken s]) := initial
  have positive : run.execution.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2 ⟨run.transverse, run.read.transversal⟩
  have causal : StrictCausalRouter (fun (_ : Fin 1) _ => []) :=
    fun _ _ _ member => (List.not_mem_nil member).elim
  obtain ⟨native, same⟩ := crossing.execution.toNative_of_transverse_completion run.execution
    causal box pf run.read.complete positive (le_of_eq complete.1)
  have weak := complete.toWeak_of_native crossing native same init box pf
  obtain ⟨endpoint, fires⟩ := run.execution.observational_unique_weak box crossing.execution pf
    run.read.complete positive weak
  rw [run.only_fire] at fires
  exact ⟨endpoint.symm, List.perm_singleton.mp fires.symm⟩

/-- A concrete one-cell work admission, with work on port 0 and the selector
on port 2. The charge is the one supplied by the capped SLOW clock. -/
noncomputable def preparedCappedWork (θ : Fin 1 → Parameters) (origin age : ℝ) (high : Bool) : Snapshot 1 where
  time := origin
  x := fun _ c => match c with
    | .q => (1 / 10) * Real.exp ((11 / 10) * age)
    | .b => 11 / 10
    | .m _ => 1 / 40
    | .z p => if p = 0 then Real.log ((θ 0).cap p) else if p = 2 then selectorReadLogGain high else 0
    | .energy => 100
  main := fun _ => .slow
  aux := fun _ _ => .ready
  raw := fun _ p => if p = 0 then some origin else none
  pending := []

/-- Both stored values have a complete upward-crossing work/read history at
a prepared capped work admission for every certified realized local delay. -/
theorem prepared_capped_work_read_crossing_exists {θ ε σ delay} (box : @PhysicalBox 1 θ ε)
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : delay ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (origin : ℝ) (high : Bool) :
    let s := preparedCappedWork θ origin (cappedTeacherPeriod - delay) high
    ∃ (run : CappedWorkRead θ s high)
      (crossing : CrossingExecution θ (fun _ _ => []) (withFuture s [cappedWorkReadToken s]) run.read.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing run.read.horizon := by
  let age := cappedTeacherPeriod - delay
  let s := preparedCappedWork θ origin age high
  have ageBounds := (capped_teacher_jitter_iff nonnegative).2 budget delay wire
  have expBound : Real.exp ((11 / 10) * age) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    linarith [ageBounds.2, Real.log_two_gt_d9]
  have physical : PhysicalInvariant θ s := by
    refine ⟨fun _ => ?_, ?_, fun _ => le_rfl, fun _ => by norm_num [s, preparedCappedWork]⟩
    · change 0 ≤ (11 / 10 : ℝ) ∧ (1 / 10 : ℝ) * Real.exp ((11 / 10) * age) ≤ 1 ∧
        ∀ q : Port, (1 / 40 : ℝ) ≤ auxUpper .ready
      refine ⟨by norm_num, by linarith, fun _ => by norm_num [auxUpper]⟩
    · intro i p
      rw [Subsingleton.elim i 0]
      have capLower : (2 : ℝ) ≤ (θ 0).cap p := by
        have h := (box.2 0 p).1.1
        linarith [box.epsilon_bounds.2]
      have logBound := Real.log_le_log (by norm_num : (0 : ℝ) < 2) capLower
      have logTwo := Real.log_two_gt_d9
      by_cases work : p = 0
      · subst p; simp [s, preparedCappedWork]
      · by_cases read : p = 2
        · subst p
          cases high <;> simp [s, preparedCappedWork, selectorReadLogGain] <;> linarith
        · simp [s, preparedCappedWork, work, read]; linarith
  have initial : InitiallyBelowReady s := by
    intro i c ready
    rw [Subsingleton.elim i 0]
    cases c with
    | q => simp [s, preparedCappedWork, ReadyCoordinate] at ready
    | m p => norm_num [s, preparedCappedWork]
    | z _ => exact False.elim ready
    | b => exact False.elim ready
    | energy => exact False.elim ready
  have frame : CappedWorkFrame θ s 0 := by
    refine ⟨rfl, by simp [s, preparedCappedWork], ?_, rfl⟩
    intro q different
    simp [s, preparedCappedWork, RestBand, different]
  obtain ⟨run⟩ := capped_work_read_exists (high := high) box frame rfl rfl (Or.inl ageBounds)
    (by simp [s, preparedCappedWork]) rfl (by norm_num [s, preparedCappedWork, RestBand])
    (by simp [s, preparedCappedWork])
  obtain ⟨crossing, same, complete⟩ := run.crossing_exists box physical initial
  exact ⟨run, crossing, same, complete⟩

end RecursiveLearning.Native
