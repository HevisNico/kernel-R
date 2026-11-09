import LearnerConjunction

/-! Arbitrary finite fan-in from physical learner trials. Each reporting
learner has one reserved slot at the counter, independently of which trials
pass. The global queue supplies only lessons and read pulses. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

noncomputable def trialBankStart (time : ℝ) : {n : ℕ} → (Fin n → Bool) → (Fin n → Bool) → Snapshot n
  | 0, _, _ => ⟨time, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, []⟩
  | n + 1, kinds, passed =>
    queueHead (trialBankStart time (fun i : Fin n => kinds i.succ) (fun i => passed i.succ))
      {seriesTrial time (kinds 0) (passed 0) with time := time}

def trialBankRouter : (n : ℕ) → Router n
  | 0 => fun i => Fin.elim0 i
  | n + 1 => prependRouted (trialBankRouter n) (fun _ _ => [])

theorem trial_bank_clock (time : ℝ) {n} (kinds passed : Fin n → Bool) :
    (trialBankStart time kinds passed).time = time := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _ _

theorem trial_bank_causal (n : ℕ) : StrictCausalRouter (trialBankRouter n) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih => exact prepend_routed_causal ih (fun _ _ _ h => (List.not_mem_nil h).elim)

private theorem prepend_parameters_split {n} (θ : Fin (n + 1) → Parameters) :
    prependParameters (fun _ => θ 0) (fun i => θ i.succ) = θ := by
  funext i
  cases i using Fin.cases <;> rfl

theorem trial_bank_physical {n θ ε} (box : @PhysicalBox n θ ε) (time : ℝ)
    (kinds passed : Fin n → Bool) : PhysicalInvariant θ (trialBankStart time kinds passed) := by
  induction n with
  | zero =>
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    have tailBox : PhysicalBox (fun i : Fin n => θ i.succ) ε := ⟨box.1, fun i => box.2 i.succ⟩
    have headBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    have h := readout_learner_physical headBox time (trialLesson (kinds 0) (passed 0)) (trialPort (kinds 0))
    have head : PhysicalInvariant (fun _ => θ 0)
        {seriesTrial time (kinds 0) (passed 0) with time := time} :=
      ⟨h.region, h.gain_cap, h.recovery_cap, h.reserve⟩
    let s := trialBankStart time (fun i : Fin n => kinds i.succ) (fun i => passed i.succ)
    let h := {seriesTrial time (kinds 0) (passed 0) with time := time}
    have tail : PhysicalInvariant (fun i : Fin n => θ i.succ) s := ih tailBox _ _
    have joined := prepend_physical tail head (independentHeadQueue s h)
    rwa [prepend_parameters_split θ] at joined

private theorem prepend_initial {n} {s : Snapshot n} {h : Snapshot 1} {Q}
    (tail : InitiallyBelowReady s) (head : InitiallyBelowReady h) :
    InitiallyBelowReady (s.prependQueued h Q) := by
  intro i c ready
  cases i using Fin.cases with
  | zero => exact head 0 c ready
  | succ i => exact tail i c ready

theorem trial_bank_initial {n} (time : ℝ) (kinds passed : Fin n → Bool) :
    InitiallyBelowReady (trialBankStart time kinds passed) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    apply prepend_initial (ih _ _)
    intro i c h
    cases c with
    | q => change (1 / 10 : ℝ) < 1; norm_num
    | m p => change (1 / 40 : ℝ) < 1; norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h

private def reportLedger : {n : ℕ} → (Fin n → Option ℝ) → List (Fin n × ℝ)
  | 0, _ => []
  | n + 1, fires =>
    (fires 0).toList.map (fun F => (0, F)) ++
      (reportLedger (fun i : Fin n => fires i.succ)).map (fun ev => (ev.1.succ, ev.2))

structure TrialBankRun {n} (θ : Fin n → Parameters) (time T : ℝ)
    (kinds passed : Fin n → Bool) where
  final : Snapshot n
  execution : Execution θ (trialBankRouter n) (trialBankStart time kinds passed) final
  complete : CompleteThrough execution T
  positive : execution.ContactsTransversal
  fires : Fin n → Option ℝ
  flags : ∀ i, (fires i).isSome = passed i
  window : ∀ i F, fires i = some F → time + 65 < F ∧ F < time + 66
  dates : ∀ i, execution.emissionTimes i = (fires i).toList
  ledger : execution.ledger.emissions.Perm (reportLedger fires)

private theorem head_emission_ledger {θ route s u}
    (e : @Execution 1 θ route s u) :
    e.ledger.emissions = (e.emissionTimes 0).map (fun F => (0, F)) := by
  unfold Execution.emissionTimes
  have h : e.ledger.emissions.filter (fun ev => ev.1 = 0) = e.ledger.emissions :=
    List.filter_eq_self.mpr (fun ev _ => by
      simpa only [decide_eq_true_eq] using (Subsingleton.elim ev.1 (0 : Fin 1)))
  rw [h, List.map_map]
  have same : (fun (ev : Fin 1 × ℝ) => (0, ev.2)) = id := by
    funext ev
    exact Prod.ext (Subsingleton.elim _ _) rfl
  change _ = e.ledger.emissions.map (fun ev => (0, ev.2))
  rw [same, List.map_id]

theorem trial_bank_exists {n θ ε time T} (box : @PhysicalBox n θ ε)
    (horizon : time + 96 < T) (kinds passed : Fin n → Bool) :
    Nonempty (TrialBankRun θ time T kinds passed) := by
  induction n with
  | zero =>
    let start := trialBankStart time kinds passed
    have lt : start.time < T := by rw [trial_bank_clock]; linarith
    have none : ∀ d ∈ start.pending, T < d.due := by simp [start, trialBankStart]
    let flow : Flow θ start (quietAt start T) := quietFlow start lt (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun d h => (none d h).le)
    obtain ⟨_, done⟩ := quiet_complete_exists (θ := θ) (route := trialBankRouter 0) start lt
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) none
    exact ⟨⟨_, .cons (.flow flow) (.nil _), done, by simp, Fin.elim0,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, .refl _⟩⟩
  | succ n ih =>
    have tailBox : PhysicalBox (fun i : Fin n => θ i.succ) ε := ⟨box.1, fun i => box.2 i.succ⟩
    have headBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    obtain ⟨tail⟩ := ih tailBox (fun i => kinds i.succ) (fun i => passed i.succ)
    obtain ⟨head, fire, flag, window, dates, _⟩ :=
      staged_trial_exists headBox le_rfl horizon (kinds 0) (passed 0)
    obtain ⟨weave, done⟩ := tail.execution.prepend_independent_complete head.execution
      (trial_bank_clock time _ _) tail.complete head.complete
    have positive := weave.contacts_transversal tail.positive head.positive
    let fires : Fin (n + 1) → Option ℝ := Fin.cases fire tail.fires
    have everyFlag (i : Fin (n + 1)) : (fires i).isSome = passed i := by
      cases i using Fin.cases with
      | zero => exact flag
      | succ i => exact tail.flags i
    have everyWindow (i : Fin (n + 1)) (F : ℝ) (h : fires i = some F) :
        time + 65 < F ∧ F < time + 66 := by
      cases i using Fin.cases with
      | zero => exact window F h
      | succ i => exact tail.window i F h
    have everyDate (i : Fin (n + 1)) : weave.execution.emissionTimes i = (fires i).toList := by
      cases i using Fin.cases with
      | zero => exact weave.head_emission_times.trans dates
      | succ i => exact (weave.tail_emission_times i).trans (tail.dates i)
    have ledger : weave.execution.ledger.emissions.Perm (reportLedger fires) := by
      have left := weave.trace.emissions
      have tailPerm := Multiset.coe_eq_coe.mpr (tail.ledger.map (fun ev => (ev.1.succ, ev.2)))
      have right := (head_emission_ledger head.execution).trans (congrArg _ dates)
      apply Multiset.coe_eq_coe.mp
      rw [left, tailPerm, right, List.map_map]
      change _ = (↑((fire.toList.map (fun F => ((0 : Fin (n + 1)), F))) ++
        (reportLedger tail.fires).map (fun ev => (ev.1.succ, ev.2))) : Multiset (Fin (n + 1) × ℝ))
      rw [← Multiset.coe_add]
      exact add_comm _ _
    let θ' := prependParameters (fun _ => θ 0) (fun i : Fin n => θ i.succ)
    have result : TrialBankRun θ' time T kinds passed :=
      ⟨_, weave.execution, done, positive, fires, everyFlag, everyWindow, everyDate, ledger⟩
    rw [show θ' = θ from prepend_parameters_split θ] at result
    exact ⟨result⟩

private def reportDates : {n : ℕ} → (Fin n → ℝ) → (Fin n → Bool) → List ℝ
  | 0, _, _ => []
  | n + 1, slot, passed =>
    (if passed 0 then [slot 0] else []) ++ reportDates (fun i : Fin n => slot i.succ) (fun i => passed i.succ)

private theorem report_dates_member {n} {slot : Fin n → ℝ} {passed : Fin n → Bool}
    {d : ℝ} (member : d ∈ reportDates slot passed) :
    ∃ i, passed i = true ∧ d = slot i := by
  induction n with
  | zero => simp [reportDates] at member
  | succ n ih =>
    rcases List.mem_append.mp member with h | h
    · by_cases pass : passed 0 = true
      · exact ⟨0, pass, by simpa [pass] using h⟩
      · simp [pass] at h
    · obtain ⟨i, pass, date⟩ := ih h
      exact ⟨i.succ, pass, date⟩

private theorem report_dates_length {n} (slot : Fin n → ℝ) (passed : Fin n → Bool) :
    (reportDates slot passed).length ≤ n ∧
    ((reportDates slot passed).length = n ↔ ∀ i, passed i = true) := by
  induction n with
  | zero => exact ⟨Nat.le_refl _, fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨bound, full⟩ := ih (fun i => slot i.succ) (fun i => passed i.succ)
    by_cases h : passed 0 = true
    · simp only [reportDates, h, ite_true, List.length_append, List.length_cons, List.length_nil]
      constructor
      · omega
      · constructor
        · intro count i
          cases i using Fin.cases with
          | zero => exact h
          | succ i => exact full.mp (by omega) i
        · intro pass
          have count := full.mpr (fun i => pass i.succ)
          omega
    · simp [reportDates, h]
      exact ⟨by omega, fun eq => by omega, fun pass => (h (pass 0)).elim⟩

private theorem report_dates_separated {n} (slot : Fin n → ℝ) (passed : Fin n → Bool)
    (gap : ∀ i j, i < j → slot i + 8 ≤ slot j) :
    (reportDates slot passed).Pairwise (fun x y => x + 8 ≤ y) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    have tail := ih (fun i : Fin n => slot i.succ) (fun i => passed i.succ)
      (fun i j h => gap i.succ j.succ (by simpa only [Fin.succ_lt_succ_iff] using h))
    by_cases h : passed 0 = true
    · simp only [reportDates, h, ite_true, List.singleton_append]
      refine List.pairwise_cons.mpr ⟨?_, tail⟩
      intro d hd
      obtain ⟨i, _, rfl⟩ := report_dates_member hd
      exact gap 0 i.succ (Fin.succ_pos i)
    · simpa [reportDates, h] using tail

private theorem report_ledger_to_queue {n} (fires : Fin n → Option ℝ) (slot : Fin n → ℝ)
    (passed : Fin n → Bool) (gate : ℝ) (flags : ∀ i, (fires i).isSome = passed i)
    (early : ∀ i F, fires i = some F → F < gate) :
    (reportLedger fires).flatMap (fun ev => fixedCalendar gate [⟨0, 0, slot ev.1⟩] ev.2) =
      conjunctionDoseTokens 0 (reportDates slot passed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have tail := ih (fun i => fires i.succ) (fun i => slot i.succ) (fun i => passed i.succ)
      (fun i => flags i.succ) (fun i => early i.succ)
    have head : (fires 0).toList.flatMap (fixedCalendar gate [⟨0, 0, slot 0⟩]) =
        conjunctionDoseTokens 0 (if passed 0 then [slot 0] else []) := by
      cases h : fires 0 with
      | none =>
        have pass : passed 0 = false := by simpa [h] using (flags 0).symm
        simp [pass, conjunctionDoseTokens]
      | some F =>
        have pass : passed 0 = true := by simpa [h] using (flags 0).symm
        simp [pass, conjunctionDoseTokens, fixedCalendar, early 0 F h]
    simp only [reportLedger, reportDates, List.flatMap_append, List.flatMap_map,
      conjunctionDoseTokens, List.map_append] at *
    rw [head]
    exact congrArg (fun xs => _ ++ xs) tail

/-- Attach a one-cell receiver whose local history includes its external
inputs and the deliveries scheduled by the sender network. The composed
birth queue contains only external inputs. -/
theorem compose_scheduled_receiver {n θ θH route s u h v T}
    (send : @Execution n θ route s u) (receive : @Execution 1 θH (fun _ _ => []) h v)
    (sendDone : CompleteThrough send T) (receiveDone : CompleteThrough receive T)
    (clock : s.time = h.time) (external : List (Delivery 1)) (contacts : HeadRoutes n)
    (strict : StrictHeadRoutes contacts)
    (inputs : (external ++ send.headInputQueue contacts).Perm h.pending) :
    Nonempty (CausalHeadWeave send receive (independentHeadQueue s (h.requeue external)) contacts) :=
  send.prepend_causal_result receive clock (sendDone.1.trans receiveDone.1.symm) contacts strict _
    (stage_balance send h external contacts inputs)

private noncomputable def fanInSlot (time : ℝ) {n} (i : Fin n) : ℝ :=
  time + 70 + 8 * (i : ℕ)

private noncomputable def fanInRead (time : ℝ) (n : ℕ) : ℝ := time + 70 + 8 * n

private noncomputable def fanInContacts (time : ℝ) (n : ℕ) : HeadRoutes n :=
  fun i => fixedCalendar (time + 69) [⟨0, 0, fanInSlot time i⟩]

private theorem fan_in_contacts_strict (time : ℝ) (n : ℕ) : StrictHeadRoutes (fanInContacts time n) := by
  intro i
  apply fixedCalendar_strict
  intro d h
  obtain rfl := List.mem_singleton.mp h
  change time + 69 ≤ time + 70 + 8 * ((i : ℕ) : ℝ)
  linarith [show (0 : ℝ) ≤ ((i : ℕ) : ℝ) by positivity]

private noncomputable def counterToCredit (n : ℕ) : HeadRoutes (n + 1) :=
  atCell 0 (acceptanceContacts 0 0)

private theorem counter_to_credit_strict (n : ℕ) : StrictHeadRoutes (counterToCredit n) := by
  apply atCell_strict
  intro F d h
  obtain rfl := List.mem_singleton.mp h
  change F < F + 7 / 20
  linarith

noncomputable def learnerFanInRouter (time : ℝ) (n : ℕ) : Router (n + 1 + 1) :=
  prependRouted (prependRouted (trialBankRouter n) (fanInContacts time n)) (counterToCredit n)

noncomputable def learnerFanInStart (time : ℝ) {n} (kinds passed : Fin n → Bool) :
    Snapshot (n + 1 + 1) :=
  let counter := (conjunctionCounter time n).requeue [conjunctionProbe (fanInRead time n)]
  queueHead (queueHead (trialBankStart time kinds passed) counter) ((preparedTeacher time).requeue [])

noncomputable def learnerFanInHorizon (time : ℝ) (n : ℕ) : ℝ := fanInRead time n + 30

abbrev learnerFanInParameters {n} (learners : Fin n → Parameters)
    (counter credit : Fin 1 → Parameters) : Fin (n + 1 + 1) → Parameters :=
  prependParameters credit (prependParameters counter learners)

private theorem fan_in_counter_physical {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) (n : ℕ) :
    PhysicalInvariant θ ((conjunctionCounter time n).requeue [conjunctionProbe (fanInRead time n)]) := by
  have c := conjunction_counter_physical box time n
  exact ⟨c.region, c.gain_cap, c.recovery_cap, c.reserve⟩

private theorem fan_in_initial {n} (time : ℝ) (kinds passed : Fin n → Bool) :
    InitiallyBelowReady (learnerFanInStart time kinds passed) := by
  apply prepend_initial (prepend_initial (trial_bank_initial time kinds passed) ?_) <;>
    intro i c h <;> cases c
  all_goals first
    | (change (1 / 10 : ℝ) < 1; norm_num)
    | (change (1 / 40 : ℝ) < 1; norm_num)
    | exact False.elim h

private theorem option_report_length {fire : Option ℝ} {passed : Bool} (h : fire.isSome = passed) :
    fire.toList.length = if passed then 1 else 0 := by
  cases fire <;> rw [← h] <;> rfl

/-- An arbitrary positive number of real learner readouts feed one counter.
The router is independent of every trial outcome. A credit is written
exactly when all learners pass, in every complete crossing execution. -/
theorem native_learner_fan_in {n θ θA θC ε} (positiveArity : 0 < n)
    (learnerBox : @PhysicalBox n θ ε) (counterBox : @PhysicalBox 1 θA ε)
    (creditBox : @PhysicalBox 1 θC ε) (time : ℝ) (kinds passed : Fin n → Bool) :
    let parameters := learnerFanInParameters θ θA θC
    let route := learnerFanInRouter time n
    let start := learnerFanInStart time kinds passed
    let T := learnerFanInHorizon time n
    ∃ (final : Snapshot (n + 1 + 1)) (e : Execution parameters route start final)
      (crossing : CrossingExecution parameters route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing T ∧
      (∀ i, (((trialLesson (kinds i) (passed i)).train ⟨3, 3⟩).retained = true ↔
        (e.emissionTimes i.succ.succ).length = 1)) ∧
      (e.emissionTimes (0 : Fin (n + 1)).succ).length =
        (if ∀ i, passed i = true then 1 else 0) ∧
      (∀ p, final.x 0 (.z p) = if p = 0 ∧ (∀ i, passed i = true) then 3 / 5 else 0) ∧
      (∀ otherFinal (other : CrossingExecution parameters route start otherFinal),
        CrossingCompleteThrough other T →
        otherFinal.ObservationalEq final ∧ ∀ i, other.execution.emissionTimes i = e.emissionTimes i) := by
  classical
  let T := learnerFanInHorizon time n
  let read := fanInRead time n
  let slot : Fin n → ℝ := fanInSlot time
  let dates := reportDates slot passed
  have readDate : read = time + 70 + 8 * n := rfl
  have horizonDate : T = read + 30 := rfl
  have nonnegative : (0 : ℝ) ≤ n := by positivity
  obtain ⟨bank⟩ := trial_bank_exists learnerBox (time := time) (T := T)
    (by rw [horizonDate, readDate]; linarith) kinds passed
  have queue : (bank.execution.headInputQueue (fanInContacts time n)).Perm
      (conjunctionDoseTokens 0 dates) := by
    have ledger := bank.ledger.flatMap_right (fun ev => fixedCalendar (time + 69) [⟨0, 0, slot ev.1⟩] ev.2)
    refine ledger.trans (List.Perm.of_eq (report_ledger_to_queue bank.fires slot passed
      (time + 69) bank.flags (fun i F h => by linarith [(bank.window i F h).2])))
  have bound := report_dates_length slot passed
  have separated : dates.Pairwise (fun a b => a + 8 ≤ b) := by
    apply report_dates_separated
    intro i j order
    have h : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
      exact_mod_cast (show (i : ℕ) + 1 ≤ (j : ℕ) from order)
    change time + 70 + 8 * ((i : ℕ) : ℝ) + 8 ≤ time + 70 + 8 * ((j : ℕ) : ℝ)
    linarith
  obtain ⟨counter⟩ := native_conjunction_counter_exists counterBox time read T n dates positiveArity
    bound.1 (by rw [readDate]; linarith) (by rw [horizonDate]; linarith)
    (by
      intro d hd
      obtain ⟨i, _, rfl⟩ := report_dates_member hd
      change time < time + 70 + 8 * ((i : ℕ) : ℝ)
      linarith [show (0 : ℝ) ≤ ((i : ℕ) : ℝ) by positivity])
    (by
      intro d hd
      obtain ⟨i, _, rfl⟩ := report_dates_member hd
      have h : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
      rw [readDate]
      change time + 70 + 8 * ((i : ℕ) : ℝ) + 15 / 2 < time + 70 + 8 * n
      linarith) separated
  have flag : counter.fire.isSome = decide (∀ i, passed i = true) := by
    rw [counter.reports]
    by_cases allPass : ∀ i, passed i = true
    · simp [allPass, show dates.length = n from bound.2.mpr allPass]
    · simp [allPass, show dates.length ≠ n from fun h => allPass (bound.2.mp h)]
  obtain ⟨counted⟩ := compose_scheduled_receiver bank.execution counter.execution
    bank.complete counter.complete (trial_bank_clock time kinds passed)
    [conjunctionProbe read] (fanInContacts time n) (fan_in_contacts_strict time n)
    (List.Perm.cons _ queue)
  have countedDone := counted.complete bank.complete counter.complete
  have countedPositive := counted.contacts_transversal bank.positive counter.transverse
  have counterDates : counted.execution.emissionTimes 0 = counter.fire.toList := by
    rw [counted.head_emission_times, Execution.emissionTimes, counter.emissions]
    cases counter.fire <;> rfl
  obtain ⟨credit⟩ := credit_response_exists creditBox (time := time) (T := T) (credit := 0) (fire := counter.fire)
    (by rw [horizonDate, readDate]; linarith)
    (fun F h => by
      obtain ⟨early, late⟩ := counter.window F h
      change read < F at early
      change F < read + 1 at late
      rw [horizonDate]
      constructor <;> linarith [readDate])
  let creditSource := (preparedTeacher time).requeue
    (counter.fire.toList.map (fun F => ⟨0, 0, F + 7 / 20⟩))
  have creditQueue : counted.execution.headInputQueue (counterToCredit n) = creditSource.pending := by
    rw [counterToCredit, atCell_inputs, counterDates]
    cases h : counter.fire <;> simp [creditSource, Snapshot.requeue, h, acceptanceContacts]
  obtain ⟨whole⟩ := compose_scheduled_receiver counted.execution credit.execution
    countedDone credit.complete (trial_bank_clock time kinds passed) []
    (counterToCredit n) (counter_to_credit_strict n) (List.Perm.of_eq creditQueue)
  have complete := whole.complete countedDone credit.complete
  have transverse := whole.contacts_transversal countedPositive credit.positive
  have box := prepend_box (prepend_box learnerBox counterBox) creditBox
  have physical : PhysicalInvariant (learnerFanInParameters θ θA θC) (learnerFanInStart time kinds passed) :=
    prepend_physical (prepend_physical (trial_bank_physical learnerBox time kinds passed)
      (fan_in_counter_physical counterBox time n) _) (preparedTeacher_physical creditBox time []) _
  have initial := fan_in_initial time kinds passed
  let e : Execution (learnerFanInParameters θ θA θC) (learnerFanInRouter time n)
      (learnerFanInStart time kinds passed) _ := whole.execution
  refine ⟨_, e, e.toCrossing initial box physical transverse, rfl,
    complete.toCrossing e initial box physical transverse, ?_, ?_, ?_, ?_⟩
  · intro i
    change _ ↔ (whole.execution.emissionTimes i.succ.succ).length = 1
    rw [whole.tail_emission_times, counted.tail_emission_times, bank.dates, option_report_length (bank.flags i)]
    cases kinds i <;> cases passed i <;> decide
  · change (whole.execution.emissionTimes (0 : Fin (n + 1)).succ).length = _
    rw [whole.tail_emission_times, counterDates, option_report_length flag]
    simp
  · intro p
    change credit.final.x 0 (.z p) = _
    rw [credit.written, flag]
    simp
  · intro otherFinal other done
    have strict := prepend_routed_causal
      (prepend_routed_causal (trial_bank_causal n) (fan_in_contacts_strict time n)) (counter_to_credit_strict n)
    obtain ⟨native, same⟩ := other.execution.toNative_of_transverse_completion e strict box physical
      complete transverse (le_of_eq done.1)
    have weak := done.toWeak_of_native other native same initial box physical
    exact ⟨(e.observational_unique_weak box other.execution physical complete transverse weak).1.symm,
      fun i => (e.emissionTimes_unique_weak other.execution box physical complete transverse weak i).symm⟩

end RecursiveLearning.Native
