import ReadoutSeries

/-! A native coincidence test over separated learner reports. The counter
uses ordinary R doses, and a common read pulse observes its physical gain. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

def conjunctionDoseTokens (port : Port) (dates : List ℝ) : List (Delivery 1) :=
  dates.map fun date => ⟨0, port, date⟩

private theorem dose_tokens_ports (port : Port) (dates : List ℝ) :
    (conjunctionDoseTokens port dates).map Delivery.port = List.replicate dates.length port := by
  induction dates with
  | nil => rfl
  | cons d ds ih =>
    change port :: (conjunctionDoseTokens port ds).map Delivery.port =
      List.replicate (ds.length + 1) port
    rw [ih, List.replicate_succ]

/-- Separated pulses write exact doses even when the calendar has gaps. -/
private theorem sparse_dose_run_exists {θ ε start port dates limit} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ start) (valid : RawValid start)
    (ready : ReadyCoordinates start 0) (rawNone : ∀ p, start.raw 0 p = none)
    (queue : start.pending = conjunctionDoseTokens port dates)
    (before : start.time ≤ limit) (future : ∀ d ∈ dates, start.time < d)
    (within : ∀ d ∈ dates, d + 15 / 2 ≤ limit)
    (separated : dates.Pairwise (fun a b => a + 8 ≤ b))
    (headroom : start.x 0 (.z port) + (3 / 5 : ℝ) * dates.length ≤ 3 / 5) :
    ∃ run : CalendarDoseRun θ start (conjunctionDoseTokens port dates), run.final.time ≤ limit := by
  induction dates generalizing start with
  | nil =>
    exact ⟨⟨start, .nil _, trivial, rfl, rfl, by simp [conjunctionDoseTokens], rfl, ready, rawNone, queue⟩, before⟩
  | cons date dates ih =>
    obtain ⟨gap, tailSeparated⟩ := List.pairwise_cons.mp separated
    have weakGain : start.x 0 (.z port) ≤ 0 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at headroom
      linarith [show (0 : ℝ) ≤ dates.length by positivity]
    obtain ⟨dose⟩ := port_dose_exists (route := fun _ _ => []) (port := port)
      (due := date) (later := conjunctionDoseTokens port dates) box physical valid ready rawNone
      (future date (by simp)) queue
      (by
        intro d hd
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
        exact gap t ht)
      (by
        have h := Real.exp_le_exp.mpr weakGain
        rw [Real.exp_zero] at h
        linarith)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)])
    obtain ⟨tail, final⟩ := ih dose.physical dose.rawValid dose.ready dose.rawNone dose.pending
      (by rw [dose.complete.1]; exact within date (by simp))
      (by intro d hd; rw [dose.complete.1]; linarith [gap d hd])
      (fun d hd => within d (by simp [hd])) tailSeparated
      (by
        rw [dose.gain]
        simp only [ite_true, List.length_cons, Nat.cast_add, Nat.cast_one] at *
        linarith)
    refine ⟨⟨tail.final, dose.execution.append tail.execution,
      (Execution.contactsTransversal_append _ _).2 ⟨dose.transversal, tail.transverse⟩,
      ?_, ?_, ?_, tail.recovery.trans dose.recovery, tail.ready, tail.rawNone, tail.empty⟩, final⟩
    · rw [Execution.emissions_append, dose.emissions, tail.silent]
      rfl
    · rw [Execution.deliveries_append, dose.deliveries, tail.deliveries]
      rfl
    · intro p
      rw [tail.gains, dose.gain, dose_tokens_ports, dose_tokens_ports]
      by_cases same : p = port
      · subst p
        simp only [ite_true, List.count_replicate_self, List.length_cons, Nat.cast_add, Nat.cast_one]
        ring
      · simp [List.count_replicate, same, Ne.symm same]

noncomputable def conjunctionCounter (time : ℝ) (arity : ℕ) : Snapshot 1 :=
  { preparedTeacher time with
    x := fun i c => match c with
      | .z 0 => -(3 / 5 : ℝ) * (arity - 1 : ℕ)
      | other => (preparedTeacher time).x i other
    pending := [] }

private theorem conjunction_counter_physical {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ)
    (arity : ℕ) : PhysicalInvariant θ (conjunctionCounter time arity) := by
  let phys := preparedTeacher_physical box time []
  refine ⟨phys.region, ?_, phys.recovery_cap, phys.reserve⟩
  intro i p
  have cap := phys.gain_cap i p
  change (0 : ℝ) ≤ Real.log ((θ i).cap p) at cap
  have nonpositive : (conjunctionCounter time arity).x i (.z p) ≤ 0 := by
    fin_cases p
    · change -(3 / 5 : ℝ) * (arity - 1 : ℕ) ≤ 0
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    · exact le_rfl
    · exact le_rfl
  exact nonpositive.trans cap

noncomputable def conjunctionProbe (read : ℝ) : Delivery 1 := ⟨0, 0, read⟩

private theorem calendar_limit {time read : ℝ} (before : time < read) (dates : List ℝ)
    (beforeRead : ∀ d ∈ dates, d + 15 / 2 < read) :
    ∃ limit, time ≤ limit ∧ (∀ d ∈ dates, d + 15 / 2 ≤ limit) ∧ limit < read := by
  induction dates with
  | nil => exact ⟨time, le_rfl, by simp, before⟩
  | cons d ds ih =>
    obtain ⟨limit, tlim, dlim, rlim⟩ := ih (fun x hx => beforeRead x (by simp [hx]))
    refine ⟨max limit (d + 15 / 2), tlim.trans (le_max_left _ _), ?_,
      max_lt rlim (beforeRead d (by simp))⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_right _ _
    · exact (dlim x hx).trans (le_max_left _ _)

/-- A native threshold test of any positive arity. The list is the actual
dose calendar. Missing slots can be anywhere, provided the admitted doses
remain separated and the common read is later than every dose cycle. -/
theorem native_conjunction_counter_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (time read horizon : ℝ) (arity : ℕ) (dates : List ℝ)
    (positive : 0 < arity) (capacity : dates.length ≤ arity)
    (before : time < read) (afterRead : read + 23 ≤ horizon)
    (future : ∀ d ∈ dates, time < d) (beforeRead : ∀ d ∈ dates, d + 15 / 2 < read)
    (separated : dates.Pairwise (fun a b => a + 8 ≤ b)) :
    Nonempty (CalendarDoseReadout θ ((conjunctionCounter time arity).requeue (conjunctionDoseTokens 0 dates))
      (conjunctionDoseTokens 0 dates) (conjunctionProbe read) horizon (decide (dates.length = arity))) := by
  let start := (conjunctionCounter time arity).requeue (conjunctionDoseTokens 0 dates)
  have p := conjunction_counter_physical box time arity
  have phys : PhysicalInvariant θ start := ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩
  have initialGain : start.x 0 (.z 0) = -(3 / 5 : ℝ) * (arity - 1 : ℕ) := rfl
  have arityCast : ((arity - 1 : ℕ) : ℝ) = (arity : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ arity), Nat.cast_one]
  have bound : start.x 0 (.z 0) + (3 / 5 : ℝ) * dates.length ≤ 3 / 5 := by
    rw [initialGain, arityCast]
    have h : (dates.length : ℝ) ≤ arity := by exact_mod_cast capacity
    linarith
  obtain ⟨limit, timeLimit, doseLimit, limitRead⟩ := calendar_limit before dates beforeRead
  obtain ⟨run, runLimit⟩ := sparse_dose_run_exists box phys
    (by simp [RawValid, start, Snapshot.requeue, conjunctionCounter, preparedTeacher])
    ⟨rfl, by norm_num [start, Snapshot.requeue, conjunctionCounter, preparedTeacher],
      fun _ => ⟨rfl, by norm_num [start, Snapshot.requeue, conjunctionCounter, preparedTeacher, RestBand]⟩⟩
    (fun _ => rfl) rfl timeLimit future doseLimit separated bound
  apply calendar_dose_readout_exists box run phys (runLimit.trans_lt limitRead) afterRead rfl
  change if decide (dates.length = arity) then
    start.x 0 (.z 0) + (3 / 5 : ℝ) * ((conjunctionDoseTokens 0 dates).map Delivery.port).count 0 = 3 / 5
    else start.x 0 (.z 0) + (3 / 5 : ℝ) * ((conjunctionDoseTokens 0 dates).map Delivery.port).count 0 ≤ 0
  rw [dose_tokens_ports, List.count_replicate_self, initialGain, arityCast]
  by_cases full : dates.length = arity
  · simp [full]; ring
  · simp [full]
    have h : (dates.length : ℝ) + 1 ≤ arity := by exact_mod_cast (show dates.length + 1 ≤ arity by omega)
    linarith


private noncomputable def preparationReport (time : ℝ) : ℝ → List (Delivery 1) :=
  fixedCalendar (time + 69) [⟨0, 0, time + 70⟩]

private noncomputable def practiceReport (time : ℝ) : ℝ → List (Delivery 1) :=
  fixedCalendar (time + 69) [⟨0, 0, time + 78⟩]

private noncomputable def conjunctionInput (time : ℝ) : HeadRoutes 2 :=
  fun i F => atCell 1 (preparationReport time) i F ++ atCell 0 (practiceReport time) i F

private theorem conjunction_input_strict (time : ℝ) : StrictHeadRoutes (conjunctionInput time) := by
  intro i F d member
  rcases List.mem_append.mp member with prep | practice
  · refine atCell_strict 1 (fixedCalendar_strict ?_) i F d prep
    intro token h
    obtain rfl := List.mem_singleton.mp h
    change time + 69 ≤ time + 70
    linarith
  · refine atCell_strict 0 (fixedCalendar_strict ?_) i F d practice
    intro token h
    obtain rfl := List.mem_singleton.mp h
    change time + 69 ≤ time + 78
    linarith

private def conjunctionDates (time : ℝ) (prep practice : Bool) : List ℝ :=
  (if prep then [time + 70] else []) ++ (if practice then [time + 78] else [])

private noncomputable def conjunctionCredit : HeadRoutes 3 :=
  atCell 0 (fun F => [⟨0, 0, F + 7 / 20⟩])

private theorem conjunction_credit_strict : StrictHeadRoutes conjunctionCredit := by
  refine atCell_strict 0 ?_
  intro F d member
  obtain rfl := List.mem_singleton.mp member
  change F < F + 7 / 20
  linarith

private def trialPairRouter : Router 2 :=
  prependRouted (fun _ _ => []) (fun _ _ => [])

noncomputable def learnerConjunctionRouter (time : ℝ) : Router 4 :=
  prependRouted (prependRouted trialPairRouter (conjunctionInput time)) conjunctionCredit

private theorem learner_conjunction_router_strict (time : ℝ) :
    StrictCausalRouter (learnerConjunctionRouter time) := by
  have empty {n : ℕ} : StrictCausalRouter (fun (_ : Fin n) (_ : ℝ) => []) :=
    fun _ _ _ member => False.elim (List.not_mem_nil member)
  exact prepend_routed_causal
    (prepend_routed_causal (prepend_routed_causal empty (fun _ _ _ h => (List.not_mem_nil h).elim))
      (conjunction_input_strict time)) conjunction_credit_strict

private noncomputable def trialPair (time : ℝ) (prep practice : Bool) : Snapshot 2 :=
  queueHead {seriesTrial time false prep with time := time}
    {seriesTrial time true practice with time := time}

/-- Cells 0 through 3 are credit, conjunction counter, practice learner
and preparation learner. Only the common read pulse is queued for the
counter. Every counted pulse and the credit pulse come from actual FIREs. -/
noncomputable def learnerConjunctionStart (time : ℝ) (prep practice : Bool) : Snapshot 4 :=
  let counter := (conjunctionCounter time 2).requeue [conjunctionProbe (time + 87)]
  queueHead (queueHead (trialPair time prep practice) counter) ((preparedTeacher time).requeue [])

abbrev learnerConjunctionParameters (prep practice counter credit : Fin 1 → Parameters) :
    Fin 4 → Parameters :=
  prependParameters credit (prependParameters counter (prependParameters practice prep))

private theorem report_calendar {time slot : ℝ} {fire : Option ℝ} {passed : Bool}
    (flag : fire.isSome = passed) (window : ∀ F, fire = some F → F < time + 69) :
    fire.toList.flatMap (fixedCalendar (time + 69) [⟨0, 0, slot⟩]) =
      conjunctionDoseTokens 0 (if passed then [slot] else []) := by
  cases fire with
  | none =>
    have eq : passed = false := flag.symm
    simp [eq, conjunctionDoseTokens]
  | some F =>
    have eq : passed = true := flag.symm
    simp [eq, conjunctionDoseTokens, fixedCalendar, window F rfl]

private theorem report_length {fire : Option ℝ} {passed : Bool} (flag : fire.isSome = passed) :
    fire.toList.length = if passed then 1 else 0 := by
  cases fire <;> rw [← flag] <;> rfl

private theorem learner_conjunction_physical {θP θR θA θC ε}
    (prepBox : @PhysicalBox 1 θP ε) (practiceBox : @PhysicalBox 1 θR ε)
    (counterBox : @PhysicalBox 1 θA ε) (creditBox : @PhysicalBox 1 θC ε)
    (time : ℝ) (prep practice : Bool) :
    PhysicalInvariant (learnerConjunctionParameters θP θR θA θC)
      (learnerConjunctionStart time prep practice) := by
  have p := readout_learner_physical prepBox time (preparationTrial prep) 0
  have r := readout_learner_physical practiceBox time (practiceTrial practice) 1
  have pp : PhysicalInvariant θP {seriesTrial time false prep with time := time} :=
    ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩
  have rp : PhysicalInvariant θR {seriesTrial time true practice with time := time} :=
    ⟨r.region, r.gain_cap, r.recovery_cap, r.reserve⟩
  exact prepend_physical
    (prepend_physical (prepend_physical pp rp _)
      (by
        have c := conjunction_counter_physical counterBox time 2
        exact ⟨c.region, c.gain_cap, c.recovery_cap, c.reserve⟩) _)
    (preparedTeacher_physical creditBox time []) _

/-- A single strictly causal router realizes all four rows of the AND truth
table. Each learner is trained and read in the same physical execution;
the counter reads their reports and issues one credit precisely when both
lessons meet the learner's requirements. -/
theorem native_learner_conjunction {θP θR θA θC ε}
    (prepBox : @PhysicalBox 1 θP ε) (practiceBox : @PhysicalBox 1 θR ε)
    (counterBox : @PhysicalBox 1 θA ε) (creditBox : @PhysicalBox 1 θC ε)
    (time : ℝ) (prep practice : Bool) :
    let θ := learnerConjunctionParameters θP θR θA θC
    let route := learnerConjunctionRouter time
    let start := learnerConjunctionStart time prep practice
    let T := time + 115
    ∃ (final : Snapshot 4) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing T ∧
      (((preparationTrial prep).train ⟨3, 3⟩).retained = true ↔ (e.emissionTimes 3).length = 1) ∧
      (((practiceTrial practice).train ⟨3, 3⟩).retained = true ↔ (e.emissionTimes 2).length = 1) ∧
      (e.emissionTimes 1).length = (if prep && practice then 1 else 0) ∧
      lessonReceipts e.deliveries 1 = (e.emissionTimes 3).length + (e.emissionTimes 2).length + 1 ∧
      (∀ p, final.x 0 (.z p) = if p = 0 ∧ (prep && practice) then 3 / 5 else 0) ∧
      (∀ otherFinal (other : CrossingExecution θ route start otherFinal),
        CrossingCompleteThrough other T →
        otherFinal.ObservationalEq final ∧
        ∀ i, other.execution.emissionTimes i = e.emissionTimes i) := by
  let T := time + 115
  obtain ⟨p, prepFire, prepFlag, prepWindow, prepEmissions, _⟩ :=
    staged_trial_exists prepBox (time := time) (clock := time) (T := T) le_rfl (by dsimp [T]; linarith)
      false prep
  obtain ⟨r, practiceFire, practiceFlag, practiceWindow, practiceEmissions, _⟩ :=
    staged_trial_exists practiceBox (time := time) (clock := time) (T := T) le_rfl (by dsimp [T]; linarith)
      true practice
  obtain ⟨pair, pairComplete⟩ :=
    p.execution.prepend_independent_complete r.execution rfl p.complete r.complete
  have pairPositive := pair.contacts_transversal p.positive r.positive
  have prepDates : pair.execution.emissionTimes 1 = prepFire.toList := by
    change pair.execution.emissionTimes (0 : Fin 1).succ = _
    rw [pair.tail_emission_times, prepEmissions]
  have practiceDates : pair.execution.emissionTimes 0 = practiceFire.toList :=
    pair.head_emission_times.trans practiceEmissions
  let dates := conjunctionDates time prep practice
  have pairQueue : (pair.execution.headInputQueue (conjunctionInput time)).Perm (conjunctionDoseTokens 0 dates) := by
    have split := (List.flatMap_append_perm pair.execution.ledger.emissions
      (fun event => atCell 1 (preparationReport time) event.1 event.2)
      (fun event => atCell 0 (practiceReport time) event.1 event.2)).symm
    change (pair.execution.headInputQueue (conjunctionInput time)).Perm
      (pair.execution.headInputQueue (atCell 1 (preparationReport time)) ++
        pair.execution.headInputQueue (atCell 0 (practiceReport time))) at split
    refine split.trans (List.Perm.of_eq ?_)
    rw [atCell_inputs, atCell_inputs, prepDates, practiceDates, preparationReport, practiceReport,
      report_calendar prepFlag (fun F h => by linarith [(prepWindow F h).2]),
      report_calendar practiceFlag (fun F h => by linarith [(practiceWindow F h).2])]
    exact List.map_append.symm
  have capacity : dates.length ≤ 2 := by
    cases prep <;> cases practice <;> norm_num [dates, conjunctionDates]
  have count (F : ℝ) (mem : F ∈ dates) : F = time + 70 ∨ F = time + 78 := by
    cases prep <;> cases practice <;> simp [dates, conjunctionDates] at mem <;> tauto
  have spacing : dates.Pairwise (fun a b => a + 8 ≤ b) := by
    cases prep <;> cases practice <;> simp [dates, conjunctionDates]
    linarith
  obtain ⟨counter⟩ := native_conjunction_counter_exists counterBox time (time + 87) T 2 dates
    (by decide) capacity (by linarith) (by dsimp [T]; linarith)
    (fun d hd => by rcases count d hd with rfl | rfl <;> linarith)
    (fun d hd => by rcases count d hd with rfl | rfl <;> linarith) spacing
  have counterFlag : counter.fire.isSome = (prep && practice) := by
    rw [counter.reports]
    cases prep <;> cases practice <;> simp [dates, conjunctionDates]
  let counterSource := withFuture ((conjunctionCounter time 2).requeue (conjunctionDoseTokens 0 dates))
    [conjunctionProbe (time + 87)]
  have counterBalance := stage_balance pair.execution counterSource [conjunctionProbe (time + 87)]
    (conjunctionInput time) (List.Perm.cons _ pairQueue)
  obtain ⟨counted⟩ := pair.execution.prepend_causal_result counter.execution rfl
    (pairComplete.1.trans counter.complete.1.symm) (conjunctionInput time) (conjunction_input_strict time)
    _ counterBalance
  have countedComplete := counted.complete pairComplete counter.complete
  have countedPositive := counted.contacts_transversal pairPositive counter.transverse
  have counterDates : counted.execution.emissionTimes 0 = counter.fire.toList := by
    rw [counted.head_emission_times, Execution.emissionTimes, counter.emissions]
    cases counter.fire <;> rfl
  obtain ⟨credit⟩ := credit_response_exists creditBox (T := T) (credit := 0) (by dsimp [T]; linarith)
    (fun F h => by
      obtain ⟨early, late⟩ := counter.window F h
      change time + 87 < F at early
      change F < time + 87 + 1 at late
      dsimp [T]
      constructor <;> linarith)
  let creditSource := (preparedTeacher time).requeue
    (counter.fire.toList.map (fun F => ⟨0, 0, F + 7 / 20⟩))
  have creditQueue : counted.execution.headInputQueue conjunctionCredit = creditSource.pending := by
    rw [conjunctionCredit, atCell_inputs, counterDates]
    cases h : counter.fire <;> simp [creditSource, Snapshot.requeue, h]
  have creditBalance := HeadQueueBalance.initial counted.execution creditSource conjunctionCredit creditQueue.symm
  obtain ⟨whole⟩ := counted.execution.prepend_causal_result credit.execution rfl
    (countedComplete.1.trans credit.complete.1.symm) conjunctionCredit conjunction_credit_strict _ creditBalance
  have complete := whole.complete countedComplete credit.complete
  have positive := whole.contacts_transversal countedPositive credit.positive
  have box := prepend_box (prepend_box (prepend_box prepBox practiceBox) counterBox) creditBox
  have physical := learner_conjunction_physical prepBox practiceBox counterBox creditBox time prep practice
  have initial : InitiallyBelowReady (learnerConjunctionStart time prep practice) := by
    intro i c h
    cases c with
    | q => fin_cases i <;> change (1 / 10 : ℝ) < 1 <;> norm_num
    | m p => fin_cases i <;> change (1 / 40 : ℝ) < 1 <;> norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  have prepOut : whole.execution.emissionTimes 3 = prepFire.toList := by
    change whole.execution.emissionTimes (1 : Fin 2).succ.succ = _
    rw [whole.tail_emission_times, counted.tail_emission_times, prepDates]
  have practiceOut : whole.execution.emissionTimes 2 = practiceFire.toList := by
    change whole.execution.emissionTimes (0 : Fin 2).succ.succ = _
    rw [whole.tail_emission_times, counted.tail_emission_times, practiceDates]
  let e : Execution (learnerConjunctionParameters θP θR θA θC) (learnerConjunctionRouter time)
      (learnerConjunctionStart time prep practice) _ := whole.execution
  change e.emissionTimes 3 = _ at prepOut
  change e.emissionTimes 2 = _ at practiceOut
  refine ⟨_, e, e.toCrossing initial box physical positive, rfl,
    complete.toCrossing e initial box physical positive, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prepOut, report_length prepFlag]
    cases prep <;> decide
  · rw [practiceOut, report_length practiceFlag]
    cases practice <;> decide
  · change (whole.execution.emissionTimes (0 : Fin 3).succ).length = _
    rw [whole.tail_emission_times, counterDates, report_length counterFlag]
  · change lessonReceipts whole.execution.deliveries (0 : Fin 3).succ = _
    rw [CausalTraceBalance.tail_receipts whole.trace, CausalTraceBalance.head_receipts counted.trace]
    change counter.execution.deliveries.length = (e.emissionTimes 3).length + (e.emissionTimes 2).length + 1
    calc
      _ = (conjunctionDoseTokens 0 dates ++ [conjunctionProbe (time + 87)]).length :=
        congrArg List.length counter.deliveries
      _ = (e.emissionTimes 3).length + (e.emissionTimes 2).length + 1 := by
        rw [prepOut, practiceOut, report_length prepFlag, report_length practiceFlag]
        cases prep <;> cases practice <;> rfl
  · intro p
    change credit.final.x 0 (.z p) = _
    rw [credit.written, counterFlag]
  · intro otherFinal other done
    obtain ⟨native, same⟩ := other.execution.toNative_of_transverse_completion e
      (learner_conjunction_router_strict time) box physical complete positive (le_of_eq done.1)
    have weak := done.toWeak_of_native other native same initial box physical
    exact ⟨(e.observational_unique_weak box other.execution physical complete positive weak).1.symm,
      fun i => (e.emissionTimes_unique_weak other.execution box physical complete positive weak i).symm⟩

end RecursiveLearning.Native
