import Thresholds.AdaptiveRounds

/-! A finite policy experiment. A failed calibration trial can route a
write packet to one policy cell. Two later reads of that same cell choose
which lesson edit to test on fresh, identically calibrated learners. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

private noncomputable def policyWrites (base : ℝ) : List ℝ :=
  [base + 1, base + 25, base + 49]

private noncomputable def policyRead (base : ℝ) (second : Bool) : ℝ :=
  base + if second then 273 else 73

private noncomputable def policyReads (base : ℝ) : List ℝ :=
  [policyRead base false, policyRead base true]

private noncomputable def policyReadTokens (base : ℝ) : List (Delivery 1) :=
  conjunctionDoseTokens 0 (policyReads base)

private noncomputable def policyContacts {n} (layout : ReportLayout n) (source : Fin n)
    (enabled : Bool) : HeadRoutes n :=
  forwardReport source (layout.windows source)
    (if enabled then conjunctionDoseTokens 0 (policyWrites layout.last) else [])

private noncomputable def policyMemoryLayout {n} (layout : ReportLayout n) (source : Fin n)
    (enabled : Bool) : ReportLayout (n + 1) :=
  let base := layout.last
  let receiver := (conjunctionCounter layout.start.time 3).requeue (policyReadTokens base)
  ⟨queueHead layout.start receiver, prependRouted layout.route (policyContacts layout source enabled),
    Fin.cases (counterWindow (policyRead base false)) layout.windows, policyRead base false + 1⟩

private theorem policy_memory_timed {n} {layout : ReportLayout n} (timed : layout.WellTimed)
    (source : Fin n) (enabled : Bool) : (policyMemoryLayout layout source enabled).WellTimed := by
  have greater : layout.last < (policyMemoryLayout layout source enabled).last := by
    change layout.last < layout.last + 73 + 1
    linarith
  refine ⟨timed.1.trans greater, ?_⟩
  intro i
  cases i using Fin.cases with
  | zero => exact le_rfl
  | succ i => exact (timed.2 i).trans greater.le

private theorem policy_memory_run {n θ θH ε T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (prior : CompiledRun θ layout T bits) (box : @PhysicalBox 1 θH ε)
    (source : Fin n) (enabled : Bool) (timed : layout.WellTimed)
    (horizon : policyRead layout.last true + 23 < T) :
    let trained := enabled && bits source
    ∃ run : CompiledRun (prependParameters θH θ) (policyMemoryLayout layout source enabled) T
        (Fin.cases trained bits),
      Reports run.execution 0 (counterWindow (policyRead layout.last true)) trained ∧
      run.final.x 0 (.z 0) = (if trained then 3 / 5 else 0) ∧
      lessonReceipts run.execution.deliveries 0 = (if trained then 5 else 2) := by
  let base := layout.last
  let trained := enabled && bits source
  let writes := if trained then policyWrites base else []
  let dates := writes ++ policyReads base
  let contacts := policyContacts layout source enabled
  have future : ∀ d ∈ dates, layout.start.time < d := by
    intro d hd
    have late : base < d := by
      cases h : trained <;>
        simp [dates, writes, h, policyWrites, policyReads, policyRead] at hd
      all_goals rcases hd with rfl | hd
      all_goals try rcases hd with rfl | hd
      all_goals try rcases hd with rfl | hd
      all_goals try rcases hd with rfl | rfl
      all_goals linarith
    exact timed.1.trans late
  have finish : ∀ d ∈ dates, d + 23 < T := by
    intro d hd
    change base + 273 + 23 < T at horizon
    cases h : trained <;>
      simp [dates, writes, h, policyWrites, policyReads, policyRead] at hd
    all_goals rcases hd with rfl | hd
    all_goals try rcases hd with rfl | hd
    all_goals try rcases hd with rfl | hd
    all_goals try rcases hd with rfl | rfl
    all_goals linarith
  have spacing : dates.Pairwise (fun a b => a + 24 ≤ b) := by
    cases h : trained <;> simp [dates, writes, h, policyWrites, policyReads, policyRead, List.pairwise_cons] <;> (repeat' constructor) <;> linarith
  have before : layout.start.time < T := by
    change base + 273 + 23 < T at horizon
    linarith [timed.1]
  obtain ⟨cell, gain, delivered, reads⟩ :=
    threshold_calendar_reports box layout.start.time T 3 dates (by decide) before future finish spacing
  have flag : decide (3 ≤ writes.length) = trained := by
    cases h : trained <;> simp [writes, h, policyWrites]
  have first := reads writes (policyRead base false) [policyRead base true] rfl
  rw [flag] at first
  have second := reads (writes ++ [policyRead base false]) (policyRead base true) [] (by
    simp [dates, policyReads, List.append_assoc])
  have secondFlag : decide (3 ≤ (writes ++ [policyRead base false]).length) = trained := by
    cases h : trained <;> simp [writes, h, policyWrites]
  rw [secondFlag] at second
  have strict : StrictHeadRoutes contacts := by
    apply forward_report_strict
    intro d hd
    have stop := timed.2 source
    cases enabled with
    | false => simp at hd
    | true =>
      simp [conjunctionDoseTokens, policyWrites] at hd
      rcases hd with rfl | rfl | rfl <;> linarith
  have routed : prior.execution.headInputQueue contacts = conjunctionDoseTokens 0 writes := by
    unfold contacts policyContacts
    rw [forward_report_inputs prior.execution source (layout.windows source) _ (bits source)
      (prior.reports source)]
    cases enabled <;> cases h : bits source <;> simp [writes, trained, h, conjunctionDoseTokens, base]
  have inputs : (policyReadTokens base ++ prior.execution.headInputQueue contacts).Perm
      ((conjunctionCounter layout.start.time 3).requeue (conjunctionDoseTokens 0 dates)).pending := by
    rw [routed]
    change (conjunctionDoseTokens 0 (policyReads base) ++ conjunctionDoseTokens 0 writes).Perm
      (conjunctionDoseTokens 0 (writes ++ policyReads base))
    rw [show conjunctionDoseTokens 0 (writes ++ policyReads base) =
      conjunctionDoseTokens 0 writes ++ conjunctionDoseTokens 0 (policyReads base) by
        simp [conjunctionDoseTokens]]
    exact List.perm_append_comm
  obtain ⟨weave⟩ := compose_scheduled_receiver prior.execution cell.execution prior.complete cell.complete
    rfl (policyReadTokens base) contacts strict inputs
  let e : Execution (prependParameters θH θ) (policyMemoryLayout layout source enabled).route
      (policyMemoryLayout layout source enabled).start _ := weave.execution
  have hp := conjunction_counter_physical box layout.start.time 3
  have init := threshold_probe_initial layout.start.time layout.start.time 3 []
  have reports (i : Fin (n + 1)) :
      Reports e i ((policyMemoryLayout layout source enabled).windows i) (Fin.cases trained bits i) := by
    cases i using Fin.cases with
    | zero =>
      change Reports e 0 (counterWindow (policyRead base false)) trained
      unfold Reports ReportWindow.dates
      rw [show e.emissionTimes 0 = _ from weave.head_emission_times]
      exact first
    | succ i =>
      unfold Reports ReportWindow.dates
      rw [show e.emissionTimes i.succ = _ from weave.tail_emission_times i]
      exact prior.reports i
  let run : CompiledRun (prependParameters θH θ) (policyMemoryLayout layout source enabled) T
      (Fin.cases trained bits) :=
    ⟨_, e, weave.complete prior.complete cell.complete, weave.contacts_transversal prior.positive cell.positive,
      reports, prepend_physical prior.physical ⟨hp.region, hp.gain_cap, hp.recovery_cap, hp.reserve⟩ _,
      prepend_initial_ready prior.initial init, prepend_routed_causal prior.causal strict⟩
  refine ⟨run, ?_, ?_, ?_⟩
  · unfold Reports ReportWindow.dates
    change ((e.emissionTimes 0).filter _).length = _
    rw [show e.emissionTimes 0 = _ from weave.head_emission_times]
    exact second
  · change cell.final.x 0 (.z 0) = (if trained then 3 / 5 else 0)
    rw [gain]
    cases h : trained <;> norm_num [dates, writes, h, policyWrites, policyReads]
  · change lessonReceipts weave.execution.deliveries 0 = (if trained then 5 else 2)
    rw [CausalTraceBalance.head_receipts weave.trace, delivered]
    cases h : trained <;> simp [dates, writes, h, policyWrites, policyReads, conjunctionDoseTokens]

/-- Each candidate drops one pulse from the same two-by-two lesson. -/
private def policyLesson (practice : Bool) : Lesson :=
  if practice then ⟨2, 1⟩ else ⟨1, 2⟩

private def policyNeeds (hardPrep : Bool) : Learner :=
  if hardPrep then ⟨2, 1⟩ else ⟨1, 2⟩

private noncomputable def policyTrial (practice hardPrep : Bool) : AdaptiveTrial where
  lesson := policyLesson practice
  testPractice := practice
  passes := decide (practice = hardPrep)
  needs := policyNeeds hardPrep
  birthGain := if practice = hardPrep then 0 else -(3 / 5)
  nonpositive := by cases practice <;> cases hardPrep <;> norm_num
  capacity := by cases practice <;> decide
  gainTest := by
    cases practice <;> cases hardPrep <;>
      norm_num [policyLesson, lessonPorts, trialPort]
  correct := by cases practice <;> cases hardPrep <;> decide

private noncomputable def roundLayout {n} (layout : ReportLayout n)
    (memory : Fin n) (hardPrep : Bool) : ReportLayout (n + 1 + 1 + 1) :=
  let withNot := layout.appendNot memory
  let withPractice := withNot.appendTrial memory.succ (policyTrial true hardPrep)
  withPractice.appendTrial (0 : Fin (n + 1)).succ (policyTrial false hardPrep)

private noncomputable def roundBits {n} (bits : Fin n → Bool) (memory : Fin n) (hardPrep : Bool) :
    Fin (n + 1 + 1 + 1) → Bool :=
  Fin.cases (!bits memory && (policyTrial false hardPrep).passes)
    (Fin.cases (bits memory && (policyTrial true hardPrep).passes) (Fin.cases (!bits memory) bits))

private theorem round_timed {n} {layout : ReportLayout n} (timed : layout.WellTimed)
    (memory : Fin n) (hardPrep : Bool) : (roundLayout layout memory hardPrep).WellTimed :=
  append_trial_timed
    (append_trial_timed (append_not_timed timed memory) memory.succ (policyTrial true hardPrep))
    (0 : Fin (n + 1)).succ (policyTrial false hardPrep)

private theorem round_run {n θ θN θP θQ ε T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (prior : CompiledRun θ layout T bits) (notBox : @PhysicalBox 1 θN ε)
    (practiceBox : @PhysicalBox 1 θP ε) (prepBox : @PhysicalBox 1 θQ ε)
    (memory : Fin n) (hardPrep : Bool) (timed : layout.WellTimed)
    (horizon : (roundLayout layout memory hardPrep).last + 75 < T) :
    ∃ run : CompiledRun (prependParameters θQ (prependParameters θP (prependParameters θN θ)))
        (roundLayout layout memory hardPrep) T (roundBits bits memory hardPrep),
      lessonReceipts run.execution.deliveries 0 = (if bits memory then 0 else 4) ∧
      lessonReceipts run.execution.deliveries 1 = (if bits memory then 4 else 0) ∧
      (∀ i, run.execution.emissionTimes i.succ.succ.succ = prior.execution.emissionTimes i) ∧
      (∀ i, run.final.x i.succ.succ.succ = prior.final.x i) ∧
      (∀ i, lessonReceipts run.execution.deliveries i.succ.succ.succ =
        lessonReceipts prior.execution.deliveries i) := by
  have later : layout.last + 153 + 75 < T := by
    change layout.last + 1 + 18 + 1 + 66 + 1 + 66 + 75 < T at horizon
    linarith
  obtain ⟨neg, negValues, negReceipts, negDates⟩ := append_not_run_with_dates prior notBox memory timed
    (by change layout.last + 1 + 18 + 45 < T; linarith)
  have negTimed := append_not_timed timed memory
  obtain ⟨practice, practiceCount, practiceValues, practiceReceipts, practiceDates⟩ :=
    append_trial_run neg practiceBox memory.succ (policyTrial true hardPrep) negTimed
      (by change layout.last + 1 + 18 + 1 + 66 + 75 < T; linarith)
  obtain ⟨prep, prepCount, prepValues, prepReceipts, prepDates⟩ :=
    append_trial_run practice prepBox (0 : Fin (n + 1)).succ (policyTrial false hardPrep)
      (append_trial_timed negTimed memory.succ (policyTrial true hardPrep)) horizon
  refine ⟨prep, ?_, ?_, ?_, ?_, ?_⟩
  · change lessonReceipts prep.execution.deliveries 0 = _
    change _ = (if !bits memory then (policyLesson false).cost + 1 else 0) at prepCount
    by_cases h : bits memory = true
    · simpa [h] using prepCount
    · have off : bits memory = false := Bool.eq_false_iff.mpr h
      simpa [off, policyLesson, Lesson.cost] using prepCount
  · exact (prepReceipts 0).trans practiceCount
  · exact fun i => (prepDates i.succ.succ).trans ((practiceDates i.succ).trans (negDates i))
  · exact fun i => (prepValues i.succ.succ).trans ((practiceValues i.succ).trans (negValues i))
  · exact fun i => (prepReceipts i.succ.succ).trans
      ((practiceReceipts i.succ).trans (negReceipts i))

private def calibrationNeed (hardPrep : Bool) : ℕ := if hardPrep then 2 else 1

private noncomputable def calibrationLayout (time : ℝ) (hardPrep : Bool) : ReportLayout 1 :=
  let read := thresholdReadTime time 1
  ⟨thresholdProbeStart time read (calibrationNeed hardPrep) (thresholdCalendar time 1),
    fun _ _ => [], fun _ => counterWindow read, read + 1⟩

private theorem calibration_timed (time : ℝ) (hardPrep : Bool) :
    (calibrationLayout time hardPrep).WellTimed := by
  refine ⟨?_, fun _ => le_rfl⟩
  change time < time + 24 * (((1 : ℕ) : ℝ) + 1) + 1
  linarith

private theorem calibration_run {θ ε T} (box : @PhysicalBox 1 θ ε) (time : ℝ)
    (hardPrep : Bool) (horizon : time + 72 ≤ T) :
    Nonempty (CompiledRun θ (calibrationLayout time hardPrep) T (fun _ => !hardPrep)) := by
  obtain ⟨cell⟩ := threshold_count_probe_exists_until box time time T (calibrationNeed hardPrep) 1
    (by cases hardPrep <;> decide) le_rfl (by norm_num [thresholdReadTime]; linarith)
  have bit : decide (calibrationNeed hardPrep ≤ 1) = !hardPrep := by cases hardPrep <;> decide
  rw [bit] at cell
  exact ⟨⟨_, cell.execution, cell.complete, cell.transverse,
    fun i => by rw [Subsingleton.elim i 0]; exact cell.reports,
    threshold_probe_physical box _ _ _ _, threshold_probe_initial _ _ _ _, fun _ _ _ h => by change _ ∈ ([] : List (Delivery 1)) at h; exact (List.not_mem_nil h).elim⟩⟩

private noncomputable def laterWindow {n} (layout : ReportLayout n) (memory : Fin n)
    (date : ℝ) : ReportLayout n :=
  { layout with windows := Function.update layout.windows memory (counterWindow date), last := date + 1 }

private theorem later_window_timed {n} {layout : ReportLayout n} (timed : layout.WellTimed)
    (memory : Fin n) {date : ℝ} (later : layout.last < date) :
    (laterWindow layout memory date).WellTimed := by
  refine ⟨by change layout.start.time < date + 1; linarith [timed.1], ?_⟩
  intro i
  by_cases h : i = memory
  · subst i
    simp [laterWindow, counterWindow]
  · simp [laterWindow, Function.update_of_ne h]
    linarith [timed.2 i]

private def later_window_run {n θ T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (run : CompiledRun θ layout T bits) (memory : Fin n) (date : ℝ)
    (report : Reports run.execution memory (counterWindow date) (bits memory)) :
    CompiledRun θ (laterWindow layout memory date) T bits :=
  ⟨run.final, run.execution, run.complete, run.positive, fun i => by
    by_cases h : i = memory
    · subst i
      simpa [laterWindow] using report
    · simpa [laterWindow, Function.update_of_ne h] using run.reports i,
    run.physical, run.initial, run.causal⟩

private noncomputable def calibrationFeedback (time : ℝ) (hardPrep : Bool) : ReportLayout 2 :=
  (calibrationLayout time hardPrep).appendNot 0

private noncomputable def firstRound (time : ℝ) (hardPrep enabled : Bool) : ReportLayout 6 :=
  roundLayout (policyMemoryLayout (calibrationFeedback time hardPrep) 0 enabled) 0 hardPrep

private noncomputable def secondRead (time : ℝ) (hardPrep : Bool) : ℝ :=
  policyRead (calibrationFeedback time hardPrep).last true

/-- The enabled flag cuts the feedback wire from calibration to memory.
Both policy reads and both evaluation rounds remain scheduled. -/
noncomputable def policyExperimentLayout (time : ℝ) (hardPrep enabled : Bool) : ReportLayout 9 :=
  roundLayout (laterWindow (firstRound time hardPrep enabled) 3 (secondRead time hardPrep)) 3 hardPrep

private theorem round_same_sources {n} {a b : ReportLayout n} (same : a.SameSources b)
    (memory : Fin n) (p q : Bool) :
    (roundLayout a memory p).SameSources (roundLayout b memory q) :=
  same_trial_sources
    (same_trial_sources (same_not_sources same memory) memory.succ
      (policyTrial true p) (policyTrial true q) (fun _ => rfl))
    (0 : Fin (n + 1)).succ (policyTrial false p) (policyTrial false q) (fun _ => rfl)

private theorem memory_same_sources {n} {a b : ReportLayout n} (same : a.SameSources b)
    (source : Fin n) (enabled : Bool) :
    (policyMemoryLayout a source enabled).SameSources (policyMemoryLayout b source enabled) := by
  obtain ⟨⟨routes, windows, times⟩, pending⟩ := same
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [policyMemoryLayout, policyContacts, routes, windows, times]
  · simp only [policyMemoryLayout, times, windows]
  · simp only [policyMemoryLayout, times]
  · change (policyReadTokens a.last).map Delivery.head ++ a.start.pending.map Delivery.succ =
      (policyReadTokens b.last).map Delivery.head ++ b.start.pending.map Delivery.succ
    rw [times, pending]

private theorem later_window_same_sources {n} {a b : ReportLayout n} (same : a.SameSources b)
    (memory : Fin n) (date : ℝ) :
    (laterWindow a memory date).SameSources (laterWindow b memory date) := by
  obtain ⟨⟨routes, windows, _⟩, pending⟩ := same
  exact ⟨⟨routes, congrArg (fun w : Fin n → ReportWindow => Function.update w memory (counterWindow date)) windows,
    rfl⟩, pending⟩

/-- The two profiles differ in calibrated gains, with identical router,
report windows, schedule and source queue for each feedback setting. -/
theorem policy_experiment_same_sources (time : ℝ) (hardPrep enabled : Bool) :
    (policyExperimentLayout time hardPrep enabled).SameSources
      (policyExperimentLayout time false enabled) := by
  have seed : (calibrationLayout time hardPrep).SameSources (calibrationLayout time false) :=
    ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  have feedback := same_not_sources seed 0
  have memory := memory_same_sources feedback 0 enabled
  have first := round_same_sources memory 0 hardPrep false
  have later := later_window_same_sources first 3 (secondRead time hardPrep)
  exact round_same_sources later 3 hardPrep false

set_option maxHeartbeats 2000000 in
theorem policy_experiment_cut_same_start (time : ℝ) (hardPrep : Bool) :
    (policyExperimentLayout time hardPrep true).start =
      (policyExperimentLayout time hardPrep false).start := by
  simp only [policyExperimentLayout, firstRound, roundLayout, laterWindow, secondRead,
    policyMemoryLayout, ReportLayout.appendTrial, ReportLayout.appendNot]

abbrev policyExperimentParameters
    (calibration diagnostic memory not₁ practice₁ prep₁ not₂ practice₂ prep₂ : Fin 1 → Parameters) :
    Fin 9 → Parameters :=
  prependParameters prep₂ (prependParameters practice₂ (prependParameters not₂
    (prependParameters prep₁ (prependParameters practice₁ (prependParameters not₁
      (prependParameters memory (prependParameters diagnostic calibration)))))))

private def memoryBits (hardPrep enabled : Bool) : Fin 3 → Bool :=
  Fin.cases (enabled && !(!hardPrep)) (Fin.cases (!(!hardPrep)) (fun _ => !hardPrep))

private noncomputable def experimentBits (hardPrep enabled : Bool) : Fin 9 → Bool :=
  roundBits (roundBits (memoryBits hardPrep enabled) 0 hardPrep) 3 hardPrep

/-- Number of first proposals accepted by the physical trial reports.
Each round activates one candidate. A report on the skipped branch
therefore contributes zero. -/
noncomputable def policyRoundAcceptances {θ route s u} (layout : ReportLayout 9)
    (e : @Execution 9 θ route s u) (second : Bool) : Nat :=
  let prep : Fin 9 := if second then 0 else 3
  let practice : Fin 9 := if second then 1 else 4
  ((layout.windows prep).dates e prep).length + ((layout.windows practice).dates e practice).length

/-- Exact receipts and outcomes for the single physical memory cell and
the four candidate receivers. The first pair of trial receivers is 3,4;
the second pair is 0,1. Cell 6 is read in both windows. -/
structure PolicyExperimentEffect {θ route s u} (e : @Execution 9 θ route s u)
    (time : ℝ) (hardPrep enabled : Bool) : Prop where
  firstRead : Reports e 6 (counterWindow (policyRead (calibrationFeedback time hardPrep).last false))
    (enabled && hardPrep)
  secondRead : Reports e 6 (counterWindow (secondRead time hardPrep)) (enabled && hardPrep)
  memoryGain : u.x 6 (.z 0) = (if enabled && hardPrep then 3 / 5 else 0)
  memoryReceipts : lessonReceipts e.deliveries 6 = (if enabled && hardPrep then 5 else 2)
  prepFirst : lessonReceipts e.deliveries 3 = (if enabled && hardPrep then 0 else 4)
  practiceFirst : lessonReceipts e.deliveries 4 = (if enabled && hardPrep then 4 else 0)
  prepSecond : lessonReceipts e.deliveries 0 = (if enabled && hardPrep then 0 else 4)
  practiceSecond : lessonReceipts e.deliveries 1 = (if enabled && hardPrep then 4 else 0)
  firstAccepted : policyRoundAcceptances (policyExperimentLayout time hardPrep enabled) e false =
    (if enabled || !hardPrep then 1 else 0)
  secondAccepted : policyRoundAcceptances (policyExperimentLayout time hardPrep enabled) e true =
    (if enabled || !hardPrep then 1 else 0)

private theorem PolicyExperimentEffect.transfer {θ route s u v}
    {e : @Execution 9 θ route s u} {other : Execution θ route s v}
    {time : ℝ} {hardPrep enabled : Bool} (effect : PolicyExperimentEffect e time hardPrep enabled)
    (physical : v.ObservationalEq u) (deliveries : other.deliveries.Perm e.deliveries)
    (fires : ∀ j, other.emissionTimes j = e.emissionTimes j) :
    PolicyExperimentEffect other time hardPrep enabled := by
  have dates (w : ReportWindow) (j : Fin 9) : w.dates other j = w.dates e j := by
    unfold ReportWindow.dates
    rw [fires]
  have receipts (j : Fin 9) :
      lessonReceipts other.deliveries j = lessonReceipts e.deliveries j :=
    (deliveries.filter _).length_eq
  have accepts (round : Bool) :
      policyRoundAcceptances (policyExperimentLayout time hardPrep enabled) other round =
        policyRoundAcceptances (policyExperimentLayout time hardPrep enabled) e round := by
    simp only [policyRoundAcceptances, dates]
  exact ⟨(congrArg List.length (dates _ 6)).trans effect.firstRead,
    (congrArg List.length (dates _ 6)).trans effect.secondRead,
    (congrArg (fun values => values 6 (.z 0)) physical.values).trans effect.memoryGain,
    (receipts 6).trans effect.memoryReceipts, (receipts 3).trans effect.prepFirst,
    (receipts 4).trans effect.practiceFirst, (receipts 0).trans effect.prepSecond,
    (receipts 1).trans effect.practiceSecond, (accepts false).trans effect.firstAccepted,
    (accepts true).trans effect.secondAccepted⟩

private theorem policy_experiment_run {θA θB θC θD θE θF θG θH θI ε}
    (a : @PhysicalBox 1 θA ε) (b : @PhysicalBox 1 θB ε) (c : @PhysicalBox 1 θC ε)
    (d : @PhysicalBox 1 θD ε) (e : @PhysicalBox 1 θE ε) (f : @PhysicalBox 1 θF ε)
    (g : @PhysicalBox 1 θG ε) (h : @PhysicalBox 1 θH ε) (i : @PhysicalBox 1 θI ε)
    (time : ℝ) (hardPrep enabled : Bool) :
    let θ := policyExperimentParameters θA θB θC θD θE θF θG θH θI
    ∃ run : CompiledRun θ (policyExperimentLayout time hardPrep enabled) (time + 600)
        (experimentBits hardPrep enabled),
      PolicyExperimentEffect run.execution time hardPrep enabled := by
  obtain ⟨seed⟩ := calibration_run (T := time + 600) a time hardPrep (by linarith)
  have seedTimed := calibration_timed time hardPrep
  obtain ⟨diagnostic, _, _, _⟩ := append_not_run_with_dates seed b 0 seedTimed (by
    change time + 24 * (((1 : ℕ) : ℝ) + 1) + 1 + 1 + 18 + 45 < time + 600
    norm_num
    linarith)
  have diagTimed := append_not_timed seedTimed 0
  obtain ⟨memory, readAgain, gain, memoryCount⟩ := policy_memory_run diagnostic c 0 enabled diagTimed (by
    change time + 24 * (((1 : ℕ) : ℝ) + 1) + 1 + 1 + 18 + 273 + 23 < time + 600
    norm_num
    linarith)
  have memoryTimed := policy_memory_timed diagTimed 0 enabled
  obtain ⟨first, firstPrep, firstPractice, firstDates, firstValues, firstCounts⟩ :=
    round_run memory d e f 0 hardPrep memoryTimed (by
      change time + 24 * (((1 : ℕ) : ℝ) + 1) + 1 + 1 + 18 + 73 + 1 + 1 + 18 + 1 + 66 + 1 + 66 + 75 < time + 600
      norm_num
      linarith)
  have firstTimed := round_timed memoryTimed 0 hardPrep
  have readDate : (firstRound time hardPrep enabled).last < secondRead time hardPrep := by
    change time + 24 * (((1 : ℕ) : ℝ) + 1) + 1 + 1 + 18 + 73 + 1 + 1 + 18 + 1 + 66 + 1 + 66 <
      time + 24 * (((1 : ℕ) : ℝ) + 1) + 1 + 1 + 18 + 273
    norm_num
    linarith
  have report : Reports first.execution (3 : Fin 6) (counterWindow (secondRead time hardPrep))
      (roundBits (memoryBits hardPrep enabled) 0 hardPrep 3) := by
    unfold Reports ReportWindow.dates
    rw [show (3 : Fin 6) = (0 : Fin 3).succ.succ.succ from rfl, firstDates]
    exact readAgain
  let retimed := later_window_run first 3 (secondRead time hardPrep) report
  have secondTimed := later_window_timed firstTimed 3 readDate
  obtain ⟨last, secondPrep, secondPractice, secondDates, secondValues, secondCounts⟩ :=
    round_run retimed g h i 3 hardPrep secondTimed (by
      change time + 24 * (((1 : ℕ) : ℝ) + 1) + 1 + 1 + 18 + 273 + 1 + 1 + 18 + 1 + 66 + 1 + 66 + 75 < time + 600
      norm_num
      linarith)
  have memoryDates : last.execution.emissionTimes 6 = memory.execution.emissionTimes 0 :=
    (secondDates 3).trans (firstDates 0)
  have firstReport : Reports memory.execution 0
      (counterWindow (policyRead (calibrationFeedback time hardPrep).last false)) (enabled && hardPrep) := by
    have h := memory.reports (0 : Fin 3)
    change Reports memory.execution 0
      (counterWindow (policyRead (calibrationFeedback time hardPrep).last false))
      (enabled && !(!hardPrep)) at h
    simpa only [Bool.not_not] using h
  have secondReport : Reports memory.execution 0
      (counterWindow (secondRead time hardPrep)) (enabled && hardPrep) := by
    change Reports memory.execution 0 (counterWindow (secondRead time hardPrep))
      (enabled && !(!hardPrep)) at readAgain
    simpa only [Bool.not_not] using readAgain
  have stored : memory.final.x 0 (.z 0) = (if enabled && hardPrep then 3 / 5 else 0) := by
    simpa only [Fin.cases_zero, Bool.not_not] using gain
  have writeCount : lessonReceipts memory.execution.deliveries 0 = (if enabled && hardPrep then 5 else 2) := by
    simpa only [Fin.cases_zero, Bool.not_not] using memoryCount
  have bit : roundBits (memoryBits hardPrep enabled) 0 hardPrep 3 = (enabled && hardPrep) := by
    change (enabled && !(!hardPrep)) = (enabled && hardPrep)
    rw [Bool.not_not]
  have policyGain : last.final.x 6 = memory.final.x 0 :=
    (secondValues 3).trans (firstValues 0)
  have policyCount : lessonReceipts last.execution.deliveries 6 = lessonReceipts memory.execution.deliveries 0 :=
    (secondCounts 3).trans (firstCounts 0)
  refine ⟨last, ?_, ?_, (congrFun policyGain (.z 0)).trans stored, policyCount.trans writeCount,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun dates : List ℝ =>
      (dates.filter (counterWindow (policyRead (calibrationFeedback time hardPrep).last false)).accepts).length)
      memoryDates).trans firstReport
  · exact (congrArg (fun dates : List ℝ =>
      (dates.filter (counterWindow (secondRead time hardPrep)).accepts).length)
      memoryDates).trans secondReport
  · have count : lessonReceipts first.execution.deliveries 0 = (if enabled && hardPrep then 0 else 4) := by
      simpa only [Fin.cases_zero, Bool.not_not] using firstPrep
    exact (secondCounts 0).trans count
  · have count : lessonReceipts first.execution.deliveries 1 = (if enabled && hardPrep then 4 else 0) := by
      simpa only [Fin.cases_zero, Bool.not_not] using firstPractice
    exact (secondCounts 1).trans count
  · exact secondPrep.trans (congrArg (fun value : Bool => if value then 0 else 4) bit)
  · exact secondPractice.trans (congrArg (fun value : Bool => if value then 4 else 0) bit)
  · have prep := last.reports (3 : Fin 9)
    have practice := last.reports (4 : Fin 9)
    have numeric :
        (if experimentBits hardPrep enabled 3 then 1 else 0) +
          (if experimentBits hardPrep enabled 4 then 1 else 0) =
            (if enabled || !hardPrep then 1 else 0) := by
      cases enabled <;> cases hardPrep <;> decide
    exact (congrArg₂ Nat.add prep practice).trans numeric
  · have prep := last.reports (0 : Fin 9)
    have practice := last.reports (1 : Fin 9)
    have numeric :
        (if experimentBits hardPrep enabled 0 then 1 else 0) +
          (if experimentBits hardPrep enabled 1 then 1 else 0) =
            (if enabled || !hardPrep then 1 else 0) := by
      cases enabled <;> cases hardPrep <;> decide
    exact (congrArg₂ Nat.add prep practice).trans numeric

/-- A report from the calibration failure writes the selector, which is
read again after the first evaluation round. For the hard-preparation
profile the enabled circuit succeeds twice, and cutting only the
feedback wire leaves both first choices rejected. -/
theorem native_policy_reuse_two_rounds {θA θB θC θD θE θF θG θH θI ε}
    (a : @PhysicalBox 1 θA ε) (b : @PhysicalBox 1 θB ε) (c : @PhysicalBox 1 θC ε)
    (d : @PhysicalBox 1 θD ε) (e : @PhysicalBox 1 θE ε) (f : @PhysicalBox 1 θF ε)
    (g : @PhysicalBox 1 θG ε) (h : @PhysicalBox 1 θH ε) (i : @PhysicalBox 1 θI ε)
    (time : ℝ) (hardPrep enabled : Bool) :
    let θ := policyExperimentParameters θA θB θC θD θE θF θG θH θI
    let layout := policyExperimentLayout time hardPrep enabled
    let T := time + 600
    ∃ (final : Snapshot 9) (native : Execution θ layout.route layout.start final)
      (crossing : CrossingExecution θ layout.route layout.start final),
      crossing.execution = native.toWeak ∧ CrossingCompleteThrough crossing T ∧
      PolicyExperimentEffect native time hardPrep enabled ∧
      ∀ otherFinal (other : CrossingExecution θ layout.route layout.start otherFinal),
        CrossingCompleteThrough other T →
        ∃ execution : Execution θ layout.route layout.start otherFinal,
          execution.toWeak = other.execution ∧ otherFinal.ObservationalEq final ∧
          execution.deliveries.Perm native.deliveries ∧
          PolicyExperimentEffect execution time hardPrep enabled ∧
          ∀ j, other.execution.emissionTimes j = native.emissionTimes j := by
  obtain ⟨run, effect⟩ := policy_experiment_run a b c d e f g h i time hardPrep enabled
  have box := prepend_box (prepend_box (prepend_box (prepend_box
    (prepend_box (prepend_box (prepend_box (prepend_box a b) c) d) e) f) g) h) i
  obtain ⟨crossing, same, complete, every⟩ :=
    complete_crossing_accounting run.execution run.complete run.positive box run.physical run.initial run.causal
  refine ⟨run.final, run.execution, crossing, same, complete, effect, ?_⟩
  intro final other done
  obtain ⟨native, same, physical, deliveries, fires⟩ := every final other done
  have dates (j : Fin 9) : native.emissionTimes j = run.execution.emissionTimes j := by
    calc
      native.emissionTimes j = native.toWeak.emissionTimes j := by rw [Execution.toWeak_emissionTimes]
      _ = other.execution.emissionTimes j := congrArg (fun execution => execution.emissionTimes j) same
      _ = run.execution.emissionTimes j := fires j
  exact ⟨native, same, physical, deliveries, effect.transfer physical deliveries dates, fires⟩

end RecursiveLearning.Native
