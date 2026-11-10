import CoincidenceProtectedTail
import CoincidenceLocalExecution

/-! Native two-cell executions and the registered constant-current comparison. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The realized thresholds and initial gains of one benchmark channel.
The unused port can have a smaller gain than the two selectable ports. -/
structure CoincidenceCellSpec (θ : Fin 1 → Parameters) (gains : Port → ℝ)
    (trained : Port) (e f : ℝ) : Prop where
  config : (θ 0).thresholds = trainingThresholds trained ((θ 0).thresholds.error trained)
    ((θ 0).thresholds.auxReady trained) (θ 0).thresholds.fire
  entry : |(θ 0).thresholds.error trained - 1 / 10| ≤ e / 10
  exit : |(θ 0).thresholds.auxReady trained - 1 / 100| ≤ e / 40
  fire : |(θ 0).thresholds.fire - 1| ≤ f
  trainGain : Real.exp (gains trained) = 6 / 5
  allGains : ∀ q, Real.exp (gains q) ≤ 6 / 5
  caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)

private theorem CoincidenceCellSpec.bands {θ gains trained e f}
    (spec : CoincidenceCellSpec θ gains trained e f) (errors : Exit001TimingBox e f) :
    (θ 0).thresholds.fire ∈ Icc (19 / 20 : ℝ) (21 / 20) ∧
    |(θ 0).thresholds.error trained - 1 / 10| ≤ 1 / 200 ∧
    (θ 0).thresholds.auxReady trained ∈ Icc (7 / 800 : ℝ) (9 / 800) := by
  have eMax : e ≤ 3 / 100 := by rcases errors with h | h | h <;> linarith [h.1]
  have fMax : f ≤ 3 / 100 := by rcases errors with h | h | h <;> linarith [h.2]
  obtain ⟨fireLo, fireHi⟩ := abs_le.mp spec.fire
  obtain ⟨exitLo, exitHi⟩ := abs_le.mp spec.exit
  exact ⟨⟨by linarith, by linarith⟩, by linarith [spec.entry], ⟨by linarith, by linarith⟩⟩

private theorem CoincidenceCellSpec.bounds {θ gains trained e f}
    (spec : CoincidenceCellSpec θ gains trained e f) (errors : Exit001TimingBox e f) :
    ParameterThresholdBounds θ := by
  obtain ⟨fire, entry, exit⟩ := spec.bands errors
  exact training_threshold_bounds spec.config fire entry (by linarith [exit.1])

theorem coincidence_local_complete {θ ε gains trained tested readTime e f}
    (box : @PhysicalBox 1 θ ε) (spec : CoincidenceCellSpec θ gains trained e f)
    (errors : Exit001TimingBox e f) (read : readTime ∈ Icc (333 / 20 : ℝ) (347 / 20)) :
    ∃ u, ∃ run : ParameterExecution θ (fun _ _ => [])
      (coincidenceTrialStart gains trained tested readTime) u,
      ParameterCompleteThrough run 20 ∧
      CoincidenceLocalReports trained tested readTime (run.emissionTimes 0) := by
  by_cases hmatch : tested = trained
  · subst tested
    obtain ⟨run, latency⟩ := training_read_exit_001_certificate (time := 0)
      box errors spec.entry spec.exit spec.fire read.1 spec.trainGain spec.caps
    obtain ⟨fire, entry, exit⟩ := spec.bands errors
    obtain ⟨u, tail, done⟩ := run.protected_complete_at_twenty box spec.config fire entry exit read
    have report := run.complete_extension_reports spec.config fire.1 tail done
    rw [coincidenceTrialStart_same]
    refine ⟨u, (run.parameterExecution spec.config).append tail, report.1, ?_⟩
    simp only [CoincidenceLocalReports]
    exact ⟨run.handoff.decision.stop, report.2, by simpa only [zero_add] using latency⟩
  · obtain ⟨u, run, done, silent⟩ := wrong_port_exit_001_benchmark
      box spec.config errors spec.entry spec.exit spec.fire read spec.trainGain
      (spec.allGains tested) spec.caps hmatch
    exact ⟨u, run, done, by simpa only [CoincidenceLocalReports, ite_eq_right hmatch] using silent⟩

/-- Existence and the observed decision in every complete two-cell
execution for a registered pair of test ports, offset and read jitters. -/
def CoincidenceFullContract (θL θR : Fin 1 → Parameters) (gainsL gainsR : Port → ℝ)
    (trainedL testedL trainedR testedR : Port) (offset jitterL jitterR : ℝ) : Prop :=
  let θ := extendParameters θL (θR 0)
  let readL := 17 + jitterL
  let readR := 17 + offset + jitterR
  let s := (coincidenceTrialStart gainsL trainedL testedL readL).independentPair
    (coincidenceTrialStart gainsR trainedR testedR readR)
  (∃ v, ∃ ref : ParameterExecution θ (fun _ _ => []) s v, ParameterCompleteThrough ref 20) ∧
  ∀ {u} (run : ParameterExecution θ (fun _ _ => []) s u), ParameterCompleteThrough run 20 →
    CoincidenceLocalReports trainedL testedL readL (run.emissionTimes 0) ∧
    CoincidenceLocalReports trainedR testedR readR (run.emissionTimes 1) ∧
    (coincidenceAccepts (run.emissionTimes 0) (run.emissionTimes 1) ↔
      testedL = trainedL ∧ testedR = trainedR ∧ offset = 0)

theorem coincidence_exit_001_full_contract {θL θR : Fin 1 → Parameters} {ε e f : ℝ}
    {gainsL gainsR : Port → ℝ} {trainedL testedL trainedR testedR : Port}
    {offset jitterL jitterR : ℝ}
    (boxL : PhysicalBox θL ε) (boxR : PhysicalBox θR ε)
    (leftSpec : CoincidenceCellSpec θL gainsL trainedL e f)
    (rightSpec : CoincidenceCellSpec θR gainsR trainedR e f)
    (errors : Exit001TimingBox e f)
    (jitterLeft : |jitterL| ≤ 1 / 20) (jitterRight : |jitterR| ≤ 1 / 20)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10) :
    CoincidenceFullContract θL θR gainsL gainsR trainedL testedL trainedR testedR
      offset jitterL jitterR := by
  have offsetBand : |offset| ≤ 3 / 10 := by
    rcases offsets with h | h | h <;> rw [h] <;> norm_num
  obtain ⟨leftLo, leftHi⟩ := abs_le.mp jitterLeft
  obtain ⟨rightLo, rightHi⟩ := abs_le.mp jitterRight
  obtain ⟨offLo, offHi⟩ := abs_le.mp offsetBand
  let readL := 17 + jitterL
  let readR := 17 + offset + jitterR
  have readLeft : readL ∈ Icc (333 / 20 : ℝ) (347 / 20) := by
    constructor <;> dsimp [readL] <;> linarith
  have readRight : readR ∈ Icc (333 / 20 : ℝ) (347 / 20) := by
    constructor <;> dsimp [readR] <;> linarith
  obtain ⟨uL, l, lc, lr⟩ := coincidence_local_complete (tested := testedL)
    boxL leftSpec errors readLeft
  obtain ⟨uR, r, rc, rr⟩ := coincidence_local_complete (tested := testedR)
    boxR rightSpec errors readRight
  have box : PhysicalBox (extendParameters θL (θR 0)) ε := by
    refine ⟨boxL.1, ?_⟩
    intro i p
    fin_cases i
    · exact boxL.2 0 p
    · exact boxR.2 0 p
  have bL := leftSpec.bounds errors
  have bR := rightSpec.bounds errors
  have bounds : ParameterThresholdBounds (extendParameters θL (θR 0)) := by
    constructor
    · intro i; fin_cases i; exact bL.fire 0; exact bR.fire 0
    · intro i; fin_cases i; exact bL.fastEnd 0; exact bR.fastEnd 0
    · intro i; fin_cases i; exact bL.fastBelowFire 0; exact bR.fastBelowFire 0
    · intro i; fin_cases i; exact bL.reopen 0; exact bR.reopen 0
    · intro i p; fin_cases i; exact bL.mark 0 p; exact bR.mark 0 p
    · intro i p; fin_cases i; exact bL.silent 0 p; exact bR.silent 0 p
    · intro i p; fin_cases i; exact bL.error 0 p; exact bR.error 0 p
    · intro i p; fin_cases i; exact bL.auxReady 0 p; exact bR.auxReady 0 p
  have sL := training_initial_invariant (time := 0) (p := trainedL) (delay := readL) leftSpec.caps
  have sR := training_initial_invariant (time := 0) (p := trainedR) (delay := readR) rightSpec.caps
  have birth : ParameterPhysicalInvariant (extendParameters θL (θR 0))
      ((coincidenceTrialStart gainsL trainedL testedL readL).independentPair
        (coincidenceTrialStart gainsR trainedR testedR readR)) := by
    constructor
    · intro i; fin_cases i; exact sL.charge 0; exact sR.charge 0
    · intro i p; fin_cases i; exact sL.sensor 0 p; exact sR.sensor 0 p
    · intro i p; fin_cases i; exact sL.gain 0 p; exact sR.gain 0 p
    · intro i; fin_cases i; exact sL.recovery 0; exact sR.recovery 0
    · intro i; fin_cases i; exact sL.reserve 0; exact sR.reserve 0
  obtain ⟨⟨ref, done⟩, all⟩ := coincidence_joint_complete_of_local l r lc rc lr rr
    rfl rfl jitterLeft jitterRight offsets box bounds birth
  exact ⟨⟨uL.independentPair uR, ref, done⟩, all⟩

/-- Acceptance of the registered positive corner by the reduced
constant-current readout. The training endpoint charges are explicit. -/
def TimedCurrentCornerAccepts (current duration expiryL expiryR : ℝ) : Prop :=
  let readL : ℝ := 17 - 1 / 20
  let readR : ℝ := 17 + 1 / 20
  let qL := relax (1 / 2) (1 / 10) expiryL 1 readL
  let qR := relax (1 / 2) (1 / 10) expiryR 1 readR
  ∃ fast slow : ℝ,
    FirstPulseReport qL (timedCurrentGain (current * duration) (11 / 10) (22 / 5))
      (97 / 100) fast ∧
    FirstPulseReport qR (timedCurrentGain (current * duration) (9 / 10) (18 / 5))
      (103 / 100) slow ∧
    coincidenceAccepts [readL + fast] [readR + slow]

/-- Quiet charge at training expiry suffices for the registered reduced
comparator to fail on the positive corner, for every common setting. -/
theorem constant_current_registered_corner_rejects {current duration expiryL expiryR : ℝ}
    (left : expiryL ∈ Icc (1 / 10 : ℝ) (103 / 100))
    (right : expiryR ∈ Icc (1 / 10 : ℝ) (103 / 100)) :
    ¬ TimedCurrentCornerAccepts current duration expiryL expiryR := by
  unfold TimedCurrentCornerAccepts
  dsimp only
  have l := timed_current_read_charge left.1 left.2
    (show (16 : ℝ) ≤ 17 - 1 / 20 by norm_num)
  have r := timed_current_read_charge right.1 right.2
    (show (16 : ℝ) ≤ 17 + 1 / 20 by norm_num)
  rintro ⟨fast, slow, hf, hs, lDate, rDate, lEq, rEq, _, _, skew⟩
  simp only [List.singleton_inj] at lEq rEq
  subst lDate
  subst rDate
  exact constant_current_no_common_timing (wire := 7 / 20) l.1 r.2 ⟨fast, slow, hf, hs, skew⟩

/-- At the primary time scale, native R realizes the decision contract
in the wide fabrication box, with 3% FIRE error and ERROR radius up to
1% in `CoincidenceCellSpec`. The positive corner with nominal ERROR
endpoints is included for every such radius. At that corner, no common
setting of the reduced timer with 10% current error satisfies the
receiver contract. -/
theorem coincidence_exit_001_separation {θL θR : Fin 1 → Parameters}
    {gainsL gainsR : Port → ℝ} {trainedL testedL trainedR testedR : Port}
    {offset jitterL jitterR e : ℝ}
    (boxL : PhysicalBox θL (1 / 10)) (boxR : PhysicalBox θR (1 / 10))
    (errorRadius : e ∈ Icc (0 : ℝ) (1 / 100))
    (left : CoincidenceCellSpec θL gainsL trainedL e (3 / 100))
    (right : CoincidenceCellSpec θR gainsR trainedR e (3 / 100))
    (jitterLeft : |jitterL| ≤ 1 / 20) (jitterRight : |jitterR| ≤ 1 / 20)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10) :
    CoincidenceFullContract θL θR gainsL gainsR trainedL testedL trainedR testedR
        offset jitterL jitterR ∧
      ∀ current duration expiryL expiryR : ℝ,
        expiryL ∈ Icc (1 / 10 : ℝ) (103 / 100) → expiryR ∈ Icc (1 / 10 : ℝ) (103 / 100) →
        ¬ TimedCurrentCornerAccepts current duration expiryL expiryR := by
  refine ⟨coincidence_exit_001_full_contract boxL boxR left right ?_
    jitterLeft jitterRight offsets, ?_⟩
  · exact Or.inl ⟨errorRadius.2, le_rfl⟩
  · intro current duration expiryL expiryR l r
    exact constant_current_registered_corner_rejects l r

end RecursiveLearning.Native
