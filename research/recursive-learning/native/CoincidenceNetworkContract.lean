import ParameterExecutionProduct
import CoincidenceReadTail
import TimedCurrentSeparation

/-! The registered two-channel decision from completed local trials. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The training pulse addresses the trained port. The later read may
address another port. -/
noncomputable def coincidenceTrialStart (gains : Port → ℝ)
    (trained tested : Port) (readTime : ℝ) : Snapshot 1 :=
  { trainingStart 0 gains trained readTime with
    pending := [errorReadDelivery trained 0, errorReadDelivery tested readTime] }

theorem coincidenceTrialStart_same (gains : Port → ℝ) (port : Port) (readTime : ℝ) :
    coincidenceTrialStart gains port port readTime = trainingStart 0 gains port readTime := by
  simp [coincidenceTrialStart, trainingStart]

/-- The local obligations for the registered observation at time 20. -/
def CoincidenceLocalReports (trained tested : Port) (readTime : ℝ) (reports : List ℝ) : Prop :=
  if tested = trained then
    ∃ t, reports = [t] ∧ t - readTime ∈ Icc (697 / 2000) (199 / 500)
  else reports = []

/-- Each receiver line delivers its cell's FIRE after 0.35 model units.
The external receiver requires one report on each line by 20.35. -/
def coincidenceAccepts (left right : List ℝ) : Prop :=
  ∃ l r, left = [l] ∧ right = [r] ∧
    l + 7 / 20 ≤ 407 / 20 ∧ r + 7 / 20 ≤ 407 / 20 ∧
    |(r + 7 / 20) - (l + 7 / 20)| < 3 / 20

theorem coincidence_accepts_iff_of_local_reports
    {trainedL testedL trainedR testedR : Port} {readL readR offset jitterL jitterR : ℝ}
    {left right : List ℝ}
    (hL : CoincidenceLocalReports trainedL testedL readL left)
    (hR : CoincidenceLocalReports trainedR testedR readR right)
    (scheduleL : readL = 17 + jitterL)
    (scheduleR : readR = 17 + offset + jitterR)
    (jitterLeft : |jitterL| ≤ 1 / 20) (jitterRight : |jitterR| ≤ 1 / 20)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10) :
    coincidenceAccepts left right ↔ testedL = trainedL ∧ testedR = trainedR ∧ offset = 0 := by
  by_cases l : testedL = trainedL
  · by_cases r : testedR = trainedR
    · simp only [CoincidenceLocalReports, ite_eq_left l] at hL
      simp only [CoincidenceLocalReports, ite_eq_left r] at hR
      obtain ⟨lt, rfl, latL⟩ := hL
      obtain ⟨rt, rfl, latR⟩ := hR
      have skew := coincidence_of_trained_latency (wire := 7 / 20)
        latL latR jitterLeft jitterRight (by linarith) offsets
      have limit : offset ≤ 3 / 10 := by rcases offsets with h | h | h <;> linarith
      have dueL : lt + 7 / 20 ≤ 407 / 20 := by linarith [latL.2, (abs_le.mp jitterLeft).2]
      have dueR : rt + 7 / 20 ≤ 407 / 20 := by linarith [latR.2, (abs_le.mp jitterRight).2]
      constructor
      · rintro ⟨a, b, ha, hb, _, _, aperture⟩
        simp only [List.singleton_inj] at ha hb
        subst a
        subst b
        exact ⟨l, r, skew.mp aperture⟩
      · rintro ⟨_, _, zero⟩
        exact ⟨lt, rt, rfl, rfl, dueL, dueR, skew.mpr zero⟩
    · have empty : right = [] := by simpa only [CoincidenceLocalReports, ite_eq_right r] using hR
      simp [coincidenceAccepts, empty, r]
  · have empty : left = [] := by simpa only [CoincidenceLocalReports, ite_eq_right l] using hL
    simp [coincidenceAccepts, empty, l]

/-- Two local complete witnesses determine every complete joint receiver
decision. The reports of the local witnesses are explicit hypotheses. -/
theorem coincidence_joint_complete_of_local {θL θR : Fin 1 → Parameters} {ε : ℝ}
    {gainsL gainsR : Port → ℝ} {trainedL testedL trainedR testedR : Port}
    {readL readR offset jitterL jitterR : ℝ} {uL uR : Snapshot 1}
    (left : ParameterExecution θL (fun _ _ => [])
      (coincidenceTrialStart gainsL trainedL testedL readL) uL)
    (right : ParameterExecution θR (fun _ _ => [])
      (coincidenceTrialStart gainsR trainedR testedR readR) uR)
    (leftComplete : ParameterCompleteThrough left 20)
    (rightComplete : ParameterCompleteThrough right 20)
    (leftReports : CoincidenceLocalReports trainedL testedL readL (left.emissionTimes 0))
    (rightReports : CoincidenceLocalReports trainedR testedR readR (right.emissionTimes 0))
    (scheduleL : readL = 17 + jitterL)
    (scheduleR : readR = 17 + offset + jitterR)
    (jitterLeft : |jitterL| ≤ 1 / 20) (jitterRight : |jitterR| ≤ 1 / 20)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10)
    (box : PhysicalBox (extendParameters θL (θR 0)) ε)
    (thresholds : ParameterThresholdBounds (extendParameters θL (θR 0)))
    (birth : ParameterPhysicalInvariant (extendParameters θL (θR 0))
      ((coincidenceTrialStart gainsL trainedL testedL readL).independentPair
        (coincidenceTrialStart gainsR trainedR testedR readR))) :
    let s := (coincidenceTrialStart gainsL trainedL testedL readL).independentPair
      (coincidenceTrialStart gainsR trainedR testedR readR)
    (∃ ref : ParameterExecution (extendParameters θL (θR 0)) (fun _ _ => [])
      s (uL.independentPair uR), ParameterCompleteThrough ref 20) ∧
    ∀ {u} (ex : ParameterExecution (extendParameters θL (θR 0)) (fun _ _ => []) s u),
      ParameterCompleteThrough ex 20 →
      CoincidenceLocalReports trainedL testedL readL (ex.emissionTimes 0) ∧
      CoincidenceLocalReports trainedR testedR readR (ex.emissionTimes 1) ∧
      (coincidenceAccepts (ex.emissionTimes 0) (ex.emissionTimes 1) ↔
        testedL = trainedL ∧ testedR = trainedR ∧ offset = 0) := by
  dsimp only
  obtain ⟨ref, l, r⟩ := left.independentPair right rfl (leftComplete.1.trans rightComplete.1.symm)
  have complete := leftComplete.independentPair rightComplete ref
  refine ⟨⟨ref, complete⟩, ?_⟩
  intro u ex done
  have leftEq := (ex.emissionTimes_unique ref box thresholds birth done complete 0).trans l
  have rightEq := (ex.emissionTimes_unique ref box thresholds birth done complete 1).trans r
  have hl := leftEq.symm ▸ leftReports
  have hr := rightEq.symm ▸ rightReports
  exact ⟨hl, hr, coincidence_accepts_iff_of_local_reports hl hr scheduleL scheduleR
    jitterLeft jitterRight offsets⟩

/-- The wrong port starts at gain 1.2. If its nominal ERROR phase
starts at age at least 0.99, the maximum live-pulse write is small even
at the top of the wide fabrication box. -/
theorem untrained_live_gain_le {age onset rate : ℝ}
    (live : age ≤ 1) (onsetLate : 99 / 100 ≤ onset)
    (rateBounds : 0 ≤ rate ∧ rate ≤ 11) :
    (6 / 5) * Real.exp
      (8 * (1 / 10) * (1 - Real.exp (-rate * max 0 (age - onset)))) ≤ 4 / 3 := by
  have elapsed : max 0 (age - onset) ≤ (1 / 100 : ℝ) :=
    max_le (by norm_num) (by linarith)
  have mulBound := mul_le_mul rateBounds.2 elapsed (le_max_left _ _) (by norm_num : (0 : ℝ) ≤ 11)
  have dose : 8 * (1 / 10) * (1 - Real.exp (-rate * max 0 (age - onset))) ≤ 11 / 125 := by
    linarith [Real.add_one_le_exp (-rate * max 0 (age - onset))]
  have expBound : Real.exp (11 / 125 : ℝ) ∈ Icc (0 : ℝ) (10 / 9) :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  have h := mul_le_mul_of_nonneg_left
    ((Real.exp_le_exp.mpr dose).trans expBound.2) (by norm_num : (0 : ℝ) ≤ 6 / 5)
  linarith

/-- An upper envelope for the actual live-pulse drive suffices to rule
out a wrong-port FIRE, including during a short overlap with ERROR. -/
theorem untrained_live_charge_below_fire {initial origin t threshold : ℝ}
    {forcing : ℝ → ℝ} (smooth : Continuous forcing)
    (initialBound : initial ≤ 101 / 1000) (thresholdBound : 97 / 100 ≤ threshold)
    (since : origin ≤ t)
    (driveBound : ∀ v ∈ Icc origin t,
      forcing v ≤ (4 / 3) * a * Real.exp (-a * (v - origin))) :
    relax (1 / 2) (1 / 10) initial origin t +
      linearConvolution (1 / 2) forcing origin t < threshold := by
  have convolution := linearConvolution_mono (rate := 1 / 2) smooth (by fun_prop) since driveBound
  rw [linearConvolution_canonical since] at convolution
  have carry := decay_upper (show initial - 1 / 10 ≤ (1 / 1000 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) (sub_nonneg.mpr since)
  have responseBound := response_uniform_upper (sub_nonneg.mpr since)
  unfold relax
  linarith

end RecursiveLearning.Native
