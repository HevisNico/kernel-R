import PhysicalEvaluator.RecordedBridge

/-! Executable replay of the public t6004 observations. This uses recorded
data, not a newly simulated physical feedback loop. The equality to the
certified environment is conditional on the physical premises in
RecordedBridge, which are not constructed merely by decoding the CSV.
The concrete replay conclusions themselves do not depend on those premises:
`replay_sound` and the discrete controller already prove them. The certificate
variants only connect this fixed computation to a conditional physical
interpretation; they do not establish that the physical premises hold. -/
namespace ReusableController.PhysicalEvaluator.Replay
open RecursiveLearning ReusableController.Adaptive RecordedData

def oracle : LessonOracle := marginOracle (decodedCount t6004p1Readings) (decodedCount t6004p2Readings)
def policies (longerSearch : Bool) : Policy :=
  if longerSearch then ⟨true, 1, 12, false⟩ else ⟨false, 1, 6, false⟩
def start : Lesson := ⟨10, 9⟩
def menu : PolicyMenu Bool := ⟨false, [true], by decide⟩
def cost (p : Bool) : Nat := policyCost oracle 0 (initial start) 1 20 (policies p)
def environment : Evaluation Bool where
  need := ⟨6, 4⟩
  initialLesson := start
  oracle := oracle
  lessonTolerance := 0
  policies := policies
  report := fun p => (cost p : Int)
  costTolerance := 0
  overhead := 1
  deployments := 20
  validationOverhead := 1
def completed : Session environment := adaptAndSearch environment menu

/-- The archived train has 21 pulses, including pulses outside the two
certified prefixes. Earlier shared calibration is a prepared input here;
any charge for obtaining it must be added to the generic acquisition ledger. -/
def recordedTrainPulses : Nat := 21

theorem recorded_readout : readoutCounts t6004p1Readings t6004p2Readings = some (6, 4) := by decide

/-- Definitional equality for any supplied certificates: the environment's
computational fields do not depend on their proof or physical-state fields.
This does not construct the premises or validate them against a circuit. -/
theorem replay_matches_certificates (p : PreparationPremises) (q : PracticePremises) :
    certifiedEnvironment (preparationCertificate p) (practiceCertificate q)
      start policies 1 20 1 = environment := by rfl

/-- Conditional physical interpretation of a fixed decoded replay. The
conclusion is independent of `p` and `q` and is also proved without them by
`replay_sound`; the premises do not add a physical validation result. -/
theorem replay_sound_from_certificates (p : PreparationPremises) (q : PracticePremises) :
    environment.Sound := by
  rw [← replay_matches_certificates p q]
  exact certified_environment_sound (preparationCertificate p) (practiceCertificate q)
    start policies 1 20 1 (by decide)

/-- As with `replay_matches_certificates`, the computation is independent of
the supplied envelope witnesses. Their physical validity remains external. -/
theorem replay_matches_envelopes (p : PreparationEnvelopePremises) (q : PracticeEnvelopePremises) :
    certifiedEnvironment (preparationEnvelopeCertificate p).toProbeCertificate
      (practiceEnvelopeCertificate q).toProbeCertificate start policies 1 20 1 = environment := by rfl

/-- This standalone replay lemma concerns the decoded discrete model. The
preceding theorem is the conditional physical interpretation of that model. -/
theorem replay_sound : environment.Sound := by
  refine ⟨by decide, ?_, ?_⟩
  · intro index lesson
    simp [environment, oracle, t6004p1Count, t6004p2Count, lessonMargin, marginOracle]
  · intro p
    simp [environment, Evaluation.trueCost, cost]

theorem cost_values : cost false = 380 ∧ cost true = 359 := by decide

theorem actual_selection_and_search :
    completed.memory.incumbent = true ∧ completed.memory.trials = 2 ∧
    completed.memory.adoptions = 1 ∧ completed.memory.spent = 741 ∧
    completed.memory.live.lesson = ⟨6, 4⟩ ∧
    completed.memory.live.trialPulses = 148 ∧ completed.memory.live.attempts = 11 ∧
    recordedTrainPulses + completed.memory.spent + completed.memory.live.work 1 = 921 := by decide

/-- The conclusion concerns a fixed, already decoded discrete replay and
does not depend on `p` or `q`. It follows independently from `replay_sound`
and the discrete adoption contract. This version supplies the conditional
certificate interpretation, not evidence that its physical premises hold. -/
theorem certified_replay_nondegradation (p : PreparationPremises) (q : PracticePremises) :
    Ready ⟨6, 4⟩ completed.memory.live ∧
      referenceCost 6 4 start policies 1 20 completed.memory.incumbent ≤
        referenceCost 6 4 start policies 1 20 menu.seed := by
  have h := recorded_controller_contract p q start policies 1 20 1 menu (by decide)
  dsimp only at h
  rw [replay_matches_certificates p q] at h
  exact h

/-- The recorded replay also accepts the lower/upper observation-envelope
premises directly; no constant physical read threshold is introduced.
The conclusion is independent of these witnesses and already follows for the
decoded model from `replay_sound`; only its physical interpretation uses them. -/
theorem envelope_replay_nondegradation
    (p : PreparationEnvelopePremises) (q : PracticeEnvelopePremises) :
    Ready ⟨6, 4⟩ completed.memory.live ∧
      referenceCost 6 4 start policies 1 20 completed.memory.incumbent ≤
        referenceCost 6 4 start policies 1 20 menu.seed := by
  have h := recorded_envelope_controller_contract p q start policies 1 20 1 menu (by decide)
  dsimp only at h
  rw [replay_matches_envelopes p q] at h
  exact h

theorem replay_budget :
    completed.memory.spent ≤ 1242 ∧ completed.memory.live.attempts ≤ 12 ∧
    completed.memory.live.trialPulses ≤ 228 ∧
    completed.memory.spent + completed.memory.live.work 1 ≤ 1482 :=
  two_level_budget environment menu replay_sound (F := 12) (by intro p; cases p <;> decide)

theorem amortization_with_recorded_train (episodes : Nat) :
    (recordedTrainPulses + completed.memory.spent + episodes * cost completed.memory.incumbent ≤
      episodes * cost menu.seed) ↔ 37 ≤ episodes := by
  change (21 + 741 + episodes * 359 ≤ episodes * 380) ↔ 37 ≤ episodes
  omega

theorem live_first_then_thirty_six :
    recordedTrainPulses + completed.memory.spent + completed.memory.live.work 1 +
      20 * completed.memory.live.lesson.cost + 36 * cost completed.memory.incumbent = 14045 ∧
    37 * cost menu.seed = 14060 := by decide

end ReusableController.PhysicalEvaluator.Replay
