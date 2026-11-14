import NativeReciprocal
import PortMemory

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid
open NetworkStability.AutonomousFeedback NetworkStability.AutonomousFeedback.Schedule
open NetworkStability.AutonomousFeedback.Schedule.PortMemory

abbrev NominalEpoch :=
  ConstructedReverseTeaching KernelR.FutureControls.parameters nominalStart
    (KernelR.FutureControls.parameters 0) Newborn.nominal nominalDelay nominalDelay

/-- Port 0 on A and port 1 on B are the first active ports. Both cells use
native port 2 for the other gain. The recovery coordinate has its own unit. -/
def nativeCoordinate (i : Fin 2) : Coordinate → Coord
  | .port0 => .z (if i = 0 then 0 else 1)
  | .port1 => .z 2
  | .recovery => .b

def doseCount (i : Fin 2) : Coordinate → Nat
  | .port0 => if i = 0 then 3 else 1
  | .port1 => 3
  | .recovery => 1

noncomputable def unitDose : Coordinate → ℝ
  | .port0 | .port1 => 3 / 5
  | .recovery => 1 / 10

noncomputable def birthMemory (i : Fin 2) (c : Coordinate) : ℝ :=
  Newborn.nominal.x (nativeCoordinate i c)

theorem reciprocal_counts (epoch : NominalEpoch) (i : Fin 2) (c : Coordinate) :
    epoch.final.x i (nativeCoordinate i c) =
      birthMemory i c + unitDose c * doseCount i c := by
  have triple : (3 / 5 : ℝ) * 3 = 9 / 5 := by norm_num
  fin_cases i <;> cases c
  · simpa [nativeCoordinate, birthMemory, nominalStart, Newborn.snapshot, unitDose, doseCount, triple]
      using epoch.a_gain_first
  · simpa [nativeCoordinate, birthMemory, nominalStart, Newborn.snapshot, unitDose, doseCount, triple]
      using epoch.a_gain_target
  · simpa [nativeCoordinate, birthMemory, nominalStart, Newborn.snapshot, unitDose, doseCount]
      using epoch.a_recovery
  · simpa [nativeCoordinate, birthMemory, unitDose, doseCount] using epoch.b_gain_first
  · simpa [nativeCoordinate, birthMemory, unitDose, doseCount, triple] using epoch.b_gain_target
  · simpa [nativeCoordinate, birthMemory, unitDose, doseCount] using epoch.b_recovery

private def gain0A : Address 2 := ⟨0, .port0⟩
private def gain1A : Address 2 := ⟨0, .port1⟩
private def recoveryA : Address 2 := ⟨0, .recovery⟩
private def gain0B : Address 2 := ⟨1, .port0⟩
private def gain1B : Address 2 := ⟨1, .port1⟩
private def recoveryB : Address 2 := ⟨1, .recovery⟩

/-- A discrete endpoint ledger. It is intentionally not a segmentation of
the native event trace: it records the certified full-dose equivalents. -/
def endpointLedger : List (Address 2) :=
  [gain0A, gain0A, gain0A, gain1A, gain1A, gain1A, recoveryA,
    gain0B, gain1B, gain1B, gain1B, recoveryB]

def endpointModel : PortModel 2 (Address 2) where
  target := id
  bias := fun _ => -10
  drive := fun _ => 0
  route := fun _ => []

def endpointState : State 6 (Address 2) :=
  run endpointModel.guarded 1 (fun _ => 0) endpointLedger.length (start 6 endpointLedger)

theorem endpoint_ledger_counts (i : Fin 2) (c : Coordinate) :
    endpointState.writes (Address.encode ⟨i, c⟩) = doseCount i c := by
  fin_cases i <;> cases c <;> decide

/-- Checked endpoint projection of the actual reciprocal execution. It
identifies units and final coordinates without asserting event refinement. -/
theorem reciprocal_endpoint_projection (epoch : NominalEpoch) :
    endpointState.pending = [] ∧
    (∀ i c, epoch.final.x i (nativeCoordinate i c) =
      birthMemory i c + unitDose c * endpointState.writes (Address.encode ⟨i, c⟩)) ∧
    epoch.final.x 0 (.z 1) = Newborn.nominal.x (.z 1) ∧
    epoch.final.x 1 (.z 0) = Newborn.nominal.x (.z 0) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro i c
    rw [endpoint_ledger_counts]
    exact reciprocal_counts epoch i c
  · exact epoch.a_gain_other 1 (by decide) (by decide)
  · exact epoch.b_gain_other 0 (by decide) (by decide)

theorem nominal_endpoint_exists :
    ∃ epoch : NominalEpoch, CompleteThrough epoch.staged.after (4599 / 10) ∧
      ∀ i c, epoch.final.x i (nativeCoordinate i c) =
        birthMemory i c + unitDose c * endpointState.writes (Address.encode ⟨i, c⟩) := by
  obtain ⟨epoch, complete, _⟩ := nominal_reciprocal_epoch
  exact ⟨epoch, complete, (reciprocal_endpoint_projection epoch).2.1⟩

/-- A direct native-FIRE projection must emit the recorded FIREs. The
memory-only endpoint ledger cannot be used as that refinement. -/
theorem endpoint_ledger_does_not_replay_fire (epoch : NominalEpoch) :
    (endpointState.log.filter (fun p => p.2)).length ≠
      (epoch.staged.before.emissionTimes 0 ++ epoch.staged.after.emissionTimes 0).length := by
  rw [epoch.a_emission_count]
  decide

/-- An exact single physical unit per guarded write is incompatible with
the two native full doses. The endpoint projection uses coordinate units. -/
theorem no_common_native_dose :
    ¬ ∃ d : ℝ, d = unitDose .port0 ∧ d = unitDose .recovery := by
  rintro ⟨d, gain, recovery⟩
  norm_num [unitDose] at gain recovery
  linarith

/-- The frozen witness keeps later deliveries. An empty discrete ledger
cannot represent this native queue if all delivered occurrences are kept. -/
theorem reciprocal_has_future_deliveries (epoch : NominalEpoch) :
    epoch.final.pending.length = 16 ∧
      ∀ delivery ∈ epoch.final.pending, epoch.final.time < delivery.due := by
  rw [epoch.pending, epoch.date]
  constructor
  · simp [sourceTrain]
  · intro delivery mem
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp mem
    dsimp [sourceTrain]
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

/-- Check that the actual router cannot produce a contact before its source
FIRE on the nominal witness. -/
theorem reciprocal_route_causal :
    CausalRouter (reciprocalEntryRouter nominalDelay nominalDelay) :=
  reciprocalEntryRouter.causal _ _ (fun _ => by norm_num [nominalDelay])
    (fun _ => by norm_num [nominalDelay])

/-- A lowered cap at an actually reached endpoint invalidates the strict
rail claim. The witness gains three full-dose equivalents on A's port 2. -/
theorem rail_contact_control (epoch : NominalEpoch) :
    ¬ epoch.final.x 0 (.z 2) < birthMemory 0 .port1 + 9 / 5 := by
  have final := reciprocal_counts epoch 0 .port1
  norm_num [nativeCoordinate, unitDose, doseCount] at final
  linarith

/-- For all settled states, each physical learning coordinate is between
its earlier and later values, independently of the discrete ledger. -/
theorem settled_between {n θ route s u ε}
    (exec : @KernelR.Hybrid.Execution n θ route s u) (box : PhysicalBox θ ε) :
    exec.AllStates (fun t =>
      (∀ i p, s.x i (.z p) ≤ t.x i (.z p) ∧ t.x i (.z p) ≤ u.x i (.z p)) ∧
      (∀ i, s.x i .b ≤ t.x i .b ∧ t.x i .b ≤ u.x i .b)) := by
  induction exec with
  | nil s =>
    exact ⟨fun _ _ => ⟨le_rfl, le_rfl⟩, fun _ => ⟨le_rfl, le_rfl⟩⟩
  | @cons s v u move rest ih =>
    have firstMove : KernelR.Hybrid.Execution θ route s v := .cons move (.nil _)
    constructor
    · exact ⟨fun i p => ⟨le_rfl, (firstMove.gain_nondecreasing box i p).trans
          (rest.gain_nondecreasing box i p)⟩,
        fun i => ⟨le_rfl, (firstMove.recovery_nondecreasing box i).trans
          (rest.recovery_nondecreasing box i)⟩⟩
    · refine rest.allStates_mono (fun t h => ?_) ih
      exact ⟨fun i p => ⟨(firstMove.gain_nondecreasing box i p).trans (h.1 i p).1, (h.1 i p).2⟩,
        fun i => ⟨(firstMove.recovery_nondecreasing box i).trans (h.2 i).1, (h.2 i).2⟩⟩

theorem nominal_box :
    PhysicalBox
      (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
      (1 / 10) := by
  refine ⟨KernelR.FutureControls.parameters_box.1, ?_⟩
  intro i p
  fin_cases i <;> exact KernelR.FutureControls.parameters_box.2 0 p

/-- The nominal final values are strictly inside both native memory rails.
Thus all earlier settled points in the post-birth execution have headroom. -/
theorem reciprocal_final_headroom (epoch : NominalEpoch) :
    (∀ i p, epoch.final.x i (.z p) < Real.log 4) ∧
      ∀ i, epoch.final.x i .b < 11 / 10 := by
  have low : Real.log (3 / 10 : ℝ) < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have high : Real.log (6 / 5 : ℝ) < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have trained : Real.log (3 / 10 : ℝ) + 9 / 5 < Real.log 4 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    have h := learned_gain_bounds (z := Real.log (3 / 10) + 9 / 5)
      (by linarith) (by linarith)
    linarith [h.2]
  have bFirst : Real.log (6 / 5 : ℝ) + 3 / 5 < Real.log 4 := by
    have logTwo : (3 / 5 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have gap := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 4 / (6 / 5))
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (6 / 5 : ℝ) ≠ 0)] at gap
    linarith
  constructor
  · intro i p
    fin_cases i <;> fin_cases p <;> dsimp only
    · change epoch.final.x 0 (.z 0) < Real.log 4
      rw [epoch.a_gain_first]
      simpa [nominalStart, Newborn.snapshot, Newborn.nominal, nominalGain] using trained
    · change epoch.final.x 0 (.z 1) < Real.log 4
      rw [epoch.a_gain_other 1 (by decide) (by decide)]
      simpa [nominalStart, Newborn.snapshot, Newborn.nominal, nominalGain] using high
    · change epoch.final.x 0 (.z 2) < Real.log 4
      rw [epoch.a_gain_target]
      simpa [nominalStart, Newborn.snapshot, Newborn.nominal, nominalGain] using trained
    · change epoch.final.x 1 (.z 0) < Real.log 4
      rw [epoch.b_gain_other 0 (by decide) (by decide)]
      simpa [Newborn.nominal, nominalGain] using low
    · change epoch.final.x 1 (.z 1) < Real.log 4
      rw [epoch.b_gain_first]
      simpa [Newborn.nominal, nominalGain] using bFirst
    · change epoch.final.x 1 (.z 2) < Real.log 4
      rw [epoch.b_gain_target]
      simpa [Newborn.nominal, nominalGain] using trained
  · intro i
    fin_cases i <;> dsimp only
    · change epoch.final.x 0 .b < 11 / 10
      rw [epoch.a_recovery]
      norm_num [nominalStart, Newborn.snapshot, Newborn.nominal]
    · change epoch.final.x 1 .b < 11 / 10
      rw [epoch.b_recovery]
      norm_num [Newborn.nominal]

theorem reciprocal_settled_headroom (epoch : NominalEpoch) :
    epoch.staged.after.AllStates (fun s =>
      (∀ i p, s.x i (.z p) < Real.log 4) ∧ ∀ i, s.x i .b < 11 / 10) := by
  refine epoch.staged.after.allStates_mono (fun s h => ?_)
    (settled_between epoch.staged.after nominal_box)
  exact ⟨fun i p => (h.1 i p).2.trans_lt ((reciprocal_final_headroom epoch).1 i p),
    fun i => (h.2 i).2.trans_lt ((reciprocal_final_headroom epoch).2 i)⟩

/-- Strict headroom also holds inside continuous flows, including partial
writes. A suffix of the actual flow bounds its interior values by the end. -/
theorem reciprocal_flow_headroom (epoch : NominalEpoch) :
    epoch.staged.after.AllFlows (fun {s u} flow =>
      ∀ time ∈ Set.Icc s.time u.time,
        (∀ i p, flow.path time i (.z p) < Real.log 4) ∧
        ∀ i, flow.path time i .b < 11 / 10) := by
  have fromEnd {n θ route s u} (exec : @KernelR.Hybrid.Execution n θ route s u)
      {ε} (box : PhysicalBox θ ε)
      (points : exec.AllStates (fun t =>
        (∀ i p, t.x i (.z p) < Real.log 4) ∧ ∀ i, t.x i .b < 11 / 10)) :
      exec.AllFlows (fun {a b} f => ∀ time ∈ Set.Icc a.time b.time,
        (∀ i p, f.path time i (.z p) < Real.log 4) ∧
        ∀ i, f.path time i .b < 11 / 10) := by
    induction exec with
    | nil => trivial
    | @cons a b c move rest ih =>
      cases move with
      | jump => exact ih points.2
      | flow flow =>
        refine ⟨fun time ht => ?_, ih points.2⟩
        have bound := rest.allStates_initial points.2
        rcases eq_or_lt_of_le ht.2 with eq | lt
        · subst time
          simpa only [flow.final] using bound
        · let suffix := flow.suffix ht.1 lt
          have gain (i : Fin n) (p : Port) :=
            suffix.gain_nondecreasing box i p b.time ⟨lt.le, le_rfl⟩
          have recovery (i : Fin n) :=
            suffix.recovery_nondecreasing box i b.time ⟨lt.le, le_rfl⟩
          exact ⟨fun i p => (show flow.path time i (.z p) ≤ b.x i (.z p) by
              simpa only [suffix, Flow.suffix, Flow.at, flow.final] using gain i p).trans_lt (bound.1 i p),
            fun i => (show flow.path time i .b ≤ b.x i .b by
              simpa only [suffix, Flow.suffix, Flow.at, flow.final] using recovery i).trans_lt (bound.2 i)⟩
  exact fromEnd epoch.staged.after nominal_box (reciprocal_settled_headroom epoch)

/-- The delivered and retained native occurrences account for the complete
post-birth FIRE routing ledger, with multiplicity. -/
theorem reciprocal_tokens (epoch : NominalEpoch) :
    (epoch.final.pending : Multiset (Delivery 2)) +
      (epoch.staged.after.deliveries : Multiset (Delivery 2)) =
      (epoch.staged.afterBirth.pending : Multiset (Delivery 2)) +
        (epoch.staged.after.ledger.emissions.flatMap
          (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2) :
            Multiset (Delivery 2)) :=
  epoch.staged.after.token_balance

/-- A literal FIRE-only replay cannot account for the witness's positive
recovery increment. This is an obstruction to a direct encoding, and
allows a future refinement with explicit recovery transactions. -/
theorem fire_only_replay_preserves_writes (M : NetworkStability.AutonomousFeedback.Model N P)
    (d : Nat) (s : State N P) (p : P) (tail : List P)
    (queue : s.pending = p :: tail) (fire : fires M d s p 0 = true) :
    (step M d 0 s).writes = s.writes := by
  simp [step, queue, fire]

theorem recovery_requires_non_fire_update (epoch : NominalEpoch) :
    epoch.final.x 0 .b ≠ birthMemory 0 .recovery := by
  have h := reciprocal_counts epoch 0 .recovery
  norm_num [nativeCoordinate, doseCount, unitDose] at h
  linarith

/-- A native read known only to touch threshold has no positive two-sided
guard certificate. Lowering its score by a positive error flips the decision. -/
theorem uncertified_threshold_control (error : ℝ) (positive : 0 < error) :
    (0 : ℝ) ≤ 0 ∧ ¬ (0 : ℝ) ≤ 0 - error := by
  constructor <;> linarith

end NetworkStability.NativeReciprocal
