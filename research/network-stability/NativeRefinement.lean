import NativeMarkTrace

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid
open AutonomousFeedback.Schedule (Config)

/-- A model with one fixed read law per physical input cannot distinguish
two input occurrences that have the same addressed gain and recovery. -/
def SameReadLaw (M : MarkFeedback.Model N P) (p q : P) : Prop :=
  MarkFeedback.gain M p = MarkFeedback.gain M q ∧
    MarkFeedback.recovery M p = MarkFeedback.recovery M q ∧
    M.bias p = M.bias q ∧ M.recoveryWeight p = M.recoveryWeight q

theorem same_read_law_same_decision (M : MarkFeedback.Model N P) (d : Nat)
    (s u : Config (3 * N) P) (p q : P) (law : SameReadLaw M p q)
    (gain : s.writes (MarkFeedback.gain M p) = u.writes (MarkFeedback.gain M q))
    (recovery : s.writes (MarkFeedback.recovery M p) = u.writes (MarkFeedback.recovery M q)) :
    MarkFeedback.read M d s p 0 = MarkFeedback.read M d u q 0 := by
  rcases law with ⟨_, _, bias, weight⟩
  simp [MarkFeedback.read, MarkFeedback.score, gain, recovery, bias, weight]

/-- With equal addresses and no writes at those addresses between the reads,
even margins at zero error cannot certify opposite decisions. -/
theorem identical_input_cannot_replay_fire_then_mark (M : MarkFeedback.Model N P) (d : Nat)
    (s u : Config (3 * N) P) (p q : P) (law : SameReadLaw M p q)
    (gain : s.writes (MarkFeedback.gain M p) = u.writes (MarkFeedback.gain M p))
    (recovery : s.writes (MarkFeedback.recovery M p) = u.writes (MarkFeedback.recovery M p)) :
    ¬ (MarkFeedback.read M d s p 0 = true ∧ MarkFeedback.read M d u q 0 = false) := by
  have same := same_read_law_same_decision M d s u p q law
    (gain.trans (congrArg u.writes law.1))
    (recovery.trans (congrArg u.writes law.2.1))
  rintro ⟨fires, silent⟩
  rw [fires, silent] at same
  contradiction

private theorem nominal_delay_range :
    ∀ t, (3 / 10 : ℝ) ≤ nominalDelay t ∧ nominalDelay t ≤ 2 / 5 := by
  intro t
  norm_num [nominalDelay]

/-- From the departure of READY until the next return to READY there is
one main transaction. A second arrival during this interval violates
settled-transaction exclusivity on that cell. An idle cut
or a delivery on another cell has no effect on this test. -/
def AllowsSettledTransactions {n θ route s u} (run : @Execution n θ route s u) : Prop :=
  ∀ (a b c : Snapshot n) (head : Execution θ route s a) (busy : Execution θ route a b)
    (next : Jump route b c) (tail : Execution θ route c u),
    run = head.append (busy.append (.cons (.jump next) tail)) →
    ∀ i : Fin n, a.main i = .fast →
      busy.AllStates (fun v => v.main i ≠ .ready) →
      ∀ token ∈ next.deliveries, token.cell ≠ i

abbrev NominalStaged (last : Snapshot 2) :=
  StagedExecution KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0)
    (fun _ _ => []) (reciprocalEntryRouter nominalDelay nominalDelay) nominalStart last

/-- Actual cuts from the preceding B FIRE through the protected receipt. -/
structure ProtectedReceipt {last : Snapshot 2} (staged : NominalStaged last) where
  readySource : Snapshot 2
  fromFire : Snapshot 2
  receipt : Snapshot 2
  completed : Snapshot 2
  head : Execution _ _ staged.afterBirth readySource
  trigger : Execution _ _ readySource fromFire
  span : Execution _ _ fromFire receipt
  finish : Execution _ _ receipt completed
  tail : Execution _ _ completed last
  reconstruct : staged.after = head.append (trigger.append (span.append (finish.append tail)))
  source_ready : readySource.main 1 = .ready
  source_raw : readySource.raw 1 1 = some readySource.time
  fire_fast : fromFire.main 1 = .fast
  fire_word : trigger.ledger.emissions = [(1, fromFire.time)]
  triggering_isolated : trigger.deliveries = []
  third_word : span.deliveries.filter (fun token => token.cell = 1) = [⟨1, 1, receipt.time⟩]
  span_silent : span.emissionTimes 1 = []
  third_slow : receipt.main 1 = .slow
  third_raw : receipt.raw 1 1 = some receipt.time
  silence : finish.emissionTimes 1 = []
  same_gain : receipt.x 1 (.z 1) = readySource.x 1 (.z 1)
  same_recovery : receipt.x 1 .b = readySource.x 1 .b
  mark_gain : completed.x 1 .b = receipt.x 1 .b + 1 / 10
  gain_preserved : ∀ p, completed.x 1 (.z p) = receipt.x 1 (.z p)
  completed_ready : completed.main 1 = .ready
  completed_raw : ∀ p, completed.raw 1 p = none
  fires_after_arrival : readySource.time < fromFire.time
  receipt_after_fire : fromFire.time < receipt.time
  arrival_gap : readySource.time + 79 / 10 ≤ receipt.time
  completion_date : completed.time = 184

/-- If an execution begins in FAST, ends outside READY, and never fires
again at that cell, its main mode could never have reopened in between. -/
theorem stays_protected_without_fire {n θ route s u}
    (run : @Execution n θ route s u) (i : Fin n) (entry : s.main i = .fast)
    (protectedAtEnd : u.main i ≠ .ready) (fires : run.emissionTimes i = []) :
    run.AllStates (fun v => v.main i ≠ .ready) := by
  have start : (s.main i == .ready) = false := by simp [entry]
  rcases run.first_state_change (fun v => v.main i == .ready) false
      (fun f => by rw [f.main_fixed]) start with all | ⟨a, b, segment, exit, tail, split, _, _, reopened⟩
  · exact run.allStates_mono (fun v h => by simpa using h) all
  · have ready : b.main i = .ready := by simpa using reopened
    have tailQuiet : tail.emissionTimes i = [] := by
      rw [split, Execution.emissionTimes_append, Execution.emissionTimes_cons] at fires
      exact (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp fires).2).2
    have readyAtEnd := tail.allStates_final (tail.ready_states_of_no_emissions i ready tailQuiet)
    exact (protectedAtEnd readyAtEnd).elim


/-- A suffix preserves the certified cuts on the actual prefix. -/
noncomputable def ProtectedReceipt.append {last final : Snapshot 2} {staged : NominalStaged last}
    (w : ProtectedReceipt staged)
    (suffix : Execution
      (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
      (reciprocalEntryRouter nominalDelay nominalDelay) last final) :
    ProtectedReceipt ({ staged with after := staged.after.append suffix } : NominalStaged final) :=
  { w with
    tail := w.tail.append suffix
    reconstruct := by
      change staged.after.append suffix = _
      rw [w.reconstruct]
      simp only [Execution.append_assoc] }

theorem ProtectedReceipt.not_settled_exclusive {last : Snapshot 2} {staged : NominalStaged last} (w : ProtectedReceipt staged) :
    ¬ AllowsSettledTransactions staged.after := by
  intro exclusive
  let token : Delivery 2 := ⟨1, 1, w.receipt.time⟩
  have arrival : w.span.cellDeliveries 1 = token :: [] := w.third_word
  obtain ⟨cut⟩ := w.span.first_cell_delivery 1 token [] arrival
  have readyOfCut : cut.beforeArrival.main 1 ≠ .ready := by
    have stillBusy := stays_protected_without_fire w.span 1 w.fire_fast
      (by rw [w.third_slow]; decide) w.span_silent
    rw [cut.reconstruct, Execution.allStates_append] at stillBusy
    exact cut.span.allStates_final stillBusy.1
  have allProtected := stays_protected_without_fire cut.span 1 w.fire_fast readyOfCut (by
    have quiet := w.span_silent
    rw [cut.reconstruct, Execution.emissionTimes_append] at quiet
    exact (List.append_eq_nil_iff.mp quiet).1)
  have split : staged.after =
      (w.head.append w.trigger).append
        (cut.span.append (.cons (.jump cut.entry) (cut.rest.append (w.finish.append w.tail)))) := by
    calc
      _ = w.head.append (w.trigger.append
          ((cut.span.append (.cons (.jump cut.entry) cut.rest)).append (w.finish.append w.tail))) :=
        w.reconstruct.trans (congrArg (fun e => w.head.append
          (w.trigger.append (e.append (w.finish.append w.tail)))) cut.reconstruct)
      _ = _ := by simp only [Execution.append_assoc, Execution.append]
  exact exclusive _ _ _ (w.head.append w.trigger) cut.span cut.entry _ split 1
    w.fire_fast allProtected token (by rw [cut.delivery]; simp) rfl

theorem ProtectedReceipt.recovery_dose {last : Snapshot 2} {staged : NominalStaged last} (w : ProtectedReceipt staged) :
    (∀ p, w.finish.ledger.error 1 p = 0) ∧ w.finish.ledger.recovery 1 = 1 / 10 := by
  constructor
  · intro p
    have balance := w.finish.gain_balance 1 p
    rw [w.gain_preserved] at balance
    linarith
  · have balance := w.finish.recovery_balance 1
    rw [w.mark_gain] at balance
    linarith

theorem ProtectedReceipt.no_fixed_input_replay {last : Snapshot 2} {staged : NominalStaged last} (w : ProtectedReceipt staged)
    (M : MarkFeedback.Model 2 P) (d : Nat) (s u : Config 6 P) (p q : P)
    (law : SameReadLaw M p q)
    (gainBefore : w.readySource.x 1 (.z 1) = birthMemory 1 .port0 +
      unitDose .port0 * s.writes (MarkFeedback.gain M p))
    (gainAfter : w.receipt.x 1 (.z 1) = birthMemory 1 .port0 +
      unitDose .port0 * u.writes (MarkFeedback.gain M p))
    (recoveryBefore : w.readySource.x 1 .b = birthMemory 1 .recovery +
      unitDose .recovery * s.writes (MarkFeedback.recovery M p))
    (recoveryAfter : w.receipt.x 1 .b = birthMemory 1 .recovery +
      unitDose .recovery * u.writes (MarkFeedback.recovery M p)) :
    ¬ (MarkFeedback.read M d s p 0 = true ∧ MarkFeedback.read M d u q 0 = false) := by
  apply identical_input_cannot_replay_fire_then_mark M d s u p q law
  · have h := w.same_gain
    rw [gainAfter, gainBefore] at h
    norm_num [unitDose] at h
    exact h.symm
  · have h := w.same_recovery
    rw [recoveryAfter, recoveryBefore] at h
    norm_num [unitDose] at h
    exact h.symm

set_option maxHeartbeats 2000000 in
/-- Retain the actual factory cuts through the full horizon. The proof uses
the same staged construction as the milestone-3 witness. -/
theorem nominal_protected_receipt :
    ∃ last : Snapshot 2, ∃ staged : NominalStaged last,
      CompleteThrough staged.after (4599 / 10) ∧ Nonempty (ProtectedReceipt staged) := by
  have born : BirthState nominalStart := Newborn.nominal_birth_state
  obtain ⟨_, _, _, _, v, f, g, u, t, x, z, w, a, q, p, _, _, _, _, _, _⟩ :=
    birth_protocol_first_reverse_interleaved_pair_exists (born := nominalStart) born nominal_box
      (fun _ => rfl) rfl Newborn.nominal nominalDelay nominalDelay nominal_delay_range nominal_delay_range
  have hzA : Real.log (3 / 10) - 1 / 100000 ≤ q.final.x 0 (.z 2) ∧
      q.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [z.first_reverse_wire_a_gain_own nominal_box.extend_old q 2 (by decide)]
    simpa only [nominalGain, show (2 : Port) ≠ 1 by decide, ite_false]
      using ((born.2.2 0).2.2.2.2 (2 : Port)).1
  have hzB : Real.log (3 / 10) - 1 / 100000 ≤ Newborn.nominal.x (.z 2) ∧
      Newborn.nominal.x (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    simpa only [nominalGain, show (2 : Port) ≠ 1 by decide, ite_false]
      using Newborn.nominal.gain (2 : Port)
  have hGB : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2 := by
    rw [z.feedback_weak_b_gain_own w]
    exact learned_gain_bounds (by linarith [hzB.1]) (by linarith [hzB.2])
  obtain ⟨finish⟩ := reverse_teaching_completion_exists p nominal_box hzA hGB nominal_delay_range
  let span := g.execution.append (u.execution.append t.execution)
  have localCuts : Nonempty (ProtectedReceipt x.staged) := by
    refine ⟨{
      readySource := v.final
      fromFire := f.final
      receipt := t.final
      completed := x.final
      head := v.staged.after
      trigger := f.execution
      span := span
      finish := x.execution
      tail := .nil _
      reconstruct := ?_
      source_ready := v.receiver_ready.ready
      source_raw := v.raw_receiver
      fire_fast := f.receiver_main_fast
      fire_word := f.emissions
      triggering_isolated := f.deliveries
      third_word := ?_
      span_silent := ?_
      third_slow := t.receiver_main_slow
      third_raw := t.raw_active
      silence := by simp [Execution.emissionTimes, x.emissions]
      same_gain := by rw [t.receiver_gain_target nominal_box nominal_delay_range,
        v.receiver_gain_target nominal_box nominal_delay_range]
      same_recovery := t.receiver_recovery.trans v.receiver_recovery.symm
      mark_gain := x.b_recovery_gain
      gain_preserved := x.gains 1
      completed_ready := (x.prepared 1).ready
      completed_raw := x.raw_receiver
      fires_after_arrival := by linarith [f.early]
      receipt_after_fire := by linarith [f.deadline, (t.received_gap nominal_delay_range).1]
      arrival_gap := by linarith [(t.received_gap nominal_delay_range).1]
      completion_date := x.date }⟩
    · let afterFire := v.staged.after.append f.execution
      let afterFast := afterFire.append g.execution
      let afterPost := afterFast.append u.execution
      let afterReceipt := afterPost.append t.execution
      change afterReceipt.append x.execution =
        v.staged.after.append (f.execution.append (span.append (x.execution.append (.nil _))))
      simp only [afterReceipt, afterPost, afterFast, afterFire, span,
        Execution.append_nil_right, Execution.append_assoc]
    · simp [span, Execution.deliveries_append, g.deliveries, u.deliveries, t.deliveries]
    · simp [span, Execution.emissionTimes, Execution.emissions_append, g.emissions, u.emissions, t.emissions]
  obtain ⟨localCut⟩ := localCuts
  let remainder := z.execution.append (w.execution.append (a.execution.append
    (q.execution.append (p.execution.append finish.execution))))
  let staged : NominalStaged finish.final :=
    { x.staged with after := x.staged.after.append remainder }
  have complete : CompleteThrough staged.after (4599 / 10) := finish.complete
  exact ⟨finish.final, staged, complete, ⟨localCut.append remainder⟩⟩

theorem nominal_settled_exclusivity_fails :
    ∃ last : Snapshot 2, ∃ staged : NominalStaged last,
      CompleteThrough staged.after (4599 / 10) ∧
      ¬ AllowsSettledTransactions staged.after := by
  obtain ⟨last, staged, complete, ⟨receipt⟩⟩ := nominal_protected_receipt
  exact ⟨last, staged, complete, receipt.not_settled_exclusive⟩

/-- Queue replay of the visible native events. The queue includes deliveries
that are still in flight. An arrival consumes exactly one occurrence at the
actual jump, and a FIRE issues exactly the contacts prescribed by the router. -/
inductive DatedQueueReplay (route : Router n) :
    List (Delivery n) → List (NativeEvent n) → List (Delivery n) → Prop where
  | nil (pending) : DatedQueueReplay route pending [] pending
  | fire (cell time pending events final) :
      DatedQueueReplay route (pending ++ route cell time) events final →
      DatedQueueReplay route pending (.fire cell time :: events) final
  | arrival (token before after events final) :
      DatedQueueReplay route (before ++ after) events final →
      DatedQueueReplay route (before ++ token :: after) (.arrival token :: events) final

theorem DatedQueueReplay.append {route : Router n}
    {s m u : List (Delivery n)} {a b : List (NativeEvent n)}
    (head : DatedQueueReplay route s a m) (tail : DatedQueueReplay route m b u) :
    DatedQueueReplay route s (a ++ b) u := by
  induction head with
  | nil => exact tail
  | fire cell time pending events final _ ih => exact .fire cell time pending _ u (ih tail)
  | arrival token before after events final _ ih => exact .arrival token before after _ u (ih tail)

private theorem jump_queue_replay {n route s u} (jump : @Jump n route s u) :
    DatedQueueReplay route s.pending (jumpEvents jump) u.pending := by
  cases jump with
  | fire i _ _ => exact .fire i _ _ [] _ (.nil _)
  | arrive token before after queue due free =>
    have take : DatedQueueReplay route (before ++ token :: after) [.arrival token] (before ++ after) :=
      .arrival token before after [] _ (.nil _)
    exact queue.symm ▸ take
  | _ => exact .nil _

theorem native_queue_replay {n θ route s u} (run : @Execution n θ route s u) :
    DatedQueueReplay route s.pending (nativeEvents run) u.pending := by
  induction run with
  | nil => exact .nil _
  | cons move rest ih =>
    change DatedQueueReplay route _ (moveEvents move ++ nativeEvents rest) _
    cases move with
    | flow f => simpa only [moveEvents, List.nil_append, f.queue_fixed] using ih
    | jump j => exact (jump_queue_replay j).append ih

/-- The same event replay covers the one-cell portion and the two-cell
portion. The birth step itself preserves every dated A occurrence and adds
the dated external B sources. -/
theorem nominal_full_dated_replay (epoch : NominalEpoch) :
    DatedQueueReplay (fun _ _ => []) nominalStart.pending (nativeEvents epoch.staged.before)
      epoch.staged.beforeBirth.pending ∧
    epoch.staged.afterBirth.pending =
      epoch.staged.beforeBirth.pending.map liftDelivery ++ constructedBBirthSources ∧
    DatedQueueReplay (reciprocalEntryRouter nominalDelay nominalDelay) epoch.staged.afterBirth.pending
      (nativeEvents epoch.staged.after) epoch.final.pending ∧
    (nativeEvents epoch.staged.before).filterMap NativeEvent.asFire =
      epoch.staged.before.ledger.emissions ∧
    (nativeEvents epoch.staged.after).filterMap NativeEvent.asFire =
      epoch.staged.after.ledger.emissions := by
  exact ⟨native_queue_replay epoch.staged.before,
    epoch.staged.birth.pending.trans
      (congrArg (epoch.staged.beforeBirth.pending.map liftDelivery ++ ·) epoch.sources_origin),
    native_queue_replay epoch.staged.after, (native_event_words epoch.staged.before).1,
    (native_event_words epoch.staged.after).1⟩

/-- Preloading the scheduled source train as eligible probes conflicts with
cell exclusivity. Dated pending and eligible pending are different. -/
theorem source_train_not_cell_exclusive (M : MarkFeedback.Model 2 P) (first second : P)
    (same : M.cell first = M.cell second) (tail : List P) :
    ¬ MarkFeedback.Exclusive M (MarkFeedback.initial 2 (first :: second :: tail)) := by
  simp [MarkFeedback.Exclusive, MarkFeedback.initial, same]


open AutonomousFeedback.Schedule.PortMemory (Coordinate)

/-- Aggregate physical doses across the dimension-changing birth. Before
birth only A has a ledger. The units here are the native real doses. -/
noncomputable def stagedDose (epoch : NominalEpoch) (i : Fin 2) : Coordinate → ℝ
  | .port0 =>
    (if i = 0 then epoch.staged.before.ledger.error 0 0 else 0) +
      epoch.staged.after.ledger.error i (if i = 0 then 0 else 1)
  | .port1 =>
    (if i = 0 then epoch.staged.before.ledger.error 0 2 else 0) +
      epoch.staged.after.ledger.error i 2
  | .recovery =>
    (if i = 0 then epoch.staged.before.ledger.recovery 0 else 0) +
      epoch.staged.after.ledger.recovery i

theorem nominal_staged_dose_balance (epoch : NominalEpoch) (i : Fin 2) (c : Coordinate) :
    stagedDose epoch i c = unitDose c * doseCount i c := by
  have final := reciprocal_counts epoch i c
  have old : epoch.staged.afterBirth.x 0 = epoch.staged.beforeBirth.x 0 :=
    epoch.staged.birth.old_coordinates 0
  have fresh : epoch.staged.afterBirth.x 1 = Newborn.nominal.x := by
    have h := epoch.staged.birth.new_coordinates
    rw [epoch.newborn_origin] at h
    exact h
  fin_cases i <;> cases c
  · have before := epoch.staged.before.gain_balance 0 0
    have after := epoch.staged.after.gain_balance 0 0
    rw [old] at after
    norm_num [stagedDose, nativeCoordinate, birthMemory, nominalStart, Newborn.snapshot,
      unitDose, doseCount] at before after final ⊢
    linarith
  · have before := epoch.staged.before.gain_balance 0 2
    have after := epoch.staged.after.gain_balance 0 2
    rw [old] at after
    norm_num [stagedDose, nativeCoordinate, birthMemory, nominalStart, Newborn.snapshot,
      unitDose, doseCount] at before after final ⊢
    linarith
  · have before := epoch.staged.before.recovery_balance 0
    have after := epoch.staged.after.recovery_balance 0
    rw [old] at after
    norm_num [stagedDose, nativeCoordinate, birthMemory, nominalStart, Newborn.snapshot,
      unitDose, doseCount] at before after final ⊢
    linarith
  · have after := epoch.staged.after.gain_balance 1 1
    rw [fresh] at after
    norm_num [stagedDose, nativeCoordinate, birthMemory, unitDose, doseCount] at after final ⊢
    linarith
  · have after := epoch.staged.after.gain_balance 1 2
    rw [fresh] at after
    norm_num [stagedDose, nativeCoordinate, birthMemory, unitDose, doseCount] at after final ⊢
    linarith
  · have after := epoch.staged.after.recovery_balance 1
    rw [fresh] at after
    norm_num [stagedDose, nativeCoordinate, birthMemory, unitDose, doseCount] at after final ⊢
    linarith


/-- The main admission mode distinguishes the two forward receipts even
when their stored gain and recovery are equal. -/
inductive ForwardAdmission
  | ready
  | slow
  deriving DecidableEq

def protectedPairModel : MarkFeedback.Model 2 ForwardAdmission where
  cell := fun _ => 1
  secondPort := fun _ => false
  bias := fun phase => if phase = .ready then 2 else -2
  recoveryWeight := fun _ => 0
  learn := fun _ => false
  mark := fun phase fire => phase == .slow && !fire
  route := fun _ => []

def protectedPairSeed : List ForwardAdmission := [.ready, .slow]

def protectedPairStart : Config 6 ForwardAdmission := MarkFeedback.initial 2 protectedPairSeed

def protectedPairMiddle : Config 6 ForwardAdmission :=
  MarkFeedback.process protectedPairModel 1 protectedPairStart .ready [.slow] 0

def protectedPairEnd : Config 6 ForwardAdmission :=
  MarkFeedback.process protectedPairModel 1 protectedPairMiddle .slow [] 0

theorem protected_pair_certified :
    MarkFeedback.CertifiedPath protectedPairModel 1 protectedPairStart protectedPairEnd := by
  apply MarkFeedback.CertifiedPath.cons .ready [.slow] (List.Perm.refl _) (-1) 1 0 (by decide)
    (by unfold RoutedCalendar.HasRoom; right; decide)
  apply MarkFeedback.CertifiedPath.cons .slow [] (List.Perm.refl _) (-1) 1 0 (by decide)
    (by unfold RoutedCalendar.HasRoom; left; decide)
  exact .nil _

/-- Guarded replay of the two B transactions distinguished by native
admission. This local slice omits A's intervening FIRE and routes. -/
theorem ProtectedReceipt.certified_pair {last : Snapshot 2} {staged : NominalStaged last} (w : ProtectedReceipt staged) :
    MarkFeedback.CertifiedPath protectedPairModel 1 protectedPairStart protectedPairEnd ∧
    MarkFeedback.read protectedPairModel 1 protectedPairStart .ready 0 = true ∧
    MarkFeedback.read protectedPairModel 1 protectedPairMiddle .slow 0 = false ∧
    w.trigger.ledger.emissions = [(1, w.fromFire.time)] ∧ w.finish.emissionTimes 1 = [] ∧
    w.completed.x 1 (.z 1) = w.readySource.x 1 (.z 1) +
      unitDose .port0 * (protectedPairEnd.writes (MarkFeedback.gain protectedPairModel .ready) : ℝ) ∧
    w.completed.x 1 .b = w.readySource.x 1 .b +
      unitDose .recovery * (protectedPairEnd.writes (MarkFeedback.recovery protectedPairModel .ready) : ℝ) := by
  refine ⟨protected_pair_certified, by decide, by decide, w.fire_word, w.silence, ?_, ?_⟩
  · have counts : protectedPairEnd.writes (MarkFeedback.gain protectedPairModel .ready) = 0 := by decide
    rw [counts, Nat.cast_zero, mul_zero, add_zero]
    exact (w.gain_preserved 1).trans w.same_gain
  · have counts : protectedPairEnd.writes (MarkFeedback.recovery protectedPairModel .ready) = 1 := by decide
    rw [counts, Nat.cast_one, mul_one, w.mark_gain, w.same_recovery]
    rfl

/-- Margins on the shared stored-memory score cannot turn identical
certified nominal reads into the two different native decisions. -/
theorem certified_opposite_decisions_need_different_read_laws (M : MarkFeedback.Model N P) (d : Nat)
    (s u : Config (3 * N) P) (p q : P) (law : SameReadLaw M p q)
    (gain : s.writes (MarkFeedback.gain M p) = u.writes (MarkFeedback.gain M q))
    (recovery : s.writes (MarkFeedback.recovery M p) = u.writes (MarkFeedback.recovery M q))
    (lo hi lo' hi' e e' : Int) (within : lo ≤ e ∧ e ≤ hi) (within' : lo' ≤ e' ∧ e' ≤ hi')
    (room : RoutedCalendar.HasRoom (MarkFeedback.score M d s p) lo hi)
    (room' : RoutedCalendar.HasRoom (MarkFeedback.score M d u q) lo' hi') :
    MarkFeedback.read M d s p e = MarkFeedback.read M d u q e' := by
  exact (MarkFeedback.read_eq_of_room _ _ _ _ within room).trans
    ((same_read_law_same_decision M d s u p q law gain recovery).trans
      (MarkFeedback.read_eq_of_room _ _ _ _ within' room').symm)

end NetworkStability.NativeReciprocal
