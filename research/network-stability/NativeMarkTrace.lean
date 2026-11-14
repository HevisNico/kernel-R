import NativeEndpoint
import MarkFeedback

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid

/-- The observable projection of each actual native step, in execution order. -/
inductive NativeEvent (n : Nat)
  | arrival (token : Delivery n)
  | fire (cell : Fin n) (time : ℝ)

def jumpEvents {n route s u} (j : @Jump n route s u) : List (NativeEvent n) := by
  cases j
  case arrive token _ _ _ _ _ => exact [.arrival token]
  case fire i _ _ => exact [.fire i s.time]
  all_goals exact []

def moveEvents {n θ route s u} (move : @KernelR.Hybrid.Move n θ route s u) : List (NativeEvent n) :=
  match move with
  | .flow _ => []
  | .jump j => jumpEvents j

def nativeEvents {n θ route s u} (run : @Execution n θ route s u) : List (NativeEvent n) :=
  match run with
  | .nil _ => []
  | .cons move rest => moveEvents move ++ nativeEvents rest

def NativeEvent.asFire : NativeEvent n → Option (Fin n × ℝ)
  | .arrival _ => none
  | .fire i t => some (i, t)

def NativeEvent.asArrival : NativeEvent n → Option (Delivery n)
  | .arrival token => some token
  | .fire _ _ => none

theorem native_event_words {n θ route s u} (run : @Execution n θ route s u) :
    (nativeEvents run).filterMap NativeEvent.asFire = run.ledger.emissions ∧
      (nativeEvents run).filterMap NativeEvent.asArrival = run.deliveries := by
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | cons move rest ih =>
    simp only [nativeEvents, List.filterMap_append, Execution.ledger, Ledger.add, Execution.deliveries,
      ih.1, ih.2]
    cases move with
    | flow f => exact ⟨rfl, rfl⟩
    | jump j => cases j <;> exact ⟨rfl, rfl⟩

/-- If an already active pulse occupies this port at the start, every
subsequent same-port arrival is at or after its unit-length expiry. -/
theorem arrival_after_raw_window {n θ route s u} (run : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (active : s.raw i p = some origin)
    (token : Delivery n) (mem : token ∈ run.deliveries) (cell : token.cell = i)
    (port : token.port = p) : origin + 1 ≤ token.due := by
  induction run with
  | nil => simp [Execution.deliveries] at mem
  | @cons s v u move rest ih =>
    rcases List.mem_append.mp mem with first | later
    · cases move with
      | flow f => simp [Move.deliveries] at first
      | jump j =>
        obtain ⟨_, _, _, _, free, _⟩ := j.delivery_snapshot token first
        rw [cell, port, active] at free
        contradiction
    · cases move with
      | flow f => exact ih (by rw [f.raw_fixed]; exact active) later
      | jump j =>
        by_cases same : v.raw i p = some origin
        · exact ih same later
        · have ended := (j.raw_departure i p origin active same).1
          rw [← ended, ← j.time_unchanged]
          exact (rest.delivery_time_bounds token later).1

/-- Actual arrival timestamps, with multiplicities retained, prove
non-overlap of the unit raw windows on each receiving port. -/
theorem actual_raw_windows_disjoint {n θ route s u} (run : @Execution n θ route s u) :
    run.deliveries.Pairwise
      (fun a b => a.cell = b.cell → a.port = b.port → a.due + 1 ≤ b.due) := by
  induction run with
  | nil => exact .nil
  | @cons s v u move rest ih =>
    apply List.pairwise_append.mpr
    refine ⟨?_, ih, ?_⟩
    · cases move with
      | flow f => exact .nil
      | jump j => cases j <;> simp [Move.deliveries, Jump.deliveries]
    · intro a first b later cell port
      cases move with
      | flow f => simp [Move.deliveries] at first
      | jump j =>
        obtain ⟨before, after, _, due, _, out⟩ := j.delivery_snapshot a first
        have active : v.raw a.cell a.port = some a.due := by
          rw [out, due]
          simp [setRaw]
        exact arrival_after_raw_window rest a.cell a.port a.due active b later cell.symm port.symm

theorem reciprocal_native_event_words (epoch : NominalEpoch) :
    ((nativeEvents epoch.staged.after).filterMap NativeEvent.asFire =
      epoch.staged.after.ledger.emissions) ∧
    ((nativeEvents epoch.staged.after).filterMap NativeEvent.asArrival).Pairwise
      (fun a b => a.cell = b.cell → a.port = b.port → a.due + 1 ≤ b.due) := by
  obtain ⟨fires, arrivals⟩ := native_event_words epoch.staged.after
  exact ⟨fires, arrivals ▸ actual_raw_windows_disjoint epoch.staged.after⟩

/-- FIRE and MARK occur at different semantic levels in the native system.
At the actual FIRE jump, all six memories are preserved. -/
theorem fire_jump_preserves_recovery {n route s u} (j : @Jump n route s u) (i : Fin n) :
    u.x i .b = s.x i .b := by rw [j.physical_continuous]

/-- An atomic MARK commit must span native flow. A positive recovery dose
cannot be matched by a cut pair at one timestamp. -/
theorem positive_mark_requires_elapsed_time {n θ route s u} (run : @Execution n θ route s u)
    (i : Fin n) (paid : s.x i .b < u.x i .b) : s.time < u.time := by
  refine lt_of_le_of_ne run.time_monotone ?_
  intro same
  rw [run.zero_duration_continuous same.symm] at paid
  exact (lt_irrefl _) paid


open MarkFeedback (Model initial process read gain recovery)
open AutonomousFeedback.Schedule (Config)

/-- The receiving side of the first forward-teaching phase, up to the
first completed recovery dose. -/
inductive ForwardProbe
  | weak
  | strong
  | markOnly
  deriving DecidableEq

def forwardReceiver : Model 2 ForwardProbe where
  cell := fun _ => 1
  secondPort := fun _ => false
  bias := fun p => if p == .markOnly then -2 else -1
  recoveryWeight := fun _ => 0
  learn := fun p => p != .markOnly
  mark := fun p fire => (p == .markOnly) && !fire
  route := fun _ => []

def forwardSeed : List ForwardProbe :=
  [.weak, .strong, .markOnly]

def receiverReplay : List ForwardProbe → Config 6 ForwardProbe → List (Fin 2) × Config 6 ForwardProbe
  | [], s => ([], s)
  | p :: rest, s =>
    let fired := read forwardReceiver 1 s p 0
    let result := receiverReplay rest (process forwardReceiver 1 s p rest 0)
    ((if fired then [forwardReceiver.cell p] else []) ++ result.1, result.2)

theorem forward_replay_computes :
    (receiverReplay forwardSeed (initial 2 forwardSeed)).1 = [1] ∧
    (receiverReplay forwardSeed (initial 2 forwardSeed)).2.writes (gain forwardReceiver .weak) = 1 ∧
    (receiverReplay forwardSeed (initial 2 forwardSeed)).2.writes (recovery forwardReceiver .weak) = 1 := by
  decide

private theorem nominal_delay_bounds :
    ∀ t, (3 / 10 : ℝ) ≤ nominalDelay t ∧ nominalDelay t ≤ 2 / 5 := by
  intro t
  norm_num [nominalDelay]

/-- The first three B receptions in the forward-teaching construction
give one gain dose, one FIRE, and one recovery dose. The MARK is supplied
by the third reception while B is already protected. -/
theorem forward_receiver_prefix :
    ∃ (s u : Snapshot 2)
      (run : Execution
        (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
        (reciprocalEntryRouter nominalDelay nominalDelay) s u),
      (run.ledger.emissions.filter (fun event => event.1 = 1)).map Prod.fst =
        (receiverReplay forwardSeed (initial 2 forwardSeed)).1 ∧
      u.x 1 (.z 1) = birthMemory 1 .port0 +
        unitDose .port0 * (receiverReplay forwardSeed (initial 2 forwardSeed)).2.writes
          (gain forwardReceiver .weak) ∧
      u.x 1 .b = birthMemory 1 .recovery +
        unitDose .recovery * (receiverReplay forwardSeed (initial 2 forwardSeed)).2.writes
          (recovery forwardReceiver .weak) ∧
      ∃ a b c fire : ℝ, run.emissionTimes 1 = [fire] ∧ b < fire ∧ fire < c ∧
        run.cellDeliveries 1 = [⟨1,1,a⟩, ⟨1,1,b⟩, ⟨1,1,c⟩] ∧
        a + 15 / 2 ≤ b ∧ b + 15 / 2 ≤ c ∧ c + 13 / 2 < u.time ∧
        ∃ aFire bFire cFire : ℝ, run.emissionTimes 0 = [aFire, bFire, cFire] ∧
          a = aFire + nominalDelay aFire ∧ b = bFire + nominalDelay bFire ∧
          c = cFire + nominalDelay cFire := by
  obtain ⟨_, _, r, pair, w, f, fast, post, t, x, _, _, _, _, _⟩ :=
    birth_protocol_first_coupled_teaching_exists (born := nominalStart) Newborn.nominal_birth_state nominal_box
      (fun _ => rfl) (show nominalStart.pending = _ from rfl) Newborn.nominal nominalDelay nominalDelay
      nominal_delay_bounds
  refine ⟨_, _, x.staged.after, ?_, ?_, ?_, ?_⟩
  · rw [x.staged_emissions, forward_replay_computes.1]
    simp
  · have writes := forward_replay_computes.2.1
    rw [writes, Nat.cast_one, mul_one]
    exact x.b_gain_target nominal_box nominal_delay_bounds
  · rw [forward_replay_computes.2.2, Nat.cast_one, mul_one]
    exact x.b_recovery_own
  · have arrivals : x.staged.after.cellDeliveries 1 =
        [⟨1,1,r.final.time⟩, ⟨1,1,w.final.time⟩, ⟨1,1,t.final.time⟩] := by
      simp [Execution.cellDeliveries, x.staged_deliveries]
    have first : r.final.time + 15 / 2 ≤ w.final.time := by
      linarith [(w.received_gap nominal_delay_bounds).1]
    have second : w.final.time + 15 / 2 ≤ t.final.time := by
      linarith [(t.received_gap nominal_delay_bounds).1]
    have last : t.final.time + 13 / 2 < x.final.time := by
      rw [x.date]
      linarith [(t.date_bounds nominal_delay_bounds).2]
    have fireWord : x.staged.after.emissionTimes 1 = [f.final.time] := by
      rw [Execution.emissionTimes, x.staged_emissions]
      simp
    have afterSecond : w.final.time < f.final.time := by linarith [f.early]
    have beforeThird : f.final.time < t.final.time := by
      linarith [f.deadline, (t.received_gap nominal_delay_bounds).1]
    have sourceWord : x.staged.after.emissionTimes 0 =
        [r.fire.final.time, w.fire.final.time, t.fire.final.time] := by
      rw [Execution.emissionTimes, x.staged_emissions]
      simp
    exact ⟨r.final.time, w.final.time, t.final.time, f.final.time, fireWord,
      afterSecond, beforeThird, arrivals, first, second, last,
      r.fire.final.time, w.fire.final.time, t.fire.final.time, sourceWord, r.date, w.date, t.date⟩

end NetworkStability.NativeReciprocal
