import TrainingClock
import SynchronizedProduct

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid

/-- A full native weak wave with its actual same-date admission list, the
settled cut, and the subsequent quiet span to the next indicated date. -/
structure TrainingStage {p : Parameters N} (s : Snapshot N) (nextDate : ℝ) where
  admitted : Snapshot N
  settled : Snapshot N
  next : Snapshot N
  intake : Execution (nativeParameters N) (router p) s admitted
  wave : Execution (nativeParameters N) (router p) admitted settled
  quiet : Execution (nativeParameters N) (router p) settled next
  settledDate : settled.time = s.time + 15 / 2
  date : next.time = nextDate
  intakeWord : intake.deliveries = waveTokens s.time (fun _ => 0) (List.finRange N)
  noArrivals : wave.deliveries = [] ∧ quiet.deliveries = []
  noFires : intake.ledger.emissions = [] ∧ wave.ledger.emissions = [] ∧ quiet.ledger.emissions = []
  pending : next.pending = settled.pending
  ready : ∀ i, ReadyCoordinates next i
  raw : ∀ i q, next.raw i q = none
  charge : ∀ i, next.x i .q = afterSilent (s.x i .q) (Real.exp (s.x i (.z 0))) (nextDate - s.time)
  gains : ∀ i q, next.x i (.z q) = s.x i (.z q) + if q = 0 then 3 / 5 else 0
  recovery : ∀ i, next.x i .b = s.x i .b
  physical : PhysicalInvariant (nativeParameters N) next
  valid : RawValid next

theorem training_stage_exists {p : Parameters N} {ε : ℝ}
    (box : PhysicalBox (nativeParameters N) ε) (s : Snapshot N)
    (physical : PhysicalInvariant (nativeParameters N) s) (valid : RawValid s)
    (ready : ∀ i, ReadyCoordinates s i) (raw : ∀ i q, s.raw i q = none)
    (window : ∀ i, Real.exp (s.x i (.z 0)) ≤ 7 / 6)
    (headroom : ∀ i, s.x i (.z 0) ≤ Real.log (6 / 5) + 1 / 1000)
    (later : List (Delivery N))
    (queue : s.pending = waveTokens s.time (fun _ => 0) (List.finRange N) ++ later)
    (nextDate : ℝ) (next : s.time + 15 / 2 < nextDate)
    (future : ∀ token ∈ later, nextDate ≤ token.due) :
    ∃ stage : TrainingStage (p := p) s nextDate, stage.next.pending = later := by
  let port : Fin N → Port := fun _ => 0
  let a := admittedWave s port (List.finRange N) later
  obtain ⟨intake, intakeWord, intakeSilent⟩ :=
    admit_wave (θ := nativeParameters N) (route := router p) s port _ (List.nodup_finRange N)
      later queue (fun i _ => raw i 0)
  have active (i : Fin N) : a.raw i 0 = some a.time := by
    simp [a, admittedWave, port]
  have inactive (i : Fin N) (q : Port) (ne : q ≠ 0) : a.raw i q = none := by
    simp [a, admittedWave, port, ne, raw]
  have aReady (i : Fin N) : ReadyCoordinates a i :=
    ⟨(ready i).ready, (ready i).charge, (ready i).auxiliary⟩
  have aPhysical := intake.physical_invariant box physical
  have aValid := intake.raw_valid valid
  obtain ⟨settled, wave, complete, pending, deliveries, fires, dose⟩ :=
    weak_training_wave (route := router p) box a port aPhysical aValid aReady active inactive
      window headroom (fun token mem => next.trans_le (future token mem))
  have date : settled.time = s.time + 15 / 2 := complete.1
  have readySettled (i : Fin N) : ReadyCoordinates settled i := (dose i).1
  have rawSettled (i : Fin N) (q : Port) : settled.raw i q = none := (dose i).2.1 q
  have pendingSettled : settled.pending = later := pending
  have readyDate : settled.time < nextDate := by rw [date]; exact next
  let flow : Flow (nativeParameters N) settled (quietAt settled nextDate) := quietFlow settled readyDate
    (fun i => (readySettled i).ready) (fun i q => ((readySettled i).auxiliary q).1) rawSettled
    (fun i => by linarith [(readySettled i).charge.2])
    (fun i q => by linarith [((readySettled i).auxiliary q).2.2])
    (fun token mem => future token (pendingSettled ▸ mem))
  let wait : Execution (nativeParameters N) (router p) settled (quietAt settled nextDate) :=
    .cons (.flow flow) (.nil _)
  have noArrival (i : Fin N) (q : Port) : NoArrivalAt wave i q := by
    simp [NoArrivalAt, deliveries]
  refine ⟨{
    admitted := a, settled := settled, next := quietAt settled nextDate
    intake := intake, wave := wave, quiet := wait
    settledDate := date, date := rfl
    intakeWord := intakeWord, noArrivals := ⟨deliveries, rfl⟩
    noFires := ⟨intakeSilent, fires, rfl⟩, pending := rfl
    ready := fun i => quietAt_ready_coordinates settled i (readySettled i) readyDate.le
    raw := rawSettled, charge := ?_, gains := ?_, recovery := ?_
    physical := wait.physical_invariant box (wave.physical_invariant box aPhysical)
    valid := wait.raw_valid (wave.raw_valid aValid)
    }, pendingSettled⟩
  · intro i
    obtain ⟨pulse⟩ := wave.silent_pulse_of_invariant box aPhysical aValid i 0 (aReady i)
      (headroom i) (active i) (inactive i) (noArrival i) (by rw [date]; change s.time + 15 / 2 ≤ _; exact le_rfl)
    have carried := native_training_clock wave i 0 pulse (active i) (inactive i)
      (noArrival i) (by rw [date]; change s.time + 1 < s.time + 15 / 2; linarith)
    change relax (1 / 2) (1 / 10) (settled.x i .q) settled.time nextDate = _
    rw [carried]
    change relax (1 / 2) (1 / 10)
      (afterSilent (s.x i .q) (Real.exp (s.x i (.z 0))) (settled.time - s.time))
      settled.time nextDate = _
    simp only [relax, afterSilent, add_sub_cancel_left, mul_assoc, ← Real.exp_add]
    congr 3 <;> ring
  · intro i q
    have h := wave.gain_balance i q
    rw [((dose i).2.2.2 q).2] at h
    exact h
  · intro i
    have h := wave.recovery_balance i
    rw [(dose i).2.2.1, add_zero] at h
    exact h

end NetworkStability.NativeMultiToken
