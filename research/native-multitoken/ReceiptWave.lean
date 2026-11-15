import ReceiptProduct
import ReceiptTiming

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid NativeStrong MeasureTheory

noncomputable def sourceOf {p : Parameters N} (accepted : p.check = true) (i : Fin N) : Fin N :=
  (Equiv.ofBijective p.successor
    (Finite.injective_iff_bijective.mp (fun {_ _} h =>
      (of_decide_eq_true accepted : p.Valid).2.2.2.1.1 _ _ h))).symm i

theorem sourceOf_receives {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    p.successor (sourceOf accepted i) = i :=
  (Equiv.ofBijective p.successor
    (Finite.injective_iff_bijective.mp (fun {_ _} h =>
      (of_decide_eq_true accepted : p.Valid).2.2.2.1.1 _ _ h))).apply_symm_apply i

/-- All receipts run from the common SLOW cut. Each local queue contains
its own one-cell occurrence, lifted to the native queue by synchronization. -/
theorem protected_receipt_wave {p : Parameters N} (accepted : p.check = true) {ε : ℝ}
    (box : PhysicalBox (nativeParameters N) ε) (s : Snapshot N)
    (physical : PhysicalInvariant (nativeParameters N) s) (valid : RawValid s)
    (before : ∀ i, s.time < receiptDate p (sourceOf accepted i))
    (slow : ∀ i, s.main i = .slow)
    (charge : ∀ i, s.x i .q = (1 / 4) * Real.exp
      (-(9 / 50) * (s.time - receiverFastEnd p (sourceOf accepted i))))
    (recovery : ∀ i, s.x i .b = 9 / 50)
    (aux : ∀ i q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (raw : ∀ i q, s.raw i q = none)
    (pending : s.pending.Perm ((List.finRange N).map
      (fun i => ⟨i, 2, receiptDate p (sourceOf accepted i)⟩))) :
    ∃ (u : Snapshot N) (run : Execution (nativeParameters N) (router p) s u),
      CompleteThrough run (horizon p) ∧ u.pending = [] ∧
      s.pending.Perm run.deliveries ∧ run.ledger.emissions = [] ∧
      ∀ i, ReadyCoordinates u i ∧ (∀ q, u.raw i q = none) ∧
        run.ledger.recovery i = 1 / 10 ∧
        (∀ q, run.ledger.error i q = 0 ∧
          run.ledger.mark i q = if q = 2 then 1 / 10 else 0) := by
  classical
  let receipt (i : Fin N) : Delivery 1 := ⟨0, 2, receiptDate p (sourceOf accepted i)⟩
  let start (i : Fin N) := { localView s i with pending := [receipt i] }
  let T := launchDate p + 19 / 2
  have leg (i : Fin N) :
      ∃ (u : Snapshot 1) (run : Execution (fun _ => nativeParameters N i) (EmptyRouter 1) (start i) u),
        u.time = T ∧ u.pending = [] ∧ run.deliveries = [receipt i] ∧ run.ledger.emissions = [] ∧
        ReadyCoordinates u 0 ∧ (∀ q, u.raw 0 q = none) ∧
        run.ledger.recovery 0 = 1 / 10 ∧
        (∀ q, run.ledger.error 0 q = 0 ∧ run.ledger.mark 0 q = if q = 2 then 1 / 10 else 0) := by
    let source := sourceOf accepted i
    let θ := fun _ : Fin 1 => nativeParameters N i
    have localBox : PhysicalBox θ ε := ⟨box.1, fun _ q => box.2 i q⟩
    have localPhysical : PhysicalInvariant θ (start i) :=
      ⟨fun _ => physical.region i, fun _ q => physical.gain_cap i q,
        fun _ => physical.recovery_cap i, fun _ => physical.reserve i⟩
    have localValid : RawValid (start i) := fun _ q o h => valid i q o h
    obtain ⟨atDate, wait, date, mode, x, b, gains, sensor, noRaw, token, silent, noFire, waitMark⟩ :=
      slow_span_to_receipt (route := EmptyRouter 1) (θ := θ) accepted source (start i)
        (receiptDate p source) (before i) le_rfl (slow i) (charge i) (recovery i)
        (aux i) (raw i) (by intro d mem; rcases List.mem_singleton.mp mem with rfl; exact le_rfl)
    have clock : atDate.time = launchDate p + latency p source + (p.delay source : ℝ) := date
    have exactCharge : atDate.x 0 .q = (1 / 4) * Real.exp (-(9 / 50) *
        (atDate.time - (launchDate p + latency p (p.successor source) + 1))) := x
    have actualQueue : atDate.pending = [⟨0, 2, atDate.time⟩] := by
      rw [token, date]
    obtain ⟨reopened, learn, _, readyDate, ready, _, ended, queueDone, delivered, emitted, dose, doses⟩ :=
      protected_slow_admission (route := EmptyRouter 1) accepted source localBox atDate
        (wait.physical_invariant localBox localPhysical) (wait.raw_valid localValid) mode clock exactCharge b
        sensor noRaw [] actualQueue (by simp)
    have enough : reopened.time < T := by
      have bound := (receipt_timing accepted source).2.2
      rw [date] at readyDate
      exact readyDate.trans bound
    have readyAll (j : Fin 1) : ReadyCoordinates reopened j := by
      rw [show j = 0 from Subsingleton.elim _ _]
      exact ready
    have inactive (j : Fin 1) (q : Port) : reopened.raw j q = none := by
      rw [show j = 0 from Subsingleton.elim _ _]
      exact ended q
    let idleFlow : Flow θ reopened (quietAt reopened T) := quietFlow reopened enough
      (fun j => (readyAll j).ready) (fun j q => ((readyAll j).auxiliary q).1) inactive
      (fun j => by linarith [(readyAll j).charge.2])
      (fun j q => by linarith [((readyAll j).auxiliary q).2.2])
      (by simp [queueDone])
    let idle : Execution θ (EmptyRouter 1) reopened (quietAt reopened T) := .cons (.flow idleFlow) (.nil _)
    let trace := wait.append (learn.append idle)
    have firstRecovery : atDate.x 0 .b = (start i).x 0 .b := b.trans (recovery i).symm
    have idleMark (q : Port) : idle.ledger.mark 0 q = 0 := by
      change (∫ v in reopened.time..T, markAct θ reopened (idleFlow.path v) 0 q) + 0 = 0
      simp [markAct, (ready.auxiliary q).1]
    refine ⟨quietAt reopened T, trace, rfl, queueDone, ?_, ?_,
      quietAt_ready_coordinates reopened 0 ready enough.le, ended, ?_, ?_⟩
    · change (wait.append (learn.append idle)).deliveries = _
      rw [Execution.deliveries_append, Execution.deliveries_append, silent, delivered]
      simp [idle, Execution.deliveries, Move.deliveries, date, receipt, source]
    · simp [trace, Execution.emissions_append, noFire, emitted, idle,
        Execution.ledger, Move.ledger, Flow.ledger, Ledger.add, Ledger.zero]
    · have h := trace.recovery_balance 0
      have hLearn := learn.recovery_balance 0
      change reopened.x 0 .b = (start i).x 0 .b + trace.ledger.recovery 0 at h
      rw [dose, firstRecovery] at hLearn
      linarith
    · intro q
      refine ⟨?_, ?_⟩
      · have h := trace.gain_balance 0 q
        have hLearn := learn.gain_balance 0 q
        have hWait := wait.gain_balance 0 q
        have noGain : wait.ledger.error 0 q = 0 := by
          have unchanged := gains q
          linarith
        change reopened.x 0 (.z q) = (start i).x 0 (.z q) + trace.ledger.error 0 q at h
        rw [(doses q).1] at hLearn
        rw [noGain] at hWait
        linarith
      · change (wait.append (learn.append idle)).ledger.mark 0 q = _
        rw [Execution.mark_append, Execution.mark_append, waitMark, idleMark, zero_add,
          add_zero, (doses q).2]
  choose finals legs finish empty delivered fired ready ended recoveryDose doses using leg
  have scheduled : s.pending.Perm ((List.finRange N).flatMap fun i => (legs i).deliveries.map (receiptAt i)) := by
    refine pending.trans ?_
    have same : ((List.finRange N).flatMap fun i => (legs i).deliveries.map (receiptAt i)) =
        (List.finRange N).map (fun i => ⟨i, 2, receiptDate p (sourceOf accepted i)⟩) := by
      calc
        _ = (List.finRange N).flatMap (fun i => [⟨i, 2, receiptDate p (sourceOf accepted i)⟩]) := by
          apply List.flatMap_congr
          intro i _
          rw [delivered]
          rfl
        _ = ((List.finRange N).map (fun i => (⟨i, 2, receiptDate p (sourceOf accepted i)⟩ : Delivery N))).flatMap
              (fun d => [d]) := (List.flatMap_map
                (fun i => (⟨i, 2, receiptDate p (sourceOf accepted i)⟩ : Delivery N))
                (fun d => [d]) (List.finRange N)).symm
        _ = _ := List.flatMap_singleton' _
    rw [same]
  obtain ⟨woven, noFire, consumed, marks⟩ :=
    synchronized_receipt_execution (route := router p) start finals legs (fun _ => rfl) finish
      (by
        have nonempty : 2 ≤ N := (of_decide_eq_true accepted : p.Valid).1
        let i : Fin N := ⟨0, by omega⟩
        have bound := (receipt_timing accepted (sourceOf accepted i)).2.2
        change s.time ≤ launchDate p + 19 / 2
        linarith [before i]) fired s.pending scheduled
  have begin : assemble s.time start s.pending = s := by
    cases s
    rfl
  let t := assemble T finals []
  let part := woven.cast_source begin.symm
  have partLedger : part.ledger = woven.ledger := woven.cast_source_ledger begin.symm
  have readyAt (i : Fin N) : ReadyCoordinates t i :=
    ⟨(ready i).ready, (ready i).charge, (ready i).auxiliary⟩
  have idleTime : t.time < horizon p := by change T < launchDate p + 10; dsimp [T]; linarith
  let quiet : Flow (nativeParameters N) t (quietAt t (horizon p)) := quietFlow t idleTime
    (fun i => (readyAt i).ready) (fun i q => ((readyAt i).auxiliary q).1) ended
    (fun i => by linarith [(readyAt i).charge.2])
    (fun i q => by linarith [((readyAt i).auxiliary q).2.2])
    (by simp [t, assemble])
  let suffix : Execution (nativeParameters N) (router p) t (quietAt t (horizon p)) :=
    .cons (.flow quiet) (.nil _)
  let run := part.append suffix
  have readyFinal (i : Fin N) : ReadyCoordinates (quietAt t (horizon p)) i :=
    quietAt_ready_coordinates t i (readyAt i) idleTime.le
  have complete : CompleteThrough run (horizon p) := by
    refine ⟨rfl, ?_, by simp [quietAt, t, assemble]⟩
    intro v
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rw [(readyFinal i).ready]
        linarith [(readyFinal i).charge.2]
      · intro i q
        rw [((readyFinal i).auxiliary q).1]
        linarith [((readyFinal i).auxiliary q).2.2]
    · intro i q o h
      have absent : (quietAt t (horizon p)).raw i q = none := ended i q
      rw [absent] at h
      cases h
    · simp [quietAt, t, assemble]
  refine ⟨_, run, complete, rfl, ?_, ?_, ?_⟩
  · change s.pending.Perm (part.append suffix).deliveries
    rw [Execution.deliveries_append, woven.cast_source_deliveries begin.symm]
    have none : suffix.deliveries = [] := rfl
    rw [none, List.append_nil]
    exact consumed
  · change (part.append suffix).ledger.emissions = []
    rw [Execution.emissions_append, partLedger, noFire]
    rfl
  · intro i
    refine ⟨readyFinal i, ended i, ?_, ?_⟩
    · have global := run.recovery_balance i
      have localBalance := (legs i).recovery_balance 0
      change (finals i).x 0 .b = s.x i .b + run.ledger.recovery i at global
      change (finals i).x 0 .b = s.x i .b + (legs i).ledger.recovery 0 at localBalance
      rw [recoveryDose] at localBalance
      linarith
    · intro q
      refine ⟨?_, ?_⟩
      · have global := run.gain_balance i q
        have localBalance := (legs i).gain_balance 0 q
        change (finals i).x 0 (.z q) = s.x i (.z q) + run.ledger.error i q at global
        change (finals i).x 0 (.z q) = s.x i (.z q) + (legs i).ledger.error 0 q at localBalance
        rw [(doses i q).1] at localBalance
        linarith
      · have noMark : suffix.ledger.mark i q = 0 := by
          change (∫ v in t.time..horizon p, markAct (nativeParameters N) t (quiet.path v) i q) + 0 = 0
          simp [markAct, ((readyAt i).auxiliary q).1]
        change (part.append suffix).ledger.mark i q = _
        rw [Execution.mark_append, noMark, partLedger, add_zero, marks, (doses i q).2]

end NetworkStability.NativeMultiToken
