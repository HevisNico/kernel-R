import NativeComposition

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid

/-- A sequence of native weak transactions, with each intervening actual
delivery retaining the complete queue and all physical coordinates. -/
inductive WeakTransactions {n θ route} (i : Fin n) (p : Port) :
    {s u : Snapshot n} → Execution θ route s u → List ℝ → Prop where
  | nil (s : Snapshot n) : WeakTransactions i p (.nil s) []
  | cons {s u : Snapshot n} {run : Execution θ route s u}
      {date : ℝ} {tokens : List (Delivery n)}
      (cut : CellDeliveryStep run i ⟨i, p, date⟩ tokens)
      (active : s.raw i p = some s.time) (ready : ReadyCoordinates s i)
      (pulse : SilentPulse cut.span i p)
      {later : List ℝ} (tail : WeakTransactions i p cut.rest later) :
      WeakTransactions i p run (s.time :: later)

theorem WeakTransactions.fire_word {n θ route s u i p} {run : @Execution n θ route s u}
    {dates : List ℝ} (cert : WeakTransactions i p run dates) : run.emissionTimes i = [] := by
  induction cert with
  | nil => rfl
  | cons cut _ _ pulse _ ih => rw [cut.emissions, pulse.emissions, ih]; rfl

/-- Re-extract individual weak pulses from the original execution.
The cut is taken at the next receipt, so the proof also records the
boundary into the next transaction. -/
theorem weak_transactions {n θ ε route} (box : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (times future : List ℝ) (stage : Nat)
    {s u : Snapshot n} (run : Execution θ route s u) (physical : PhysicalInvariant θ s)
    (valid : RawValid s) (ready : ReadyCoordinates s i) (stageBound : stage + times.length ≤ 3)
    (gain : s.x i (.z p) ≤ Real.log (3 / 10) + (3 / 5) * (stage : ℝ) + 1 / 100000)
    (active : s.raw i p = some s.time) (other : ∀ q, q ≠ p → s.raw i q = none)
    (calendar : run.cellDeliveries i = (times ++ future).map (fun date => ⟨i, p, date⟩))
    (spacing : (s.time :: (times ++ future)).Pairwise (fun a b => a + 15 / 2 ≤ b)) :
    ∃ (finish : Snapshot n) (head : Execution θ route s finish) (tail : Execution θ route finish u)
      (dates : List ℝ), run = head.append tail ∧ dates.length = times.length ∧
      dates = (s.time :: times).take times.length ∧ WeakTransactions i p head dates ∧
      finish.time = times.getLastD s.time ∧
      finish.x i (.z p) = s.x i (.z p) + (3 / 5) * (times.length : ℝ) ∧
      finish.x i .b = s.x i .b := by
  induction times generalizing s u stage with
  | nil => exact ⟨s, .nil _, run, [], rfl, rfl, rfl, .nil _, rfl,
      by simp, rfl⟩
  | cons date times ih =>
    have nextList : run.cellDeliveries i =
        ⟨i, p, date⟩ :: (times ++ future).map (fun t => ⟨i, p, t⟩) := calendar
    obtain ⟨cut⟩ := run.first_cell_delivery i _ _ nextList
    have step : stage ≤ 2 := by simp only [List.length_cons] at stageBound; omega
    have threshold := (own_birth_weak_gain_bounds (initial := Real.log (3 / 10) + 1 / 100000)
      (stage := stage) (current := Real.log (3 / 10) + 1 / 100000 + (3 / 5) * (stage : ℝ))
      le_rfl step rfl).2.2
    have low : s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000 := by linarith
    have gap := (List.pairwise_cons.mp spacing).1 date (by simp)
    obtain ⟨pulse⟩ := cut.span.silent_pulse_of_invariant box physical valid i p ready low active other
      cut.no_arrivals_before (by rw [cut.date.1]; exact gap)
    have afterReady : ReadyCoordinates cut.afterArrival i := by
      refine ⟨?_, ?_, ?_⟩
      · rw [cut.modes_after.1]; exact pulse.coordinates.ready
      · rw [cut.entry.physical_continuous]; exact pulse.coordinates.charge
      · rw [cut.modes_after.2, cut.entry.physical_continuous]; exact pulse.coordinates.auxiliary
    have afterGain : cut.afterArrival.x i (.z p) ≤
        Real.log (3 / 10) + (3 / 5) * ((stage + 1 : Nat) : ℝ) + 1 / 100000 := by
      rw [cut.entry.physical_continuous, pulse.gain_target, Nat.cast_add, Nat.cast_one]
      linarith
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    obtain ⟨finish, head, tail, dates, split, count, word, certified, endpoint, gains, recovery⟩ :=
      ih (stage + 1) cut.rest (advanced.physical_invariant box physical) (advanced.raw_valid valid)
        afterReady (by simp only [List.length_cons] at stageBound; omega) afterGain
        cut.raw_after (fun q ne => by rw [cut.raw_other i q (Or.inr ne)]; exact pulse.raw_finished q)
        cut.later (by rw [cut.date.2]; exact (List.pairwise_cons.mp spacing).2)
    let combined := cut.span.append (.cons (.jump cut.entry) head)
    let boundary : CellDeliveryStep combined i ⟨i, p, date⟩ (head.cellDeliveries i) :=
      { beforeArrival := cut.beforeArrival
        afterArrival := cut.afterArrival
        span := cut.span
        entry := cut.entry
        rest := head
        reconstruct := rfl
        no_earlier := cut.no_earlier
        delivery := cut.delivery
        cell := rfl
        later := rfl }
    refine ⟨finish, combined, tail, s.time :: dates, ?_, by simp [count], ?_,
      .cons boundary active ready pulse certified, ?_, ?_, ?_⟩
    · rw [cut.reconstruct, split]
      simp only [combined, Execution.append_assoc, Execution.append]
    · simp only [word, List.length_cons, List.take_succ_cons, cut.date.2]
    · rw [endpoint, cut.date.2]
      cases times <;> rfl
    · rw [gains, cut.entry.physical_continuous, pulse.gain_target, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    · rw [recovery, cut.entry.physical_continuous, pulse.recovery_preserved]


/-- The three pre-birth weak inputs of the retained native construction,
with the starting delivery at zero and a boundary at the strong input. -/
theorem birth_weak_rows {θ route born ε} (w : BirthWeakPrefix θ route born)
    (box : PhysicalBox θ ε) (aux : ∀ p, born.aux 0 p = .ready) :
    ∃ first : BirthInput w.execution 0 0 3,
      ∃ (cut : Snapshot 1) (head : Execution θ route first.cut.afterArrival cut)
        (tail : Execution θ route cut w.final),
        first.cut.rest = head.append tail ∧ WeakTransactions 0 0 head [0, 8, 16] ∧
          cut.time = 24 := by
  obtain ⟨first⟩ := w.execution.birth_input w.birth 0 0 3 aux w.deliveries
  have prefixPhysical : PhysicalInvariant θ first.cut.afterArrival :=
    (first.cut.span.append (.cons (.jump first.cut.entry) (.nil _))).physical_invariant box
      (w.birth.physical_invariant box)
  have prefixValid : RawValid first.cut.afterArrival :=
    (first.cut.span.append (.cons (.jump first.cut.entry) (.nil _))).raw_valid w.birth.raw_valid
  have gain : first.cut.afterArrival.x 0 (.z 0) ≤
      Real.log (3 / 10) + (3 / 5) * ((0 : Nat) : ℝ) + 1 / 100000 := by
    rw [first.gain_preserved]
    simpa [nominalGain] using ((w.birth.2.2 0).2.2.2.2 (0 : Port)).1.2
  have calendar : first.cut.rest.cellDeliveries 0 = ([8, 16, 24] ++ ([] : List ℝ)).map
      (fun date => (⟨0, 0, date⟩ : Delivery 1)) := by
    simp [Execution.cellDeliveries, first.cut.later, sourceTrain, List.ofFn_succ]
    norm_num
  have spacing : (first.cut.afterArrival.time :: ([8, 16, 24] ++ ([] : List ℝ))).Pairwise
      (fun a b => a + 15 / 2 ≤ b) := by
    rw [first.date]
    norm_num [List.pairwise_cons]
  obtain ⟨finish, head, tail, dates, shape, _, word, cert, endpoint, _, _⟩ :=
    weak_transactions box 0 0 [8, 16, 24] [] 0 first.cut.rest prefixPhysical prefixValid
      first.coordinates (by decide) gain first.raw_active first.raw_other calendar spacing
  have exactWord : dates = [0, 8, 16] := by simpa [first.date] using word
  exact ⟨first, finish, head, tail, shape, exactWord ▸ cert, by simpa using endpoint⟩


/-- The B source warm-up has three individually certified writes and
keeps the native boundary at its next source, due at 344. -/
theorem feedback_weak_rows {θ route start ε} (w : FeedbackWeakEntry θ route start)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ start) (valid : RawValid start)
    (resting : start.x 1 .q = 1 / 10) (raw : ∀ p, start.raw 1 p = none)
    (gain : start.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    ∃ first : CellDeliveryStep w.execution 1 ⟨1, 2, 320⟩
        ([328, 336, 344].map (fun date => ⟨1, 2, date⟩)),
      ∃ (cut : Snapshot 2) (head : Execution θ route first.afterArrival cut)
        (tail : Execution θ route cut w.final),
        first.rest = head.append tail ∧ WeakTransactions 1 2 head [320, 328, 336] ∧
          cut.time = 344 := by
  have calendar : w.execution.cellDeliveries 1 =
      ⟨1, 2, 320⟩ :: [328, 336, 344].map (fun date => ⟨1, 2, date⟩) := by
    simp [Execution.cellDeliveries, w.deliveries, sourceTrain, List.ofFn_succ]
    norm_num
  obtain ⟨first⟩ := w.execution.first_cell_delivery 1 _ _ calendar
  obtain ⟨idle⟩ := first.span.idle_prepared 1 (w.initial_prepared 1) resting raw first.no_arrivals_before
  let through := first.span.append (.cons (.jump first.entry) (.nil _))
  have activeGain : first.afterArrival.x 1 (.z 2) ≤
      Real.log (3 / 10) + (3 / 5) * ((0 : Nat) : ℝ) + 1 / 100000 := by
    rw [first.entry.physical_continuous, idle.gain_preserved]
    simpa using gain
  obtain ⟨finish, head, tail, dates, shape, _, word, cert, endpoint, _, _⟩ :=
    weak_transactions box 1 2 [328, 336, 344] [] 0 first.rest
      (through.physical_invariant box physical) (through.raw_valid valid)
      (first.prepared idle.prepared).ready_coordinates (by decide) activeGain first.raw_after
      (fun q ne => by
        rw [first.raw_other 1 q (Or.inr ne)]
        exact (first.span.raw_absent_of_no_arrival 1 q (raw q) (first.no_arrivals_before q)).1)
      first.later (by rw [first.date.2]; norm_num [List.pairwise_cons])
  have exactWord : dates = [320, 328, 336] := by simpa [first.date.2] using word
  exact ⟨first, finish, head, tail, shape, exactWord ▸ cert, by simpa using endpoint⟩


/-- Local evidence for the first B reception, on the very weak cut used
in the interleaved reciprocal construction. -/
theorem first_forward_weak_row {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} (p : FirstInterleavedPair r)
    (box : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (delay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    r.final.time = r.fire.final.time + forward r.fire.final.time ∧
      r.receiverLocal.main 0 = .ready ∧
      p.receiver.cut168.cut.ledger.emissions = [] ∧
      p.receiver.cut168.cut.ledger.error 0 1 = 3 / 5 ∧
      p.final.x 1 (.z 1) = r.final.x 1 (.z 1) + 3 / 5 ∧
      p.final.x 1 .b = r.final.x 1 .b ∧
      p.receiver.cut168.state.pending = r.receiverLocal.pending := by
  refine ⟨r.date, (r.receiver_local_ready 0).ready, p.receiver.cut_emissions,
    p.receiver.cut_error_dose box delay, ?_, ?_, p.receiver.cut_pending⟩
  · rw [p.b_values]
    exact p.receiver.cut_gain_target box delay
  · rw [p.b_values]
    exact p.receiver.cut_recovery

/-- The first A receipt of the reverse epoch gives one dose while B
continues to its next external source. -/
theorem first_reverse_weak_row {θ routeStart forward backward ε}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) routeStart}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) (box : PhysicalBox θ ε)
    (low : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    r.final.time = f.final.time + backward f.final.time ∧ r.final.main 0 = .ready ∧
      p.receiver.cut352.cut.ledger.emissions = [] ∧
      p.receiver.cut352.cut.ledger.error 0 2 = 3 / 5 ∧
      p.final.x 0 (.z 2) = r.final.x 0 (.z 2) + 3 / 5 ∧
      p.final.x 0 .b = r.final.x 0 .b ∧
      p.final.time = 352 := by
  exact ⟨r.date, r.a_prepared.ready, p.receiver.cut_emissions,
    (p.receiver.cut_error_and_gain box low).1, p.a_gain_target box low, p.a_recovery, p.date⟩


/-- The native source at 32 is the protected A MARK. The gain and the
queue are unchanged on this exact span. -/
theorem birth_protected_row {θ born} (c : BirthProtectedMark θ born) :
    c.arrival.final.time = 32 ∧ c.arrival.final.main 0 = .slow ∧
      c.markTrace.ledger.emissions = [] ∧
      c.final.pending = c.arrival.final.pending ∧
      (∀ port, c.final.x 0 (.z port) = c.arrival.final.x 0 (.z port)) ∧
      c.final.x 0 .b = c.arrival.final.x 0 .b + 1 / 10 := by
  exact ⟨c.arrival.date, c.arrival.main_slow,
    by rw [c.markTrace_ledger]; exact c.mark.emissions, c.mark.pending, c.mark.gain_preserved,
    c.mark.recovery_gain⟩

/-- At the reciprocal source 344 the native guard fires. This is the
carried-charge firing, with its actual issued contact in the queue. -/
theorem feedback_strong_row {θ start forward backward}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    (f : FeedbackFirstFire w) :
    w.final.time = 344 ∧ w.final.main 1 = .ready ∧
      f.execution.ledger.emissions = [(1, f.final.time)] ∧
      f.final.pending = w.final.pending ++ [⟨0, 2, f.final.time + backward f.final.time⟩] ∧
      (∀ i port, f.final.x i (.z port) = w.final.x i (.z port)) ∧
      (∀ i, f.final.x i .b = w.final.x i .b) := by
  exact ⟨w.date, (w.prepared 1).ready, f.emissions, f.pending, f.gains, f.recovery⟩


/-- The first three external A probes of the forward epoch issue the
first three B contacts at their exact native FIRE dates. -/
theorem forward_sender_entry_rows {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {p : FirstInterleavedPair r} {v : SecondWiredArrival p}
    {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
    (t : ThirdWiredArrival u) :
    b.final.time = 160 ∧ p.final.time = 168 ∧ u.final.time = 176 ∧
    b.final.main 0 = .ready ∧ p.final.main 0 = .ready ∧ u.final.main 0 = .ready ∧
    r.fire.execution.ledger.emissions = [(0, r.fire.final.time)] ∧
    v.fire.execution.ledger.emissions = [(0, v.fire.final.time)] ∧
    t.fire.execution.ledger.emissions = [(0, t.fire.final.time)] ∧
    r.fire.final.pending = b.final.pending ++ [⟨1, 1, r.fire.final.time + forward r.fire.final.time⟩] ∧
    v.fire.final.pending = p.final.pending ++ [⟨1, 1, v.fire.final.time + forward v.fire.final.time⟩] ∧
    t.fire.final.pending = u.final.pending ++ [⟨1, 1, t.fire.final.time + forward t.fire.final.time⟩] ∧
    (∀ port, r.fire.final.x 0 (.z port) = b.final.x 0 (.z port) ∧
      v.fire.final.x 0 (.z port) = p.final.x 0 (.z port) ∧
      t.fire.final.x 0 (.z port) = u.final.x 0 (.z port)) ∧
    r.fire.final.x 0 .b = b.final.x 0 .b ∧
    v.fire.final.x 0 .b = p.final.x 0 .b ∧
    t.fire.final.x 0 .b = u.final.x 0 .b := by
  refine ⟨b.date, p.date, u.date, b.a_prepared.ready, p.a_prepared.ready, u.a_prepared.ready,
    r.fire.emissions, v.fire.emissions, t.fire.emissions, ?_, ?_, ?_,
    fun port => ⟨r.fire.gains 0 port, v.fire.gains 0 port, t.fire.gains 0 port⟩,
    r.fire.recovery 0, v.fire.recovery 0, t.fire.recovery 0⟩
  · rw [r.fire.pending, r.fire.protocol_route, b.pending]
    rfl
  · rw [v.fire.pending, v.fire.protocol_route, p.pending]
  · rw [t.fire.pending, t.fire.protocol_route, u.pending]

end NetworkStability.NativeReciprocal
