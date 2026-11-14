import NativeWireTransactions

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid

private theorem source_spacing (first : ℝ) (count : Nat) :
    (first :: List.ofFn (fun k : Fin count => first + 8 + 8 * (k.val : ℝ))).Pairwise
      (fun a b => a + 15 / 2 ≤ b) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro b mem
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp mem
    linarith [Nat.cast_nonneg (α := ℝ) k.val]
  · apply List.pairwise_ofFn.mpr
    intro k l less
    have h : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr less)
    linarith

/-- The eleven prepared A sources before birth use the same native
transaction certificate, with no routed descendants. -/
theorem birth_sender_transactions {θ born ε} (c : ConstructedBirthPreparation θ born)
    (box : PhysicalBox θ ε) :
    ∃ word, word.length = 11 ∧ PreparedTransactions 0 0 c.suffix word := by
  let times := List.ofFn (fun k : Fin 10 => c.at40.final.time + 8 + 8 * (k.val : ℝ))
  have gain : 9 / 5 ≤ Real.exp (c.at40.final.x 0 (.z 0)) ∧
      Real.exp (c.at40.final.x 0 (.z 0)) ≤ 12 / 5 := by
    have birth := ((c.at40.mark.first.weak.birth.2.2 0).2.2.2.2 (0 : Port)).1
    simp only [nominalGain, show (0 : Port) ≠ 1 by decide, ite_false] at birth
    have trained := learned_gain_bounds (z := c.at40.final.x 0 (.z 0))
      (by rw [c.at40.gain_target]; linarith [birth.1])
      (by rw [c.at40.gain_target]; linarith [birth.2])
    exact ⟨trained.1, by linarith [trained.2]⟩
  obtain ⟨word, dates, certified⟩ := prepared_transactions box 0 0 times c.suffix
    c.at40.physical.region c.at40.raw_valid c.at40.prepared gain
    (by rw [c.at40.date]; exact c.at40.raw_active) c.at40.raw_other
    (by
      simpa only [times, c.at40.date, sourceTrain, List.map_ofFn, Function.comp_def,
        show (40 : ℝ) + 8 = 48 by norm_num] using
        (show c.suffix.cellDeliveries 0 = sourceTrain 0 0 48 8 10 by
          simp [Execution.cellDeliveries, c.deliveries_suffix, sourceTrain]))
    (source_spacing _ _) (by
      intro date mem
      rw [c.date]
      rcases List.mem_cons.mp mem with rfl | later
      · rw [c.at40.date]
        norm_num
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp later
        have last : (k.val : ℝ) ≤ 9 := by exact_mod_cast (show k.val ≤ 9 by omega)
        change c.at40.final.time + 8 + 8 * (k.val : ℝ) + 15 / 2 ≤ 128
        rw [c.at40.date]
        linarith)
  have length := congrArg List.length dates
  simp [times] at length
  exact ⟨word, length, certified⟩

/-- Certify the forward sender on the particular coupled train supplied
by the native construction, so it can be composed with other witnesses. -/
theorem forward_sender_transactions {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {v : SecondWiredArrival s}
    {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
    {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t}
    (z : FirstCoupledTeaching x) (box : @PhysicalBox 2 (extendParameters θ fresh) ε) :
    ∃ word, word.length = 13 ∧ PreparedTransactions 0 0 z.train.execution word := by
  let times := List.ofFn (fun k : Fin 12 => x.final.time + 8 + 8 * (k.val : ℝ))
  have hdate : z.train.final.time = (288 : ℝ) := by rw [z.train.date, x.date]; norm_num
  have hz := x.learned_gain_a box.extend_old
  obtain ⟨word, dates, evidence⟩ := prepared_transactions box 0 0 times z.train.execution
    x.physical.region x.raw_valid (x.prepared 0) ⟨hz.1, by linarith [hz.2]⟩
    (by rw [x.date]; exact x.raw_active) (fun q h => x.raw_other 0 q (Or.inr h))
    (by simpa only [times, sourceTrain, List.map_ofFn, Function.comp_def] using z.train.a_deliveries)
    (source_spacing _ _) (by
      intro t mem
      rcases List.mem_cons.mp mem with rfl | inside
      · rw [x.date, hdate]
        norm_num
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp inside
        have kBound : (k.val : ℝ) ≤ 11 := by exact_mod_cast (show k.val ≤ 11 by omega)
        change x.final.time + 8 + 8 * (k.val : ℝ) + 15 / 2 ≤ z.train.final.time
        rw [x.date, hdate]
        linarith)
  have length := congrArg List.length dates
  simp [times] at length
  exact ⟨word, length, evidence⟩

private theorem prepared_cast_parameters {n θ θ' route s u i p word}
    {e : @Execution n θ route s u} (equal : θ = θ')
    (prepared : PreparedTransactions i p e word) :
    PreparedTransactions i p (e.cast_parameters equal) word := by
  cases equal
  exact prepared

/-- Certify the reverse sender on the particular completion supplied
by the same native construction. -/
theorem reverse_sender_transactions {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {a : FeedbackFirstFire w} {q : FirstReverseWiredArrival a}
    {p : FirstReverseInterleavedPair q} (entry : ReverseEntryCompletion p)
    (epoch : ReverseLearnedEpoch a.parametersA a.parametersB forward backward entry.final)
    (physical : PhysicalBox θ ε)
    (hGB : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2) :
    ∃ word, word.length = 9 ∧
      PreparedTransactions 1 2 (epoch.execution.cast_parameters a.parameters_product) word := by
  let s := entry.final
  let run := epoch.execution
  let times := List.ofFn (fun k : Fin 8 => s.time + 8 + 8 * (k.val : ℝ))
  have box : PhysicalBox (extendParameters a.parametersA (a.parametersB 0)) ε := by
    rw [a.parameters_product]
    exact physical
  have region : UpperRegion s := entry.physical.region
  have gain : 9 / 5 ≤ Real.exp (s.x 1 (.z 2)) ∧ Real.exp (s.x 1 (.z 2)) ≤ 12 / 5 := by
    change 9 / 5 ≤ Real.exp (entry.final.x 1 (.z 2)) ∧ _
    rw [entry.b_gains, p.b_gains]
    exact ⟨hGB.1, by linarith [hGB.2]⟩
  obtain ⟨word, dates, evidence⟩ := prepared_transactions box 1 2 times run region
    entry.raw_valid (entry.prepared 1) gain entry.raw_active
    (fun port h => entry.raw_other 1 port (Or.inr h))
    (by
      change epoch.execution.cellDeliveries 1 = _
      rw [epoch.b_deliveries]
      simp only [times, s, entry.date, sourceTrain, List.map_ofFn, Function.comp_def]
      norm_num)
    (source_spacing _ _) (by
      intro t mem
      rcases List.mem_cons.mp mem with rfl | inside
      · change entry.final.time + 15 / 2 ≤ epoch.final.time
        rw [entry.date, epoch.date]
        norm_num
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp inside
        have kBound : (k.val : ℝ) ≤ 7 := by exact_mod_cast (show k.val ≤ 7 by omega)
        change entry.final.time + 8 + 8 * (k.val : ℝ) + 15 / 2 ≤ epoch.final.time
        rw [entry.date, epoch.date]
        linarith)
  have length := congrArg List.length dates
  simp [times] at length
  exact ⟨word, length, prepared_cast_parameters a.parameters_product evidence⟩

set_option maxHeartbeats 2000000 in
/-- The protected receipt and all five prepared trains are cuts of one
staged native history complete through the reciprocal horizon. The
nonprepared blocks remain explicit native executions. -/
theorem nominal_composed_cuts :
    ∃ last : Snapshot 2, ∃ staged : NominalStaged last, CompleteThrough staged.after (4599 / 10) ∧
      Nonempty (ProtectedReceipt staged) ∧
      ∃ (v w y x : Snapshot 2)
        (first : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
          (reciprocalEntryRouter nominalDelay nominalDelay) staged.afterBirth v)
        (forwardRun : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
          (reciprocalEntryRouter nominalDelay nominalDelay) v w)
        (quiet : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
          (reciprocalEntryRouter nominalDelay nominalDelay) w y)
        (middle : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
          (reciprocalEntryRouter nominalDelay nominalDelay) y x)
        (reverseRun : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
          (reciprocalEntryRouter nominalDelay nominalDelay) x last)
        (forward reverse : List (ℝ × ℝ)),
        staged.after = (first.append forwardRun).append (quiet.append (middle.append reverseRun)) ∧
        forward.length = 13 ∧ PreparedTransactions 0 0 forwardRun forward ∧
        reverse.length = 9 ∧ PreparedTransactions 1 2 reverseRun reverse ∧
        last.pending = sourceTrain 1 2 480 8 16 ∧
        (∃ (start past : Snapshot 1)
          (initial : Execution KernelR.FutureControls.parameters (fun _ _ => []) nominalStart start)
          (prepared : Execution KernelR.FutureControls.parameters (fun _ _ => []) start past)
          (wait : Execution KernelR.FutureControls.parameters (fun _ _ => []) past staged.beforeBirth)
          (word : List (ℝ × ℝ)),
          staged.before = (initial.append prepared).append wait ∧ word.length = 11 ∧
            PreparedTransactions 0 0 prepared word) ∧
        ∃ (fstart rstart : Snapshot 2)
          (fhead : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
            (reciprocalEntryRouter nominalDelay nominalDelay) v fstart)
          (rhead : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
            (reciprocalEntryRouter nominalDelay nominalDelay) x rstart)
          (fcut : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
            (reciprocalEntryRouter nominalDelay nominalDelay) fstart y)
          (rcut : Execution (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
            (reciprocalEntryRouter nominalDelay nominalDelay) rstart last)
          (forwardFire reverseFire : List (ℝ × ℝ)),
          forwardRun.append quiet = fhead.append fcut ∧ reverseRun = rhead.append rcut ∧
          forwardFire.length = 13 ∧ reverseFire.length = 9 ∧
          PreparedTransactions 1 1 fcut forwardFire ∧ PreparedTransactions 0 2 rcut reverseFire ∧
          (forwardRun.append quiet).emissionTimes 1 = forwardFire.map Prod.snd ∧
          reverseRun.emissionTimes 0 = reverseFire.map Prod.snd := by
  have born : BirthState nominalStart := Newborn.nominal_birth_state
  have delay : ∀ t, (3 / 10 : ℝ) ≤ nominalDelay t ∧ nominalDelay t ≤ 2 / 5 := by
    intro t
    norm_num [nominalDelay]
  obtain ⟨c, b, _, _, v, f, g, u, t, x, z, w, a, q, p, _, _, _, _, _, _⟩ :=
    birth_protocol_first_reverse_interleaved_pair_exists (born := nominalStart) born nominal_box
      (fun _ => rfl) rfl Newborn.nominal nominalDelay nominalDelay delay delay
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
  obtain ⟨entry⟩ := reverse_entry_completion_exists p nominal_box hzA hGB delay
  have params : PhysicalBox (extendParameters a.parametersA (a.parametersB 0)) (1 / 10) := by
    rw [a.parameters_product]
    exact nominal_box
  have physical : PhysicalInvariant (extendParameters a.parametersA (a.parametersB 0)) entry.final := by
    rw [a.parameters_product]
    exact entry.physical
  have hGA : 9 / 5 ≤ Real.exp (entry.final.x 0 (.z 2)) ∧ Real.exp (entry.final.x 0 (.z 2)) ≤ 2 := by
    have memory : entry.final.x 0 (.z 2) = q.final.x 0 (.z 2) + 9 / 5 := by
      rw [entry.a_gain_target, p.a_gain_target nominal_box hzA.2]
      ring
    exact learned_gain_bounds (by rw [memory]; linarith [hzA.1]) (by rw [memory]; linarith [hzA.2])
  have hGB' : 9 / 5 ≤ Real.exp (entry.final.x 1 (.z 2)) ∧ Real.exp (entry.final.x 1 (.z 2)) ≤ 2 := by
    rw [entry.b_gains, p.b_gains]
    exact hGB
  obtain ⟨epoch⟩ := reverse_learned_epoch_exists params entry.final physical entry.raw_valid entry.date
    entry.prepared entry.charge hGA hGB' entry.raw_active entry.raw_other entry.pending
    nominalDelay nominalDelay delay
  let reverseRun := epoch.execution.cast_parameters a.parameters_product
  let finish := entry.execution.append reverseRun
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
      same_gain := by rw [t.receiver_gain_target nominal_box delay,
        v.receiver_gain_target nominal_box delay]
      same_recovery := t.receiver_recovery.trans v.receiver_recovery.symm
      mark_gain := x.b_recovery_gain
      gain_preserved := x.gains 1
      completed_ready := (x.prepared 1).ready
      completed_raw := x.raw_receiver
      fires_after_arrival := by linarith [f.early]
      receipt_after_fire := by linarith [f.deadline, (t.received_gap delay).1]
      arrival_gap := by linarith [(t.received_gap delay).1]
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
    (q.execution.append (p.execution.append finish))))
  let staged : NominalStaged epoch.final :=
    { x.staged with after := x.staged.after.append remainder }
  have complete : CompleteThrough staged.after (4599 / 10) := epoch.complete
  obtain ⟨forward, countF, certF⟩ := forward_sender_transactions z nominal_box
  obtain ⟨backward, countR, certR⟩ := reverse_sender_transactions entry epoch nominal_box hGB
  obtain ⟨_, fhead, fcut, forwardFire, fsplit, fcount, fcert, fword⟩ := forward_receiver_transactions z nominal_box delay
  obtain ⟨_, rhead, rcut, reverseFire, rsplit, rcount, rcert, rword⟩ := reverse_receiver_transactions entry epoch params
    ⟨hGB'.1, by linarith [hGB'.2]⟩ ⟨hGA.1, by linarith [hGA.2]⟩
  let middle := w.execution.append (a.execution.append
    (q.execution.append (p.execution.append entry.execution)))
  have split : staged.after = (x.staged.after.append z.train.execution).append
      (z.wait.append (middle.append reverseRun)) := by
    change x.staged.after.append remainder = _
    simp only [remainder, FirstCoupledTeaching.execution, middle, finish, Execution.append_assoc]
  obtain ⟨birthWord, birthCount, birthCert⟩ := birth_sender_transactions c nominal_box.extend_old
  have before : staged.before = (c.at40.execution.append c.suffix).append b.wait := rfl
  refine ⟨_, staged, complete, ⟨localCut.append remainder⟩, _, _, _, _, _, _, _, _, _, _, _, split,
    countF, certF, countR, certR, epoch.pending, ⟨_, _, _, _, _, birthWord, before, birthCount, birthCert⟩,
    _, _, fhead, rhead.cast_parameters a.parameters_product,
    fcut, rcut.cast_parameters a.parameters_product, forwardFire, reverseFire, fsplit, ?_,
    fcount, rcount, fcert, prepared_cast_parameters a.parameters_product rcert, fword, ?_⟩
  · have castAppend {n θ θ' route s v u} (a : @Execution n θ route s v) (b : Execution θ route v u)
        (equal : θ = θ') :
        (a.append b).cast_parameters equal = (a.cast_parameters equal).append (b.cast_parameters equal) := by
      cases equal
      rfl
    change epoch.execution.cast_parameters _ = _
    rw [rsplit, castAppend]
  · simpa only [reverseRun, Execution.emissionTimes, Execution.cast_parameters_ledger] using rword

end NetworkStability.NativeReciprocal
