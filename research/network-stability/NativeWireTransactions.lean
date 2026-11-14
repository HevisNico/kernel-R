import NativeTiming
import KernelR.HybridFeedbackCalendar

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid

/-- Cut the actual receiving execution at its first derived wire date.
Before that arrival, the receiver stays prepared by the idle equations. -/
theorem prepared_wire_transactions {n θ ε route s u} (box : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (e : Execution θ route s u) (first : ℝ) (times : List ℝ)
    (region : UpperRegion s) (valid : RawValid s) (prepared : PreparedSection s i)
    (resting : s.x i .q = 1 / 10) (raw : ∀ q, s.raw i q = none)
    (gain : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (calendar : e.cellDeliveries i = (first :: times).map (fun t => ⟨i, p, t⟩))
    (spacing : (first :: times).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (horizon : ∀ t ∈ first :: times, t + 15 / 2 ≤ u.time) :
    ∃ cut : CellDeliveryStep e i ⟨i, p, first⟩ (times.map (fun t => ⟨i, p, t⟩)),
      ∃ word, word.map Prod.fst = first :: times ∧
        PreparedTransactions i p cut.rest word ∧ e.emissionTimes i = word.map Prod.snd := by
  obtain ⟨cut⟩ := e.first_cell_delivery i ⟨i, p, first⟩ _ (by simpa using calendar)
  obtain ⟨idle⟩ := cut.span.idle_prepared i prepared resting raw cut.no_arrivals_before
  have afterGain : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
      Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by
    rw [cut.entry.physical_continuous, idle.gain_preserved]
    exact gain
  let head := cut.span.append (.cons (.jump cut.entry) (.nil _))
  obtain ⟨word, dates, evidence⟩ := prepared_transactions box i p times cut.rest
    (head.upper_region box region) (head.raw_valid valid) (cut.prepared idle.prepared)
    afterGain cut.raw_after (fun q h => by rw [cut.raw_other i q (Or.inr h)]; exact
      (cut.span.raw_absent_of_no_arrival i q (raw q) (cut.no_arrivals_before q)).1)
    cut.later (by rw [cut.date.2]; exact spacing) (by rw [cut.date.2]; exact horizon)
  refine ⟨cut, word, ?_, evidence, ?_⟩
  · simpa only [cut.date.2] using dates
  · rw [cut.emissions, idle.emissions, List.nil_append, evidence.fire_word]

private theorem mapped_spacing {times : List ℝ} (space : times.Pairwise (fun a b => a + 15 / 2 ≤ b))
    (offset : ℝ) : (times.map (· + offset)).Pairwise (fun a b => a + 15 / 2 ≤ b) := by
  apply List.pairwise_map.mpr
  exact space.imp (fun h => by linarith)

/-- Certify the B side of the forward learned block from the periodic A
source and fixed wire delay. The quiet continuation provides the horizon
for the final receiver, which arrives later than its associated A source. -/
theorem forward_receiver_transactions {θ born fresh ε newborn}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter nominalDelay nominalDelay)
      constructedBBirthSources}
    {r : FirstWiredArrival b} {a : FirstInterleavedPair r} {v : SecondWiredArrival a}
    {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
    {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t}
    (z : FirstCoupledTeaching x) (box : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (delay : ∀ time, (3 / 10 : ℝ) ≤ nominalDelay time ∧ nominalDelay time ≤ 2 / 5) :
    ∃ (start : Snapshot 2) (head : Execution (extendParameters θ fresh)
      (reciprocalEntryRouter nominalDelay nominalDelay) x.final start)
      (run : Execution (extendParameters θ fresh)
      (reciprocalEntryRouter nominalDelay nominalDelay) start z.final) (word : List (ℝ × ℝ)),
      z.execution = head.append run ∧ word.length = 13 ∧ PreparedTransactions 1 1 run word ∧
        z.execution.emissionTimes 1 = word.map Prod.snd := by
  let times := List.ofFn (fun k : Fin 12 => x.final.time + 8 + 8 * (k.val : ℝ))
  let contact := teachingContact nominalDelay
  have bound : ∀ t ∈ x.final.time :: times, 184 ≤ t ∧ t ≤ 280 := by
    intro date mem
    rcases List.mem_cons.mp mem with rfl | later
    · rw [x.date]; norm_num
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp later
      have nonnegative : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
      have last : (j.val : ℝ) ≤ 11 := by exact_mod_cast (show j.val ≤ 11 by omega)
      change 184 ≤ x.final.time + 8 + 8 * (j.val : ℝ) ∧
        x.final.time + 8 + 8 * (j.val : ℝ) ≤ 280
      rw [x.date]
      constructor <;> linarith
  have senderGain : 9 / 5 ≤ Real.exp (x.final.x 0 (.z 0)) ∧
      Real.exp (x.final.x 0 (.z 0)) ≤ 12 / 5 := by
    have gain := x.learned_gain_a box.extend_old
    exact ⟨gain.1, by linarith [gain.2]⟩
  have receiverGain : 9 / 5 ≤ Real.exp (x.final.x 1 (.z 1)) ∧
      Real.exp (x.final.x 1 (.z 1)) ≤ 12 / 5 := by
    have gain := x.learned_gain_b box delay
    exact ⟨gain.1, by linarith [gain.2]⟩
  have spacing : (x.final.time :: times).Pairwise (fun a b => a + 15 / 2 ≤ b) := by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_ofFn.mpr ?_⟩
    · intro y mem
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp mem
      linarith [Nat.cast_nonneg (α := ℝ) j.val]
    · intro j k earlier
      have gap : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast (Nat.add_one_le_iff.mpr earlier)
      linarith
  have source : z.execution.cellDeliveries 0 = times.map (fun t => ⟨0, 0, t⟩) := by
    simpa only [times, x.date, sourceTrain, List.map_ofFn, Function.comp_def,
      show (184 : ℝ) + 8 = 192 by norm_num] using z.a_deliveries
  have future : PendingFuture z.final := fun token mem => z.complete.1 ▸ (z.complete.2.2 token mem).le
  have noExternal : ∀ token ∈ x.final.pending, token.cell = contact.target → z.final.time < token.due := by
    intro token mem dest
    rw [x.learned_train_pending] at mem
    rcases List.mem_append.mp mem with source | later
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp source
      simp [contact, teachingContact] at dest
    · rw [z.date]
      rcases List.mem_append.mp later with sources | sources
      all_goals
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp sources
        dsimp
        linarith [Nat.cast_nonneg (α := ℝ) j.val]
  have route : ∀ event ∈ z.execution.ledger.emissions,
      ((reciprocalEntryRouter nominalDelay nominalDelay) event.1 event.2).filter
        (fun token => token.cell = contact.target) = contact.route event.1 event.2 := by
    intro event mem
    have time := (z.execution.emission_time_bounds event mem).2
    rw [z.date] at time
    exact reciprocalEntryRouter.to_b _ _ _ (by linarith)
  have geometry : ∀ date ∈ x.final.time :: times,
      contact.opens ≤ date + 3 / 10 ∧ date + 9 / 10 ≤ contact.closes := by
    intro date mem
    have h := bound date mem
    change 160 ≤ date + 3 / 10 ∧ date + 9 / 10 ≤ 310
    constructor <;> linarith [h.1, h.2]
  have enough : ∀ date ∈ x.final.time :: times, date + 15 / 2 ≤ z.final.time := by
    intro date mem
    rw [z.date]
    linarith [(bound date mem).2]
  have native := prepared_contact_calendar_of_valid box contact 0 times z.execution x.physical.region
    x.raw_valid (x.prepared 0) (x.charge 0) senderGain (by rw [x.date]; exact x.raw_active)
    (fun port ne => x.raw_other 0 port (Or.inr ne))
    source spacing enough future noExternal route geometry delay
  let offset := restLatency (Real.exp (x.final.x 0 (.z 0))) + 7 / 20
  let first := x.final.time + offset
  let later := times.map (· + offset)
  have calendar : z.execution.cellDeliveries 1 = (first :: later).map (fun t => ⟨1, 1, t⟩) := by
    rw [show z.execution.cellDeliveries 1 = _ from native]
    simp [contact, teachingContact, Contact.token, nominalDelay, first, later, offset, add_assoc]
  have readyGap : (first :: later).Pairwise (fun a b => a + 15 / 2 ≤ b) := mapped_spacing spacing offset
  have horizon : ∀ date ∈ first :: later, date + 15 / 2 ≤ z.final.time := by
    intro date mem
    have mapped : date ∈ (x.final.time :: times).map (· + offset) := mem
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp mapped
    have latency := (restLatency_spec senderGain).2.1
    rw [z.date]
    dsimp [offset]
    linarith [(bound source hs).2]
  obtain ⟨cut, word, dates, certified, fires⟩ := prepared_wire_transactions box 1 1 z.execution first later
    x.physical.region x.raw_valid (x.prepared 1) (x.charge 1) (fun port => x.raw_other 1 port (Or.inl (by decide)))
    receiverGain calendar readyGap horizon
  have count := congrArg List.length dates
  simp [later, times] at count
  exact ⟨_, cut.span.append (.cons (.jump cut.entry) (.nil _)), cut.rest, word,
    by simpa only [Execution.append_assoc, Execution.append] using cut.reconstruct, count, certified, fires⟩

/-- Certify the A side of the reverse learned block from the periodic B
source and the native return wire. -/
theorem reverse_receiver_transactions {θ ε forward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward nominalDelay) start}
    {a : FeedbackFirstFire w} {q : FirstReverseWiredArrival a}
    {p : FirstReverseInterleavedPair q} (entry : ReverseEntryCompletion p)
    (epoch : ReverseLearnedEpoch a.parametersA a.parametersB forward nominalDelay entry.final)
    (box : @PhysicalBox 2 (extendParameters a.parametersA (a.parametersB 0)) ε)
    (senderGain : 9 / 5 ≤ Real.exp (entry.final.x 1 (.z 2)) ∧
      Real.exp (entry.final.x 1 (.z 2)) ≤ 12 / 5)
    (receiverGain : 9 / 5 ≤ Real.exp (entry.final.x 0 (.z 2)) ∧
      Real.exp (entry.final.x 0 (.z 2)) ≤ 12 / 5) :
    ∃ (start : Snapshot 2) (head : Execution (extendParameters a.parametersA (a.parametersB 0))
      (reciprocalEntryRouter forward nominalDelay) entry.final start)
      (run : Execution (extendParameters a.parametersA (a.parametersB 0))
      (reciprocalEntryRouter forward nominalDelay) start epoch.final) (word : List (ℝ × ℝ)),
      epoch.execution = head.append run ∧ word.length = 9 ∧ PreparedTransactions 0 2 run word ∧
        epoch.execution.emissionTimes 0 = word.map Prod.snd := by
  let times := List.ofFn (fun k : Fin 8 => entry.final.time + 8 + 8 * (k.val : ℝ))
  let contact := feedbackContact nominalDelay
  have bound : ∀ t ∈ entry.final.time :: times, 376 ≤ t ∧ t ≤ 440 := by
    intro date mem
    rcases List.mem_cons.mp mem with rfl | later
    · rw [entry.date]
      norm_num
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp later
      have nonnegative : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
      have last : (j.val : ℝ) ≤ 7 := by exact_mod_cast (show j.val ≤ 7 by omega)
      change 376 ≤ entry.final.time + 8 + 8 * (j.val : ℝ) ∧
        entry.final.time + 8 + 8 * (j.val : ℝ) ≤ 440
      rw [entry.date]
      constructor <;> linarith
  have spacing : (entry.final.time :: times).Pairwise (fun a b => a + 15 / 2 ≤ b) := by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_ofFn.mpr ?_⟩
    · intro y mem
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp mem
      linarith [Nat.cast_nonneg (α := ℝ) j.val]
    · intro j k earlier
      have gap : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast (Nat.add_one_le_iff.mpr earlier)
      linarith
  have source : epoch.execution.cellDeliveries 1 = times.map (fun t => ⟨1, 2, t⟩) := by
    simpa only [times, entry.date, sourceTrain, List.map_ofFn, Function.comp_def,
      show (376 : ℝ) + 8 = 384 by norm_num] using epoch.b_deliveries
  have future : PendingFuture epoch.final := fun token mem => epoch.complete.1 ▸ (epoch.complete.2.2 token mem).le
  have noExternal : ∀ token ∈ entry.final.pending, token.cell = contact.target → epoch.final.time < token.due := by
    intro token mem dest
    rw [entry.pending] at mem
    rcases List.mem_append.mp mem with sources | later
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp sources
      simp [contact, feedbackContact] at dest
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp later
      simp [contact, feedbackContact] at dest
  have route : ∀ event ∈ epoch.execution.ledger.emissions,
      ((reciprocalEntryRouter forward nominalDelay) event.1 event.2).filter
        (fun token => token.cell = contact.target) = contact.route event.1 event.2 := by
    intro event mem
    have time := (epoch.execution.emission_time_bounds event mem).1
    rw [entry.date] at time
    exact reciprocalEntryRouter.to_a _ _ _ (by linarith)
  have geometry : ∀ date ∈ entry.final.time :: times,
      contact.opens ≤ date + 3 / 10 ∧ date + 9 / 10 ≤ contact.closes := by
    intro date mem
    have h := bound date mem
    change 320 ≤ date + 3 / 10 ∧ date + 9 / 10 ≤ 470
    constructor <;> linarith [h.1, h.2]
  have enough : ∀ date ∈ entry.final.time :: times, date + 15 / 2 ≤ epoch.final.time := by
    intro date mem
    rw [epoch.date]
    linarith [(bound date mem).2]
  have native := prepared_contact_calendar_of_valid box contact 2 times epoch.execution entry.physical.region
    entry.raw_valid (entry.prepared 1) (entry.charge 1) senderGain entry.raw_active
    (fun port ne => entry.raw_other 1 port (Or.inr ne))
    source spacing enough future noExternal route geometry (fun _ => by norm_num [contact, feedbackContact, nominalDelay])
  let offset := restLatency (Real.exp (entry.final.x 1 (.z 2))) + 7 / 20
  let first := entry.final.time + offset
  let later := times.map (· + offset)
  have calendar : epoch.execution.cellDeliveries 0 = (first :: later).map (fun t => ⟨0, 2, t⟩) := by
    rw [show epoch.execution.cellDeliveries 0 = _ from native]
    simp [contact, feedbackContact, Contact.token, nominalDelay, first, later, offset, add_assoc]
  have readyGap : (first :: later).Pairwise (fun a b => a + 15 / 2 ≤ b) := mapped_spacing spacing offset
  have horizon : ∀ date ∈ first :: later, date + 15 / 2 ≤ epoch.final.time := by
    intro date mem
    have mapped : date ∈ (entry.final.time :: times).map (· + offset) := mem
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp mapped
    have latency := (restLatency_spec senderGain).2.1
    rw [epoch.date]
    dsimp [offset]
    linarith [(bound source hs).2]
  obtain ⟨cut, word, dates, certified, fires⟩ := prepared_wire_transactions box 0 2 epoch.execution first later
    entry.physical.region entry.raw_valid (entry.prepared 0) (entry.charge 0)
    (fun port => entry.raw_other 0 port (Or.inl (by decide)))
    receiverGain calendar readyGap horizon
  have count := congrArg List.length dates
  simp [later, times] at count
  exact ⟨_, cut.span.append (.cons (.jump cut.entry) (.nil _)), cut.rest, word,
    by simpa only [Execution.append_assoc, Execution.append] using cut.reconstruct, count, certified, fires⟩


end NetworkStability.NativeReciprocal
