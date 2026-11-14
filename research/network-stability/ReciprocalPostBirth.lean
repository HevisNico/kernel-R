import ReciprocalReplay

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid
open PhaseAdmission
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

private abbrev Row := ReciprocalTransaction

noncomputable def firingRows (i : Fin 2) (port : Port) (word : List (ℝ × ℝ)) : List Row :=
  word.map (fun clocks => reciprocalRow ⟨clocks.1, i, port⟩ (some clocks.2))

theorem firingRows_fires (i : Fin 2) (port : Port) (word : List (ℝ × ℝ)) :
    Transaction.fires Prod.fst (firingRows i port word) = word.map (fun clocks => (i, clocks.2)) := by
  simp [firingRows, Transaction.fires, reciprocalRow, List.filterMap_map]

theorem firingRows_clocks {θ route s u i port word}
    {run : @Execution 2 θ route s u} (cert : PreparedTransactions i port run word) :
    ∀ row ∈ firingRows i port word, ∀ t ∈ row.fireDate, row.probe.due ≤ t ∧ t < row.probe.due + 1 := by
  intro row mem t fire
  obtain ⟨clocks, seen, rfl⟩ := List.mem_map.mp mem
  have eq : clocks.2 = t := by simpa [reciprocalRow] using fire
  subst t
  exact cert.clock_bounds clocks seen

theorem firingRows_admissions {θ route s u i port word}
    {run : @Execution 2 θ route s u} (cert : PreparedTransactions i port run word)
    (ports : ∀ token ∈ run.cellDeliveries i, token.port = port) :
    (firingRows i port word).map Transaction.probe =
      ⟨s.time, i, port⟩ :: (run.cellDeliveries i).map reciprocalOccurrence := by
  have dates := congrArg (List.map (fun date => (⟨date, i, port⟩ : ReciprocalProbe))) cert.delivery_word
  simp only [List.map_cons, List.map_map, Function.comp_def] at dates
  rw [show (firingRows i port word).map Transaction.probe =
    word.map (fun clocks => ⟨clocks.1, i, port⟩) by
      simp [firingRows, reciprocalRow, List.map_map, Function.comp_def]]
  rw [dates]
  congr 1
  apply List.map_congr_left
  intro token mem
  have cell : token.cell = i := of_decide_eq_true (List.mem_filter.mp mem).2
  simp [reciprocalOccurrence, ports token mem, cell]

private theorem prepared_has_active {n θ route s u i port}
    {e : @Execution n θ route s u} {word} (cert : PreparedTransactions i port e word) :
    s.raw i port = some s.time := by cases cert <;> assumption

/-- Account for the receiver's first contact in the head cut. The pulse
list starts at this already-active contact. The independently known
delivery count rules out any additional contact in that head. -/
theorem firingRows_receiver_admissions {θ route s v u i port word}
    (head : @Execution 2 θ route s v) {tail : Execution θ route v u}
    (cert : PreparedTransactions i port tail word)
    (empty : s.raw i port = none)
    (size : ((head.append tail).cellDeliveries i).length = word.length)
    (ports : ∀ token ∈ (head.append tail).cellDeliveries i, token.port = port) :
    (firingRows i port word).map Transaction.probe =
      ((head.append tail).cellDeliveries i).map reciprocalOccurrence := by
  have tailPorts : ∀ token ∈ tail.cellDeliveries i, token.port = port := by
    intro tok ht
    apply ports
    rw [Execution.cellDeliveries_append]
    exact List.mem_append_right _ ht
  have rows := firingRows_admissions cert tailPorts
  have counts := congrArg List.length rows
  simp only [List.length_map, List.length_cons, firingRows] at counts
  have one : (head.cellDeliveries i).length = 1 := by
    rw [Execution.cellDeliveries_append, List.length_append, counts] at size
    omega
  rcases head.raw_origin_provenance i port v.time (prepared_has_active cert) with prior | ⟨tok, mem, cell, key, date⟩
  · rw [empty] at prior
    contradiction
  have present : tok ∈ head.cellDeliveries i := by simp [Execution.cellDeliveries, mem, cell]
  have exactHead : head.cellDeliveries i = [tok] := by
    obtain ⟨only, eq⟩ := List.length_eq_one_iff.mp one
    have same : tok = only := by simpa [eq] using present
    rw [eq, same]
  rw [Execution.cellDeliveries_append, exactHead, rows]
  simp [reciprocalOccurrence, cell, key, date]

/-- Pin the forward receiver's learned rows to the actual deliveries
and FIRE word of the forward execution, including the head admission. -/
theorem forward_prepared_replay_rows {θ born fresh ε newborn}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter nominalDelay nominalDelay)
      constructedBBirthSources}
    {r : FirstWiredArrival b} {a : FirstInterleavedPair r} {v : SecondWiredArrival a}
    {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
    {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t}
    (z : FirstCoupledTeaching x) (box : @PhysicalBox 2 (extendParameters θ fresh) ε) :
    ∃ word : List (ℝ × ℝ), word.length = 13 ∧
      (firingRows 1 1 word).map Transaction.probe = (z.execution.cellDeliveries 1).map reciprocalOccurrence ∧
      word.map Prod.snd = z.execution.emissionTimes 1 ∧
      (∀ row ∈ firingRows 1 1 word, ∀ date ∈ row.fireDate,
        row.probe.due ≤ date ∧ date < row.probe.due + 1) := by
  obtain ⟨s, head, tail, word, split, count, cert, emissions⟩ := forward_receiver_transactions z box
    (fun _ => by norm_num [nominalDelay])
  have empty : x.final.raw 1 1 = none := x.raw_receiver 1
  have size : (z.execution.cellDeliveries 1).length = word.length := by
    rw [z.b_deliveries, List.length_map, z.train.wire_count, count]
  have ports : ∀ token ∈ z.execution.cellDeliveries 1, token.port = 1 := by
    intro token mem
    rw [z.b_deliveries] at mem
    obtain ⟨date, _, rfl⟩ := List.mem_map.mp mem
    rfl
  refine ⟨word, count, ?_, emissions.symm, firingRows_clocks cert⟩
  rw [split]
  exact firingRows_receiver_admissions head cert empty (split ▸ size) (split ▸ ports)

/-- Pin the reverse receiver's nine learned rows to the exact receiving
train, including the head admission during the sender's first pulse. -/
theorem reverse_prepared_replay_rows {θ ε forward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward nominalDelay) start}
    {a : FeedbackFirstFire w} {q : FirstReverseWiredArrival a}
    {p : FirstReverseInterleavedPair q} (entry : ReverseEntryCompletion p)
    (epoch : ReverseLearnedEpoch a.parametersA a.parametersB forward nominalDelay entry.final)
    (box : @PhysicalBox 2 (extendParameters a.parametersA (a.parametersB 0)) ε)
    (senderGain : 9 / 5 ≤ Real.exp (entry.final.x 1 (.z 2)) ∧
      Real.exp (entry.final.x 1 (.z 2)) ≤ 12 / 5)
    (receiverGain : 9 / 5 ≤ Real.exp (entry.final.x 0 (.z 2)) ∧
      Real.exp (entry.final.x 0 (.z 2)) ≤ 12 / 5) :
    ∃ word : List (ℝ × ℝ), word.length = 9 ∧
      (firingRows 0 2 word).map Transaction.probe = (epoch.execution.cellDeliveries 0).map reciprocalOccurrence ∧
      word.map Prod.snd = epoch.execution.emissionTimes 0 ∧
      (∀ row ∈ firingRows 0 2 word, ∀ date ∈ row.fireDate,
        row.probe.due ≤ date ∧ date < row.probe.due + 1) := by
  obtain ⟨s, head, tail, word, split, count, cert, emissions⟩ :=
    reverse_receiver_transactions entry epoch box senderGain receiverGain
  have empty : entry.final.raw 0 2 = none := entry.raw_other 0 2 (Or.inl (by decide))
  have size : (epoch.execution.cellDeliveries 0).length = word.length := by
    rw [epoch.a_deliveries, List.length_map, epoch.wire_count, count]
  have ports : ∀ token ∈ epoch.execution.cellDeliveries 0, token.port = 2 := by
    intro token mem
    rw [epoch.a_deliveries] at mem
    obtain ⟨date, _, rfl⟩ := List.mem_map.mp mem
    rfl
  refine ⟨word, count, ?_, emissions.symm, firingRows_clocks cert⟩
  rw [split]
  exact firingRows_receiver_admissions head cert empty (split ▸ size) (split ▸ ports)

private theorem only_cell {α : Type} (cell : α → Fin 2) (xs : List α) :
    ((xs.filter (fun x => cell x = 0)) ++ (xs.filter (fun x => cell x = 1))).Perm xs := by
  have other (x : α) : (cell x = 1) ↔ ¬ (cell x = 0) := by
    generalize cell x = i
    fin_cases i <;> decide
  have eq : (fun x => decide (cell x = 1)) = fun x => !decide (cell x = 0) := by
    funext x
    simp only [other x]
    try simp
  rw [eq]
  exact List.filter_append_perm _ xs

private theorem clockOfRows_exists (rows : List Row)
    (distinct : (rows.map Transaction.probe).Nodup)
    (clocks : ∀ tx ∈ rows, ∀ t ∈ tx.fireDate, tx.probe.due ≤ t ∧ t < tx.probe.due + 1) :
    ∃ fire : ReciprocalProbe → ℝ, (∀ p, p.due ≤ fire p ∧ fire p < p.due + 1) ∧
      ∀ tx ∈ rows, ∀ t ∈ tx.fireDate, fire tx.probe = t := by
  classical
  have unique : ∀ tx ∈ rows, ∀ p ∈ rows, tx.probe = p.probe → tx = p := by
    intro tx hx p hp eq
    exact List.inj_on_of_nodup_map distinct hx hp eq
  let matchesRow (p : ReciprocalProbe) (date : ℝ) := ∃ tx ∈ rows, tx.probe = p ∧ tx.fireDate = some date
  let fire : ReciprocalProbe → ℝ := fun p =>
    if h : ∃ t, matchesRow p t then h.choose else p.due
  refine ⟨fire, ?_, ?_⟩
  · intro p
    unfold fire
    split_ifs with h
    · obtain ⟨tx, mem, eq, found⟩ := h.choose_spec
      have bound := clocks tx mem h.choose (by simp [found])
      rwa [eq] at bound
    · exact ⟨le_rfl, by linarith⟩
  · intro tx mem t ht
    have tokenDate : tx.fireDate = some t := Option.mem_def.mp ht
    have someFire : ∃ date, matchesRow tx.probe date := ⟨t, tx, mem, rfl, tokenDate⟩
    obtain ⟨other, seen, same, actual⟩ := someFire.choose_spec
    have identical := unique other seen tx mem same
    rw [identical, tokenDate] at actual
    simpa only [fire, dite_eq_left someFire] using (Option.some.inj actual).symm

set_option maxHeartbeats 1500000 in
/-- Retain the entry used for the learned suffix and the exact transaction
clocks of that same entry. The next B source at 376 is consumed here
and responds in the following prepared block. -/
theorem reverse_entry_with_clocks {θ ε start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter nominalDelay nominalDelay) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) (hb : PhysicalBox θ ε)
    (low : Real.log (3 / 10) - 1 / 100000 ≤ r.final.x 0 (.z 2) ∧
      r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (high : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧
      Real.exp (w.final.x 1 (.z 2)) ≤ 2) :
    ∃ (entry : ReverseEntryCompletion p) (f352 f360 f368 aFire : ℝ),
      entry.execution.deliveries =
        [⟨0, 2, f352 + 7 / 20⟩, ⟨1, 2, 360⟩,
          ⟨0, 2, f360 + 7 / 20⟩, ⟨1, 2, 368⟩,
          ⟨0, 2, f368 + 7 / 20⟩, ⟨1, 2, 376⟩] ∧
      entry.execution.ledger.emissions = [(1, f352), (1, f360), (1, f368), (0, aFire)] ∧
      (352 ≤ f352 ∧ f352 < 353) ∧ (360 ≤ f360 ∧ f360 < 361) ∧
      (368 ≤ f368 ∧ f368 < 369) ∧
      (f368 + 7 / 20 ≤ aFire ∧ aFire < f368 + 7 / 20 + 1) := by
  obtain ⟨n2, s360, n3, s368, n4, s376, date360, date368, _, wire2, wire3, wire4,
    _, _, _⟩ := reverse_entry_transaction_rows p hb low high (fun _ => by norm_num [nominalDelay])
  have hfuture376 : ∀ d ∈ reversePending376, (376 : ℝ) < d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  let after : Execution (extendParameters f.parametersA (f.parametersB 0))
      (reciprocalEntryRouter nominalDelay nominalDelay) n2.wire.final s376.final :=
    ((((s360.execution.append n3.wire.execution).append s368.execution).append n4.wire.execution).append s376.execution)
  let trace := n2.execution.append (after.cast_parameters f.parameters_product)
  have htarget : s376.final.x 0 (.z 2) = p.final.x 0 (.z 2) + 6 / 5 := by
    rw [s376.gains,n4.wire.gains,s368.a_gain_target,n3.wire.gains,s360.a_gain_target,n2.wire.gains]
    ring
  have hother : ∀ q, q ≠ 2 → s376.final.x 0 (.z q) = p.final.x 0 (.z q) := by
    intro q hq
    rw [s376.gains,n4.wire.gains,s368.a_gain_other q hq,n3.wire.gains,
      s360.a_gain_other q hq,n2.wire.gains]
  have hB : ∀ q, s376.final.x 1 (.z q) = p.final.x 1 (.z q) := by
    intro q
    rw [s376.gains,n4.wire.gains,s368.b_gains,n3.wire.gains,s360.b_gains,n2.wire.gains]
  have hrec : ∀ i, s376.final.x i .b = p.final.x i .b := by
    intro i
    rw [s376.recovery,n4.wire.recovery,s368.recovery,n3.wire.recovery,s360.recovery,n2.wire.recovery]
  have he : trace.ledger.emissions = [(1,n2.cycle.fire.final.time),
      (1,n3.senderCycle.fire.final.time),(1,n4.senderCycle.fire.final.time),
      (0,s376.returned.receiver.fire.final.time)] := by
    simp only [trace,after,Execution.emissions_append,Execution.cast_parameters_ledger,
      n2.emissions,s360.emissions,n3.wire.emissions,s368.emissions,n4.wire.emissions,
      s376.emissions,List.nil_append,List.append_nil,List.cons_append]
  let entry : ReverseEntryCompletion p := {
    final := s376.final, execution := trace
    date := by rw [s376.date,date368]; norm_num
    prepared := s376.prepared, charge := s376.charge
    raw_active := s376.raw_active, raw_other := s376.raw_other, pending := s376.pending
    a_gain_target := htarget, a_gain_other := hother, b_gains := hB, recovery := hrec
    a_emission_count := by simp [Execution.emissionTimes,he]
    b_emission_count := by simp [Execution.emissionTimes,he]
    physical := by simpa only [f.parameters_product] using s376.physical
    raw_valid := s376.raw_valid
    complete := by
      have hc := s376.complete (by rw [date368]; norm_num; exact hfuture376)
      simpa only [CompleteThrough,date368,show (368 : ℝ) + 8 = 376 by norm_num] using hc }
  refine ⟨entry, _, _, _, _, ?_, he, ?_, ?_, ?_, ?_⟩

  · simp only [entry, trace, after, Execution.deliveries_append, Execution.cast_parameters_deliveries,
      n2.deliveries, s360.deliveries, n3.wire.deliveries, s368.deliveries, n4.wire.deliveries,
      s376.deliveries, List.cons_append, List.nil_append]
    change ([⟨0, 2, n2.wire.final.time⟩, ⟨1, 2, p.final.time + 8⟩,
      ⟨0, 2, n3.wire.final.time⟩, ⟨1, 2, s360.final.time + 8⟩,
      ⟨0, 2, n4.wire.final.time⟩, ⟨1, 2, s368.final.time + 8⟩] : List (Delivery 2)) = _
    rw [wire2, wire3, wire4, p.date, date360, date368]
    norm_num [nominalDelay]
  · have bounds := n2.cycle.fire_bounds
    change p.final.time + 2 / 5 < n2.cycle.fire.final.time ∧
      n2.cycle.fire.final.time < p.final.time + 7 / 10 at bounds
    rw [p.date] at bounds
    constructor <;> linarith [bounds.1, bounds.2]
  · have bounds := n3.senderCycle.fire_bounds
    change s360.final.time + 2 / 5 < n3.senderCycle.fire.final.time ∧
      n3.senderCycle.fire.final.time < s360.final.time + 7 / 10 at bounds
    rw [date360] at bounds
    constructor <;> linarith [bounds.1, bounds.2]
  · have bounds := n4.senderCycle.fire_bounds
    change s368.final.time + 2 / 5 < n4.senderCycle.fire.final.time ∧
      n4.senderCycle.fire.final.time < s368.final.time + 7 / 10 at bounds
    rw [date368] at bounds
    constructor <;> linarith [bounds.1, bounds.2]
  · have bounds := s376.returned.receiver.fire_bounds
    change n4.wire.final.time + 2 / 5 < s376.returned.receiver.fire.final.time ∧
      s376.returned.receiver.fire.final.time < n4.wire.final.time + 7 / 10 at bounds
    rw [wire4] at bounds
    change n4.senderCycle.fire.final.time + 7 / 20 ≤ s376.returned.receiver.fire.final.time ∧
      s376.returned.receiver.fire.final.time < n4.senderCycle.fire.final.time + 7 / 20 + 1
    unfold nominalDelay at bounds
    exact ⟨(le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2 / 5)).trans bounds.1.le,
      bounds.2.trans (add_lt_add_right (by norm_num : (7 / 10 : ℝ) < 1) _)⟩

private theorem nativeOccurrence_injective : Function.Injective reciprocalOccurrence := by
  intro a b h
  cases a
  cases b
  simpa [reciprocalOccurrence, and_left_comm, and_comm, and_assoc] using h

private theorem deliveryNodup {n θ route s u} (run : @Execution n θ route s u) :
    run.deliveries.Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply (actual_raw_windows_disjoint run).imp
  intro a b separate eq
  subst b
  linarith [separate rfl rfl]

private theorem stagedOccurrenceNodup (epoch : NominalEpoch)
    (beforeClose : ∀ d ∈ epoch.staged.before.deliveries, d.due < (160 : ℝ))
    (birthDate : epoch.staged.afterBirth.time = 160) :
    ((stagedDeliveries epoch).map reciprocalOccurrence).Nodup := by
  have liftInjective : Function.Injective (@liftDelivery 1) := by
    intro a b h
    cases a
    cases b
    simpa [liftDelivery, Fin.castSucc_inj] using h
  apply List.Nodup.map nativeOccurrence_injective
  apply (List.Nodup.map liftInjective (deliveryNodup epoch.staged.before)).append
    (deliveryNodup epoch.staged.after)
  intro tok left right
  obtain ⟨original, mem, rfl⟩ := List.mem_map.mp left
  have later := (epoch.staged.after.delivery_time_bounds (liftDelivery original) right).1
  change epoch.staged.afterBirth.time ≤ original.due at later
  linarith [beforeClose original mem]

/-- Reorder the cut certificates into the exact native admission order.
The permutation is checked with multiplicities. -/
private theorem alignRows (rows : List Row) (admissions : List ReciprocalProbe)
    (same : (rows.map Transaction.probe).Perm admissions) :
    ∃ aligned : List Row, aligned.Perm rows ∧ aligned.map Transaction.probe = admissions := by
  classical
  induction admissions generalizing rows with
  | nil =>
    have empty : rows = [] := List.length_eq_zero_iff.mp (by simpa using same.length_eq)
    subst rows
    exact ⟨[], List.Perm.refl _, rfl⟩
  | cons p pending ih =>
    obtain ⟨head, mem, eq⟩ := List.mem_map.mp (same.mem_iff.mpr (List.mem_cons_self ..))
    have remove := List.perm_cons_erase mem
    have tail : ((rows.erase head).map Transaction.probe).Perm pending := by
      have rearrange := (remove.map Transaction.probe).symm.trans same
      simpa only [List.map_cons, eq, List.perm_cons] using rearrange
    obtain ⟨aligned, order, mapped⟩ := ih (rows.erase head) tail
    exact ⟨head :: aligned, (order.cons _).trans remove.symm, by simp [mapped, eq]⟩

private theorem firingRows_shape (i : Fin 2) (port : Port) (word : List (ℝ × ℝ)) :
    ∀ tx ∈ firingRows i port word, tx = reciprocalRow tx.probe tx.fireDate := by
  intro tx ht
  obtain ⟨clocks, _, rfl⟩ := List.mem_map.mp ht
  rfl

section Forward

variable {θ born fresh ε newborn} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter nominalDelay nominalDelay) constructedBBirthSources}
  {r : FirstWiredArrival b} {a : FirstInterleavedPair r} {v : SecondWiredArrival a}
  {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
  {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t}

private noncomputable def forwardEntryRows (tA tB tC tD first second third : ℝ) : List Row :=
  [reciprocalRow ⟨160, 0, 0⟩ (some tA), reciprocalRow ⟨first, 1, 1⟩ none,
    reciprocalRow ⟨168, 0, 0⟩ (some tB), reciprocalRow ⟨second, 1, 1⟩ (some tD),
    reciprocalRow ⟨176, 0, 0⟩ (some tC), reciprocalRow ⟨third, 1, 1⟩ none]

private theorem forward_entry_rows (x : FirstCoupledPreparedPair t) :
    let rows := forwardEntryRows r.fire.final.time v.fire.final.time t.fire.final.time
      f.final.time r.final.time v.final.time t.final.time
    (rows.map Transaction.probe ++ [⟨184, 0, 0⟩] =
      x.staged.after.deliveries.map reciprocalOccurrence) ∧
    (Transaction.fires Prod.fst rows).Perm x.staged.after.ledger.emissions ∧
    (∀ row ∈ rows, ∀ clock ∈ row.fireDate, row.probe.due ≤ clock ∧ clock < row.probe.due + 1) ∧
    (160 < r.final.time ∧ r.final.time < 162) ∧ (168 < v.final.time ∧ v.final.time < 170) ∧
    (176 < t.final.time ∧ t.final.time < 178) := by
  have delay : ∀ t, (3 / 10 : ℝ) ≤ nominalDelay t ∧ nominalDelay t ≤ 2 / 5 :=
    fun _ => by norm_num [nominalDelay]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [x.staged_deliveries]
    rfl
  · rw [x.staged_emissions]
    change ([(0, r.fire.final.time), (0, v.fire.final.time), (1, f.final.time),
      (0, t.fire.final.time)] : List (Fin 2 × ℝ)).Perm _
    rfl
  · intro tx mem clock fired
    simp only [forwardEntryRows, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reciprocalRow, Option.mem_def, reduceCtorEq, Option.some.injEq] at fired
    all_goals
      subst clock
      simp only [reciprocalRow]
      constructor <;> first
        | linarith only [r.fire.early, r.fire.deadline]
        | linarith only [v.fire.early, v.fire.deadline]
        | linarith only [f.early, f.deadline]
        | linarith only [t.fire.early, t.fire.deadline]
  · exact ⟨by linarith [(r.date_bounds delay).1], by linarith [(r.date_bounds delay).2]⟩
  · exact ⟨by linarith [(v.date_bounds delay).1], by linarith [(v.date_bounds delay).2]⟩
  · exact ⟨by linarith [(t.date_bounds delay).1], by linarith [(t.date_bounds delay).2]⟩

set_option maxHeartbeats 800000 in
/-- Assemble the post-birth forward rows on the execution through 319.9.
The active source at 184 belongs to the prepared tail's pulse word. -/
theorem forward_transaction_table (z : FirstCoupledTeaching x)
    (box : @PhysicalBox 2 (extendParameters θ fresh) ε) :
    ∃ (sender receiver : List (ℝ × ℝ)) (rows : List Row),
      sender.length = 13 ∧ receiver.length = 13 ∧
      rows = forwardEntryRows r.fire.final.time v.fire.final.time t.fire.final.time
        f.final.time r.final.time v.final.time t.final.time ++
        firingRows 0 0 sender ++ firingRows 1 1 receiver ∧
      (rows.map Transaction.probe).Perm (z.staged.after.deliveries.map reciprocalOccurrence) ∧
      (Transaction.fires Prod.fst rows).Perm z.staged.after.ledger.emissions ∧
      (∀ row ∈ rows, ∀ clock ∈ row.fireDate, row.probe.due ≤ clock ∧ clock < row.probe.due + 1) ∧
      (∀ row ∈ firingRows 0 0 sender ++ firingRows 1 1 receiver, (184 : ℝ) ≤ row.probe.due) := by
  obtain ⟨sender, senderCount, senderCert⟩ := forward_sender_transactions z box
  obtain ⟨receiver, receiverCount, receiverDates, receiverFire, receiverClocks⟩ :=
    forward_prepared_replay_rows z box
  obtain ⟨headDates, headFire, headClocks, _, _, _⟩ := forward_entry_rows x
  have senderPorts : ∀ token ∈ z.train.execution.cellDeliveries 0, token.port = 0 := by
    intro token mem
    rw [z.train.a_deliveries] at mem
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp mem
    rfl
  have senderDates := firingRows_admissions senderCert senderPorts
  rw [x.date] at senderDates
  have senderAfter : z.execution.cellDeliveries 0 = z.train.execution.cellDeliveries 0 := by
    simp [FirstCoupledTeaching.execution, Execution.cellDeliveries, Execution.deliveries_append, z.wait_deliveries]
  have senderFire : sender.map Prod.snd = z.execution.emissionTimes 0 := by
    rw [FirstCoupledTeaching.execution, Execution.emissionTimes_append, senderCert.fire_word]
    simp [Execution.emissionTimes, z.wait_emissions]
  let first := forwardEntryRows r.fire.final.time v.fire.final.time t.fire.final.time
    f.final.time r.final.time v.final.time t.final.time
  refine ⟨sender, receiver, first ++ firingRows 0 0 sender ++ firingRows 1 1 receiver,
    senderCount, receiverCount, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_append, senderDates, receiverDates, ← senderAfter]
    rw [show z.staged.after.deliveries = x.staged.after.deliveries ++ z.execution.deliveries from
      Execution.deliveries_append _ _, List.map_append, ← headDates]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply List.Perm.append_left
    simpa only [Execution.cellDeliveries, List.map_append] using
      ((only_cell Delivery.cell z.execution.deliveries).map reciprocalOccurrence).cons ⟨184, 0, 0⟩
  · simp only [Transaction.fires, List.filterMap_append]
    change ((Transaction.fires Prod.fst first) ++
      Transaction.fires Prod.fst (firingRows 0 0 sender) ++
      Transaction.fires Prod.fst (firingRows 1 1 receiver)).Perm _
    rw [firingRows_fires, firingRows_fires]
    rw [show sender.map (fun clocks => ((0 : Fin 2), clocks.2)) =
       (z.execution.emissionTimes 0).map (fun time => (0, time)) by rw [← senderFire]; simp]
    rw [show receiver.map (fun clocks => ((1 : Fin 2), clocks.2)) =
       (z.execution.emissionTimes 1).map (fun time => (1, time)) by rw [← receiverFire]; simp]
    rw [show z.staged.after.ledger.emissions = x.staged.after.ledger.emissions ++ z.execution.ledger.emissions from
      Execution.emissions_append _ _]
    have fireByCell (i : Fin 2) : (z.execution.emissionTimes i).map (fun time => (i, time)) =
        z.execution.ledger.emissions.filter (fun event => event.1 = i) := by
      simp only [Execution.emissionTimes, List.map_map, Function.comp_def]
      conv_rhs => rw [← List.map_id (l := z.execution.ledger.emissions.filter _)]
      apply List.map_congr_left
      intro item mem
      exact Prod.ext ((of_decide_eq_true (List.mem_filter.mp mem).2 : item.1 = i).symm) rfl
    rw [fireByCell, fireByCell]
    simpa only [List.append_assoc] using headFire.append (only_cell Prod.fst z.execution.ledger.emissions)
  · intro row mem
    rcases List.mem_append.mp mem with earlier | last
    · rcases List.mem_append.mp earlier with head | middle
      · exact headClocks row head
      · exact firingRows_clocks senderCert row middle
    · exact receiverClocks row last

  · intro row mem
    rcases List.mem_append.mp mem with left | right
    · have present : row.probe ∈ (firingRows 0 0 sender).map Transaction.probe := List.mem_map_of_mem left
      rw [senderDates] at present
      rcases List.mem_cons.mp present with same | delivered
      · rw [same]
      · obtain ⟨token, member, same⟩ := List.mem_map.mp delivered
        rw [← same]
        have bound := (z.train.execution.delivery_time_bounds token (List.mem_filter.mp member).1).1
        rwa [x.date] at bound
    · have present : row.probe ∈ (firingRows 1 1 receiver).map Transaction.probe := List.mem_map_of_mem right
      rw [receiverDates] at present
      obtain ⟨token, member, same⟩ := List.mem_map.mp present
      rw [← same]
      have bound := (z.execution.delivery_time_bounds token (List.mem_filter.mp member).1).1
      rwa [x.date] at bound

end Forward

section Reverse

variable {θ ε start} {w : FeedbackWeakEntry θ (reciprocalEntryRouter nominalDelay nominalDelay) start}
  {a : FeedbackFirstFire w} {q : FirstReverseWiredArrival a} {p : FirstReverseInterleavedPair q}

private noncomputable def reverseEntryRows (first f352 f360 f368 returnFire : ℝ) : List Row :=
  [reciprocalRow ⟨320, 1, 2⟩ none, reciprocalRow ⟨328, 1, 2⟩ none,
    reciprocalRow ⟨336, 1, 2⟩ none, reciprocalRow ⟨344, 1, 2⟩ (some first),
    reciprocalRow ⟨first + 7 / 20, 0, 2⟩ none,
    reciprocalRow ⟨352, 1, 2⟩ (some f352), reciprocalRow ⟨f352 + 7 / 20, 0, 2⟩ none,
    reciprocalRow ⟨360, 1, 2⟩ (some f360), reciprocalRow ⟨f360 + 7 / 20, 0, 2⟩ none,
    reciprocalRow ⟨368, 1, 2⟩ (some f368), reciprocalRow ⟨f368 + 7 / 20, 0, 2⟩ (some returnFire)]

private noncomputable def reverseHead (p : FirstReverseInterleavedPair q) : Execution θ
    (reciprocalEntryRouter nominalDelay nominalDelay) start p.final :=
  (((w.execution.append a.execution).append q.execution).append p.execution)

private theorem reverse_entry_rows (p : FirstReverseInterleavedPair q)
    (entry : ReverseEntryCompletion p) (f352 f360 f368 returnFire : ℝ)
    (delivered : entry.execution.deliveries =
      [⟨0, 2, f352 + 7 / 20⟩, ⟨1, 2, 360⟩, ⟨0, 2, f360 + 7 / 20⟩,
        ⟨1, 2, 368⟩, ⟨0, 2, f368 + 7 / 20⟩, ⟨1, 2, 376⟩])
    (fired : entry.execution.ledger.emissions = [(1, f352), (1, f360), (1, f368), (0, returnFire)])
    (second : 352 ≤ f352 ∧ f352 < 353) (third : 360 ≤ f360 ∧ f360 < 361)
    (fourth : 368 ≤ f368 ∧ f368 < 369)
    (returned : f368 + 7 / 20 ≤ returnFire ∧ returnFire < f368 + 7 / 20 + 1) :
    let rows := reverseEntryRows a.final.time f352 f360 f368 returnFire
    rows.map Transaction.probe ++ [⟨376, 1, 2⟩] =
      ((reverseHead p).append entry.execution).deliveries.map reciprocalOccurrence ∧
    Transaction.fires Prod.fst rows = ((reverseHead p).append entry.execution).ledger.emissions ∧
    (∀ row ∈ rows, ∀ clock ∈ row.fireDate, row.probe.due ≤ clock ∧ clock < row.probe.due + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [reverseHead, Execution.deliveries_append, w.deliveries, a.deliveries, q.deliveries,
      p.deliveries, delivered, sourceTrain, List.ofFn_succ, reciprocalOccurrence,
      reverseEntryRows, reciprocalRow, FeedbackFirstFire.reverseToken, nominalDelay]
  · simp [reverseHead, Execution.emissions_append, w.emissions, a.emissions, q.emissions, p.emissions,
      fired, Transaction.fires, reverseEntryRows, reciprocalRow]
  · intro row mem clock hc
    simp only [reverseEntryRows, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reciprocalRow, Option.mem_def, reduceCtorEq, Option.some.injEq] at hc
    all_goals
      subst clock
    · change 344 ≤ a.final.time ∧ a.final.time < (344 : ℝ) + 1
      constructor <;> linarith only [a.window.1, a.window.2]
    · exact ⟨second.1, by simpa only [reciprocalRow, show (352 : ℝ) + 1 = 353 by norm_num] using second.2⟩
    · exact ⟨third.1, by simpa only [reciprocalRow, show (360 : ℝ) + 1 = 361 by norm_num] using third.2⟩
    · exact ⟨fourth.1, by simpa only [reciprocalRow, show (368 : ℝ) + 1 = 369 by norm_num] using fourth.2⟩
    · exact returned

end Reverse

private theorem emissionByCell {n θ route s u} (run : @Execution n θ route s u) (i : Fin n) :
    (run.emissionTimes i).map (fun time => (i, time)) =
      run.ledger.emissions.filter (fun event => event.1 = i) := by
  simp only [Execution.emissionTimes, List.map_map, Function.comp_def]
  conv_rhs => rw [← List.map_id (l := run.ledger.emissions.filter _)]
  apply List.map_congr_left
  intro item mem
  exact Prod.ext ((of_decide_eq_true (List.mem_filter.mp mem).2 : item.1 = i).symm) rfl

section ReverseTail
variable {θ ε start} {w : FeedbackWeakEntry θ (reciprocalEntryRouter nominalDelay nominalDelay) start}
  {a : FeedbackFirstFire w} {q : FirstReverseWiredArrival a} {p : FirstReverseInterleavedPair q}

set_option maxHeartbeats 1000000 in
/-- Cover the reverse training rows and prepared suffix. The source at
376 is consumed in the entry and fires in the suffix. -/
theorem reverse_transaction_table (p : FirstReverseInterleavedPair q)
    (box : PhysicalBox θ ε)
    (low : Real.log (3 / 10) - 1 / 100000 ≤ q.final.x 0 (.z 2) ∧
      q.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (high : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧
      Real.exp (w.final.x 1 (.z 2)) ≤ 2) :
    ∃ (entry : ReverseEntryCompletion p)
      (epoch : ReverseLearnedEpoch a.parametersA a.parametersB nominalDelay nominalDelay entry.final)
      (f352 f360 f368 returnFire : ℝ) (sender receiver : List (ℝ × ℝ)) (rows : List Row),
      sender.length = 9 ∧ receiver.length = 9 ∧
      rows = reverseEntryRows a.final.time f352 f360 f368 returnFire ++
        firingRows 1 2 sender ++ firingRows 0 2 receiver ∧
      (rows.map Transaction.probe).Perm (((reverseHead p).append
          (entry.execution.append (epoch.execution.cast_parameters a.parameters_product))).deliveries.map
        reciprocalOccurrence) ∧
      (Transaction.fires Prod.fst rows).Perm ((reverseHead p).append
          (entry.execution.append (epoch.execution.cast_parameters a.parameters_product))).ledger.emissions ∧
      (∀ row ∈ rows, ∀ clock ∈ row.fireDate, row.probe.due ≤ clock ∧ clock < row.probe.due + 1) ∧
      (∀ row ∈ firingRows 1 2 sender ++ firingRows 0 2 receiver, (376 : ℝ) ≤ row.probe.due) := by
  obtain ⟨entry, f352, f360, f368, returnFire, delivered, fired, second, third, fourth, returned⟩ :=
    reverse_entry_with_clocks p box low high
  have params : PhysicalBox (extendParameters a.parametersA (a.parametersB 0)) ε := by
    rw [a.parameters_product]
    exact box
  have physical : PhysicalInvariant (extendParameters a.parametersA (a.parametersB 0)) entry.final := by
    rw [a.parameters_product]
    exact entry.physical
  have receiverGain : 9 / 5 ≤ Real.exp (entry.final.x 0 (.z 2)) ∧
      Real.exp (entry.final.x 0 (.z 2)) ≤ 2 := by
    have sum : entry.final.x 0 (.z 2) = q.final.x 0 (.z 2) + 9 / 5 := by
      rw [entry.a_gain_target, p.a_gain_target box low.2]
      ring
    exact learned_gain_bounds (by rw [sum]; linarith [low.1]) (by rw [sum]; linarith [low.2])
  have senderGain : 9 / 5 ≤ Real.exp (entry.final.x 1 (.z 2)) ∧
      Real.exp (entry.final.x 1 (.z 2)) ≤ 2 := by
    rw [entry.b_gains, p.b_gains]
    exact high
  obtain ⟨epoch⟩ := reverse_learned_epoch_exists params entry.final physical entry.raw_valid entry.date
    entry.prepared entry.charge receiverGain senderGain entry.raw_active entry.raw_other entry.pending
    nominalDelay nominalDelay (fun _ => by norm_num [nominalDelay])
  obtain ⟨sender, senderCount, senderCert⟩ := reverse_sender_transactions entry epoch box high
  obtain ⟨receiver, receiverCount, receiverDates, receiverFire, receiverClocks⟩ :=
    reverse_prepared_replay_rows entry epoch params ⟨senderGain.1, by linarith [senderGain.2]⟩
      ⟨receiverGain.1, by linarith [receiverGain.2]⟩
  obtain ⟨headDates, headFire, headClocks⟩ :=
    reverse_entry_rows p entry f352 f360 f368 returnFire delivered fired second third fourth returned
  let run := epoch.execution.cast_parameters a.parameters_product
  have castDates (i : Fin 2) : run.cellDeliveries i = epoch.execution.cellDeliveries i := by
    simp [run, Execution.cellDeliveries, Execution.cast_parameters_deliveries]
  have senderPorts : ∀ token ∈ run.cellDeliveries 1, token.port = 2 := by
    intro token mem
    rw [castDates, epoch.b_deliveries] at mem
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp mem
    rfl
  have senderDates := firingRows_admissions senderCert senderPorts
  rw [entry.date, castDates] at senderDates
  have senderFire : sender.map Prod.snd = epoch.execution.emissionTimes 1 := by
    simpa only [Execution.emissionTimes, Execution.cast_parameters_ledger] using senderCert.fire_word.symm
  let first := reverseEntryRows a.final.time f352 f360 f368 returnFire
  refine ⟨entry, epoch, f352, f360, f368, returnFire, sender, receiver,
    first ++ firingRows 1 2 sender ++ firingRows 0 2 receiver,
    senderCount, receiverCount, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_append, senderDates, receiverDates, Execution.deliveries_append,
      Execution.cast_parameters_deliveries] at headDates ⊢
    rw [← List.append_assoc (List.map reciprocalOccurrence (reverseHead p).deliveries), ← headDates]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply List.Perm.append_left
    have perm := (List.perm_append_comm (l₁ := epoch.execution.cellDeliveries 1)
      (l₂ := epoch.execution.cellDeliveries 0)).trans (only_cell Delivery.cell epoch.execution.deliveries)
    simpa only [Execution.cellDeliveries, List.map_append] using
      (perm.map reciprocalOccurrence).cons ⟨376, 1, 2⟩
  · simp only [Transaction.fires, List.filterMap_append]
    change ((Transaction.fires Prod.fst first) ++
      Transaction.fires Prod.fst (firingRows 1 2 sender) ++
      Transaction.fires Prod.fst (firingRows 0 2 receiver)).Perm _
    rw [firingRows_fires, firingRows_fires]
    rw [show sender.map (fun clocks => ((1 : Fin 2), clocks.2)) =
      (epoch.execution.emissionTimes 1).map (fun time => (1, time)) by rw [← senderFire]; simp]
    rw [show receiver.map (fun clocks => ((0 : Fin 2), clocks.2)) =
      (epoch.execution.emissionTimes 0).map (fun time => (0, time)) by rw [← receiverFire]; simp]
    rw [emissionByCell, emissionByCell, headFire]
    simp only [Execution.emissions_append, Execution.cast_parameters_ledger]
    rw [List.append_assoc, List.append_assoc]
    apply List.Perm.append_left
    apply List.Perm.append_left
    exact List.perm_append_comm.trans (only_cell Prod.fst epoch.execution.ledger.emissions)
  · intro row mem
    rcases List.mem_append.mp mem with earlier | last
    · rcases List.mem_append.mp earlier with head | middle
      · exact headClocks row head
      · exact firingRows_clocks senderCert row middle
    · exact receiverClocks row last

  · intro row mem
    rcases List.mem_append.mp mem with left | right
    · have present : row.probe ∈ (firingRows 1 2 sender).map Transaction.probe := List.mem_map_of_mem left
      rw [senderDates] at present
      rcases List.mem_cons.mp present with same | delivered
      · rw [same]
      · obtain ⟨token, member, same⟩ := List.mem_map.mp delivered
        rw [← same]
        have bound := (epoch.execution.delivery_time_bounds token (List.mem_filter.mp member).1).1
        rwa [entry.date] at bound
    · have present : row.probe ∈ (firingRows 0 2 receiver).map Transaction.probe := List.mem_map_of_mem right
      rw [receiverDates] at present
      obtain ⟨token, member, same⟩ := List.mem_map.mp present
      rw [← same]
      have bound := (epoch.execution.delivery_time_bounds token (List.mem_filter.mp member).1).1
      rwa [entry.date] at bound

end ReverseTail

private noncomputable def gainWrites (C : Calendar 2 ℝ ReciprocalInput) (i : Fin 6) (row : Row) : Bool :=
  !row.decision && C.model.learn row.probe && decide (MarkFeedback.gain C.model row.probe = i)

private noncomputable def markWrites (C : Calendar 2 ℝ ReciprocalInput) (i : Fin 6) (row : Row) : Bool :=
  C.model.mark row.probe row.decision && decide (MarkFeedback.recovery C.model row.probe = i)

private theorem countFold (fire : ReciprocalProbe → ℝ) (rows : List Row)
    (start : Fin 6 → Nat) (i : Fin 6) :
    writesAfter (reciprocalCalendar fire) rows start i =
      start i + rows.countP (gainWrites (reciprocalCalendar fire) i) +
        rows.countP (markWrites (reciprocalCalendar fire) i) := by
  induction rows generalizing start with
  | nil => simp [writesAfter]
  | cons head tail ih =>
    change writesAfter (reciprocalCalendar fire) tail
      (fun j => start j + MarkFeedback.footprint (reciprocalCalendar fire).model head.probe head.decision j) i = _
    rw [ih]
    simp only [List.countP_cons]
    have dose : MarkFeedback.footprint (reciprocalCalendar fire).model head.probe head.decision i =
        (if gainWrites (reciprocalCalendar fire) i head then 1 else 0) +
        (if markWrites (reciprocalCalendar fire) i head then 1 else 0) := by
      unfold MarkFeedback.footprint gainWrites markWrites
      have gainEq : (((!head.decision && (reciprocalCalendar fire).model.learn head.probe) &&
        decide (MarkFeedback.gain (reciprocalCalendar fire).model head.probe = i)) = true) =
          (head.decision = false ∧ (reciprocalCalendar fire).model.learn head.probe = true ∧
            i = MarkFeedback.gain (reciprocalCalendar fire).model head.probe) := by
        simp [and_assoc, eq_comm (a := i)]
      have markEq : (((reciprocalCalendar fire).model.mark head.probe head.decision &&
        decide (MarkFeedback.recovery (reciprocalCalendar fire).model head.probe = i)) = true) =
          ((reciprocalCalendar fire).model.mark head.probe head.decision = true ∧
            i = MarkFeedback.recovery (reciprocalCalendar fire).model head.probe) := by
        simp [eq_comm (a := i)]
      simp only [gainEq, markEq]
    rw [dose]
    omega

private theorem markWrites_ne_gain (fire : ReciprocalProbe → ℝ) (i : Fin 2) (port : Bool)
    (row : Row) :
    markWrites (reciprocalCalendar fire)
      (Address.mk i (if port then .port1 else .port0)).encode row = false := by
  have ne : MarkFeedback.recovery (reciprocalCalendar fire).model row.probe ≠
      (Address.mk i (if port then .port1 else .port0)).encode := by
    intro same
    have eq := congrArg Address.coordinate (AutonomousFeedback.Schedule.PortMemory.address_encode_injective _ _ same)
    cases port <;> contradiction
  simp [markWrites, ne]

private theorem ready_odd_score (fire : ReciprocalProbe → ℝ) (counts : Fin 6 → Nat) (p : ReciprocalProbe)
    (ready : (reciprocalCalendar fire).phase p.input p.due = .ready) :
    MarkFeedback.score (reciprocalCalendar fire).model 2 ⟨[], counts⟩ p =
      2 * (counts (MarkFeedback.gain (reciprocalCalendar fire).model p) : Int) -
        (if p.input = (1, 1) then 1 else 5) := by
  change (if (reciprocalCalendar fire).phase p.input p.due = .slow then (-7 : Int)
      else if p.input = (1, 1) then -1 else -5) +
    2 * (counts (MarkFeedback.gain (reciprocalCalendar fire).model p) : Int) + 0 * _ = _
  rw [ready]
  by_cases h : p.input = (1, 1) <;> simp [h] <;> omega

private theorem slow_odd_score (fire : ReciprocalProbe → ℝ) (counts : Fin 6 → Nat) (p : ReciprocalProbe)
    (slow : (reciprocalCalendar fire).phase p.input p.due = .slow) :
    MarkFeedback.score (reciprocalCalendar fire).model 2 ⟨[], counts⟩ p =
      2 * (counts (MarkFeedback.gain (reciprocalCalendar fire).model p) : Int) - 7 := by
  change (if (reciprocalCalendar fire).phase p.input p.due = .slow then (-7 : Int)
      else if p.input = (1, 1) then -1 else -5) +
    2 * (counts (MarkFeedback.gain (reciprocalCalendar fire).model p) : Int) + 0 * _ = _
  rw [slow]
  simp
  omega

private theorem guard_of_partition (fire : ReciprocalProbe → ℝ) (rows : List Row)
    (shape : ∀ tx ∈ rows, tx = reciprocalRow tx.probe tx.fireDate)
    (fireClocks : ∀ tx ∈ rows, ∀ t ∈ tx.fireDate, fire tx.probe = t)
    (ordered : rows.Pairwise (fun a b => a.probe.due ≤ b.probe.due))
    (totals : ∀ tx ∈ rows, let C := reciprocalCalendar fire
      rows.countP (gainWrites C (MarkFeedback.gain C.model tx.probe)) =
        if tx.probe.input = (1, 1) then 1 else 3)
    (silentSlow : ∀ tx ∈ rows, (reciprocalCalendar fire).phase tx.probe.input tx.probe.due = .slow →
      tx.decision = false)
    (trainingFirst : ∀ tx ∈ rows, ∀ learner ∈ rows,
      tx.decision = true → gainWrites (reciprocalCalendar fire)
        (MarkFeedback.gain (reciprocalCalendar fire).model tx.probe) learner = true →
      learner.probe.due < tx.probe.due) :
    RowGuards (reciprocalCalendar fire) 2 rows (fun _ => 0) := by
  classical
  let C := reciprocalCalendar fire
  have go (past tail : List Row) (split : rows = past ++ tail) :
      RowGuards C 2 tail (writesAfter C past (fun _ => 0)) := by
    induction tail generalizing past with
    | nil => trivial
    | cons head tail ih =>
      have mem : head ∈ rows := by rw [split]; simp
      let g := MarkFeedback.gain C.model head.probe
      let k := past.countP (gainWrites C g)
      let threshold : Nat := if head.probe.input = (1, 1) then 1 else 3
      let counts := writesAfter C past (fun _ => 0)
      have sum : counts g = k := by
        rw [show counts g = _ from countFold fire past _ g]
        have zero : past.countP (markWrites C g) = 0 := by
          apply List.countP_eq_zero.mpr
          intro row _
          simp [show markWrites C g row = false from
            markWrites_ne_gain fire (C.model.cell head.probe) (C.model.secondPort head.probe) row]
        change 0 + past.countP (gainWrites C g) + past.countP (markWrites C g) = k
        rw [zero, Nat.add_zero, Nat.zero_add]
      have total : rows.countP (gainWrites C g) = threshold := totals head mem
      have remaining : k + (head :: tail).countP (gainWrites C g) = threshold := by
        simpa only [split, List.countP_append, k] using total
      have trip : k ≤ 3 := by
        have upper : threshold ≤ 3 := by unfold threshold; split <;> decide
        omega
      have rowShape := shape head mem
      have limits : head.lo = -1 ∧ head.hi = 0 := by
        constructor
        · exact congrArg Transaction.lo rowShape
        · exact congrArg Transaction.hi rowShape
      have branches : let score := MarkFeedback.score C.model 2 ⟨[], counts⟩ head.probe
          (head.decision = false ∧ score < 0) ∨ (head.decision = true ∧ 1 ≤ score) := by
        cases hp : C.phase head.probe.input head.probe.due with
        | slow =>
          refine Or.inl ⟨silentSlow head mem hp, ?_⟩
          rw [slow_odd_score fire counts _ hp, sum]
          omega
        | ready =>
          rw [ready_odd_score fire counts _ hp, sum]
          cases hd : head.decision with
          | false =>
            have self : gainWrites C g head = true := by
              simp only [gainWrites, hd, Bool.not_false, Bool.true_and, g, decide_true, Bool.and_true]
              change decide (C.phase head.probe.input head.probe.due = .ready) = true
              simp [hp]
            simp only [List.countP_cons, self, ite_true] at remaining
            left
            refine ⟨rfl, ?_⟩
            by_cases key : head.probe.input = (1, 1) <;>
              simp [threshold, key] at remaining ⊢ <;> omega
          | true =>
            have none : (head :: tail).countP (gainWrites C g) = 0 := by
              apply List.countP_eq_zero.mpr
              intro row hr
              cases write : gainWrites C g row with
              | false => simp
              | true =>
                have present : row ∈ rows := by rw [split]; exact List.mem_append_right _ hr
                have before := trainingFirst head mem row present hd write
                have after : head.probe.due ≤ row.probe.due := by
                  rcases List.mem_cons.mp hr with rfl | later
                  · rfl
                  · have sorted := ordered.sublist (show List.Sublist (head :: tail) rows by rw [split]; exact List.sublist_append_right ..)
                    exact (List.pairwise_cons.mp sorted).1 row later
                exact (not_lt_of_ge after before).elim
            have eq : k = threshold := by omega
            right
            refine ⟨rfl, ?_⟩
            by_cases key : head.probe.input = (1, 1) <;> simp [threshold, key] at eq ⊢ <;> omega
      have emitted : MarkFeedback.emitted C.model head.probe head.decision = head.children := by
        have children := congrArg Transaction.children rowShape
        rw [children]
        cases hc : head.fireDate with
        | none => simp [Transaction.decision, hc, reciprocalRow, MarkFeedback.emitted]
        | some clock =>
          have same := fireClocks head mem clock (by simp [hc])
          simp [Transaction.decision, hc, reciprocalRow, MarkFeedback.emitted, C,
            Calendar.model, reciprocalCalendar, same]
      refine ⟨by rw [limits.1, limits.2]; decide, ?_, ?_, emitted, ?_⟩
      · change RoutedCalendar.HasRoom (MarkFeedback.score C.model 2 ⟨[], counts⟩ head.probe) head.lo head.hi
        rw [limits.1, limits.2]
        rcases branches with ⟨_, negative⟩ | ⟨_, positive⟩
        · exact Or.inl ⟨negative, by simpa⟩
        · exact Or.inr ⟨by omega, by omega⟩
      · change MarkFeedback.read C.model 2 ⟨[], counts⟩ head.probe 0 = _
        unfold MarkFeedback.read
        rcases branches with ⟨decision, negative⟩ | ⟨decision, positive⟩
        · rw [decision]
          exact decide_eq_false (by omega)
        · rw [decision]
          exact decide_eq_true (by omega)
      · have step : writesAfter C (past ++ [head]) (fun _ => 0) =
            (fun j => counts j + MarkFeedback.footprint C.model head.probe head.decision j) := by
          simp only [writesAfter, List.foldl_append, List.foldl_cons, List.foldl_nil, counts]
        rw [← step]
        exact ih (past ++ [head]) (by simpa using split)
  exact go [] rows rfl

private theorem rowWindow (fire : ReciprocalProbe → ℝ) (span : ℝ) (key : ReciprocalInput)
    (later : 178 ≤ span) : (reciprocalCalendar fire).phase key span = .ready := by
  classical
  have not32 : span ≠ 32 := by linarith
  simp [reciprocalCalendar, not32, not_lt.mpr later]

private theorem firing_no_write (fire : ReciprocalProbe → ℝ) (i : Fin 6) {row : Row}
    (fired : row.decision = true) :
    gainWrites (reciprocalCalendar fire) i row = false ∧
      markWrites (reciprocalCalendar fire) i row = false := by
  simp [gainWrites, markWrites, fired, Calendar.model, reciprocalCalendar]

private def readyDose (fire : ReciprocalProbe → ℝ) (row : Row) (i : Fin 6) : Prop :=
  row.decision = false ∧ (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready ∧
    MarkFeedback.gain (reciprocalCalendar fire).model row.probe = i

private theorem gainWrites_iff (fire : ReciprocalProbe → ℝ) (row : Row) (i : Fin 6) :
    gainWrites (reciprocalCalendar fire) i row = true ↔ readyDose fire row i := by
  change ((!row.decision && decide ((reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready)) &&
    decide (MarkFeedback.gain (reciprocalCalendar fire).model row.probe = i)) = true ↔ _
  simp [readyDose, and_assoc]

private theorem recoveryWrites_iff (fire : ReciprocalProbe → ℝ) (row : Row) (i : Fin 6) :
    markWrites (reciprocalCalendar fire) i row = true ↔
      row.decision = false ∧ (reciprocalCalendar fire).phase row.probe.input row.probe.due = .slow ∧
      MarkFeedback.recovery (reciprocalCalendar fire).model row.probe = i := by
  change ((decide ((reciprocalCalendar fire).phase row.probe.input row.probe.due = .slow) && !row.decision) &&
    decide (MarkFeedback.recovery (reciprocalCalendar fire).model row.probe = i)) = true ↔ _
  simp [and_left_comm, and_comm]

private theorem gainIndex_eq (fire : ReciprocalProbe → ℝ) (p : ReciprocalProbe) :
    MarkFeedback.gain (reciprocalCalendar fire).model p =
      (Address.mk p.input.1 (if p.input.2 = 2 then .port1 else .port0)).encode := by
  classical
  simp [MarkFeedback.gain, Calendar.model, reciprocalCalendar]

private theorem explicitCounts (fire : ReciprocalProbe → ℝ)
    (a0 a2 b1 b2 : List Row) (rest : List Row) (marks : List Row)
    (sizes : a0.length = 3 ∧ a2.length = 3 ∧ b1.length = 1 ∧ b2.length = 3)
    (gain0 : ∀ row ∈ a0, row.probe.input = (0, 0) ∧ row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready)
    (gain2 : ∀ row ∈ a2, row.probe.input = (0, 2) ∧ row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready)
    (gain1 : ∀ row ∈ b1, row.probe.input = (1, 1) ∧ row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready)
    (gain3 : ∀ row ∈ b2, row.probe.input = (1, 2) ∧ row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready)
    (firing : ∀ row ∈ rest, row.decision = true)
    (marksPhase : ∀ row ∈ marks, row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .slow)
    (markBalance : ∀ i : Fin 2, (marks.filter (fun row => row.probe.input.1 = i)).length = 1)
    (keys : ∀ row ∈ a0 ++ a2 ++ b1 ++ b2 ++ rest ++ marks, row.probe.input = (0, 0) ∨
      row.probe.input = (0, 2) ∨ row.probe.input = (1, 1) ∨ row.probe.input = (1, 2)) :
    let table := a0 ++ a2 ++ b1 ++ b2 ++ rest ++ marks
    (∀ i : Fin 2, ∀ c : Coordinate, writesAfter (reciprocalCalendar fire) table (fun _ => 0)
      (Address.mk i c).encode = doseCount i c) ∧
    (∀ row ∈ table, table.countP
        (gainWrites (reciprocalCalendar fire) (MarkFeedback.gain (reciprocalCalendar fire).model row.probe)) =
      if row.probe.input = (1, 1) then 1 else 3) := by
  classical
  let C := reciprocalCalendar fire
  let table := a0 ++ a2 ++ b1 ++ b2 ++ rest ++ marks
  have group (rows : List Row) (key : ReciprocalInput) (i : Fin 6)
      (all : ∀ row ∈ rows, row.probe.input = key ∧ row.decision = false ∧ C.phase row.probe.input row.probe.due = .ready) :
      rows.countP (gainWrites C i) =
        if (Address.mk key.1 (if key.2 = 2 then .port1 else .port0)).encode = i then rows.length else 0 := by
    by_cases same : (Address.mk key.1 (if key.2 = 2 then .port1 else .port0)).encode = i
    · rw [ite_eq_left same]
      apply List.countP_eq_length.mpr
      intro row mem
      obtain ⟨keyEq, silent, ready⟩ := all row mem
      exact (gainWrites_iff fire row i).mpr ⟨silent, ready, by rw [gainIndex_eq, keyEq]; exact same⟩
    · rw [ite_eq_right same]
      apply List.countP_eq_zero.mpr
      intro row mem
      have keyEq := (all row mem).1
      intro written
      have addr := ((gainWrites_iff fire row i).mp written).2.2
      rw [gainIndex_eq, keyEq] at addr
      exact same addr
  have noGainRest (i : Fin 6) : rest.countP (gainWrites C i) = 0 := by
    apply List.countP_eq_zero.mpr
    intro row mem
    intro yes
    have no := (firing_no_write fire i (firing row mem)).1
    exact Bool.noConfusion (no.symm.trans yes)
  have noGainMark (i : Fin 6) : marks.countP (gainWrites C i) = 0 := by
    apply List.countP_eq_zero.mpr
    intro row mem written
    have ready := ((gainWrites_iff fire row i).mp written).2.1
    rw [(marksPhase row mem).2] at ready
    contradiction
  have gains (i : Fin 6) :
      table.countP (gainWrites C i) =
        (if i = 0 then 3 else 0) + (if i = 1 then 3 else 0) +
        (if i = 3 then 1 else 0) + (if i = 4 then 3 else 0) := by
    simp only [table, List.countP_append, noGainRest, noGainMark, Nat.add_zero,
      group a0 (0, 0) i gain0, group a2 (0, 2) i gain2,
      group b1 (1, 1) i gain1, group b2 (1, 2) i gain3,
      sizes.1, sizes.2.1, sizes.2.2.1, sizes.2.2.2]
    fin_cases i <;> decide
  have noMarkReady (rows : List Row) (i : Fin 6)
      (all : ∀ row ∈ rows, C.phase row.probe.input row.probe.due = .ready) :
      rows.countP (markWrites C i) = 0 := by
    apply List.countP_eq_zero.mpr
    intro row mem marked
    have slow := ((recoveryWrites_iff fire row i).mp marked).2.1
    rw [all row mem] at slow
    contradiction
  have noMarkRest (i : Fin 6) : rest.countP (markWrites C i) = 0 := by
    apply List.countP_eq_zero.mpr
    intro row mem
    intro yes
    have no := (firing_no_write fire i (firing row mem)).2
    exact Bool.noConfusion (no.symm.trans yes)
  have recover (i : Fin 2) : marks.countP (markWrites C (Address.mk i .recovery).encode) = 1 := by
    rw [List.countP_eq_length_filter, ← markBalance i]
    congr 1
    apply List.filter_congr
    intro row mem
    have evidence := marksPhase row mem
    apply Bool.eq_iff_iff.mpr
    rw [recoveryWrites_iff]
    simp only [evidence.1, evidence.2, true_and, decide_eq_true_eq]
    refine ⟨fun eq => ?_, fun eq => ?_⟩
    · exact congrArg Address.cell (AutonomousFeedback.Schedule.PortMemory.address_encode_injective _ _ eq)
    · change (Address.mk row.probe.input.1 .recovery).encode = _
      rw [eq]
  refine ⟨?_, ?_⟩
  · intro i c
    rw [countFold, gains]
    have marksOnly : table.countP (markWrites C (Address.mk i c).encode) =
        marks.countP (markWrites C (Address.mk i c).encode) := by
      change (a0 ++ a2 ++ b1 ++ b2 ++ rest ++ marks).countP (markWrites C _) = _
      rw [List.countP_append, List.countP_append, List.countP_append, List.countP_append, List.countP_append,
        noMarkRest, noMarkReady a0 _ (fun row mem => (gain0 row mem).2.2),
        noMarkReady a2 _ (fun row mem => (gain2 row mem).2.2),
        noMarkReady b1 _ (fun row mem => (gain1 row mem).2.2),
        noMarkReady b2 _ (fun row mem => (gain3 row mem).2.2)]
      simp only [Nat.zero_add]
    rw [marksOnly]
    cases c with
    | port0 =>
      have zero : marks.countP (markWrites C (Address.mk i .port0).encode) = 0 := by
        apply List.countP_eq_zero.mpr
        intro row _
        intro yes
        exact Bool.noConfusion ((markWrites_ne_gain fire i false row).symm.trans yes)
      rw [zero]
      fin_cases i <;> norm_num [Address.encode, Coordinate.index, doseCount]
    | port1 =>
      have zero : marks.countP (markWrites C (Address.mk i .port1).encode) = 0 := by
        apply List.countP_eq_zero.mpr
        intro row _
        intro yes
        exact Bool.noConfusion ((markWrites_ne_gain fire i true row).symm.trans yes)
      rw [zero]
      fin_cases i <;> norm_num [Address.encode, Coordinate.index, doseCount]
    | recovery =>
      rw [recover]
      fin_cases i <;> norm_num [Address.encode, Coordinate.index, doseCount]
  · intro row member
    rw [gains, gainIndex_eq]
    rcases keys row member with h | h | h | h <;> rw [h] <;> decide

private theorem gainKey_injective_on_protocol (a b : ReciprocalInput)
    (ha : a = (0, 0) ∨ a = (0, 2) ∨ a = (1, 1) ∨ a = (1, 2))
    (hb : b = (0, 0) ∨ b = (0, 2) ∨ b = (1, 1) ∨ b = (1, 2))
    (h : (Address.mk a.1 (if a.2 = 2 then .port1 else .port0)).encode =
      (Address.mk b.1 (if b.2 = 2 then .port1 else .port0)).encode) :
    a = b := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | have values := congrArg Fin.val h
      simp [Address.encode, Coordinate.index] at values

private theorem canonicalOrder (execution : NominalEpoch) (orderedRows : List Row)
    (eq : orderedRows.map Transaction.probe = (stagedDeliveries execution).map reciprocalOccurrence)
    (before : ∀ d ∈ execution.staged.before.deliveries, d.due < (160 : ℝ))
    (birth : execution.staged.afterBirth.time = 160) :
    orderedRows.Pairwise (fun a b => a.probe.due ≤ b.probe.due) := by
  have timing : (stagedDeliveries execution).Pairwise (fun a b => a.due ≤ b.due) := by
    unfold stagedDeliveries
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr execution.staged.before.deliveries_chronological,
      execution.staged.after.deliveries_chronological, ?_⟩
    intro token mem next hn
    obtain ⟨old, seen, rfl⟩ := List.mem_map.mp mem
    have later := (execution.staged.after.delivery_time_bounds next hn).1
    rw [birth] at later
    exact (before old seen).le.trans later
  have mapped : (orderedRows.map Transaction.probe).Pairwise (fun a b => a.due ≤ b.due) := by
    rw [eq]
    exact List.pairwise_map.mpr timing
  exact (List.pairwise_map (f := Transaction.probe)).mp mapped

set_option maxHeartbeats 30000000 in
/-- A single staged native history realizes the entire reciprocal
admission list and FIRE multiset. Each FIRE row retains its native clock. -/
theorem nominal_reciprocal_transaction_words :
    ∃ (epoch : NominalEpoch) (rows : List Row) (fire : ReciprocalProbe → ℝ),
      rows.length = 77 ∧
      rows.map Transaction.probe = (stagedDeliveries epoch).map reciprocalOccurrence ∧
      (Transaction.fires Prod.fst rows).Perm (stagedFires epoch) ∧
      (∀ tx ∈ rows, tx = reciprocalRow tx.probe tx.fireDate) ∧
      (∀ p, p.due ≤ fire p ∧ fire p < p.due + 1) ∧
      (∀ tx ∈ rows, ∀ t ∈ tx.fireDate, fire tx.probe = t) ∧
      ((epoch.staged.before.ledger.emissions.map (fun event => (event.1.castSucc, event.2))).flatMap
        (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2) = []) ∧
      RowGuards (reciprocalCalendar fire) 2 rows (fun _ => 0) ∧
      (∀ i : Fin 2, ∀ coord : Coordinate,
        writesAfter (reciprocalCalendar fire) rows (fun _ => 0) (Address.mk i coord).encode = doseCount i coord) := by
  have born : BirthState nominalStart := Newborn.nominal_birth_state
  have delay : ∀ t, (3 / 10 : ℝ) ≤ nominalDelay t ∧ nominalDelay t ≤ 2 / 5 :=
    fun _ => by norm_num [nominalDelay]
  obtain ⟨c, b, r, s, v, f, g, u, t, x, z, w, a, q, p, _, _, hA, hB, hownA, hownB⟩ :=
    birth_protocol_first_reverse_interleaved_pair_exists born nominal_box (fun _ => rfl) rfl
      Newborn.nominal nominalDelay nominalDelay delay delay
  have low : Real.log (3 / 10) - 1 / 100000 ≤ q.final.x 0 (.z 2) ∧
      q.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [z.first_reverse_wire_a_gain_own nominal_box.extend_old q 2 (by decide)]
    simpa [nominalGain] using ((born.2.2 0).2.2.2.2 (2 : Port)).1
  have high : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2 := by
    rw [z.feedback_weak_b_gain_own w]
    have bounds := Newborn.nominal.gain (2 : Port)
    simp only [nominalGain, show (2 : Port) ≠ 1 by decide, ite_false] at bounds
    exact learned_gain_bounds (by linarith [bounds.1]) (by linarith [bounds.2])
  obtain ⟨entry, learned, f352, f360, f368, returnFire, rSend, rRecv, reverseRows, rs, rr,
    reverseShape, reverseDates, reverseFires, reverseClocks, reverseLate⟩ := reverse_transaction_table p nominal_box low high
  let finish : ReverseTeachingCompletion p := {
    entry := entry
    epoch := learned
    final := learned.final
    execution := entry.execution.append (learned.execution.cast_parameters a.parameters_product)
    date := learned.date
    prepared := learned.prepared
    charge := learned.charge
    raw_none := learned.raw_none
    pending := learned.pending
    a_gain_target := (learned.gains 0 2).trans entry.a_gain_target
    a_gain_other := fun port hp => (learned.gains 0 port).trans (entry.a_gain_other port hp)
    b_gains := fun port => (learned.gains 1 port).trans (entry.b_gains port)
    recovery := fun i => (learned.recovery i).trans (entry.recovery i)
    a_emission_count := by
      rw [Execution.emissionTimes_append, List.length_append, entry.a_emission_count]
      have same := learned.a_emission_count
      simpa only [Execution.emissionTimes, Execution.cast_parameters_ledger] using congrArg (1 + ·) same
    b_emission_count := by
      rw [Execution.emissionTimes_append, List.length_append, entry.b_emission_count]
      have same := learned.b_emission_count
      simpa only [Execution.emissionTimes, Execution.cast_parameters_ledger] using congrArg (3 + ·) same
    physical := by simpa only [a.parameters_product] using learned.physical
    raw_valid := learned.raw_valid
    complete := learned.complete
  }
  have hcomplete : CompleteThrough (z.reverse_teaching_staged finish).after (4599 / 10) := by
    simpa only [CompleteThrough] using finish.complete
  let native : NominalEpoch := by
    refine {
      final := finish.final, staged := z.reverse_teaching_staged finish
      newborn_origin := b.newborn_state
      sources_origin := b.source_list
      date := finish.date
      prepared := finish.prepared
      charge := finish.charge
      raw_none := finish.raw_none
      pending := finish.pending
      a_emission_count := ?_
      b_emission_count := ?_
      a_gain_target := ?_
      a_gain_first := ?_
      a_gain_other := ?_
      b_gain_target := ?_
      b_gain_first := ?_
      b_gain_other := ?_
      a_recovery := ?_
      b_recovery := ?_
      physical := finish.physical
      raw_valid := finish.raw_valid
      complete := hcomplete
    }
    · simp only [FirstCoupledTeaching.reverse_teaching_staged,Execution.emissionTimes_append,
        List.length_append,finish.a_emission_count]
      simp only [List.length_append] at hA
      omega
    · simp only [FirstCoupledTeaching.reverse_teaching_staged,Execution.emissionTimes_append,
        List.length_append,finish.b_emission_count]
      omega
    · rw [finish.a_gain_target,hownA]; ring
    · rw [finish.a_gain_other 0 (by decide),p.a_gain_other 0 (by decide),q.gains,a.gains,
        w.gain_other 0 0 (Or.inl (by decide)),z.a_gain_target nominal_box.extend_old]
    · intro port hp0 hp2
      rw [finish.a_gain_other port hp2,p.a_gain_other port hp2,q.gains,a.gains,
        w.gain_other 0 port (Or.inl (by decide)),z.a_gain_other nominal_box.extend_old port hp0]
    · rw [finish.b_gains,hownB]
    · rw [finish.b_gains,p.b_gains,w.gain_other 1 1 (Or.inr (by decide)),z.b_gain_target nominal_box delay]
    · intro port hp1 hp2
      rw [finish.b_gains,p.b_gains,w.gain_other 1 port (Or.inr hp2),z.b_gain_other port hp1]
    · rw [finish.recovery,p.a_recovery,q.recovery,a.recovery,w.recovery,z.a_recovery_own nominal_box.extend_old]
    · rw [finish.recovery,p.b_recovery,z.b_recovery_own]

  have sameBefore : native.staged.before.deliveries = (c.execution.append b.wait).deliveries :=
    by rfl
  have samePreFires : native.staged.before.ledger.emissions = (c.execution.append b.wait).ledger.emissions :=
    by rfl
  have actualAfter : native.staged.after = z.staged.after.append ((reverseHead p).append finish.execution) := by
    change ((((z.staged.after.append w.execution).append a.execution).append q.execution).append
      p.execution).append finish.execution =
      z.staged.after.append ((reverseHead p).append finish.execution)
    simp only [reverseHead, Execution.append_assoc]
  have sameAfter := congrArg (fun e => e.deliveries) actualAfter
  have samePostFires := congrArg (fun e => e.ledger.emissions) actualAfter
  have birthDate : native.staged.afterBirth.time = 160 := b.after_date
  rw [Execution.deliveries_append, b.wait_deliveries, List.append_nil] at sameBefore
  rw [Execution.emissions_append, b.wait_emissions, List.append_nil] at samePreFires
  obtain ⟨strong, prepared, birthRows, _, cert, birthShape, birthDates, birthFires, birthBand, birthClocks⟩ :=
    birth_transaction_table c
  obtain ⟨fSend, fRecv, forwardRows, fs, fr, forwardShape, forwardDates, forwardFires, forwardClocks, forwardLate⟩ :=
    forward_transaction_table z nominal_box
  have beforeClose : ∀ token ∈ native.staged.before.deliveries, token.due < (160 : ℝ) := by
    intro token ht
    have loaded : reciprocalOccurrence (liftDelivery token) ∈ birthRows.map Transaction.probe := by
      rw [birthDates, ← sameBefore]
      exact List.mem_map.mpr ⟨liftDelivery token, List.mem_map_of_mem ht, rfl⟩
    obtain ⟨row, present, eq⟩ := List.mem_map.mp loaded
    have cap := (birthBand row present).1.2
    rw [eq] at cap
    change token.due ≤ 120 at cap
    linarith
  have preClosed : (native.staged.before.ledger.emissions.map (fun event => (event.1.castSucc, event.2))).flatMap
      (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2) = [] := by
    rw [samePreFires, ← birthFires]
    apply List.flatMap_eq_nil_iff.mpr
    intro event mem
    obtain ⟨row, member, picked⟩ := List.mem_filterMap.mp mem
    cases h : row.fireDate with
    | none => simp [h] at picked
    | some clock =>
      have eq : (row.probe.input.1, clock) = event := by simpa [h] using picked
      subst event
      have input := congrArg Prod.fst (birthBand row member).1.1
      have bounds := birthClocks row member clock (by simp [h])
      have cap := (birthBand row member).1.2
      have early : ¬ (160 : ℝ) ≤ clock := by linarith [bounds.2]
      have other : (0 : Fin 2) ≠ 1 := by decide
      simp [reciprocalEntryRouter, Contact.route, teachingContact, feedbackContact, input, other, early]
  let table := birthRows ++ forwardRows ++ reverseRows
  have budget : (table.map Transaction.probe).Perm ((stagedDeliveries native).map reciprocalOccurrence) := by
    have appendDates := Execution.deliveries_append z.staged.after ((reverseHead p).append finish.execution)
    rw [stagedDeliveries, sameBefore, sameAfter.trans appendDates]
    simp only [table, List.map_append]
    rw [← birthDates]
    simpa only [List.append_assoc] using (forwardDates.append reverseDates).append_left
      (birthRows.map Transaction.probe)
  obtain ⟨rows, alignment, admitted⟩ := alignRows table _ budget
  have limits : ∀ tx ∈ rows, ∀ clock ∈ tx.fireDate, tx.probe.due ≤ clock ∧ clock < tx.probe.due + 1 := by
    intro tx ht clock hc
    have mem := alignment.mem_iff.mp ht
    rcases List.mem_append.mp mem with earlier | last
    · rcases List.mem_append.mp earlier with early | middle
      · exact birthClocks tx early clock hc
      · exact forwardClocks tx middle clock hc
    · exact reverseClocks tx last clock hc
  obtain ⟨fire, causal, exactFire⟩ := clockOfRows_exists rows
    (admitted ▸ stagedOccurrenceNodup native beforeClose birthDate) limits
  have exactShape : ∀ tx ∈ rows, tx = reciprocalRow tx.probe tx.fireDate := by
    intro tx ht
    have mem := alignment.mem_iff.mp ht
    rcases List.mem_append.mp mem with earlier | last
    · rcases List.mem_append.mp earlier with early | middle
      · rw [birthShape] at early
        rcases List.mem_append.mp early with head | tail
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at head
          rcases head with rfl | rfl | rfl | rfl | rfl <;> rfl
        · exact firingRows_shape 0 0 prepared tx tail
      · rw [forwardShape] at middle
        rcases List.mem_append.mp middle with head | tail
        · rcases List.mem_append.mp head with first | snd
          · simp only [forwardEntryRows, List.mem_cons, List.not_mem_nil, or_false] at first
            rcases first with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
          · exact firingRows_shape 0 0 fSend tx snd
        · exact firingRows_shape 1 1 fRecv tx tail
    · rw [reverseShape] at last
      rcases List.mem_append.mp last with head | tail
      · rcases List.mem_append.mp head with first | snd
        · simp only [reverseEntryRows, List.mem_cons, List.not_mem_nil, or_false] at first
          rcases first with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
        · exact firingRows_shape 1 2 rSend tx snd
      · exact firingRows_shape 0 2 rRecv tx tail
  have preparedCount : prepared.length = 11 := by
    have count := congrArg List.length cert.delivery_word
    simp [Execution.cellDeliveries, c.deliveries_suffix, sourceTrain] at count
    exact count
  have tableLength : table.length = 77 := by
    simp [table, birthShape, forwardShape, reverseShape, firingRows, preparedCount, fs, fr, rs, rr,
      forwardEntryRows, reverseEntryRows]
  have firePerm : (Transaction.fires Prod.fst rows).Perm (stagedFires native) := by
    have move := alignment.filterMap (fun tx => tx.fireDate.map (fun date => (tx.probe.input.1, date)))
    refine move.trans ?_
    have appendFires := Execution.emissions_append z.staged.after ((reverseHead p).append finish.execution)
    rw [stagedFires, samePreFires, samePostFires.trans appendFires, ← birthFires]
    simp only [table, Transaction.fires, List.filterMap_append]
    simpa only [List.append_assoc, Transaction.fires] using (forwardFires.append reverseFires).append_left
      (Transaction.fires Prod.fst birthRows)

  let gainsA0 : List Row := [reciprocalRow ⟨0, 0, 0⟩ none,
    reciprocalRow ⟨8, 0, 0⟩ none, reciprocalRow ⟨16, 0, 0⟩ none]
  let gainsA2 : List Row := [reciprocalRow ⟨a.final.time + 7 / 20, 0, 2⟩ none,
    reciprocalRow ⟨f352 + 7 / 20, 0, 2⟩ none, reciprocalRow ⟨f360 + 7 / 20, 0, 2⟩ none]
  let gainsB1 : List Row := [reciprocalRow ⟨r.final.time, 1, 1⟩ none]
  let gainsB2 : List Row := [reciprocalRow ⟨320, 1, 2⟩ none, reciprocalRow ⟨328, 1, 2⟩ none,
    reciprocalRow ⟨336, 1, 2⟩ none]
  let marked : List Row := [reciprocalRow ⟨32, 0, 0⟩ none, reciprocalRow ⟨t.final.time, 1, 1⟩ none]
  let fixedFires :=
    firingRows 0 0 [(24, strong), (160, r.fire.final.time), (168, v.fire.final.time), (176, t.fire.final.time)] ++
    firingRows 1 1 [(v.final.time, f.final.time)] ++
    firingRows 1 2 [(344, a.final.time), (352, f352), (360, f360), (368, f368)] ++
    firingRows 0 2 [(f368 + 7 / 20, returnFire)]
  let firedRows := fixedFires ++ firingRows 0 0 prepared ++ firingRows 0 0 fSend ++
    firingRows 1 1 fRecv ++ firingRows 1 2 rSend ++ firingRows 0 2 rRecv
  let classified := gainsA0 ++ gainsA2 ++ gainsB1 ++ gainsB2 ++ firedRows ++ marked
  have perm : rows.Perm classified := by
    apply alignment.trans
    let block : Nat → List Row
      | 0 => [reciprocalRow ⟨0, 0, 0⟩ none]
      | 1 => [reciprocalRow ⟨8, 0, 0⟩ none]
      | 2 => [reciprocalRow ⟨16, 0, 0⟩ none]
      | 3 => [reciprocalRow ⟨24, 0, 0⟩ (some strong)]
      | 4 => [reciprocalRow ⟨32, 0, 0⟩ none]
      | 5 => [reciprocalRow ⟨160, 0, 0⟩ (some r.fire.final.time)]
      | 6 => [reciprocalRow ⟨r.final.time, 1, 1⟩ none]
      | 7 => [reciprocalRow ⟨168, 0, 0⟩ (some v.fire.final.time)]
      | 8 => [reciprocalRow ⟨v.final.time, 1, 1⟩ (some f.final.time)]
      | 9 => [reciprocalRow ⟨176, 0, 0⟩ (some t.fire.final.time)]
      | 10 => [reciprocalRow ⟨t.final.time, 1, 1⟩ none]
      | 11 => [reciprocalRow ⟨320, 1, 2⟩ none]
      | 12 => [reciprocalRow ⟨328, 1, 2⟩ none]
      | 13 => [reciprocalRow ⟨336, 1, 2⟩ none]
      | 14 => [reciprocalRow ⟨344, 1, 2⟩ (some a.final.time)]
      | 15 => [reciprocalRow ⟨a.final.time + 7 / 20, 0, 2⟩ none]
      | 16 => [reciprocalRow ⟨352, 1, 2⟩ (some f352)]
      | 17 => [reciprocalRow ⟨f352 + 7 / 20, 0, 2⟩ none]
      | 18 => [reciprocalRow ⟨360, 1, 2⟩ (some f360)]
      | 19 => [reciprocalRow ⟨f360 + 7 / 20, 0, 2⟩ none]
      | 20 => [reciprocalRow ⟨368, 1, 2⟩ (some f368)]
      | 21 => [reciprocalRow ⟨f368 + 7 / 20, 0, 2⟩ (some returnFire)]
      | 22 => firingRows 0 0 prepared
      | 23 => firingRows 0 0 fSend
      | 24 => firingRows 1 1 fRecv
      | 25 => firingRows 1 2 rSend
      | 26 => firingRows 0 2 rRecv
      | _ => []
    have layout : ([0, 1, 2, 3, 4, 22, 5, 6, 7, 8, 9, 10, 23, 24, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 25, 26] : List Nat).Perm [0, 1, 2, 15, 17, 19, 6, 11, 12, 13, 3, 5, 7, 9, 8, 14, 16, 18, 20, 21, 22, 23, 24, 25, 26, 4, 10] := by decide
    have moved := layout.flatMap_right block
    simpa only [table, birthShape, forwardShape, reverseShape, classified, gainsA0, gainsA2,
      gainsB1, gainsB2, firedRows, fixedFires, marked, forwardEntryRows, reverseEntryRows,
      List.flatMap_cons, List.flatMap_nil, block, List.singleton_append, List.nil_append,
      List.append_nil, List.append_assoc, List.cons_append,
      firingRows, List.map_cons, List.map_nil] using moved
  have actualForward : 160 < r.final.time ∧ r.final.time < 162 := by
    exact ⟨by linarith [(r.date_bounds delay).1], by linarith [(r.date_bounds delay).2]⟩
  have actualSecond : 168 < v.final.time ∧ v.final.time < 170 := by
    exact ⟨by linarith [(v.date_bounds delay).1], by linarith [(v.date_bounds delay).2]⟩
  have actualSlow : 176 < t.final.time ∧ t.final.time < 178 := by
    exact ⟨by linarith [(t.date_bounds delay).1], by linarith [(t.date_bounds delay).2]⟩
  have reverseTiming (r : ℝ) (due : ℝ)
      (mem : reciprocalRow ⟨due, 1, 2⟩ (some r) ∈ reverseRows) :
      due ≤ r ∧ r < due + 1 :=
    reverseClocks _ mem r (by simp [reciprocalRow])
  have bound344 := reverseTiming a.final.time 344 (by simp [reverseShape, reverseEntryRows])
  have bound352 := reverseTiming f352 352 (by simp [reverseShape, reverseEntryRows])
  have bound360 := reverseTiming f360 360 (by simp [reverseShape, reverseEntryRows])
  have bound368 := reverseTiming f368 368 (by simp [reverseShape, reverseEntryRows])
  have readyA0 : ∀ row ∈ gainsA0, row.probe.input = (0, 0) ∧ row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready := by
    intro row mem
    simp only [gainsA0, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;>
      norm_num [reciprocalCalendar, reciprocalRow, Transaction.decision]
  have readyA2 : ∀ row ∈ gainsA2, row.probe.input = (0, 2) ∧ row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready := by
    intro row mem
    simp only [gainsA2, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;>
      exact ⟨rfl, rfl, rowWindow fire _ _ (by simp only [reciprocalRow]; linarith [bound344.1, bound352.1, bound360.1])⟩
  have readyB1 : ∀ row ∈ gainsB1, row.probe.input = (1, 1) ∧ row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready := by
    intro row mem
    obtain rfl := List.mem_singleton.mp mem
    have early : ¬ (176 : ℝ) < r.final.time := by linarith [actualForward.2]
    exact ⟨rfl, rfl, by simp [reciprocalCalendar, reciprocalRow, early]⟩
  have readyB2 : ∀ row ∈ gainsB2, row.probe.input = (1, 2) ∧ row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready := by
    intro row mem
    simp only [gainsB2, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;>
      exact ⟨rfl, rfl, rowWindow fire _ _ (by norm_num [reciprocalRow])⟩
  have markPhase : ∀ row ∈ marked, row.decision = false ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .slow := by
    intro row mem
    simp only [marked, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨rfl, by simp [reciprocalCalendar, reciprocalRow]⟩
    · exact ⟨rfl, by simp [reciprocalCalendar, reciprocalRow, actualSlow.1, actualSlow.2]⟩
  have firedPhase : ∀ row ∈ firedRows, row.decision = true ∧
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready := by
    intro row mem
    have always {i p word} : ∀ row ∈ firingRows i p word, row.decision = true := by
      intro row mem
      obtain ⟨clocks, _, rfl⟩ := List.mem_map.mp mem
      rfl
    have later {i p word} {min : ℝ} (bound : 178 ≤ min) (subset : ∀ row ∈ firingRows i p word, min ≤ row.probe.due)
        (row : Row) (mem : row ∈ firingRows i p word) :
        row.decision = true ∧ (reciprocalCalendar fire).phase row.probe.input row.probe.due = .ready :=
      ⟨always row mem, rowWindow fire _ _ (bound.trans (subset row mem))⟩
    simp only [firedRows, List.mem_append] at mem
    rcases mem with (((((fixed | born) | fA) | fB) | rB) | rA)
    · have early : ¬ (176 : ℝ) < v.final.time := by linarith [actualSecond.2]
      simp only [fixedFires, firingRows, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact ⟨rfl, rowWindow fire _ _ (by change 178 ≤ f368 + 7 / 20; linarith [bound368.1])⟩
        | exact ⟨rfl, by norm_num [reciprocalCalendar, reciprocalRow, early]⟩
    · obtain ⟨clocks, seen, rfl⟩ := List.mem_map.mp born
      have dates := cert.delivery_word
      have deadline : 40 ≤ clocks.1 := by
        have member : clocks.1 ∈ prepared.map Prod.fst := List.mem_map_of_mem seen
        rw [dates, c.at40.date] at member
        rcases List.mem_cons.mp member with eq | tail
        · rw [eq]
        · obtain ⟨token, present, eq⟩ := List.mem_map.mp tail
          rw [← eq]
          have h := (c.suffix.delivery_time_bounds token (List.mem_filter.mp present).1).1
          rwa [c.at40.date] at h
      have ne : clocks.1 ≠ 32 := by linarith
      exact ⟨rfl, by simp [reciprocalCalendar, reciprocalRow, ne]⟩
    · exact later (by norm_num : (178 : ℝ) ≤ 184) (fun p mem => forwardLate p (List.mem_append_left _ mem)) row fA
    · exact later (by norm_num : (178 : ℝ) ≤ 184) (fun p mem => forwardLate p (List.mem_append_right _ mem)) row fB
    · exact later (by norm_num : (178 : ℝ) ≤ 376) (fun p mem => reverseLate p (List.mem_append_left _ mem)) row rB
    · exact later (by norm_num : (178 : ℝ) ≤ 376) (fun p mem => reverseLate p (List.mem_append_right _ mem)) row rA
  have firedPK : ∀ row ∈ firedRows, row.probe.input = (0, 0) ∨ row.probe.input = (0, 2) ∨
      row.probe.input = (1, 1) ∨ row.probe.input = (1, 2) := by
    intro row mem
    simp only [firedRows, fixedFires, List.mem_append] at mem
    rcases mem with ((((((((p0 | p1) | p2) | p3) | p0') | p0'') | p1') | p2') | p3')
    all_goals
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp ‹_›
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
        exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr rfl))
  have keys : ∀ row ∈ classified, row.probe.input = (0, 0) ∨ row.probe.input = (0, 2) ∨
      row.probe.input = (1, 1) ∨ row.probe.input = (1, 2) := by
    intro row mem
    simp only [classified, List.mem_append] at mem
    rcases mem with (((((m | m) | m) | m) | m) | m)
    · exact Or.inl (readyA0 row m).1
    · exact Or.inr (Or.inl (readyA2 row m).1)
    · exact Or.inr (Or.inr (Or.inl (readyB1 row m).1))
    · exact Or.inr (Or.inr (Or.inr (readyB2 row m).1))
    · exact firedPK row m
    · simp only [marked, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨counts, totals⟩ := explicitCounts fire gainsA0 gainsA2 gainsB1 gainsB2 firedRows marked
    (by exact ⟨rfl, rfl, rfl, rfl⟩) readyA0 readyA2 readyB1 readyB2 (fun p mem => (firedPhase p mem).1) markPhase
    (by intro i; fin_cases i <;> rfl) keys
  have countsRows (i : Fin 2) (coord : Coordinate) :
      writesAfter (reciprocalCalendar fire) rows (fun _ => 0) (Address.mk i coord).encode = doseCount i coord := by
    calc
      _ = writesAfter (reciprocalCalendar fire) classified (fun _ => 0) (Address.mk i coord).encode := by
        rw [countFold, countFold, List.Perm.countP_eq _ perm, List.Perm.countP_eq _ perm]
      _ = _ := counts i coord
  have totalsRows : ∀ row ∈ rows, rows.countP
      (gainWrites (reciprocalCalendar fire) (MarkFeedback.gain (reciprocalCalendar fire).model row.probe)) =
      if row.probe.input = (1, 1) then 1 else 3 := by
    intro row mem
    rw [List.Perm.countP_eq _ perm]
    exact totals row (perm.mem_iff.mp mem)
  have protectedSilent : ∀ row ∈ rows,
      (reciprocalCalendar fire).phase row.probe.input row.probe.due = .slow → row.decision = false := by
    intro row mem slow
    have member := perm.mem_iff.mp mem
    simp only [classified, List.mem_append] at member
    rcases member with (((((m | m) | m) | m) | m) | m)
    · exact (readyA0 row m).2.1
    · exact (readyA2 row m).2.1
    · exact (readyB1 row m).2.1
    · exact (readyB2 row m).2.1
    · exact Phase.noConfusion ((firedPhase row m).2.symm.trans slow)
    · exact (markPhase row m).1

  have order := canonicalOrder native rows admitted beforeClose birthDate
  have learnedMin (row : Row) (mem : row ∈ firedRows) :
      (row.probe.input = (0, 0) → 24 ≤ row.probe.due) ∧
      (row.probe.input = (0, 2) → f368 + 7 / 20 ≤ row.probe.due) ∧
      (row.probe.input = (1, 1) → v.final.time ≤ row.probe.due) ∧
      (row.probe.input = (1, 2) → 344 ≤ row.probe.due) := by
    simp only [firedRows, List.mem_append] at mem
    rcases mem with (((((fixed | born) | fA) | fB) | rB) | rA)
    · simp only [fixedFires, firingRows, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [reciprocalRow]
    · obtain ⟨clock, seen, rfl⟩ := List.mem_map.mp born
      have dates := cert.delivery_word
      have member : clock.1 ∈ prepared.map Prod.fst := List.mem_map_of_mem seen
      rw [dates, c.at40.date] at member
      norm_num [reciprocalRow]
      rcases List.mem_cons.mp member with eq | tail
      · rw [eq]
        norm_num
      · obtain ⟨token, present, eq⟩ := List.mem_map.mp tail
        have h := (c.suffix.delivery_time_bounds token (List.mem_filter.mp present).1).1
        rw [c.at40.date] at h
        rw [← eq]
        linarith only [h]
    · have h := forwardLate row (List.mem_append_left _ fA)
      obtain ⟨clock, _, rfl⟩ := List.mem_map.mp fA
      norm_num [reciprocalRow] at h ⊢
      linarith only [h]
    · have h := forwardLate row (List.mem_append_right _ fB)
      obtain ⟨clock, _, rfl⟩ := List.mem_map.mp fB
      norm_num [reciprocalRow] at h ⊢
      linarith only [h, actualSecond.2]
    · have h := reverseLate row (List.mem_append_left _ rB)
      obtain ⟨clock, _, rfl⟩ := List.mem_map.mp rB
      norm_num [reciprocalRow] at h ⊢
      linarith only [h]
    · have h := reverseLate row (List.mem_append_right _ rA)
      obtain ⟨clock, _, rfl⟩ := List.mem_map.mp rA
      norm_num [reciprocalRow] at h ⊢
      linarith only [h, bound368.2]
  have trainingFirst : ∀ tx ∈ rows, ∀ learner ∈ rows, tx.decision = true →
      gainWrites (reciprocalCalendar fire) (MarkFeedback.gain (reciprocalCalendar fire).model tx.probe) learner = true →
      learner.probe.due < tx.probe.due := by
    intro tx htx learner hl fired dose
    have fireMember : tx ∈ firedRows := by
      have h := perm.mem_iff.mp htx
      simp only [classified, List.mem_append] at h
      rcases h with (((((m | m) | m) | m) | m) | m)
      · simp [(readyA0 tx m).2.1] at fired
      · simp [(readyA2 tx m).2.1] at fired
      · simp [(readyB1 tx m).2.1] at fired
      · simp [(readyB2 tx m).2.1] at fired
      · exact m
      · simp [(markPhase tx m).1] at fired
    have address := ((gainWrites_iff fire learner _).mp dose).2.2
    rw [gainIndex_eq, gainIndex_eq] at address
    have same := gainKey_injective_on_protocol learner.probe.input tx.probe.input
      (keys learner (perm.mem_iff.mp hl)) (firedPK tx fireMember) address
    have bounds := learnedMin tx fireMember
    have compare (key : ReciprocalInput) (h : learner.probe.input = key) :
        tx.probe.input = key := same.symm.trans h
    have m := perm.mem_iff.mp hl
    simp only [classified, List.mem_append] at m
    rcases m with (((((m | m) | m) | m) | m) | m)
    · have low := bounds.1 (compare (0, 0) (readyA0 learner m).1)
      simp only [gainsA0, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl | rfl <;> exact (lt_of_lt_of_le (by norm_num [reciprocalRow]) low)
    · have low := bounds.2.1 (compare (0, 2) (readyA2 learner m).1)
      simp only [gainsA2, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl | rfl <;>
        simp only [reciprocalRow] <;>
        linarith only [low, bound344.2, bound352.2, bound360.2, bound368.1]
    · have low := bounds.2.2.1 (compare (1, 1) (readyB1 learner m).1)
      obtain rfl := List.mem_singleton.mp m
      change r.final.time < tx.probe.due
      linarith only [low, actualForward.2, actualSecond.1]
    · have low := bounds.2.2.2 (compare (1, 2) (readyB2 learner m).1)
      simp only [gainsB2, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl | rfl <;> exact (lt_of_lt_of_le (by norm_num [reciprocalRow]) low)
    · exact Bool.noConfusion ((firing_no_write fire _ (firedPhase learner m).1).1.symm.trans dose)
    · have fast := ((gainWrites_iff fire learner _).mp dose).2.1
      exact Phase.noConfusion (fast.symm.trans (markPhase learner m).2)
  have guards := guard_of_partition fire rows exactShape exactFire order totalsRows protectedSilent trainingFirst
  exact ⟨native, rows, fire, alignment.length_eq.trans tableLength, admitted, firePerm,
    exactShape, causal, exactFire, preClosed, guards, countsRows⟩

open AutonomousFeedback.Schedule (Config SafeMemory)

/-- The fixed-delay native reciprocal witness refines the dated guarded
model through 459.9. The replay keeps all sixteen future source
occurrences and identifies each modeled native memory coordinate. -/
theorem nominal_reciprocal_refinement :
    ∃ (epoch : NominalEpoch) (rows : List Row) (fire : ReciprocalProbe → ℝ)
      (out : Config 6 ReciprocalProbe),
      CompleteThrough epoch.staged.after (4599 / 10) ∧ rows.length = 77 ∧
      rows.map Transaction.probe = (stagedDeliveries epoch).map reciprocalOccurrence ∧
      (Transaction.fires Prod.fst rows).Perm (stagedFires epoch) ∧
      TransactionReplay (reciprocalCalendar fire) 2 (· ≤ ·)
        (MarkFeedback.initial 2 reciprocalSeed) rows out ∧
      out.pending.Perm ((sourceTrain 1 2 480 8 16).map reciprocalOccurrence) ∧
      out.pending.length = 16 ∧
      SafeMemory 256 2 0 513 (fun _ => 0) out ∧
      NominalTrace (reciprocalCalendar fire) 2 (· ≤ ·) (MarkFeedback.initial 2 reciprocalSeed)
        (Transaction.word rows) out ∧
      (∀ i coord, epoch.final.x i (nativeCoordinate i coord) =
        birthMemory i coord + unitDose coord * out.writes (Address.mk i coord).encode) ∧
      (∀ other word, Trace (reciprocalCalendar fire) 2 (· ≤ ·)
        (MarkFeedback.initial 2 reciprocalSeed) word other →
        (∀ entry ∈ word, entry.1.due ≤ (4599 / 10 : ℝ)) →
        (∀ p ∈ other.pending, (4599 / 10 : ℝ) < p.due) → other.writes = out.writes) := by
  obtain ⟨epoch, rows, fire, size, admissions, fired, shape, latency, clocks, closed, guards, counts⟩ :=
    nominal_reciprocal_transaction_words
  obtain ⟨out, replay, pending, count, safe, nominal, memory, unique⟩ :=
    reciprocal_replay_of_transaction_table epoch fire latency rows admissions fired shape clocks closed guards counts
  rw [epoch.pending] at pending
  exact ⟨epoch, rows, fire, out, epoch.complete, size, admissions, fired, replay,
    pending, count, safe, nominal, memory, unique⟩

end NetworkStability.NativeReciprocal
