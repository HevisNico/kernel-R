import ReciprocalDated
import NativeComposition

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid
open PhaseAdmission
open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

abbrev ReciprocalTransaction := Transaction ℝ ReciprocalInput

/-- Count writes through an ordered list of native transaction rows. -/
def writesAfter (C : Calendar 2 ℝ ReciprocalInput) (rows : List ReciprocalTransaction)
    (before : Fin 6 → Nat) : Fin 6 → Nat :=
  rows.foldl (fun counts tx i =>
    counts i + MarkFeedback.footprint C.model tx.probe tx.decision i) before

/-- Check the guards against the counters at each boundary. The queue
induction can then change the order of pending occurrences freely. -/
def RowGuards (C : Calendar 2 ℝ ReciprocalInput) (d : Nat) :
    List ReciprocalTransaction → (Fin 6 → Nat) → Prop
  | [], _ => True
  | tx :: rows, counts =>
    (tx.lo ≤ 0 ∧ 0 ≤ tx.hi) ∧
    RoutedCalendar.HasRoom (MarkFeedback.score C.model d ⟨[], counts⟩ tx.probe) tx.lo tx.hi ∧
    MarkFeedback.read C.model d ⟨[], counts⟩ tx.probe 0 = tx.decision ∧
    MarkFeedback.emitted C.model tx.probe tx.decision = tx.children ∧
    RowGuards C d rows (fun i =>
      counts i + MarkFeedback.footprint C.model tx.probe tx.decision i)

theorem PreparedTransactions.clock_bounds {n θ route s u i port}
    {run : @Execution n θ route s u} {word}
    (cert : PreparedTransactions i port run word) :
    ∀ pair ∈ word, pair.1 ≤ pair.2 ∧ pair.2 < pair.1 + 1 := by
  induction cert with
  | last _ _ _ pulse =>
    intro pair mem
    obtain rfl := List.mem_singleton.mp mem
    exact ⟨by linarith [pulse.trigger.early, pulse.trigger.entry.time_unchanged],
      by linarith [pulse.trigger.deadline, pulse.trigger.entry.time_unchanged]⟩
  | next cut _ _ pulse _ ih =>
    intro pair mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact ⟨by linarith [pulse.trigger.early, pulse.trigger.entry.time_unchanged],
        by linarith [pulse.trigger.deadline, pulse.trigger.entry.time_unchanged]⟩
    · exact ih pair later

/-- The first prepared pulse starts just after admission. The remaining
admission clocks are the actual deliveries in the cut. -/
theorem PreparedTransactions.delivery_word {n θ route s u i port}
    {run : @Execution n θ route s u} {word}
    (cert : PreparedTransactions i port run word) :
    word.map Prod.fst = s.time :: (run.cellDeliveries i).map Delivery.due := by
  induction cert with
  | last _ _ none _ => simp [none]
  | next cut _ _ _ _ ih =>
    simp only [List.map_cons, ih]
    have reconstruction := congrArg (fun e => e.cellDeliveries i) cut.reconstruct
    rw [reconstruction, Execution.cellDeliveries_append, cut.no_earlier, List.nil_append]
    change _ = _ :: (((cut.entry.deliveries ++ cut.rest.deliveries).filter
      (fun token => decide (token.cell = i))).map Delivery.due)
    rw [List.filter_append, cut.delivery]
    simp [cut.cell, cut.date.2, Execution.cellDeliveries]

set_option maxHeartbeats 650000 in
private theorem replayFromTokenBudget (C : Calendar 2 ℝ ReciprocalInput) (d : Nat)
    (rows : List ReciprocalTransaction) (s : Config 6 ReciprocalProbe) (future : List ReciprocalProbe)
    (guards : RowGuards C d rows s.writes)
    (chronology : rows.Pairwise (fun a b => a.probe.due ≤ b.probe.due))
    (causal : ∀ tx ∈ rows, ∀ q ∈ tx.children, tx.probe.due < q.due)
    (later : ∀ tx ∈ rows, ∀ q ∈ future, tx.probe.due ≤ q.due)
    (balance : (s.pending ++ rows.flatMap Transaction.children).Perm
      (rows.map Transaction.probe ++ future)) :
    ∃ out, TransactionReplay C d (· ≤ ·) s rows out ∧
      out.pending.Perm future ∧ out.writes = writesAfter C rows s.writes := by
  induction rows generalizing s with
  | nil =>
    exact ⟨s, TransactionReplay.nil (C := C) (d := d) (le := (· ≤ ·)) s, by simpa using balance, rfl⟩
  | cons tx rows ih =>
    rcases List.pairwise_cons.mp chronology with ⟨first, ordered⟩
    have present : tx.probe ∈ s.pending := by
      have member := balance.mem_iff.mpr (show tx.probe ∈ (tx :: rows).map Transaction.probe ++ future by simp)
      rcases List.mem_append.mp member with h | children
      · exact h
      · obtain ⟨parent, occurs, child⟩ := List.mem_flatMap.mp children
        have bound : tx.probe.due ≤ parent.probe.due := by
          rcases List.mem_cons.mp occurs with rfl | tail
          · rfl
          · exact first parent tail
        exact (lt_irrefl _ (bound.trans_lt (causal parent occurs _ child))).elim
    classical
    let rest := s.pending.erase tx.probe
    have selected : s.pending.Perm (tx.probe :: rest) := List.perm_cons_erase present
    have earliest : Earliest (· ≤ ·) tx.probe rest := by
      intro q queued
      have mem := selected.mem_iff.mpr (List.mem_cons_of_mem _ queued)
      rcases List.mem_append.mp (balance.mem_iff.mp (List.mem_append_left _ mem)) with admitted | stays
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp admitted
        rcases List.mem_cons.mp ha with rfl | other
        · rfl
        · exact first a other
      · exact later tx (by simp) q stays
    rcases guards with ⟨interval, room, decision, issued, tailGuards⟩
    let next : Config 6 ReciprocalProbe :=
      ⟨rest ++ tx.children, fun i => s.writes i + MarkFeedback.footprint C.model tx.probe tx.decision i⟩
    have nextBalance : (next.pending ++ rows.flatMap Transaction.children).Perm
        (rows.map Transaction.probe ++ future) := by
      have aligned := (selected.append_right ((tx :: rows).flatMap Transaction.children)).symm.trans balance
      simpa only [List.cons_append, List.flatMap_cons, List.map_cons, List.perm_cons, List.append_assoc, next] using aligned
    obtain ⟨out, tail, queued, counts⟩ := ih next tailGuards ordered
      (fun x hx => causal x (List.mem_cons_of_mem _ hx))
      (fun x hx => later x (List.mem_cons_of_mem _ hx)) nextBalance
    have run : TransactionReplay C d (· ≤ ·) s (tx :: rows) out :=
      TransactionReplay.cons (s := s) (next := next) tx rest selected earliest interval room decision
        issued rfl (fun _ => rfl) tail
    exact ⟨out, run, queued, counts⟩

noncomputable def stagedDeliveries (epoch : NominalEpoch) : List (Delivery 2) :=
  epoch.staged.before.deliveries.map liftDelivery ++ epoch.staged.after.deliveries

noncomputable def stagedFires (epoch : NominalEpoch) : List (Fin 2 × ℝ) :=
  epoch.staged.before.ledger.emissions.map (fun event => (event.1.castSucc, event.2)) ++
    epoch.staged.after.ledger.emissions

private theorem stagedTokenBudget (epoch : NominalEpoch)
    (closed : (epoch.staged.before.ledger.emissions.map (fun event => (event.1.castSucc, event.2))).flatMap
      (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2) = []) :
    (reciprocalSeed ++ ((stagedFires epoch).flatMap
      (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2)).map reciprocalOccurrence).Perm
      ((stagedDeliveries epoch).map reciprocalOccurrence ++ epoch.final.pending.map reciprocalOccurrence) := by
  have before := epoch.staged.before.token_balance
  simp only [List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl :
      ∀ a ∈ epoch.staged.before.ledger.emissions, ([] : List (Delivery 1)) = []),
    Multiset.coe_nil, add_zero] at before
  have lift := congrArg (Multiset.map (@liftDelivery 1)) before
  have birth : epoch.staged.afterBirth.pending =
      epoch.staged.beforeBirth.pending.map liftDelivery ++ constructedBBirthSources :=
    epoch.staged.birth.pending.trans
      (congrArg (epoch.staged.beforeBirth.pending.map liftDelivery ++ ·) epoch.sources_origin)
  have after := epoch.staged.after.token_balance
  rw [birth] at after
  simp only [Multiset.map_add, Multiset.map_coe] at lift
  have tokens :
      ((nominalStart.pending.map liftDelivery ++ constructedBBirthSources) ++
        epoch.staged.after.ledger.emissions.flatMap
          (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2) : List (Delivery 2)).Perm
        (stagedDeliveries epoch ++ epoch.final.pending) := by
    apply Multiset.coe_eq_coe.mp
    simp only [stagedDeliveries, ← Multiset.coe_add] at after ⊢
    rw [← lift]
    let waiting : Multiset (Delivery 2) := ↑(epoch.staged.beforeBirth.pending.map liftDelivery)
    let delivered : Multiset (Delivery 2) := ↑(epoch.staged.before.deliveries.map liftDelivery)
    let born : Multiset (Delivery 2) := ↑constructedBBirthSources
    let routed : Multiset (Delivery 2) := ↑(epoch.staged.after.ledger.emissions.flatMap
      (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2))
    calc
      _ = waiting + born + routed + delivered := by dsimp only [waiting, born, routed, delivered]; ac_rfl
      _ = _ := by rw [show waiting + born + routed = _ from after.symm]; dsimp only [delivered]; ac_rfl
  simpa only [reciprocalSeed, stagedFires, List.flatMap_append, closed, List.nil_append,
    List.map_append] using tokens.map reciprocalOccurrence

/-- The protocol's two protected admissions are A's source at 32 and
the B wire from A's source at 176. Native latency and the fixed wire
delay put the latter strictly between 176 and 178. -/
noncomputable def reciprocalCalendar (fire : ReciprocalProbe → ℝ) :
    Calendar 2 ℝ ReciprocalInput where
  cell := Prod.fst
  secondPort input := decide (input.2 = 2)
  phase input date :=
    if (input = (0, 0) ∧ date = 32) ∨ (input = (1, 1) ∧ 176 < date ∧ date < 178)
    then .slow else .ready
  bias input phase :=
    if phase = .slow then -7 else if input = (1, 1) then -1 else -5
  recoveryWeight _ _ := 0
  learn _ phase := decide (phase = .ready)
  mark _ phase fired := decide (phase = .slow) && !fired
  route probe := (reciprocalEntryRouter nominalDelay nominalDelay probe.input.1 (fire probe)).map
    reciprocalOccurrence

/-- The finite history keeps the actual admission and FIRE clocks.
The physical router supplies the children and the normalized read
error interval is [-1, 0]. -/
noncomputable def reciprocalRow (probe : ReciprocalProbe) (fire : Option ℝ) : ReciprocalTransaction :=
  ⟨probe, fire, (fire.toList.flatMap
    (reciprocalEntryRouter nominalDelay nominalDelay probe.input.1)).map reciprocalOccurrence, -1, 0⟩

private def isBirthPort (p : ReciprocalProbe) : Prop :=
  p.input = (0, 0) ∧ p.due ≤ 120

private theorem birth_admission_learned {pair : ℝ × ℝ} {word : List (ℝ × ℝ)}
    (dates : word.map Prod.fst = 40 :: (sourceTrain (0 : Fin 1) 0 48 8 10).map Delivery.due)
    (mem : pair ∈ word) : 40 ≤ pair.1 ∧ pair.1 ≤ 120 := by
  have recorded := List.mem_map_of_mem (f := Prod.fst) mem
  rw [dates] at recorded
  rcases List.mem_cons.mp recorded with head | other
  · rw [head]
    norm_num
  · obtain ⟨token, arrived, eq⟩ := List.mem_map.mp other
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp arrived
    have cap : (j.val : ℝ) ≤ 9 := by exact_mod_cast (show j.val ≤ 9 by omega)
    rw [← eq]
    change 40 ≤ 48 + 8 * (j.val : ℝ) ∧ 48 + 8 * (j.val : ℝ) ≤ 120
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j.val]

private theorem birth_row_route_closed {t : ℝ} (prior : t < 160) :
    reciprocalEntryRouter nominalDelay nominalDelay 0 t = [] := by
  have other : (0 : Fin 2) ≠ 1 := by decide
  simp [reciprocalEntryRouter, Contact.route, teachingContact, feedbackContact, other, not_le.mpr prior]

/-- The first sixteen transactions have a single native admission/FIRE
table. The weak prefix and protected MARK are retained from the very
same construction as the eleven later prepared pulses. -/
theorem birth_transaction_table
    (c : ConstructedBirthPreparation KernelR.FutureControls.parameters nominalStart) :
    ∃ (strong : ℝ) (prepared : List (ℝ × ℝ)) (rows : List ReciprocalTransaction),
      strong = c.at40.mark.first.final.time ∧
      PreparedTransactions 0 0 c.suffix prepared ∧
      rows = [reciprocalRow ⟨0, 0, 0⟩ none, reciprocalRow ⟨8, 0, 0⟩ none,
        reciprocalRow ⟨16, 0, 0⟩ none, reciprocalRow ⟨24, 0, 0⟩ (some strong),
        reciprocalRow ⟨32, 0, 0⟩ none] ++
        prepared.map (fun clocks => reciprocalRow ⟨clocks.1, 0, 0⟩ (some clocks.2)) ∧
      rows.map Transaction.probe = (c.execution.deliveries.map liftDelivery).map reciprocalOccurrence ∧
      Transaction.fires Prod.fst rows =
        c.execution.ledger.emissions.map (fun e => (e.1.castSucc, e.2)) ∧
      (∀ r ∈ rows, isBirthPort r.probe ∧ r.children = []) ∧
      (∀ r ∈ rows, ∀ t ∈ r.fireDate, r.probe.due ≤ t ∧ t < r.probe.due + 1) := by
  obtain ⟨prepared, _, cert⟩ := birth_sender_transactions c nominal_box.extend_old
  have times := cert.delivery_word
  rw [c.at40.date, show c.suffix.cellDeliveries 0 = sourceTrain 0 0 48 8 10 by
    simp [Execution.cellDeliveries, c.deliveries_suffix, sourceTrain]] at times
  let strong := c.at40.mark.first.final.time
  let initialRows : List ReciprocalTransaction := [reciprocalRow ⟨0, 0, 0⟩ none, reciprocalRow ⟨8, 0, 0⟩ none,
    reciprocalRow ⟨16, 0, 0⟩ none, reciprocalRow ⟨24, 0, 0⟩ (some strong),
    reciprocalRow ⟨32, 0, 0⟩ none]
  let tail := prepared.map (fun clocks => reciprocalRow ⟨clocks.1, 0, 0⟩ (some clocks.2))
  have strongBounds := c.at40.mark.first.date_bounds
  have closeStrong : strong < 160 := by change c.at40.mark.first.final.time < 160; linarith [strongBounds.2]
  have tailFires : Transaction.fires Prod.fst tail = (prepared.map Prod.snd).map
      (fun date => ((0 : Fin 2), date)) := by
    simp [tail, Transaction.fires, reciprocalRow, List.filterMap_map, Function.comp_def]
  refine ⟨strong, prepared, initialRows ++ tail, rfl, cert, rfl, ?_, ?_, ?_, ?_⟩
  · have prep := congrArg (List.map (fun t => reciprocalOccurrence (⟨0, 0, t⟩ : Delivery 2))) times
    rw [c.deliveries]
    simp only [tail, List.map_append, List.map_map, Function.comp_def, reciprocalRow] at prep ⊢
    have tailEq : List.map (fun p : ℝ × ℝ => (⟨p.1, 0, 0⟩ : ReciprocalProbe)) prepared =
        ⟨40, 0, 0⟩ :: List.map (fun d : Delivery 1 => ⟨d.due, 0, 0⟩)
          (sourceTrain 0 0 48 8 10) := prep
    rw [tailEq]
    norm_num [initialRows, reciprocalRow, reciprocalOccurrence, liftDelivery, sourceTrain, List.ofFn_succ]
  · have allFires : c.suffix.ledger.emissions =
        (prepared.map Prod.snd).map (fun date => ((0 : Fin 1), date)) := by
      rw [← cert.fire_word]
      simp [Execution.emissionTimes, List.map_map, Subsingleton.elim (α := Fin 1) _ 0, Function.comp_def]
      conv_lhs => rw [← List.map_id (l := c.suffix.ledger.emissions)]
      apply List.map_congr_left
      intro pair _
      exact Prod.ext (Subsingleton.elim pair.1 (0 : Fin 1)) rfl
    rw [ConstructedBirthPreparation.execution, Execution.emissions_append, c.at40.emissions, allFires]
    have split : Transaction.fires Prod.fst (initialRows ++ tail) =
        [(0, strong)] ++ Transaction.fires Prod.fst tail := by
      simp only [Transaction.fires, List.filterMap_append]
      rfl
    rw [split, tailFires]
    simp [strong, List.map_map, Function.comp_def]
  · intro r mem
    rcases List.mem_append.mp mem with first | later
    · simp only [initialRows, List.mem_cons, List.not_mem_nil, or_false] at first
      rcases first with rfl | rfl | rfl | rfl | rfl <;>
        norm_num [isBirthPort, reciprocalRow, birth_row_route_closed closeStrong]
    · obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp later
      have date := birth_admission_learned times hp
      have fire := (cert.clock_bounds pair hp).2
      have close : pair.2 < 160 := by linarith [date.2]
      simp [isBirthPort, reciprocalRow, date.2, birth_row_route_closed close]
  · intro r mem t ht
    rcases List.mem_append.mp mem with first | later
    · simp only [initialRows, List.mem_cons, List.not_mem_nil, or_false] at first
      rcases first with rfl | rfl | rfl | rfl | rfl <;>
        simp only [reciprocalRow, Option.mem_def, reduceCtorEq] at ht
      cases ht
      change (24 : ℝ) ≤ strong ∧ strong < 24 + 1
      change (243 / 10 : ℝ) < strong ∧ strong < 249 / 10 at strongBounds
      constructor <;> linarith [strongBounds.1, strongBounds.2]
    · obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp later
      have eq : pair.2 = t := by simpa [reciprocalRow] using ht
      subst t
      exact cert.clock_bounds pair hp

private def birthCounts (gain recovery : Nat) (j : Fin 6) : Nat :=
  if j = 0 then gain else if j = 2 then recovery else 0

private theorem birth_row_guard (fire : ReciprocalProbe → ℝ) {t : ℝ} {clock : Option ℝ}
    (gain recovery : Nat)
    (branch : (t = 32 ∧ clock = none ∧ gain = 3) ∨
      (t ≠ 32 ∧ clock = none ∧ gain < 3) ∨
      (t ≠ 32 ∧ clock.isSome = true ∧ gain = 3))
    (routed : MarkFeedback.emitted (reciprocalCalendar fire).model ⟨t, 0, 0⟩
      (reciprocalRow ⟨t, 0, 0⟩ clock).decision = (reciprocalRow ⟨t, 0, 0⟩ clock).children) :
    ∀ tail, RowGuards (reciprocalCalendar fire) 2 tail
      (if t = 32 then birthCounts gain (recovery + 1)
       else if clock.isSome then birthCounts gain recovery else birthCounts (gain + 1) recovery) →
    RowGuards (reciprocalCalendar fire) 2 (reciprocalRow ⟨t, 0, 0⟩ clock :: tail)
      (birthCounts gain recovery) := by
  classical
  intro tail following
  let C := reciprocalCalendar fire
  let p : ReciprocalProbe := ⟨t, 0, 0⟩
  let row : ReciprocalTransaction := reciprocalRow p clock
  change (row.lo ≤ 0 ∧ 0 ≤ row.hi) ∧
    RoutedCalendar.HasRoom (MarkFeedback.score C.model 2 ⟨[], birthCounts gain recovery⟩ p) row.lo row.hi ∧
    MarkFeedback.read C.model 2 ⟨[], birthCounts gain recovery⟩ p 0 = row.decision ∧
    MarkFeedback.emitted C.model p row.decision = row.children ∧ _
  have gainIndex : MarkFeedback.gain C.model p = 0 := by rfl
  have recoveryIndex : MarkFeedback.recovery C.model p = 2 := rfl
  have notOther : ((0 : Fin 2), (0 : Port)) ≠ (1, 1) := by decide
  have phase : C.phase p.input t = if t = 32 then .slow else .ready := by
    simp [C, p, reciprocalCalendar, notOther]
  have score : MarkFeedback.score C.model 2 ⟨[], birthCounts gain recovery⟩ p =
      (if t = 32 then (-7 : Int) else -5) + 2 * gain := by
    change C.bias p.input (C.phase p.input t) + 2 * (birthCounts gain recovery (MarkFeedback.gain C.model p) : Int) +
      C.recoveryWeight p.input (C.phase p.input t) * (birthCounts gain recovery (MarkFeedback.recovery C.model p) : Int) = _
    rw [gainIndex, phase]
    by_cases ht : t = 32 <;> simp [ht, C, p, reciprocalCalendar, notOther, birthCounts]
  have dose (j : Fin 6) : MarkFeedback.footprint C.model p row.decision j =
      (if t ≠ 32 ∧ clock.isSome = false ∧ j = 0 then 1 else 0) +
      (if t = 32 ∧ clock.isSome = false ∧ j = 2 then 1 else 0) := by
    change (if row.decision = false ∧ C.learn p.input (C.phase p.input t) = true ∧
      j = MarkFeedback.gain C.model p then 1 else 0) +
      (if C.mark p.input (C.phase p.input t) row.decision = true ∧
      j = MarkFeedback.recovery C.model p then 1 else 0) = _
    rw [gainIndex, recoveryIndex, phase]
    by_cases ht : t = 32 <;> cases hc : clock.isSome <;>
      simp [ht, C, row, reciprocalRow, Transaction.decision, reciprocalCalendar, hc]
  have interval : row.lo = -1 ∧ row.hi = 0 := ⟨rfl, rfl⟩
  refine ⟨by rw [interval.1, interval.2]; decide, ?_, ?_, routed, ?_⟩
  · rw [score, interval.1, interval.2]
    rcases branch with ⟨ht, _, count⟩ | ⟨ht, _, count⟩ | ⟨ht, _, count⟩
    · simp [ht, count, RoutedCalendar.HasRoom]
    · simp only [ht, ite_false, RoutedCalendar.HasRoom]; omega
    · simp [ht, count, RoutedCalendar.HasRoom]
  · unfold MarkFeedback.read
    rw [score]
    rcases branch with ⟨ht, hc, count⟩ | ⟨ht, hc, count⟩ | ⟨ht, hc, count⟩
    · simp [ht, hc, count, row, reciprocalRow, Transaction.decision]
    · simp only [ht, hc, ite_false, row, reciprocalRow, Transaction.decision, Option.isSome_none]
      apply decide_eq_false
      omega
    · simp [ht, hc, count, row, reciprocalRow, Transaction.decision]
  · have w : (fun j => birthCounts gain recovery j + MarkFeedback.footprint C.model p row.decision j) =
        (if t = 32 then birthCounts gain (recovery + 1)
          else if clock.isSome then birthCounts gain recovery else birthCounts (gain + 1) recovery) := by
      funext j
      rw [dose]
      rcases branch with ⟨ht, hc, _⟩ | ⟨ht, hc, _⟩ | ⟨ht, hc, _⟩ <;>
        fin_cases j <;> simp [ht, hc, birthCounts]
    change RowGuards C 2 tail (fun j =>
      birthCounts gain recovery j + MarkFeedback.footprint C.model p row.decision j)
    rw [w]
    exact following

private theorem birth_emitted (fire : ReciprocalProbe → ℝ)
    (latency : ∀ p, fire p < p.due + 1) {t : ℝ} (h : t ≤ 120) (clock : Option ℝ)
    (native : ∀ date ∈ clock, date < 160) :
    MarkFeedback.emitted (reciprocalCalendar fire).model ⟨t, 0, 0⟩
      (reciprocalRow ⟨t, 0, 0⟩ clock).decision = (reciprocalRow ⟨t, 0, 0⟩ clock).children := by
  cases clock with
  | none => rfl
  | some date =>
    have abstract : fire ⟨t, 0, 0⟩ < 160 := by
      have bound := latency ⟨t, 0, 0⟩
      change fire ⟨t, 0, 0⟩ < t + 1 at bound
      linarith
    have physical := native date (by simp)
    simp [MarkFeedback.emitted, Transaction.decision, reciprocalRow, Calendar.model, reciprocalCalendar,
      birth_row_route_closed abstract, birth_row_route_closed physical]

private theorem birth_learned_guards (fire : ReciprocalProbe → ℝ)
    (latency : ∀ p, fire p < p.due + 1) (prepared : List (ℝ × ℝ))
    (bounds : ∀ p ∈ prepared, 40 ≤ p.1 ∧ p.1 ≤ 120 ∧ p.2 < p.1 + 1) :
    RowGuards (reciprocalCalendar fire) 2
      (prepared.map (fun pair => reciprocalRow ⟨pair.1, 0, 0⟩ (some pair.2))) (birthCounts 3 1) := by
  induction prepared with
  | nil => trivial
  | cons pair tail ih =>
    have date := bounds pair (by simp)
    have separated : pair.1 ≠ 32 := by linarith [date.1]
    have routed := birth_emitted fire latency date.2.1 (some pair.2) (by
      intro t mem
      simp only [Option.mem_def, Option.some.injEq] at mem
      subst t
      linarith [date.2.1, date.2.2])
    simpa only [List.map_cons] using
      birth_row_guard fire 3 1 (.inr (.inr ⟨separated, rfl, rfl⟩)) routed _
        (by simpa [separated] using ih (fun q mem => bounds q (List.mem_cons_of_mem _ mem)))

private theorem birth_guards (fire : ReciprocalProbe → ℝ)
    (latency : ∀ p, fire p < p.due + 1) (strong : ℝ) (strongBound : strong < 160)
    (prepared : List (ℝ × ℝ))
    (bounds : ∀ p ∈ prepared, 40 ≤ p.1 ∧ p.1 ≤ 120 ∧ p.2 < p.1 + 1) :
    RowGuards (reciprocalCalendar fire) 2
      ([reciprocalRow ⟨0, 0, 0⟩ none, reciprocalRow ⟨8, 0, 0⟩ none,
        reciprocalRow ⟨16, 0, 0⟩ none, reciprocalRow ⟨24, 0, 0⟩ (some strong),
        reciprocalRow ⟨32, 0, 0⟩ none] ++
        prepared.map (fun pair => reciprocalRow ⟨pair.1, 0, 0⟩ (some pair.2))) (fun _ => 0) := by
  have late := birth_learned_guards fire latency prepared bounds
  have mark := birth_row_guard fire (t := 32) (clock := none) 3 0 (Or.inl ⟨rfl, rfl, rfl⟩) rfl _
    (by simpa using late)
  have routed := birth_emitted fire latency (t := 24) (by norm_num) (some strong) (by
    intro t mem
    simp only [Option.mem_def, Option.some.injEq] at mem
    rwa [← mem])
  have fireRow := birth_row_guard fire 3 0 (Or.inr (Or.inr ⟨by norm_num, rfl, rfl⟩)) routed _
    (by simpa using mark)
  have row16 := birth_row_guard fire (t := 16) (clock := none) 2 0
    (Or.inr (Or.inl ⟨by norm_num, rfl, by decide⟩)) rfl _ (by simpa using fireRow)
  have row8 := birth_row_guard fire (t := 8) (clock := none) 1 0
    (Or.inr (Or.inl ⟨by norm_num, rfl, by decide⟩)) rfl _ (by simpa using row16)
  have row0 := birth_row_guard fire (t := 0) (clock := none) 0 0
    (Or.inr (Or.inl ⟨by norm_num, rfl, by decide⟩)) rfl _ (by simpa using row8)
  have zero : birthCounts 0 0 = (fun _ => 0) := by funext j; simp [birthCounts]
  simpa only [zero, List.cons_append, List.nil_append] using row0

private theorem birth_learned_counts (fire : ReciprocalProbe → ℝ)
    (prepared : List (ℝ × ℝ)) (bounds : ∀ p ∈ prepared, 40 ≤ p.1) :
    writesAfter (reciprocalCalendar fire)
      (prepared.map (fun pair => reciprocalRow ⟨pair.1, 0, 0⟩ (some pair.2))) (birthCounts 3 1) =
      birthCounts 3 1 := by
  induction prepared with
  | nil => rfl
  | cons pair tail ih =>
    have separated : pair.1 ≠ 32 := by linarith [bounds pair (by simp)]
    have other : ((0 : Fin 2), (0 : Port)) ≠ (1, 1) := by decide
    have noWrite (i : Fin 6) :
        MarkFeedback.footprint (reciprocalCalendar fire).model ⟨pair.1, 0, 0⟩ true i = 0 := by
      simp [MarkFeedback.footprint, Calendar.model, reciprocalCalendar, separated, other]
    change writesAfter (reciprocalCalendar fire) _
      (fun i => birthCounts 3 1 i + MarkFeedback.footprint (reciprocalCalendar fire).model
        ⟨pair.1, 0, 0⟩ true i) = birthCounts 3 1
    simpa only [noWrite, Nat.add_zero] using ih (fun q mem => bounds q (List.mem_cons_of_mem _ mem))

private theorem birth_counts (fire : ReciprocalProbe → ℝ) (strong : ℝ) (prepared : List (ℝ × ℝ))
    (bounds : ∀ p ∈ prepared, 40 ≤ p.1) :
    writesAfter (reciprocalCalendar fire)
      ([reciprocalRow ⟨0, 0, 0⟩ none, reciprocalRow ⟨8, 0, 0⟩ none,
        reciprocalRow ⟨16, 0, 0⟩ none, reciprocalRow ⟨24, 0, 0⟩ (some strong),
        reciprocalRow ⟨32, 0, 0⟩ none] ++
        prepared.map (fun pair => reciprocalRow ⟨pair.1, 0, 0⟩ (some pair.2))) (fun _ => 0) =
      birthCounts 3 1 := by
  rw [writesAfter, List.foldl_append]
  have first :
      ([reciprocalRow ⟨0, 0, 0⟩ none, reciprocalRow ⟨8, 0, 0⟩ none,
        reciprocalRow ⟨16, 0, 0⟩ none, reciprocalRow ⟨24, 0, 0⟩ (some strong),
        reciprocalRow ⟨32, 0, 0⟩ none] : List ReciprocalTransaction).foldl (fun counts tx i =>
          counts i + MarkFeedback.footprint (reciprocalCalendar fire).model tx.probe tx.decision i)
        (fun _ => 0) = birthCounts 3 1 := by
    funext i
    have other : ((0 : Fin 2), (0 : Port)) ≠ (1, 1) := by decide
    fin_cases i <;>
      norm_num [List.foldl, reciprocalRow, Transaction.decision, MarkFeedback.footprint,
        Calendar.model, reciprocalCalendar, other, MarkFeedback.gain, MarkFeedback.recovery,
        Address.encode, AutonomousFeedback.Schedule.PortMemory.Coordinate.index, birthCounts]
  rw [first]
  exact birth_learned_counts fire prepared bounds

private theorem birth_rows_balance
    (c : ConstructedBirthPreparation KernelR.FutureControls.parameters nominalStart)
    {rows : List ReciprocalTransaction}
    (admissions : rows.map Transaction.probe = (c.execution.deliveries.map liftDelivery).map reciprocalOccurrence)
    (closed : ∀ r ∈ rows, r.children = []) :
    (reciprocalSeed ++ rows.flatMap Transaction.children).Perm
      (rows.map Transaction.probe ++ (c.final.pending.map liftDelivery ++
        constructedBBirthSources).map reciprocalOccurrence) := by
  have before := c.execution.token_balance
  simp only [List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl :
      ∀ e ∈ c.execution.ledger.emissions, ([] : List (Delivery 1)) = []),
    Multiset.coe_nil, add_zero] at before
  have consumed : nominalStart.pending.Perm (c.execution.deliveries ++ c.final.pending) := by
    apply Multiset.coe_eq_coe.mp
    rw [← Multiset.coe_add, ← before, add_comm]
  rw [List.flatMap_eq_nil_iff.mpr closed, List.append_nil, admissions]
  simpa only [reciprocalSeed, List.map_append, List.append_assoc] using
    (((consumed.map (@liftDelivery 1)).append_right constructedBBirthSources).map reciprocalOccurrence)

/-- Every pre-birth admission, including the strong source at 24 and the
protected source at 32, replays on one dated guarded trace. This leaves
the actual later A train and the reserved B sources pending. -/
theorem reciprocal_before_birth_replay
    (c : ConstructedBirthPreparation KernelR.FutureControls.parameters nominalStart) :
    ∃ (rows : List ReciprocalTransaction) (out : Config 6 ReciprocalProbe),
      TransactionReplay (reciprocalCalendar Occurrence.due) 2 (· ≤ ·)
        (MarkFeedback.initial 2 reciprocalSeed) rows out ∧
      rows.map Transaction.probe = (c.execution.deliveries.map liftDelivery).map reciprocalOccurrence ∧
      Transaction.fires Prod.fst rows = c.execution.ledger.emissions.map (fun e => (e.1.castSucc, e.2)) ∧
      out.pending.Perm ((c.final.pending.map liftDelivery ++ constructedBBirthSources).map reciprocalOccurrence) ∧
      out.writes = birthCounts 3 1 := by
  obtain ⟨strong, prepared, rows, clock, cert, shape, admissions, firingWord, inBand, timed⟩ :=
    birth_transaction_table c
  have dates := cert.delivery_word
  rw [c.at40.date, show c.suffix.cellDeliveries 0 = sourceTrain 0 0 48 8 10 by
    simp [Execution.cellDeliveries, c.deliveries_suffix, sourceTrain]] at dates
  have bounds : ∀ p ∈ prepared, 40 ≤ p.1 ∧ p.1 ≤ 120 ∧ p.2 < p.1 + 1 := by
    intro pair mem
    exact ⟨(birth_admission_learned dates mem).1, (birth_admission_learned dates mem).2,
      (cert.clock_bounds pair mem).2⟩
  have close : strong < 160 := by rw [clock]; linarith [c.at40.mark.first.date_bounds.2]
  have guards : RowGuards (reciprocalCalendar Occurrence.due) 2 rows (fun _ => 0) := by
    rw [shape]
    exact birth_guards _ (fun _ => by simp) strong close prepared bounds
  have chronology : rows.Pairwise (fun a b => a.probe.due ≤ b.probe.due) := by
    have order : (rows.map Transaction.probe).Pairwise (fun a b => a.due ≤ b.due) := by
      rw [admissions]
      exact List.pairwise_map.mpr (List.pairwise_map.mpr c.execution.deliveries_chronological)
    exact (List.pairwise_map (f := Transaction.probe)).mp order
  have future : ∀ r ∈ rows, ∀ q ∈ (c.final.pending.map liftDelivery ++
      constructedBBirthSources).map reciprocalOccurrence, r.probe.due ≤ q.due := by
    intro row hr q hq
    have cap := (inBand row hr).1.2
    obtain ⟨token, queued, rfl⟩ := List.mem_map.mp hq
    rcases List.mem_append.mp queued with old | fresh
    · obtain ⟨source, fromA, rfl⟩ := List.mem_map.mp old
      rw [c.pending] at fromA
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp fromA
      change row.probe.due ≤ 160 + 8 * (k.val : ℝ)
      linarith [Nat.cast_nonneg (α := ℝ) k.val]
    · have later := constructedBBirthSources_strict_future token fresh
      change row.probe.due ≤ token.due
      linarith
  have closed : ∀ r ∈ rows, r.children = [] := fun r mem => (inBand r mem).2
  obtain ⟨out, replay, pending, writes⟩ := replayFromTokenBudget (reciprocalCalendar Occurrence.due) 2 rows
    (MarkFeedback.initial 2 reciprocalSeed) _ guards chronology
    (fun r mem q child => by rw [closed r mem] at child; contradiction)
    future (birth_rows_balance c admissions closed)
  refine ⟨rows, out, replay, admissions, firingWord, pending, ?_⟩
  rw [writes, shape]
  exact birth_counts _ strong prepared (fun pair mem => (bounds pair mem).1)

/-- Exact physical memory comparison on the pre-birth slice, with the
native learned gains and MARK dose normalized by their respective units. -/
theorem nominal_prebirth_refinement :
    ∃ (c : ConstructedBirthPreparation KernelR.FutureControls.parameters nominalStart)
      (rows : List ReciprocalTransaction) (out : Config 6 ReciprocalProbe),
      CompleteThrough c.execution 128 ∧
      TransactionReplay (reciprocalCalendar Occurrence.due) 2 (· ≤ ·)
        (MarkFeedback.initial 2 reciprocalSeed) rows out ∧
      rows.map Transaction.probe = (c.execution.deliveries.map liftDelivery).map reciprocalOccurrence ∧
      Transaction.fires Prod.fst rows = c.execution.ledger.emissions.map (fun e => (e.1.castSucc, e.2)) ∧
      out.pending.Perm ((c.final.pending.map liftDelivery ++ constructedBBirthSources).map reciprocalOccurrence) ∧
      ∀ coord : Coordinate, c.final.x 0 (nativeCoordinate 0 coord) =
        birthMemory 0 coord + unitDose coord * out.writes (Address.mk (0 : Fin 2) coord).encode := by
  obtain ⟨at40⟩ := birth_protocol_prepared40_exists
    (born := nominalStart) Newborn.nominal_birth_state nominal_box.extend_old (fun _ => rfl) rfl
  obtain ⟨c⟩ := at40.preparation_exists nominal_box.extend_old
  obtain ⟨rows, out, replay, admissions, decisions, pending, counts⟩ := reciprocal_before_birth_replay c
  obtain ⟨physical⟩ := c.outcome nominal_box.extend_old
  refine ⟨c, rows, out, c.complete, replay, admissions, decisions, pending, ?_⟩
  intro coord
  rw [counts]
  cases coord
  · have scale : (3 / 5 : ℝ) * 3 = 9 / 5 := by norm_num
    simpa [nativeCoordinate, birthMemory, unitDose, birthCounts, Address.encode,
      Coordinate.index, nominalStart, Newborn.snapshot, scale] using physical.gain_target
  · simpa [nativeCoordinate, birthMemory, unitDose, birthCounts, Address.encode,
      Coordinate.index, nominalStart, Newborn.snapshot] using physical.gain_other 2 (by decide)
  · simpa [nativeCoordinate, birthMemory, unitDose, birthCounts, Address.encode,
      Coordinate.index, nominalStart, Newborn.snapshot] using physical.recovery_gain

private theorem row_children (rows : List ReciprocalTransaction)
    (native : ∀ row ∈ rows, row = reciprocalRow row.probe row.fireDate) :
    rows.flatMap Transaction.children =
      ((Transaction.fires Prod.fst rows).flatMap
        (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2)).map
        reciprocalOccurrence := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have shape := native row (by simp)
    have issued := congrArg Transaction.children shape
    rw [List.flatMap_cons, ih (fun tx mem => native tx (List.mem_cons_of_mem _ mem)), issued]
    cases h : row.fireDate <;>
      simp [reciprocalRow, Transaction.fires, List.map_append, h]

private theorem rows_future {epoch : NominalEpoch} {rows : List ReciprocalTransaction}
    (admissions : rows.map Transaction.probe = (stagedDeliveries epoch).map reciprocalOccurrence) :
    ∀ row ∈ rows, row.probe.due ≤ (4599 / 10 : ℝ) := by
  intro row mem
  have present : row.probe ∈ rows.map Transaction.probe := List.mem_map_of_mem mem
  rw [admissions] at present
  obtain ⟨token, delivered, eq⟩ := List.mem_map.mp present
  have clock : row.probe.due = token.due := (congrArg Occurrence.due eq).symm
  rw [clock, ← epoch.date]
  rcases List.mem_append.mp delivered with before | after
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp before
    exact ((epoch.staged.before.delivery_time_bounds d hd).2.trans
      (epoch.staged.birth.time_unchanged.ge.trans epoch.staged.after.time_monotone))
  · exact (epoch.staged.after.delivery_time_bounds token after).2

private theorem rows_chronological {epoch : NominalEpoch} {rows : List ReciprocalTransaction}
    (admissions : rows.map Transaction.probe = (stagedDeliveries epoch).map reciprocalOccurrence) :
    rows.Pairwise (fun a b => a.probe.due ≤ b.probe.due) := by
  have order : (rows.map Transaction.probe).Pairwise (fun a b => a.due ≤ b.due) := by
    rw [admissions]
    apply List.pairwise_map.mpr
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr epoch.staged.before.deliveries_chronological,
      epoch.staged.after.deliveries_chronological, ?_⟩
    intro d hd e he
    obtain ⟨token, delivered, rfl⟩ := List.mem_map.mp hd
    exact (epoch.staged.before.delivery_time_bounds token delivered).2.trans
      (epoch.staged.birth.time_unchanged.ge.trans (epoch.staged.after.delivery_time_bounds e he).1)
  exact (List.pairwise_map (f := Transaction.probe)).mp order

private theorem future_len (epoch : NominalEpoch) : epoch.final.pending.length = 16 := by
  simp [epoch.pending, sourceTrain]

set_option maxHeartbeats 1000000 in
/-- Assemble an aligned native row table into a guarded replay. The proof
uses the actual staged token balance, including the B birth, and checks
the queue at every earliest-date step. -/
theorem reciprocal_replay_of_transaction_table (epoch : NominalEpoch) (fire : ReciprocalProbe → ℝ)
    (latency : ∀ p, p.due ≤ fire p ∧ fire p < p.due + 1)
    (rows : List ReciprocalTransaction)
    (admissions : rows.map Transaction.probe = (stagedDeliveries epoch).map reciprocalOccurrence)
    (firingWord : (Transaction.fires Prod.fst rows).Perm (stagedFires epoch))
    (rowShape : ∀ tx ∈ rows, tx = reciprocalRow tx.probe tx.fireDate)
    (fireClocks : ∀ tx ∈ rows, ∀ t ∈ tx.fireDate, fire tx.probe = t)
    (closed : (epoch.staged.before.ledger.emissions.map (fun event => (event.1.castSucc, event.2))).flatMap
      (fun event => reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2) = [])
    (guards : RowGuards (reciprocalCalendar fire) 2 rows (fun _ => 0))
    (counts : ∀ i (c : Coordinate), writesAfter (reciprocalCalendar fire) rows (fun _ => 0)
      (Address.mk i c).encode = doseCount i c) :
    ∃ out, TransactionReplay (reciprocalCalendar fire) 2 (· ≤ ·)
      (MarkFeedback.initial 2 reciprocalSeed) rows out ∧
      List.Perm out.pending (epoch.final.pending.map reciprocalOccurrence) ∧
      out.pending.length = 16 ∧
      SafeMemory 256 2 0 513 (fun _ => 0) out ∧
      NominalTrace (reciprocalCalendar fire) 2 (· ≤ ·) (MarkFeedback.initial 2 reciprocalSeed)
        (Transaction.word rows) out ∧
      (∀ i c, epoch.final.x i (nativeCoordinate i c) =
        birthMemory i c + unitDose c * out.writes (Address.mk i c).encode) ∧
      (∀ other word, Trace (reciprocalCalendar fire) 2 (· ≤ ·)
        (MarkFeedback.initial 2 reciprocalSeed) word other →
        (∀ entry ∈ word, entry.1.due ≤ (4599 / 10 : ℝ)) →
        (∀ p ∈ other.pending, (4599 / 10 : ℝ) < p.due) →
        other.writes = out.writes) := by
  have issued := (firingWord.flatMap_right (fun event =>
    reciprocalEntryRouter nominalDelay nominalDelay event.1 event.2)).map reciprocalOccurrence
  have balance : (reciprocalSeed ++ rows.flatMap Transaction.children).Perm
      (rows.map Transaction.probe ++ epoch.final.pending.map reciprocalOccurrence) := by
    rw [row_children rows rowShape, admissions]
    exact (issued.append_left reciprocalSeed).trans (stagedTokenBudget epoch closed)
  have childrenLater : ∀ tx ∈ rows, ∀ q ∈ tx.children, tx.probe.due < q.due := by
    intro tx member q queued
    have shape := congrArg Transaction.children (rowShape tx member)
    rw [shape] at queued
    obtain ⟨token, issued, rfl⟩ := List.mem_map.mp queued
    obtain ⟨clock, present, routed⟩ := List.mem_flatMap.mp issued
    have eq := fireClocks tx member clock (by simpa using present)
    have strict : clock < token.due := by
      classical
      rcases List.mem_append.mp routed with forward | reverse
      · unfold Contact.route at forward
        split_ifs at forward
        · obtain rfl := List.mem_singleton.mp forward
          change clock < clock + 7 / 20
          linarith
        · exact (List.not_mem_nil forward).elim
      · unfold Contact.route at reverse
        split_ifs at reverse
        · obtain rfl := List.mem_singleton.mp reverse
          change clock < clock + 7 / 20
          linarith
        · exact (List.not_mem_nil reverse).elim
    exact ((latency tx.probe).1.trans_eq eq).trans_lt strict
  have stay : ∀ tx ∈ rows, ∀ q ∈ epoch.final.pending.map reciprocalOccurrence, tx.probe.due ≤ q.due := by
    intro tx txMem q qMem
    obtain ⟨token, queued, rfl⟩ := List.mem_map.mp qMem
    exact (rows_future admissions tx txMem).trans (epoch.complete.2.2 token queued).le
  obtain ⟨out, replay, future, written⟩ := replayFromTokenBudget (reciprocalCalendar fire) 2 rows
    (MarkFeedback.initial 2 reciprocalSeed) (epoch.final.pending.map reciprocalOccurrence)
    guards (rows_chronological admissions) childrenLater stay balance
  obtain ⟨safe, nominal, memory⟩ := reciprocal_replay_network (reciprocalCalendar fire) 2
    rfl fire latency (fun _ => rfl) epoch replay (by rw [written]; exact counts)
  refine ⟨out, replay, future, by simpa [future_len epoch] using future.length_eq, safe, nominal, memory, ?_⟩
  intro other word trace dates clear
  have routes (p : ReciprocalProbe) :
      (reciprocalCalendar fire).route p =
        (reciprocalEntryRouter nominalDelay nominalDelay p.input.1 (fire p)).map reciprocalOccurrence := rfl
  have causal := reciprocal_route_causal_at_admission (reciprocalCalendar fire)
    fire (fun p => (latency p).1) routes
  have ties := reciprocal_clipped_ties (reciprocalCalendar fire) 2 (4599 / 10) rfl fire routes
  have admitted : ∀ entry ∈ Transaction.word rows, entry.1.due ≤ (4599 / 10 : ℝ) := by
    intro entry mem
    obtain ⟨tx, htx, rfl⟩ := List.mem_map.mp mem
    exact rows_future admissions tx htx
  have exhausted : ∀ p ∈ out.pending, ¬ p.due ≤ (4599 / 10 : ℝ) := by
    intro p mem
    obtain ⟨token, queued, rfl⟩ := List.mem_map.mp (future.mem_iff.mp mem)
    exact not_le.mpr (epoch.complete.2.2 token queued)
  exact dated_horizon_unique (4599 / 10) reciprocalSeed causal ties trace replay.trace dates admitted
    (fun p mem => not_le.mpr (clear p mem)) exhausted

end NetworkStability.NativeReciprocal
