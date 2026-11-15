import GuardedReplay

namespace NetworkStability.NativeMultiToken

open PhaseAdmission
open AutonomousFeedback.Schedule (Equivalent)

private theorem nominal_transport {C : Calendar N Date Label} {d : Nat} [Preorder Date]
    {s t u : QueueState N Date Label} {word : List (Occurrence Date Label × Bool)}
    (trace : NominalTrace C d (· ≤ ·) s word u) (same : Equivalent s t) :
    ∃ v, NominalTrace C d (· ≤ ·) t word v ∧ Equivalent u v := by
  induction trace generalizing t with
  | nil => exact ⟨t, .nil _, same⟩
  | @cons s _ probe rest available earliest word tail ih =>
    have decision : MarkFeedback.read C.model d s probe 0 = MarkFeedback.read C.model d t probe 0 := by
      simp only [MarkFeedback.read, MarkFeedback.score, same.2]
      rfl
    obtain ⟨v, path, final⟩ := ih (MarkFeedback.process_equivalent C.model d same.2 probe (List.Perm.refl _))
    exact ⟨v, decision.symm ▸ NominalTrace.cons probe rest (same.1.symm.trans available) earliest path, final⟩

private theorem stable_tied_decision {C : Calendar N Date Label} {d : Nat} [Preorder Date]
    {s : QueueState N Date Label} (room : TieRoom C d s) {p q : Occurrence Date Label}
    (ep : Eligible s p) (eq : Eligible s q) (ne : p ≠ q) (rest : List (Occurrence Date Label)) :
    MarkFeedback.read C.model d (MarkFeedback.process C.model d s q rest 0) p 0 =
      MarkFeedback.read C.model d s p 0 := by
  unfold MarkFeedback.read
  rw [MarkFeedback.score_after, Int.add_zero]
  by_cases cell : C.model.cell p = C.model.cell q
  · exact MarkFeedback.read_eq_of_room _ _ _ _ ⟨Int.le_refl _, Int.le_refl _⟩
      (room p q ep eq ne cell (MarkFeedback.read C.model d s q 0))
  · rw [MarkFeedback.different_cells_displacement C.model d p q cell]

private theorem eligible_from_queue [Preorder Date]
    {s : QueueState N Date Label} {r : Occurrence Date Label} {rest : List (Occurrence Date Label)}
    (available : s.pending.Perm (r :: rest)) (earliest : Earliest (· ≤ ·) r rest) : Eligible s r := by
  refine ⟨available.mem_iff.mpr List.mem_cons_self, fun probe mem => ?_⟩
  rcases List.mem_cons.mp (available.mem_iff.mp mem) with rfl | later
  · rfl
  · exact earliest probe later

/-- Move a legal first choice to the front of a drained nominal word.
The displaced same-date choices keep their decisions. -/
private theorem take_nominal_head {C : Calendar N Date Label} {d : Nat} [Preorder Date]
    (causal : Causal C) {root s out : QueueState N Date Label}
    (ties : TieAdmissible C d root) (reach : DatedPath C d root s)
    {word : List (Occurrence Date Label × Bool)} (trace : NominalTrace C d (· ≤ ·) s word out)
    (drained : out.pending = []) (probe : Occurrence Date Label) (rest : List (Occurrence Date Label))
    (selected : s.pending.Perm (probe :: rest)) (earliest : Earliest (· ≤ ·) probe rest) :
    ∃ next tailWord, NominalTrace C d (· ≤ ·) (MarkFeedback.process C.model d s probe rest 0) tailWord next ∧
      next.pending = [] ∧ word.Perm ((probe, MarkFeedback.read C.model d s probe 0) :: tailWord) := by
  classical
  induction trace generalizing probe rest with
  | nil => simp [drained] at selected
  | @cons s out q qs available first word tail ih =>
    let read := MarkFeedback.read C.model d s
    let step (p : Occurrence Date Label) (ps : List (Occurrence Date Label)) :=
      MarkFeedback.process C.model d s p ps 0
    by_cases equal : probe = q
    · subst probe
      have rests : qs.Perm rest := (available.symm.trans selected).cons_inv
      obtain ⟨last, residual, same⟩ := nominal_transport tail (MarkFeedback.process_equivalent C.model d rfl q rests)
      exact ⟨last, word, residual, same.1.symm.trans (drained ▸ List.Perm.refl _) |>.eq_nil, List.Perm.refl _⟩
    · have pBefore := eligible_from_queue selected earliest
      have qBefore := eligible_from_queue available first
      have qInRest : q ∈ rest := (List.mem_cons.mp (selected.mem_iff.mp qBefore.1)).resolve_left (Ne.symm equal)
      let survivors := rest.erase q
      have left : rest.Perm (q :: survivors) := List.perm_cons_erase qInRest
      have right : qs.Perm (probe :: survivors) :=
        ((available.symm.trans (selected.trans (left.cons probe))).trans (List.Perm.swap _ _ _)).cons_inv
      let children (p : Occurrence Date Label) := MarkFeedback.emitted C.model p (read p 0)
      have legal {x y : Occurrence Date Label} (hx : Eligible s x) (hy : Eligible s y) :
          Earliest (· ≤ ·) x (survivors ++ children y) := by
        intro a mem
        rcases List.mem_append.mp mem with fromRoot | routed
        · exact hx.2 a (selected.mem_iff.mpr (List.mem_cons_of_mem _
            (left.mem_iff.mpr (List.mem_cons_of_mem _ fromRoot))))
        · have rule : a ∈ C.route y := by
            cases choice : read y 0 with
            | false => simp [children, MarkFeedback.emitted, choice] at routed
            | true => simpa [children, Calendar.model, MarkFeedback.emitted, choice] using routed
          exact (hx.2 y hy.1).trans (causal y a rule)
      let leftState := step probe rest
      let rightState := step q qs
      have leftQueue : leftState.pending.Perm (q :: (survivors ++ children probe)) := left.append_right _
      have rightQueue : rightState.pending.Perm (probe :: (survivors ++ children q)) := right.append_right _
      have afterQ : DatedPath C d root rightState := reach.tail ⟨q, qs, available, first, rfl⟩
      obtain ⟨last, residualWord, residual, empty, perm⟩ := ih afterQ drained probe (survivors ++ children q)
        rightQueue (legal pBefore qBefore)
      have pStable := stable_tied_decision (ties s reach) pBefore qBefore equal qs
      have qStable := stable_tied_decision (ties s reach) qBefore pBefore (Ne.symm equal) rest
      have pCanonical := stable_tied_decision (ties s reach) pBefore qBefore equal (probe :: survivors)
      have qCanonical := stable_tied_decision (ties s reach) qBefore pBefore (Ne.symm equal) (q :: survivors)
      have beforeLeft : Equivalent leftState (step probe (q :: survivors)) :=
        MarkFeedback.process_equivalent C.model d rfl probe left
      have beforeRight : Equivalent rightState (step q (probe :: survivors)) :=
        MarkFeedback.process_equivalent C.model d rfl q right
      have diamond := MarkFeedback.two_occurrences_commute C.model d s probe q survivors pCanonical qCanonical
      let l := MarkFeedback.process C.model d leftState q (survivors ++ children probe) 0
      let r := MarkFeedback.process C.model d rightState probe (survivors ++ children q) 0
      have lEq := MarkFeedback.process_equivalent C.model d beforeLeft.2 q (List.Perm.refl (survivors ++ children probe))
      have rEq := MarkFeedback.process_equivalent C.model d beforeRight.2 probe (List.Perm.refl (survivors ++ children q))
      have equivalent : Equivalent r l :=
        ⟨rEq.1.trans (diamond.1.symm.trans lEq.1.symm), rEq.2.trans (diamond.2.symm.trans lEq.2.symm)⟩
      obtain ⟨final, finalTrace, finalEq⟩ := nominal_transport residual equivalent
      have residualTrace : NominalTrace C d (· ≤ ·) leftState ((q, read q 0) :: residualWord) final := by
        have stepTrace := NominalTrace.cons q _ leftQueue (legal qBefore pBefore) finalTrace
        change NominalTrace C d (· ≤ ·) leftState ((q, MarkFeedback.read C.model d s q 0) :: residualWord) final
        exact qStable ▸ stepTrace
      have terminal : final.pending = [] := by
        have same := finalEq.1.symm
        rw [empty] at same
        exact same.eq_nil
      refine ⟨final, _, residualTrace, terminal, ?_⟩
      have recorded := perm.cons (q, read q 0)
      rw [pStable] at recorded
      exact recorded.trans (List.Perm.swap _ _ _)

private theorem nominal_words_agree {C : Calendar N Date Label} {d : Nat} [Preorder Date]
    (causal : Causal C) {root s u v : QueueState N Date Label}
    (ties : TieAdmissible C d root) (reach : DatedPath C d root s)
    {word alternate : List (Occurrence Date Label × Bool)}
    (left : NominalTrace C d (· ≤ ·) s word u) (right : NominalTrace C d (· ≤ ·) s alternate v)
    (leftEmpty : u.pending = []) (rightEmpty : v.pending = []) : word.Perm alternate := by
  induction left generalizing v alternate with
  | nil s =>
    cases right with
    | nil => rfl
    | cons _ _ available => simp [leftEmpty] at available
  | @cons s _ p rest selected earliest word tail ih =>
    obtain ⟨last, residual, next, empty, perm⟩ :=
      take_nominal_head causal ties reach right rightEmpty p rest selected earliest
    have agrees := ih (reach.tail ⟨p, rest, selected, earliest, rfl⟩) next leftEmpty empty
    exact (agrees.cons _).trans perm.symm

/-- Every guarded trace can finish with the prescribed decision word up to
permutation. The memory and rank guarantees are those of the dated network. -/
theorem guarded_trace_refinement {p : Parameters N} (accepted : p.check = true)
    {rows : List (Row N)} {out : State N}
    (replay : TransactionReplay (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) rows out)
    (matching : ∀ row ∈ rows, RowMatches p row) (done : out.pending = []) :
    AutonomousFeedback.Schedule.SafeMemory Q d B rail (fun _ => 0) out ∧
    ∀ other word, Trace (calendar p) d (· ≤ ·) (MarkFeedback.initial N (seed p)) word other →
      word.length ≤ 4 * N ∧
      (∀ entry ∈ word, entry.2 = targetDecision entry.1.input) ∧
      (other.pending = [] → word.Perm (Transaction.word rows) ∧ other.writes = out.writes) ∧
      ∃ terminal suffix, Trace (calendar p) d (· ≤ ·) other suffix terminal ∧ terminal.pending = [] ∧
        (word ++ suffix).Perm (Transaction.word rows) ∧ terminal.writes = out.writes := by
  obtain ⟨⟨reserve⟩, ⟨rank, _⟩, causal, ties⟩ := guarded_conjuncts accepted
  let root := MarkFeedback.initial N (seed p)
  have reference := replay.trace
  obtain ⟨safe, _, _, _, terminalCounts, _, _, bound⟩ :=
    dated_network_memory Q d B rail W eta₀ (calendar p) (seed p) reserve (fun _ => 0)
      (fun _ => Nat.zero_le _) (by decide) causal ties
  refine ⟨(safe out reference.zero_error_replay.dated.mark).1, ?_⟩
  have agree {other : State N} {word : List (Probe N × Bool)} (tr : Trace (calendar p) d (· ≤ ·) root word other)
      (empty : other.pending = []) : word.Perm (Transaction.word rows) ∧ other.writes = out.writes :=
    ⟨nominal_words_agree causal ties .refl tr.zero_error_replay reference.zero_error_replay empty done,
      terminalCounts other out word (Transaction.word rows) tr reference empty done⟩
  intro other word tr
  obtain ⟨terminal, suffix, extension, empty⟩ := guarded_drain rank other
  have all := agree (tr.append extension) empty
  refine ⟨(bound rank other word tr).1, ?_, agree tr, terminal, suffix, extension, empty, all.1, all.2⟩
  intro entry mem
  have inReference := all.1.mem_iff.mp (List.mem_append_left _ mem)
  obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp inReference
  exact (matching row rowMem).2.2.1

end NetworkStability.NativeMultiToken
