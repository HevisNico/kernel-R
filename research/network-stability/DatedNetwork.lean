import DatedFairness
import DatedReplay
import Mathlib.Logic.Relation
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder

namespace NetworkStability.PhaseAdmission

open AutonomousFeedback (mass)
open AutonomousFeedback.Schedule (Config Equivalent SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address)

abbrev QueueState (N : Nat) (Date Input : Type) := Config (3 * N) (Occurrence Date Input)

/-- Every selected occurrence is earliest. There is no move from an empty queue. -/
def DatedMove (C : Calendar N Date Input) (d : Nat) [LE Date]
    (s t : QueueState N Date Input) : Prop :=
  ∃ p rest, s.pending.Perm (p :: rest) ∧ Earliest (· ≤ ·) p rest ∧
    t = MarkFeedback.process C.model d s p rest 0

abbrev DatedPath (C : Calendar N Date Input) (d : Nat) [LE Date] :=
  Relation.ReflTransGen (DatedMove C d)

def Eligible [LE Date] (s : QueueState N Date Input) (p : Occurrence Date Input) : Prop :=
  p ∈ s.pending ∧ ∀ q ∈ s.pending, p.due ≤ q.due

/-- Check the full competing footprint only against other earliest choices. -/
def TieRoom (C : Calendar N Date Input) (d : Nat) [LE Date]
    (s : QueueState N Date Input) : Prop :=
  ∀ p q, Eligible s p → Eligible s q → p ≠ q → C.model.cell p = C.model.cell q →
    ∀ fire, RoutedCalendar.HasRoom (MarkFeedback.score C.model d s p)
      (MarkFeedback.displacement C.model d p q fire) (MarkFeedback.displacement C.model d p q fire)

def TieAdmissible (C : Calendar N Date Input) (d : Nat) [LE Date]
    (root : QueueState N Date Input) : Prop :=
  ∀ s, DatedPath C d root s → TieRoom C d s

def Causal (C : Calendar N Date Input) [LE Date] : Prop :=
  ∀ p q, q ∈ C.route p → p.due ≤ q.due

theorem DatedMove.mark {C : Calendar N Date Input} {d} [LE Date] {s t}
    (step : DatedMove C d s t) : MarkFeedback.Move C.model d s t := by
  obtain ⟨p, rest, available, _, rfl⟩ := step
  exact .select _ _ _ available

theorem DatedPath.mark {C : Calendar N Date Input} {d} [LE Date] {s t}
    (path : DatedPath C d s t) : MarkFeedback.Path C.model d s t := by
  induction path with
  | refl => exact .nil _
  | tail _ step ih => exact MarkFeedback.path_trans ih (.cons step.mark (.nil _))

theorem NominalTrace.dated {C : Calendar N Date Input} {d} [LE Date] {s u word}
    (path : NominalTrace C d (· ≤ ·) s word u) : DatedPath C d s u := by
  induction path with
  | nil => exact .refl
  | cons p rest available first _ ih =>
    exact Relation.ReflTransGen.head ⟨p, rest, available, first, rfl⟩ ih

theorem TieAdmissible.of_global {C : Calendar N Date Input} {d root} [LE Date]
    (global : MarkFeedback.Admissible C.model d root) : TieAdmissible C d root := by
  classical
  intro s reach p q ep eq ne cell fire
  rcases global s reach.mark with exclusive | separated
  · have split := List.perm_cons_erase ep.1
    have inTail := (List.mem_cons.mp (split.mem_iff.mp eq.1)).resolve_left ne.symm
    have perm := split.trans ((List.perm_cons_erase inTail).cons p)
    have collision := ((perm.map C.model.cell).nodup_iff.mp exclusive)
    rw [List.map_cons, List.map_cons, cell] at collision
    exact ((List.nodup_cons.mp collision).1 (by simp)).elim
  · exact separated p ep.1 q eq.1 ne cell fire

private theorem eligible_of_selection [Preorder Date] {s : QueueState N Date Input} {p rest}
    (available : s.pending.Perm (p :: rest)) (first : Earliest (· ≤ ·) p rest) :
    Eligible s p := by
  refine ⟨available.mem_iff.mpr (by simp), fun q mem => ?_⟩
  rcases List.mem_cons.mp (available.mem_iff.mp mem) with rfl | later
  · exact le_rfl
  · exact first q later

private theorem earliest_of_eligible [LE Date] {s : QueueState N Date Input} {p rest}
    (available : s.pending.Perm (p :: rest)) (eligible : Eligible s p) :
    Earliest (· ≤ ·) p rest :=
  fun q mem => eligible.2 q (available.mem_iff.mpr (List.mem_cons_of_mem _ mem))

private theorem read_stable_at_tie {C : Calendar N Date Input} {d s} [LE Date]
    (room : TieRoom C d s) {p q : Occurrence Date Input} (ep : Eligible s p) (eq : Eligible s q)
    (different : p ≠ q) (rest : List (Occurrence Date Input)) :
    MarkFeedback.read C.model d (MarkFeedback.process C.model d s q rest 0) p 0 =
      MarkFeedback.read C.model d s p 0 := by
  unfold MarkFeedback.read
  rw [MarkFeedback.score_after, Int.add_zero]
  by_cases cell : C.model.cell p = C.model.cell q
  · exact MarkFeedback.read_eq_of_room _ _ _ _ ⟨Int.le_refl _, Int.le_refl _⟩
      (room p q ep eq different cell (MarkFeedback.read C.model d s q 0))
  · rw [MarkFeedback.different_cells_displacement C.model d p q cell]

private theorem later_children {C : Calendar N Date Input} [Preorder Date]
    (causal : Causal C) {p q : Occurrence Date Input} (before : q.due ≤ p.due) (fire : Bool) :
    ∀ child ∈ MarkFeedback.emitted C.model p fire, q.due ≤ child.due := by
  intro child mem
  cases fire
  · simp [MarkFeedback.emitted] at mem
  · exact before.trans (causal p child mem)

theorem move_transport {C : Calendar N Date Input} {d} [Preorder Date] {s t u}
    (same : Equivalent s t) (step : DatedMove C d s u) :
    ∃ v, DatedMove C d t v ∧ Equivalent u v := by
  obtain ⟨p, rest, available, first, rfl⟩ := step
  exact ⟨_, ⟨p, rest, same.1.symm.trans available, first, rfl⟩,
    MarkFeedback.process_equivalent C.model d same.2 p (List.Perm.refl _)⟩

theorem local_tie_diamond {C : Calendar N Date Input} {d} [Preorder Date] {s a b}
    (causal : Causal C) (room : TieRoom C d s)
    (left : DatedMove C d s a) (right : DatedMove C d s b) :
    Equivalent a b ∨ ∃ u v, DatedMove C d a u ∧ DatedMove C d b v ∧ Equivalent u v := by
  classical
  obtain ⟨p, ps, availP, firstP, rfl⟩ := left
  obtain ⟨q, qs, availQ, firstQ, rfl⟩ := right
  have heads := availP.symm.trans availQ
  by_cases same : p = q
  · subst q
    exact Or.inl (MarkFeedback.process_equivalent C.model d rfl p heads.cons_inv)
  have inPs := (List.mem_cons.mp (heads.mem_iff.mpr (by simp : q ∈ q :: qs))).resolve_left (fun eq => same eq.symm)
  let rest := ps.erase q
  have pTail : ps.Perm (q :: rest) := List.perm_cons_erase inPs
  have qTail : qs.Perm (p :: rest) :=
    ((List.Perm.swap _ _ _).trans ((pTail.symm.cons p).trans heads)).cons_inv.symm
  have ep := eligible_of_selection availP firstP
  have eq := eligible_of_selection availQ firstQ
  let ep' := MarkFeedback.emitted C.model p (MarkFeedback.read C.model d s p 0)
  let eq' := MarkFeedback.emitted C.model q (MarkFeedback.read C.model d s q 0)
  have firstAfter {x y : Occurrence Date Input} (ex : Eligible s x) (ey : Eligible s y) :
      Earliest (· ≤ ·) x (rest ++ MarkFeedback.emitted C.model y (MarkFeedback.read C.model d s y 0)) := by
    intro z mem
    rcases List.mem_append.mp mem with old | child
    · exact ex.2 z (availP.mem_iff.mpr (List.mem_cons_of_mem _
        (pTail.mem_iff.mpr (List.mem_cons_of_mem _ old))))
    · exact later_children causal (ex.2 y ey.1) _ z child
  have eqLeft : Equivalent (MarkFeedback.process C.model d s p ps 0)
      (MarkFeedback.process C.model d s p (q :: rest) 0) :=
    MarkFeedback.process_equivalent C.model d rfl p pTail
  have eqRight : Equivalent (MarkFeedback.process C.model d s q qs 0)
      (MarkFeedback.process C.model d s q (p :: rest) 0) :=
    MarkFeedback.process_equivalent C.model d rfl q qTail
  have diamond := MarkFeedback.two_occurrences_commute C.model d s p q rest
    (read_stable_at_tie room ep eq same (p :: rest))
    (read_stable_at_tie room eq ep (fun h => same h.symm) (q :: rest))
  refine Or.inr ⟨_, _, ⟨q, rest ++ ep', eqLeft.1, firstAfter eq ep, rfl⟩,
    ⟨p, rest ++ eq', eqRight.1, firstAfter ep eq, rfl⟩, ?_⟩
  have leftEq := MarkFeedback.process_equivalent C.model d eqLeft.2 q (List.Perm.refl (rest ++ ep'))
  have rightEq := MarkFeedback.process_equivalent C.model d eqRight.2 p (List.Perm.refl (rest ++ eq'))
  exact ⟨leftEq.1.trans (diamond.1.trans rightEq.1.symm), leftEq.2.trans (diamond.2.trans rightEq.2.symm)⟩

inductive DatedBudget (C : Calendar N Date Input) (d : Nat) [LE Date] :
    Nat → QueueState N Date Input → QueueState N Date Input → Prop where
  | nil (n) (s) : DatedBudget C d n s s
  | cons {n s t u} : DatedMove C d s t → DatedBudget C d n t u → DatedBudget C d (n + 1) s u

private theorem budget_transport {C : Calendar N Date Input} {d n} [Preorder Date] {s t u}
    (same : Equivalent s t) (path : DatedBudget C d n s u) :
    ∃ v, DatedBudget C d n t v ∧ Equivalent u v := by
  induction path generalizing t with
  | nil => exact ⟨_, .nil _ _, same⟩
  | cons first _ ih =>
    obtain ⟨v, step, eq⟩ := move_transport same first
    obtain ⟨last, tail, final⟩ := ih eq
    exact ⟨last, .cons step tail, final⟩

private theorem budget_pad {C : Calendar N Date Input} {d n} [LE Date] {s t}
    (path : DatedBudget C d n s t) : DatedBudget C d (n + 1) s t := by
  induction path with
  | nil => exact .nil _ _
  | cons first _ ih => exact .cons first ih

private theorem move_writes_le {C : Calendar N Date Input} {d} [LE Date] {s t}
    (step : DatedMove C d s t) (i : Fin (3 * N)) : s.writes i ≤ t.writes i :=
  MarkFeedback.move_writes_mono step.mark i

private theorem budget_diamond {C : Calendar N Date Input} {d root} [Preorder Date]
    (causal : Causal C) (diamond : TieAdmissible C d root) {s a b n}
    (reach : DatedPath C d root s) (step : DatedMove C d s a)
    (path : DatedBudget C d n s b) :
    ∃ u v, DatedBudget C d n a u ∧ (v = b ∨ DatedMove C d b v) ∧ Equivalent u v := by
  induction path generalizing a with
  | nil => exact ⟨a, a, .nil _ _, Or.inr step, List.Perm.refl _, rfl⟩
  | cons first tail ih =>
    rcases local_tie_diamond causal (diamond _ reach) step first with
        same | ⟨x, y, ax, next, xy⟩
    · obtain ⟨v, residual, eq⟩ := budget_transport ⟨same.1.symm, same.2.symm⟩ tail
      exact ⟨v, _, budget_pad residual, Or.inl rfl, ⟨eq.1.symm, eq.2.symm⟩⟩
    · obtain ⟨u, v, residual, short, uv⟩ := ih (reach.tail first) next
      obtain ⟨last, transported, eq⟩ := budget_transport ⟨xy.1.symm, xy.2.symm⟩ residual
      exact ⟨last, v, .cons ax transported, short, ⟨eq.1.symm.trans uv.1, eq.2.symm.trans uv.2⟩⟩

private theorem dated_budget {C : Calendar N Date Input} {d} [LE Date] {s t}
    (path : DatedPath C d s t) : ∃ n, DatedBudget C d n s t := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .nil _ _⟩
  | head first _ ih =>
    obtain ⟨n, tail⟩ := ih
    exact ⟨n + 1, .cons first tail⟩

private theorem budget_path {C : Calendar N Date Input} {d n} [LE Date] {s t}
    (path : DatedBudget C d n s t) : DatedPath C d s t := by
  induction path with
  | nil => exact .refl
  | cons first _ ih => exact Relation.ReflTransGen.head first ih

/-- The strong local diamond lifts to finite continuations even without
a termination hypothesis. All residual choices still respect dates. -/
theorem dated_confluent {C : Calendar N Date Input} {d root} [Preorder Date]
    (causal : Causal C) (diamond : TieAdmissible C d root) {a b}
    (left : DatedPath C d root a) (right : DatedPath C d root b) :
    ∃ u v, DatedPath C d a u ∧ DatedPath C d b v ∧ Equivalent u v := by
  obtain ⟨n, sized⟩ := dated_budget right
  induction left generalizing b with
  | refl => exact ⟨b, b, budget_path sized, .refl, List.Perm.refl _, rfl⟩
  | @tail s t _ first ih =>
    obtain ⟨u, v, fromS, fromB, uv⟩ := ih (budget_path sized) sized
    obtain ⟨m, residual⟩ := dated_budget fromS
    obtain ⟨x, y, fromT, fromU, xy⟩ := budget_diamond causal diamond ‹DatedPath C d root s› first residual
    rcases fromU with rfl | advance
    · exact ⟨x, v, budget_path fromT, fromB, ⟨xy.1.trans uv.1, xy.2.trans uv.2⟩⟩
    · obtain ⟨z, next, yz⟩ := move_transport uv advance
      exact ⟨x, z, budget_path fromT, fromB.tail next, ⟨xy.1.trans yz.1, xy.2.trans yz.2⟩⟩

theorem dated_terminal_unique {C : Calendar N Date Input} {d root} [Preorder Date]
    (causal : Causal C) (diamond : TieAdmissible C d root) {a b}
    (left : DatedPath C d root a) (right : DatedPath C d root b)
    (emptyA : a.pending = []) (emptyB : b.pending = []) : a.writes = b.writes := by
  obtain ⟨u, v, fromA, fromB, equal⟩ := dated_confluent causal diamond left right
  rw [MarkFeedback.path_from_empty emptyA fromA.mark, MarkFeedback.path_from_empty emptyB fromB.mark] at equal
  exact equal.2


theorem EarliestStep.dated {C : Calendar N Date Input} {d} [LE Date] {s t}
    (step : EarliestStep C d (· ≤ ·) s t) : DatedPath C d s t := by
  rcases step with ⟨_, rfl⟩ | move
  · exact .refl
  · exact Relation.ReflTransGen.single move

def DatedWriteFair (C : Calendar N Date Input) (d : Nat) [LE Date]
    (state : Nat → QueueState N Date Input) : Prop :=
  ∀ k t, DatedPath C d (state k) t → ∃ j, k ≤ j ∧ ∀ i, t.writes i ≤ (state j).writes i

private theorem step_catches_head {C : Calendar N Date Input} {d root} [Preorder Date]
    (causal : Causal C) (diamond : TieAdmissible C d root)
    (state : Nat → QueueState N Date Input)
    (reach : ∀ k, DatedPath C d root (state k))
    (steps : ∀ k, EarliestStep C d (· ≤ ·) (state k) (state (k + 1)))
    (p : Occurrence Date Input) {j : Nat} (gone : p ∉ (state j).pending)
    {k : Nat} (later : k ≤ j) {rest : List (Occurrence Date Input)}
    (available : (state k).pending.Perm (p :: rest)) (first : Earliest (· ≤ ·) p rest)
    {n b} (path : DatedBudget C d n (MarkFeedback.process C.model d (state k) p rest 0) b) :
    ∃ l u, k ≤ l ∧ DatedBudget C d n (state l) u ∧ ∀ i, b.writes i ≤ u.writes i := by
  classical
  induction lengthEq : j - k using Nat.strongRecOn generalizing k rest b with
  | ind gap ih =>
    have present := eligible_of_selection available first
    have before : k < j := by
      by_cases lt : k < j
      · exact lt
      have same : k = j := by omega
      exact (gone (same ▸ present.1)).elim
    rcases steps k with ⟨empty, _⟩ | ⟨q, qs, actual, earliest, next⟩
    · have := present.1
      simp [empty] at this
    by_cases same : p = q
    · subst q
      have eq := MarkFeedback.process_equivalent C.model d (s := state k) (t := state k)
        rfl p (available.symm.trans actual).cons_inv
      rw [← next] at eq
      obtain ⟨u, residual, eqU⟩ := budget_transport eq path
      exact ⟨k + 1, u, by omega, residual, fun i => Nat.le_of_eq (congrFun eqU.2 i)⟩
    · have left : DatedMove C d (state k) (MarkFeedback.process C.model d (state k) p rest 0) :=
        ⟨p, rest, available, first, rfl⟩
      have eligibleQ := eligible_of_selection actual earliest
      have perm := actual.symm.trans available
      have pIn : p ∈ qs := (List.mem_cons.mp (actual.mem_iff.mp present.1)).resolve_left same
      let residual := qs.erase p
      have queue : qs.Perm (p :: residual) := List.perm_cons_erase pIn
      have qTail : rest.Perm (q :: residual) :=
        ((List.Perm.swap _ _ _).trans ((queue.symm.cons q).trans perm)).cons_inv.symm
      let pFire := MarkFeedback.emitted C.model p (MarkFeedback.read C.model d (state k) p 0)
      let qFire := MarkFeedback.emitted C.model q (MarkFeedback.read C.model d (state k) q 0)
      let s := state k
      let a := MarkFeedback.process C.model d s p (q :: residual) 0
      let c := MarkFeedback.process C.model d s q (p :: residual) 0
      have eqA : Equivalent (MarkFeedback.process C.model d s p rest 0) a :=
        MarkFeedback.process_equivalent C.model d rfl p qTail
      have eqC : Equivalent (state (k + 1)) c := by
        rw [next]
        exact MarkFeedback.process_equivalent C.model d rfl q queue
      have leftCanonical : DatedMove C d s a :=
        ⟨p, q :: residual, available.trans (qTail.cons p),
          earliest_of_eligible (available.trans (qTail.cons p)) present, rfl⟩
      have residualDate (x : Occurrence Date Input) (ex : Eligible s x) {y} (ey : Eligible s y) :
          Earliest (· ≤ ·) x (residual ++ MarkFeedback.emitted C.model y (MarkFeedback.read C.model d s y 0)) := by
        intro z hz
        rcases List.mem_append.mp hz with tail | child
        · exact ex.2 z (actual.mem_iff.mpr (List.mem_cons_of_mem _
            (queue.mem_iff.mpr (List.mem_cons_of_mem _ tail))))
        · exact later_children causal (ex.2 y ey.1) _ z child
      obtain ⟨b', pathA, sameB⟩ := budget_transport eqA path
      have afterP : DatedMove C d a (MarkFeedback.process C.model d a q (residual ++ pFire) 0) :=
        ⟨_, _, List.Perm.refl _, residualDate q eligibleQ present, rfl⟩
      obtain ⟨u, v, moved, short, uv⟩ :=
        budget_diamond causal diamond ((reach k).tail leftCanonical) afterP pathA
      have joined := MarkFeedback.two_occurrences_commute C.model d s p q residual
        (read_stable_at_tie (diamond _ (reach k)) present eligibleQ same _)
        (read_stable_at_tie (diamond _ (reach k)) eligibleQ present (fun h => same h.symm) _)
      have afterC := MarkFeedback.process_equivalent C.model d (s := c) (t := state (k + 1))
        eqC.2.symm p (List.Perm.refl (residual ++ qFire))
      obtain ⟨continued, remaining, eqU⟩ := budget_transport
        ⟨joined.1.trans afterC.1, joined.2.trans afterC.2⟩ moved
      obtain ⟨l, out, time, finish, counts⟩ := ih (j - (k + 1)) (by omega)
        (k := k + 1) (by omega) eqC.1 (residualDate p present eligibleQ) remaining rfl
      refine ⟨l, out, by omega, finish, fun i => ?_⟩
      have monotone : b'.writes i ≤ v.writes i := by
        rcases short with rfl | mv
        · exact Nat.le_refl _
        · exact move_writes_le mv i
      rw [← congrFun sameB.2 i, ← congrFun uv.2 i, congrFun eqU.2 i] at monotone
      exact Nat.le_trans monotone (counts i)

theorem dated_write_fair {C : Calendar N Date Input} {d root} [Preorder Date]
    (causal : Causal C) (diamond : TieAdmissible C d root)
    (state : Nat → QueueState N Date Input) (starts : state 0 = root)
    (steps : ∀ k, EarliestStep C d (· ≤ ·) (state k) (state (k + 1)))
    (clears : ClearsDates (· ≤ ·) state) : DatedWriteFair C d state := by
  have reach (k : Nat) : DatedPath C d root (state k) := by
    induction k with
    | zero => rw [starts]
    | succ k ih => exact ih.trans (steps k).dated
  have dominate (n : Nat) (k : Nat) (t : QueueState N Date Input)
      (path : DatedBudget C d n (state k) t) :
      ∃ j, k ≤ j ∧ ∀ i, t.writes i ≤ (state j).writes i := by
    induction n generalizing k t with
    | zero => cases path; exact ⟨k, Nat.le_refl _, fun _ => Nat.le_refl _⟩
    | succ n ih =>
      cases path with
      | nil => exact ⟨k, Nat.le_refl _, fun _ => Nat.le_refl _⟩
      | cons first tail =>
        obtain ⟨p, rest, pending, due, rfl⟩ := first
        obtain ⟨j, later, clear⟩ := clears k p (pending.mem_iff.mpr (by simp))
        obtain ⟨l, u, time, residual, counts⟩ :=
          step_catches_head causal diamond state reach steps p (fun mem => clear p mem le_rfl)
            later pending due tail
        obtain ⟨last, lastTime, bound⟩ := ih l u residual
        exact ⟨last, Nat.le_trans time lastTime, fun i => Nat.le_trans (counts i) (bound i)⟩
  intro k t path
  obtain ⟨n, budget⟩ := dated_budget path
  exact dominate n k t budget


/-- Finite joining gives a common memory limit for fair dated runs.
The maximal counts are taken over dated continuations only. -/
theorem dated_limit_unique (Q d : Nat) {C : Calendar N Date Input} [Preorder Date]
    {seed} (reserve : MarkFeedback.Reserve Q C.model seed)
    (causal : Causal C) (diamond : TieAdmissible C d (MarkFeedback.initial N seed))
    (a b : Nat → QueueState N Date Input)
    (startA : a 0 = MarkFeedback.initial N seed) (startB : b 0 = MarkFeedback.initial N seed)
    (stepA : ∀ k, EarliestStep C d (· ≤ ·) (a k) (a (k + 1)))
    (stepB : ∀ k, EarliestStep C d (· ≤ ·) (b k) (b (k + 1)))
    (clearA : ClearsDates (· ≤ ·) a) (clearB : ClearsDates (· ≤ ·) b) :
    ∃ counts, MarkFeedback.Stabilizes a counts ∧ MarkFeedback.Stabilizes b counts := by
  let root := MarkFeedback.initial N seed
  have reach (state : Nat → QueueState N Date Input) (start : state 0 = root)
      (step : ∀ k, EarliestStep C d (· ≤ ·) (state k) (state (k + 1))) :
      ∀ k, DatedPath C d root (state k) := by
    intro k
    induction k with
    | zero => rw [start]
    | succ k ih => exact ih.trans (step k).dated
  have stable (state : Nat → QueueState N Date Input) (start : state 0 = root)
      (step : ∀ k, EarliestStep C d (· ≤ ·) (state k) (state (k + 1))) :
      ∃ counts, MarkFeedback.Stabilizes state counts := by
    apply MarkFeedback.counts_stabilize Q
    · intro k i
      have paid := MarkFeedback.path_reserve reserve (reach state start step k).mark i
      have cap := reserve.seed_bound i
      change (state k).writes i + _ ≤ 0 + mass (reserve.credit i) seed at paid
      omega
    · exact fun k i => MarkFeedback.path_writes_mono (step k).dated.mark i
  obtain ⟨x, k, atA⟩ := stable a startA stepA
  obtain ⟨y, l, atB⟩ := stable b startB stepB
  obtain ⟨u, v, fromA, fromB, joined⟩ :=
    dated_confluent causal diamond (reach a startA stepA k) (reach b startB stepB l)
  obtain ⟨ka, lateA, boundA⟩ := dated_write_fair causal diamond a startA stepA clearA k u fromA
  obtain ⟨kb, lateB, boundB⟩ := dated_write_fair causal diamond b startB stepB clearB l v fromB
  have same : x = y := by
    funext i
    have fromAx := MarkFeedback.path_writes_mono fromA.mark i
    have fromBy := MarkFeedback.path_writes_mono fromB.mark i
    rw [atA k (Nat.le_refl _)] at fromAx
    rw [atB l (Nat.le_refl _)] at fromBy
    rw [atA ka lateA] at boundA
    rw [atB kb lateB] at boundB
    have eq : u.writes i = v.writes i := congrFun joined.2 i
    exact Nat.le_antisymm (Nat.le_trans (eq ▸ fromAx) (boundB i))
      (Nat.le_trans (eq.symm ▸ fromBy) (boundA i))
  exact ⟨x, ⟨k, atA⟩, same.symm ▸ ⟨l, atB⟩⟩

/-- Network memory for an earliest-date scheduler. The reserve covers
all abstract paths. The rank is optional for memory stabilization. -/
theorem dated_network_memory (Q d B rail W eta : Nat) {N : Nat} {Date Input : Type} [Preorder Date]
    (C : Calendar N Date Input) (seed : List (Occurrence Date Input))
    (reserve : MarkFeedback.Reserve Q C.model seed)
    (base : Fin (3 * N) → Nat) (baseBound : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (causal : Causal C) (ties : TieAdmissible C d (MarkFeedback.initial N seed)) :
    (∀ s, MarkFeedback.Path C.model d (MarkFeedback.initial N seed) s →
      SafeMemory Q d B rail base s ∧
      ∀ i : Fin N, s.writes (Address.mk i .port0).encode + s.writes (Address.mk i .port1).encode +
        s.writes (Address.mk i .recovery).encode ≤ 3 * Q) ∧
    (∀ s word, Trace C d (· ≤ ·) (MarkFeedback.initial N seed) word s →
      NominalTrace C d (· ≤ ·) (MarkFeedback.initial N seed) word s) ∧
    (∀ state : Nat → QueueState N Date Input, state 0 = MarkFeedback.initial N seed →
      (∀ k, ∃ word, Trace C d (· ≤ ·) (state k) word (state (k + 1))) →
      ∃ counts, MarkFeedback.Stabilizes state counts) ∧
    (∀ s a b, DatedPath C d (MarkFeedback.initial N seed) s →
      DatedMove C d s a → DatedMove C d s b →
      Equivalent a b ∨ ∃ u v, DatedMove C d a u ∧ DatedMove C d b v ∧ Equivalent u v) ∧
    (∀ a b wa wb, Trace C d (· ≤ ·) (MarkFeedback.initial N seed) wa a →
      Trace C d (· ≤ ·) (MarkFeedback.initial N seed) wb b →
      a.pending = [] → b.pending = [] → a.writes = b.writes) ∧
    (∀ state : Nat → QueueState N Date Input, state 0 = MarkFeedback.initial N seed →
      (∀ k, EarliestStep C d (· ≤ ·) (state k) (state (k + 1))) →
      ClearsDates (· ≤ ·) state → DatedWriteFair C d state) ∧
    (∀ a b : Nat → QueueState N Date Input, a 0 = MarkFeedback.initial N seed →
      b 0 = MarkFeedback.initial N seed →
      (∀ k, EarliestStep C d (· ≤ ·) (a k) (a (k + 1))) →
      (∀ k, EarliestStep C d (· ≤ ·) (b k) (b (k + 1))) →
      ClearsDates (· ≤ ·) a → ClearsDates (· ≤ ·) b →
      ∃ counts, MarkFeedback.Stabilizes a counts ∧ MarkFeedback.Stabilizes b counts) ∧
    (MarkFeedback.Rank W eta C.model seed →
      ∀ s word, Trace C d (· ≤ ·) (MarkFeedback.initial N seed) word s →
        word.length ≤ W * N ∧ (word.length = W * N → s.pending = [])) := by
  refine ⟨?_, fun _ _ h => h.zero_error_replay, ?_, ?_, ?_,
    dated_write_fair causal ties, dated_limit_unique Q d reserve causal ties, ?_⟩
  · intro s reach
    have safe := MarkFeedback.path_safe Q d B rail C.model seed reserve base baseBound headroom s reach
    exact ⟨safe, MarkFeedback.cell_write_bound Q s (fun i => (safe.2 i).1)⟩
  · intro state start steps
    exact MarkFeedback.certified_execution_stabilizes Q d C.model seed reserve state start
      (fun k => by obtain ⟨_, trace⟩ := steps k; exact trace.certified)
  · exact fun s _ _ reach => local_tie_diamond causal (ties s reach)
  · exact fun _ _ _ _ a b => dated_terminal_unique causal ties a.zero_error_replay.dated b.zero_error_replay.dated
  · intro rank s word trace
    have paid := trace.rank_bound rank
    change word.length + mass rank.weight s.pending ≤ mass rank.weight seed at paid
    have limit := rank.seed_bound
    refine ⟨by omega, fun full => ?_⟩
    cases queue : s.pending with
    | nil => rfl
    | cons p rest =>
      rw [queue] at paid
      change word.length + (rank.weight p + mass rank.weight rest) ≤ _ at paid
      have h := rank.decreases p
      have pos := rank.positive
      omega


/-- The reserve accounts for any error values along an earliest-date
execution. Margins are only needed for comparing decisions. -/
theorem dated_noisy_safe (Q d B rail : Nat) {C : Calendar N Date Input} [LE Date]
    {seed} (reserve : MarkFeedback.Reserve Q C.model seed)
    (base : Fin (3 * N) → Nat) (baseBound : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (state : Nat → QueueState N Date Input) (start : state 0 = MarkFeedback.initial N seed)
    (error : Nat → Int)
    (step : ∀ k, ((state k).pending = [] ∧ state (k + 1) = state k) ∨
      ∃ p rest, (state k).pending.Perm (p :: rest) ∧ Earliest (· ≤ ·) p rest ∧
        state (k + 1) = MarkFeedback.process C.model d (state k) p rest (error k)) :
    (∀ k, SafeMemory Q d B rail base (state k)) ∧
      ∃ counts, MarkFeedback.Stabilizes state counts := by
  have cap (k : Nat) (i : Fin (3 * N)) :
      (state k).writes i + mass (reserve.credit i) (state k).pending ≤ Q := by
    induction k with
    | zero => rw [start]; simpa [MarkFeedback.initial] using reserve.seed_bound i
    | succ k ih =>
      rcases step k with ⟨_, eq⟩ | ⟨p, rest, available, _, eq⟩
      · rw [eq]
        exact ih
      · rw [eq]
        exact Nat.le_trans (MarkFeedback.process_reserve C.model d Q reserve _ p rest available _ i) ih
  have weights (k : Nat) (i : Fin (3 * N)) : (state k).writes i ≤ Q :=
    Nat.le_trans (Nat.le_add_right _ _) (cap k i)
  refine ⟨fun k => MarkFeedback.safe_of_counts Q d B rail base baseBound headroom _ (weights k), ?_⟩
  apply MarkFeedback.counts_stabilize Q state weights
  intro k i
  rcases step k with ⟨_, eq⟩ | ⟨p, rest, _, _, eq⟩
  · rw [eq]
    exact Nat.le_refl _
  · rw [eq]
    exact Nat.le_add_right _ _


/-- Compare completed dated prefixes while keeping the actual future
queue in the original configurations. Clipping preserves causal
routing. The tie hypothesis is checked on the clipped calendar. -/
theorem dated_horizon_unique {C : Calendar N Date Input} {d} [Preorder Date]
    (horizon : Date) (seed : List (Occurrence Date Input))
    (causal : Causal C)
    (ties : TieAdmissible (C.through (· ≤ ·) horizon) d
      (horizonCut (· ≤ ·) horizon (MarkFeedback.initial N seed)))
    {a b wa wb} (left : Trace C d (· ≤ ·) (MarkFeedback.initial N seed) wa a)
    (right : Trace C d (· ≤ ·) (MarkFeedback.initial N seed) wb b)
    (leftDates : ∀ row ∈ wa, row.1.due ≤ horizon) (rightDates : ∀ row ∈ wb, row.1.due ≤ horizon)
    (leftClear : ∀ p ∈ a.pending, ¬ p.due ≤ horizon)
    (rightClear : ∀ p ∈ b.pending, ¬ p.due ≤ horizon) : a.writes = b.writes := by
  have cutCausal : Causal (C.through (· ≤ ·) horizon) := by
    intro p q mem
    exact causal p q (List.mem_filter.mp mem).1
  exact dated_terminal_unique cutCausal ties
    (a := horizonCut (· ≤ ·) horizon a) (b := horizonCut (· ≤ ·) horizon b)
    (left.through horizon leftDates).zero_error_replay.dated
    (right.through horizon rightDates).zero_error_replay.dated
    (horizonCut_empty leftClear) (horizonCut_empty rightClear)

end NetworkStability.PhaseAdmission
