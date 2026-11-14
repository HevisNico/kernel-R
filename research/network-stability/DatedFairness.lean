import PhaseAdmission

namespace NetworkStability.PhaseAdmission

open AutonomousFeedback.Schedule (Config Equivalent)
open MarkFeedback (BudgetPath)

/-- A sampled earliest-date execution selects one eligible occurrence
per step, and stutters when the queue is empty. -/
def EarliestStep (C : Calendar N Date Input) (d : Nat) (le : Date → Date → Prop)
    (s t : Config (3 * N) (Occurrence Date Input)) : Prop :=
  (s.pending = [] ∧ t = s) ∨
  ∃ p rest, s.pending.Perm (p :: rest) ∧ Earliest le p rest ∧
    t = MarkFeedback.process C.model d s p rest 0

/-- Every date visible at a cut is eventually cleared. All later arrivals
at that date are included in the obligation. -/
def ClearsDates (le : Date → Date → Prop)
    (state : Nat → Config (3 * N) (Occurrence Date Input)) : Prop :=
  ∀ k p, p ∈ (state k).pending → ∃ j, k ≤ j ∧
    ∀ q ∈ (state j).pending, ¬ le q.due p.due

/-- For each date, a finite budget pays for all work
at or before that date generated after any cut. Each selected sublevel occurrence
must strictly reduce the budget; work due later does not have to do so. -/
def SublevelBudget (le : Date → Date → Prop)
    (state : Nat → Config (3 * N) (Occurrence Date Input)) : Prop :=
  ∀ cutoff : Date, ∃ budget : Nat → Nat,
    ∀ k, (∃ q ∈ (state k).pending, le q.due cutoff) → budget (k + 1) < budget k

theorem clears_of_sublevel_budget {le : Date → Date → Prop}
    (state : Nat → Config (3 * N) (Occurrence Date Input)) (paid : SublevelBudget le state) :
    ClearsDates le state := by
  intro k p _
  obtain ⟨budget, decrease⟩ := paid p.due
  have drain : ∀ limit k, budget k = limit →
      ∃ j, k ≤ j ∧ ∀ q ∈ (state j).pending, ¬ le q.due p.due := by
    intro limit
    induction limit using Nat.strongRecOn with
    | ind limit ih =>
      intro k count
      classical
      by_cases more : ∃ q ∈ (state k).pending, le q.due p.due
      · obtain ⟨j, later, clear⟩ := ih (budget (k + 1))
          (count ▸ decrease k more) (k + 1) rfl
        exact ⟨j, by omega, clear⟩
      · exact ⟨k, Nat.le_refl _, fun q mem due => more ⟨q, mem, due⟩⟩
  exact drain (budget k) k rfl

theorem earliest_step_path {C : Calendar N Date Input} {d le s t}
    (step : EarliestStep C d le s t) : MarkFeedback.Path C.model d s t := by
  rcases step with ⟨_, rfl⟩ | ⟨p, rest, available, _, rfl⟩
  · exact .nil _
  · exact .cons (.select _ p rest available) (.nil _)

private theorem budget_transport {M : MarkFeedback.Model N P} {d n s t u}
    (same : Equivalent s t) (path : BudgetPath M d n s u) :
    ∃ v, BudgetPath M d n t v ∧ Equivalent u v := by
  induction path generalizing t with
  | nil => exact ⟨_, .nil _ _, same⟩
  | cons first _ ih =>
    obtain ⟨v, step, eq⟩ := MarkFeedback.move_transport same first
    obtain ⟨last, rest, final⟩ := ih eq
    exact ⟨last, .cons step rest, final⟩

private theorem budget_of_path {M : MarkFeedback.Model N P} {d s t}
    (path : MarkFeedback.Path M d s t) : ∃ n, BudgetPath M d n s t := by
  induction path with
  | nil => exact ⟨0, .nil _ _⟩
  | cons first _ ih =>
    obtain ⟨n, tail⟩ := ih
    exact ⟨n + 1, .cons first tail⟩

private theorem pad_budget {M : MarkFeedback.Model N P} {d n s t}
    (path : BudgetPath M d n s t) : BudgetPath M d (n + 1) s t := by
  induction path with
  | nil => exact .nil _ _
  | cons first _ ih => exact .cons first ih

/-- Commute one actual step across a hypothetical continuation. Its endpoint
can only gain writes, and the remaining continuation does not get longer. -/
private theorem commute_budget {M : MarkFeedback.Model N P} {d root}
    (diamond : MarkFeedback.Admissible M d root) {s a b n}
    (reach : MarkFeedback.Path M d root s) (step : MarkFeedback.Move M d s a)
    (path : BudgetPath M d n s b) :
    ∃ u v, BudgetPath M d n a u ∧ (v = b ∨ MarkFeedback.Move M d b v) ∧ Equivalent u v := by
  induction path generalizing a with
  | nil => exact ⟨a, a, .nil _ _, Or.inr step, ⟨List.Perm.refl _, rfl⟩⟩
  | cons first _ ih =>
    rcases MarkFeedback.local_diamond M d (diamond _ reach) step first with
      same | ⟨x, y, ax, next, xy⟩
    · obtain ⟨v, tail, eq⟩ := budget_transport ⟨same.1.symm, same.2.symm⟩ ‹BudgetPath _ _ _ _ _›
      exact ⟨v, _, pad_budget tail, Or.inl rfl, ⟨eq.1.symm, eq.2.symm⟩⟩
    · obtain ⟨u, v, tail, short, uv⟩ :=
        ih (MarkFeedback.path_trans reach (.cons first (.nil _))) next
      obtain ⟨last, transported, eq⟩ := budget_transport ⟨xy.1.symm, xy.2.symm⟩ tail
      exact ⟨last, v, .cons ax transported, short, ⟨eq.1.symm.trans uv.1, eq.2.symm.trans uv.2⟩⟩

/-- By the clearing cut, the scheduler must have matched the chosen
occurrence. The method uses the MARK diamond even for continuations that
were permitted to ignore the date order. -/
private theorem catch_by_cut {C : Calendar N Date Input} {d le root}
    (diamond : MarkFeedback.Admissible C.model d root)
    (state : Nat → Config (3 * N) (Occurrence Date Input))
    (reach : ∀ k, MarkFeedback.Path C.model d root (state k))
    (steps : ∀ k, EarliestStep C d le (state k) (state (k + 1)))
    (p : Occurrence Date Input) {j : Nat} (cleared : p ∉ (state j).pending)
    {k : Nat} (later : k ≤ j)
    {rest : List (Occurrence Date Input)} (available : (state k).pending.Perm (p :: rest))
    {n b} (path : BudgetPath C.model d n (MarkFeedback.process C.model d (state k) p rest 0) b) :
    ∃ l u, k ≤ l ∧ BudgetPath C.model d n (state l) u ∧ ∀ i, b.writes i ≤ u.writes i := by
  classical
  induction h : j - k using Nat.strongRecOn generalizing k rest b with
  | ind gap ih =>
    have mem := available.mem_iff.mpr (List.mem_cons_self ..)
    have before : k < j := by
      by_cases lt : k < j
      · exact lt
      have ge : j ≤ k := by omega
      have eq := Nat.le_antisymm later ge
      exact (cleared (eq ▸ mem)).elim
    rcases steps k with ⟨empty, _⟩ | ⟨q, qs, actual, _, next⟩
    · simp [empty] at mem
    by_cases same : q = p
    · subst q
      have eq := MarkFeedback.process_equivalent C.model d (s := state k) (t := state k) rfl p (available.symm.trans actual).cons_inv
      rw [← next] at eq
      obtain ⟨u, residual, moved⟩ := budget_transport eq path
      exact ⟨k + 1, u, by omega, residual, fun i => Nat.le_of_eq (congrFun moved.2 i)⟩
    · let r := rest.erase q
      have qMem : q ∈ rest :=
        (List.mem_cons.mp (available.mem_iff.mp (actual.mem_iff.mpr (by simp)))).resolve_left same
      have pTail : rest.Perm (q :: r) := List.perm_cons_erase qMem
      have qTail : qs.Perm (p :: r) :=
        (actual.symm.trans (available.trans ((pTail.cons p).trans (List.Perm.swap _ _ _)))).cons_inv
      let s := state k
      let a := MarkFeedback.process C.model d s p (q :: r) 0
      let b' := MarkFeedback.process C.model d s q (p :: r) 0
      let ep := MarkFeedback.emitted C.model p (MarkFeedback.read C.model d s p 0)
      let eq := MarkFeedback.emitted C.model q (MarkFeedback.read C.model d s q 0)
      have eqA : Equivalent (MarkFeedback.process C.model d s p rest 0) a :=
        MarkFeedback.process_equivalent C.model d rfl p pTail
      have eqB : Equivalent (state (k + 1)) b' := by
        rw [next]
        exact MarkFeedback.process_equivalent C.model d rfl q qTail
      obtain ⟨endA, pathA, sameA⟩ := budget_transport eqA path
      have aReach : MarkFeedback.Path C.model d root a :=
        MarkFeedback.path_trans (reach k) (.cons (.select _ _ _ (available.trans (pTail.cons _))) (.nil _))
      have afterP : MarkFeedback.Move C.model d a (MarkFeedback.process C.model d a q (r ++ ep) 0) :=
        .select _ _ _ (List.Perm.refl _)
      obtain ⟨u, v, fromA, short, eqUV⟩ := commute_budget diamond aReach afterP pathA
      have joined := MarkFeedback.two_occurrences_commute C.model d s p q r
        (MarkFeedback.read_stable C.model d s (diamond _ (reach k))
          (available.trans (pTail.cons p)) (Ne.symm same))
        (MarkFeedback.read_stable C.model d s (diamond _ (reach k))
          (actual.trans (qTail.cons q)) same)
      have pStill : (state (k + 1)).pending.Perm (p :: (r ++ eq)) := eqB.1
      have eqNext := MarkFeedback.process_equivalent C.model d (s := b') (t := state (k + 1)) eqB.2.symm p
        (List.Perm.refl (r ++ eq))
      obtain ⟨continued, residual, eqU⟩ := budget_transport
        ⟨joined.1.trans eqNext.1, joined.2.trans eqNext.2⟩ fromA
      obtain ⟨l, out, time, finish, counts⟩ :=
        ih (j - (k + 1)) (by omega) (k := k + 1) (by omega) pStill residual rfl
      refine ⟨l, out, by omega, finish, fun i => ?_⟩
      have monotone : endA.writes i ≤ v.writes i := by
        rcases short with rfl | mv
        · exact Nat.le_refl _
        · exact MarkFeedback.move_writes_mono mv i
      rw [← congrFun sameA.2 i, ← congrFun eqUV.2 i, congrFun eqU.2 i] at monotone
      exact Nat.le_trans monotone (counts i)

theorem earliest_write_fair {C : Calendar N Date Input} {d le seed}
    (refl : ∀ t, le t t) (diamond : MarkFeedback.Admissible C.model d (MarkFeedback.initial N seed))
    (state : Nat → Config (3 * N) (Occurrence Date Input)) (starts : state 0 = MarkFeedback.initial N seed)
    (steps : ∀ k, EarliestStep C d le (state k) (state (k + 1))) (clears : ClearsDates le state) :
    MarkFeedback.WriteFair C.model d state := by
  have reach (k : Nat) : MarkFeedback.Path C.model d (MarkFeedback.initial N seed) (state k) := by
    induction k with
    | zero => rw [starts]; exact .nil _
    | succ k ih => exact MarkFeedback.path_trans ih (earliest_step_path (steps k))
  have dominate (n : Nat) (k : Nat) (t : Config (3 * N) (Occurrence Date Input))
      (path : BudgetPath C.model d n (state k) t) :
      ∃ j, k ≤ j ∧ ∀ i, t.writes i ≤ (state j).writes i := by
    induction n generalizing k t with
    | zero => cases path; exact ⟨k, Nat.le_refl _, fun _ => Nat.le_refl _⟩
    | succ n ih =>
      cases path with
      | nil => exact ⟨k, Nat.le_refl _, fun _ => Nat.le_refl _⟩
      | cons first tail =>
        cases first with
        | select p rest available =>
          obtain ⟨j, late, clear⟩ := clears k p (available.mem_iff.mpr (by simp))
          have gone : p ∉ (state j).pending := fun mem => clear p mem (refl _)
          obtain ⟨l, u, later, residual, counts⟩ :=
            catch_by_cut diamond state reach steps p gone late available tail
          obtain ⟨finish, time, bounds⟩ := ih l u residual
          exact ⟨finish, Nat.le_trans later time, fun i => Nat.le_trans (counts i) (bounds i)⟩
  intro k t path
  obtain ⟨n, sized⟩ := budget_of_path path
  exact dominate n k t sized


/-- Local finiteness of service is sufficient: only finitely many steps
can select an occurrence at or below any fixed date. If such work is
pending, earliest-date service necessarily spends one of those steps. -/
theorem clears_of_locally_finite_service {C : Calendar N Date Input} {d le}
    (trans : ∀ {a b c}, le a b → le b c → le a c)
    (state : Nat → Config (3 * N) (Occurrence Date Input))
    (steps : ∀ k, EarliestStep C d le (state k) (state (k + 1)))
    (locallyFinite : ∀ cutoff : Date, ∃ last : Nat, ∀ k, last ≤ k →
      ∀ p rest, (state k).pending.Perm (p :: rest) → Earliest le p rest →
        state (k + 1) = MarkFeedback.process C.model d (state k) p rest 0 → ¬ le p.due cutoff) :
    ClearsDates le state := by
  intro k p _
  obtain ⟨last, later⟩ := locallyFinite p.due
  let j := k + last
  refine ⟨j, Nat.le_add_right _ _, fun q mem due => ?_⟩
  rcases steps j with ⟨empty, _⟩ | ⟨selected, rest, available, earliest, result⟩
  · simp [empty] at mem
  · apply later j (by dsimp [j]; omega) selected rest available earliest result
    rcases List.mem_cons.mp (available.mem_iff.mp mem) with same | remain
    · exact same ▸ due
    · exact trans (earliest q remain) due


/-- After the last possible write, earliest-date service has the same
limit as FIFO if every date visible at a cut eventually clears. -/
theorem earliest_limit_unique (Q d : Nat) {C : Calendar N Date Input} {le seed}
    (refl : ∀ t, le t t) (reserve : MarkFeedback.Reserve Q C.model seed)
    (diamond : MarkFeedback.Admissible C.model d (MarkFeedback.initial N seed))
    (state : Nat → Config (3 * N) (Occurrence Date Input)) (starts : state 0 = MarkFeedback.initial N seed)
    (steps : ∀ k, EarliestStep C d le (state k) (state (k + 1))) (clears : ClearsDates le state) :
    ∃ counts, MarkFeedback.Stabilizes state counts ∧
      MarkFeedback.Stabilizes (MarkFeedback.fifo C.model d (fun _ => 0) (MarkFeedback.initial N seed)) counts := by
  apply MarkFeedback.fair_limit_unique Q d C.model seed reserve diamond state starts
  · intro k
    rcases steps k with ⟨_, eq⟩ | ⟨p, rest, available, _, next⟩
    · rw [eq]
      exact .nil _
    · rw [next]
      have room : RoutedCalendar.HasRoom (MarkFeedback.score C.model d (state k) p) 0 0 := by
        unfold RoutedCalendar.HasRoom
        omega
      exact .cons p rest available 0 0 0 ⟨Int.le_refl _, Int.le_refl _⟩ room (.nil _)
  · exact earliest_write_fair refl diamond state starts steps clears

namespace Starvation

def loop : Occurrence Nat Bool := ⟨0, false⟩
def writer : Occurrence Nat Bool := ⟨1, true⟩

/-- A FIRE reissues itself at its current date. An independent later
probe would write once if the scheduler ever got to it. -/
def calendar : Calendar 2 Nat Bool where
  cell p := if p then 1 else 0
  secondPort := fun _ => false
  phase := fun _ _ => .ready
  bias p _ := if p then -1 else 1
  recoveryWeight := fun _ _ => 0
  learn p _ := p
  mark := fun _ _ _ => false
  route p := if p.input then [] else [p]

def start : Config 6 (Occurrence Nat Bool) := MarkFeedback.initial 2 [loop, writer]
def steady : Config 6 (Occurrence Nat Bool) := MarkFeedback.initial 2 [writer, loop]
def execution : Nat → Config 6 (Occurrence Nat Bool)
  | 0 => start
  | _ + 1 => steady

theorem calendar_causal : ∀ p q, q ∈ calendar.route p → q.due ≥ p.due := by
  intro p q mem
  cases input : p.input
  · have same : q = p := by simpa [calendar, input] using mem
    exact same ▸ Nat.le_refl _
  · simp [calendar, input] at mem

theorem calendar_diamond : MarkFeedback.Admissible calendar.model 0 start := by
  intro s _
  right
  intro p _ q _ _ _ fire
  have zero : MarkFeedback.displacement calendar.model 0 p q fire = 0 := by
    simp [MarkFeedback.displacement, Calendar.model, calendar]
  rw [zero]
  unfold RoutedCalendar.HasRoom
  omega

def calendarReserve : MarkFeedback.Reserve 1 calendar.model [loop, writer] := by
  refine ⟨fun _ p => if p.input then 1 else 0, ?_, fun _ => by decide⟩
  intro p fire i
  cases input : p.input <;> cases fire <;>
    simp [MarkFeedback.emitted, MarkFeedback.footprint, Calendar.model, calendar,
      AutonomousFeedback.mass, input]
  split <;> decide

theorem earliest_starves : (∀ k, EarliestStep calendar 0 Nat.le (execution k) (execution (k + 1))) ∧
    ¬ MarkFeedback.WriteFair calendar.model 0 execution := by
  have first : MarkFeedback.process calendar.model 0 start loop [writer] 0 = steady := by rfl
  have again : MarkFeedback.process calendar.model 0 steady loop [writer] 0 = steady := by rfl
  constructor
  · intro k
    cases k with
    | zero => exact Or.inr ⟨loop, [writer], List.Perm.refl _, by simp [Earliest, loop, writer], first.symm⟩
    | succ k => exact Or.inr ⟨loop, [writer], List.Perm.swap _ _ _, by simp [Earliest, loop, writer], again.symm⟩
  · intro fair
    let out := MarkFeedback.process calendar.model 0 start writer [loop] 0
    have path : MarkFeedback.Path calendar.model 0 start out :=
      .cons (.select _ _ _ (List.Perm.swap _ _ _)) (.nil _)
    obtain ⟨j, _, counts⟩ := fair 0 out path
    have h := counts (MarkFeedback.gain calendar.model writer)
    cases j <;> exact (by decide : ¬ 1 ≤ 0) h

end Starvation

end NetworkStability.PhaseAdmission
