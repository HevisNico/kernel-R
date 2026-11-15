import NativeAdmissions
import KernelR.HybridPrefixBeforeFlow
import KernelR.HybridStableMemory

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid MeasureTheory Set

private theorem admissions_append {N : Nat} {θ : Fin N → KernelR.Hybrid.Parameters}
    {route : Router N} {s t u : Snapshot N} (head : Execution θ route s t)
    (tail : Execution θ route t u) :
    NativeReciprocal.nativeAdmissions (head.append tail) =
      NativeReciprocal.nativeAdmissions head ++ NativeReciprocal.nativeAdmissions tail := by
  induction head with
  | nil => rfl
  | cons move rest ih =>
    simp only [Execution.append, NativeReciprocal.nativeAdmissions, ih, List.append_assoc]

private theorem split_mark {N : Nat} {θ : Fin N → KernelR.Hybrid.Parameters} {s u : Snapshot N}
    (f : Flow θ s u) {date : ℝ} (start : s.time < date) (finish : date < u.time)
    (i : Fin N) (port : Port) :
    (f.prefix start finish.le).ledger.mark i port + (f.suffix start.le finish).ledger.mark i port =
      f.ledger.mark i port := by
  let dose := fun t => markAct θ s (f.path t) i port
  have left : IntervalIntegrable dose volume s.time date := (f.mark_integrable i port).mono_set (by
    rw [uIcc_of_le start.le, uIcc_of_le f.positive.le]
    exact Icc_subset_Icc le_rfl finish.le)
  have right : IntervalIntegrable dose volume date u.time := (f.mark_integrable i port).mono_set (by
    rw [uIcc_of_le finish.le, uIcc_of_le f.positive.le]
    exact Icc_subset_Icc start.le le_rfl)
  change (∫ t in s.time..date, dose t) + (∫ t in date..u.time, dose t) = _
  exact intervalIntegral.integral_add_adjacent_intervals left right

/-- Insert an actual execution boundary. If the clock is at a jump, all
jumps at that clock are in the head. Flow splitting preserves actuation
as well as the ordered FIRE and delivery words. -/
theorem exact_execution_cut {N : Nat} {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) (date : ℝ)
    (start : s.time ≤ date) (finish : date < u.time) :
    ∃ (cut : Snapshot N) (head : Execution θ route s cut) (tail : Execution θ route cut u),
      CompleteThrough head date ∧
      NativeReciprocal.nativeAdmissions (head.append tail) = NativeReciprocal.nativeAdmissions run ∧
      (head.append tail).ledger.emissions = run.ledger.emissions ∧
      (∀ i q, (head.append tail).ledger.mark i q = run.ledger.mark i q) ∧
      (head.append tail).ContactsTransversal = run.ContactsTransversal := by
  induction run with
  | nil s => exact False.elim (not_lt_of_ge start finish)
  | @cons s v u move run ih =>
    have step (bound : v.time ≤ date) :
        ∃ (cut : Snapshot N) (head : Execution θ route s cut) (tail : Execution θ route cut u),
          CompleteThrough head date ∧
          NativeReciprocal.nativeAdmissions (head.append tail) =
            NativeReciprocal.nativeAdmissions (Execution.cons move run) ∧
          (head.append tail).ledger.emissions = (Execution.cons move run).ledger.emissions ∧
          (∀ i q, (head.append tail).ledger.mark i q = (Execution.cons move run).ledger.mark i q) ∧
          (head.append tail).ContactsTransversal = (Execution.cons move run).ContactsTransversal := by
      obtain ⟨cut, head, tail, hDate, arrivals, fires, mark, contacts⟩ := ih bound finish
      refine ⟨cut, .cons move head, tail, hDate, ?_, ?_, ?_, ?_⟩
      · simp only [Execution.append, NativeReciprocal.nativeAdmissions, arrivals]
      · simp only [Execution.append, Execution.ledger, Ledger.add] at fires ⊢
        rw [fires]
      · intro i q
        change move.ledger.mark i q + (head.append tail).ledger.mark i q =
          move.ledger.mark i q + run.ledger.mark i q
        rw [mark]
      · cases move with
        | flow _ => exact contacts
        | jump j =>
          change (j.ContactTransversal θ ∧ (head.append tail).ContactsTransversal) =
            (j.ContactTransversal θ ∧ run.ContactsTransversal)
          rw [contacts]
    cases move with
    | jump j => exact step (j.time_unchanged.trans_le start)
    | flow f =>
      by_cases ordered : v.time ≤ date
      · exact step ordered
      have inside := lt_of_not_ge ordered
      by_cases equal : s.time = date
      · have complete : CompleteThrough (.nil s : Execution θ route s s) date := by
          refine ⟨equal, ?_, fun d mem => equal ▸ f.initial_pending_strict d mem⟩
          intro target
          exact f.initial_before_guards.no_jump (fun i q o h => f.initial_raw_strict i q o h)
            f.initial_pending_strict target
        exact ⟨s, .nil s, .cons (.flow f) run, complete, rfl, rfl, fun _ _ => rfl, rfl⟩
      let head : Execution θ route s (f.at date) := .cons (.flow (f.prefix (lt_of_le_of_ne start equal) inside.le)) (.nil _)
      let tail : Execution θ route (f.at date) u := .cons (.flow (f.suffix start inside)) run
      refine ⟨f.at date, head, tail, ⟨rfl, f.interior_saturated ⟨start, inside⟩⟩, rfl, rfl, ?_, rfl⟩
      intro i q
      change (f.prefix (lt_of_le_of_ne start equal) inside.le).ledger.mark i q +
        ((f.suffix start inside).ledger.mark i q + run.ledger.mark i q) =
        f.ledger.mark i q + run.ledger.mark i q
      rw [← add_assoc, split_mark]

/-- An actual append boundary in this execution. -/
def HasExecutionCut {N : Nat} {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) (date : ℝ) : Prop :=
  ∃ (cut : Snapshot N) (head : Execution θ route s cut) (tail : Execution θ route cut u),
    CompleteThrough head date ∧ run = head.append tail

/-- A boundary strictly after a given prefix belongs to the remaining
execution. This turns a global clock boundary into a row-local slice. -/
theorem HasExecutionCut.after_prefix {N : Nat} {θ : Fin N → KernelR.Hybrid.Parameters}
    {route : Router N} {s v u : Snapshot N} {date : ℝ}
    (head : Execution θ route s v) (tail : Execution θ route v u)
    (later : v.time < date) (present : HasExecutionCut (head.append tail) date) :
    HasExecutionCut tail date := by
  induction head with
  | nil => exact present
  | @cons s w v step head ih =>
    obtain ⟨cut, before, after, clock, shape⟩ := present
    cases before with
    | nil => exact False.elim (not_lt_of_ge (clock.1 ▸ step.time_monotone.trans head.time_monotone) later)
    | @cons _ w' _ first rest =>
      change Execution.cons step (head.append tail) = Execution.cons first (rest.append after) at shape
      injection shape with _ sameState _ _ sameTail
      subst w'
      apply ih
      · exact later
      · exact ⟨cut, rest, after, clock, eq_of_heq sameTail⟩

theorem jump_admission_of_delivery {N : Nat} {route : Router N}
    {before admitted : Snapshot N} (jump : Jump route before admitted)
    (admission : NativeReciprocal.Admission N) (arrivals : jump.deliveries = [admission.token])
    (mode : before.main admission.token.cell = admission.mode) :
    NativeReciprocal.jumpAdmissions jump = [admission] := by
  cases jump with
  | arrive token =>
    have tokenEq : token = admission.token := (List.cons.inj arrivals).1
    cases admission with
    | mk expected expectedMode =>
      change token = expected at tokenEq
      subst expected
      change before.main token.cell = expectedMode at mode
      subst expectedMode
      rfl
  | _ => simp [Jump.deliveries] at arrivals

/-- The admission and its deadline cut are factors of the same native run. -/
theorem admission_through_cut {N : Nat} {θ : Fin N → KernelR.Hybrid.Parameters}
    {route : Router N} {s u : Snapshot N} (run : Execution θ route s u)
    (admission : NativeReciprocal.Admission N)
    (seen : admission ∈ NativeReciprocal.nativeAdmissions run) {date : ℝ}
    (later : admission.token.due < date) (present : HasExecutionCut run date) :
    ∃ (before admitted finished : Snapshot N) (head : Execution θ route s before)
      (jump : Jump route before admitted) (body : Execution θ route admitted finished)
      (tail : Execution θ route finished u),
      run = head.append (.cons (.jump jump) (body.append tail)) ∧
      NativeReciprocal.jumpAdmissions jump = [admission] ∧
      before.time = admission.token.due ∧ finished.time = date := by
  obtain ⟨before, admitted, head, jump, remaining, shape, arrivals, mode, clock⟩ :=
    NativeReciprocal.admission_cut run admission seen
  let intakeHead : Execution θ route s admitted := head.append (.cons (.jump jump) (.nil _))
  have prepended : intakeHead.append remaining = run := by
    simp only [intakeHead, Execution.append_assoc, Execution.append, shape]
  have laterClock : admitted.time < date := by rw [jump.time_unchanged, clock]; exact later
  obtain ⟨finished, body, tail, finish, split⟩ := HasExecutionCut.after_prefix intakeHead remaining laterClock
    (prepended.symm ▸ present)
  exact ⟨before, admitted, finished, head, jump, body, tail,
    by rw [shape, split], jump_admission_of_delivery jump admission arrivals mode, clock, finish.1⟩

/-- Insert a single finite schedule of cuts into one witness. Distinct
cells may need the same clock, so the schedule is only weakly ordered. -/
theorem exact_execution_cuts {N : Nat} {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) (dates : List ℝ)
    (ordered : dates.Pairwise (· ≤ ·)) (inside : ∀ date ∈ dates, s.time ≤ date ∧ date < u.time) :
    ∃ refined : Execution θ route s u,
      (∀ date ∈ dates, HasExecutionCut refined date) ∧
      NativeReciprocal.nativeAdmissions refined = NativeReciprocal.nativeAdmissions run ∧
      refined.ledger.emissions = run.ledger.emissions ∧
      (∀ i q, refined.ledger.mark i q = run.ledger.mark i q) ∧
      refined.ContactsTransversal = run.ContactsTransversal := by
  induction dates generalizing s with
  | nil => exact ⟨run, by simp, rfl, rfl, fun _ _ => rfl, rfl⟩
  | cons date dates ih =>
    have bound := inside date List.mem_cons_self
    obtain ⟨cut, head, tail, clock, admissions, fires, marks, contact⟩ :=
      exact_execution_cut run date bound.1 bound.2
    obtain ⟨refined, cuts, tailAdmissions, tailFires, tailMarks, tailContact⟩ := ih tail
      (List.pairwise_cons.mp ordered).2 (by
        intro t mem
        exact ⟨clock.1.trans_le ((List.pairwise_cons.mp ordered).1 t mem),
          (inside t (List.mem_cons_of_mem _ mem)).2⟩)
    refine ⟨head.append refined, ?_, ?_, ?_, ?_, ?_⟩
    · intro t mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact ⟨cut, head, refined, clock, rfl⟩
      · obtain ⟨v, front, rest, hDate, split⟩ := cuts t later
        exact ⟨v, head.append front, rest, hDate, by rw [split, Execution.append_assoc]⟩
    · rwa [admissions_append, tailAdmissions, ← admissions_append]
    · rwa [Execution.emissions_append, tailFires, ← Execution.emissions_append]
    · intro i q
      rw [Execution.mark_append, tailMarks, ← Execution.mark_append, marks]
    · rwa [Execution.contactsTransversal_append, tailContact, ← Execution.contactsTransversal_append]

end NetworkStability.NativeMultiToken
