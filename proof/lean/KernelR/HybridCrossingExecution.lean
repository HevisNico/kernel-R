import KernelR.HybridCellOrbitExistence
import KernelR.HybridWeakExecution

/-! Crossing semantics uses the actual recorded left history and a genuine
incoming-mode ODE continuation on the right. Weak flows allow tangential
contacts; FIRE and MARK require actual crossings rather than threshold equality. -/
namespace KernelR.Hybrid
open Set

/-- Only the two coordinates with upper READY guards are crossing sections. -/
def ReadyCoordinate {n} (s : Snapshot n) (i : Fin n) : Coord → Prop
  | .q => s.main i = .ready
  | .m p => s.aux i p = .ready
  | _ => False

/-- A positive flow in the actual history approaches the final date strictly
below one. Every following move has the same date, by time monotonicity. -/
def WeakFlow.LeftApproach {n θ s u} (flow : @WeakFlow n θ s u)
    (final : Snapshot n) (i : Fin n) (c : Coord) : Prop :=
  u.time = final.time ∧ ∃ cut : ℝ, s.time ≤ cut ∧ cut < u.time ∧
    ∀ t ∈ Ioo cut u.time, flow.path t i c < 1

def WeakExecution.LeftBelow {n θ route s u} : @WeakExecution n θ route s u → Fin n → Coord → Prop
  | .nil _, _, _ => False
  | .cons (.flow flow) rest, i, c =>
      flow.LeftApproach u i c ∨ rest.LeftBelow i c
  | .cons (.jump _) rest, i, c => rest.LeftBelow i c

def Jump.CrossingLeft {n θ route born s u} (past : @WeakExecution n θ route born s) :
    @Jump n route s u → Prop
  | .fire _ i _ _ => past.LeftBelow i .q
  | .mark _ i p _ _ => past.LeftBelow i (.m p)
  | _ => True

/-- The prefix argument is actual executed history, never an independently
chosen scalar path. -/
def WeakExecution.CrossingFrom {n θ route born s u}
    (execution : @WeakExecution n θ route s u)
    (past : WeakExecution θ route born s) : Prop :=
  match execution with
  | .nil _ => True
  | .cons (.flow flow) rest =>
      rest.CrossingFrom (past.append (.cons (.flow flow) (.nil _)))
  | .cons (.jump jump) rest =>
      jump.CrossingLeft past ∧ jump.CrossingRight θ ∧
        rest.CrossingFrom (past.append (.cons (.jump jump) (.nil _)))

@[simp] theorem WeakExecution.append_nil {n θ route s u}
    (execution : @WeakExecution n θ route s u) : execution.append (.nil u) = execution := by
  induction execution with
  | nil => rfl
  | cons move tail ih => simp only [WeakExecution.append, ih]

theorem WeakExecution.append_assoc {n θ route s a b u}
    (first : @WeakExecution n θ route s a) (middle : WeakExecution θ route a b)
    (last : WeakExecution θ route b u) :
    (first.append middle).append last = first.append (middle.append last) := by
  induction first with
  | nil => rfl
  | cons move tail ih => simp only [WeakExecution.append, ih]

/-- Crossing certificates concatenate with the exact accumulated history. -/
theorem WeakExecution.crossingFrom_append {n θ route born s v u}
    (first : @WeakExecution n θ route s v) (rest : WeakExecution θ route v u)
    (past : WeakExecution θ route born s) :
    (first.append rest).CrossingFrom past ↔
      first.CrossingFrom past ∧ rest.CrossingFrom (past.append first) := by
  induction first generalizing born with
  | nil => simp [WeakExecution.append, WeakExecution.CrossingFrom]
  | cons move tail ih =>
    cases move <;> simp only [WeakExecution.append, WeakExecution.CrossingFrom, ih,
      WeakExecution.append_assoc, and_assoc]

structure CrossingExecution {n} (θ : Fin n → Parameters) (route : Router n)
    (s u : Snapshot n) where
  execution : WeakExecution θ route s u
  crossings : execution.CrossingFrom (.nil s)

/-- Exact historical terminal saturation: no jump satisfies both its actual
left-history guard and its incoming-mode right crossing. Protected-mode and raw
jumps have trivial crossing guards and remain urgent. -/
def CrossingCompleteThrough {n θ route s u} (execution : @CrossingExecution n θ route s u)
    (T : ℝ) : Prop :=
  u.time = T ∧ (∀ v (jump : Jump route u v),
    ¬ (jump.CrossingLeft execution.execution ∧ jump.CrossingRight θ)) ∧
    ∀ d ∈ u.pending, T < d.due

theorem Jump.readyCoordinate_of_target_one {n route s u} (jump : @Jump n route s u)
    (i : Fin n) (c : Coord) (ready : ReadyCoordinate u i c) (threshold : u.x i c = 1) :
    ReadyCoordinate s i c := by
  have original : s.x i c = 1 := by simpa only [jump.physical_continuous] using threshold
  cases c <;> cases jump <;>
    simp_all [ReadyCoordinate, setMain, setAux, setRaw, Function.update_apply]
  case q.fire k mode guard =>
    by_cases equal : i = k <;> simp_all
  case q.fastEnd k mode guard =>
    by_cases equal : i = k <;> simp_all
  case q.reopen k mode guard =>
    by_cases equal : i = k <;> simp_all
  case m.mark p k q mode guard =>
    by_cases equal : i = k
    · subst i
      by_cases port : p = q <;> simp_all
    · simp_all
  case m.silent p k q mode guard =>
    by_cases equal : i = k
    · subst i
      by_cases port : p = q <;> simp_all
    · simp_all
  case m.error p k q mode guard =>
    by_cases equal : i = k
    · subst i
      by_cases port : p = q <;> simp_all
    · simp_all
  case m.auxReady p k q mode guard =>
    by_cases equal : i = k
    · subst i
      by_cases port : p = q <;> simp_all
    · simp_all

theorem Execution.ready_threshold_history {n θ route s u} (execution : @Execution n θ route s u)
    (i : Fin n) (c : Coord) (ready : ReadyCoordinate u i c) (threshold : u.x i c = 1) :
    (s.time = u.time ∧ ReadyCoordinate s i c ∧ s.x i c = 1) ∨
      execution.toWeak.LeftBelow i c := by
  induction execution with
  | nil => exact Or.inl ⟨rfl, ready, threshold⟩
  | @cons s v u move rest ih =>
    rcases ih ready threshold with reached | history
    · cases move with
      | flow flow =>
        apply Or.inr
        apply Or.inl
        refine ⟨reached.1, s.time, le_rfl, flow.positive, ?_⟩
        intro t ht
        have initialReady : ReadyCoordinate s i c := by
          cases c <;> simpa only [ReadyCoordinate, flow.main_fixed, flow.aux_fixed] using reached.2.1
        have guards := flow.guards t ⟨ht.1.le, ht.2⟩
        change flow.path t i c < 1
        cases c with
        | q =>
          change s.main i = .ready at initialReady
          simpa only [ReadyCoordinate] using (show flow.path t i .q < 1 by simpa only [initialReady] using guards.1 i)
        | m p =>
          change s.aux i p = .ready at initialReady
          simpa only [ReadyCoordinate] using (show flow.path t i (.m p) < 1 by simpa only [initialReady] using guards.2 i p)
        | z p => exact False.elim initialReady
        | b => exact False.elim initialReady
        | energy => exact False.elim initialReady
      | jump jump =>
        exact Or.inl ⟨jump.time_unchanged.symm.trans reached.1,
          jump.readyCoordinate_of_target_one i c reached.2.1 reached.2.2,
          by simpa only [jump.physical_continuous] using reached.2.2⟩
    · apply Or.inr
      cases move with
      | flow flow => exact Or.inr history
      | jump jump => exact history

def InitiallyBelowReady {n} (s : Snapshot n) : Prop :=
  ∀ i c, ReadyCoordinate s i c → s.x i c < 1

theorem Execution.crossingLeft_of_initiallyBelow {n θ route born s u}
    (past : @Execution n θ route born s) (initial : InitiallyBelowReady born)
    (jump : Jump route s u) : jump.CrossingLeft past.toWeak := by
  have history (i : Fin n) (c : Coord) (ready : ReadyCoordinate s i c) (threshold : s.x i c = 1) :
      past.toWeak.LeftBelow i c := by
    rcases past.ready_threshold_history i c ready threshold with reached | actual
    · have below := initial i c reached.2.1
      rw [reached.2.2] at below
      exact False.elim ((lt_irrefl (1 : ℝ)) below)
    · exact actual
  cases jump with
  | fire i mode threshold => exact history i .q mode threshold
  | mark i p mode threshold => exact history i (.m p) mode threshold
  | fastEnd | reopen | silent | error | auxReady | rawEnd | arrive => trivial

@[simp] theorem Execution.toWeak_append {n θ route s v u}
    (first : @Execution n θ route s v) (rest : Execution θ route v u) :
    (first.append rest).toWeak = first.toWeak.append rest.toWeak := by
  induction first with
  | nil => rfl
  | cons move tail ih => cases move <;> simp only [Execution.append, Execution.toWeak,
      WeakExecution.append, ih]

theorem BirthState.initiallyBelowReady {n s} (birth : @BirthState n s) :
    InitiallyBelowReady s := by
  intro i c ready
  rcases birth.2.2 i with ⟨main, charge, recovery, energy, auxiliary⟩
  cases c with
  | q => linarith [charge.2]
  | m p =>
    rcases (auxiliary p).2 with rest | error
    · linarith [rest.2.2]
    · simp only [ReadyCoordinate, error.1, reduceCtorEq] at ready
  | z p => exact False.elim ready
  | b => exact False.elim ready
  | energy => exact False.elim ready

theorem Jump.crossingRight_of_physical_transversal {n θ route s u}
    (jump : @Jump n route s u) (physical : PhysicalInvariant θ s)
    (transversal : jump.ContactTransversal θ) : jump.CrossingRight θ := by
  cases jump with
  | fire i mode threshold =>
    exact ⟨physical.cell_orbit i,
      (physical.cell_orbit i).crossing_of_positive_field .q threshold transversal⟩
  | mark i p mode threshold =>
    exact ⟨physical.cell_orbit i,
      (physical.cell_orbit i).crossing_of_positive_field (.m p) threshold transversal⟩
  | fastEnd | reopen | silent | error | auxReady | rawEnd | arrive => trivial

theorem Execution.toWeak_crossingFrom {n θ ε route born s u}
    (execution : @Execution n θ route s u) (past : Execution θ route born s)
    (initial : InitiallyBelowReady born) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ born) (transversal : execution.ContactsTransversal) :
    execution.toWeak.CrossingFrom past.toWeak := by
  induction execution generalizing born with
  | nil => trivial
  | @cons s v u move rest ih =>
    cases move with
    | flow flow =>
      have tail := ih (past.append (.cons (.flow flow) (.nil _))) initial physical transversal
      simpa only [Execution.toWeak_append, Execution.toWeak, WeakExecution.CrossingFrom] using tail
    | jump jump =>
      refine ⟨past.crossingLeft_of_initiallyBelow initial jump,
        jump.crossingRight_of_physical_transversal (past.physical_invariant box physical) transversal.1, ?_⟩
      have tail := ih (past.append (.cons (.jump jump) (.nil _))) initial physical transversal.2
      simpa only [Execution.toWeak_append, Execution.toWeak] using tail

/-- A strict witness with certified transverse contacts realizes the crossing
semantics. All physical states and ODE germs are derived from its initial state. -/
def Execution.toCrossing {n θ ε route s u} (execution : @Execution n θ route s u)
    (initial : InitiallyBelowReady s) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (transversal : execution.ContactsTransversal) :
    CrossingExecution θ route s u :=
  ⟨execution.toWeak, execution.toWeak_crossingFrom (.nil _) initial box physical transversal⟩

def Execution.toCrossingFromBirth {n θ ε route s u} (execution : @Execution n θ route s u)
    (birth : BirthState s) (box : PhysicalBox θ ε) (transversal : execution.ContactsTransversal) :
    CrossingExecution θ route s u :=
  execution.toCrossing birth.initiallyBelowReady box (birth.physical_invariant box) transversal

theorem CompleteThrough.toCrossing {n θ ε route s u T}
    (execution : @Execution n θ route s u) (complete : CompleteThrough execution T)
    (initial : InitiallyBelowReady s) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (transversal : execution.ContactsTransversal) :
    CrossingCompleteThrough (execution.toCrossing initial box physical transversal) T :=
  ⟨complete.1, fun v jump => False.elim ((complete.2.1 v).false jump), complete.2.2⟩

/-- Once a protocol comparison has shown that the candidate's exact weak
moves are native moves, geometric saturation implies the weak comparison
terminal condition. No stronger saturation assumption is used. -/
theorem CrossingCompleteThrough.toWeak_of_native {n θ ε route s u T}
    (candidate : @CrossingExecution n θ route s u)
    (complete : CrossingCompleteThrough candidate T)
    (native : Execution θ route s u) (same : native.toWeak = candidate.execution)
    (initial : InitiallyBelowReady s) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) : WeakCompleteThrough candidate.execution T := by
  refine ⟨complete.1, ?_, complete.2.2⟩
  intro v jump transversal
  apply complete.2.1 v jump
  refine ⟨?_, jump.crossingRight_of_physical_transversal
    (native.physical_invariant box physical) transversal⟩
  rw [← same]
  exact native.crossingLeft_of_initiallyBelow initial jump

end KernelR.Hybrid
