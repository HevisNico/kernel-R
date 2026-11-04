import KernelR.HybridWeakFlow
import KernelR.HybridContactTransversalityTransport

/-! A comparison envelope for crossing semantics. READY flows may touch one
without leaving READY; jumps retain the physical updates of the kernel.
Terminal saturation only demands jumps whose READY contact is transverse.
Thus a terminal tangency is admitted, rather than assumed impossible. -/
namespace KernelR.Hybrid
open MeasureTheory

inductive WeakMove {n} (θ : Fin n → Parameters) (route : Router n)
    (s u : Snapshot n) : Type
  | flow : WeakFlow θ s u → WeakMove θ route s u
  | jump : Jump route s u → WeakMove θ route s u

inductive WeakExecution {n} (θ : Fin n → Parameters) (route : Router n) :
    Snapshot n → Snapshot n → Type
  | nil (s) : WeakExecution θ route s s
  | cons {s u v} : WeakMove θ route s u → WeakExecution θ route u v →
      WeakExecution θ route s v

def WeakCompleteThrough {n θ route s u} (_e : @WeakExecution n θ route s u)
    (T : ℝ) : Prop :=
  u.time = T ∧ (∀ v (jump : Jump route u v), ¬ jump.ContactTransversal θ) ∧
    ∀ d ∈ u.pending, T < d.due

noncomputable def WeakFlow.ledger {n θ s u} (flow : @WeakFlow n θ s u) : Ledger n :=
  ⟨fun i p => ∫ t in s.time..u.time, errorAct θ s (flow.path t) i p,
   fun i p => ∫ t in s.time..u.time, markAct θ s (flow.path t) i p,
   fun i => ∫ t in s.time..u.time, ∑ p : Port, markAct θ s (flow.path t) i p,
   [], 0, 0⟩

noncomputable def WeakMove.ledger {n θ route s u} : @WeakMove n θ route s u → Ledger n
  | .flow f => f.ledger
  | .jump j => j.ledger

noncomputable def WeakExecution.ledger {n θ route s u} :
    @WeakExecution n θ route s u → Ledger n
  | .nil _ => Ledger.zero
  | .cons move rest => move.ledger.add rest.ledger

@[simp] def WeakExecution.moveCount {n θ route s u} :
    @WeakExecution n θ route s u → ℕ
  | .nil _ => 0
  | .cons _ rest => rest.moveCount + 1

noncomputable def WeakExecution.emissionTimes {n θ route s u}
    (execution : @WeakExecution n θ route s u) (i : Fin n) : List ℝ :=
  (execution.ledger.emissions.filter (fun event => event.1 = i)).map Prod.snd

def WeakExecution.append {n θ route s u v} (first : @WeakExecution n θ route s u)
    (rest : WeakExecution θ route u v) : WeakExecution θ route s v :=
  match first with
  | .nil _ => rest
  | .cons move tail => .cons move (tail.append rest)

theorem WeakExecution.time_monotone {n θ route s u}
    (execution : @WeakExecution n θ route s u) : s.time ≤ u.time := by
  induction execution with
  | nil => exact le_rfl
  | cons move rest ih =>
    apply le_trans _ ih
    cases move with
    | flow flow => exact flow.positive.le
    | jump jump => exact jump.time_unchanged.ge

def Execution.toWeak {n θ route s u} : @Execution n θ route s u →
    WeakExecution θ route s u
  | .nil s => .nil s
  | .cons (.flow f) rest => .cons (.flow f.toWeak) rest.toWeak
  | .cons (.jump j) rest => .cons (.jump j) rest.toWeak

@[simp] theorem Execution.toWeak_ledger {n θ route s u}
    (execution : @Execution n θ route s u) : execution.toWeak.ledger = execution.ledger := by
  induction execution with
  | nil => rfl
  | cons move rest ih =>
    cases move <;> simp only [Execution.toWeak, WeakExecution.ledger, Execution.ledger,
      WeakMove.ledger, Move.ledger, ih]
    rfl

@[simp] theorem Execution.toWeak_emissionTimes {n θ route s u}
    (execution : @Execution n θ route s u) :
    execution.toWeak.emissionTimes = execution.emissionTimes := by
  funext i
  simp only [WeakExecution.emissionTimes, Execution.emissionTimes, Execution.toWeak_ledger]

theorem CompleteThrough.toWeak {n θ route s u T} {execution : @Execution n θ route s u}
    (complete : CompleteThrough execution T) : WeakCompleteThrough execution.toWeak T :=
  ⟨complete.1, fun v jump => False.elim ((complete.2.1 v).false jump), complete.2.2⟩

end KernelR.Hybrid
