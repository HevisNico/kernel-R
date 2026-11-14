import PerpetualFeedback

namespace NetworkStability.AutonomousFeedback.ScheduleCounterexample

inductive Probe
  | trigger
  | warm
  | read
  deriving DecidableEq

/-- Trigger FIRE introduces two pending probes at the other cell. One dose of size two is enough to make the warm probe FIRE. The routed read
has the higher threshold and stays silent after just one dose. -/
def model : Model 2 Probe where
  cell p := match p with
    | .trigger => 0
    | _ => 1
  bias p := match p with
    | .trigger => 3
    | .warm => -1
    | .read => -4
  drive p := match p with
    | .read => 1
    | _ => 0
  route p := match p with
    | .trigger => [.warm, .read]
    | _ => []

/-- An admissible step selects an existing occurrence by a list split.
The other pending occurrences stay in relative order. The guarded update
and appended FIRE routes are exactly the FIFO update after selecting it. -/
inductive Select {N : Nat} {P : Type} (M : Model N P) (d : Nat) (e : Int) :
    State N P → State N P → Prop where
  | process (s : State N P) (before : List P) (p : P) (after : List P)
      (available : s.pending = before ++ p :: after) :
      Select M d e s (step M d e { s with pending := p :: (before ++ after) })

inductive Trace {N : Nat} {P : Type} (M : Model N P) (d : Nat) (e : Int) :
    State N P → State N P → Prop where
  | nil (s) : Trace M d e s s
  | cons {s t u} : Select M d e s t → Trace M d e t u → Trace M d e s u

def seed : State 2 Probe := start 2 [.trigger]

/-- The two orders diverge even for a router with a strict probe rank
and a uniform reserve covering both visits to cell 1. -/
def budget : Certificate 2 2 1 model [.trigger] where
  weight p := match p with | .trigger => 3 | _ => 1
  reserve i p := match p with
    | .trigger => if i = 0 then 1 else 2
    | _ => if i = 1 then 1 else 0
  eta_pos := by decide
  scalar := by intro p; cases p <;> decide
  local_route := by
    intro p i
    cases p <;> rcases i with ⟨i, hi⟩ <;> (have h : i = 0 ∨ i = 1 := by omega) <;>
      rcases h with rfl | rfl <;> decide +revert
  local_write := by intro p; cases p <;> decide
  seed_weight := by decide
  seed_reserve := by
    intro i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl <;> decide +revert

def ready : State 2 Probe := step model 2 0 seed

def reversed : State 2 Probe := { ready with pending := [.read, .warm] }

def warmFirst : State 2 Probe := run model 2 (fun _ => 0) 2 ready

def readFirst : State 2 Probe := run model 2 (fun _ => 0) 2 reversed

private theorem initial_step : Select model 2 0 seed ready :=
  Select.process seed [] .trigger [] rfl

private theorem warm_path : Trace model 2 0 seed warmFirst := by
  refine .cons initial_step (.cons (Select.process ready [] .warm [.read] rfl) ?_)
  let s := step model 2 0 ready
  exact .cons (Select.process s [] .read [] rfl) (.nil _)

private theorem read_path : Trace model 2 0 seed readFirst := by
  refine .cons initial_step (.cons (Select.process ready [.warm] .read [] rfl) ?_)
  let s := step model 2 0 reversed
  exact .cons (Select.process s [] .warm [] rfl) (.nil _)

/-- The same seed and router admit two finite, queue-empty executions
at zero error. A real fixed-dose memory differs at cell 1. -/
theorem different_terminal_memory :
    Trace model 2 0 seed warmFirst ∧ Trace model 2 0 seed readFirst ∧
    warmFirst.pending = [] ∧ readFirst.pending = [] ∧
    stored 2 (fun _ => 1) warmFirst 1 = 5 ∧
    stored 2 (fun _ => 1) readFirst 1 = 3 ∧
    stored 2 (fun _ => 1) warmFirst 1 ≠ stored 2 (fun _ => 1) readFirst 1 := by
  exact ⟨warm_path, read_path, by decide, by decide, by decide, by decide, by decide⟩

/-- The two orders even have nonzero per-probe error margins, evaluated
on each of their own nominal trajectories. -/
theorem both_orders_have_margins :
    NominalMargins model 2 (fun _ => -1) (fun _ => 0) 3 seed ∧
    NominalMargins model 2 (fun _ => -1) (fun _ => 0) 2 reversed := by
  constructor <;> simp [NominalMargins, ready, reversed, seed, start, step,
    fires, score, model, RoutedCalendar.HasRoom]

end NetworkStability.AutonomousFeedback.ScheduleCounterexample
