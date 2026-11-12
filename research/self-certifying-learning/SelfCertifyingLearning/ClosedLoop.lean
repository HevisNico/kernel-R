import SelfCertifyingLearning.Repair
import SelfCertifyingLearning.Budget
import SelfCertifyingLearning.Controller

/-! Executable conservative fallback. A fixed ceiling covers the complete
execution, including repair time. Estimates are propagated lower bounds;
this is not a learned sensor or a transistor realization. -/
namespace SelfCertifyingLearning.ClosedLoop
open Repair

inductive Action where
  | wait (ticks : Nat)
  | write
  | refuse
  deriving DecidableEq, Repr

/-- Wait while preserving the repair buffer; otherwise repair. Invalid
configurations and unbuffered starts are explicitly refused. -/
def choose (c : Config) (lower : Nat) : Action :=
  if c.Valid ∧ c.Ready lower then
    match Scheduler.plan lower c.guard c.bound c.maxWait with
    | some delay => .wait delay
    | none => .write
  else .refuse

def duration (c : Config) : Action → Nat
  | .wait ticks => ticks
  | .write => c.latency
  | .refuse => 0

def next (c : Config) (lower : Nat) : Action → Nat
  | .wait ticks => lower - c.bound * ticks
  | .write => pulse c lower
  | .refuse => lower

def deficit (c : Config) (lower : Nat) : Nat := c.target - lower

theorem choose_spec {c : Config} (valid : c.Valid) {lower : Nat} (ready : c.Ready lower) :
    match choose c lower with
    | .wait delay => 0 < delay ∧ delay ≤ c.maxWait ∧ c.bound * delay + c.guard ≤ lower
    | .write => lower < c.target
    | .refuse => False := by
  unfold choose
  simp only [ite_eq_left (And.intro valid ready)]
  cases selected : Scheduler.plan lower c.guard c.bound c.maxWait with
  | some delay =>
    have spec := Scheduler.plan_spec selected
    exact ⟨spec.1, spec.2.1, spec.2.2.1⟩
  | none =>
    by_cases below : lower < c.target
    · exact below
    · obtain ⟨delay, accepted⟩ := Scheduler.plan_exists (initial := lower)
        (reserve := c.guard) (bound := c.bound) (cap := c.maxWait) (delay := 1)
        (by decide) valid.2.1 (by simp only [Nat.mul_one]; unfold Config.target at below; omega)
      rw [selected] at accepted
      contradiction

theorem next_ready {c : Config} (valid : c.Valid) {lower : Nat} (ready : c.Ready lower) :
    c.Ready (next c lower (choose c lower)) := by
  have spec := choose_spec valid ready
  cases chosen : choose c lower with
  | wait delay =>
    rw [chosen] at spec
    unfold Config.Ready at *
    simp only [next]
    omega
  | write => exact pulse_ready valid ready
  | refuse => rw [chosen] at spec; contradiction

theorem action_progress {c : Config} (valid : c.Valid) {lower : Nat} (ready : c.Ready lower) :
    0 < duration c (choose c lower) := by
  have spec := choose_spec valid ready
  cases chosen : choose c lower with
  | wait delay => rw [chosen] at spec; exact spec.1
  | write => exact valid.1
  | refuse => rw [chosen] at spec; contradiction

theorem write_decreases {c : Config} (valid : c.Valid) {lower : Nat}
    (below : lower < c.target) : deficit c (pulse c lower) + 1 ≤ deficit c lower := by
  have gain := gain_positive valid
  have capacity := valid.2.2.2
  unfold deficit pulse
  omega

theorem wait_increases (c : Config) (lower delay : Nat) :
    deficit c (lower - c.bound * delay) ≤ deficit c lower + c.bound * delay := by
  unfold deficit
  omega

def trace (c : Config) : Nat → Nat → List Action
  | 0, _ => []
  | n + 1, lower =>
    let action := choose c lower
    action :: trace c n (next c lower action)

def final (c : Config) : Nat → Nat → Nat
  | 0, lower => lower
  | n + 1, lower => final c n (next c lower (choose c lower))

def clock (c : Config) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, lower => duration c (choose c lower) + clock c n (next c lower (choose c lower))

def writes : List Action → Nat
  | [] => 0
  | .write :: rest => 1 + writes rest
  | _ :: rest => writes rest

def waits : List Action → Nat
  | [] => 0
  | .wait _ :: rest => 1 + waits rest
  | _ :: rest => waits rest

def waitTime : List Action → Nat
  | [] => 0
  | .wait ticks :: rest => ticks + waitTime rest
  | _ :: rest => waitTime rest

def ledger (c : Config) : List Action → List Event
  | [] => []
  | .write :: rest => .correction :: ledger c rest
  | .wait ticks :: rest => .disturbance (c.bound * ticks) :: ledger c rest
  | .refuse :: rest => .idle :: ledger c rest

theorem ledger_counts (c : Config) (actions : List Action) :
    corrections (ledger c actions) = writes actions ∧
    injected (ledger c actions) = c.bound * waitTime actions := by
  induction actions with
  | nil => simp [ledger, writes, waitTime, corrections, injected]
  | cons action rest ih =>
    cases action <;> simp [ledger, corrections, injected, writes, waitTime, ih, Nat.mul_add]

/-- Every controller transition realizes the original potential ledger.
Repair-time loss is paid inside the strict net-gain condition; wait-time
loss is injected explicitly. The last saturating pulse still removes at
least one deficit tick, hence the conservative unit charge per write. -/
theorem ledger_run {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) :
    Run 1 (deficit c lower) (ledger c (trace c n lower)) (deficit c (final c n lower)) := by
  induction n generalizing lower with
  | zero => exact .nil _
  | succ n ih =>
    have spec := choose_spec valid ready
    have following := next_ready valid ready
    have tail := ih following
    cases chosen : choose c lower with
    | wait delay =>
      simp only [trace, final, chosen, ledger, next] at *
      exact .disturbance (wait_increases c lower delay) tail
    | write =>
      rw [chosen] at spec
      simp only [trace, final, chosen, ledger, next] at *
      exact .correction (write_decreases valid spec) tail
    | refuse => rw [chosen] at spec; contradiction

theorem write_bound {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) :
    writes (trace c n lower) ≤ deficit c lower + c.bound * waitTime (trace c n lower) := by
  have bound := (ledger_run valid n ready).correction_bound
  have counts := ledger_counts c (trace c n lower)
  rw [counts.1, counts.2] at bound
  simpa using bound

theorem trace_counts {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) : writes (trace c n lower) + waits (trace c n lower) = n := by
  induction n generalizing lower with
  | zero => rfl
  | succ n ih =>
    have tail := ih (next_ready valid ready)
    have spec := choose_spec valid ready
    cases chosen : choose c lower with
    | wait delay => simp only [trace, chosen, writes, waits] at *; omega
    | write => simp only [trace, chosen, writes, waits] at *; omega
    | refuse => rw [chosen] at spec; contradiction

theorem no_wait_no_time (actions : List Action) (none : waits actions = 0) : waitTime actions = 0 := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    cases action <;> simp only [waits, waitTime] at * <;> omega

/-- At least one positive wait occurs within deficit + 1 decisions. The
policy cannot stay in a repair loop forever under the stated capacity. -/
theorem returns_to_wait {c : Config} (valid : c.Valid) {lower : Nat} (ready : c.Ready lower) :
    0 < waits (trace c (deficit c lower + 1) lower) := by
  have count := trace_counts valid (deficit c lower + 1) ready
  have bound := write_bound valid (deficit c lower + 1) ready
  by_cases positive : 0 < waits (trace c (deficit c lower + 1) lower)
  · exact positive
  have zero : waits (trace c (deficit c lower + 1) lower) = 0 := by omega
  have noTime := no_wait_no_time _ zero
  rw [noTime] at bound
  simp only [Nat.mul_zero, Nat.add_zero] at bound
  omega

theorem clock_accounting (c : Config) (n lower : Nat) :
    clock c n lower = waitTime (trace c n lower) + c.latency * writes (trace c n lower) := by
  induction n generalizing lower with
  | zero => simp [clock, trace, writes, waitTime]
  | succ n ih =>
    simp only [clock, trace]
    rw [ih]
    cases choose c lower <;> simp [duration, waitTime, writes, Nat.mul_add] <;> omega

theorem time_progress {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) : n ≤ clock c n lower := by
  induction n generalizing lower with
  | zero => simp [clock]
  | succ n ih =>
    have tail := ih (next_ready valid ready)
    have positive := action_progress valid ready
    simp only [clock]
    omega

/-- This computable horizon can be used when obtaining the envelope for a
finite fallback epoch. It includes both waiting and writing time. -/
theorem clock_upper {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) : clock c n lower ≤ n * max c.maxWait c.latency := by
  induction n generalizing lower with
  | zero => simp [clock]
  | succ n ih =>
    have tail := ih (next_ready valid ready)
    have spec := choose_spec valid ready
    have perAction : duration c (choose c lower) ≤ max c.maxWait c.latency := by
      cases chosen : choose c lower with
      | wait delay => rw [chosen] at spec; simp only [duration]; omega
      | write => simp only [duration]; omega
      | refuse => rw [chosen] at spec; contradiction
    simp only [clock, Nat.succ_mul]
    omega

/-- A plant must satisfy these transition laws, not a pre-assumed safety
predicate. Time is relative to the start of the currently chosen action. -/
def Dynamics (c : Config) (state : Nat → Int) (action : Action) : Prop :=
  (∀ k, k < duration c action → state k - (c.bound : Int) ≤ state (k + 1)) ∧
  (action = .write →
    min (c.capacity : Int) (state 0 - (c.loss : Int) + (c.dose : Int)) ≤ state c.latency)

theorem action_safe {c : Config} (valid : c.Valid) {lower : Nat} (ready : c.Ready lower)
    (state : Nat → Int) (observed : (lower : Int) ≤ state 0)
    (dynamics : Dynamics c state (choose c lower)) :
    SafeUntil state c.service (duration c (choose c lower)) ∧
    (next c lower (choose c lower) : Int) ≤ state (duration c (choose c lower)) := by
  have spec := choose_spec valid ready
  cases chosen : choose c lower with
  | wait delay =>
    rw [chosen] at spec dynamics
    simp only [duration, next]
    have steps := dynamics.1
    have enclosure := Scheduler.enclosure_from_steps state c.bound delay steps
    constructor
    · apply constant_rate_deadline state lower c.service c.bound delay
      · intro k hk; have := enclosure k hk; omega
      · have := spec.2.2
        unfold Config.guard at this
        omega
    · have endBound := enclosure delay (by omega)
      have paid := spec.2.2
      omega
  | write =>
    rw [chosen] at dynamics
    exact ⟨pulse_interior_safe c ready state observed dynamics.1,
      pulse_endpoint valid (state 0) (state c.latency) observed (dynamics.2 rfl)⟩
  | refuse => rw [chosen] at spec; contradiction

/-- The observation-driven supervisor can hand off to this repair loop if
it schedules against the repair buffer rather than the bare service floor.
The next phase still needs its own valid full-duration loss envelope. -/
theorem guarded_visit_handoff {c : Config} (valid : c.Valid)
    (g slew : Nat) (anchor : Renewal.Interval) (reading : Controller.Reading)
    (truth : Nat) (rate : Nat → Nat) (state : Nat → Int)
    (rateObserved : reading.rate.Contains truth)
    (reserveObserved : (reading.lowerReserve : Int) ≤ state 0)
    (growth : ∀ k, k ≤ c.maxWait → rate k ≤ truth + slew * k)
    (dynamics : ∀ k, k < c.maxWait → state k - (rate (k + 1) : Int) ≤ state (k + 1))
    {delay : Nat}
    (accepted : (Controller.visit g c.guard slew c.maxWait anchor reading).delay = some delay) :
    SafeUntil state c.service delay ∧ (c.guard : Int) ≤ state delay ∧ c.Ready c.guard := by
  have buffered := Controller.visit_safe g c.guard slew c.maxWait anchor reading truth rate state
    rateObserved reserveObserved growth dynamics accepted
  refine ⟨?_, buffered delay (Nat.le_refl _), ?_⟩
  · intro k hk
    have := buffered k hk
    unfold Config.guard at this
    omega
  · have capacity := valid.2.2.2
    unfold Config.Ready Config.target at *
    omega

/-- Realization of a generated trace on one physical-time trajectory. The
same ceiling must cover every segment, including all delayed writes. -/
def Realizes (c : Config) : Nat → Nat → (Nat → Int) → Prop
  | 0, _, _ => True
  | n + 1, lower, state =>
    let action := choose c lower
    Dynamics c state action ∧
      Realizes c n (next c lower action) (fun t => state (duration c action + t))

/-- Safety and the conservative endpoint invariant compose over every
finite execution, at all discrete times including repair interiors. -/
theorem execution_safe {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) (state : Nat → Int) (observed : (lower : Int) ≤ state 0)
    (realizes : Realizes c n lower state) :
    SafeUntil state c.service (clock c n lower) ∧
    (final c n lower : Int) ≤ state (clock c n lower) := by
  induction n generalizing lower state with
  | zero =>
    constructor
    · intro k hk
      have := ready.1
      unfold Config.guard at this
      simp only [clock] at hk
      have : k = 0 := by omega
      subst k
      omega
    · exact observed
  | succ n ih =>
    have segment := action_safe valid ready state observed realizes.1
    have tail := ih (next_ready valid ready)
      (fun t => state (duration c (choose c lower) + t)) (by simpa using segment.2) realizes.2
    constructor
    · intro k hk
      by_cases early : k ≤ duration c (choose c lower)
      · exact segment.1 k early
      · have later := tail.1 (k - duration c (choose c lower)) (by simp only [clock] at hk; omega)
        have offset : duration c (choose c lower) + (k - duration c (choose c lower)) = k := by omega
        simpa only [offset] using later
    · exact tail.2

end SelfCertifyingLearning.ClosedLoop
