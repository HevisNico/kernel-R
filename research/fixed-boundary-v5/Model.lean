import Std

/-! A fixed-boundary executable policy and its canonical physical execution.
The physical loss, sensor and delivered-dose laws are explicit premises.
No learned law, runtime authority or assumed safety predicate is used. -/
namespace FixedBoundaryV5

inductive Policy where
  | prudent
  | early
  deriving DecidableEq, Repr

inductive Action where
  | wait1
  | wait2
  | write
  | refuse
  deriving DecidableEq, Repr

def duration : Action → Nat
  | .wait1 => 1
  | .wait2 => 2
  | .write => 1
  | .refuse => 0

def Ready (lower : Int) : Prop := 250 ≤ lower ∧ lower ≤ 660
instance (lower : Int) : Decidable (Ready lower) := inferInstanceAs (Decidable (_ ∧ _))

def postDelivery (pre : Int) (delivered : Bool) : Int :=
  if delivered then min 660 (pre + 220) else pre

def freshLower (report : Int) (delivered : Bool) : Int :=
  if delivered then min 660 (report - 2 + 220) else report - 2

def freshUpper (report : Int) (delivered : Bool) : Int :=
  if delivered then min 660 (report + 2 + 220) else report + 2

def choose (policy : Policy) (lower upper : Int) : Action :=
  if Ready lower then
    if policy = .early ∧ upper + 220 ≤ 660 then .write
    else if policy = .early ∧ 550 ≤ lower then .wait2
    else if 400 ≤ lower then .wait1
    else .write
  else .refuse

def carry (lower : Int) : Action → Int
  | .wait1 => lower - 150
  | .wait2 => lower - 300
  | .write => min 660 (lower - 150 + 220)
  | .refuse => 0

structure Reply where
  action : Action
  lower : Int
  upper : Int
  nextCarry : Int
  deriving Repr

/-- This observation-only kernel is called by the runtime bridge. -/
def kernel (policy : Policy) (report rateReport : Int) (delivered : Bool)
    (previousCarry : Int) : Reply :=
  let lower := if rateReport - 1 > 150 then freshLower report delivered
    else max (freshLower report delivered) previousCarry
  let upper := freshUpper report delivered
  let action := if rateReport - 1 > 150 then .refuse else choose policy lower upper
  ⟨action, lower, upper, carry lower action⟩

def Certified (lower : Int) (action : Action) : Prop :=
  Ready lower ∧ match action with
    | .wait1 => 400 ≤ lower
    | .wait2 => 550 ≤ lower
    | .write => True
    | .refuse => False

theorem choose_certified (policy : Policy) (lower upper : Int) (ready : Ready lower) :
    Certified lower (choose policy lower upper) := by
  unfold choose
  rw [ite_eq_left ready]
  split
  · exact ⟨ready, trivial⟩
  · split
    · rename_i high
      exact ⟨ready, high.2⟩
    · split
      · rename_i middle
        exact ⟨ready, middle⟩
      · exact ⟨ready, trivial⟩

theorem maximum_wait_formula (lower : Int) (ready : Ready lower) :
    min 40 ((lower - 250) / 150) =
      if 550 ≤ lower then 2 else if 400 ≤ lower then 1 else 0 := by
  unfold Ready at ready
  by_cases high : 550 ≤ lower
  · simp [high]; omega
  · by_cases middle : 400 ≤ lower
    · simp [high, middle]; omega
    · simp [high, middle]; omega

theorem kernel_certified (policy : Policy) (report rateReport : Int) (delivered : Bool)
    (previousCarry : Int) (ready : Ready (max (freshLower report delivered) previousCarry))
    (rateWithin : rateReport - 1 ≤ 150) :
    Certified (kernel policy report rateReport delivered previousCarry).lower
      (kernel policy report rateReport delivered previousCarry).action := by
  simp only [kernel]
  simp only [ite_eq_right (by omega : ¬ rateReport - 1 > 150)]
  exact choose_certified policy _ _ ready

theorem fresh_bounds (pre error : Int) (delivered : Bool)
    (noise : -2 ≤ error ∧ error ≤ 2) :
    freshLower (pre + error) delivered ≤ postDelivery pre delivered ∧
    postDelivery pre delivered ≤ freshUpper (pre + error) delivered := by
  cases delivered <;> simp [freshLower, freshUpper, postDelivery] <;> omega

theorem fresh_width (pre error : Int) (delivered : Bool)
    (noise : -2 ≤ error ∧ error ≤ 2) :
    postDelivery pre delivered - 4 ≤ freshLower (pre + error) delivered := by
  cases delivered <;> simp [freshLower, postDelivery] <;> omega

theorem combine_sound (fresh carried actual : Int)
    (freshSound : fresh ≤ actual) (carriedSound : carried ≤ actual) :
    max fresh carried ≤ actual := by omega

theorem early_refill_not_saturated (actual upper loss : Int)
    (enclosed : actual ≤ upper) (nonnegative : 0 ≤ loss)
    (early : upper + 220 ≤ 660) : actual - loss + 220 ≤ 660 := by omega

theorem measured_violation_sound (actual report : Int)
    (noise : -1 ≤ report - actual ∧ report - actual ≤ 1)
    (violation : report - 1 > 150) : 150 < actual := by omega

theorem measured_violation_refuses (policy : Policy) (report rateReport : Int)
    (delivered : Bool) (previousCarry : Int) (violation : rateReport - 1 > 150) :
    (kernel policy report rateReport delivered previousCarry).action = .refuse ∧
    (kernel policy report rateReport delivered previousCarry).nextCarry = 0 := by
  simp [kernel, violation, carry]

theorem within_boundary_cannot_trigger_rate_refusal (actual error : Int)
    (rate : actual ≤ 150) (noise : error ≤ 1) : actual + error - 1 ≤ 150 := by omega

/-- The exact physical segment: a write arrives after its pre-delivery read.
There are at most two ticks because H=150 and capacity=660. -/
def endpointPre (actual loss1 loss2 : Int) : Action → Int
  | .wait2 => actual - loss1 - loss2
  | _ => actual - loss1

def endpointPost (actual loss1 loss2 : Int) (action : Action) : Int :=
  postDelivery (endpointPre actual loss1 loss2 action) (action == .write)

def samples (actual loss1 loss2 : Int) : Action → List (Int × Int)
  | .wait1 => [(actual - loss1, actual - loss1)]
  | .wait2 => [(actual - loss1, actual - loss1),
              (actual - loss1 - loss2, actual - loss1 - loss2)]
  | .write => [(actual - loss1, min 660 (actual - loss1 + 220))]
  | .refuse => []

def SafeSamples (xs : List (Int × Int)) : Prop :=
  ∀ point ∈ xs, 100 ≤ point.1 ∧ 100 ≤ point.2

theorem segment_certificate (lower actual loss1 loss2 : Int) (action : Action)
    (certified : Certified lower action) (observed : lower ≤ actual)
    (capacity : actual ≤ 660) (first : 0 ≤ loss1 ∧ loss1 ≤ 150)
    (second : 0 ≤ loss2 ∧ loss2 ≤ 150) :
    SafeSamples (samples actual loss1 loss2 action) ∧
    100 ≤ endpointPre actual loss1 loss2 action ∧
    Ready (carry lower action) ∧
    carry lower action ≤ endpointPost actual loss1 loss2 action ∧
    endpointPost actual loss1 loss2 action ≤ 660 ∧
    1 ≤ duration action ∧ duration action ≤ 2 := by
  cases action <;>
    simp_all [Certified, Ready, SafeSamples, samples, endpointPre, endpointPost,
      postDelivery, carry, duration] <;> omega

theorem samples_length (actual loss1 loss2 : Int) (action : Action) :
    (samples actual loss1 loss2 action).length = duration action := by
  cases action <;> rfl

structure World where
  loss : Nat → Int
  reserveError : Nat → Int
  rateError : Nat → Int

/-- These are plant and sensor laws, not conclusions about service. -/
def Physics (world : World) : Prop :=
  (∀ t, 0 ≤ world.loss t ∧ world.loss t ≤ 150) ∧
  (∀ t, -2 ≤ world.reserveError t ∧ world.reserveError t ≤ 2) ∧
  (∀ t, -1 ≤ world.rateError t ∧ world.rateError t ≤ 1)

structure State where
  now : Nat
  pre : Int
  delivered : Bool
  carried : Int
  deriving Repr

def State.post (s : State) : Int := postDelivery s.pre s.delivered

def reading (world : World) (policy : Policy) (s : State) : Reply :=
  kernel policy (s.pre + world.reserveError s.now)
    (world.loss s.now + world.rateError s.now) s.delivered s.carried

theorem reading_lower (world : World) (policy : Policy) (s : State)
    (physics : Physics world) :
    (reading world policy s).lower =
      max (freshLower (s.pre + world.reserveError s.now) s.delivered) s.carried := by
  have rate := (physics.1 s.now).2
  have error := (physics.2.2 s.now).2
  simp only [reading, kernel]
  rw [ite_eq_right (by omega)]


def Entry (world : World) (policy : Policy) (s : State) : Prop :=
  100 ≤ s.pre ∧ Ready (reading world policy s).lower ∧
  (reading world policy s).lower ≤ s.post ∧ s.post ≤ 660

def advance (world : World) (policy : Policy) (s : State) : State :=
  let reply := reading world policy s
  ⟨s.now + duration reply.action,
   endpointPre s.post (world.loss (s.now + 1)) (world.loss (s.now + 2)) reply.action,
   reply.action == .write, reply.nextCarry⟩

def emitted (world : World) (policy : Policy) (s : State) : List (Int × Int) :=
  samples s.post (world.loss (s.now + 1)) (world.loss (s.now + 2))
    (reading world policy s).action

theorem reading_carry (world : World) (policy : Policy) (s : State) :
    (reading world policy s).nextCarry =
      carry (reading world policy s).lower (reading world policy s).action := by
  rfl

theorem step_certified (world : World) (policy : Policy) (s : State)
    (physics : Physics world) (entry : Entry world policy s) :
    Certified (reading world policy s).lower (reading world policy s).action := by
  apply kernel_certified
  · simpa only [reading_lower world policy s physics] using entry.2.1
  · have rate := (physics.1 s.now).2
    have error := (physics.2.2 s.now).2
    omega

theorem step_preserves_entry (world : World) (policy : Policy) (s : State)
    (physics : Physics world) (entry : Entry world policy s) :
    Entry world policy (advance world policy s) := by
  have cert := step_certified world policy s physics entry
  have segment := segment_certificate (reading world policy s).lower s.post
    (world.loss (s.now + 1)) (world.loss (s.now + 2))
    (reading world policy s).action cert entry.2.2.1 entry.2.2.2
    (physics.1 _) (physics.1 _)
  have nextCarry : (advance world policy s).carried =
      carry (reading world policy s).lower (reading world policy s).action := by
    simp only [advance, reading_carry]
  have nextPost : (advance world policy s).post =
      endpointPost s.post (world.loss (s.now + 1)) (world.loss (s.now + 2))
        (reading world policy s).action := by rfl
  have fresh := fresh_bounds (advance world policy s).pre
    (world.reserveError (advance world policy s).now)
    (advance world policy s).delivered (physics.2.1 _)
  have freshSound : freshLower ((advance world policy s).pre +
      world.reserveError (advance world policy s).now) (advance world policy s).delivered ≤
      (advance world policy s).post := fresh.1
  rw [nextPost] at freshSound
  have carryReady := segment.2.2.1
  have carriedSound := segment.2.2.2.1
  have actualCapacity := segment.2.2.2.2.1
  unfold Entry
  refine ⟨segment.2.1, ?_, ?_, ?_⟩
  · rw [reading_lower world policy (advance world policy s) physics]
    unfold Ready at *
    rw [nextCarry]
    omega
  · rw [reading_lower world policy (advance world policy s) physics]
    rw [nextCarry, nextPost]
    exact combine_sound _ _ _ freshSound segment.2.2.2.1
  · rw [nextPost]
    exact segment.2.2.2.2.1

theorem step_safe (world : World) (policy : Policy) (s : State)
    (physics : Physics world) (entry : Entry world policy s) :
    SafeSamples (emitted world policy s) := by
  exact (segment_certificate (reading world policy s).lower s.post
    (world.loss (s.now + 1)) (world.loss (s.now + 2)) (reading world policy s).action
    (step_certified world policy s physics entry) entry.2.2.1 entry.2.2.2
    (physics.1 _) (physics.1 _)).1

theorem step_progress (world : World) (policy : Policy) (s : State)
    (physics : Physics world) (entry : Entry world policy s) :
    1 ≤ (emitted world policy s).length ∧ (emitted world policy s).length ≤ 2 := by
  have segment := segment_certificate (reading world policy s).lower s.post
    (world.loss (s.now + 1)) (world.loss (s.now + 2)) (reading world policy s).action
    (step_certified world policy s physics entry) entry.2.2.1 entry.2.2.2
    (physics.1 _) (physics.1 _)
  simpa only [emitted, samples_length] using segment.2.2.2.2.2

/-- Canonical execution: the environment supplies physical losses/noise only.
Actions are computed by the very same observation-only kernel as the bridge. -/
def finalState (world : World) (policy : Policy) : Nat → State → State
  | 0, s => s
  | n + 1, s => finalState world policy n (advance world policy s)

def trace (world : World) (policy : Policy) : Nat → State → List (Int × Int)
  | 0, _ => []
  | n + 1, s => emitted world policy s ++ trace world policy n (advance world policy s)

def writes (world : World) (policy : Policy) : Nat → State → Nat
  | 0, _ => 0
  | n + 1, s => (if (reading world policy s).action = .write then 1 else 0) +
      writes world policy n (advance world policy s)

theorem execution_safe (world : World) (policy : Policy) (n : Nat) (s : State)
    (physics : Physics world) (entry : Entry world policy s) :
    Entry world policy (finalState world policy n s) ∧ SafeSamples (trace world policy n s) := by
  induction n generalizing s with
  | zero => exact ⟨entry, by simp [trace, SafeSamples]⟩
  | succ n ih =>
    have following := step_preserves_entry world policy s physics entry
    have tail := ih (advance world policy s) following
    refine ⟨tail.1, ?_⟩
    intro point member
    simp only [trace, List.mem_append] at member
    rcases member with early | later
    · exact step_safe world policy s physics entry point early
    · exact tail.2 point later

theorem execution_length (world : World) (policy : Policy) (n : Nat) (s : State)
    (physics : Physics world) (entry : Entry world policy s) :
    n ≤ (trace world policy n s).length ∧ (trace world policy n s).length ≤ 2*n := by
  induction n generalizing s with
  | zero => simp [trace]
  | succ n ih =>
    have step := step_progress world policy s physics entry
    have tail := ih (advance world policy s) (step_preserves_entry world policy s physics entry)
    simp only [trace, List.length_append]
    omega

theorem execution_clock (world : World) (policy : Policy) (n : Nat) (s : State) :
    (finalState world policy n s).now = s.now + (trace world policy n s).length := by
  induction n generalizing s with
  | zero => simp [finalState, trace]
  | succ n ih =>
    simp only [finalState, trace, List.length_append, emitted, samples_length]
    rw [ih]
    simp only [advance]
    omega

theorem write_budget (world : World) (policy : Policy) (n : Nat) (s : State) :
    writes world policy n s ≤ n := by
  induction n generalizing s with
  | zero => simp [writes]
  | succ n ih =>
    have tail := ih (advance world policy s)
    simp only [writes]
    split <;> omega

/-- n decisions pay n probes, at most n writes, and one terminal readout.
This abstract ledger does not price acquisition of the physical hypothesis. -/
theorem total_cost_bound (world : World) (policy : Policy) (n : Nat) (s : State) :
    n + 1 + 10 * writes world policy n s ≤ 11*n + 1 := by
  have bounded := write_budget world policy n s
  omega

def initial : State := ⟨0, 440, false, 0⟩

theorem initial_entry (world : World) (policy : Policy) (physics : Physics world) :
    Entry world policy initial := by
  have error := physics.2.1 0
  unfold Entry
  rw [reading_lower world policy initial physics]
  simp only [initial, freshLower, Bool.false_eq_true,
    ite_false, State.post, postDelivery, Ready]
  omega

/-- Every horizon is covered by an actually constructed safe execution for
both policies, rather than assuming a certified plan exists. -/
theorem every_horizon_covered (world : World) (policy : Policy) (horizon : Nat)
    (physics : Physics world) :
    horizon ≤ (trace world policy horizon initial).length ∧
    SafeSamples (trace world policy horizon initial) ∧
    horizon ≤ (finalState world policy horizon initial).now := by
  have entry := initial_entry world policy physics
  have length := execution_length world policy horizon initial physics entry
  have safe := execution_safe world policy horizon initial physics entry
  have clock := execution_clock world policy horizon initial
  refine ⟨length.1, safe.2, ?_⟩
  rw [clock]
  simpa only [initial, Nat.zero_add] using length.1

theorem exact_horizon_prefix (world : World) (policy : Policy) (horizon : Nat)
    (physics : Physics world) :
    ((trace world policy horizon initial).take horizon).length = horizon ∧
    SafeSamples ((trace world policy horizon initial).take horizon) := by
  have all := every_horizon_covered world policy horizon physics
  constructor
  · simp only [List.length_take]
    omega
  · intro point member
    exact all.2.1 point (List.mem_of_mem_take member)

theorem decision_count_within_horizon (world : World) (policy : Policy)
    (n horizon : Nat) (physics : Physics world)
    (within : (finalState world policy n initial).now ≤ horizon) : n ≤ horizon := by
  have covered := every_horizon_covered world policy n physics
  omega

theorem horizon_cost_bound (world : World) (policy : Policy)
    (n horizon : Nat) (physics : Physics world)
    (within : (finalState world policy n initial).now ≤ horizon) :
    n + 1 + 10 * writes world policy n initial ≤ 11*horizon + 1 := by
  have count := decision_count_within_horizon world policy n horizon physics within
  have cost := total_cost_bound world policy n initial
  omega

theorem no_refusal_inside_boundary (world : World) (policy : Policy) (s : State)
    (physics : Physics world) (entry : Entry world policy s) :
    (reading world policy s).action ≠ .refuse := by
  have certified := step_certified world policy s physics entry
  intro refused
  simp [Certified, refused] at certified

theorem early_refill_selected (lower upper : Int) (ready : Ready lower)
    (room : upper + 220 ≤ 660) : choose .early lower upper = .write := by
  simp [choose, ready, room]

theorem prudent_one_tick (lower upper : Int) (ready : Ready lower) :
    duration (choose .prudent lower upper) = 1 := by
  by_cases wait : 400 ≤ lower <;> simp [choose, ready, wait, duration]


/-- This is arithmetic about the already explored comparator, not a
uniform competitive ratio over new scenarios or a physical theorem. -/
theorem known_gap_below_2_82_percent : (5671 - 5516) * 10000 < 282 * 5516 := by decide

theorem known_gap_not_below_2_8_percent : ¬ ((5671 - 5516) * 1000 < 28 * 5516) := by decide

end FixedBoundaryV5
