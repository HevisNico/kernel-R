import NativeRingTarget

/-!
# Periodic native ring: design and frozen target

Use the prepared cells, ports, successor graph, physical parameters, and
fixed per-edge delays of the one-token ring. A new external token arrives
at root port 0 at each time `1 + k * period`. The root contact opens for the
unit interval starting at each launch. A return on root port 2 arrives
after that window and settles before the next launch. Its learned FIRE
therefore acknowledges the lap without issuing another token.

The plant's pending list is finite. For an observation horizon, provide
any finite prefix of the external calendar whose first omitted date is
strictly after the horizon. The target includes a complete native
execution for every such prefix. Dates at the horizon are included.

## Membership and training order

All checks use rational arithmetic and inspect only parameters. A
settled weak transaction multiplies the amplitude by `exp (3 / 5)`.
The rational enclosure [1.822, 1.823] of this factor can be discharged
using `Real.exp_bound` at 3/5 with eight terms. Test the complete
trajectory up to the first certified strong stage. Every earlier stage
must be positive with upper amplitude at most 1. The last stage must
be contained in [9/5, 2]. The lower bound 9/10 from the launch-once class
is unnecessary for the native weak constructor. This design allows at
most two doses per port, independently of N, and at most 2N doses in all.
A later strong stage requires a certificate for every preceding weak stage.

Launch port 0 needs no dose. Return port 2 needs at least one. Relays
train in forward order, then the return trains. Each training lap
processes exactly one entry of the parameter-computed training list.
After that list is exhausted the whole ring fires on every lap.

With delays in [8, 9], a strong relay's FIRE within 9/10 of admission
gives an intake-to-intake gap below 99/10 and above the settlement
time 15/2. A lap of at most N forward hops followed by one final
transaction settles within 10(N+1) of launch. The period exceeds this
budget. On a certified trajectory all gains stay below log 4, including
during a partial dose, and recovery stays at its prepared value.

## Proof obligations for a later milestone

Use the weak and strong local legs with READY sections and quiet
spectators. Repeated admissions have a READY charge band, so their
actual FIRE clocks need not equal the launch-once scalar clock.
Transport the strong return with the root contact closed, using the
empty outgoing route. Compose settled laps with quiet waits and keep
the future external sources in the native queue. Use the complete
prefix construction for horizons inside a lap. The ledger at such a
horizon can include a fractional dose; only settled laps and the
frozen suffix have integer dose counts. The target below asserts all
of these observable consequences on the same execution at each horizon.
-/

namespace NetworkStability.NativePeriodicRing

open KernelR.Hybrid
open NativeRing (Input root inputCell inputPort successor toDelivery nativeParameters BelowRail horizon)

/-- The ring geometry is the same as for the one-launch compiler. -/
structure Parameters (N : Nat) where
  ring : NativeRing.Parameters N
  period : ℚ

abbrev Q : Nat := 2

def lowerAmplitude (a : ℚ) (writes : Nat) : ℚ := a * (911 / 500) ^ writes

def upperAmplitude (a : ℚ) (writes : Nat) : ℚ := a * (1823 / 1000) ^ writes

def weakAt (a : ℚ) (writes : Nat) : Bool :=
  decide (0 < a ∧ upperAmplitude a writes ≤ 1)

def strongAt (a : ℚ) (writes : Nat) : Bool :=
  decide (9 / 5 ≤ lowerAmplitude a writes ∧ upperAmplitude a writes ≤ 2)

/-- The entire prefix before the selected strong stage must be certified weak. -/
def dosePlan (a : ℚ) : Option Nat :=
  (List.range (Q + 1)).find? fun k =>
    strongAt a k && (List.range k).all (weakAt a)

def Parameters.Valid (p : Parameters N) : Prop :=
  2 ≤ N ∧ 10 * ((N : ℚ) + 1) < p.period ∧
  (∀ i, 8 ≤ p.ring.delay i ∧ p.ring.delay i ≤ 9) ∧
  (∀ i, if i.val = 0 then dosePlan (p.ring.forwardAmplitude i) = some 0
    else (dosePlan (p.ring.forwardAmplitude i)).isSome = true) ∧
  (dosePlan p.ring.returnAmplitude).isSome = true ∧ dosePlan p.ring.returnAmplitude ≠ some 0

instance (p : Parameters N) : Decidable p.Valid := by
  unfold Parameters.Valid
  infer_instance

def Parameters.check (p : Parameters N) : Bool := decide p.Valid

/-- Only read under `Parameters.Valid`, which ensures a plan for every used port. -/
def expectedWrites (p : Parameters N) (size : 2 ≤ N) (i : Fin N) (port : Port) : Nat :=
  if port = 0 then (dosePlan (p.ring.forwardAmplitude i)).getD 0
  else if i = root size ∧ port = 2 then (dosePlan p.ring.returnAmplitude).getD 0
  else 0

def trainingOrder (p : Parameters N) : List (Input N) :=
  (List.finRange N).flatMap (fun i =>
    List.replicate ((dosePlan (p.ring.forwardAmplitude i)).getD 0) (.inl i)) ++
  List.replicate ((dosePlan p.ring.returnAmplitude).getD 0) (.inr ())

def ports (N : Nat) : List (Input N) :=
  (List.finRange N).map Sum.inl ++ [.inr ()]

def firingKeys (p : Parameters N) (lap : Nat) : List (Input N) :=
  (ports N).takeWhile fun key => decide (some key ≠ (trainingOrder p)[lap]?)

def admittedKeys (p : Parameters N) (lap : Nat) : List (Input N) :=
  firingKeys p lap ++ (trainingOrder p)[lap]?.toList

def launchDate (p : Parameters N) (lap : Nat) : ℝ :=
  1 + (lap : ℝ) * (p.period : ℝ)

def boundary (p : Parameters N) : Nat → ℝ
  | 0 => 0
  | lap + 1 => launchDate p lap + horizon N

def freezeTime (p : Parameters N) : ℝ :=
  boundary p (trainingOrder p).length

def launchQueue (p : Parameters N) (size : 2 ≤ N) (count : Nat) : List (Delivery N) :=
  (List.range count).map fun lap => ⟨root size, 0, launchDate p lap⟩

noncomputable def prepared (p : Parameters N) (size : 2 ≤ N) (count : Nat) : Snapshot N :=
  { NativeRing.prepared p.ring size with pending := launchQueue p size count }

noncomputable def router (p : Parameters N) (size : 2 ≤ N) : Router N := by
  classical
  exact fun i fire =>
    if i ≠ root size ∨ (∃ lap, launchDate p lap ≤ fire ∧ fire < launchDate p lap + 1) then
      [toDelivery size ⟨fire + p.ring.delay i, successor i⟩]
    else []

def SettledLap (p : Parameters N) (size : 2 ≤ N) (sourceCount lap : Nat)
    {s u : Snapshot N} (run : Execution (nativeParameters N) (router p size) s u) : Prop :=
  s.time = boundary p lap ∧ CompleteThrough run (boundary p (lap + 1)) ∧
  s.pending = (launchQueue p size sourceCount).drop lap ∧
  u.pending = (launchQueue p size sourceCount).drop (lap + 1) ∧
  (∀ i, PreparedSection u i) ∧ (∀ i port, u.raw i port = none) ∧
  run.deliveries.map (fun d => (d.cell, d.port)) =
    (admittedKeys p lap).map (fun k => (inputCell size k, inputPort k)) ∧
  run.ledger.emissions.map Prod.fst = (firingKeys p lap).map (inputCell size) ∧
  (∀ i port, run.ledger.error i port =
    match (trainingOrder p)[lap]? with
    | none => 0
    | some k => if i = inputCell size k ∧ port = inputPort k then 3 / 5 else 0)

def FrozenMemory (p : Parameters N) (size : 2 ≤ N) (x : Values N) : Prop :=
  (∀ i port, x i (.z port) = (NativeRing.prepared p.ring size).x i (.z port) +
    (3 / 5 : ℝ) * expectedWrites p size i port) ∧
  ∀ i, x i .b = (NativeRing.prepared p.ring size).x i .b

/-- Every finite observation of the periodic source has a complete native
run. The settled cuts certify the predicted lap decisions and doses.
After the parameter-computed cut the cumulative counts and physical
memory have their frozen values, even as acknowledgement FIREs continue. -/
def NativePeriodicRingRefinement : Prop :=
  ∀ (N : Nat) (p : Parameters N), p.Valid → ∀ (size : 2 ≤ N)
    (sourceCount : Nat) (T : ℝ), 0 ≤ T → T < launchDate p sourceCount →
    ∃ (last : Snapshot N)
      (run : Execution (nativeParameters N) (router p size) (prepared p size sourceCount) last),
      CompleteThrough run T ∧
      run.AllStates (fun s => BelowRail s.x ∧ (freezeTime p ≤ s.time → FrozenMemory p size s.x)) ∧
      run.AllFlows (fun {s u} flow => ∀ t ∈ Set.Icc s.time u.time,
        BelowRail (flow.path t) ∧ (freezeTime p ≤ t → FrozenMemory p size (flow.path t))) ∧
      (∀ i port, run.ledger.mark i port = 0) ∧ (∀ i, run.ledger.recovery i = 0) ∧
      (∀ lap, boundary p (lap + 1) ≤ T →
        ∃ (start stop : Snapshot N)
          (before : Execution (nativeParameters N) (router p size) (prepared p size sourceCount) start)
          (during : Execution (nativeParameters N) (router p size) start stop)
          (after : Execution (nativeParameters N) (router p size) stop last),
          run = before.append (during.append after) ∧ SettledLap p size sourceCount lap during) ∧
      (freezeTime p ≤ T →
        ∀ i port, run.ledger.error i port = (3 / 5 : ℝ) * expectedWrites p size i port)

private def trainingExample : Parameters 2 :=
  ⟨⟨fun _ => 8, fun i => if i.val = 0 then 37 / 20 else 137 / 250, 1⟩, 31⟩

/-- Two weak laps train the relay; one weak lap then trains the return.
Every further lap fires at launch, relay, and return. -/
example : trainingExample.check = true ∧ trainingOrder trainingExample = [.inl 1, .inl 1, .inr ()] := by
  decide +kernel

/-- A one-cell loop lacks the distinct launch and relay cells required
by this topology. -/
example : (⟨⟨fun _ => 8, fun _ => 37 / 20, 1⟩, 31⟩ : Parameters 1).check = false := by
  decide +kernel

/-- With period 1, the next launch arrives at 2 while the first launch
is still FAST: its FIRE is later than 1 + 3/10 and FAST lasts one unit. -/
example : ({ trainingExample with period := 1 } : Parameters 2).check = false := by
  decide +kernel

/-- With both delays 1/20 and a strong relay, the return in a full lap
arrives less than one time unit after the root FIRE, while the root is FAST. -/
example : ({ trainingExample with ring :=
    { trainingExample.ring with delay := fun _ => 1 / 20, forwardAmplitude := fun _ => 37 / 20 } } :
    Parameters 2).check = false := by
  decide +kernel

/-- A delay of 40 leaves the first token in flight at the next launch
for period 31. The nominal lap budget no longer separates the launches. -/
example : ({ trainingExample with ring := { trainingExample.ring with delay := fun _ => 40 } } :
    Parameters 2).check = false := by
  decide +kernel

/-- A weak launch would consume the token at the root and write there. -/
example : ({ trainingExample with ring :=
    { trainingExample.ring with forwardAmplitude := fun i => if i.val = 0 then 1 else 137 / 250 } } :
    Parameters 2).check = false := by
  decide +kernel

/-- A relay starting at 0.9 leaves the weak window after one dose but
has not reached the strong window. A second weak stage cannot be certified. -/
example : dosePlan (9 / 10) = none ∧ ({ trainingExample with ring :=
    { trainingExample.ring with forwardAmplitude := fun i => if i.val = 0 then 37 / 20 else 9 / 10 } } :
    Parameters 2).check = false := by
  decide +kernel

/-- The same intermediate gap can prevent certification at the return port. -/
example : ({ trainingExample with ring := { trainingExample.ring with returnAmplitude := 9 / 10 } } :
    Parameters 2).check = false := by
  decide +kernel

/-- An initially strong return would acknowledge on its first visit,
where the prescribed protocol requires a learning write. -/
example : ({ trainingExample with ring := { trainingExample.ring with returnAmplitude := 37 / 20 } } :
    Parameters 2).check = false := by
  decide +kernel

end NetworkStability.NativePeriodicRing
