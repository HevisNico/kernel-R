import SelfCertifyingLearning.Scheduler

/-! One executable observation-level supervisor. Search-epoch memory and
fresh safety decisions are intentionally distinct. This is not a circuit
observer or an implementation of the search performed inside an epoch. -/
namespace SelfCertifyingLearning.Controller

structure Reading where
  rate : Renewal.Interval
  lowerReserve : Nat
  deriving Repr

/-- Build the controller input from bounded-error measurements. A signed
reserve lower bound below zero is rejected, never clipped to a false zero. -/
def fromMeasurement (rateReading rateError : Nat) (reserveReading : Int)
    (reserveError : Nat) : Option Reading :=
  let lower := reserveReading - (reserveError : Int)
  if 0 ≤ lower then
    some ⟨Renewal.measurement rateReading rateError, lower.toNat⟩
  else none

theorem measurement_sound (rateReading rateError truth : Nat)
    (reserveReading actualReserve : Int) (reserveError : Nat) (reading : Reading)
    (rateNoise : Renewal.distance rateReading truth ≤ rateError)
    (reserveNoise : reserveReading - (reserveError : Int) ≤ actualReserve)
    (accepted : fromMeasurement rateReading rateError reserveReading reserveError = some reading) :
    reading.rate.Contains truth ∧ (reading.lowerReserve : Int) ≤ actualReserve := by
  unfold fromMeasurement at accepted
  dsimp only at accepted
  split at accepted
  next nonnegative =>
    have equal := Option.some.inj accepted
    subst reading
    constructor
    · exact Renewal.measurement_honest rateReading rateError truth rateNoise
    · dsimp only
      rw [Int.toNat_of_nonneg nonnegative]
      exact reserveNoise
  next => contradiction

theorem negative_lower_bound_refused : fromMeasurement 10 1 0 1 = none := by decide

structure Result where
  anchor : Renewal.Interval
  reopened : Bool
  delay : Option Nat
  deriving Repr

/-- Every visit refreshes the safety decision from the current report,
including visits that keep the search anchor. No truth value is an input. -/
def visit (g reserve slew cap : Nat) (anchor : Renewal.Interval) (reading : Reading) : Result :=
  let memory := Renewal.review g anchor reading.rate
  ⟨memory.1, memory.2,
    Scheduler.plan reading.lowerReserve reserve (Scheduler.rateCeiling reading.rate slew cap) cap⟩

def run (g reserve slew cap : Nat) (anchor : Renewal.Interval) : List Reading → List Result
  | [] => []
  | reading :: rest =>
    let result := visit g reserve slew cap anchor reading
    result :: run g reserve slew cap result.anchor rest

def countReopens : List Result → Nat
  | [] => 0
  | result :: rest => (if result.reopened then 1 else 0) + countReopens rest

theorem run_length (g reserve slew cap anchor readings) :
    (run g reserve slew cap anchor readings).length = readings.length := by
  induction readings generalizing anchor with
  | nil => rfl
  | cons reading rest ih => simp [run, ih]

theorem run_reopening_count (g reserve slew cap anchor readings) :
    countReopens (run g reserve slew cap anchor readings) =
      Renewal.reopenings g anchor (readings.map Reading.rate) := by
  induction readings generalizing anchor with
  | nil => rfl
  | cons reading rest ih =>
    simp only [run, countReopens, List.map_cons, Renewal.reopenings]
    by_cases apart : Renewal.Separated g anchor reading.rate
    · simp [visit, Renewal.review, apart, ih]
    · simp [visit, Renewal.review, apart, ih]

/-- The actual executable supervisor inherits the nonoverlapping charge.
Honest true samples justify accounting but are not controller inputs. -/
theorem run_reopening_bound (g reserve slew cap : Nat) (initial : Renewal.Sample)
    (readings : List Reading) (samples : List Renewal.Sample)
    (matching : readings.map Reading.rate = samples.map Renewal.Sample.report) :
    g * countReopens (run g reserve slew cap initial.report readings) ≤
      Renewal.variation initial.truth samples := by
  rw [run_reopening_count, matching]
  exact Renewal.reopening_bound g initial samples

/-- No old anchor can lengthen the fresh report's authorized wait. -/
theorem visit_plan {g reserve slew cap anchor reading delay}
    (accepted : (visit g reserve slew cap anchor reading).delay = some delay) :
    0 < delay ∧ delay ≤ cap ∧
    Scheduler.rateCeiling reading.rate slew cap * delay + reserve ≤ reading.lowerReserve ∧
    ∀ other, other ≤ cap →
      Scheduler.rateCeiling reading.rate slew cap * other + reserve ≤ reading.lowerReserve →
      other ≤ delay :=
  Scheduler.plan_spec accepted

/-- Conditional service guarantee from current interval observations,
known future slew and per-tick dynamics. All times are relative to this
visit; lowerReserve must already be a sound measurement lower bound. -/
theorem visit_safe (g reserve slew cap : Nat) (anchor : Renewal.Interval) (reading : Reading)
    (truth : Nat) (rate : Nat → Nat) (state : Nat → Int)
    (rateObserved : reading.rate.Contains truth)
    (reserveObserved : (reading.lowerReserve : Int) ≤ state 0)
    (growth : ∀ k, k ≤ cap → rate k ≤ truth + slew * k)
    (dynamics : ∀ k, k < cap → state k - (rate (k + 1) : Int) ≤ state (k + 1))
    {delay : Nat} (accepted : (visit g reserve slew cap anchor reading).delay = some delay) :
    SafeUntil state reserve delay := by
  apply Scheduler.plan_safe state reserveObserved (accepted := accepted)
  intro k hk
  have ceiling := Scheduler.rate_ceiling_sound reading.rate truth slew cap rateObserved rate growth
    (k + 1) (by omega)
  have step := dynamics k hk
  omega

/-- The anchor can stay fixed while a smaller fresh delay is required. -/
theorem fresh_safety_without_reopening :
    let anchor : Renewal.Interval := ⟨10, 10, by decide⟩
    let reading : Reading := ⟨⟨12, 12, by decide⟩, 110⟩
    (visit 5 10 0 40 anchor reading).reopened = false ∧
    (visit 5 10 0 40 anchor reading).delay = some 8 := by decide

/-- Wide uncertainty alone may require refusal, without evidence of drift.
The accounting guarantee must never be used to suppress that refusal. -/
theorem uncertainty_refuses_without_reopening :
    let anchor : Renewal.Interval := ⟨10, 10, by decide⟩
    let reading : Reading := ⟨⟨0, 200, by decide⟩, 110⟩
    (visit 5 10 0 40 anchor reading).reopened = false ∧
    (visit 5 10 0 40 anchor reading).delay = none := by decide

end SelfCertifyingLearning.Controller
