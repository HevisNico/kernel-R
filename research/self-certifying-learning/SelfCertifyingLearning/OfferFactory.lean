import SelfCertifyingLearning.EpochSafety

/-! Observation-backed finite-horizon offer construction. Measurement error,
future slew and delayed-dose physics stay explicit, independently testable
premises. Stale readings are refused rather than assigned a fresh date. -/
namespace SelfCertifyingLearning.OfferFactory
open Repair ClosedLoop Epochs

structure Hardware where
  latency : Nat
  dose : Nat
  capacity : Nat
  maxWait : Nat
  slew : Nat
  deriving DecidableEq, Repr

structure Reading where
  measuredAt : Nat
  value : Nat
  error : Nat
  deriving DecidableEq, Repr

structure Request where
  reading : Reading
  counts : List Nat
  deriving DecidableEq, Repr

def horizon (hardware : Hardware) (count : Nat) : Nat :=
  count * max hardware.maxWait hardware.latency

def make (policy : Policy) (hardware : Hardware) (reading : Reading) (count : Nat) : Offer :=
  let window := horizon hardware count
  let report := Renewal.measurement reading.value reading.error
  ⟨⟨policy.service, Scheduler.rateCeiling report hardware.slew window,
    hardware.latency, hardware.dose, hardware.capacity, hardware.maxWait⟩,
    count, reading.measuredAt, reading.measuredAt + window⟩

theorem make_hardware (policy hardware reading count) :
    (make policy hardware reading count).config.service = policy.service ∧
    (make policy hardware reading count).config.latency = hardware.latency ∧
    (make policy hardware reading count).config.dose = hardware.dose ∧
    (make policy hardware reading count).config.capacity = hardware.capacity ∧
    (make policy hardware reading count).config.maxWait = hardware.maxWait := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def propose (policy : Policy) (hardware : Hardware) (cursor : Cursor) (request : Request) : List Offer :=
  if request.reading.measuredAt = cursor.now then request.counts.map (make policy hardware request.reading)
  else []

/-- Fresh observations generate candidates; the existing admission filter
still checks gain, capacity, handoff reserve, completion and switching cost. -/
def run (policy : Policy) (hardware : Hardware) (cursor : Cursor) : List Request → Plan
  | [] => .complete cursor
  | request :: rest =>
    match select policy cursor (propose policy hardware cursor request) with
    | none => .blocked cursor
    | some offer => .phase cursor offer (run policy hardware (advance cursor offer) rest)

theorem run_wellFormed (policy hardware cursor requests) :
    WellFormed policy cursor (run policy hardware cursor requests) := by
  induction requests generalizing cursor with
  | nil => exact .complete cursor
  | cons request rest ih =>
    simp only [run]
    split
    next => exact .blocked cursor
    next offer chosen => exact .phase (select_sound chosen).2 (ih _)

theorem proposed_origin {policy hardware cursor request offer}
    (member : offer ∈ propose policy hardware cursor request) :
    request.reading.measuredAt = cursor.now ∧
      ∃ count ∈ request.counts, make policy hardware request.reading count = offer := by
  unfold propose at member
  split at member
  next fresh => exact ⟨fresh, List.mem_map.mp member⟩
  next => simp at member

theorem stale_refused (policy hardware cursor request) (stale : request.reading.measuredAt ≠ cursor.now) :
    propose policy hardware cursor request = [] := by simp [propose, stale]

theorem generated_span {policy hardware cursor reading count}
    (admitted : Admissible policy cursor (make policy hardware reading count)) :
    span cursor (make policy hardware reading count) ≤ horizon hardware count :=
  clock_upper admitted.valid count admitted.ready

/-- Loss accumulated over a write, using actual rates rather than the
controller's proposed ceiling. Rate k is the loss during the tick ending k. -/
def loss (rate : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => loss rate n + rate (n + 1)

theorem constant_loss (rate n : Nat) : loss (fun _ => rate) n = rate * n := by
  induction n with
  | zero => simp [loss]
  | succ n ih => simp [loss, ih, Nat.mul_succ]

theorem loss_bounded (rate : Nat → Nat) (bound n : Nat)
    (rates : ∀ k, k ≤ n → rate k ≤ bound) : loss rate n ≤ bound * n := by
  induction n with
  | zero => simp [loss]
  | succ n ih =>
    have previous := ih (by intro k hk; exact rates k (by omega))
    have last := rates (n + 1) (by omega)
    simp only [loss, Nat.mul_succ]
    omega

/-- Minimum dose and usable capacity, applied only to commanded writes.
This is an actuator assumption stated with actual accumulated loss. -/
def Delivers (c : Config) : Nat → Nat → (Nat → Nat) → (Nat → Int) → Prop
  | 0, _, _, _ => True
  | n + 1, lower, rate, state =>
    let action := choose c lower
    (action = .write → min (c.capacity : Int)
      (state 0 - (loss rate c.latency : Int) + (c.dose : Int)) ≤ state c.latency) ∧
    Delivers c n (next c lower action) (fun t => rate (duration c action + t))
      (fun t => state (duration c action + t))

/-- Derive the old transition contract from bounded actual rates, per-tick
physics and delayed delivery. No safety predicate is assumed. -/
theorem realizes_from_physics (c : Config) (n lower : Nat) (rate : Nat → Nat) (state : Nat → Int)
    (rates : ∀ k, k ≤ clock c n lower → rate k ≤ c.bound)
    (flow : ∀ k, k < clock c n lower → state k - (rate (k + 1) : Int) ≤ state (k + 1))
    (delivery : Delivers c n lower rate state) : ClosedLoop.Realizes c n lower state := by
  induction n generalizing lower rate state with
  | zero => trivial
  | succ n ih =>
    constructor
    · constructor
      · intro k hk
        have physical := flow k (by simp only [clock]; omega)
        have ceiling := rates (k + 1) (by simp only [clock]; omega)
        omega
      · intro writing
        have durationEq : duration c (choose c lower) = c.latency := by rw [writing]; rfl
        have ceiling := loss_bounded rate c.bound c.latency
          (by intro k hk; apply rates; simp only [clock, durationEq]; omega)
        have delivered := delivery.1 writing
        unfold Config.loss
        omega
    · apply ih
      · intro k hk
        exact rates (duration c (choose c lower) + k) (by simp only [clock]; omega)
      · intro k hk
        have physical := flow (duration c (choose c lower) + k) (by simp only [clock]; omega)
        simpa only [Nat.add_assoc] using physical
      · exact delivery.2

/-- Physical evidence for the actual reading and generated phase. A known
slew envelope is necessary even with a perfect current measurement. -/
structure Evidence (policy : Policy) (hardware : Hardware) (cursor : Cursor)
    (reading : Reading) (count : Nat) (rate : Nat → Nat) (state : Nat → Int) : Prop where
  fresh : reading.measuredAt = cursor.now
  noise : Renewal.distance reading.value (rate 0) ≤ reading.error
  growth : ∀ k, k ≤ horizon hardware count → rate k ≤ rate 0 + hardware.slew * k
  flow : ∀ k, k < horizon hardware count → state k - (rate (k + 1) : Int) ≤ state (k + 1)
  delivery : Delivers (make policy hardware reading count).config count
    (entry cursor (make policy hardware reading count)) rate state

theorem generated_realizes {policy hardware cursor reading count rate state}
    (admitted : Admissible policy cursor (make policy hardware reading count))
    (evidence : Evidence policy hardware cursor reading count rate state) :
    ClosedLoop.Realizes (make policy hardware reading count).config count
      (entry cursor (make policy hardware reading count)) state := by
  have honest := Renewal.measurement_honest reading.value reading.error (rate 0) evidence.noise
  have ceiling := Scheduler.rate_ceiling_sound (Renewal.measurement reading.value reading.error)
    (rate 0) hardware.slew (horizon hardware count) honest rate evidence.growth
  have window := generated_span admitted
  change clock (make policy hardware reading count).config count
    (entry cursor (make policy hardware reading count)) ≤ horizon hardware count at window
  apply realizes_from_physics
  · intro k hk
    exact ceiling k (by omega)
  · intro k hk
    exact evidence.flow k (by omega)
  · exact evidence.delivery

/-- Evidence follows the exact requests and selections used by run. It is
only required for executed phases, not for a blocked future continuation. -/
def Supported (policy : Policy) (hardware : Hardware) (state : Nat → Int) (rate : Nat → Nat) :
    Cursor → List Request → Prop
  | _, [] => True
  | cursor, request :: rest =>
    match select policy cursor (propose policy hardware cursor request) with
    | none => True
    | some offer =>
      (∃ count ∈ request.counts, make policy hardware request.reading count = offer ∧
        Evidence policy hardware cursor request.reading count
          (fun t => rate (cursor.now + t)) (fun t => state (cursor.now + t))) ∧
      Supported policy hardware state rate (advance cursor offer) rest

theorem supported_realizes {policy hardware cursor requests state rate}
    (supported : Supported policy hardware state rate cursor requests) :
    EpochSafety.Realizes state (run policy hardware cursor requests) := by
  induction requests generalizing cursor with
  | nil => trivial
  | cons request rest ih =>
    simp only [run]
    unfold Supported at supported
    cases chosen : select policy cursor (propose policy hardware cursor request) with
    | none => simp [EpochSafety.Realizes]
    | some offer =>
      simp only [chosen] at supported ⊢
      obtain ⟨count, _, equal, evidence⟩ := supported.1
      have admitted := (select_sound chosen).2
      rw [← equal] at admitted
      have realized := generated_realizes admitted evidence
      rw [equal] at realized
      have countEqual : offer.decisions = count := by rw [← equal]; rfl
      rw [← countEqual] at realized
      exact ⟨realized, ih supported.2⟩

/-- End-to-end finite-prefix guarantee: fresh noisy observations generate
offers, admission selects them, physics implies their transition laws,
and the existing calendar and cost theorems compose the resulting plan. -/
theorem system_safe {policy hardware cursor requests state rate}
    (initial : policy.service ≤ cursor.lower)
    (observed : (cursor.lower : Int) ≤ state cursor.now)
    (supported : Supported policy hardware state rate cursor requests) :
    EpochSafety.SafeBetween state policy.service cursor.now (run policy hardware cursor requests).finish.now ∧
    ((run policy hardware cursor requests).finish.lower : Int) ≤
      state (run policy hardware cursor requests).finish.now :=
  EpochSafety.composed_safe (run_wellFormed policy hardware cursor requests) state initial observed
    (supported_realizes supported)

theorem system_cost (policy hardware cursor requests) :
    (run policy hardware cursor requests).writes ≤ cursor.debt + cursor.credit +
      (run policy hardware cursor requests).leakBudget :=
  global_write_bound (run_wellFormed policy hardware cursor requests)

end SelfCertifyingLearning.OfferFactory
