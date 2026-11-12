import SelfCertifyingLearning.ClosedLoop

/-! A concrete worst-case plant witnesses that the transition contracts are
jointly realizable. Loss occurs every tick; a write delivers its dose only
at completion and then saturates. No empirical experiment is claimed. -/
namespace SelfCertifyingLearning.RepairPlant
open Repair ClosedLoop

/-- Segment values beyond the action duration are irrelevant. -/
def segment (c : Config) (lower : Nat) (action : Action) (t : Nat) : Int :=
  match action with
  | .wait _ => (lower : Int) - (c.bound * t : Nat)
  | .write => if t < c.latency then (lower : Int) - (c.bound * t : Nat)
      else (pulse c lower : Int)
  | .refuse => lower

theorem segment_initial {c : Config} (valid : c.Valid) (lower : Nat) (action : Action) :
    segment c lower action 0 = lower := by
  cases action <;> simp [segment, valid.1]

theorem segment_end {c : Config} (valid : c.Valid) {lower : Nat} (ready : c.Ready lower) :
    segment c lower (choose c lower) (duration c (choose c lower)) =
      (next c lower (choose c lower) : Int) := by
  have spec := choose_spec valid ready
  cases chosen : choose c lower with
  | wait delay =>
    rw [chosen] at spec
    simp only [segment, duration, next]
    omega
  | write => simp [segment, duration, next]
  | refuse => rw [chosen] at spec; contradiction

theorem segment_dynamics {c : Config} (valid : c.Valid) {lower : Nat} (ready : c.Ready lower) :
    Dynamics c (segment c lower (choose c lower)) (choose c lower) := by
  have spec := choose_spec valid ready
  have capacity := ready.2
  have net := valid.2.2.1
  cases chosen : choose c lower with
  | wait delay =>
    constructor
    · intro k _
      simp only [segment, Nat.mul_succ, Int.natCast_add]
      omega
    · intro impossible; contradiction
  | write =>
    constructor
    · intro k hk
      change k < c.latency at hk
      simp only [segment, ite_eq_left hk]
      by_cases before : k + 1 < c.latency
      · simp only [ite_eq_left before, Nat.mul_succ, Int.natCast_add]
        omega
      · simp only [ite_eq_right before]
        have nonnegative : 0 ≤ ((c.bound * k : Nat) : Int) := by omega
        unfold pulse Config.gain
        omega
    · intro _
      simp [segment, valid.1]
      unfold pulse Config.gain Config.loss at *
      omega
  | refuse => rw [chosen] at spec; contradiction

/-- Execute n actions and hold the final value afterwards. This is a
finite deterministic witness, not an unbounded external clock driver. -/
def simulate (c : Config) : Nat → Nat → Nat → Int
  | 0, lower, _ => lower
  | n + 1, lower, t =>
    let action := choose c lower
    if t < duration c action then segment c lower action t
    else simulate c n (next c lower action) (t - duration c action)

theorem simulate_initial {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) : simulate c n lower 0 = lower := by
  cases n with
  | zero => rfl
  | succ n =>
    have positive := action_progress valid ready
    simp only [simulate, ite_eq_left positive]
    exact segment_initial valid lower _

theorem simulate_prefix {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) {t : Nat} (within : t ≤ duration c (choose c lower)) :
    simulate c (n + 1) lower t = segment c lower (choose c lower) t := by
  by_cases before : t < duration c (choose c lower)
  · simp [simulate, before]
  · have equal : t = duration c (choose c lower) := by omega
    subst t
    simp [simulate, simulate_initial valid n (next_ready valid ready), segment_end valid ready]

theorem simulate_shift (c : Config) (n lower t : Nat) :
    simulate c (n + 1) lower (duration c (choose c lower) + t) =
      simulate c n (next c lower (choose c lower)) t := by
  have after : ¬ duration c (choose c lower) + t < duration c (choose c lower) := by omega
  simp [simulate, after]

theorem simulate_realizes {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) : Realizes c n lower (simulate c n lower) := by
  induction n generalizing lower with
  | zero => trivial
  | succ n ih =>
    constructor
    · have laws := segment_dynamics valid ready
      constructor
      · intro k hk
        rw [simulate_prefix valid n ready (by omega), simulate_prefix valid n ready (by omega)]
        exact laws.1 k hk
      · intro write
        have endTime : duration c (choose c lower) = c.latency := by rw [write]; rfl
        rw [simulate_prefix valid n ready (by omega), simulate_prefix valid n ready (by omega)]
        exact laws.2 write
    · have tail := ih (next_ready valid ready)
      have same : (fun t => simulate c (n + 1) lower (duration c (choose c lower) + t)) =
          simulate c n (next c lower (choose c lower)) := by
        funext t
        exact simulate_shift c n lower t
      simpa only [same] using tail

theorem simulated_service {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) : SafeUntil (simulate c n lower) c.service (clock c n lower) :=
  (execution_safe valid n ready (simulate c n lower)
    (by rw [simulate_initial valid n ready]; exact Int.le_refl _) (simulate_realizes valid n ready)).1

/-- Service 10, rate 2, latency 3: guard 16, net gain 1, target 18.
Two delayed writes are necessary before a positive wait can be authorized. -/
def exampleConfig : Config := ⟨10, 2, 3, 7, 20, 4⟩

theorem example_valid : exampleConfig.Valid := by decide

theorem example_actions : trace exampleConfig 3 16 = [.write, .write, .wait 1] := by decide

theorem example_values :
    (List.range 8).map (simulate exampleConfig 3 16) = [16, 14, 12, 17, 15, 13, 18, 16] := by decide

theorem example_cost : clock exampleConfig 3 16 = 7 ∧ writes (trace exampleConfig 3 16) = 2 := by decide

theorem example_service : SafeUntil (simulate exampleConfig 3 16) 10 7 :=
  simulated_service example_valid 3 (by decide)

/-- Without the repair buffer, service may fail before the dose arrives. -/
theorem missing_buffer_fails : segment exampleConfig 10 .write 1 = 8 := by decide

theorem missing_buffer_refused : choose exampleConfig 10 = .refuse := by decide

/-- An explicitly interrupted-service batch can also restart from below
the buffer. Its endpoint contract is covered by recovery_restores. -/
theorem interrupted_recovery_count : budget exampleConfig 12 = 6 ∧
    pulses exampleConfig 6 12 = 18 ∧ 6 * exampleConfig.latency = 18 := by decide

/-- Equal dose and repair-time loss give no progress, despite repeating
writes. The production policy refuses this configuration. -/
def stalledConfig : Config := ⟨10, 2, 3, 6, 20, 4⟩

theorem no_net_gain_stalls : pulses stalledConfig 10 16 = 16 ∧
    choose stalledConfig 16 = .refuse := by decide

def crampedConfig : Config := ⟨10, 2, 3, 7, 17, 4⟩

theorem insufficient_capacity_stalls : pulses crampedConfig 10 16 = 17 ∧
    choose crampedConfig 16 = .refuse := by decide

end SelfCertifyingLearning.RepairPlant
