import SelfCertifyingLearning.ClosedLoop
import SelfCertifyingLearning.Renewal

/-! Renewable finite-horizon ceilings and the v2 decision policy. No absolute
rate ceiling or future true rate is a controller input. These are local
lemmas, not a new end-to-end physical wrapper theorem. -/
open SelfCertifyingLearning

namespace AdaptiveRefresh

/-- A finite observed prefix admits a continuation exceeding any proposed
unconditional ceiling at the next tick, without altering any past sample. -/
theorem finite_prefix_no_unconditional_ceiling (past : Nat → Nat) (n bound : Nat) :
    ∃ alternative : Nat → Nat,
      (∀ t, t ≤ n → alternative t = past t) ∧ bound < alternative (n + 1) := by
  refine ⟨fun t => if t ≤ n then past t else bound + 1, ?_, ?_⟩
  · intro t ht; simp [ht]
  · have later : ¬ n + 1 ≤ n := by omega
    simp only [ite_eq_right later]
    omega

def ceiling (report error variation : Nat) := report + error + variation

theorem ceiling_sound (report error variation truth future : Nat)
    (observed : truth ≤ report + error) (growth : future ≤ truth + variation) :
    future ≤ ceiling report error variation := by unfold ceiling; omega

theorem next_ceiling_growth (y z error variation a b : Nat)
    (first : a ≤ y + error) (second : z ≤ b + error)
    (growth : b ≤ a + variation) :
    ceiling z error variation ≤ ceiling y error variation + variation + 2 * error := by
  unfold ceiling
  omega

theorem measured_violation (lower truth oldCeiling : Nat)
    (honest : lower ≤ truth) (exceeds : oldCeiling < lower) : oldCeiling < truth := by omega

def config (u : Nat) : Repair.Config := ⟨100, u, 1, 220, 660, 40⟩

def choose (u lower : Nat) : ClosedLoop.Action :=
  let c := config u
  if c.Valid ∧ c.Ready lower then
    match Scheduler.plan lower (100 + u + 12) u 40 with
    | some d => .wait d
    | none => .write
  else .refuse

theorem wait_certificate {u lower d}
    (chosen : choose u lower = .wait d) :
    0 < d ∧ d ≤ 40 ∧ u * d + (100 + u + 12) ≤ lower := by
  by_cases ready : (config u).Valid ∧ (config u).Ready lower
  · simp only [choose, ite_eq_left ready] at chosen
    cases h : Scheduler.plan lower (100 + u + 12) u 40 with
    | none => simp [h] at chosen
    | some k =>
      simp only [h, ClosedLoop.Action.wait.injEq] at chosen
      subst k
      have spec := Scheduler.plan_spec h
      exact ⟨spec.1, spec.2.1, spec.2.2.1⟩
  · simp [choose, ready] at chosen

theorem wait_handoff {u nextU lower d : Nat}
    (chosen : choose u lower = .wait d) (growth : nextU ≤ u + 12) :
    100 + nextU ≤ lower - u * d := by
  have spec := wait_certificate chosen
  omega

theorem write_ready {u lower}
    (chosen : choose u lower = .write) : (config u).Valid ∧ (config u).Ready lower := by
  by_cases ready : (config u).Valid ∧ (config u).Ready lower
  · exact ready
  · simp [choose, ready] at chosen

theorem write_interior {u lower} (chosen : choose u lower = .write)
    (state : Nat → Int) (observed : (lower : Int) ≤ state 0)
    (flow : ∀ k, k < (config u).latency → state k - (u : Int) ≤ state (k + 1)) :
    SafeUntil state 100 1 :=
  Repair.pulse_interior_safe (config u) (write_ready chosen).2 state observed flow

theorem write_endpoint {u lower} (chosen : choose u lower = .write)
    (initial final : Int) (observed : (lower : Int) ≤ initial)
    (delivered : min (660 : Int) (initial - (u : Int) + 220) ≤ final) :
    (Repair.pulse (config u) lower : Int) ≤ final := by
  apply Repair.pulse_endpoint (write_ready chosen).1 initial final observed
  simpa [config, Repair.Config.loss] using delivered

/-- Reports beyond the upper endpoint can be ambiguous: 21±1 contains 20,
which still satisfies the old ceiling 20. -/
theorem upper_exceedance_is_not_violation :
    (Renewal.measurement 21 1).Contains 20 ∧ 20 < (Renewal.measurement 21 1).hi := by
  unfold Renewal.Interval.Contains Renewal.measurement
  decide

/-- Input: reserve report, rate report, anchor center, delivery flag,
carried lower (-1 means absent), previous ceiling (-1 means absent). -/
def respond (line : String) : String :=
  match line.splitOn " " with
  | [xs, ys, ans, ds, cs, us] =>
    match xs.toInt?, ys.toNat?, ans.toNat?, ds.toNat?, cs.toInt?, us.toInt? with
    | some x, some y, some anchor, some delivered, some carried, some oldU =>
      if delivered > 1 then "ERROR delivery flag" else
      let fresh := if delivered = 1 then min (660 : Int) (x - 2 + 220) else x - 2
      let report := Renewal.measurement y 1
      let invalid := oldU ≥ 0 && (report.lo : Int) > oldU
      let ambiguous := oldU ≥ 0 && !invalid && (report.hi : Int) > oldU
      let lower := if invalid || carried < 0 then fresh else max fresh carried
      let u := ceiling y 1 10
      let review := Renewal.review 5 (Renewal.measurement anchor 1) report
      let newAnchor := if review.2 then y else anchor
      let action := if invalid || lower < 0 then ClosedLoop.Action.refuse else choose u lower.toNat
      let kind := match action with
        | .wait _ => "wait"
        | .write => "write"
        | .refuse => "refuse"
      s!"{lower} {u} {kind} {ClosedLoop.duration (config u) action} {newAnchor} {if review.2 then 1 else 0} {if ambiguous then 1 else 0} {if invalid then 1 else 0}"
    | _, _, _, _, _, _ => "ERROR numeric input"
  | _ => "ERROR field count"

end AdaptiveRefresh

partial def serve (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  output.putStrLn (AdaptiveRefresh.respond line.trimAscii.toString)
  output.flush
  serve input output

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "READY"
  output.flush
  serve input output
