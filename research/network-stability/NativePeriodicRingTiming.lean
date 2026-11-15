import NativePeriodicRingTarget

namespace NetworkStability.NativePeriodicRing

open KernelR.Hybrid
open NativeRing (Input Probe root inputCell inputPort successor toDelivery horizon)

def stage : Input N → Nat
  | .inl i => i.val
  | .inr _ => N

theorem stage_le (key : Input N) : stage key ≤ N := by
  rcases key with i | ⟨⟩
  · exact i.isLt.le
  · exact le_rfl

theorem successor_stage (i : Fin N) : stage (successor i) = i.val + 1 := by
  unfold successor
  split
  · rfl
  · change N = i.val + 1
    have hi := i.isLt
    omega

theorem delay_bounds {p : Parameters N} (valid : p.Valid) (i : Fin N) :
    (8 : ℝ) ≤ p.ring.delay i ∧ (p.ring.delay i : ℝ) ≤ 9 :=
  ⟨by exact_mod_cast (valid.2.2.1 i).1, by exact_mod_cast (valid.2.2.1 i).2⟩

theorem period_bound {p : Parameters N} (valid : p.Valid) : horizon N < (p.period : ℝ) := by
  unfold horizon
  exact_mod_cast valid.2.1

private theorem horizon_pos (N : Nat) : 0 < horizon N := by
  unfold horizon
  positivity

theorem launch_mono {p : Parameters N} (valid : p.Valid) : StrictMono (launchDate p) := by
  intro i j order
  have period : (0 : ℝ) < p.period := (horizon_pos N).trans (period_bound valid)
  have time : (i : ℝ) < j := by exact_mod_cast order
  have gain := mul_lt_mul_of_pos_right time period
  change 1 + (i : ℝ) * p.period < 1 + (j : ℝ) * p.period
  linarith

theorem boundary_after_launch (p : Parameters N) (lap : Nat) :
    launchDate p lap < boundary p (lap + 1) :=
  lt_add_of_pos_right _ (horizon_pos N)

theorem boundary_before_launch {p : Parameters N} (valid : p.Valid) (lap : Nat) :
    boundary p lap < launchDate p lap := by
  cases lap with
  | zero => norm_num [boundary, launchDate]
  | succ k =>
    change launchDate p k + horizon N < launchDate p (k + 1)
    have period := period_bound valid
    simp only [launchDate, Nat.cast_add, Nat.cast_one]
    linarith

theorem boundary_mono {p : Parameters N} (valid : p.Valid) : StrictMono (boundary p) :=
  strictMono_nat_of_lt_succ fun k =>
    (boundary_before_launch valid k).trans (boundary_after_launch p k)

def launchToken (p : Parameters N) (size : 2 ≤ N) (lap : Nat) : Delivery N :=
  ⟨root size, 0, launchDate p lap⟩

theorem launch_queue_next (p : Parameters N) (size : 2 ≤ N) {lap sourceCount : Nat}
    (available : lap < sourceCount) :
    (launchQueue p size sourceCount).drop lap =
      launchToken p size lap :: (launchQueue p size sourceCount).drop (lap + 1) := by
  have inside : lap < (launchQueue p size sourceCount).length := by simpa [launchQueue] using available
  rw [List.drop_eq_getElem_cons inside]
  simp [launchQueue, launchToken]

theorem launch_queue_future {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {lap sourceCount : Nat} (token : Delivery N)
    (seen : token ∈ (launchQueue p size sourceCount).drop lap) :
    launchDate p lap ≤ token.due := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp seen
  rw [List.getElem_drop]
  simp only [launchQueue, List.getElem_map, List.getElem_range]
  exact (launch_mono valid).monotone (by omega)

/-- Bound every possible admission relative to its launch, including the return. -/
structure IntakeWindow (p : Parameters N) (lap : Nat) (x : Probe N) : Prop where
  lower : launchDate p lap + 8 * (stage x.input : ℝ) ≤ x.due
  upper : x.due ≤ launchDate p lap + (99 / 10) * (stage x.input : ℝ)
  initial : stage x.input = 0 → x.due = launchDate p lap

theorem IntakeWindow.settled_before_boundary {p : Parameters N} {lap : Nat} {x : Probe N}
    (window : IntakeWindow p lap x) :
    x.due + 15 / 2 < boundary p (lap + 1) := by
  have bound : (stage x.input : ℝ) ≤ N := by exact_mod_cast stage_le x.input
  have nonnegative : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  change x.due + 15 / 2 < launchDate p lap + horizon N
  unfold horizon
  linarith [window.upper]

theorem forward_routes {p : Parameters N} (size : 2 ≤ N) {lap : Nat} {x : Probe N} (i : Fin N)
    (key : x.input = .inl i) (intake : IntakeWindow p lap x)
    {fire : ℝ} (window : x.due + 3 / 10 < fire ∧ fire < x.due + 9 / 10) :
    router p size i fire = [toDelivery size ⟨fire + p.ring.delay i, successor i⟩] := by
  classical
  unfold router
  apply ite_eq_left
  by_cases eq : i = root size
  · right
    have time := intake.initial (by rw [key, eq]; rfl)
    exact ⟨lap, by linarith [window.1], by linarith [window.2]⟩
  · exact Or.inl eq

theorem return_route_closed {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {lap : Nat} {x : Probe N} (key : x.input = .inr ()) (intake : IntakeWindow p lap x)
    {fire : ℝ} (window : x.due + 3 / 10 < fire ∧ fire < x.due + 9 / 10) :
    router p size (root size) fire = [] := by
  classical
  unfold router
  apply ite_eq_right
  rintro (different | ⟨j, opened, shut⟩)
  · exact different rfl
  have lower := intake.lower
  rw [key] at lower
  change launchDate p lap + 8 * (N : ℝ) ≤ x.due at lower
  have sizeReal : (2 : ℝ) ≤ N := by exact_mod_cast size
  have late : launchDate p lap + 1 < fire := by linarith [window.1]
  have early : fire < launchDate p (lap + 1) := by
    have settled := intake.settled_before_boundary
    have next := boundary_before_launch valid (lap + 1)
    linarith [window.2]
  by_cases order : j ≤ lap
  · have before := (launch_mono valid).monotone order
    linarith
  · have after := (launch_mono valid).monotone (show lap + 1 ≤ j by omega)
    linarith

theorem IntakeWindow.routed {p : Parameters N} (valid : p.Valid)
    {lap : Nat} {x : Probe N} (intake : IntakeWindow p lap x) (i : Fin N)
    (key : x.input = .inl i) {fire : ℝ}
    (window : x.due + 3 / 10 < fire ∧ fire < x.due + 9 / 10) :
    IntakeWindow p lap ⟨fire + p.ring.delay i, successor i⟩ ∧
      x.due + 15 / 2 < fire + p.ring.delay i := by
  have delay := delay_bounds valid i
  have stageCast : (stage (successor i) : ℝ) = (stage x.input : ℝ) + 1 := by
    rw [successor_stage, key, Nat.cast_add, Nat.cast_one]
    rfl
  refine ⟨⟨?_, ?_, ?_⟩, by linarith [delay.1, window.1]⟩
  · change launchDate p lap + 8 * (stage (successor i) : ℝ) ≤ fire + p.ring.delay i
    rw [stageCast]
    linarith [intake.lower, delay.1, window.1]
  · change fire + p.ring.delay i ≤ launchDate p lap + (99 / 10) * (stage (successor i) : ℝ)
    rw [stageCast]
    linarith [intake.upper, delay.2, window.2]
  · intro zero
    change stage (successor i) = 0 at zero
    rw [successor_stage] at zero
    omega

end NetworkStability.NativePeriodicRing
