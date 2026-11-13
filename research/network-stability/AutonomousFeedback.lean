import RoutedCalendar

namespace NetworkStability.AutonomousFeedback

open RoutedCalendar (HasRoom)
open SelfCertifyingLearning

structure Model (N : Nat) (P : Type) where
  cell : P → Fin N
  bias : P → Int
  drive : P → Nat
  route : P → List P

structure State (N : Nat) (P : Type) where
  pending : List P
  writes : Fin N → Nat
  log : List (P × Bool)

def start (N : Nat) (seed : List P) : State N P := ⟨seed, fun _ => 0, []⟩

def score (M : Model N P) (d : Nat) (s : State N P) (p : P) : Int :=
  M.bias p + (d : Int) * s.writes (M.cell p) + (M.drive p : Int)

def fires (M : Model N P) (d : Nat) (s : State N P) (p : P) (e : Int) : Bool :=
  decide (0 ≤ score M d s p + e)

/-- Process the head of a FIFO queue. Only FIRE appends downstream probes.
A silent read writes one dose. The transition contains no budget gate. -/
def step (M : Model N P) (d : Nat) (e : Int) (s : State N P) : State N P :=
  match s.pending with
  | [] => s
  | p :: tail =>
    let fire := fires M d s p e
    ⟨tail ++ (if fire then M.route p else []),
      fun i => s.writes i + if i = M.cell p ∧ fire = false then 1 else 0,
      (p, fire) :: s.log⟩

def run (M : Model N P) (d : Nat) (error : Nat → Int) :
    Nat → State N P → State N P
  | 0, s => s
  | n + 1, s => run M d error n (step M d (error s.log.length) s)

def mass (weight : P → Nat) (queue : List P) : Nat := (queue.map weight).sum

theorem mass_append (weight : P → Nat) (a b : List P) :
    mass weight (a ++ b) = mass weight a + mass weight b := by
  simp [mass]

/-- Each probe pays for itself and any FIRE descendants. The local reserve
pays separately for the currently serviced cell and its descendants. -/
structure Certificate (Q W eta : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) where
  weight : P → Nat
  reserve : Fin N → P → Nat
  eta_pos : 0 < eta
  scalar : ∀ p, mass weight (M.route p) + eta ≤ weight p
  local_route : ∀ p i, mass (reserve i) (M.route p) ≤ reserve i p
  local_write : ∀ p, 1 ≤ reserve (M.cell p) p
  seed_weight : mass weight seed ≤ W * N
  seed_reserve : ∀ i, mass (reserve i) seed ≤ Q

theorem step_scalar (M : Model N P) (d eta : Nat) (weight : P → Nat)
    (h : ∀ p, mass weight (M.route p) + eta ≤ weight p)
    (e : Int) (s : State N P) (active : s.pending ≠ []) :
    mass weight (step M d e s).pending + eta ≤ mass weight s.pending := by
  cases queue : s.pending with
  | nil => exact False.elim (active queue)
  | cons p tail =>
    simp only [step, queue]
    have hp := h p
    cases fires M d s p e <;> simp [mass] at hp ⊢ <;> omega

theorem step_local (M : Model N P) (d : Nat) (reserve : Fin N → P → Nat)
    (route : ∀ p i, mass (reserve i) (M.route p) ≤ reserve i p)
    (write : ∀ p, 1 ≤ reserve (M.cell p) p)
    (e : Int) (s : State N P) (i : Fin N) :
    (step M d e s).writes i + mass (reserve i) (step M d e s).pending ≤
      s.writes i + mass (reserve i) s.pending := by
  cases queue : s.pending with
  | nil => simp [step, queue]
  | cons p tail =>
    have routed := route p i
    have paid := write p
    by_cases cell : i = M.cell p <;> cases f : fires M d s p e <;>
      simp [step, queue, f, cell, mass] at routed paid ⊢ <;> omega

theorem local_run (M : Model N P) (d : Nat) (reserve : Fin N → P → Nat)
    (route : ∀ p i, mass (reserve i) (M.route p) ≤ reserve i p)
    (write : ∀ p, 1 ≤ reserve (M.cell p) p)
    (error : Nat → Int) (n : Nat) (s : State N P) (i : Fin N) :
    (run M d error n s).writes i + mass (reserve i) (run M d error n s).pending ≤
      s.writes i + mass (reserve i) s.pending := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.le_trans (ih _) (step_local M d reserve route write _ s i)

theorem run_empty (M : Model N P) (d : Nat) (error : Nat → Int)
    (n : Nat) (s : State N P) (done : s.pending = []) : run M d error n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, step, done] using ih

theorem terminal_by_budget (M : Model N P) (d eta : Nat) (weight : P → Nat)
    (pos : 0 < eta) (h : ∀ p, mass weight (M.route p) + eta ≤ weight p)
    (error : Nat → Int) (n : Nat) (s : State N P)
    (budget : mass weight s.pending ≤ eta * n) : (run M d error n s).pending = [] := by
  induction n generalizing s with
  | zero =>
    cases queue : s.pending with
    | nil => exact queue
    | cons p tail =>
      have hp := h p
      simp [queue, mass] at budget
      omega
  | succ n ih =>
    by_cases done : s.pending = []
    · rw [run_empty M d error _ s done]
      exact done
    · apply ih
      have decrease := step_scalar M d eta weight h (error s.log.length) s done
      rw [Nat.mul_succ] at budget
      omega

def NominalMargins (M : Model N P) (d : Nat) (lo hi : Nat → Int) :
    Nat → State N P → Prop
  | 0, _ => True
  | n + 1, s =>
    match s.pending with
    | [] => True
    | p :: _ =>
      HasRoom (score M d s p) (lo s.log.length) (hi s.log.length) ∧
        NominalMargins M d lo hi n (step M d 0 s)

theorem fires_eq_of_margin (M : Model N P) (d : Nat) (s : State N P) (p : P)
    (e lo hi : Int) (within : lo ≤ e ∧ e ≤ hi) (h : HasRoom (score M d s p) lo hi) :
    fires M d s p e = fires M d s p 0 := by
  unfold fires
  rcases h with ⟨clean, upper⟩ | ⟨clean, lower⟩
  · have a : ¬ 0 ≤ score M d s p + e := by omega
    simp [a, clean]
  · have a : 0 ≤ score M d s p + e := by omega
    simp [a, clean]

/-- Equal decisions give equal downstream queues as well as equal memories. -/
theorem run_eq_of_margins (M : Model N P) (d : Nat) (lo hi error : Nat → Int)
    (within : ∀ k, lo k ≤ error k ∧ error k ≤ hi k)
    (n : Nat) (s : State N P) (margins : NominalMargins M d lo hi n s) :
    run M d error n s = run M d (fun _ => 0) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases queue : s.pending with
    | nil => rw [run_empty M d error _ s queue, run_empty M d (fun _ => 0) _ s queue]
    | cons p tail =>
      simp only [NominalMargins, queue] at margins
      have same := fires_eq_of_margin M d s p _ _ _ (within s.log.length) margins.1
      have eqStep : step M d (error s.log.length) s = step M d 0 s := by
        simp only [step, queue, same]
      simpa only [run, eqStep] using ih _ margins.2

/-- This bound applies at every step, independently of the margins. -/
theorem prefix_bounds (Q d B rail W eta : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Certificate Q W eta M seed)
    (base : Fin N → Nat) (hbase : ∀ i, base i ≤ B) (railRoom : B + d * Q < rail)
    (error : Nat → Int) (n : Nat) :
    let s := run M d error n (start N seed)
    (RoutedCalendar.total ⟨s.writes, []⟩ ≤ Q * N) ∧
    ∀ i, s.writes i ≤ Q ∧ base i ≤ base i + d * s.writes i ∧
      base i + d * s.writes i < rail := by
  dsimp only
  have counts (i : Fin N) : (run M d error n (start N seed)).writes i ≤ Q := by
    have bound := local_run M d cert.reserve cert.local_route cert.local_write error n (start N seed) i
    have initial := cert.seed_reserve i
    change _ ≤ 0 + mass (cert.reserve i) seed at bound
    omega
  refine ⟨RoutedCalendar.total_le Q _ counts, fun i => ⟨counts i, ?_, ?_⟩⟩
  · omega
  · have mul := Nat.mul_le_mul_left d (counts i)
    have := hbase i
    omega

/-- All constants precede N. W*N is a common queue-draining horizon since
the integer margin eta is at least one. An empty queue is absorbing. -/
theorem certified_feedback (Q d B rail W eta : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Certificate Q W eta M seed)
    (base : Fin N → Nat) (hbase : ∀ i, base i ≤ B) (railRoom : B + d * Q < rail)
    (lo hi error : Nat → Int) (within : ∀ k, lo k ≤ error k ∧ error k ≤ hi k)
    (margins : NominalMargins M d lo hi (W * N) (start N seed)) :
    let terminal := run M d error (W * N) (start N seed)
    terminal.pending = [] ∧ terminal = run M d (fun _ => 0) (W * N) (start N seed) ∧
      (∀ n, run M d error n terminal = terminal) ∧
      ∀ n, let s := run M d error n (start N seed)
        RoutedCalendar.total ⟨s.writes, []⟩ ≤ Q * N ∧
        ∀ i, s.writes i ≤ Q ∧ base i ≤ base i + d * s.writes i ∧
          base i + d * s.writes i < rail := by
  dsimp only
  have size := Nat.mul_le_mul_right (W * N) (show 1 ≤ eta from cert.eta_pos)
  rw [Nat.one_mul] at size
  have done := terminal_by_budget M d eta cert.weight cert.eta_pos cert.scalar error (W * N)
    (start N seed) (Nat.le_trans cert.seed_weight size)
  exact ⟨done, run_eq_of_margins M d lo hi error within _ _ margins,
    fun n => run_empty M d error n _ done, prefix_bounds Q d B rail W eta M seed cert base hbase railRoom error⟩

end NetworkStability.AutonomousFeedback
