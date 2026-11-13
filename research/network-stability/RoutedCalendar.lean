import SelfCertifyingLearning.Composition

namespace NetworkStability.RoutedCalendar

open SelfCertifyingLearning

/-- A contact names an earlier FIRE slot and contributes a nonnegative amount
to the receiving probe's score. Unavailable slots contribute zero. -/
structure Contact where
  source : Nat
  weight : Nat

structure Slot (N : Nat) where
  cell : Fin N
  offset : Int
  contacts : List Contact

structure State (N : Nat) where
  writes : Fin N → Nat
  fires : List Bool

def start (N : Nat) : State N := ⟨fun _ => 0, []⟩

def load (fires : Nat → Bool) : List Contact → Nat
  | [] => 0
  | c :: rest => (if fires c.source then c.weight else 0) + load fires rest

def cleanScore (d : Nat) (s : State N) (p : Slot N) : Int :=
  p.offset + (d : Int) * s.writes p.cell +
    (load (fun j => s.fires[j]?.getD false) p.contacts : Int)

def decision (d : Nat) (s : State N) (p : Slot N) (error : Int) : Bool :=
  decide (0 ≤ cleanScore d s p + error)

def advance (s : State N) (p : Slot N) (fire : Bool) : State N :=
  ⟨fun i => s.writes i + if i = p.cell ∧ fire = false then 1 else 0,
    s.fires ++ [fire]⟩

/-- The error is indexed by the calendar position, equivalently by the
number of decisions already recorded. -/
def run (d : Nat) (error : Nat → Int) : State N → List (Slot N) → State N
  | s, [] => s
  | s, p :: rest =>
    run d error (advance s p (decision d s p (error s.fires.length))) rest

/-- Strict room for silence, weak room for FIRE. Equality at threshold fires. -/
def HasRoom (score lo hi : Int) : Prop :=
  (score < 0 ∧ score + hi < 0) ∨ (0 ≤ score ∧ 0 ≤ score + lo)

def NominalMargins (d : Nat) (lo hi : Nat → Int) : State N → List (Slot N) → Prop
  | _, [] => True
  | s, p :: rest =>
    HasRoom (cleanScore d s p) (lo s.fires.length) (hi s.fires.length) ∧
      NominalMargins d lo hi (advance s p (decision d s p 0)) rest

theorem decision_eq_of_margin (d : Nat) (s : State N) (p : Slot N) (e lo hi : Int)
    (within : lo ≤ e ∧ e ≤ hi) (margin : HasRoom (cleanScore d s p) lo hi) :
    decision d s p e = decision d s p 0 := by
  unfold decision
  rcases margin with ⟨clean, upper⟩ | ⟨clean, lower⟩
  · have a : ¬ 0 ≤ cleanScore d s p + e := by omega
    simp [a, clean]
  · have a : 0 ≤ cleanScore d s p + e := by omega
    simp [a, clean]

/-- First differing decision: equal earlier decisions give equal stored counts
and equal routed input. The nominal margin then forces the next decision. -/
theorem run_eq_of_margins (d : Nat) (lo hi error : Nat → Int) {N : Nat}
    (calendar : List (Slot N)) (s : State N)
    (within : ∀ k, lo k ≤ error k ∧ error k ≤ hi k)
    (margins : NominalMargins d lo hi s calendar) :
    run d error s calendar = run d (fun _ => 0) s calendar := by
  induction calendar generalizing s with
  | nil => rfl
  | cons p rest ih =>
    change _ ∧ _ at margins
    have same := decision_eq_of_margin d s p _ _ _ (within s.fires.length) margins.1
    rw [run, run, same]
    exact ih _ margins.2

theorem run_append (d : Nat) (error : Nat → Int) (s : State N)
    (before after : List (Slot N)) :
    run d error s (before ++ after) = run d error (run d error s before) after := by
  induction before generalizing s with
  | nil => rfl
  | cons p rest ih => exact ih _

theorem margins_append (d : Nat) (lo hi : Nat → Int) (s : State N)
    (before after : List (Slot N)) (h : NominalMargins d lo hi s (before ++ after)) :
    NominalMargins d lo hi s before := by
  induction before generalizing s with
  | nil => trivial
  | cons p rest ih =>
    change _ ∧ _ at h ⊢
    exact ⟨h.1, ih _ h.2⟩

/-- The budget counts offered opportunities, which are externally scheduled.
There is no clipping or budget gate in the write transition. -/
def offers (i : Fin N) : List (Slot N) → Nat
  | [] => 0
  | p :: rest => (if i = p.cell then 1 else 0) + offers i rest

theorem offers_append (i : Fin N) (a b : List (Slot N)) :
    offers i (a ++ b) = offers i a + offers i b := by
  induction a with
  | nil => simp [offers]
  | cons p rest ih => simp [offers, ih, Nat.add_assoc]

theorem writes_bound (d : Nat) (error : Nat → Int) (s : State N)
    (calendar : List (Slot N)) (i : Fin N) :
    (run d error s calendar).writes i ≤ s.writes i + offers i calendar := by
  induction calendar generalizing s with
  | nil => simp [run, offers]
  | cons p rest ih =>
    simp only [run, offers]
    apply Nat.le_trans (ih _)
    by_cases cell : i = p.cell <;> cases decision d s p (error s.fires.length) <;>
      simp [advance, cell, Nat.add_assoc]

def total (s : State N) : Nat :=
  weighted (fun _ => 1) s.writes (List.finRange N)

private theorem weighted_zero {I : Type} (xs : List I) :
    weighted (fun _ => 1) (fun _ => 0) xs = 0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [weighted, ih]

private theorem weighted_const {I : Type} (xs : List I) (Q : Nat) :
    weighted (fun _ => 1) (fun _ => Q) xs = Q * xs.length := by
  induction xs with
  | nil => simp [weighted]
  | cons i xs ih => simp [weighted, ih, Nat.mul_succ, Nat.add_comm]

theorem total_le (Q : Nat) {N : Nat} (s : State N) (counts : ∀ i, s.writes i ≤ Q) :
    total s ≤ Q * N := by
  have h := weighted_balance (List.finRange N) (fun _ => 1) (fun _ => Q) s.writes
    (fun _ => 0) (fun _ => 0) (fun i _ => by simpa using counts i)
  simpa [total, weighted_zero, weighted_const] using h

/-- Unclipped stored memory in integer score units. A write adds d units. -/
def memory (d : Nat) (base : Fin N → Nat) (s : State N) (i : Fin N) : Nat :=
  base i + d * s.writes i

/-- The routed need and write budget hold together at every calendar cut.
Q, d, B and rail are fixed before the size N. -/
theorem certified_episode (Q d B rail : Nat) {N : Nat}
    (calendar : List (Slot N)) (base : Fin N → Nat) (lo hi error : Nat → Int)
    (hbase : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (budget : ∀ i, offers i calendar ≤ Q)
    (within : ∀ k, lo k ≤ error k ∧ error k ≤ hi k)
    (margins : NominalMargins d lo hi (start N) calendar) :
    ∀ before after, calendar = before ++ after →
      let s := run d error (start N) before
      s = run d (fun _ => 0) (start N) before ∧
      total s ≤ Q * N ∧
      ∀ i, s.writes i ≤ Q ∧ base i ≤ memory d base s i ∧
        memory d base s i ≤ B + d * Q ∧ memory d base s i < rail := by
  intro before after split
  subst calendar
  have counts (i : Fin N) : (run d error (start N) before).writes i ≤ Q := by
    have localBound := writes_bound d error (start N) before i
    have full := budget i
    rw [offers_append] at full
    change _ ≤ 0 + _ at localBound
    omega
  refine ⟨run_eq_of_margins d lo hi error before (start N) within
      (margins_append d lo hi (start N) before after margins), total_le Q _ counts, ?_⟩
  intro i
  have bound := Nat.mul_le_mul_left d (counts i)
  have baseBound := hbase i
  exact ⟨counts i, by unfold memory; omega, by unfold memory; omega, by unfold memory; omega⟩

theorem run_length (d : Nat) (error : Nat → Int) (s : State N)
    (calendar : List (Slot N)) :
    (run d error s calendar).fires.length = s.fires.length + calendar.length := by
  induction calendar generalizing s with
  | nil => simp [run]
  | cons p rest ih =>
    rw [run, ih]
    simp [advance, Nat.add_assoc, Nat.add_comm]

/-- Each listed contact refers to a probe strictly earlier in the calendar. -/
def CausalFrom (k : Nat) : List (Slot N) → Prop
  | [] => True
  | p :: rest => (∀ c ∈ p.contacts, c.source < k) ∧ CausalFrom (k + 1) rest

/-- A planned decision word and a routed-load interval at each slot.
The interval may use already certified FIRE decisions. Its upper end is
bounded by R, as is the sum of all listed contributions at that slot. -/
def Structural (d E R : Nat) (planned : Nat → Bool) (window : Nat → Nat × Nat) :
    State N → List (Slot N) → Prop
  | _, [] => True
  | s, p :: rest =>
    let k := s.fires.length
    let received := load (fun j => s.fires[j]?.getD false) p.contacts
    let free := p.offset + (d : Int) * s.writes p.cell
    (load (fun _ => true) p.contacts ≤ R ∧
      (window k).1 ≤ received ∧ received ≤ (window k).2 ∧ (window k).2 ≤ R) ∧
    (if planned k then 0 ≤ free + (window k).1 - E
      else free + (window k).2 + E < 0) ∧
    Structural d E R planned window (advance s p (planned k)) rest

/-- Read out the planned suffix starting at index k. -/
def plannedWord (planned : Nat → Bool) (k : Nat) : List (Slot N) → List Bool
  | [] => []
  | _ :: rest => planned k :: plannedWord planned (k + 1) rest

theorem structural_sound (d E R : Nat) {N : Nat}
    (planned : Nat → Bool) (window : Nat → Nat × Nat) (s : State N)
    (calendar : List (Slot N)) (check : Structural d E R planned window s calendar) :
    NominalMargins d (fun _ => -(E : Int)) (fun _ => E) s calendar ∧
    (run d (fun _ => 0) s calendar).fires = s.fires ++ plannedWord planned s.fires.length calendar := by
  induction calendar generalizing s with
  | nil => simp [NominalMargins, run, plannedWord]
  | cons p rest ih =>
    change _ ∧ _ ∧ _ at check
    obtain ⟨⟨_, lower, upper, _⟩, guard, tail⟩ := check
    cases plan : planned s.fires.length with
    | false =>
      rw [plan] at guard tail
      simp only [Bool.false_eq_true, ite_false] at guard
      have margin : cleanScore d s p + E < 0 := by
        unfold cleanScore
        omega
      have next : decision d s p 0 = false := by
        unfold decision
        exact decide_eq_false (by omega)
      obtain ⟨margins, word⟩ := ih _ tail
      constructor
      · change _ ∧ _
        rw [next]
        exact ⟨Or.inl ⟨by omega, margin⟩, margins⟩
      · rw [run, next, word]
        simp [plannedWord, plan, advance, List.append_assoc]
    | true =>
      rw [plan] at guard tail
      simp only [ite_true] at guard
      have margin : 0 ≤ cleanScore d s p - E := by
        unfold cleanScore
        omega
      have next : decision d s p 0 = true := by
        unfold decision
        exact decide_eq_true (by omega)
      obtain ⟨margins, word⟩ := ih _ tail
      constructor
      · change _ ∧ _
        rw [next]
        exact ⟨Or.inr ⟨by omega, by change 0 ≤ cleanScore d s p + -(E : Int); omega⟩, margins⟩
      · rw [run, next, word]
        simp [plannedWord, plan, advance, List.append_assoc]

/-- The full physical-load range [0, R] gives a simple local certificate.
A tighter causal window lets an earlier signal influence a certified output. -/
theorem full_load_window (d E R : Nat) {N : Nat} (s : State N) (p : Slot N)
    (maxLoad : load (fun _ => true) p.contacts ≤ R)
    (port : let free := p.offset + (d : Int) * s.writes p.cell
      free + R + E < 0 ∨ (E : Int) ≤ free) :
    HasRoom (cleanScore d s p) (-(E : Int)) E := by
  have bounded (fires : Nat → Bool) (contacts : List Contact) :
      load fires contacts ≤ load (fun _ => true) contacts := by
    induction contacts with
    | nil => exact Nat.le_refl _
    | cons c rest ih =>
      cases h : fires c.source <;> simp [load, h] <;> omega
  have upper := Nat.le_trans (bounded (fun j => s.fires[j]?.getD false) p.contacts) maxLoad
  dsimp at port
  unfold HasRoom cleanScore
  omega

theorem structural_episode (Q d B rail E R : Nat) {N : Nat}
    (calendar : List (Slot N)) (base : Fin N → Nat) (error : Nat → Int)
    (planned : Nat → Bool) (window : Nat → Nat × Nat)
    (hbase : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (budget : ∀ i, offers i calendar ≤ Q)
    (within : ∀ k, -(E : Int) ≤ error k ∧ error k ≤ (E : Int))
    (check : Structural d E R planned window (start N) calendar) :
    ∀ before after, calendar = before ++ after →
      let s := run d error (start N) before
      s = run d (fun _ => 0) (start N) before ∧
      total s ≤ Q * N ∧
      ∀ i, s.writes i ≤ Q ∧ base i ≤ memory d base s i ∧
        memory d base s i ≤ B + d * Q ∧ memory d base s i < rail :=
  certified_episode Q d B rail calendar base _ _ error hbase headroom budget within
    (structural_sound d E R planned window (start N) calendar check).1

end NetworkStability.RoutedCalendar
