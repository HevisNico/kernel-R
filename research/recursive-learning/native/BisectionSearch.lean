import SearchActions

/-! A binary search of every depth. For every `k`, a complete tree of
`2 ^ k - 1` questions separates the needs 1 to `2 ^ k`. The run asks `k`
of them, one at each depth. The nodes are numbered as in a heap: the
children of node `i` are `2 i + 1` after a yes and `2 i + 2` after a no. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-! ### The heap layout -/

/-- A search laid out as a heap. Cell `2 ν` is the probe of node `ν` and
cell `2 ν + 1` is its gate. The parent of node `κ > 0` is `(κ - 1) / 2`,
reached by a yes when `κ` is odd and by a no when `κ` is even. -/
def heapSearch (N : ℕ) (plan : Fin N → Question) : SearchLayout N (2 * N) where
  role := fun j =>
    if j.val % 2 = 0 then .probe ⟨j.val / 2, by have := j.isLt; omega⟩
    else .gate ⟨j.val / 2, by have := j.isLt; omega⟩
  probe := fun ν => ⟨2 * ν.val, by have := ν.isLt; omega⟩
  gate := fun ν => ⟨2 * ν.val + 1, by have := ν.isLt; omega⟩
  parent := fun κ =>
    if κ.val = 0 then none
    else some (⟨(κ.val - 1) / 2, by have := κ.isLt; omega⟩, decide (κ.val % 2 = 1))
  plan := plan
  probePort := fun _ => 0
  clockPort := fun _ => 0
  reportPort := fun _ => 1

theorem heap_role {N : ℕ} {plan : Fin N → Question} {j : Fin (2 * N)} {κ : Fin N}
    (h : (heapSearch N plan).role j = .probe κ ∨ (heapSearch N plan).role j = .gate κ) :
    κ.val = j.val / 2 := by
  simp only [heapSearch] at h
  split_ifs at h with even
  · rcases h with h | h
    · injection h with e; rw [← e]
    · cases h
  · rcases h with h | h
    · cases h
    · injection h with e; rw [← e]

theorem heap_parent {N : ℕ} {plan : Fin N → Question} {κ π : Fin N} {b : Bool}
    (h : (heapSearch N plan).parent κ = some (π, b)) :
    0 < κ.val ∧ π.val = (κ.val - 1) / 2 ∧ b = decide (κ.val % 2 = 1) := by
  simp only [heapSearch] at h
  split_ifs at h with root
  injection h with e
  injection e with e₁ e₂
  exact ⟨Nat.pos_of_ne_zero root, by rw [← e₁], e₂.symm⟩

/-- The heap layout is sound as soon as its dates are: each question is
spaced, its clock pulse follows its report window, and the question of a
child starts after the gate of its parent has answered. -/
theorem heapSearch_sound {N : ℕ} {plan : Fin N → Question} {T rest : ℝ} {horizon : Fin N → ℝ}
    (first : ∀ κ, T ≤ (plan κ).first)
    (spaced : ∀ κ, Spaced (plan κ).first (plan κ).dates ((plan κ).read - 1))
    (clock : ∀ κ, (plan κ).read + 1 < (plan κ).clock)
    (trained : ∀ κ, horizon κ ≤ (plan κ).clock) (wait : ∀ κ, (plan κ).clock + 22 ≤ rest)
    (after : ∀ κ π : Fin N, 0 < κ.val → π.val = (κ.val - 1) / 2 →
      (plan π).clock + 1 < (plan κ).first) :
    (heapSearch N plan).Sound T rest horizon where
  roleProbe := by
    intro κ
    simp only [heapSearch]
    split_ifs with even
    · congr 1
      exact Fin.ext (by show 2 * κ.val / 2 = κ.val; omega)
    · omega
  roleGate := by
    intro κ
    simp only [heapSearch]
    split_ifs with even
    · omega
    · congr 1
      exact Fin.ext (by show (2 * κ.val + 1) / 2 = κ.val; omega)
  reportOrder := by
    intro j κ h
    have node := heap_role (Or.inr h)
    have odd : j.val % 2 = 1 := by
      simp only [heapSearch] at h
      split_ifs at h with even
      omega
    show 2 * κ.val < j.val
    omega
  parentOrder := by
    intro j κ π b role hp
    have node := heap_role role
    obtain ⟨pos, up, _⟩ := heap_parent hp
    constructor
    · show 2 * π.val < j.val
      omega
    · show 2 * π.val + 1 < j.val
      omega
  first := first
  spaced := spaced
  clock := clock
  trained := trained
  wait := wait
  after := by
    intro κ π b hp
    obtain ⟨pos, up, _⟩ := heap_parent hp
    exact after κ π pos up

/-! ### The bisection of the needs -/

/-- The exponent of node `i`: its interval of needs has `2 ^ exOf k i`
elements. The root has the exponent `k`, and each level loses one. -/
def exOf (k : ℕ) : ℕ → ℕ
  | 0 => k
  | i + 1 => exOf k (i / 2) - 1
termination_by i => i
decreasing_by omega

/-- The lower end of the interval of node `i`: the node is reached for
the needs `m` with `loOf k i < m ≤ loOf k i + 2 ^ exOf k i`. A yes keeps
the lower half and a no keeps the upper half. -/
def loOf (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
    if i % 2 = 0 then loOf k (i / 2) else loOf k (i / 2) + 2 ^ (exOf k (i / 2) - 1)
termination_by i => i
decreasing_by all_goals omega

/-- The count of the question of node `i`: the middle of its interval. -/
def midOf (k i : ℕ) : ℕ := loOf k i + 2 ^ (exOf k i - 1)

theorem exOf_succ (k i : ℕ) : exOf k (i + 1) = exOf k (i / 2) - 1 := by
  rw [exOf]

theorem loOf_succ (k i : ℕ) : loOf k (i + 1) =
    if i % 2 = 0 then loOf k (i / 2) else loOf k (i / 2) + 2 ^ (exOf k (i / 2) - 1) := by
  rw [loOf]

/-- Inside the tree every interval has at least two needs and lies below
`2 ^ k`. -/
theorem bisect_invariant (k : ℕ) : ∀ i, i + 1 < 2 ^ k →
    2 ^ k ≤ (i + 1) * 2 ^ exOf k i ∧ loOf k i + 2 ^ exOf k i ≤ 2 ^ k ∧ 1 ≤ exOf k i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro inside
    have positive (e : ℕ) (big : 2 ^ k ≤ (i + 1) * 2 ^ e) : 1 ≤ e := by
      by_contra h
      have zero : e = 0 := by omega
      rw [zero] at big
      omega
    rcases i with _ | i
    · have root : exOf k 0 = k := by rw [exOf]
      have low : loOf k 0 = 0 := by rw [loOf]
      rw [root, low]
      exact ⟨by omega, by omega, positive k (by omega)⟩
    · obtain ⟨big, top, one⟩ := ih (i / 2) (by omega) (by omega)
      obtain ⟨h, eh⟩ : ∃ h, exOf k (i / 2) = h + 1 := ⟨exOf k (i / 2) - 1, by omega⟩
      rw [eh] at big top
      have double : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
      rw [double] at big top
      have ex : exOf k (i + 1) = h := by rw [exOf_succ, eh]; rfl
      have grow : 2 ^ k ≤ (i + 1 + 1) * 2 ^ h := by
        have wide : (i / 2 + 1) * (2 * 2 ^ h) ≤ (i + 1 + 1) * 2 ^ h := by
          have step : 2 * (i / 2 + 1) ≤ i + 1 + 1 := by omega
          calc (i / 2 + 1) * (2 * 2 ^ h) = 2 * (i / 2 + 1) * 2 ^ h := by ring
            _ ≤ (i + 1 + 1) * 2 ^ h := Nat.mul_le_mul_right _ step
        omega
      rw [ex]
      refine ⟨grow, ?_, positive h grow⟩
      rw [loOf_succ, eh, Nat.add_sub_cancel]
      split_ifs <;> omega

theorem exOf_le (k : ℕ) : ∀ i, exOf k i ≤ k := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases i with _ | i
    · rw [exOf]
    · have up := ih (i / 2) (by omega)
      rw [exOf_succ]
      omega

/-- The interval of a child is one half of the interval of its parent:
the lower half after a yes, the upper half after a no. -/
theorem bisect_child (k m i : ℕ) (inside : i / 2 + 1 < 2 ^ k) :
    (loOf k (i + 1) < m ∧ m ≤ loOf k (i + 1) + 2 ^ exOf k (i + 1)) ↔
      (loOf k (i / 2) < m ∧ m ≤ loOf k (i / 2) + 2 ^ exOf k (i / 2)) ∧
        (if i % 2 = 0 then m ≤ midOf k (i / 2) else midOf k (i / 2) < m) := by
  obtain ⟨_, _, one⟩ := bisect_invariant k (i / 2) inside
  obtain ⟨h, eh⟩ : ∃ h, exOf k (i / 2) = h + 1 := ⟨exOf k (i / 2) - 1, by omega⟩
  have double : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
  unfold midOf
  rw [loOf_succ, exOf_succ, eh, Nat.add_sub_cancel, double]
  split_ifs <;> omega

/-! ### The dates of the questions -/

/-- The length of one level: room for `2 ^ k` training pulses, the read
pulse and the clock pulse. -/
noncomputable def bisectStep (k : ℕ) : ℝ := 22 * 2 ^ k + 26

/-- The first pulse of the question of node `i`. All the nodes of one
depth share their dates. -/
noncomputable def bisectFirst (k i : ℕ) : ℝ := 1000 + ((k - exOf k i : ℕ) : ℝ) * bisectStep k

/-- The question of node `i`: `midOf k i` training pulses, 22 units
apart, then the read pulse and the clock pulse. -/
noncomputable def bisectPlan (k i : ℕ) : Question where
  first := bisectFirst k i
  dates := train (bisectFirst k i) (midOf k i - 1)
  read := bisectFirst k i + 22 * midOf k i + 1
  clock := bisectFirst k i + 22 * midOf k i + 3

theorem midOf_bounds (k i : ℕ) (inside : i + 1 < 2 ^ k) : 1 ≤ midOf k i ∧ midOf k i ≤ 2 ^ k := by
  obtain ⟨_, top, one⟩ := bisect_invariant k i inside
  obtain ⟨h, eh⟩ : ∃ h, exOf k i = h + 1 := ⟨exOf k i - 1, by omega⟩
  have double : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
  have pos : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  unfold midOf
  rw [eh, Nat.add_sub_cancel]
  rw [eh, double] at top
  omega

theorem bisect_count (k i : ℕ) (inside : i + 1 < 2 ^ k) : (bisectPlan k i).count = midOf k i := by
  have one := (midOf_bounds k i inside).1
  show (train (bisectFirst k i) (midOf k i - 1)).length + 1 = midOf k i
  rw [train_length]
  omega

theorem bisectStep_pos (k : ℕ) : 0 < bisectStep k := by
  unfold bisectStep
  positivity

theorem bisectFirst_ge (k i : ℕ) : 1000 ≤ bisectFirst k i := by
  unfold bisectFirst
  have step := (bisectStep_pos k).le
  have levels : (0 : ℝ) ≤ ((k - exOf k i : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg levels step]

theorem mid_cast (k i : ℕ) (inside : i + 1 < 2 ^ k) :
    (1 : ℝ) ≤ midOf k i ∧ (midOf k i : ℝ) ≤ 2 ^ k := by
  obtain ⟨one, top⟩ := midOf_bounds k i inside
  exact ⟨by exact_mod_cast one, by exact_mod_cast top⟩

/-- The question of a child starts after the gate of its parent has
answered. -/
theorem bisect_after (k i : ℕ) (inside : i + 1 + 1 < 2 ^ k) :
    (bisectPlan k (i / 2)).clock + 1 < (bisectPlan k (i + 1)).first := by
  have parent : i / 2 + 1 < 2 ^ k := by omega
  obtain ⟨_, _, one⟩ := bisect_invariant k (i / 2) parent
  have top := exOf_le k (i / 2)
  have level : k - exOf k (i + 1) = (k - exOf k (i / 2)) + 1 := by
    rw [exOf_succ]
    omega
  obtain ⟨_, mid⟩ := mid_cast k (i / 2) parent
  show bisectFirst k (i / 2) + 22 * midOf k (i / 2) + 3 + 1 < bisectFirst k (i + 1)
  unfold bisectFirst
  rw [level]
  push_cast
  unfold bisectStep
  nlinarith

/-- The binary search of depth `k`: a heap of `2 ^ k - 1` questions. -/
noncomputable def bisectSearch (k : ℕ) : SearchLayout (2 ^ k - 1) (2 * (2 ^ k - 1)) :=
  heapSearch (2 ^ k - 1) (fun κ => bisectPlan k κ.val)

theorem bisectSearch_sound (k : ℕ) {horizon : Fin (2 ^ k - 1) → ℝ}
    (trained : ∀ κ, horizon κ ≤ 1000) :
    (bisectSearch k).Sound 0 (1000 + k * bisectStep k) horizon := by
  have inside (κ : Fin (2 ^ k - 1)) : κ.val + 1 < 2 ^ k := by have := κ.isLt; omega
  apply heapSearch_sound
  · intro κ
    show (0 : ℝ) ≤ bisectFirst k κ.val
    linarith [bisectFirst_ge k κ.val]
  · intro κ
    obtain ⟨one, _⟩ := midOf_bounds k κ.val (inside κ)
    show Spaced (bisectFirst k κ.val) (train (bisectFirst k κ.val) (midOf k κ.val - 1))
      (bisectFirst k κ.val + 22 * midOf k κ.val + 1 - 1)
    apply train_spaced
    rw [Nat.cast_pred one]
    linarith
  · intro κ
    show bisectFirst k κ.val + 22 * midOf k κ.val + 1 + 1 <
      bisectFirst k κ.val + 22 * midOf k κ.val + 3
    linarith
  · intro κ
    obtain ⟨one, _⟩ := mid_cast k κ.val (inside κ)
    show horizon κ ≤ bisectFirst k κ.val + 22 * midOf k κ.val + 3
    linarith [trained κ, bisectFirst_ge k κ.val]
  · intro κ
    obtain ⟨_, _, one⟩ := bisect_invariant k κ.val (inside κ)
    obtain ⟨_, mid⟩ := mid_cast k κ.val (inside κ)
    have kPos : 1 ≤ k := by
      rcases k with _ | k
      · have := inside κ; simp at this
      · omega
    have level : ((k - exOf k κ.val : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
      have h : k - exOf k κ.val ≤ k - 1 := by omega
      have c : ((k - exOf k κ.val : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_pred kPos] at c
      exact c
    show bisectFirst k κ.val + 22 * midOf k κ.val + 3 + 22 ≤ 1000 + k * bisectStep k
    unfold bisectFirst
    have step := bisectStep_pos k
    have scaled := mul_le_mul_of_nonneg_right level step.le
    unfold bisectStep at scaled step ⊢
    nlinarith
  · intro κ π pos up
    obtain ⟨i, hi⟩ : ∃ i, κ.val = i + 1 := ⟨κ.val - 1, by omega⟩
    have parent : π.val = i / 2 := by rw [up, hi]; rfl
    show (bisectPlan k π.val).clock + 1 < (bisectPlan k κ.val).first
    rw [parent, hi]
    exact bisect_after k i (by have := inside κ; omega)

/-- The nodes reached for the need `m`: those whose interval holds it. -/
def bisectReached (k m : ℕ) (κ : Fin (2 ^ k - 1)) : Bool :=
  decide (loOf k κ.val < m ∧ m ≤ loOf k κ.val + 2 ^ exOf k κ.val)

theorem bisectSearch_consistent (k : ℕ) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) :
    (bisectSearch k).Consistent (bisectReached k m) (fun _ => m) := by
  intro κ
  have inside (ν : Fin (2 ^ k - 1)) : ν.val + 1 < 2 ^ k := by have := ν.isLt; omega
  rcases hκ : κ.val with _ | i
  · have root : (bisectSearch k).parent κ = none := by
      simp [bisectSearch, heapSearch, hκ]
    rw [root]
    have ex : exOf k 0 = k := by rw [exOf]
    have low : loOf k 0 = 0 := by rw [loOf]
    simp only [bisectReached, hκ, ex, low]
    simpa using ⟨by omega, hi⟩
  · have lt : i / 2 < 2 ^ k - 1 := by have := κ.isLt; omega
    have up : (bisectSearch k).parent κ =
        some (⟨i / 2, lt⟩, decide ((i + 1) % 2 = 1)) := by
      simp [bisectSearch, heapSearch, hκ]
    rw [up]
    have count : ((bisectSearch k).plan ⟨i / 2, lt⟩).count = midOf k (i / 2) :=
      bisect_count k (i / 2) (by omega)
    have child := bisect_child k m i (by omega)
    simp only [bisectReached, hκ, count]
    rw [Bool.eq_iff_iff]
    by_cases par : i % 2 = 0
    · have odd : (i + 1) % 2 = 1 := by omega
      simp only [par, ite_true] at child
      simp only [odd, decide_true, ite_true, Bool.and_eq_true, decide_eq_true_eq]
      exact child
    · have even : ¬ (i + 1) % 2 = 1 := by omega
      simp only [par, ite_false] at child
      simp only [even, decide_false, Bool.false_eq_true, ite_false, Bool.and_eq_true,
        decide_eq_true_eq]
      exact child

/-! ### The `k` questions that are asked -/

/-- The node asked at depth `t` for the need `m`. -/
def bisectPath (k m : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
    if m ≤ midOf k (bisectPath k m t) then 2 * bisectPath k m t + 1
    else 2 * bisectPath k m t + 2

theorem bisectPath_lt (k m t : ℕ) : bisectPath k m t < bisectPath k m (t + 1) := by
  show bisectPath k m t < if m ≤ midOf k (bisectPath k m t) then 2 * bisectPath k m t + 1
    else 2 * bisectPath k m t + 2
  split_ifs <;> omega

/-- The node asked at depth `t < k` is in the tree, at depth `t`, and
its interval holds the need. -/
theorem bisectPath_spec (k : ℕ) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) : ∀ t, t < k →
    bisectPath k m t + 1 < 2 ^ (t + 1) ∧ exOf k (bisectPath k m t) = k - t ∧
      (loOf k (bisectPath k m t) < m ∧
        m ≤ loOf k (bisectPath k m t) + 2 ^ exOf k (bisectPath k m t)) := by
  intro t
  induction t with
  | zero =>
    intro _
    have ex : exOf k 0 = k := by rw [exOf]
    have low : loOf k 0 = 0 := by rw [loOf]
    show 0 + 1 < 2 ^ (0 + 1) ∧ exOf k 0 = k - 0 ∧ (loOf k 0 < m ∧ m ≤ loOf k 0 + 2 ^ exOf k 0)
    rw [ex, low]
    exact ⟨by norm_num, rfl, by omega, by omega⟩
  | succ t ih =>
    intro ht
    obtain ⟨bound, level, reached⟩ := ih (by omega)
    have power : 2 ^ (t + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have double : 2 ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by rw [pow_succ]; ring
    set q := bisectPath k m t with hq
    by_cases yes : m ≤ midOf k q
    · have next : bisectPath k m (t + 1) = 2 * q + 1 := by
        show (if m ≤ midOf k q then 2 * q + 1 else 2 * q + 2) = _
        simp only [yes, reduceIte]
      have half : 2 * q / 2 = q := by omega
      have child := bisect_child k m (2 * q) (by rw [half]; omega)
      rw [half] at child
      rw [next]
      refine ⟨by omega, by rw [exOf_succ, half]; omega, child.mpr ⟨reached, ?_⟩⟩
      have par : 2 * q % 2 = 0 := by omega
      simp only [par, reduceIte]
      exact yes
    · have next : bisectPath k m (t + 1) = 2 * q + 1 + 1 := by
        show (if m ≤ midOf k q then 2 * q + 1 else 2 * q + 2) = _
        simp only [yes, reduceIte]
      have half : (2 * q + 1) / 2 = q := by omega
      have child := bisect_child k m (2 * q + 1) (by rw [half]; omega)
      rw [half] at child
      rw [next]
      refine ⟨by omega, by rw [exOf_succ, half]; omega, child.mpr ⟨reached, ?_⟩⟩
      have par : ¬ (2 * q + 1) % 2 = 0 := by omega
      simp only [par, reduceIte]
      omega

/-- The nodes whose interval holds the need are the `k` nodes of the
path, one at each depth. -/
theorem bisect_reached_iff (k : ℕ) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) :
    ∀ i, i + 1 < 2 ^ k →
      ((loOf k i < m ∧ m ≤ loOf k i + 2 ^ exOf k i) ↔ ∃ t, t < k ∧ i = bisectPath k m t) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro inside
    constructor
    · intro reached
      rcases i with _ | i
      · have kPos : 0 < k := by
          rcases k with _ | k
          · simp at inside
          · omega
        exact ⟨0, kPos, rfl⟩
      · have child := (bisect_child k m i (by omega)).mp reached
        obtain ⟨t, ht, here⟩ := (ih (i / 2) (by omega) (by omega)).mp child.1
        obtain ⟨_, level, _⟩ := bisectPath_spec k lo hi t ht
        obtain ⟨_, _, one⟩ := bisect_invariant k (i + 1) inside
        rw [exOf_succ, here, level] at one
        refine ⟨t + 1, by omega, ?_⟩
        show i + 1 = if m ≤ midOf k (bisectPath k m t) then 2 * bisectPath k m t + 1
          else 2 * bisectPath k m t + 2
        rw [← here]
        have answer := child.2
        split_ifs at answer with par
        · simp only [answer, reduceIte]
          omega
        · have no : ¬ m ≤ midOf k (i / 2) := by omega
          simp only [no, reduceIte]
          omega
    · rintro ⟨t, ht, rfl⟩
      exact (bisectPath_spec k lo hi t ht).2.2

/-- The last question gives the need. The node asked at depth `k - 1`
has an interval of two needs: its probe answers yes exactly for the
first one and its gate answers no exactly for the second one. -/
theorem bisect_last (k : ℕ) (kPos : 0 < k) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) (q : ℕ)
    (last : q = bisectPath k m (k - 1)) :
    ((loOf k q < m ∧ m ≤ midOf k q) ↔ m = loOf k q + 1) ∧
      ((midOf k q < m ∧ m ≤ loOf k q + 2 ^ exOf k q) ↔ m = loOf k q + 2) := by
  obtain ⟨_, level, reached⟩ := bisectPath_spec k lo hi (k - 1) (by omega)
  rw [← last] at level reached
  have leaf : exOf k q = 1 := by omega
  unfold midOf
  rw [leaf] at reached ⊢
  norm_num at reached ⊢
  constructor <;> constructor <;> intro h <;> omega

/-! ### The search of depth `k` -/

/-- A binary search of every depth. For every `k ≥ 1`, a tree of
`2 ^ k - 1` questions is built with `2 (2 ^ k - 1)` cells. Every probe
has the need `m`, between 1 and `2 ^ k`, with its own parameters, start
gain, dose and FIRE level. Every gate is trained before the date 1000.
The network has a complete run, and in every complete run:

- the probe of node `κ` fires in its report window exactly when `m`
  lies in the lower half of its interval;
- the gate of node `κ` fires late exactly when `m` lies in the upper
  half of its interval;
- a probe outside the `k` nodes of the path `bisectPath k m` receives no
  question: it never fires and its gain does not move.

At the last depth the intervals have two needs, so the last answer gives
`m`. The FIRE dates and the final values are the same in every complete
run. -/
theorem bisection_search (k : ℕ) (kPos : 0 < k) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) {ε : ℝ}
    {horizon : Fin (2 ^ k - 1) → ℝ} {θp θg : Fin (2 ^ k - 1) → Fin 1 → Parameters}
    {sp sg : Fin (2 ^ k - 1) → Snapshot 1}
    {up lp levelp u₁ l₁ u₂ l₂ levelg : Fin (2 ^ k - 1) → ℝ}
    {dates₁ dates₂ : Fin (2 ^ k - 1) → List ℝ} {middle : Fin (2 ^ k - 1) → ℝ}
    {r₁ r₂ : Fin (2 ^ k - 1) → ℕ}
    (probes : ∀ κ, ProbeCell (θp κ) ε (sp κ) 0 (up κ) (lp κ) (levelp κ) m)
    (gates : ∀ κ, OpenCell (θg κ) ε (sg κ) 0 1 (u₁ κ) (l₁ κ) (u₂ κ) (l₂ κ) (levelg κ)
      (dates₁ κ) (dates₂ κ) (middle κ) (horizon κ) (r₁ κ) (r₂ κ))
    (trained : ∀ κ, horizon κ ≤ 1000)
    (startP : ∀ κ, (sp κ).time = 0) (startG : ∀ κ, (sg κ).time = 0) :
    ∃ (dates : Fin (2 * (2 ^ k - 1)) → List ℝ) (u : Fin (2 * (2 ^ k - 1)) → Snapshot 1),
      (∀ κ : Fin (2 ^ k - 1),
        Signal ((bisectPlan k κ.val).read - 1) ((bisectPlan k κ.val).read + 1)
          (dates ((bisectSearch k).probe κ))
          (decide (loOf k κ.val < m ∧ m ≤ midOf k κ.val))) ∧
      (∀ κ : Fin (2 ^ k - 1),
        Signal ((bisectPlan k κ.val).clock + 71 / 200) ((bisectPlan k κ.val).clock + 1)
          (dates ((bisectSearch k).gate κ))
          (decide (midOf k κ.val < m ∧ m ≤ loOf k κ.val + 2 ^ exOf k κ.val))) ∧
      (∀ κ : Fin (2 ^ k - 1), (∀ t, t < k → κ.val ≠ bisectPath k m t) →
        dates ((bisectSearch k).probe κ) = [] ∧
        (u ((bisectSearch k).probe κ)).x 0 (.z 0) = (sp κ).x 0 (.z 0)) ∧
      (∃ ref : ParameterExecution
        (familyParameters (fun j => SearchLayout.pick θp θg ((bisectSearch k).role j)))
        (signalRoute (bisectSearch k).lo (bisectSearch k).hi (bisectSearch k).inputs)
        (Snapshot.family 0 ((bisectSearch k).start sp sg))
        (Snapshot.family (1000 + k * bisectStep k) u),
        ParameterCompleteThrough ref (1000 + k * bisectStep k)) ∧
      ∀ {w : Snapshot (2 * (2 ^ k - 1))} (ex : ParameterExecution
        (familyParameters (fun j => SearchLayout.pick θp θg ((bisectSearch k).role j)))
        (signalRoute (bisectSearch k).lo (bisectSearch k).hi (bisectSearch k).inputs)
        (Snapshot.family 0 ((bisectSearch k).start sp sg)) w),
        ParameterCompleteThrough ex (1000 + k * bisectStep k) →
        (∀ i, ex.emissionTimes i = dates i) ∧ ∀ i c, w.x i c = (u i).x 0 c := by
  have two : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) kPos
  have inside (κ : Fin (2 ^ k - 1)) : κ.val + 1 < 2 ^ k := by have := κ.isLt; omega
  obtain ⟨dates, u, yes, no, silent, gains, _, ref, all⟩ :=
    trained_search (by omega : 0 < 2 * (2 ^ k - 1)) (bisectSearch k) (bisectSearch_sound k trained)
      (bisectSearch_consistent k lo hi) probes gates startP startG
  have count (κ : Fin (2 ^ k - 1)) : ((bisectSearch k).plan κ).count = midOf k κ.val :=
    bisect_count k κ.val (inside κ)
  have half (κ : Fin (2 ^ k - 1)) : midOf k κ.val ≤ loOf k κ.val + 2 ^ exOf k κ.val := by
    unfold midOf
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.sub_le (exOf k κ.val) 1)
    omega
  refine ⟨dates, u, fun κ => ?_, fun κ => ?_, fun κ off => ?_, ref, all⟩
  · have h := yes κ
    have bit : (bisectReached k m κ && decide (m ≤ ((bisectSearch k).plan κ).count)) =
        decide (loOf k κ.val < m ∧ m ≤ midOf k κ.val) := by
      rw [count, Bool.eq_iff_iff]
      simp only [bisectReached, Bool.and_eq_true, decide_eq_true_eq]
      have := half κ
      constructor <;> intro h <;> omega
    rw [bit] at h
    exact h
  · have h := no κ
    have bit : (bisectReached k m κ && decide (((bisectSearch k).plan κ).count < m)) =
        decide (midOf k κ.val < m ∧ m ≤ loOf k κ.val + 2 ^ exOf k κ.val) := by
      rw [count, Bool.eq_iff_iff]
      simp only [bisectReached, Bool.and_eq_true, decide_eq_true_eq]
      have : loOf k κ.val ≤ midOf k κ.val := Nat.le_add_right _ _
      constructor <;> intro h <;> omega
    rw [bit] at h
    exact h
  · have away : bisectReached k m κ = false := by
      by_contra h
      have reached : loOf k κ.val < m ∧ m ≤ loOf k κ.val + 2 ^ exOf k κ.val := by
        simpa [bisectReached] using h
      obtain ⟨t, ht, here⟩ := (bisect_reached_iff k lo hi κ.val (inside κ)).mp reached
      exact off t ht here
    have gain := gains κ
    rw [away] at gain
    simp only [Bool.false_eq_true, reduceIte, Nat.cast_zero, zero_mul, add_zero] at gain
    exact ⟨silent κ away, gain⟩

/-- The search of depth `k` with explicit cells, for every `k ≥ 1`. Each
of the `2 ^ k - 1` probes has its own start gain, anywhere within 3/125
of the centre of the band of need `m`. The conclusions are those of
`bisection_search`. -/
theorem bisection_search_witness (k : ℕ) (kPos : 0 < k) (m : ℕ) (lo : 1 ≤ m) (hi : m ≤ 2 ^ k)
    (z : Fin (2 ^ k - 1) → ℝ) (band : ∀ κ, |z κ - needCentre 1 (1 / 20) m| ≤ 3 / 125) :
    ∃ (dates : Fin (2 * (2 ^ k - 1)) → List ℝ) (u : Fin (2 * (2 ^ k - 1)) → Snapshot 1),
      (∀ κ : Fin (2 ^ k - 1),
        Signal ((bisectPlan k κ.val).read - 1) ((bisectPlan k κ.val).read + 1)
          (dates ((bisectSearch k).probe κ))
          (decide (loOf k κ.val < m ∧ m ≤ midOf k κ.val))) ∧
      (∀ κ : Fin (2 ^ k - 1),
        Signal ((bisectPlan k κ.val).clock + 71 / 200) ((bisectPlan k κ.val).clock + 1)
          (dates ((bisectSearch k).gate κ))
          (decide (midOf k κ.val < m ∧ m ≤ loOf k κ.val + 2 ^ exOf k κ.val))) ∧
      (∀ κ : Fin (2 ^ k - 1), (∀ t, t < k → κ.val ≠ bisectPath k m t) →
        dates ((bisectSearch k).probe κ) = [] ∧
        (u ((bisectSearch k).probe κ)).x 0 (.z 0) = z κ) ∧
      (∃ ref : ParameterExecution
        (familyParameters (fun (_ : Fin (2 * (2 ^ k - 1))) (_ : Fin 1) => witnessParameters))
        (signalRoute (bisectSearch k).lo (bisectSearch k).hi (bisectSearch k).inputs)
        (Snapshot.family 0 ((bisectSearch k).start (fun κ => probeAt (z κ))
          (fun _ => witnessSource)))
        (Snapshot.family (1000 + k * bisectStep k) u),
        ParameterCompleteThrough ref (1000 + k * bisectStep k)) ∧
      ∀ {w : Snapshot (2 * (2 ^ k - 1))} (ex : ParameterExecution
        (familyParameters (fun (_ : Fin (2 * (2 ^ k - 1))) (_ : Fin 1) => witnessParameters))
        (signalRoute (bisectSearch k).lo (bisectSearch k).hi (bisectSearch k).inputs)
        (Snapshot.family 0 ((bisectSearch k).start (fun κ => probeAt (z κ))
          (fun _ => witnessSource))) w),
        ParameterCompleteThrough ex (1000 + k * bisectStep k) →
        (∀ i, ex.emissionTimes i = dates i) ∧ ∀ i c, w.x i c = (u i).x 0 c := by
  obtain ⟨dates, u, yes, no, off, ref, all⟩ :=
    bisection_search k kPos lo hi (θp := fun _ _ => witnessParameters)
      (θg := fun _ _ => witnessParameters) (sp := fun κ => probeAt (z κ))
      (sg := fun _ => witnessSource) (horizon := fun _ => 968)
      (fun κ => probeCell_band m (band κ)) (fun _ => openCell_witness)
      (fun _ => by norm_num) (fun _ => rfl) (fun _ => rfl)
  have same : (fun j => SearchLayout.pick
      (fun (_ : Fin (2 ^ k - 1)) (_ : Fin 1) => witnessParameters)
      (fun _ _ => witnessParameters) ((bisectSearch k).role j)) =
      fun (_ : Fin (2 * (2 ^ k - 1))) (_ : Fin 1) => witnessParameters := by
    funext j
    cases (bisectSearch k).role j <;> rfl
  rw [same] at ref all
  exact ⟨dates, u, yes, no, off, ref, all⟩

end RecursiveLearning.Native
