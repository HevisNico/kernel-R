import KernelR.Chain.Packets

/-! Universal finite-chain composition from explicitly supplied local contracts.
There is no bounded enumeration of N, and no hypothesis that devices are equal.
The missing hybrid-to-contract refinement is not asserted by these theorems. -/
namespace KernelR.Chain

def prefixLength (j : ℕ) : ℕ := 3 + 2 * j
def tailLength (K j : ℕ) : ℕ := K - 8 - 4 * j

def pathJitter (σ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => pathJitter σ j + σ j

theorem pathJitter_nonneg (σ : ℕ → ℝ) (hσ : ∀ j, 0 ≤ σ j) :
    ∀ j, 0 ≤ pathJitter σ j := by
  intro j
  induction j with
  | zero => simp [pathJitter]
  | succ j ih => exact add_nonneg ih (hσ j)

theorem pathJitter_mono (σ : ℕ → ℝ) (hσ : ∀ j, 0 ≤ σ j)
    {i j : ℕ} (h : i ≤ j) : pathJitter σ i ≤ pathJitter σ j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases hij : i ≤ j
    · exact (ih hij).trans (by
        rw [pathJitter]
        linarith [hσ j])
    · have hi : i = j + 1 := by omega
      subst i
      exact le_rfl

theorem tail_budget {N K j : ℕ} (hN : 0 < N) (hK : 4 * N + 12 ≤ K)
    (hj : j < N) : 8 ≤ tailLength K j := by
  unfold tailLength
  omega

theorem relay_input_budget {N K j : ℕ} (hK : 4 * N + 12 ≤ K)
    (hj : j + 1 < N) : 12 ≤ tailLength K j := by
  unfold tailLength
  omega

theorem prefix_step (j : ℕ) : prefixLength (j + 1) = prefixLength j + 2 := by
  unfold prefixLength
  omega

theorem tail_step (K j : ℕ) : tailLength K (j + 1) = tailLength K j - 4 := by
  unfold tailLength
  omega

theorem node_outputs {N K j : ℕ} (hK : 4 * N + 12 ≤ K) (hj : j < N) :
    prefixLength j + tailLength K j = K - 5 - 2 * j := by
  unfold prefixLength tailLength
  omega

theorem root_outputs {N K : ℕ} (hN : 0 < N) (hK : 4 * N + 12 ≤ K) :
    prefixLength (N - 1) + tailLength K (N - 1) = K - 2 * N - 3 := by
  unfold prefixLength tailLength
  omega

theorem surplus_tail {N R j : ℕ} (hj : j < N) :
    tailLength (4 * N + 12 + R) j = 8 + 4 * (N - 1 - j) + R := by
  unfold tailLength
  omega

theorem root_tail {N R : ℕ} (hN : 0 < N) :
    tailLength (4 * N + 12 + R) (N - 1) = 8 + R := by
  unfold tailLength
  omega

/-- P j m L J says the actual output of physical cell j has that packet contract.
The leaf and relay refinements are premises, not project axioms or admitted proofs. -/
theorem compose_every_finite_chain
    (P : ℕ → ℕ → ℕ → ℝ → Prop) (σ : ℕ → ℝ)
    (N K : ℕ) (hN : 0 < N) (hK : 4 * N + 12 ≤ K)
    (hσ : ∀ j, 0 ≤ σ j) (budget : pathJitter σ (N - 1) ≤ 3 / 20)
    (leaf : P 0 3 (K - 8) 0)
    (step : ∀ j m L J, j + 1 < N → 5 ≤ L → J + σ j ≤ 3 / 20 →
      P j m L J → P (j + 1) (m + 2) (L - 4) (J + σ j)) :
    ∀ j, j < N → P j (prefixLength j) (tailLength K j) (pathJitter σ j) := by
  intro j
  induction j with
  | zero =>
    intro _
    simpa [prefixLength, tailLength, pathJitter] using leaf
  | succ j ih =>
    intro hj
    have hj' : j < N := by omega
    have hL : 5 ≤ tailLength K j := by
      have := relay_input_budget hK hj
      omega
    have hJ : pathJitter σ j + σ j ≤ 3 / 20 := by
      have hm := pathJitter_mono σ hσ (show j + 1 ≤ N - 1 by omega)
      change pathJitter σ j + σ j ≤ pathJitter σ (N - 1) at hm
      exact hm.trans budget
    simpa only [prefix_step, tail_step, pathJitter] using
      step j (prefixLength j) (tailLength K j) (pathJitter σ j) hj hL hJ (ih hj')

theorem root_contract
    (P : ℕ → ℕ → ℕ → ℝ → Prop) (σ : ℕ → ℝ)
    (N K : ℕ) (hN : 0 < N) (hK : 4 * N + 12 ≤ K)
    (hσ : ∀ j, 0 ≤ σ j) (budget : pathJitter σ (N - 1) ≤ 3 / 20)
    (leaf : P 0 3 (K - 8) 0)
    (step : ∀ j m L J, j + 1 < N → 5 ≤ L → J + σ j ≤ 3 / 20 →
      P j m L J → P (j + 1) (m + 2) (L - 4) (J + σ j)) :
    P (N - 1) (prefixLength (N - 1)) (tailLength K (N - 1))
      (pathJitter σ (N - 1)) ∧ 8 ≤ tailLength K (N - 1) := by
  exact ⟨compose_every_finite_chain P σ N K hN hK hσ budget leaf step
    (N - 1) (by omega), tail_budget hN hK (by omega)⟩

def traffic (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => traffic K n + (K - 5 - 2 * n)

theorem traffic_closed_form {N K : ℕ} (hK : 4 * N + 12 ≤ K) :
    traffic K N = N * (K - N - 4) := by
  induction N with
  | zero => simp [traffic]
  | succ n ih =>
    have hk : 4 * n + 12 ≤ K := by omega
    have h₁ : K - n - 4 = K - (n + 1) - 4 + 1 := by omega
    have h₂ : K - 5 - 2 * n + n = K - (n + 1) - 4 := by omega
    rw [traffic, ih hk, h₁]
    nlinarith

theorem traffic_sum (K N : ℕ) :
    traffic K N = (Finset.range N).sum (fun j => K - 5 - 2 * j) := by
  induction N with
  | zero => simp [traffic]
  | succ n ih => simp [traffic, Finset.sum_range_succ, ih]

theorem total_emissions_sum {N K : ℕ} (hK : 4 * N + 12 ≤ K) :
    (Finset.range N).sum (fun j => prefixLength j + tailLength K j) =
      N * (K - N - 4) := by
  calc
    (Finset.range N).sum (fun j => prefixLength j + tailLength K j) =
        (Finset.range N).sum (fun j => K - 5 - 2 * j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact node_outputs hK (Finset.mem_range.mp hj)
    _ = traffic K N := (traffic_sum K N).symm
    _ = N * (K - N - 4) := traffic_closed_form hK

theorem traffic_at_minimum (N : ℕ) :
    traffic (4 * N + 12) N = 3 * N * N + 8 * N := by
  rw [traffic_closed_form (by omega)]
  have h : 4 * N + 12 - N - 4 = 3 * N + 8 := by omega
  rw [h]
  ring

theorem constant_jitter (s : ℝ) (n : ℕ) :
    pathJitter (fun _ => s) n = n * s := by
  induction n with
  | zero => simp [pathJitter]
  | succ n ih => simp [pathJitter, ih, Nat.cast_add, Nat.cast_one]; ring

theorem fixed_delays_any_depth (n : ℕ) :
    pathJitter (fun _ => (0 : ℝ)) n = 0 := by rw [constant_jitter]; ring

theorem full_jitter_iff_four_cells {N : ℕ} (hN : 0 < N) :
    pathJitter (fun _ => (1 / 20 : ℝ)) (N - 1) ≤ 3 / 20 ↔ N ≤ 4 := by
  rw [constant_jitter]
  have hn : (N - 1 : ℕ) + 1 = N := by omega
  have hc : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast hn
  constructor
  · intro h
    have : (N : ℝ) ≤ 4 := by linarith
    exact_mod_cast this
  · intro h
    have : (N : ℝ) ≤ 4 := by exact_mod_cast h
    linarith

theorem uniform_jitter_nonneg (n : ℕ) :
    0 ≤ min (1 / 20 : ℝ) (3 / (20 * (n : ℝ))) := by
  apply le_min <;> positivity

theorem uniform_jitter_per_link (n : ℕ) :
    min (1 / 20 : ℝ) (3 / (20 * (n : ℝ))) ≤ 1 / 20 := min_le_left _ _

theorem uniform_jitter_total {n : ℕ} (hn : 0 < n) :
    pathJitter (fun _ => min (1 / 20 : ℝ) (3 / (20 * (n : ℝ)))) n ≤ 3 / 20 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [constant_jitter]
  calc
    (n : ℝ) * min (1 / 20 : ℝ) (3 / (20 * (n : ℝ))) ≤
        (n : ℝ) * (3 / (20 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg n)
    _ = 3 / 20 := by field_simp <;> ring

end KernelR.Chain
