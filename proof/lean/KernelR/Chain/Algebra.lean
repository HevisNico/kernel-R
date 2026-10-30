import Mathlib.Tactic

/-! The twelve published polynomial identities, over integers rather than
truncated natural subtraction. Natural-count side conditions are proved in
Chain.Induction. No Python polynomial normalizer is trusted by these proofs. -/
namespace KernelR.Chain.Algebra

theorem base_prefix : (3 : ℤ) + 2 * 0 = 3 := by ring
theorem base_tail (K : ℤ) : K - 8 - 4 * 0 = K - 8 := by ring
theorem prefix_step (j : ℤ) : 3 + 2 * (j + 1) = (3 + 2 * j) + 2 := by ring
theorem tail_step (K j : ℤ) : K - 8 - 4 * (j + 1) = (K - 8 - 4 * j) - 4 := by ring
theorem node_outputs (K j : ℤ) : (3 + 2 * j) + (K - 8 - 4 * j) = K - 5 - 2 * j := by ring
theorem remaining_tail (N j R : ℤ) :
    (4 * N + 12 + R) - 8 - 4 * j = 8 + 4 * (N - 1 - j) + R := by ring
theorem last_tail (N R : ℤ) :
    (4 * N + 12 + R) - 8 - 4 * (N - 1) = 8 + R := by ring
theorem root_outputs (K N : ℤ) : K - 5 - 2 * (N - 1) = K - 2 * N - 3 := by ring
theorem root_outputs_surplus (N R : ℤ) :
    (4 * N + 12 + R) - 2 * N - 3 = 2 * N + 9 + R := by ring
theorem traffic_base (K : ℤ) : 1 * (K - 1 - 4) = K - 5 := by ring
theorem traffic_step (N K : ℤ) :
    (N + 1) * (K - (N + 1) - 4) = N * (K - N - 4) + (K - 5 - 2 * N) := by ring
theorem traffic_at_minimum (N R : ℤ) :
    N * ((4 * N + 12 + R) - N - 4) = 3 * N * N + 8 * N + N * R := by ring

end KernelR.Chain.Algebra
