import KernelR.HybridFiniteChainCanonicalRouter

/-! A closed-form finite-chain protocol, independent of execution witnesses.
Cell zero emits no routed token. Every other cell sends one token to its
parent at port two in the fixed contact window, using its leaf-indexed delay.
The definition contains no recursion or routed-chain composition. -/
namespace KernelR.Hybrid
attribute [local instance] Classical.propDecidable

noncomputable def explicitFiniteChainRouter (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T : ℝ) : Router (n + 1) := fun i time =>
  if i.val = 0 then [] else
    if 160 ≤ time ∧ time < T + 1 then
      [⟨⟨i.val - 1, by omega⟩, 2, time + delay (n - i.val) time⟩] else []

/-- The explicit finite-chain protocol is extensionally the existing
canonical protocol, for every size, delay function and horizon. -/
theorem canonicalFiniteChainRouter_eq_explicit (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T : ℝ) : canonicalFiniteChainRouter n delay T = explicitFiniteChainRouter n delay T := by
  funext i time
  cases n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rw [canonicalFiniteChainRouter_root]
    simp [explicitFiniteChainRouter]
  | succ n =>
    cases i using Fin.cases with
    | zero =>
      rw [canonicalFiniteChainRouter_root]
      simp [explicitFiniteChainRouter]
    | succ i =>
      rw [canonicalFiniteChainRouter_parent]
      simp only [explicitFiniteChainRouter, Fin.val_succ, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_add_right]
      split_ifs <;> rfl

@[simp] theorem explicitFiniteChainRouter_root (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T time : ℝ) : explicitFiniteChainRouter n delay T 0 time = [] := by
  simp [explicitFiniteChainRouter]

theorem explicitFiniteChainRouter_parent (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T time : ℝ) (i : Fin (n + 1)) :
    explicitFiniteChainRouter (n + 1) delay T i.succ time =
      if 160 ≤ time ∧ time < T + 1 then
        [⟨i.castSucc, 2, time + delay (n - i.val) time⟩] else [] := by
  rw [← canonicalFiniteChainRouter_eq_explicit]
  exact canonicalFiniteChainRouter_parent n delay T time i

#print axioms canonicalFiniteChainRouter_eq_explicit

end KernelR.Hybrid
