import KernelR.HybridUniversalBirthCadenceChain

/-! The finite-chain router is fixed by the supplied delay family and horizon.
Its definition uses no constructed execution, preparation state or parameters. -/
namespace KernelR.Hybrid

noncomputable def canonicalFiniteChainRouter (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T : ℝ) : Router (n + 1) :=
  match n with
  | 0 => fun _ _ => []
  | j + 1 => prependRouted (canonicalFiniteChainRouter j delay T)
      (finiteCadenceHeadContact (0 : Fin (j + 1)) 2 160 (T + 1) (delay j))

@[simp] theorem canonicalFiniteChainRouter_root (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T time : ℝ) : canonicalFiniteChainRouter n delay T 0 time = [] := by
  cases n <;> rfl

/-- A non-root FIRE sends one token to its physical parent, at port 2, only
in the fixed contact window. Link indices count upward from the leaf. -/
theorem canonicalFiniteChainRouter_parent (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T time : ℝ) (i : Fin (n + 1)) :
    canonicalFiniteChainRouter (n + 1) delay T i.succ time =
      if 160 ≤ time ∧ time < T + 1 then
        [⟨i.castSucc, 2, time + delay (n - i.val) time⟩] else [] := by
  classical
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    change ([] : List (Delivery 1)).map Delivery.succ ++
      (finiteCadenceHeadContact (0 : Fin 1) 2 160 (T + 1) (delay 0) 0 time).map
        Delivery.head = _
    simp only [finiteCadenceHeadContact, true_and, List.map_nil, List.nil_append,
      Fin.val_zero, Nat.sub_zero]
    split_ifs <;> rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      change (canonicalFiniteChainRouter (n + 1) delay T 0 time).map Delivery.succ ++
        (finiteCadenceHeadContact (0 : Fin (n + 2)) 2 160 (T + 1)
          (delay (n + 1)) 0 time).map Delivery.head = _
      rw [canonicalFiniteChainRouter_root]
      simp only [finiteCadenceHeadContact, true_and, List.map_nil, List.nil_append,
        Fin.val_zero, Nat.sub_zero]
      split_ifs <;> rfl
    | succ i =>
      change (canonicalFiniteChainRouter (n + 1) delay T i.succ time).map Delivery.succ ++
        (finiteCadenceHeadContact (0 : Fin (n + 2)) 2 160 (T + 1)
          (delay (n + 1)) i.succ time).map Delivery.head = _
      rw [ih]
      simp only [finiteCadenceHeadContact, Fin.succ_ne_zero, false_and, ite_false,
        List.map_nil, List.append_nil, Fin.val_succ, Nat.add_sub_add_right]
      split_ifs <;> rfl

theorem FiniteChainPreparedData.route_eq_canonical
    {n θ s delay T hd} :
    (@finiteChainPreparedData n θ s delay T hd).route n =
      canonicalFiniteChainRouter n delay T := by
  have suffix : ∀ j, j ≤ n →
      (finiteChainPreparedData θ s delay T hd).route j =
        canonicalFiniteChainRouter j delay T := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      simp only [FiniteCausalChainData.route, canonicalFiniteChainRouter]
      rw [ih (by omega), FiniteChainPreparedData.contacts j (by omega)]
  exact suffix n le_rfl

theorem ConstructedBirthCadenceChain.router_eq_canonical
    {n θ bornCells K sigma centre delay T}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T) :
    chain.router = canonicalFiniteChainRouter n delay T :=
  FiniteChainPreparedData.route_eq_canonical

#print axioms ConstructedBirthCadenceChain.router_eq_canonical
#print axioms canonicalFiniteChainRouter_parent

end KernelR.Hybrid
