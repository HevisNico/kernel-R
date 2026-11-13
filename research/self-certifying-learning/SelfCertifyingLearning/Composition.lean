import SelfCertifyingLearning.Budget

/-! Exact witnesses for finite weighted coupling inequalities. No eigenvalue
calculation or M-matrix characterization is assumed or proved here. -/
namespace SelfCertifyingLearning

def weighted {I : Type} (weights value : I → Nat) : List I → Nat
  | [] => 0
  | i :: rest => weights i * value i + weighted weights value rest

theorem weighted_balance {I : Type} (indices : List I)
    (weights before after removed added : I → Nat)
    (coordinateBound : ∀ i ∈ indices, after i + removed i ≤ before i + added i) :
    weighted weights after indices + weighted weights removed indices ≤
      weighted weights before indices + weighted weights added indices := by
  induction indices with
  | nil => simp [weighted]
  | cons i rest ih =>
    have head := Nat.mul_le_mul_left (weights i) (coordinateBound i (by simp))
    simp only [Nat.mul_add] at head
    have tail := ih (fun j hj => coordinateBound j (by simp [hj]))
    simp only [weighted]
    omega

/-- A positive margin pays for spillover into every other coordinate. -/
theorem coupled_decrease {I : Type} (indices : List I)
    (weights before after removed added : I → Nat) (eta : Nat)
    (coordinateBound : ∀ i ∈ indices, after i + removed i ≤ before i + added i)
    (margin : eta + weighted weights added indices ≤ weighted weights removed indices) :
    weighted weights after indices + eta ≤ weighted weights before indices := by
  have := weighted_balance indices weights before after removed added coordinateBound
  omega

def retired {n : Nat} (delta : Fin n → Nat) (i j : Fin n) : Nat :=
  if j = i then delta i else 0

/-- a j i is the damage to coordinate j made by a correction at i.
The own-coordinate entry is ignored; it is already in delta. -/
def spill {n : Nat} (a : Fin n → Fin n → Nat) (i j : Fin n) : Nat :=
  if j = i then 0 else a j i

structure CouplingCertificate (n : Nat) where
  weights : Fin n → Nat
  delta : Fin n → Nat
  damage : Fin n → Fin n → Nat
  eta : Nat
  weightsPositive : ∀ i, 0 < weights i
  marginPositive : 0 < eta
  margin : ∀ i,
    eta + weighted weights (spill damage i) (List.finRange n) ≤
      weighted weights (retired delta i) (List.finRange n)

theorem CouplingCertificate.decrease {n} (cert : CouplingCertificate n)
    (before after : Fin n → Nat) (i : Fin n)
    (coordinateBound : ∀ j, after j + retired cert.delta i j ≤ before j + spill cert.damage i j) :
    weighted cert.weights after (List.finRange n) + cert.eta ≤
      weighted cert.weights before (List.finRange n) :=
  coupled_decrease _ _ _ _ _ _ _ (fun j _ => coordinateBound j) (cert.margin i)

/-- This connects the coordinate contract to the actual finite-run ledger. -/
theorem CouplingCertificate.prepend {n} (cert : CouplingCertificate n)
    (before after : Fin n → Nat) (i : Fin n) {rest final}
    (coordinateBound : ∀ j, after j + retired cert.delta i j ≤ before j + spill cert.damage i j)
    (tail : Run cert.eta (weighted cert.weights after (List.finRange n)) rest final) :
    Run cert.eta (weighted cert.weights before (List.finRange n))
      (.correction :: rest) final :=
  .correction (cert.decrease before after i coordinateBound) tail

/-- Two levels: each removes three ticks locally and creates at most one
tick in the other. Equal weights certify a two-tick global decrease. -/
def twoLevel : CouplingCertificate 2 where
  weights := fun _ => 1
  delta := fun _ => 3
  damage := fun _ _ => 1
  eta := 2
  weightsPositive := by decide
  marginPositive := by decide
  margin := by decide

theorem two_level_decreases (before after : Fin 2 → Nat) (i : Fin 2)
    (coordinateBound : ∀ j, after j + retired twoLevel.delta i j ≤
      before j + spill twoLevel.damage i j) :
    weighted twoLevel.weights after (List.finRange 2) + 2 ≤
      weighted twoLevel.weights before (List.finRange 2) :=
  twoLevel.decrease before after i coordinateBound

end SelfCertifyingLearning
