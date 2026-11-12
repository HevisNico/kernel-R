import SelfCertifyingLearning.Composition

/-! An exact finite checker for supplied coupling weights. It validates a
witness; it neither searches for weights nor characterizes M-matrices. -/
namespace SelfCertifyingLearning.CompositionCheck

structure Witness (n : Nat) where
  weights : Fin n → Nat
  delta : Fin n → Nat
  damage : Fin n → Fin n → Nat
  eta : Nat

def Valid {n : Nat} (w : Witness n) : Prop :=
  0 < w.eta ∧ ∀ i, 0 < w.weights i ∧
    w.eta + weighted w.weights (spill w.damage i) (List.finRange n) ≤
      weighted w.weights (retired w.delta i) (List.finRange n)

instance {n : Nat} (w : Witness n) : Decidable (Valid w) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ ∧ _))

def check {n : Nat} (w : Witness n) : Bool := decide (Valid w)

theorem check_iff {n : Nat} (w : Witness n) : check w = true ↔ Valid w := by
  simp [check]

/-- Convert accepted numeric data into the existing proof-carrying
certificate without changing any supplied weight or coupling bound. -/
def certify {n : Nat} (w : Witness n) (accepted : check w = true) : CouplingCertificate n where
  weights := w.weights
  delta := w.delta
  damage := w.damage
  eta := w.eta
  weightsPositive := fun i => ((check_iff w).mp accepted).2 i |>.1
  marginPositive := ((check_iff w).mp accepted).1
  margin := fun i => ((check_iff w).mp accepted).2 i |>.2

theorem verified_decrease {n : Nat} (w : Witness n) (accepted : check w = true)
    (before after : Fin n → Nat) (i : Fin n)
    (coordinates : ∀ j, after j + retired w.delta i j ≤ before j + spill w.damage i j) :
    weighted w.weights after (List.finRange n) + w.eta ≤
      weighted w.weights before (List.finRange n) :=
  (certify w accepted).decrease before after i coordinates

def two : Witness 2 := ⟨fun _ => 1, fun _ => 3, fun _ _ => 1, 2⟩

theorem two_accepted : check two = true := by decide

theorem zero_margin_rejected : check { two with eta := 0 } = false := by decide

theorem zero_weight_rejected : check { two with weights := fun _ => 0 } = false := by decide

def chain : Witness 3 := ⟨fun _ => 1, fun _ => 5,
  fun j i => if j.val + 1 = i.val ∨ i.val + 1 = j.val then 4 else 0, 1⟩

theorem accumulated_spillover_rejected : check chain = false := by decide

end SelfCertifyingLearning.CompositionCheck
