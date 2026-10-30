import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Exact rational certificates and their interpretation over the reals.
These lemmas do not assume that an interval encloses a transcendental expression.
That membership must be provided explicitly by a separate analytic proof. -/
namespace KernelR

structure RationalBox where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def RationalBox.Valid (a : RationalBox) : Prop := a.lo ≤ a.hi
def RationalBox.StrictBefore (a b : RationalBox) : Prop := a.hi < b.lo
def RationalBox.Before (a b : RationalBox) : Prop := a.hi ≤ b.lo
def RationalBox.Contains (a : RationalBox) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

theorem strict_of_enclosures {a b : RationalBox} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) (h : a.StrictBefore b) : x < y := by
  have h' : (a.hi : ℝ) < (b.lo : ℝ) := by exact_mod_cast h
  exact lt_of_le_of_lt ha.2 (lt_of_lt_of_le h' hb.1)

theorem le_of_enclosures {a b : RationalBox} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) (h : a.Before b) : x ≤ y := by
  have h' : (a.hi : ℝ) ≤ (b.lo : ℝ) := by exact_mod_cast h
  exact ha.2.trans (h'.trans hb.1)

theorem enclosure_intersection {l₁ u₁ l₂ u₂ x : ℝ}
    (h₁ : l₁ ≤ x ∧ x ≤ u₁) (h₂ : l₂ ≤ x ∧ x ≤ u₂) :
    max l₁ l₂ ≤ x ∧ x ≤ min u₁ u₂ :=
  ⟨max_le h₁.1 h₂.1, le_min h₁.2 h₂.2⟩

theorem enclosure_hull_left {l₁ u₁ l₂ u₂ x : ℝ}
    (h : l₁ ≤ x ∧ x ≤ u₁) : min l₁ l₂ ≤ x ∧ x ≤ max u₁ u₂ :=
  ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩

theorem exponential_enclosure {l u z : ℝ} (h : l ≤ z ∧ z ≤ u) :
    Real.exp l ≤ Real.exp z ∧ Real.exp z ≤ Real.exp u :=
  ⟨Real.exp_le_exp.mpr h.1, Real.exp_le_exp.mpr h.2⟩

theorem independent_boxes {ι : Type*} (box : ι → RationalBox) (x : ι → ℝ)
    (hx : ∀ i, (box i).Contains (x i)) (i : ι) : (box i).Contains (x i) := hx i

end KernelR
