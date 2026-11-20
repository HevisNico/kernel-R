import MonotoneCharacterization
import TwoRailsTarget

/-! Negation by two rails. When each input comes with its complement on a second line, every Boolean function
is the predicted answer of an admissible monotone cascade. No inhibition is used and no cell law is changed:
the result is a corollary of `monotone_characterization`. -/

namespace LearnedCoincidence.MonotoneDNF

/-- The monotone function on the two rails that stands for `f`: true on a pattern of lines when some input
pattern that makes `f` true has all its rails among those lines. -/
private noncomputable def lifted {M : Nat} (f : Pattern M → Bool) (u : Pattern (M + M)) : Bool :=
  @decide (∃ x, contains u (rails x) = true ∧ f x = true) (Classical.propDecidable _)

private theorem lifted_true {M : Nat} (f : Pattern M → Bool) (u : Pattern (M + M)) :
    lifted f u = true ↔ ∃ x, contains u (rails x) = true ∧ f x = true := by
  unfold lifted
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- More lines never turn the lifted function from true to false. -/
private theorem lifted_monotone {M : Nat} (f : Pattern M → Bool) : MonotoneFunction (lifted f) := by
  intro u v more held
  obtain ⟨x, inside, good⟩ := (lifted_true f u).mp held
  exact (lifted_true f v).mpr
    ⟨x, contains_iff.mpr fun j hj => contains_iff.mp more j (contains_iff.mp inside j hj), good⟩

/-- Two input patterns whose rails are included one in the other are the same pattern. -/
private theorem same_of_rails_contained {M : Nat} {x y : Pattern M}
    (inside : contains (rails x) (rails y) = true) : y = x := by
  funext j
  have low := contains_iff.mp inside ⟨j.val, by omega⟩
  have high := contains_iff.mp inside ⟨M + j.val, by omega⟩
  have hj : j.val < M := j.isLt
  simp only [rails, hj, dite_true] at low
  have nj : ¬ (M + j.val < M) := by omega
  have idx : (⟨M + j.val - M, by omega⟩ : Fin M) = j := Fin.ext (by simp)
  simp only [rails, nj, dite_false, idx] at high
  cases hy : y j <;> cases hx : x j <;> simp_all

/-- On the two rails of an input pattern, the lifted function is `f`. -/
private theorem lifted_on_rails {M : Nat} (f : Pattern M → Bool) (x : Pattern M) :
    lifted f (rails x) = f x := by
  cases hfx : f x with
  | true => exact (lifted_true f (rails x)).mpr ⟨x, contains_iff.mpr fun _ h => h, hfx⟩
  | false =>
    cases hl : lifted f (rails x) with
    | false => rfl
    | true =>
      obtain ⟨y, inside, good⟩ := (lifted_true f (rails x)).mp hl
      rw [same_of_rails_contained inside] at good
      rw [good] at hfx
      exact absurd hfx (by decide)

theorem every_function_on_two_rails : EveryFunctionOnTwoRails := by
  intro M f
  obtain ⟨A, B, p, i, valid, same⟩ :=
    (monotone_characterization (M + M) (lifted f)).mp (lifted_monotone f)
  exact ⟨A, B, p, i, valid, fun x => by rw [same, lifted_on_rails]⟩

/-- The exclusive OR of two inputs, on two rails, is the function of campaign 6's circuit: with the lines in
the order `p`, `q`, `not p`, `not q`, it is `(p and not q) or (not p and q)`. -/
theorem exclusive_or_on_two_rails (x : Pattern 2) :
    (rails x 0 && rails x 3 || rails x 2 && rails x 1) = (x 0 != x 1) := by
  have r0 : rails x 0 = x 0 := rfl
  have r1 : rails x 1 = x 1 := rfl
  have r2 : rails x 2 = !x 0 := rfl
  have r3 : rails x 3 = !x 1 := rfl
  rw [r0, r1, r2, r3]
  cases x 0 <;> cases x 1 <;> rfl

end LearnedCoincidence.MonotoneDNF
