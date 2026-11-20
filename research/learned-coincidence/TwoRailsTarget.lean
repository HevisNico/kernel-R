import MonotoneTarget

namespace LearnedCoincidence.MonotoneDNF

/-- The two rails of an input pattern: line `j` carries input `j`, and line `M + j` carries its complement. -/
def rails {M : Nat} (x : Pattern M) : Pattern (M + M) := fun j =>
  if h : j.val < M then x ⟨j.val, h⟩ else !x ⟨j.val - M, by omega⟩

/-- Frozen target: every Boolean function of `M` inputs is the predicted answer of an admissible cascade on
`2 M` lines, on the two rails of each input pattern. -/
def EveryFunctionOnTwoRails : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool),
    ∃ (A B : Nat) (p : Cascade A B (M + M)) (i : Fin B),
      p.Valid ∧ ∀ x : Pattern M, output p i (rails x) = f x

end LearnedCoincidence.MonotoneDNF
