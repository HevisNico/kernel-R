import OwnAxiomDecl

/-! Campaign 4, amendment 8: a negative case of check.sh's audit, written by hand, never by the campaign code. Its theorem
rests on a postulate of our own, declared in the imported module OwnAxiomDecl.lean, not in this file. check.sh
must refuse it on the check of the axioms. -/

namespace NegOwnAxiomTest

theorem uses_own_axiom : (1 : Nat) = 2 := (OwnAxiomTest.own_false).elim

end NegOwnAxiomTest
