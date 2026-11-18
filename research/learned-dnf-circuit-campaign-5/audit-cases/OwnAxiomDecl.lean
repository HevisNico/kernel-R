import Lean

/-! Campaign 4, amendment 8: the module of a negative case of check.sh's audit, written by hand, never by the
campaign code. It declares a postulate of our own with none of the forbidden tokens; its own theorem rests on
nothing, so this module passes the audit. NegOwnAxiom.lean imports it. -/

namespace OwnAxiomTest

open Lean Elab Command in
run_cmd liftCoreM <| addDecl <| .axiomDecl { name := `OwnAxiomTest.own_false, levelParams := [], type := mkConst ``False, isUnsafe := false }

theorem declared_module_has_a_theorem : True := trivial

end OwnAxiomTest
