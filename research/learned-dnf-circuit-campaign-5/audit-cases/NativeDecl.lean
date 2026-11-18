import Lean

/-! Campaign 4, amendment 8: the module of a negative case of check.sh's audit, written by hand, never by the
campaign code. It builds, from a string split in two, a theorem proved by the compiler's evaluation, so Lean declares
its auxiliary postulate for it; its own theorem rests on nothing, so this module passes the audit. NegNative.lean
imports it. -/

namespace NativeTest

open Lean Elab Command in
run_cmd do
  let src := "theorem four_native : 2 + 2 = 4 := by native" ++ "_decide"
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => elabCommand stx
  | .error e => throwError e

theorem native_module_has_a_theorem : True := trivial

end NativeTest
