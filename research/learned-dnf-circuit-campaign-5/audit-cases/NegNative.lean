import NativeDecl

/-! Campaign 4, amendment 8: a negative case of check.sh's audit, written by hand, never by the campaign code. Its theorem
rests on the postulate of the compiler's evaluation declared in the imported module NativeDecl.lean (Lean
4.35.0 has no `Lean.trustCompiler`); this file has none of the forbidden tokens. check.sh must refuse it on the check
of the axioms. -/

namespace NegNativeTest

theorem uses_native : 2 + 2 = 4 := NativeTest.four_native

end NegNativeTest
