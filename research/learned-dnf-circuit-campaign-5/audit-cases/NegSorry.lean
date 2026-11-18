/-! Campaign 4, amendment 8: a negative case of check.sh's audit, written by hand, never by the campaign code. Its theorem
rests on `sorryAx`, written with none of the forbidden tokens, its warning not turned into an error. check.sh
must refuse it on the check of the axioms. -/

namespace NegSorryTest

set_option warningAsError false in
theorem uses_sorry_ax : (1 : Nat) = 2 := sorryAx _ false

end NegSorryTest
