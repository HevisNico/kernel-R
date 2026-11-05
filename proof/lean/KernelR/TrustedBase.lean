import KernelR.TrustedHeadline
import KernelR.TrustedBaseChecker

/-! Explicit review allowlist for the headline's statement semantics.

The checker computes its closure independently of this list. Proof values are
not mathematical assumptions of the statement and are checked separately by
Lean and Audit.lean. An incomplete list fails the build, including this draft
while the machine-reported semantic parents are being registered.
-/
namespace KernelR.TrustedBase
open Lean
set_option maxHeartbeats 8000000

def trustedDeclarations : List Name := []

open Elab Command in
run_cmd liftTermElabM do
  let report ← TrustedBaseChecker.check
    `KernelR.Hybrid.TrustedHeadline.every_finite_chain trustedDeclarations
  logInfo m!"Trusted statement check passed: {report.parents.toArray.size} semantic parents."

end KernelR.TrustedBase
