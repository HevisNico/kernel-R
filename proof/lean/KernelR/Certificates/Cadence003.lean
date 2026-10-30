import KernelR.Certificates.Cadence003.Bounds00
import KernelR.Certificates.Cadence003.Bounds01
import KernelR.Certificates.Cadence003.Bounds02
import KernelR.Certificates.Cadence003.Bounds03
import KernelR.Certificates.Cadence003.Bounds04
import KernelR.Certificates.Cadence003.Bounds05
import KernelR.Certificates.Cadence003.Bounds06
import KernelR.Certificates.Cadence003.Bounds07
import KernelR.Certificates.Cadence003.Bounds08
import KernelR.Certificates.Cadence003.Bounds09
import KernelR.Certificates.Cadence003.Bounds10
import KernelR.Certificates.Cadence003.Bounds11
import KernelR.Certificates.Cadence003.Bounds12
import KernelR.Certificates.Cadence003.Bounds13
import KernelR.Certificates.Cadence003.Bounds14
import KernelR.Certificates.Cadence003.Bounds15
import KernelR.Certificates.Cadence003.Checks00
import KernelR.Certificates.Cadence003.Checks01
import KernelR.Certificates.Cadence003.Checks02
import KernelR.Certificates.Cadence003.Checks03
import KernelR.Certificates.Cadence003.Checks04
import KernelR.Certificates.Cadence003.Checks05
import KernelR.Certificates.Cadence003.Checks06

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence003
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def Obligations : Prop :=
  Checks00Valid ∧
  Checks01Valid ∧
  Checks02Valid ∧
  Checks03Valid ∧
  Checks04Valid ∧
  Checks05Valid ∧
  Checks06Valid
theorem Obligations_verified : Obligations := by
  exact ⟨Checks00Valid_verified, Checks01Valid_verified, Checks02Valid_verified, Checks03Valid_verified, Checks04Valid_verified, Checks05Valid_verified, Checks06Valid_verified⟩

def AllBoundsValid : Prop :=
  Bounds00Valid ∧
  Bounds01Valid ∧
  Bounds02Valid ∧
  Bounds03Valid ∧
  Bounds04Valid ∧
  Bounds05Valid ∧
  Bounds06Valid ∧
  Bounds07Valid ∧
  Bounds08Valid ∧
  Bounds09Valid ∧
  Bounds10Valid ∧
  Bounds11Valid ∧
  Bounds12Valid ∧
  Bounds13Valid ∧
  Bounds14Valid ∧
  Bounds15Valid
theorem AllBoundsValid_verified : AllBoundsValid := by
  exact ⟨Bounds00Valid_verified, Bounds01Valid_verified, Bounds02Valid_verified, Bounds03Valid_verified, Bounds04Valid_verified, Bounds05Valid_verified, Bounds06Valid_verified, Bounds07Valid_verified, Bounds08Valid_verified, Bounds09Valid_verified, Bounds10Valid_verified, Bounds11Valid_verified, Bounds12Valid_verified, Bounds13Valid_verified, Bounds14Valid_verified, Bounds15Valid_verified⟩

end KernelR.Certificates.Cadence003
#print axioms KernelR.Certificates.Cadence003.Obligations_verified
#print axioms KernelR.Certificates.Cadence003.AllBoundsValid_verified
