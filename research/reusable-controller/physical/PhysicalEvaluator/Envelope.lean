import PhysicalEvaluator.Counts

/-! Finite observation envelopes allow disturbances to vary during a read.
The two scalar implications are explicit physical premises: this module
does not derive them from a sampled noise supremum or a transistor trace.
The constant level introduced below is only a logical witness, not a claim
that the physical threshold or perturbation was constant during the read. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open ReusableController.Adaptive

/-- A finite scalar envelope around each actual Boolean observation.
A detected FIRE requires the lower scalar threshold to be reached; reaching
the upper scalar threshold cannot be missed. These assumptions may describe a
time-varying disturbance without assigning it one constant physical level. -/
structure FiniteEnvelopeCertificate (m : ℕ) where
  level0 : ℝ
  dose0 : ℝ
  a : ℝ
  B : ℝ
  ell : ℝ
  gain : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  observed : Fin (m + 1) → Bool
  ellNonnegative : 0 ≤ ell
  levelFloor : 19 / 20 ≤ level0 - ell
  gainBound : |gain 0 - needCentre level0 dose0 m| ≤ a
  cumulativeBound : ∀ k, |gain k - gain 0 - (k.val : ℝ) * dose0| ≤ B
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  room : a + B + 20 / 17 * ell + 1 / 8000 < dose0 / 2
  observableSound : ∀ k, observed k = true →
    PulseFires (charge k) (Real.exp (gain k)) (level0 - ell)
  observableComplete : ∀ k,
    PulseFires (charge k) (Real.exp (gain k)) (level0 + ell) → observed k = true

/-- This level merely witnesses an exact scalar classification compatible
with the envelope. It is not a reconstructed physical threshold. -/
noncomputable def FiniteEnvelopeCertificate.effectiveLevel {m}
    (certificate : FiniteEnvelopeCertificate m) (k : Fin (m + 1)) : ℝ :=
  if certificate.observed k then certificate.level0 - certificate.ell
  else certificate.level0 + certificate.ell

theorem FiniteEnvelopeCertificate.effectiveLevel_bound {m}
    (certificate : FiniteEnvelopeCertificate m) (k : Fin (m + 1)) :
    |certificate.effectiveLevel k - certificate.level0| ≤ certificate.ell := by
  cases observed : certificate.observed k <;>
    simp [effectiveLevel, observed, abs_of_nonneg certificate.ellNonnegative,
      sub_sub_cancel_left]

theorem FiniteEnvelopeCertificate.effectiveLevel_correspondence {m}
    (certificate : FiniteEnvelopeCertificate m) (k : Fin (m + 1)) :
    certificate.observed k = true ↔
      PulseFires (certificate.charge k) (Real.exp (certificate.gain k))
        (certificate.effectiveLevel k) := by
  cases observed : certificate.observed k with
  | false =>
    constructor
    · intro impossible; contradiction
    · intro fires
      have high : PulseFires (certificate.charge k) (Real.exp (certificate.gain k))
          (certificate.level0 + certificate.ell) := by
        simpa [effectiveLevel, observed] using fires
      have detected := certificate.observableComplete k high
      rw [observed] at detected
      exact detected
  | true =>
    constructor
    · intro _
      simpa [effectiveLevel, observed] using certificate.observableSound k observed
    · intro _; rfl

/-- Reuse the finite tolerance proof through a bounded logical level.
There is still no physical gain sequence or monotonicity premise after `m`. -/
noncomputable def FiniteEnvelopeCertificate.toProbeCertificate {m}
    (certificate : FiniteEnvelopeCertificate m) : FiniteProbeCertificate m where
  level0 := certificate.level0
  dose0 := certificate.dose0
  a := certificate.a
  B := certificate.B
  ell := certificate.ell
  gain := certificate.gain
  level := certificate.effectiveLevel
  charge := certificate.charge
  observed := certificate.observed
  levelFloor := certificate.levelFloor
  gainBound := certificate.gainBound
  cumulativeBound := certificate.cumulativeBound
  levelBound := certificate.effectiveLevel_bound
  chargeBand := certificate.chargeBand
  room := certificate.room
  scalarCorrespondence := certificate.effectiveLevel_correspondence

def FiniteEnvelopeCertificate.readings {m} (certificate : FiniteEnvelopeCertificate m) : List Bool :=
  List.ofFn certificate.observed

theorem FiniteEnvelopeCertificate.silent_before {m}
    (certificate : FiniteEnvelopeCertificate m) (k : Fin (m + 1)) (before : k.val < m) :
    certificate.observed k = false := certificate.toProbeCertificate.silent_before k before

theorem FiniteEnvelopeCertificate.fires_at {m} (certificate : FiniteEnvelopeCertificate m) :
    certificate.observed (Fin.last m) = true := certificate.toProbeCertificate.fires_at

theorem FiniteEnvelopeCertificate.readings_shape {m} (certificate : FiniteEnvelopeCertificate m) :
    certificate.readings = List.replicate m false ++ [true] := certificate.toProbeCertificate.readings_shape

theorem FiniteEnvelopeCertificate.firstFire_exact {m} (certificate : FiniteEnvelopeCertificate m) :
    firstFire certificate.readings = some m := certificate.toProbeCertificate.firstFire_exact

theorem FiniteEnvelopeCertificate.count_exact {m} (certificate : FiniteEnvelopeCertificate m) :
    decodedCount certificate.readings = m := certificate.toProbeCertificate.count_exact

/-- Zero discrete count error follows from the two finite observation
envelopes, without assuming a constant physical threshold during a read. -/
theorem accuracy_from_envelopes {preparation practice : ℕ}
    (preparationCertificate : FiniteEnvelopeCertificate preparation)
    (practiceCertificate : FiniteEnvelopeCertificate practice) :
    LessonAccurate ⟨preparation, practice⟩
      (marginOracle (decodedCount preparationCertificate.readings)
        (decodedCount practiceCertificate.readings)) 0 :=
  accuracy_from_certificates preparationCertificate.toProbeCertificate practiceCertificate.toProbeCertificate

end ReusableController.PhysicalEvaluator
