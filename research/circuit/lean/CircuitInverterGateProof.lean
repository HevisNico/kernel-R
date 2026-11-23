import CircuitInverterGate
import CircuitInverterGateBridge

/-! The bridge, stated about the single source of the gate's definitions
(`CircuitInverterGate.lean`, core Lean only). `CircuitInverterGateBridge.lean`
holds an earlier restatement of the same definitions over `ℚ`; it is superseded as
an interface and kept as the proof engine. The translation below is definitional:
each premise here is the very same proposition as its restatement there.

The measured state bound now enters through the gate's `StateBound`: the trajectory
stays within the measured `xPresent` (silence) or `xAbsent` (firing), and
`StateBound` puts those within `H0 * hl`. -/

namespace KernelR.Circuit.Gate

open MeasureTheory Set KernelR.Circuit

/-- The same design, measures and allowance in the restated structures. -/
def toDesign (d : Design) : InverterGate.Design := ⟨d.tau, d.h, d.hl, d.H0, d.D, d.level⟩
def toMeasures (m : Measures) : InverterGate.Measures :=
  ⟨m.aLo, m.aHi, m.aRef, m.alpha, m.eps0, m.etaH, m.etaM, m.etaJ, m.delta, m.Q, m.latchLo, m.latchHi,
    m.emit, m.early⟩
def toAllowance (k : Allowance) : InverterGate.Allowance := ⟨k.delta, k.eta⟩

theorem order_iff (d : Design) (m : Measures) (k : Allowance) :
    Order d m k ↔ InverterGate.Order (toDesign d) (toMeasures m) (toAllowance k) := Iff.rfl
theorem silenceBefore_iff (d : Design) (m : Measures) (k : Allowance) :
    SilenceBefore d m k ↔ InverterGate.SilenceBefore (toDesign d) (toMeasures m) (toAllowance k) := Iff.rfl
theorem silenceAfter_iff (d : Design) (m : Measures) (k : Allowance) :
    SilenceAfter d m k ↔ InverterGate.SilenceAfter (toDesign d) (toMeasures m) (toAllowance k) := Iff.rfl
theorem firingBefore_iff (d : Design) (m : Measures) (k : Allowance) :
    FiringBefore d m k ↔ InverterGate.FiringBefore (toDesign d) (toMeasures m) (toAllowance k) := Iff.rfl
theorem firingAfter_iff (d : Design) (m : Measures) (k : Allowance) :
    FiringAfter d m k ↔ InverterGate.FiringAfter (toDesign d) (toMeasures m) (toAllowance k) := Iff.rfl

/-- Silence from the gate, about the single-source definitions. -/
theorem gate_silence (d : Design) (m : Measures) (k : Allowance) (xPresent xAbsent : Rat)
    (order : Order d m k) (silenceBefore : SilenceBefore d m k) (silenceAfter : SilenceAfter d m k)
    (bound : StateBound d xPresent xAbsent)
    {actual leak help inhibitory wrongSign : ℝ → ℝ} {initial actualLevel : ℝ}
    (helpInt : IntervalIntegrable help volume 0 d.D)
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 d.D)
    (wrongInt : IntervalIntegrable wrongSign volume 0 d.D)
    (driftInt : IntervalIntegrable (fun u => (leak u - m.aRef) * actual u) volume 0 d.D)
    (gap : ∀ u ∈ Icc (0 : ℝ) d.D, |leak u - m.aRef| ≤ m.alpha)
    (stateBound : ∀ u ∈ Icc (0 : ℝ) d.D, |actual u| ≤ xPresent)
    (actualLaw : ∀ t ∈ Icc (0 : ℝ) d.D, actual t = leakyResponse m.aRef initial
      (fun u => (help u - (leak u - m.aRef) * actual u) - inhibitory u + wrongSign u) t)
    (initialError : |initial| ≤ m.eps0)
    (helpError : ∀ t ∈ Icc (0 : ℝ) d.D,
      (∫ u in 0..t, |help u - boxHelp d.H0 d.h d.hl u|) ≤ (m.etaH : ℝ) + k.eta)
    (inhibitorySign : ∀ u ∈ Icc (0 : ℝ) d.D, 0 ≤ inhibitory u)
    (wrongSignNonneg : ∀ u ∈ Icc (0 : ℝ) d.D, 0 ≤ wrongSign u)
    (wrongCharge : (∫ u in (0 : ℝ)..d.D, wrongSign u) ≤ m.etaM)
    (charge : (m.Q : ℝ) - k.eta ≤ ∫ u in (0 : ℝ)..d.tau, inhibitory u)
    (thresholdError : |actualLevel - d.level| ≤ (m.delta : ℝ) + k.delta) :
    ∀ t ∈ Icc (0 : ℝ) d.D, actual t < actualLevel := by
  have within : (xPresent : ℝ) ≤ (d.H0 : ℝ) * d.hl := by exact_mod_cast bound.2.1
  exact InverterGate.gate_silence (toDesign d) (toMeasures m) (toAllowance k) order silenceBefore
    silenceAfter helpInt inhibitoryInt wrongInt driftInt gap
    (fun u hu => (stateBound u hu).trans within) actualLaw initialError helpError inhibitorySign
    wrongSignNonneg wrongCharge charge thresholdError

/-- Firing from the gate, about the single-source definitions. -/
theorem gate_firing (d : Design) (m : Measures) (k : Allowance) (xPresent xAbsent : Rat)
    (order : Order d m k) (firingBefore : FiringBefore d m k) (firingAfter : FiringAfter d m k)
    (bound : StateBound d xPresent xAbsent)
    {actual leak help inhibitory : ℝ → ℝ} {initial actualLevel : ℝ}
    (actualCont : Continuous actual)
    (helpInt : IntervalIntegrable help volume 0 ((d.h : ℝ) + d.hl))
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 ((d.h : ℝ) + d.hl))
    (driftInt : IntervalIntegrable (fun u => (leak u - m.aRef) * actual u) volume 0 ((d.h : ℝ) + d.hl))
    (gap : ∀ u ∈ Icc (0 : ℝ) ((d.h : ℝ) + d.hl), |leak u - m.aRef| ≤ m.alpha)
    (stateBound : ∀ u ∈ Icc (0 : ℝ) ((d.h : ℝ) + d.hl), |actual u| ≤ xAbsent)
    (actualLaw : ∀ t ∈ Icc (0 : ℝ) ((d.h : ℝ) + d.hl), actual t = leakyResponse m.aRef initial
      (fun u => (help u - (leak u - m.aRef) * actual u) - inhibitory u) t)
    (initialError : |initial| ≤ m.eps0)
    (helpError : ∀ t ∈ Icc (0 : ℝ) ((d.h : ℝ) + d.hl),
      (∫ u in 0..t, |help u - boxHelp d.H0 d.h d.hl u|) ≤ (m.etaH : ℝ) + k.eta)
    (offCharge : (∫ u in (0 : ℝ)..((d.h : ℝ) + d.hl), |inhibitory u|) ≤ m.etaJ)
    (thresholdError : |actualLevel - d.level| ≤ (m.delta : ℝ) + k.delta) :
    ∃ root, (d.h : ℝ) + m.early < root ∧ root < (d.h : ℝ) + d.hl ∧ actual root = actualLevel ∧
      ∀ t ∈ Ico 0 root, actual t < actualLevel := by
  have within : (xAbsent : ℝ) ≤ (d.H0 : ℝ) * d.hl := by exact_mod_cast bound.2.2.2
  exact InverterGate.gate_firing (toDesign d) (toMeasures m) (toAllowance k) order firingBefore
    firingAfter actualCont helpInt inhibitoryInt driftInt gap
    (fun u hu => (stateBound u hu).trans within) actualLaw initialError helpError offCharge thresholdError

end KernelR.Circuit.Gate
