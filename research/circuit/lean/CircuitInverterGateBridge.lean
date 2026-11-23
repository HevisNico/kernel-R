import CircuitInverterVaryingLeak
import CircuitInverterBoxReference
import CircuitInverterTaylor

/-! The bridge from the per-instance gate (rational premises checked by
`decide +kernel`) to the real hypotheses of the varying-leak theorems.

The gate's definitions are restated here, over `ℚ` and with the same names and
formulas, from the instance worker's interface (`InverterInstanceCheck.lean`,
local commit cd8823e, file not in this branch): `Design`, `Measures`,
`Allowance`, `expLo`, `expHi`, `refUpper`, `refLower`, `leakBudget`, `leakTerm`,
`silenceBudget`, `firingBudget`, `silenceMargin`, `firingMargin`, `Order`,
`SilenceBefore`, `SilenceAfter`, `FiringBefore`, `FiringAfter`.

The real theorems are those with a VARYING leak (`inhibited_silence_varying`,
`uninhibited_first_crossing_varying`), with `a' = aRef`, `α = alpha`,
`X = H0 * hl`, reference `leakyResponse aRef 0 (boxHelp H0 h hl)`,
`ηH = etaH + k.eta`, `δ = delta + k.delta`, `Q = m.Q - k.eta`,
`early = h + m.early` and `deadline = h + hl`. The gate's `leakTerm = α * D * H0 * hl`
covers `α * X * D` exactly when the measured state stays within `X = H0 * hl`:
that state bound is a hypothesis here, NOT one of the gate's current premises.

The box help is `H0` on `(h, h + hl]`; the worker's box is `H0` on `[h, h + hl)`.
They differ on two points only, so every integral (and the measured `etaH`) is
the same. -/

namespace KernelR.Circuit.InverterGate

open MeasureTheory Set KernelR.Circuit

structure Design where
  tau : ℚ
  h : ℚ
  hl : ℚ
  H0 : ℚ
  D : ℚ
  level : ℚ

structure Measures where
  aLo : ℚ
  aHi : ℚ
  aRef : ℚ
  alpha : ℚ
  eps0 : ℚ
  etaH : ℚ
  etaM : ℚ
  etaJ : ℚ
  delta : ℚ
  Q : ℚ
  latchLo : ℚ
  latchHi : ℚ
  emit : ℚ
  early : ℚ

structure Allowance where
  delta : ℚ
  eta : ℚ

def expLo (x : ℚ) : ℚ := 1 - x + x * x / 2 - x * x * x / 6 + x * x * x * x / 24 - x * x * x * x * x / 120
def expHi (x : ℚ) : ℚ := expLo x + x * x * x * x * x * x / 720
def refUpper (d : Design) (m : Measures) (y : ℚ) : ℚ := d.H0 * (1 - expLo (m.aRef * y)) / m.aRef
def refLower (d : Design) (m : Measures) (y : ℚ) : ℚ := d.H0 * (1 - expHi (m.aRef * y)) / m.aRef
def leakBudget (d : Design) : ℚ := d.D * d.H0 * d.hl
def leakTerm (d : Design) (m : Measures) : ℚ := m.alpha * leakBudget d
def silenceBudget (m : Measures) (k : Allowance) : ℚ := m.eps0 + m.etaH + m.etaM + k.eta
def firingBudget (m : Measures) (k : Allowance) : ℚ := m.eps0 + m.etaH + m.etaJ + k.eta

def silenceMargin (d : Design) (m : Measures) (k : Allowance) : ℚ :=
  d.level + expLo ((m.aRef + m.alpha) * d.D) * (m.Q - k.eta) -
    (refUpper d m d.hl + silenceBudget m k + (m.delta + k.delta) + leakTerm d m)

def firingMargin (d : Design) (m : Measures) (k : Allowance) : ℚ :=
  refLower d m d.hl - (d.level + firingBudget m k + (m.delta + k.delta) + leakTerm d m)

def Order (d : Design) (m : Measures) (k : Allowance) : Prop :=
  0 ≤ d.tau ∧ d.tau ≤ d.h ∧ 0 < d.hl ∧ d.h + d.hl ≤ d.D ∧ 0 ≤ m.aLo ∧ m.aLo ≤ m.aHi ∧ 0 < m.aRef ∧
  0 ≤ m.alpha ∧ m.aRef - m.alpha ≤ m.aLo ∧ m.aHi ≤ m.aRef + m.alpha ∧ 0 ≤ m.Q - k.eta ∧ 0 < d.H0 ∧
  0 ≤ m.eps0 ∧ 0 ≤ m.etaH ∧ 0 ≤ m.etaM ∧ 0 ≤ m.etaJ ∧ 0 ≤ m.delta ∧ 0 ≤ k.delta ∧ 0 ≤ k.eta ∧
  0 ≤ m.early ∧ m.early < d.hl ∧ 0 ≤ m.latchLo ∧ m.latchLo ≤ m.latchHi

def SilenceBefore (d : Design) (m : Measures) (k : Allowance) : Prop :=
  silenceBudget m k + (m.delta + k.delta) + leakTerm d m < d.level

def SilenceAfter (d : Design) (m : Measures) (k : Allowance) : Prop := 0 < silenceMargin d m k

def FiringBefore (d : Design) (m : Measures) (k : Allowance) : Prop :=
  refUpper d m m.early + firingBudget m k + (m.delta + k.delta) + leakTerm d m < d.level

def FiringAfter (d : Design) (m : Measures) (k : Allowance) : Prop := 0 < firingMargin d m k

/-! ### Casts of the rational bounds of `exp`. -/

theorem expLo_cast (x : ℚ) : ((expLo x : ℚ) : ℝ) = expNegSum 6 (x : ℝ) := by
  rw [expNegSum_six_eq]; simp [expLo]

theorem expHi_cast (x : ℚ) : ((expHi x : ℚ) : ℝ) = expNegSum 7 (x : ℝ) := by
  rw [expNegSum_seven_eq, ← expLo_cast]; simp [expHi]

/-! ### The box reference within and at the end of its window. -/

theorem box_closed_le_window {a c h ℓ y t : ℝ} (leak : 0 < a) (help : 0 ≤ c)
    (hy : 0 ≤ y) (yl : y ≤ ℓ) (ht : t ≤ h + y) :
    boxClosed a c h ℓ t ≤ c / a * (1 - Real.exp (-a * y)) := by
  have ca : 0 ≤ c / a := div_nonneg help leak.le
  unfold boxClosed
  split_ifs with h1 h2
  · exact mul_nonneg ca (by have := Real.exp_le_one_iff.mpr (show -a * y ≤ 0 by nlinarith); linarith)
  · apply mul_le_mul_of_nonneg_left _ ca
    have := Real.exp_le_exp.mpr (show -a * y ≤ -a * (t - h) by nlinarith)
    linarith
  · exact absurd (ht.trans (by linarith)) h2

theorem box_closed_at_end {a c h ℓ : ℝ} (width : 0 < ℓ) :
    boxClosed a c h ℓ (h + ℓ) = c / a * (1 - Real.exp (-a * ℓ)) := by
  have h1 : ¬ (h + ℓ ≤ h) := by linarith
  simp [boxClosed, h1]

theorem box_help_integrable (c h ℓ x y : ℝ) : IntervalIntegrable (boxHelp c h ℓ) volume x y := by
  have eq : boxHelp c h ℓ = (Ioc h (h + ℓ)).indicator (fun _ => c) := by
    funext u; simp only [boxHelp, indicator, mem_Ioc]
  rw [eq]
  refine (intervalIntegrable_const (c := c)).mono_fun
    ((measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun u => by simp only [indicator]; split_ifs <;> simp)

/-! ### The assembly. -/

/-- Silence from the gate: the rational premises `Order`, `SilenceBefore` and
`SilenceAfter`, with the measured real hypotheses of the cell, give silence on the
whole slot under a varying leak. -/
theorem gate_silence (d : Design) (m : Measures) (k : Allowance)
    (order : Order d m k) (silenceBefore : SilenceBefore d m k) (silenceAfter : SilenceAfter d m k)
    {actual leak help inhibitory wrongSign : ℝ → ℝ} {initial actualLevel : ℝ}
    (helpInt : IntervalIntegrable help volume 0 d.D)
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 d.D)
    (wrongInt : IntervalIntegrable wrongSign volume 0 d.D)
    (driftInt : IntervalIntegrable (fun u => (leak u - m.aRef) * actual u) volume 0 d.D)
    (gap : ∀ u ∈ Icc (0 : ℝ) d.D, |leak u - m.aRef| ≤ m.alpha)
    (stateBound : ∀ u ∈ Icc (0 : ℝ) d.D, |actual u| ≤ (d.H0 : ℝ) * d.hl)
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
  obtain ⟨tau0, tauH, hl0, hD, _, _, aRef0, alpha0, _, _, Q0, H00, _⟩ := order
  have tau0' : (0 : ℝ) ≤ d.tau := by exact_mod_cast tau0
  have tauH' : (d.tau : ℝ) ≤ d.h := by exact_mod_cast tauH
  have hl0' : (0 : ℝ) < d.hl := by exact_mod_cast hl0
  have hD' : (d.h : ℝ) + d.hl ≤ d.D := by exact_mod_cast hD
  have aRef0' : (0 : ℝ) < m.aRef := by exact_mod_cast aRef0
  have alpha0' : (0 : ℝ) ≤ m.alpha := by exact_mod_cast alpha0
  have Q0' : (0 : ℝ) ≤ (m.Q : ℝ) - k.eta := by exact_mod_cast Q0
  have H00' : (0 : ℝ) < d.H0 := by exact_mod_cast H00
  have h0 : (0 : ℝ) ≤ d.h := tau0'.trans tauH'
  have before' : ((silenceBudget m k + (m.delta + k.delta) + leakTerm d m : ℚ) : ℝ) < d.level := by
    exact_mod_cast silenceBefore
  have after' : (0 : ℝ) < ((silenceMargin d m k : ℚ) : ℝ) := by exact_mod_cast silenceAfter
  push_cast [silenceBudget, leakTerm, leakBudget] at before'
  simp only [silenceMargin, refUpper, silenceBudget, leakTerm, leakBudget, Rat.cast_sub, Rat.cast_add,
    Rat.cast_mul, Rat.cast_div, expLo_cast] at after'
  push_cast at after'
  -- The peak of the reference against `refUpper`.
  have peak : ∀ t, 0 ≤ t → leakyResponse m.aRef 0 (boxHelp d.H0 d.h d.hl) t ≤
      (d.H0 : ℝ) * (1 - expNegSum 6 ((m.aRef : ℝ) * d.hl)) / m.aRef := by
    intro t ht
    rw [box_reference_eq aRef0' h0 hl0'.le ht]
    have b := box_closed_le_peak (t := t) aRef0' H00'.le hl0'.le (h := (d.h : ℝ))
    have e := expNegSum_six_le (mul_nonneg aRef0'.le hl0'.le)
    have scale : 0 ≤ (d.H0 : ℝ) / m.aRef := div_nonneg H00'.le aRef0'.le
    have : (d.H0 : ℝ) / m.aRef * (1 - Real.exp (-(m.aRef * d.hl))) ≤
        (d.H0 : ℝ) / m.aRef * (1 - expNegSum 6 ((m.aRef : ℝ) * d.hl)) :=
      mul_le_mul_of_nonneg_left (by linarith) scale
    rw [show -(m.aRef : ℝ) * d.hl = -(m.aRef * d.hl) by ring] at b
    calc _ ≤ _ := b
      _ ≤ _ := this
      _ = _ := by ring
  -- The discount of the inhibitory charge.
  have discount : expNegSum 6 (((m.aRef : ℝ) + m.alpha) * d.D) * ((m.Q : ℝ) - k.eta) ≤
      Real.exp (-(m.aRef : ℝ) * d.D) * ((m.Q : ℝ) - k.eta) := by
    have D0 : (0 : ℝ) ≤ d.D := by linarith
    have e1 := expNegSum_six_le (mul_nonneg (by linarith : (0 : ℝ) ≤ m.aRef + m.alpha) D0)
    have e2 : Real.exp (-(((m.aRef : ℝ) + m.alpha) * d.D)) ≤ Real.exp (-(m.aRef : ℝ) * d.D) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul_of_nonneg_right (e1.trans e2) Q0'
  apply inhibited_silence_varying (reference := leakyResponse m.aRef 0 (boxHelp d.H0 d.h d.hl))
    (nominalHelp := boxHelp d.H0 d.h d.hl) (referenceInitial := 0) (X := (d.H0 : ℝ) * d.hl)
    (ε₀ := m.eps0) (ηH := (m.etaH : ℝ) + k.eta) (ηm := m.etaM) (δ := (m.delta : ℝ) + k.delta)
    (Q := (m.Q : ℝ) - k.eta) aRef0'.le ⟨tau0', tauH'.trans (by linarith)⟩ helpInt
    (box_help_integrable _ _ _ _ _) inhibitoryInt wrongInt driftInt gap stateBound actualLaw
    (fun _ _ => rfl) (by simpa using initialError) helpError inhibitorySign wrongSignNonneg
    wrongCharge charge thresholdError
  · intro t ht
    rw [box_reference_eq aRef0' h0 hl0'.le ht.1, box_closed_before (ht.2.trans tauH')]
    nlinarith
  · intro t ht
    have p := peak t (tau0'.trans ht.1)
    nlinarith

/-- Firing from the gate: the rational premises `Order`, `FiringBefore` and
`FiringAfter`, with the measured real hypotheses of the cell (input absent), give a
first contact between `h + early` and `h + hl` under a varying leak. -/
theorem gate_firing (d : Design) (m : Measures) (k : Allowance)
    (order : Order d m k) (firingBefore : FiringBefore d m k) (firingAfter : FiringAfter d m k)
    {actual leak help inhibitory : ℝ → ℝ} {initial actualLevel : ℝ}
    (actualCont : Continuous actual)
    (helpInt : IntervalIntegrable help volume 0 ((d.h : ℝ) + d.hl))
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 ((d.h : ℝ) + d.hl))
    (driftInt : IntervalIntegrable (fun u => (leak u - m.aRef) * actual u) volume 0 ((d.h : ℝ) + d.hl))
    (gap : ∀ u ∈ Icc (0 : ℝ) ((d.h : ℝ) + d.hl), |leak u - m.aRef| ≤ m.alpha)
    (stateBound : ∀ u ∈ Icc (0 : ℝ) ((d.h : ℝ) + d.hl), |actual u| ≤ (d.H0 : ℝ) * d.hl)
    (actualLaw : ∀ t ∈ Icc (0 : ℝ) ((d.h : ℝ) + d.hl), actual t = leakyResponse m.aRef initial
      (fun u => (help u - (leak u - m.aRef) * actual u) - inhibitory u) t)
    (initialError : |initial| ≤ m.eps0)
    (helpError : ∀ t ∈ Icc (0 : ℝ) ((d.h : ℝ) + d.hl),
      (∫ u in 0..t, |help u - boxHelp d.H0 d.h d.hl u|) ≤ (m.etaH : ℝ) + k.eta)
    (offCharge : (∫ u in (0 : ℝ)..((d.h : ℝ) + d.hl), |inhibitory u|) ≤ m.etaJ)
    (thresholdError : |actualLevel - d.level| ≤ (m.delta : ℝ) + k.delta) :
    ∃ root, (d.h : ℝ) + m.early < root ∧ root < (d.h : ℝ) + d.hl ∧ actual root = actualLevel ∧
      ∀ t ∈ Ico 0 root, actual t < actualLevel := by
  obtain ⟨tau0, tauH, hl0, hD, _, _, aRef0, alpha0, _, _, _, H00, _, _, _, _, _, _, _,
    early0, earlyHl, _⟩ := order
  have tau0' : (0 : ℝ) ≤ d.tau := by exact_mod_cast tau0
  have tauH' : (d.tau : ℝ) ≤ d.h := by exact_mod_cast tauH
  have hl0' : (0 : ℝ) < d.hl := by exact_mod_cast hl0
  have hD' : (d.h : ℝ) + d.hl ≤ d.D := by exact_mod_cast hD
  have aRef0' : (0 : ℝ) < m.aRef := by exact_mod_cast aRef0
  have alpha0' : (0 : ℝ) ≤ m.alpha := by exact_mod_cast alpha0
  have H00' : (0 : ℝ) < d.H0 := by exact_mod_cast H00
  have early0' : (0 : ℝ) ≤ m.early := by exact_mod_cast early0
  have earlyHl' : (m.early : ℝ) < d.hl := by exact_mod_cast earlyHl
  have h0 : (0 : ℝ) ≤ d.h := tau0'.trans tauH'
  have before' : ((refUpper d m m.early + firingBudget m k + (m.delta + k.delta) + leakTerm d m : ℚ) : ℝ) <
      d.level := by exact_mod_cast firingBefore
  have after' : (0 : ℝ) < ((firingMargin d m k : ℚ) : ℝ) := by exact_mod_cast firingAfter
  simp only [refUpper, firingBudget, leakTerm, leakBudget, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_sub, expLo_cast] at before'
  simp only [firingMargin, refLower, firingBudget, leakTerm, leakBudget, Rat.cast_sub, Rat.cast_add,
    Rat.cast_mul, Rat.cast_div, expHi_cast] at after'
  push_cast at before' after'
  have scale : 0 ≤ (d.H0 : ℝ) / m.aRef := div_nonneg H00'.le aRef0'.le
  have leakDeadline : (m.alpha : ℝ) * (d.H0 * d.hl) * (d.h + d.hl) ≤ m.alpha * (d.D * d.H0 * d.hl) := by
    have : 0 ≤ (m.alpha : ℝ) * (d.H0 * d.hl) := mul_nonneg alpha0' (mul_nonneg H00'.le hl0'.le)
    nlinarith
  apply uninhibited_first_crossing_varying
    (reference := leakyResponse m.aRef 0 (boxHelp d.H0 d.h d.hl))
    (nominalHelp := boxHelp d.H0 d.h d.hl) (referenceInitial := 0) (X := (d.H0 : ℝ) * d.hl)
    (ε₀ := m.eps0) (ηH := (m.etaH : ℝ) + k.eta) (ηJ := m.etaJ) (δ := (m.delta : ℝ) + k.delta)
    aRef0'.le actualCont helpInt (box_help_integrable _ _ _ _ _) inhibitoryInt driftInt gap stateBound
    ⟨by linarith, by linarith⟩ actualLaw (fun _ _ => rfl) (by simpa using initialError) helpError
    offCharge thresholdError
  · intro t ht
    have window := box_closed_le_window (t := t) aRef0' H00'.le early0' earlyHl'.le ht.2 (ℓ := (d.hl : ℝ))
    rw [box_reference_eq aRef0' h0 hl0'.le ht.1]
    have e := expNegSum_six_le (mul_nonneg aRef0'.le early0')
    have up : (d.H0 : ℝ) / m.aRef * (1 - Real.exp (-(m.aRef : ℝ) * m.early)) ≤
        (d.H0 : ℝ) * (1 - expNegSum 6 ((m.aRef : ℝ) * m.early)) / m.aRef := by
      rw [show -(m.aRef : ℝ) * m.early = -(m.aRef * m.early) by ring]
      have := mul_le_mul_of_nonneg_left (show 1 - Real.exp (-(m.aRef * m.early)) ≤
        1 - expNegSum 6 ((m.aRef : ℝ) * m.early) by linarith) scale
      linarith [show (d.H0 : ℝ) / m.aRef * (1 - expNegSum 6 ((m.aRef : ℝ) * m.early)) =
        (d.H0 : ℝ) * (1 - expNegSum 6 ((m.aRef : ℝ) * m.early)) / m.aRef by ring]
    nlinarith
  · rw [box_reference_eq aRef0' h0 hl0'.le (by linarith), box_closed_at_end hl0']
    have e := exp_le_expNegSum_seven (mul_nonneg aRef0'.le hl0'.le)
    have down : (d.H0 : ℝ) * (1 - expNegSum 7 ((m.aRef : ℝ) * d.hl)) / m.aRef ≤
        (d.H0 : ℝ) / m.aRef * (1 - Real.exp (-(m.aRef : ℝ) * d.hl)) := by
      rw [show -(m.aRef : ℝ) * d.hl = -(m.aRef * d.hl) by ring]
      have := mul_le_mul_of_nonneg_left (show 1 - expNegSum 7 ((m.aRef : ℝ) * d.hl) ≤
        1 - Real.exp (-(m.aRef * d.hl)) by linarith) scale
      linarith [show (d.H0 : ℝ) / m.aRef * (1 - expNegSum 7 ((m.aRef : ℝ) * d.hl)) =
        (d.H0 : ℝ) * (1 - expNegSum 7 ((m.aRef : ℝ) * d.hl)) / m.aRef by ring]
    nlinarith

end KernelR.Circuit.InverterGate
