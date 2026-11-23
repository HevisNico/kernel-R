/-! The inverter instance gate: the single source of its definitions. Core Lean
only (no Mathlib), over `Rat`, so that both the per-instance gate files (checked by
`decide +kernel`) and the Mathlib bridge (`CircuitInverterGateProof.lean`) import
the same constants.

The definitions are the instance worker's interface (`InverterInstanceCheck.lean`,
commits cd8823e and d952021 on its branch research/inverter-instances), with its
names and formulas, plus `StateBound`. -/

namespace KernelR.Circuit.Gate

structure Design where
  tau : Rat
  h : Rat
  hl : Rat
  H0 : Rat
  D : Rat
  level : Rat

structure Measures where
  aLo : Rat
  aHi : Rat
  aRef : Rat
  alpha : Rat
  eps0 : Rat
  etaH : Rat
  etaM : Rat
  etaJ : Rat
  delta : Rat
  Q : Rat
  latchLo : Rat
  latchHi : Rat
  emit : Rat
  early : Rat

structure Allowance where
  delta : Rat
  eta : Rat

def expLo (x : Rat) : Rat := 1 - x + x * x / 2 - x * x * x / 6 + x * x * x * x / 24 - x * x * x * x * x / 120
def expHi (x : Rat) : Rat := expLo x + x * x * x * x * x * x / 720
def refUpper (d : Design) (m : Measures) (y : Rat) : Rat := d.H0 * (1 - expLo (m.aRef * y)) / m.aRef
def refLower (d : Design) (m : Measures) (y : Rat) : Rat := d.H0 * (1 - expHi (m.aRef * y)) / m.aRef
def leakBudget (d : Design) : Rat := d.D * d.H0 * d.hl
def leakTerm (d : Design) (m : Measures) : Rat := m.alpha * leakBudget d
def silenceBudget (m : Measures) (k : Allowance) : Rat := m.eps0 + m.etaH + m.etaM + k.eta
def firingBudget (m : Measures) (k : Allowance) : Rat := m.eps0 + m.etaH + m.etaJ + k.eta

def silenceMargin (d : Design) (m : Measures) (k : Allowance) : Rat :=
  d.level + expLo ((m.aRef + m.alpha) * d.D) * (m.Q - k.eta) -
    (refUpper d m d.hl + silenceBudget m k + (m.delta + k.delta) + leakTerm d m)

def firingMargin (d : Design) (m : Measures) (k : Allowance) : Rat :=
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

/-- The measured state bound: the largest `|x|` with the input present (over `[0, D]`)
and absent (over `[0, h + hl]`) stays within `H0 * hl`. -/
def StateBound (d : Design) (xPresent xAbsent : Rat) : Prop :=
  0 ≤ xPresent ∧ xPresent ≤ d.H0 * d.hl ∧ 0 ≤ xAbsent ∧ xAbsent ≤ d.H0 * d.hl

instance (d : Design) (m : Measures) (k : Allowance) : Decidable (Order d m k) := by
  unfold Order; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) : Decidable (SilenceBefore d m k) := by
  unfold SilenceBefore; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) : Decidable (SilenceAfter d m k) := by
  unfold SilenceAfter; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) : Decidable (FiringBefore d m k) := by
  unfold FiringBefore; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) : Decidable (FiringAfter d m k) := by
  unfold FiringAfter; infer_instance
instance (d : Design) (xPresent xAbsent : Rat) : Decidable (StateBound d xPresent xAbsent) := by
  unfold StateBound; infer_instance

end KernelR.Circuit.Gate
