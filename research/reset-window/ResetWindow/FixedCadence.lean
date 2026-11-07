module

public import ResetWindow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace ResetWindow

noncomputable section

/-- The base protocol supplies the request period and the two forcing levels.
A successful request shields the system only for `duration` of that period. -/
structure FixedCadence where
  base : Protocol
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  duration_le_period : duration ≤ base.window

namespace FixedCadence

def suffixRetention (p : FixedCadence) : ℝ :=
  Real.exp (-p.base.rate * (p.base.window - p.duration))

private theorem retention_le_suffix (p : FixedCadence) :
    p.base.retention ≤ p.suffixRetention := by
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg p.base.rate_pos.le p.duration_nonneg]

private theorem suffix_le_one (p : FixedCadence) : p.suffixRetention ≤ 1 :=
  Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.base.rate_pos.le)
      (sub_nonneg.mpr p.duration_le_period))

/-- Effective forcing over the complete period, weighted by the decay after
each part of the interval. This parameter describes the endpoint only. -/
def effectiveLeak (p : FixedCadence) : ℝ :=
  1 - (1 - p.base.leak) * ((p.suffixRetention - p.base.retention) / (1 - p.base.retention))

theorem effectiveLeak_bounds (p : FixedCadence) :
    0 ≤ p.effectiveLeak ∧ p.effectiveLeak ≤ 1 := by
  have hpos := sub_pos.mpr p.base.retention_lt_one
  have hratio0 := div_nonneg (sub_nonneg.mpr p.retention_le_suffix) hpos.le
  have hratio1 : (p.suffixRetention - p.base.retention) / (1 - p.base.retention) ≤ 1 :=
    (div_le_iff₀ hpos).mpr (by linarith [p.suffix_le_one])
  have h := mul_le_mul_of_nonneg_left hratio1 (sub_nonneg.mpr p.base.leak_le_one)
  have h' := mul_nonneg (sub_nonneg.mpr p.base.leak_le_one) hratio0
  unfold effectiveLeak
  constructor <;> linarith [p.base.leak_nonneg]

def endpointProtocol (p : FixedCadence) : Protocol :=
  { p.base with leak := p.effectiveLeak
                leak_nonneg := p.effectiveLeak_bounds.1
                leak_le_one := p.effectiveLeak_bounds.2 }

def phase (p : FixedCadence) (equilibrium load t : ℝ) : ℝ :=
  equilibrium + (load - equilibrium) * Real.exp (-p.base.rate * t)

theorem phase_derivative (p : FixedCadence) (equilibrium load t : ℝ) :
    HasDerivAt (p.phase equilibrium load) (-p.base.rate * (p.phase equilibrium load t - equilibrium)) t := by
  have h := ((hasDerivAt_id t).const_mul (-p.base.rate)).exp
  convert (h.const_mul (load - equilibrium)).const_add equilibrium using 1
  · rfl
  · simp only [phase, id_eq, mul_one]
    ring

/-- After a successful request the protected phase is followed by an
unprotected phase. A blocked request is unprotected for the whole period. -/
def intervalPath (p : FixedCadence) (load t : ℝ) : ℝ :=
  if load < p.base.limit then
    if t ≤ p.duration then p.phase p.base.protectedEquilibrium (load + p.base.impulse) t
    else p.phase p.base.drive
      (p.phase p.base.protectedEquilibrium (load + p.base.impulse) p.duration) (t - p.duration)
  else p.phase p.base.drive (load + p.base.impulse) t

theorem intervalPath_initial (p : FixedCadence) (load : ℝ) :
    p.intervalPath load 0 = load + p.base.impulse := by
  by_cases h : load < p.base.limit <;>
    simp [intervalPath, h, p.duration_nonneg, phase]

private theorem phase_zero (p : FixedCadence) (equilibrium load : ℝ) :
    p.phase equilibrium load 0 = load := by simp [phase]

theorem endpoint_eq (p : FixedCadence) (load : ℝ) :
    p.intervalPath load p.base.window = p.endpointProtocol.advance load := by
  by_cases h : load < p.base.limit
  · have hp : Real.exp (-p.base.rate * p.duration) * p.suffixRetention = p.base.retention := by
      unfold suffixRetention Protocol.retention
      rw [← Real.exp_add]
      congr 1
      ring
    have hend : p.intervalPath load p.base.window = p.phase p.base.drive
        (p.phase p.base.protectedEquilibrium (load + p.base.impulse) p.duration)
        (p.base.window - p.duration) := by
      rcases p.duration_le_period.lt_or_eq with hlt | heq
      · simp [intervalPath, h, not_le_of_gt hlt]
      · simp [intervalPath, h, heq, phase_zero]
    rw [hend]
    change p.base.drive +
      (p.base.protectedEquilibrium +
        (load + p.base.impulse - p.base.protectedEquilibrium) * Real.exp (-p.base.rate * p.duration) -
        p.base.drive) * p.suffixRetention = _
    have hmul : p.effectiveLeak * (1 - p.base.retention) =
        (1 - p.base.retention) - (1 - p.base.leak) * (p.suffixRetention - p.base.retention) := by
      unfold effectiveLeak
      field_simp [(sub_pos.mpr p.base.retention_lt_one).ne']
    have h' : load < p.endpointProtocol.limit := h
    simp only [Protocol.advance, Protocol.intervalPath, Protocol.intervalEquilibrium, ite_eq_left h']
    change _ = p.effectiveLeak * p.base.drive +
      (load + p.base.impulse - p.effectiveLeak * p.base.drive) * p.base.retention
    unfold Protocol.protectedEquilibrium
    calc
      _ = (load + p.base.impulse) * p.base.retention +
          p.base.drive * ((1 - p.base.retention) - (1 - p.base.leak) *
            (p.suffixRetention - p.base.retention)) := by
        linear_combination (load + p.base.impulse - p.base.leak * p.base.drive) * hp
      _ = _ := by rw [← hmul]; ring
  · simp [intervalPath, h, phase, endpointProtocol, Protocol.advance,
      Protocol.intervalPath, Protocol.intervalEquilibrium]

def loadAt (p : FixedCadence) (initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => p.intervalPath (p.loadAt initial n) p.base.window

def Fires (p : FixedCadence) (initial : ℝ) (n : ℕ) : Prop :=
  p.loadAt initial n < p.base.limit

def TerminalSaturation (p : FixedCadence) (initial : ℝ) : Prop :=
  ∃ n : ℕ, ∀ k : ℕ, n ≤ k → ¬ p.Fires initial k

theorem loadAt_eq (p : FixedCadence) (initial : ℝ) (n : ℕ) :
    p.loadAt initial n = p.endpointProtocol.loadAt initial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [loadAt, Protocol.loadAt, ih, p.endpoint_eq]

theorem fires_iff_endpoint (p : FixedCadence) (initial : ℝ) (n : ℕ) :
    p.Fires initial n ↔ p.endpointProtocol.Fires initial n := by
  unfold Fires Protocol.Fires
  rw [p.loadAt_eq]
  rfl

theorem terminalSaturation_iff (p : FixedCadence) {initial : ℝ} (ready : initial < p.base.limit) :
    p.TerminalSaturation initial ↔ p.base.limit < p.endpointProtocol.protectedFixedPoint := by
  change p.TerminalSaturation initial ↔ p.endpointProtocol.limit < p.endpointProtocol.protectedFixedPoint
  simpa only [TerminalSaturation, Protocol.TerminalSaturation, ← p.fires_iff_endpoint] using
    p.endpointProtocol.terminalSaturation_iff ready

/-- With the requests and drive fixed, shortening protection can only raise
the protected fixed point. Terminal saturation persists under compression. -/
theorem terminalSaturation_of_shorter (p : FixedCadence) {initial shorter : ℝ}
    (ready : initial < p.base.limit) (nonneg : 0 ≤ shorter) (short : shorter ≤ p.duration)
    (saturated : p.TerminalSaturation initial) :
    (FixedCadence.mk p.base shorter nonneg (short.trans p.duration_le_period)).TerminalSaturation initial := by
  let q := FixedCadence.mk p.base shorter nonneg (short.trans p.duration_le_period)
  have hs : q.suffixRetention ≤ p.suffixRetention := by
    apply Real.exp_le_exp.mpr
    change -p.base.rate * (p.base.window - shorter) ≤ -p.base.rate * (p.base.window - p.duration)
    exact mul_le_mul_of_nonpos_left (sub_le_sub_left short _) (neg_nonpos.mpr p.base.rate_pos.le)
  have he : p.effectiveLeak ≤ q.effectiveLeak := by
    have hratio := div_le_div_of_nonneg_right (sub_le_sub_right hs p.base.retention)
      (sub_nonneg.mpr p.base.retention_lt_one.le)
    unfold effectiveLeak
    change 1 - (1 - p.base.leak) * ((p.suffixRetention - p.base.retention) / (1 - p.base.retention)) ≤
      1 - (1 - p.base.leak) * ((q.suffixRetention - p.base.retention) / (1 - p.base.retention))
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr p.base.leak_le_one)) 1
  have hf : p.endpointProtocol.protectedFixedPoint ≤ q.endpointProtocol.protectedFixedPoint := by
    let impulseLoad := p.base.impulse / (Real.exp (p.base.rate * p.base.window) - 1)
    change p.effectiveLeak * p.base.drive + impulseLoad ≤ q.effectiveLeak * p.base.drive + impulseLoad
    exact add_le_add (mul_le_mul_of_nonneg_right he
      (p.base.limit_pos.le.trans p.base.drive_ge_limit)) le_rfl
  exact (q.terminalSaturation_iff ready).mpr (((p.terminalSaturation_iff ready).mp saturated).trans_le hf)

theorem blocked_after (p : FixedCadence) {initial : ℝ} {n k : ℕ}
    (blocked : ¬ p.Fires initial n) (later : n ≤ k) : ¬ p.Fires initial k := by
  simp only [p.fires_iff_endpoint] at blocked ⊢
  exact p.endpointProtocol.blocked_after blocked later

theorem intervalPath_stays_blocked (p : FixedCadence) {load t : ℝ}
    (blocked : p.base.limit ≤ load) (ht : 0 ≤ t) :
    p.base.limit ≤ p.intervalPath load t := by
  simpa only [intervalPath, phase, Protocol.intervalPath, Protocol.intervalEquilibrium,
    ite_eq_right (not_lt_of_ge blocked)] using p.base.intervalPath_stays_blocked blocked ht

end FixedCadence
end
end ResetWindow
