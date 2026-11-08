module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A separate load model with periodic requests and event-triggered protection.
An external request adds a load impulse whether or not it emits a transition.
A successful request enables protection for the next interval. An unsuccessful
request leaves the system coupled to the maintained forcing. -/

@[expose] public section

namespace ResetWindow

noncomputable section

/-- `drive` is the load equilibrium under full coupling. The actual constant
inflow under full coupling is `rate * drive`. -/
structure Protocol where
  rate : ℝ
  window : ℝ
  impulse : ℝ
  limit : ℝ
  drive : ℝ
  leak : ℝ
  rate_pos : 0 < rate
  window_pos : 0 < window
  impulse_pos : 0 < impulse
  limit_pos : 0 < limit
  drive_ge_limit : limit ≤ drive
  leak_nonneg : 0 ≤ leak
  leak_le_one : leak ≤ 1

namespace Protocol

def protectedEquilibrium (p : Protocol) : ℝ := p.leak * p.drive

def intervalEquilibrium (p : Protocol) (load : ℝ) : ℝ :=
  if load < p.limit then p.protectedEquilibrium else p.drive

/-- The post-request path starts at the old load plus the external impulse. -/
def intervalPath (p : Protocol) (load t : ℝ) : ℝ :=
  p.intervalEquilibrium load +
    (load + p.impulse - p.intervalEquilibrium load) * Real.exp (-p.rate * t)

theorem intervalPath_initial (p : Protocol) (load : ℝ) :
    p.intervalPath load 0 = load + p.impulse := by
  simp [intervalPath]

/-- Both interval modes solve the declared dissipation-plus-inflow equation. -/
theorem intervalPath_derivative (p : Protocol) (load t : ℝ) :
    HasDerivAt (p.intervalPath load)
      (-p.rate * (p.intervalPath load t - p.intervalEquilibrium load)) t := by
  have h := ((hasDerivAt_id t).const_mul (-p.rate)).exp
  convert (h.const_mul (load + p.impulse - p.intervalEquilibrium load)).const_add
    (p.intervalEquilibrium load) using 1
  · rfl
  · simp only [intervalPath, id_eq, mul_one]
    ring

def advance (p : Protocol) (load : ℝ) : ℝ := p.intervalPath load p.window

/-- Load sampled just before each exogenous request. -/
def loadAt (p : Protocol) (initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => p.advance (p.loadAt initial n)

theorem requests_reach_arbitrarily_late (p : Protocol) (time : ℝ) :
    ∃ n : ℕ, time < (n : ℝ) * p.window := by
  obtain ⟨n, hn⟩ := exists_nat_gt (time / p.window)
  exact ⟨n, (div_lt_iff₀ p.window_pos).mp hn⟩

def Fires (p : Protocol) (initial : ℝ) (n : ℕ) : Prop :=
  p.loadAt initial n < p.limit

def TerminalSaturation (p : Protocol) (initial : ℝ) : Prop :=
  ∃ n : ℕ, ∀ k : ℕ, n ≤ k → ¬ p.Fires initial k

def UniformMargin (p : Protocol) (initial : ℝ) : Prop :=
  ∃ margin : ℝ, 0 < margin ∧ ∀ n : ℕ, p.loadAt initial n ≤ p.limit - margin

def retention (p : Protocol) : ℝ := Real.exp (-p.rate * p.window)

theorem retention_pos (p : Protocol) : 0 < p.retention := Real.exp_pos _

theorem retention_lt_one (p : Protocol) : p.retention < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos p.rate_pos) p.window_pos

private theorem exp_duration_sub_one_pos (p : Protocol) :
    0 < Real.exp (p.rate * p.window) - 1 :=
  sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos p.rate_pos p.window_pos))

/-- Fixed point of the map used while requests are successful. -/
def protectedFixedPoint (p : Protocol) : ℝ :=
  p.protectedEquilibrium + p.impulse / (Real.exp (p.rate * p.window) - 1)

theorem advance_eq_of_ready (p : Protocol) {load : ℝ} (ready : load < p.limit) :
    p.advance load =
      p.retention * load + (1 - p.retention) * p.protectedFixedPoint := by
  have he : Real.exp (p.rate * p.window) ≠ 0 := Real.exp_ne_zero _
  have hg := (p.exp_duration_sub_one_pos).ne'
  simp only [advance, intervalPath, intervalEquilibrium, ite_eq_left ready,
    retention, protectedFixedPoint, neg_mul, Real.exp_neg]
  field_simp
  ring

/-- Once a request finds excessive load, even the continuous path remains
above the rearming level under the maintained full forcing. -/
theorem intervalPath_stays_blocked (p : Protocol) {load t : ℝ}
    (blocked : p.limit ≤ load) (ht : 0 ≤ t) :
    p.limit ≤ p.intervalPath load t := by
  have hr : 0 ≤ Real.exp (-p.rate * t) := (Real.exp_pos _).le
  have hr' : Real.exp (-p.rate * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.rate_pos.le) ht)
  have hload : p.limit ≤ load + p.impulse := by linarith [p.impulse_pos]
  have h1 := mul_le_mul_of_nonneg_left hload hr
  have h2 := mul_le_mul_of_nonneg_left p.drive_ge_limit (sub_nonneg.mpr hr')
  simp only [intervalPath, intervalEquilibrium, ite_eq_right (not_lt_of_ge blocked)]
  nlinarith only [h1, h2]

theorem blocked_after (p : Protocol) {initial : ℝ} {n k : ℕ}
    (blocked : ¬ p.Fires initial n) (later : n ≤ k) : ¬ p.Fires initial k := by
  induction later with
  | refl => exact blocked
  | step _ ih =>
    unfold Fires at ih ⊢
    rw [loadAt]
    exact not_lt_of_ge (p.intervalPath_stays_blocked (le_of_not_gt ih) p.window_pos.le)

theorem fires_all_of_fixedPoint_le (p : Protocol) {initial : ℝ}
    (ready : initial < p.limit) (safe : p.protectedFixedPoint ≤ p.limit) :
    ∀ n : ℕ, p.Fires initial n := by
  intro n
  induction n with
  | zero => exact ready
  | succ n ih =>
    change p.loadAt initial n < p.limit at ih
    change p.advance (p.loadAt initial n) < p.limit
    rw [p.advance_eq_of_ready ih]
    have hx := mul_lt_mul_of_pos_left ih p.retention_pos
    have hf := mul_le_mul_of_nonneg_left safe (sub_nonneg.mpr p.retention_lt_one.le)
    nlinarith only [hx, hf]

/-- Every successful interval below the given bound gains at least the
corresponding distance-to-fixed-point times the fraction dissipated. -/
theorem drift_bound (p : Protocol) (initial bound : ℝ) (n : ℕ)
    (ready : ∀ k < n, p.Fires initial k)
    (bounded : ∀ k < n, p.loadAt initial k ≤ bound) :
    initial + (n : ℝ) * ((1 - p.retention) * (p.protectedFixedPoint - bound))
      ≤ p.loadAt initial n := by
  induction n with
  | zero => simp [loadAt]
  | succ n ih =>
    have hr := ready n (Nat.lt_succ_self n)
    have hb := bounded n (Nat.lt_succ_self n)
    have hprev := ih (fun k hk => ready k (Nat.lt_succ_of_lt hk))
      (fun k hk => bounded k (Nat.lt_succ_of_lt hk))
    have hdelta := mul_le_mul_of_nonneg_left
      (sub_le_sub_left hb p.protectedFixedPoint) (sub_nonneg.mpr p.retention_lt_one.le)
    change p.loadAt initial n < p.limit at hr
    rw [loadAt, p.advance_eq_of_ready hr, Nat.cast_succ]
    nlinarith only [hprev, hdelta]

/-- A quantitative upper bound on the index of the first blocked request. -/
theorem blocked_by (p : Protocol) {initial : ℝ} (n : ℕ)
    (budget : p.limit - initial ≤
      (n : ℝ) * ((1 - p.retention) * (p.protectedFixedPoint - p.limit))) :
    ¬ p.Fires initial n := by
  intro fires
  have before : ∀ k < n, p.Fires initial k := by
    intro k hk
    by_contra h
    exact p.blocked_after h hk.le fires
  have hb := p.drift_bound initial p.limit n before (fun k hk => (before k hk).le)
  change p.loadAt initial n < p.limit at fires
  linarith

theorem load_increases_of_overload (p : Protocol) {initial : ℝ} {n : ℕ}
    (ready : p.Fires initial n) (overload : p.limit < p.protectedFixedPoint) :
    p.loadAt initial n < p.loadAt initial (n + 1) := by
  change p.loadAt initial n < p.limit at ready
  have h := mul_pos (sub_pos.mpr p.retention_lt_one) (sub_pos.mpr (ready.trans overload))
  rw [loadAt, p.advance_eq_of_ready ready]
  nlinarith only [h]

/-- Exact initial segment of successful transitions followed by permanent block. -/
theorem first_block (p : Protocol) (initial : ℝ)
    (overload : p.limit < p.protectedFixedPoint) :
    ∃ n : ℕ, (∀ k < n, p.Fires initial k) ∧
      ∀ k : ℕ, n ≤ k → ¬ p.Fires initial k := by
  classical
  let delta := (1 - p.retention) * (p.protectedFixedPoint - p.limit)
  have hdelta : 0 < delta := mul_pos (sub_pos.mpr p.retention_lt_one) (sub_pos.mpr overload)
  obtain ⟨n, hn⟩ := exists_nat_gt ((p.limit - initial) / delta)
  have hex : ∃ k : ℕ, ¬ p.Fires initial k :=
    ⟨n, p.blocked_by n ((div_lt_iff₀ hdelta).mp hn).le⟩
  refine ⟨Nat.find hex, ?_, fun k hk => p.blocked_after (Nat.find_spec hex) hk⟩
  intro k hk
  by_contra h
  exact Nat.find_min hex hk h

theorem terminalSaturation_iff (p : Protocol) {initial : ℝ}
    (ready : initial < p.limit) :
    p.TerminalSaturation initial ↔ p.limit < p.protectedFixedPoint := by
  constructor
  · rintro ⟨n, blocked⟩
    by_contra! safe
    exact blocked n le_rfl (p.fires_all_of_fixedPoint_le ready safe n)
  · intro overload
    obtain ⟨n, _, blocked⟩ := p.first_block initial overload
    exact ⟨n, blocked⟩

theorem repeats_iff (p : Protocol) {initial : ℝ} (ready : initial < p.limit) :
    (∀ n : ℕ, p.Fires initial n) ↔ p.protectedFixedPoint ≤ p.limit := by
  constructor
  · intro all
    by_contra! overload
    obtain ⟨n, _, blocked⟩ := p.first_block initial overload
    exact blocked n le_rfl (all n)
  · exact p.fires_all_of_fixedPoint_le ready

/-- Critical equality permits every finite request but no positive safety margin. -/
theorem uniformMargin_iff (p : Protocol) {initial : ℝ} (ready : initial < p.limit) :
    p.UniformMargin initial ↔ p.protectedFixedPoint < p.limit := by
  constructor
  · rintro ⟨margin, positive, hbound⟩
    by_contra! hover
    let bound := p.limit - margin
    let delta := (1 - p.retention) * (p.protectedFixedPoint - bound)
    have hd : 0 < delta := mul_pos (sub_pos.mpr p.retention_lt_one) (by dsimp [bound]; linarith)
    obtain ⟨n, hn⟩ := exists_nat_gt ((bound - initial) / delta)
    have hlarge := (div_lt_iff₀ hd).mp hn
    have hloads : ∀ k : ℕ, p.loadAt initial k ≤ bound := hbound
    have hall : ∀ k : ℕ, p.Fires initial k := fun k => (hloads k).trans_lt (by dsimp [bound]; linarith)
    have hsmall := p.drift_bound initial bound n (fun k _ => hall k) (fun k _ => hloads k)
    change initial + (n : ℝ) * delta ≤ p.loadAt initial n at hsmall
    linarith only [hsmall, hloads n, hlarge]
  · intro hfixed
    let bound := max initial p.protectedFixedPoint
    have hbound : bound < p.limit := max_lt_iff.mpr ⟨ready, hfixed⟩
    refine ⟨p.limit - bound, sub_pos.mpr hbound, ?_⟩
    have all : ∀ n : ℕ, p.loadAt initial n ≤ bound := by
      intro n
      induction n with
      | zero => exact le_max_left _ _
      | succ n ih =>
        change p.advance (p.loadAt initial n) ≤ bound
        rw [p.advance_eq_of_ready (ih.trans_lt hbound)]
        have h1 := mul_le_mul_of_nonneg_left ih p.retention_pos.le
        have h2 := mul_le_mul_of_nonneg_left (le_max_right initial p.protectedFixedPoint)
          (sub_nonneg.mpr p.retention_lt_one.le)
        nlinarith only [h1, h2]
    intro n
    linarith [all n]

def criticalWindow (p : Protocol) : ℝ :=
  Real.log (1 + p.impulse / (p.limit - p.protectedEquilibrium)) / p.rate

theorem fixedPoint_le_iff_window (p : Protocol)
    (room : p.protectedEquilibrium < p.limit) :
    p.protectedFixedPoint ≤ p.limit ↔ p.criticalWindow ≤ p.window := by
  have hroom := sub_pos.mpr room
  have harg : 0 < 1 + p.impulse / (p.limit - p.protectedEquilibrium) :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg p.impulse_pos.le hroom.le)
  calc
    p.protectedFixedPoint ≤ p.limit ↔
        p.impulse / (Real.exp (p.rate * p.window) - 1) ≤
          p.limit - p.protectedEquilibrium := by unfold protectedFixedPoint; constructor <;> intro h <;> linarith
    _ ↔ p.impulse ≤ (p.limit - p.protectedEquilibrium) *
          (Real.exp (p.rate * p.window) - 1) := div_le_iff₀ p.exp_duration_sub_one_pos
    _ ↔ 1 + p.impulse / (p.limit - p.protectedEquilibrium) ≤ Real.exp (p.rate * p.window) := by
      constructor
      · intro h
        have hd := (div_le_iff₀ hroom).mpr (by simpa only [mul_comm] using h)
        linarith
      · intro h
        have hd : p.impulse / (p.limit - p.protectedEquilibrium) ≤
            Real.exp (p.rate * p.window) - 1 := by linarith
        simpa only [mul_comm] using (div_le_iff₀ hroom).mp hd
    _ ↔ Real.log (1 + p.impulse / (p.limit - p.protectedEquilibrium)) ≤ p.rate * p.window := by
      constructor
      · intro h
        apply Real.exp_le_exp.mp
        simpa only [Real.exp_log harg] using h
      · intro h
        simpa only [Real.exp_log harg] using Real.exp_le_exp.mpr h
    _ ↔ p.criticalWindow ≤ p.window := by
      rw [criticalWindow, div_le_iff₀ p.rate_pos, mul_comm]

theorem terminalSaturation_iff_short_window (p : Protocol) {initial : ℝ}
    (ready : initial < p.limit) (room : p.protectedEquilibrium < p.limit) :
    p.TerminalSaturation initial ↔ p.window < p.criticalWindow := by
  rw [p.terminalSaturation_iff ready, ← not_le, p.fixedPoint_le_iff_window room, not_le]

theorem overload_of_leak_equilibrium (p : Protocol)
    (leakHigh : p.limit ≤ p.protectedEquilibrium) :
    p.limit < p.protectedFixedPoint := by
  unfold protectedFixedPoint
  linarith [div_pos p.impulse_pos p.exp_duration_sub_one_pos]

def withDrive (p : Protocol) (drive : ℝ) (strong : p.limit ≤ drive) : Protocol :=
  { p with drive := drive, drive_ge_limit := strong }

/-- Every sustained forcing amplitude above the strong-drive floor admits
indefinitely many requests, with all other parameters fixed. -/
def RobustRecursion (p : Protocol) (initial : ℝ) : Prop :=
  ∀ drive : ℝ, ∀ strong : p.limit ≤ drive, ∀ n : ℕ, (p.withDrive drive strong).Fires initial n

/-- In this linear leakage family, exact decoupling and adequate duration are
necessary and sufficient for repetition under arbitrarily large forcing. -/
theorem robustRecursion_iff (p : Protocol) {initial : ℝ} (ready : initial < p.limit) :
    p.RobustRecursion initial ↔
      p.leak = 0 ∧ Real.log (1 + p.impulse / p.limit) / p.rate ≤ p.window := by
  constructor
  · intro robust
    have hz : p.leak = 0 := by
      by_contra h
      have hp : 0 < p.leak := lt_of_le_of_ne p.leak_nonneg (Ne.symm h)
      let drive := p.limit / p.leak
      have hd : p.limit ≤ drive :=
        (le_div_iff₀ hp).mpr (by nlinarith [mul_le_mul_of_nonneg_left p.leak_le_one p.limit_pos.le])
      let q := p.withDrive drive hd
      have he : q.protectedEquilibrium = p.limit := by
        change p.leak * (p.limit / p.leak) = p.limit
        field_simp
      have hf := (q.repeats_iff ready).mp (robust drive hd)
      exact not_lt_of_ge hf (q.overload_of_leak_equilibrium he.ge)
    have hroom : p.protectedEquilibrium < p.limit := by simpa [protectedEquilibrium, hz] using p.limit_pos
    have hf := (p.repeats_iff ready).mp (robust p.drive p.drive_ge_limit)
    refine ⟨hz, ?_⟩
    simpa [criticalWindow, protectedEquilibrium, hz] using (p.fixedPoint_le_iff_window hroom).mp hf
  · rintro ⟨hz, htime⟩ drive strong
    let q := p.withDrive drive strong
    have he : q.protectedEquilibrium = 0 := by change p.leak * drive = 0; simp [hz]
    have hroom : q.protectedEquilibrium < q.limit := he ▸ p.limit_pos
    apply (q.repeats_iff ready).mpr
    apply (q.fixedPoint_le_iff_window hroom).mpr
    change Real.log (1 + p.impulse / (p.limit - q.protectedEquilibrium)) / p.rate ≤ p.window
    simpa only [he, sub_zero] using htime

end Protocol
end
end ResetWindow
