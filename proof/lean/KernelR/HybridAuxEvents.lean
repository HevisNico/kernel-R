import KernelR.HybridEvents

/-! Auxiliary event budgets from the protected SILENT decay, without assuming a
pulse-case word. These count actual auxiliary mode changes at every port. -/
namespace KernelR.Hybrid
open Set

/-- The cap two covers the coarse SILENT charge bound m <= 1. -/
noncomputable def silentPotential {n} (s : Snapshot n) (i : Fin n) (p : Port) : ℝ :=
  if s.aux i p = .silent then min 2 (Real.log (10 * s.x i (.m p)) / Real.log 8) else 0

theorem silentPotential_le_two {n} (s : Snapshot n) (i : Fin n) (p : Port) :
    silentPotential s i p ≤ 2 := by
  unfold silentPotential
  split_ifs
  · exact min_le_left _ _
  · norm_num

theorem silentPotential_of_silent {n} (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : s.aux i p = .silent) (hp : 0 < s.x i (.m p)) (hq : s.x i (.m p) ≤ 1) :
    silentPotential s i p = Real.log (10 * s.x i (.m p)) / Real.log 8 := by
  have hl : Real.log (10 * s.x i (.m p)) ≤ 2 * Real.log 8 := by
    have h := Real.log_le_log (show 0 < 10 * s.x i (.m p) by positivity)
      (show 10 * s.x i (.m p) ≤ (8 : ℝ) ^ 2 by nlinarith)
    simpa [Real.log_pow] using h
  simp only [silentPotential, hm, ↓reduceIte]
  exact min_eq_right ((div_le_iff₀ (by linarith [log_eight_lower])).mpr hl)

/-- Normalized progress: one unit is a complete protected SILENT phase. -/
noncomputable def Flow.silentProgress {n θ s u} (_f : @Flow n θ s u) (i : Fin n) (p : Port) : ℝ :=
  if s.aux i p = .silent then (θ i).ls p / Real.log 8 * (u.time - s.time) else 0

noncomputable def Move.silentProgress {n θ route s u} : @Move n θ route s u → Fin n → Port → ℝ
  | .flow f => f.silentProgress
  | .jump _ => fun _ _ => 0

noncomputable def Execution.silentProgress {n θ route s u} : @Execution n θ route s u → Fin n → Port → ℝ
  | .nil _ => fun _ _ => 0
  | .cons step rest => fun i p => step.silentProgress i p + rest.silentProgress i p

def Jump.silentCount {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port) : ℕ :=
  match j with
  | .silent _ k q _ _ => if k = i ∧ q = p then 1 else 0
  | _ => 0

def Jump.auxCount {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port) : ℕ :=
  match j with
  | .mark _ k q _ _ | .silent _ k q _ _ | .error _ k q _ _ | .auxReady _ k q _ _ =>
    if k = i ∧ q = p then 1 else 0
  | _ => 0

def Move.silentCount {n θ route s u} : @Move n θ route s u → Fin n → Port → ℕ
  | .flow _ => fun _ _ => 0
  | .jump j => j.silentCount

def Move.auxCount {n θ route s u} : @Move n θ route s u → Fin n → Port → ℕ
  | .flow _ => fun _ _ => 0
  | .jump j => j.auxCount

def Execution.silentCount {n θ route s u} : @Execution n θ route s u → Fin n → Port → ℕ
  | .nil _ => fun _ _ => 0
  | .cons step rest => fun i p => step.silentCount i p + rest.silentCount i p

def Execution.auxCount {n θ route s u} : @Execution n θ route s u → Fin n → Port → ℕ
  | .nil _ => fun _ _ => 0
  | .cons step rest => fun i p => step.auxCount i p + rest.auxCount i p

theorem Flow.silent_potential_balance {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port) :
    silentPotential u i p + f.silentProgress i p = silentPotential s i p := by
  by_cases hm : s.aux i p = .silent
  · have ht : u.time ∈ Icc s.time u.time := ⟨f.positive.le, le_rfl⟩
    have hps : 0 < s.x i (.m p) := by
      have hg := (f.guards s.time ⟨le_rfl, f.positive⟩).2 i p
      rw [f.initial, hm] at hg
      linarith
    have hpu : 0 < u.x i (.m p) := by
      simpa only [f.final] using f.protected_aux_positive i p (by simp [hm]) ht
    have hus : u.aux i p = .silent := by simpa [f.aux_fixed] using hm
    rw [silentPotential_of_silent u i p hus hpu (by
      simpa [auxUpper, hus] using (f.upper_region hb hi i).2.2 p),
      silentPotential_of_silent s i p hm hps (by simpa [auxUpper, hm] using (hi i).2.2 p)]
    have hsol := f.aux_decay_solution i p (by simp [hm]) u.time ht
    simp only [hm, f.final] at hsol
    have heq : Real.log (10 * u.x i (.m p)) =
        Real.log (10 * s.x i (.m p)) - (θ i).ls p * (u.time - s.time) := by
      rw [hsol, ← mul_assoc, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
      ring
    rw [heq]
    simp only [Flow.silentProgress, hm, ↓reduceIte]
    ring
  · simp [silentPotential, Flow.silentProgress, hm, f.aux_fixed]

theorem Jump.silent_potential_balance {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) :
    silentPotential u i p = silentPotential s i p + (j.silentCount i p : ℝ) := by
  have hl : Real.log (8 : ℝ) ≠ 0 := ne_of_gt (by linarith [log_eight_lower])
  cases j with
  | mark k q mode guard | silent k q mode guard | error k q mode guard | auxReady k q mode guard =>
    by_cases hk : i = k <;> by_cases hp : p = q
    all_goals first
      | (subst i; subst p; norm_num [silentPotential, Jump.silentCount, setAux, mode, guard, hl])
      | simp [silentPotential, Jump.silentCount, setAux, hk, hp, eq_comm]
  | _ => simp [silentPotential, Jump.silentCount, setMain, setRaw]; rfl

theorem Move.silent_potential_balance {n θ ε route s u} (m : @Move n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port) :
    silentPotential u i p + m.silentProgress i p =
      silentPotential s i p + (m.silentCount i p : ℝ) := by
  cases m with
  | flow f => simpa [Move.silentProgress, Move.silentCount] using f.silent_potential_balance hb hi i p
  | jump j => simpa [Move.silentProgress, Move.silentCount] using j.silent_potential_balance i p

theorem Execution.silent_potential_balance {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port) :
    silentPotential u i p + e.silentProgress i p =
      silentPotential s i p + (e.silentCount i p : ℝ) := by
  induction e with
  | nil => simp [silentProgress, silentCount]
  | cons step rest ih =>
    have hs := step.silent_potential_balance hb hi i p
    have hr := ih (by
      cases step with
      | flow f => exact f.upper_region hb hi
      | jump j => exact j.upper_region hi)
    simp only [silentProgress, silentCount, Nat.cast_add]
    linarith

theorem Move.silentProgress_bounds {n θ ε route s u} (m : @Move n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    0 ≤ m.silentProgress i p ∧ m.silentProgress i p ≤ 2 * (u.time - s.time) := by
  cases m with
  | flow f =>
    have hlog : 0 < Real.log (8 : ℝ) := by linarith [log_eight_lower]
    have hr : 0 < (θ i).ls p / Real.log 8 := div_pos (hb.rates_positive i p).2.1 hlog
    have hu : (θ i).ls p / Real.log 8 ≤ 2 :=
      (div_le_iff₀ hlog).mpr (by linarith [(hb.coarse_upper i p).2.2.1, log_eight_lower])
    simp only [Move.silentProgress, Flow.silentProgress]
    split_ifs
    · exact ⟨mul_nonneg hr.le (by linarith [f.positive]),
        mul_le_mul_of_nonneg_right hu (by linarith [f.positive])⟩
    · constructor <;> linarith [f.positive]
  | jump j => simp [Move.silentProgress, j.time_unchanged]

theorem Execution.silentProgress_bounds {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    0 ≤ e.silentProgress i p ∧ e.silentProgress i p ≤ 2 * (u.time - s.time) := by
  induction e with
  | nil => simp [silentProgress]
  | cons step rest ih =>
    have h := step.silentProgress_bounds hb i p
    simp only [silentProgress]
    constructor <;> linarith [h.1, h.2, ih.1, ih.2]

/-- Rank is a proof counter. SILENT entry raises it by three; each of the
other three real auxiliary transitions lowers it by one. -/
def auxRank : AuxMode → ℕ
  | .mark => 0 | .silent => 3 | .error => 2 | .ready => 1

theorem Jump.aux_rank_balance {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port) :
    j.auxCount i p + auxRank (u.aux i p) = 4 * j.silentCount i p + auxRank (s.aux i p) := by
  cases j with
  | mark k q mode guard | silent k q mode guard | error k q mode guard | auxReady k q mode guard =>
    by_cases hk : i = k <;> by_cases hp : p = q
    all_goals first
      | (subst i; subst p; simp [Jump.auxCount, Jump.silentCount, setAux, mode, auxRank])
      | simp [Jump.auxCount, Jump.silentCount, setAux, hk, hp, eq_comm]
  | _ => simp [Jump.auxCount, Jump.silentCount, setMain, setRaw]

theorem Move.aux_rank_balance {n θ route s u} (m : @Move n θ route s u) (i : Fin n) (p : Port) :
    m.auxCount i p + auxRank (u.aux i p) = 4 * m.silentCount i p + auxRank (s.aux i p) := by
  cases m with
  | flow f => simp [Move.auxCount, Move.silentCount, f.aux_fixed]
  | jump j => exact j.aux_rank_balance i p

theorem Execution.aux_rank_balance {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) :
    e.auxCount i p + auxRank (u.aux i p) = 4 * e.silentCount i p + auxRank (s.aux i p) := by
  induction e with
  | nil => simp [auxCount, silentCount]
  | cons step rest ih =>
    have h := step.aux_rank_balance i p
    simp only [auxCount, silentCount]
    omega

/-- A uniform bound on all four kinds of auxiliary mode changes from birth.
Residual ERROR birth is included; no completed dose is assumed. -/
theorem Execution.aux_count_bound {n θ ε route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    (e.auxCount i p : ℝ) ≤ 8 * u.time + 10 := by
  have h := e.silent_potential_balance hb hs.upper_region i p
  have ht := (e.silentProgress_bounds hb i p).2
  have hp := silentPotential_le_two u i p
  have hz : silentPotential s i p = 0 := by
    rcases ((hs.2.2 i).2.2.2.2 p).2 with ha | ha <;> simp [silentPotential, ha.1]
  have hrank : auxRank (s.aux i p) ≤ 2 := by
    rcases ((hs.2.2 i).2.2.2.2 p).2 with ha | ha <;> simp [auxRank, ha.1]
  have hr := e.aux_rank_balance i p
  have hc : e.auxCount i p ≤ 4 * e.silentCount i p + 2 := by omega
  have hcast := (Nat.cast_le (α := ℝ)).mpr hc
  rw [hz] at h
  rw [hs.1] at ht
  push_cast at hcast
  linarith

end KernelR.Hybrid
