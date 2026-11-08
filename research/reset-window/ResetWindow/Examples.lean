module

public import ResetWindow.FixedCadence
import Mathlib.Tactic.NormNum

@[expose] public section

namespace ResetWindow.Examples

noncomputable section

/-- All experiments use the same request impulse, decay, threshold,
initial load and sustained forcing. -/
def experiment (window leak : ℝ) (hw : 0 < window) (hl : 0 ≤ leak) (hu : leak ≤ 1) : Protocol :=
  ⟨1, window, 1, 1, 2, leak, by norm_num, hw, by norm_num, by norm_num, by norm_num, hl, hu⟩

def ample : Protocol :=
  experiment (Real.log 4) 0 (Real.log_pos (by norm_num)) (by norm_num) (by norm_num)

def compressed : Protocol :=
  experiment (Real.log (3 / 2)) 0 (Real.log_pos (by norm_num)) (by norm_num) (by norm_num)

def leaky : Protocol :=
  experiment (Real.log 4) (1 / 2) (Real.log_pos (by norm_num)) (by norm_num) (by norm_num)

def critical : Protocol :=
  experiment (Real.log 2) 0 (Real.log_pos (by norm_num)) (by norm_num) (by norm_num)

theorem ample_fires_forever : ∀ n, ample.Fires 0 n := by
  apply ample.fires_all_of_fixedPoint_le ample.limit_pos
  norm_num [Protocol.protectedFixedPoint, Protocol.protectedEquilibrium, ample, experiment,
    Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem compressed_first_block_is_two :
    (∀ k < 2, compressed.Fires 0 k) ∧ ∀ k, 2 ≤ k → ¬ compressed.Fires 0 k := by
  have h₁ : compressed.loadAt 0 1 = 2 / 3 := by
    norm_num [Protocol.loadAt, Protocol.advance, Protocol.intervalPath,
      Protocol.intervalEquilibrium, Protocol.protectedEquilibrium, compressed, experiment,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
  have ready₁ : compressed.loadAt 0 1 < compressed.limit := by
    rw [h₁]
    norm_num [compressed, experiment]
  have h₂ : compressed.loadAt 0 2 = 10 / 9 := by
    rw [Protocol.loadAt, Protocol.advance, Protocol.intervalPath,
      Protocol.intervalEquilibrium, ite_eq_left ready₁, h₁]
    norm_num [Protocol.protectedEquilibrium, compressed, experiment,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
  have blocked₂ : ¬ compressed.Fires 0 2 := by
    unfold Protocol.Fires
    rw [h₂]
    norm_num [compressed, experiment]
  refine ⟨?_, fun k hk => compressed.blocked_after blocked₂ hk⟩
  intro k hk
  have he : k = 0 ∨ k = 1 := by omega
  rcases he with rfl | rfl
  · exact compressed.limit_pos
  · exact ready₁

theorem leak_blocks_under_the_same_forcing : leaky.TerminalSaturation 0 := by
  apply (leaky.terminalSaturation_iff leaky.limit_pos).mpr
  apply leaky.overload_of_leak_equilibrium
  norm_num [Protocol.protectedEquilibrium, leaky, experiment]

theorem critical_repeats_without_margin :
    (∀ n, critical.Fires 0 n) ∧ ¬ critical.UniformMargin 0 := by
  have hfixed : critical.protectedFixedPoint = critical.limit := by
    norm_num [Protocol.protectedFixedPoint, Protocol.protectedEquilibrium, critical, experiment,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact ⟨critical.fires_all_of_fixedPoint_le critical.limit_pos hfixed.le,
    fun margin => (not_lt_of_ge hfixed.ge) ((critical.uniformMargin_iff critical.limit_pos).mp margin)⟩

def fullProtection : FixedCadence := ⟨ample, ample.window, ample.window_pos.le, le_rfl⟩

def shortProtection : FixedCadence :=
  ⟨ample, Real.log (11 / 4), (Real.log_pos (by norm_num)).le,
    Real.log_le_log (by norm_num) (by norm_num)⟩

theorem fullProtection_fires_forever : ∀ n, fullProtection.Fires 0 n := by
  have hs : fullProtection.suffixRetention = 1 := by
    change Real.exp (-ample.rate * (ample.window - ample.window)) = 1
    simp
  have hleak : fullProtection.effectiveLeak = 0 := by
    simp only [FixedCadence.effectiveLeak, hs]
    change 1 - (1 - 0) * ((1 - ample.retention) / (1 - ample.retention)) = 0
    rw [div_self (sub_pos.mpr ample.retention_lt_one).ne']
    norm_num
  intro n
  rw [fullProtection.fires_iff_endpoint]
  apply fullProtection.endpointProtocol.fires_all_of_fixedPoint_le ample.limit_pos _ n
  change fullProtection.effectiveLeak * 2 + 1 / (Real.exp (1 * Real.log 4) - 1) ≤ 1
  norm_num [hleak, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem shortProtection_loads :
    shortProtection.loadAt 0 1 = 7 / 8 ∧ shortProtection.loadAt 0 2 = 35 / 32 := by
  let q := shortProtection.endpointProtocol
  have hr : q.retention = 1 / 4 := by
    norm_num [q, FixedCadence.endpointProtocol, Protocol.retention, shortProtection, ample,
      experiment, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have hs : shortProtection.suffixRetention = 11 / 16 := by
    unfold FixedCadence.suffixRetention shortProtection ample experiment
    simp only [neg_mul, one_mul, Real.exp_neg, Real.exp_sub]
    norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 4),
      Real.exp_log (by norm_num : (0 : ℝ) < 11 / 4)]
  have hf : q.protectedFixedPoint = 7 / 6 := by
    have hleak : shortProtection.effectiveLeak = 5 / 12 := by
      change ample.retention = 1 / 4 at hr
      simp only [FixedCadence.effectiveLeak, hs]
      change 1 - (1 - 0) * ((11 / 16 - ample.retention) / (1 - ample.retention)) = _
      rw [hr]
      norm_num
    change shortProtection.effectiveLeak * 2 + 1 / (Real.exp (1 * Real.log 4) - 1) = _
    norm_num [hleak, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have h₁ : q.loadAt 0 1 = 7 / 8 := by
    change q.advance 0 = _
    rw [q.advance_eq_of_ready q.limit_pos, hr, hf]
    norm_num
  have h₂ : q.loadAt 0 2 = 35 / 32 := by
    change q.advance (q.loadAt 0 1) = _
    rw [h₁, q.advance_eq_of_ready (by change (7 / 8 : ℝ) < 1; norm_num), hr, hf]
    norm_num
  simpa only [shortProtection.loadAt_eq] using And.intro h₁ h₂

theorem shortProtection_blocks_at_third_request :
    (∀ k < 2, shortProtection.Fires 0 k) ∧ ∀ k, 2 ≤ k → ¬ shortProtection.Fires 0 k := by
  obtain ⟨h₁, h₂⟩ := shortProtection_loads
  have blocked₂ : ¬ shortProtection.Fires 0 2 := by
    unfold FixedCadence.Fires
    rw [h₂]
    change ¬ (35 / 32 : ℝ) < 1
    norm_num
  refine ⟨?_, fun k hk => shortProtection.blocked_after blocked₂ hk⟩
  intro k hk
  have he : k = 0 ∨ k = 1 := by omega
  rcases he with rfl | rfl
  · exact ample.limit_pos
  · unfold FixedCadence.Fires
    rw [h₁]
    change (7 / 8 : ℝ) < 1
    norm_num

end
end ResetWindow.Examples
