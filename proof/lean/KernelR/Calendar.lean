import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Sound calendar algebra. Arrival/firing latency enclosures remain hypotheses;
the time separation and quiescence implications are proved here. -/
namespace KernelR

theorem routed_latency {f d : ℝ}
    (hf : (1 / 2 : ℝ) ≤ f ∧ f ≤ 9 / 10)
    (hd : (3 / 10 : ℝ) ≤ d ∧ d ≤ 2 / 5) :
    (4 / 5 : ℝ) ≤ f + d ∧ f + d ≤ 13 / 10 := by constructor <;> linarith [hf.1,hf.2,hd.1,hd.2]

theorem jittered_gap {f₁ f₂ d₁ d₂ : ℝ}
    (hf₁ : (1 / 2 : ℝ) ≤ f₁ ∧ f₁ ≤ 9 / 10)
    (hf₂ : (1 / 2 : ℝ) ≤ f₂ ∧ f₂ ≤ 9 / 10)
    (hd₁ : (3 / 10 : ℝ) ≤ d₁ ∧ d₁ ≤ 2 / 5)
    (hd₂ : (3 / 10 : ℝ) ≤ d₂ ∧ d₂ ≤ 2 / 5) :
    (15 / 2 : ℝ) ≤ 8 + f₂ + d₂ - (f₁ + d₁) ∧
    8 + f₂ + d₂ - (f₁ + d₁) ≤ 17 / 2 := by
  constructor <;> linarith [hf₁.1,hf₁.2,hf₂.1,hf₂.2,hd₁.1,hd₁.2,hd₂.1,hd₂.2]

theorem pulse_supports_disjoint {s t : ℝ} (hgap : (15 / 2 : ℝ) ≤ t - s) : s + 1 < t := by linarith

theorem positive_delay_causal {f d : ℝ} (hd : (3 / 10 : ℝ) ≤ d) : f < f + d := by linarith

theorem protected_mark_before_fire {mark fire : ℝ}
    (hm : mark < 3 / 10) (hf : (3 / 10 : ℝ) ≤ fire) : mark < fire := hm.trans_le hf

theorem error_inside_fast {fire es ee : ℝ}
    (hf : (1 / 2 : ℝ) < fire ∧ fire < 9 / 10)
    (hs : (9 / 10 : ℝ) < es) (he : ee < 3 / 2) :
    fire < es ∧ ee < fire + 1 := by constructor <;> linarith [hf.1,hf.2]

theorem stable_return_before_next {ret gap : ℝ}
    (hr : ret < 6990787 / 1000000) (hg : (15 / 2 : ℝ) ≤ gap) : ret < gap := by linarith

theorem final_entry_quiet {ret : ℝ} (hr : ret < 288290787 / 1000000) : ret < 3199 / 10 := by linarith

/-- A fixed latency preserves all inter-pulse intervals exactly. -/
theorem fixed_latency_preserves_intervals (s t latency : ℝ) :
    (t + latency) - (s + latency) = t - s := by ring

theorem two_fixed_latencies_preserve_intervals (s t a b : ℝ) :
    ((t + a) + b) - ((s + a) + b) = t - s := by ring

end KernelR
