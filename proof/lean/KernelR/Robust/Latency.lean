import FirstCrossing
import KernelR.Robust.Noise

/-! First-crossing stability about a cell's own fixed learned-gain response.
The analytic envelope and uniform response increment are explicit premises.
The rational certificates check their proposed numerical margins separately. -/
namespace KernelR.Robust
open A22.Crossing

/-- Concavity makes a fixed-width response increment decrease with its location.
This justifies testing the rightmost reference root for both timing margins. -/
theorem increment_antitone {h : ℝ → ℝ} {lo hi δ : ℝ}
    (hd : Differentiable ℝ h) (hδ : 0 ≤ δ)
    (ha : AntitoneOn (deriv h) (Set.Icc lo (hi+δ))) :
    AntitoneOn (fun t => h (t+δ) - h t) (Set.Icc lo hi) := by
  have derivative : ∀ t, HasDerivAt (fun x => h (x+δ)-h x)
      (deriv h (t+δ)-deriv h t) t := by
    intro t
    exact (HasDerivAt.comp_add_const t δ (hd (t+δ)).hasDerivAt).sub (hd t).hasDerivAt
  apply antitoneOn_of_deriv_nonpos (convex_Icc lo hi)
  · exact (continuous_iff_continuousAt.mpr (fun t => (derivative t).continuousAt)).continuousOn
  · intro t ht
    exact (derivative t).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Set.Icc lo hi := interior_subset ht
    rw [(derivative t).deriv]
    have hm := ha (show t ∈ Set.Icc lo (hi+δ) by constructor <;> linarith [ht'.1, ht'.2])
      (show t+δ ∈ Set.Icc lo (hi+δ) by constructor <;> linarith [ht'.1, ht'.2])
      (show t ≤ t+δ by linarith)
    linarith

theorem concave_increment_lower {h : ℝ → ℝ} {lo hi δ root : ℝ}
    (hd : Differentiable ℝ h) (hc : ConcaveOn ℝ (Set.Icc lo (hi+δ)) h)
    (hδ : 0 ≤ δ) (hr : root ∈ Set.Icc lo hi) :
    h (hi+δ)-h hi ≤ h (root+δ)-h root := by
  exact increment_antitone hd hδ (hc.antitoneOn_deriv (fun t _ => hd t))
    hr ⟨by linarith [hr.1, hr.2], le_rfl⟩ hr.2

/-- Direct finite-increment form used by the interval certificates. The upper
envelope is monotone up to the early time, so one endpoint excludes all earlier
crossings. The lower envelope is needed only at the late time. -/
theorem crossing_radius_of_increments {q reference envelope : ℝ → ℝ}
    {start finish root δ earlyError lateError : ℝ}
    (crossing : IsFirstCrossing q start finish)
    (root_value : reference root = 1)
    (hδ : 0 ≤ δ) (hstart : start ≤ root-δ)
    (upper : ∀ t ∈ Set.Ico start (root-δ), q t ≤ envelope t)
    (mono : MonotoneOn envelope (Set.Icc start (root-δ)))
    (earlyEnvelope : envelope (root-δ) ≤ reference (root-δ)+earlyError)
    (earlyMargin : earlyError < reference root-reference (root-δ))
    (lateEnvelope : reference (root+δ)-lateError ≤ q (root+δ))
    (lateMargin : lateError < reference (root+δ)-reference root) :
    root-δ ≤ finish ∧ finish ≤ root+δ := by
  apply cover_encloses crossing
  · intro t ht
    have hm := mono ⟨ht.1, ht.2.le⟩ ⟨hstart, le_rfl⟩ ht.2.le
    have hu := upper t ht
    linarith
  · linarith
  · linarith

/-- A uniform secant lower bound turns a charge perturbation into a time radius.
The early argument covers the whole interval, not just one endpoint. -/
theorem crossing_radius {q reference : ℝ → ℝ} {start finish root δ E slope : ℝ}
    (crossing : IsFirstCrossing q start finish)
    (root_value : reference root = 1)
    (hδ : 0 ≤ δ) (hstart : start ≤ root + δ)
    (hslope : 0 < slope) (margin : E < slope * δ)
    (early : ∀ t ∈ Set.Ico start (root - δ),
      slope * (root - t) ≤ reference root - reference t)
    (late : slope * δ ≤ reference (root + δ) - reference root)
    (upper : ∀ t ∈ Set.Ico start (root - δ), q t ≤ reference t + E)
    (lower : reference (root + δ) - E ≤ q (root + δ)) :
    root - δ ≤ finish ∧ finish ≤ root + δ := by
  apply cover_encloses crossing
  · intro t ht
    have hinc := early t ht
    have hq := upper t ht
    have hdist : slope * δ ≤ slope * (root - t) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.2]) (le_of_lt hslope)
    linarith
  · exact hstart
  · linarith

theorem radius_iff_abs {finish root δ : ℝ} :
    (root - δ ≤ finish ∧ finish ≤ root + δ) ↔ |finish - root| ≤ δ := by
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Positive residual charge needs only a one-sided latency estimate. -/
theorem first_crossing_late_bound {q reference : ℝ → ℝ} {start finish root δ E : ℝ}
    (crossing : IsFirstCrossing q start finish)
    (hs : start ≤ root + δ)
    (separation : 1 + E ≤ reference (root + δ))
    (lower : reference (root + δ) - E ≤ q (root + δ)) :
    finish ≤ root + δ := by
  by_contra h
  have hbefore := crossing.2.2 (root + δ) ⟨hs, by linarith⟩
  linarith

theorem noiseless_same_latency {q reference : ℝ → ℝ} {start finish root : ℝ}
    (hq : IsFirstCrossing q start finish)
    (hr : IsFirstCrossing reference start root) (same : q = reference) :
    finish = root := by
  subst q
  exact first_crossing_unique hq hr

end KernelR.Robust
