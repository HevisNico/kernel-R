import KernelR.HybridFeedbackFireProjection
import KernelR.HybridSameGainLatency

/-! Actual own response roots, rather than assumed firing calendars, control
the spacing of reciprocal contacts. The first residual root may be earlier. -/
namespace KernelR.Hybrid

theorem FirstLearnedFire.latency_eq_rest_reference {n θ route s i p}
    (c : @FirstLearnedFire n θ route s i p) (hq : s.x i .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5) :
    c.latency = restLatency (Real.exp (s.x i (.z p))) := by
  have hroot := c.response_root
  rw [hq] at hroot
  have href := restLatency_spec hg
  exact readyPulse_rest_roots_same_latency (sourceA := s.time) (sourceB := 0) (Real.exp_pos _)
    ⟨by linarith [c.early],c.deadline.le⟩
    ⟨by linarith [href.1],href.2.1.le⟩ hroot (by simpa only [zero_add] using href.2.2)

/-- A lower bound suffices for the first received gap. It deliberately does
not assert the regular eight-period upper bound for the first residual FIRE. -/
theorem received_gap_of_firing_lower {first second delayFirst delaySecond : ℝ}
    (hfire : first + 8 ≤ second)
    (hfirst : 3 / 10 ≤ delayFirst ∧ delayFirst ≤ 2 / 5)
    (hsecond : 3 / 10 ≤ delaySecond ∧ delaySecond ≤ 2 / 5) :
    first + delayFirst + 79 / 10 ≤ second + delaySecond := by
  linarith [hfirst.2,hsecond.1]

/-- Independent resting responses with the same own gain have the same
root latency. Only the external sources are spaced by eight. -/
theorem FirstLearnedFire.rest_fire_gap {θ : Fin 1 → Parameters} {route : Router 1}
    {s t : Snapshot 1} {p : Port}
    (first : FirstLearnedFire θ route s 0 p)
    (second : FirstLearnedFire θ route t 0 p)
    (hqS : s.x 0 .q = 1 / 10) (hqT : t.x 0 .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 12 / 5)
    (hz : t.x 0 (.z p) = s.x 0 (.z p)) (ht : t.time = s.time + 8) :
    second.final.time = first.final.time + 8 := by
  have hgT : 9 / 5 ≤ Real.exp (t.x 0 (.z p)) ∧ Real.exp (t.x 0 (.z p)) ≤ 12 / 5 := by
    rw [hz]
    exact hg
  rw [first.date,second.date,first.latency_eq_rest_reference hqS hg,
    second.latency_eq_rest_reference hqT hgT,hz,ht]
  ring

/-- Fresh delay samples may differ; the real received gap is bounded from
the two actual resting FIRE roots, with no shared latency assumption. -/
theorem FirstLearnedFire.rest_receipt_gap {θ : Fin 1 → Parameters} {route : Router 1}
    {s t : Snapshot 1} {p : Port} (delay : ℝ → ℝ)
    (first : FirstLearnedFire θ route s 0 p)
    (second : FirstLearnedFire θ route t 0 p)
    (hqS : s.x 0 .q = 1 / 10) (hqT : t.x 0 .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 12 / 5)
    (hz : t.x 0 (.z p) = s.x 0 (.z p)) (ht : t.time = s.time + 8)
    (hd : ∀ F, (3 / 10 : ℝ) ≤ delay F ∧ delay F ≤ 2 / 5) :
    first.final.time + delay first.final.time + 79 / 10 ≤
      second.final.time + delay second.final.time ∧
      second.final.time + delay second.final.time ≤
        first.final.time + delay first.final.time + 81 / 10 := by
  have hfire := first.rest_fire_gap second hqS hqT hg hz ht
  constructor <;> linarith [(hd first.final.time).1,(hd first.final.time).2,
    (hd second.final.time).1,(hd second.final.time).2]

namespace FeedbackFirstFire
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start} (f : FeedbackFirstFire w)

/-- The next own resting response is constructed independently. Preserved
gain and the first root's actual residual bound give its real firing gap. -/
theorem next_rest_fire_gap {sB : Snapshot 1}
    (next : FirstLearnedFire f.parametersB (fun _ _ => []) sB 0 2)
    (hq : sB.x 0 .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (sB.x 0 (.z 2)) ∧ Real.exp (sB.x 0 (.z 2)) ≤ 12 / 5)
    (hz : sB.x 0 (.z 2) = w.final.x 1 (.z 2))
    (ht : sB.time = w.final.time + 8) :
    f.final.time + 8 ≤ next.final.time := by
  have hlat := next.latency_eq_rest_reference hq hg
  have hf : f.final.time = w.final.time + f.firing.latency := f.firing.date
  rw [next.date,hlat,hz,ht,hf]
  linarith [f.first_le_rest]

theorem next_rest_receipt_gap {sB : Snapshot 1}
    (next : FirstLearnedFire f.parametersB (fun _ _ => []) sB 0 2)
    (hq : sB.x 0 .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (sB.x 0 (.z 2)) ∧ Real.exp (sB.x 0 (.z 2)) ≤ 12 / 5)
    (hz : sB.x 0 (.z 2) = w.final.x 1 (.z 2))
    (ht : sB.time = w.final.time + 8)
    (hd : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    f.final.time + backward f.final.time + 79 / 10 ≤ next.final.time + backward next.final.time :=
  received_gap_of_firing_lower (f.next_rest_fire_gap next hq hg hz ht)
    (hd f.final.time) (hd next.final.time)

end FeedbackFirstFire
end KernelR.Hybrid
