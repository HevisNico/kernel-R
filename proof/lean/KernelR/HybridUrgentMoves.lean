import KernelR.Hybrid

/-! A positive physical flow cannot bypass a jump already enabled at its start.
This follows directly from strict interior guards, raw support and pending
urgency; no priority between simultaneous jumps is imposed. -/
namespace KernelR.Hybrid

/-- Every pending input is strictly future at the start of a positive flow. -/
theorem Flow.pending_strict_at_start {n θ s u} (f : @Flow n θ s u)
    (d : Delivery n) (hd : d ∈ s.pending) : s.time < d.due :=
  f.positive.trans_le (f.pending_urgent d hd)

/-- All enabled zero-time transitions must be resolved before time can advance. -/
theorem Flow.no_initial_jump {n θ route s u} (f : @Flow n θ s u)
    (v : Snapshot n) : IsEmpty (Jump route s v) := by
  constructor
  intro j
  have hg : BeforeGuards s s.x := by
    simpa only [f.initial] using f.guards s.time ⟨le_rfl, f.positive⟩
  cases j with
  | fire i hm hq =>
      have h := hg.1 i
      simp only [hm] at h
      linarith
  | fastEnd i hm hq =>
      have h := hg.1 i
      simp only [hm] at h
      linarith
  | reopen i hm hq =>
      have h := hg.1 i
      simp only [hm] at h
      linarith
  | mark i p hm hq =>
      have h := hg.2 i p
      simp only [hm] at h
      linarith
  | silent i p hm hq =>
      have h := hg.2 i p
      simp only [hm] at h
      linarith
  | error i p hm hq =>
      have h := hg.2 i p
      simp only [hm] at h
      linarith
  | auxReady i p hm hq =>
      have h := hg.2 i p
      simp only [hm] at h
      linarith
  | arrive d before after hqueue hdue hfree =>
      have hd : d ∈ s.pending := by simp [hqueue]
      have h := f.pending_strict_at_start d hd
      linarith
  | rawEnd i p origin hraw hdue =>
      have h := (f.raw_support i p origin hraw).2
      linarith [f.positive]

end KernelR.Hybrid
