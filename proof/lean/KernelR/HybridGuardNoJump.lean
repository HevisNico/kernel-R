import KernelR.Hybrid
/-! Strict interior physical guards and strictly future deadlines exclude every jump. -/
namespace KernelR.Hybrid

/-- Once all physical guards are strict, all active raw expiries are later,
and every pending token is strictly future, no instantaneous move is enabled.
The queue premise deliberately excludes tokens due exactly now. -/
theorem BeforeGuards.no_jump {n route s} (hguard : @BeforeGuards n s s.x)
    (hraw : ∀ i p origin, s.raw i p = some origin → s.time < origin + 1)
    (hpending : ∀ d ∈ s.pending, s.time < d.due) (u : Snapshot n) :
    IsEmpty (Jump route s u) := by
  constructor
  intro jump
  cases jump with
  | fire i mode guard =>
    have h := hguard.1 i
    rw [mode] at h
    linarith
  | fastEnd i mode guard =>
    have h := hguard.1 i
    rw [mode] at h
    linarith
  | reopen i mode guard =>
    have h := hguard.1 i
    rw [mode] at h
    linarith
  | mark i p mode guard =>
    have h := hguard.2 i p
    rw [mode] at h
    linarith
  | silent i p mode guard =>
    have h := hguard.2 i p
    rw [mode] at h
    linarith
  | error i p mode guard =>
    have h := hguard.2 i p
    rw [mode] at h
    linarith
  | auxReady i p mode guard =>
    have h := hguard.2 i p
    rw [mode] at h
    linarith
  | arrive d before after queue due free =>
    have hmem : d ∈ s.pending := by
      rw [queue]
      simp
    have h := hpending d hmem
    rw [due] at h
    exact (lt_irrefl s.time) h
  | rawEnd i p origin active due =>
    have h := hraw i p origin active
    rw [due] at h
    exact (lt_irrefl (origin + 1)) h

end KernelR.Hybrid
