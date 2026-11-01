import KernelR.HybridClipping
/-! Physical bounds and reserve-derived exposure at any current starting state. -/
namespace KernelR.Hybrid
open Set

/-- Current physical bounds, independent of the birth date or nominal memories. -/
structure PhysicalInvariant {n} (θ : Fin n → Parameters) (s : Snapshot n) : Prop where
  region : UpperRegion s
  gain_cap : ∀ i p, s.x i (.z p) ≤ Real.log ((θ i).cap p)
  recovery_cap : ∀ i, s.x i .b ≤ 11 / 10
  reserve : ∀ i, 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100

theorem BirthState.physical_invariant {n θ ε s} (hs : @BirthState n s) (hb : PhysicalBox θ ε) :
    PhysicalInvariant θ s := by
  exact ⟨hs.upper_region,fun i p => hs.initial_gain_cap hb i p,
    fun i => by linarith [(hs.2.2 i).2.2.1.2],fun i => (hs.2.2 i).2.2.2.1⟩

theorem Execution.physical_invariant {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) : PhysicalInvariant θ u := by
  exact ⟨e.upper_region hb hs.region,fun i p => e.gain_cap i p (hs.gain_cap i p),
    fun i => e.recovery_cap i (hs.recovery_cap i),
    fun i => e.reserve_invariant i (hs.reserve i) (e.actual_work_bound hb hs.region hs.gain_cap i)⟩

theorem Flow.power_gate_open_of_invariant {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) (i : Fin n) :
    ∀ t ∈ Icc s.time u.time, 0 < f.path t i .energy := by
  have h := f.reserve_invariant_on hb hs.region hs.gain_cap i (hs.reserve i)
  intro t ht
  linarith [(h t ht).1]

theorem Flow.mark_open_of_invariant {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) (i : Fin n) (p : Port)
    (ha : s.aux i p = .mark) (hm : s.main i ≠ .ready)
    (hcap : ∀ t ∈ Icc s.time u.time, f.path t i .b < 11 / 10) : MarkOpen f i p :=
  ⟨ha,hm,fun t ht => ⟨f.power_gate_open_of_invariant hb hs i t ht,hcap t ht⟩⟩

theorem Flow.error_open_of_invariant {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) (i : Fin n) (p : Port)
    (ha : s.aux i p = .error) (hm : s.main i = .ready)
    (hcap : ∀ t ∈ Icc s.time u.time, f.path t i (.z p) < Real.log ((θ i).cap p)) : ErrorOpen f i p :=
  ⟨ha,hm,fun t ht => ⟨f.power_gate_open_of_invariant hb hs i t ht,hcap t ht⟩⟩

theorem Execution.error_exposed_of_invariant {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) (i : Fin n) (p : Port)
    (ha : e.AuxFlows i p .error) (hm : e.MainFlows i .ready)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p)) :
    e.ErrorExposed i p := by
  induction e with
  | nil => trivial
  | @cons s v u move rest ih =>
    have hnext := (.cons move (.nil _) : Execution θ route s v).physical_invariant hb hs
    cases move with
    | flow f =>
      refine ⟨f.error_open_of_invariant hb hs i p ha.1 hm.1
        (f.error_cap_open_of_headroom hb i p ha.1 hh),?_⟩
      apply ih hnext ha.2 hm.2
      have h := f.error_gain_budget hb i p ha.1
      linarith
    | jump j =>
      apply ih hnext ha hm
      simpa only [j.physical_continuous] using hh

end KernelR.Hybrid
