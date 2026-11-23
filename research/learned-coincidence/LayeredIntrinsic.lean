import LayeredTrainingChain

/-! The assumption on `λmax`, made explicit. A cell has an intrinsic delay in
`[dmin, dmax]`, measured from the later of its read start and its last arrival to its
emission. Inside a read window of width `skew`, the arrival spread is at most `skew`.
So the emission lies in `[start + dmin, start + skew + dmax]`, and the latency premise
holds for every `λmax` with

    skew ℓ + dmax ℓ ≤ λmax ℓ        (total arrival spread plus intrinsic delay)

and `λmin ℓ ≤ dmin ℓ`.

- `latency_of_intrinsic` is the per-read statement.
- `layered_recognition_from_intrinsic` is the chain with `λmin = dmin` and
  `λmax = skew + dmax`. Each layer's windows are derived first and then give that
  layer's latencies, layer by layer. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)

/-- The intrinsic delay law of one read. `ref` is the later of the read start and every
arrival. -/
def IntrinsicDelay (dmin dmax : Rat) (r : ReadObservation 2) : Prop :=
  ∀ t ∈ r.emissions, ∃ ref : Rat,
    (ref = r.start ∨ ∃ j, r.arrival j = some ref) ∧ r.start ≤ ref ∧
    (∀ j v, r.arrival j = some v → v ≤ ref) ∧ ref + dmin ≤ t ∧ t ≤ ref + dmax

def IntrinsicDelays (dmin dmax : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Prop
  | .input, _ => True
  | .layer (L := L) lower _ _, r =>
    IntrinsicDelays dmin dmax lower r.1 ∧ ∀ i, IntrinsicDelay (dmin (L + 1)) (dmax (L + 1)) (r.2.1 i)

/-- The skew of each layer, by layer number. -/
def layerSkew : (c : Cascade M L N) → Nat → Rat
  | .input => fun _ => 0
  | .layer (L := L) lower timing _ => fun ℓ => if ℓ = L + 1 then timing.skew else layerSkew lower ℓ

/-- Within its read window, an intrinsic delay in `[dmin, dmax]` gives the latency law with
`λmin = dmin` and every `λmax ≥ skew + dmax`. -/
theorem latency_of_intrinsic {dmin dmax lmax : Rat} {timing : SlotTiming} {r : ReadObservation 2}
    (delay : IntrinsicDelay dmin dmax r) (window : InWindow timing r)
    (skewNonneg : 0 ≤ timing.skew) (covers : timing.skew + dmax ≤ lmax) :
    CellLatency dmin lmax r := by
  intro t mem
  obtain ⟨ref, source, after, _, lo, hi⟩ := delay t mem
  have late : ref ≤ r.start + timing.skew := by
    rcases source with same | ⟨j, arrived⟩
    · subst same; grind
    · exact (window j ref arrived).2
  constructor <;> grind

/-- The chain from intrinsic delays. Layer by layer, the arrival window comes from the
lower pulses, and the pulse window then comes from the intrinsic delay. -/
theorem intrinsic_windows {s dmin dmax : Nat → Rat} {w : Rat} {c : Cascade M L N}
    {train : TrainingTrace c} {r : ReadTrace c} (valid : c.Valid) (D : Nat → Rat)
    (agree : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → D ℓ = layerSkew c ℓ + dmax ℓ)
    (dates : ChainDates s (latencyLow dmin) (latencyHigh w D) c) (reads : LayerReads c train r)
    (scheduled : Scheduled s c r) (external : ExternalWindow (s 0) w c r)
    (delays : IntrinsicDelays dmin dmax c r) :
    ArrivalWindows c r ∧ PulseWindows s (latencyLow dmin) (latencyHigh w D) c r := by
  induction c with
  | input =>
    refine ⟨trivial, fun j t arrived => ?_⟩
    obtain ⟨lo, hi⟩ := external j t arrived
    simp only [latencyLow, latencyHigh]
    constructor <;> grind
  | @layer L N B lower timing nodes ih =>
    have lowerAgree : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → D ℓ = layerSkew lower ℓ + dmax ℓ := by
      intro ℓ one le
      rw [agree ℓ one (by omega)]
      simp [layerSkew, show ℓ ≠ L + 1 by omega]
    obtain ⟨lowerWindows, lowerPulses⟩ :=
      ih valid.1 lowerAgree dates.1 reads.1 scheduled.1 external delays.1
    have windows : ∀ i, InWindow timing (r.2.1 i) := fun i =>
      routed_window (reads.2 i).1 (scheduled.2 i) lowerPulses (dates.2 i)
    refine ⟨⟨lowerWindows, windows⟩, lowerPulses, fun i t first => ?_⟩
    have top : D (L + 1) = timing.skew + dmax (L + 1) := by
      rw [agree (L + 1) (by omega) (Nat.le_refl _)]
      simp [layerSkew]
    have latency := latency_of_intrinsic (lmax := D (L + 1)) (delays.2 i) (windows i) valid.2.1.1
      (by rw [top]; exact Rat.le_refl) t (head_mem first)
    rw [scheduled.2 i] at latency
    exact latency

/-- The recognition theorem from intrinsic delays. `λmax ℓ = skew ℓ + dmax ℓ`, so a measured
`dmax` is checked against the chain through `checkChainDates`. -/
theorem layered_recognition_from_intrinsic {c : Cascade M L N} (valid : c.Valid)
    {train : TrainingTrace c} (training : TrainingCalibration c train)
    {s dmin dmax : Nat → Rat} {w : Rat}
    (dates : ChainDates s (latencyLow dmin) (latencyHigh w fun ℓ => layerSkew c ℓ + dmax ℓ) c)
    {x : Pattern M} {test : ReadTrace c}
    (inputs : (fun j => (inputTrace c test j).isSome) = x) (reads : LayerReads c train test)
    (scheduled : Scheduled s c test) (external : ExternalWindow (s 0) w c test)
    (delays : IntrinsicDelays dmin dmax c test) :
    ArrivalWindows c test ∧ observed c test = c.predict x := by
  obtain ⟨windows, _⟩ := intrinsic_windows valid _ (fun _ _ _ => rfl) dates reads scheduled
    external delays
  exact ⟨windows, (layered_recognition_at M L N c valid train training x test
    ((read_calibration_iff c train x test).mpr ⟨inputs, reads, windows⟩)).2⟩

end LearnedCoincidence.Layered
