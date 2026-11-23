import LayeredRecognitionAt

/-! The timing chain. Arrival windows are derived from the schedule, the pulse windows and
the chain inequalities. The pulse windows are derived in turn from the per-cell latencies,
or from the deadlines alone. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF (ThresholdRead)

theorem firing_slot_iff {p : Cell} {w : Writes} {t : SlotTiming} {r : ReadObservation 2}
    {scoreAt : Pattern 2 → Int} :
    FiringSlot p w t r scoreAt ↔ FiringDecoded p w t r scoreAt ∧ InWindow t r := by
  unfold FiringSlot FiringDecoded ThresholdRead DecodedRead InWindow
  constructor
  · rintro ⟨⟨v, win, em, fi⟩, rest⟩
    exact ⟨⟨⟨v, em, fi⟩, rest⟩, win⟩
  · rintro ⟨⟨⟨v, em, fi⟩, rest⟩, win⟩
    exact ⟨⟨v, win, em, fi⟩, rest⟩

theorem additive_slot_iff {p : Cell} {w : Writes} {budget : Nat} {t : SlotTiming}
    {r : ReadObservation 2} :
    AdditiveSlot p w budget t r ↔ AdditiveDecoded p w budget t r ∧ InWindow t r := by
  unfold AdditiveSlot AdditiveDecoded ThresholdRead DecodedRead InWindow
  constructor
  · rintro ⟨⟨v, win, em, fi⟩, rest⟩
    exact ⟨⟨⟨v, em, fi⟩, rest⟩, win⟩
  · rintro ⟨⟨⟨v, em, fi⟩, rest⟩, win⟩
    exact ⟨⟨v, win, em, fi⟩, rest⟩

/-- A read calibration is exactly its external mask, its window-free reads and its windows. -/
theorem read_calibration_iff (c : Cascade M L N) (train : TrainingTrace c) (x : Pattern M)
    (r : ReadTrace c) :
    ReadCalibration c train x r ↔
      (fun j => (inputTrace c r j).isSome) = x ∧ LayerReads c train r ∧ ArrivalWindows c r := by
  induction c with
  | input => simp [ReadCalibration, LayerReads, ArrivalWindows, inputTrace]
  | layer lower timing nodes ih =>
    simp only [ReadCalibration, LayerReads, ArrivalWindows, inputTrace, ih]
    constructor
    · rintro ⟨⟨hx, hl, hw⟩, h⟩
      refine ⟨hx, ⟨hl, fun i => ?_⟩, hw, fun i => ?_⟩
      · obtain ⟨route, slot⟩ := h i
        refine ⟨route, ?_⟩
        split at slot
        · rw [ite_eq_left (by assumption)]; exact (firing_slot_iff.mp slot).1
        · rw [ite_eq_right (by assumption)]; exact (additive_slot_iff.mp slot).1
      · obtain ⟨_, slot⟩ := h i
        split at slot
        · exact (firing_slot_iff.mp slot).2
        · exact (additive_slot_iff.mp slot).2
    · rintro ⟨hx, ⟨hl, h⟩, hw, win⟩
      refine ⟨⟨hx, hl, hw⟩, fun i => ?_⟩
      obtain ⟨route, slot⟩ := h i
      refine ⟨route, ?_⟩
      split at slot
      · rw [ite_eq_left (by assumption)]; exact firing_slot_iff.mpr ⟨slot, win i⟩
      · rw [ite_eq_right (by assumption)]; exact additive_slot_iff.mpr ⟨slot, win i⟩

/-- The pulse window of the top layer of a cascade. -/
theorem top_pulse {s e f : Nat → Rat} {c : Cascade M L N} {r : ReadTrace c}
    (pulses : PulseWindows s e f c r) :
    ∀ i t, pulseDates c r i = some t → s L + e L ≤ t ∧ t ≤ s L + f L := by
  cases c with
  | input => exact pulses
  | layer lower timing nodes => exact pulses.2

/-- The chain inequalities and the pulse windows give every arrival window. -/
theorem chain_windows {s e f : Nat → Rat} {c : Cascade M L N} {train : TrainingTrace c}
    {r : ReadTrace c} (dates : ChainDates s e f c) (reads : LayerReads c train r)
    (scheduled : Scheduled s c r) (pulses : PulseWindows s e f c r) : ArrivalWindows c r := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    refine ⟨ih dates.1 reads.1 scheduled.1 pulses.1, fun i j t arrived => ?_⟩
    have route := (reads.2 i).1 j
    rw [route] at arrived
    rw [scheduled.2 i]
    cases source : (nodes i).source j with
    | none => simp [source] at arrived
    | some src =>
      rw [source] at arrived
      cases pulse : pulseDates lower r.1 src with
      | none => simp [pulse] at arrived
      | some u =>
        simp only [Option.bind_some, pulse, Option.map_some, Option.some.injEq] at arrived
        subst arrived
        obtain ⟨lo, hi⟩ := top_pulse pulses.1 src u pulse
        obtain ⟨early, late⟩ := dates.2 i j src source
        constructor <;> grind

/-- General form: declared pulse windows. -/
theorem layered_recognition_chained : LayeredRecognitionChained := by
  intro M L N c valid train training s e f dates x test inputs reads scheduled pulses
  have windows := chain_windows dates reads scheduled pulses
  exact ⟨windows, (layered_recognition_at M L N c valid train training x test
    ((read_calibration_iff c train x test).mpr ⟨inputs, reads, windows⟩)).2⟩

theorem cell_latency_of_last_arrival {lmin lmax : Rat} {r : ReadObservation 2}
    (law : CellLatencyFromLastArrival lmin lmax r) : CellLatency lmin lmax r :=
  fun t mem => ⟨(law t mem).1, (law t mem).2.2⟩

theorem head_mem {xs : List Rat} {t : Rat} (h : xs.head? = some t) : t ∈ xs := by
  cases xs with
  | nil => simp at h
  | cons y ys =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self

/-- The latencies and the external window give the pulse windows. -/
theorem latency_pulse_windows {s lmin lmax : Nat → Rat} {w : Rat} {c : Cascade M L N}
    {r : ReadTrace c} (scheduled : Scheduled s c r) (external : ExternalWindow (s 0) w c r)
    (latency : Latencies lmin lmax c r) :
    PulseWindows s (latencyLow lmin) (latencyHigh w lmax) c r := by
  induction c with
  | input =>
    intro j t arrived
    obtain ⟨lo, hi⟩ := external j t arrived
    simp only [latencyLow, latencyHigh]
    constructor <;> grind
  | @layer L N B lower timing nodes ih =>
    refine ⟨ih scheduled.1 external latency.1, fun i t first => ?_⟩
    obtain ⟨lo, hi⟩ := latency.2 i t (head_mem first)
    rw [scheduled.2 i] at lo hi
    exact ⟨lo, hi⟩

/-- Latency form: the calendar follows from per-cell constants. -/
theorem layered_recognition_from_latency : LayeredRecognitionFromLatency := by
  intro M L N c valid train training s lmin lmax w dates x test inputs reads scheduled
    external latency
  have pulses := latency_pulse_windows scheduled external latency
  obtain ⟨windows, decisions⟩ :=
    layered_recognition_chained M L N c valid train training s _ _ dates x test inputs reads
      scheduled pulses
  exact ⟨windows, decisions, top_pulse pulses⟩

/-- A window-free read has its single emission between its start and its deadline. -/
theorem decoded_latency {level : Nat} {timing : SlotTiming} {r : ReadObservation 2}
    (read : DecodedRead level timing r) : CellLatency 0 timing.deadline r := by
  obtain ⟨_, emission, _⟩ := read
  intro t mem
  match h : r.emissions, emission with
  | [], _ => simp [h] at mem
  | [u], ⟨lo, hi, _⟩ =>
    rw [h, List.mem_singleton] at mem
    subst mem
    constructor <;> grind
  | _ :: _ :: _, bad => exact bad.elim

/-- The window-free reads give the latencies `0` and the deadline of each layer. -/
theorem deadline_latencies {c : Cascade M L N} {train : TrainingTrace c} {r : ReadTrace c}
    (reads : LayerReads c train r) (D : Nat → Rat)
    (agree : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → D ℓ = layerDeadline c ℓ) :
    Latencies (fun _ => 0) D c r := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    refine ⟨ih reads.1 (fun ℓ one le => ?_), fun i => ?_⟩
    · rw [agree ℓ one (by omega)]
      simp [layerDeadline, show ℓ ≠ L + 1 by omega]
    · have top : D (L + 1) = timing.deadline := by
        rw [agree (L + 1) (by omega) (Nat.le_refl _)]
        simp [layerDeadline]
      rw [top]
      obtain ⟨_, slot⟩ := reads.2 i
      split at slot
      · exact decoded_latency slot.1
      · exact decoded_latency slot.1

/-- Deadline-only form: `e = 0` and `f = deadline` above the input. -/
theorem layered_recognition_from_deadlines : LayeredRecognitionFromDeadlines := by
  intro M L N c valid train training s w dates x test inputs reads scheduled external
  have latency := deadline_latencies reads (layerDeadline c) (fun _ _ _ => rfl)
  obtain ⟨windows, decisions, _⟩ :=
    layered_recognition_from_latency M L N c valid train training s _ _ w dates x test inputs
      reads scheduled external latency
  exact ⟨windows, decisions⟩

private theorem all_fin {n : Nat} {P : Fin n → Bool} :
    (List.finRange n).all P = true ↔ ∀ i, P i = true := by
  simp [List.all_eq_true]

theorem chain_dates_checker_sound : ChainDatesCheckerSound := by
  intro M L N c s e f
  induction c with
  | input => intro _; trivial
  | @layer L N B lower timing nodes ih =>
    intro h
    simp only [checkChainDates, Bool.and_eq_true] at h
    refine ⟨ih h.1, fun i a src source => ?_⟩
    have port := all_fin.mp (all_fin.mp h.2 i) a
    rw [source] at port
    simp only [Bool.and_eq_true, decide_eq_true_eq] at port
    exact port

theorem chain_dates_checker_complete : ChainDatesCheckerComplete := by
  intro M L N c s e f
  induction c with
  | input => intro _; rfl
  | @layer L N B lower timing nodes ih =>
    intro h
    simp only [checkChainDates, Bool.and_eq_true]
    refine ⟨ih h.1, all_fin.mpr fun i => all_fin.mpr fun a => ?_⟩
    cases source : (nodes i).source a with
    | none => rfl
    | some src =>
      obtain ⟨early, late⟩ := h.2 i a src source
      simp [early, late]

end LearnedCoincidence.Layered
