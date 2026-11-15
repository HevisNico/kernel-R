import MonotonePremiseTargets

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch)
open PremiseCheck

private theorem patterns_complete (x : Pattern M) : x ∈ patterns M := by
  induction M with
  | zero =>
    have empty : x = Fin.elim0 := funext fun j => j.elim0
    simp [patterns, empty]
  | succ M ih =>
    let tail : Pattern M := fun j => x j.succ
    have reconstruct : Fin.cases (x 0) tail = x := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [← reconstruct, patterns]
    refine List.mem_flatMap.mpr ⟨tail, ih tail, ?_⟩
    cases x 0 <;> simp

private theorem all_patterns {f : Pattern M → Bool} (h : (patterns M).all f = true)
    (x : Pattern M) : f x = true :=
  List.all_eq_true.mp h x (patterns_complete x)

private theorem all_indices {f : Nat → Bool} {n : Nat} (h : (List.range n).all f = true)
    {k : Nat} (bound : k < n) : f k = true :=
  List.all_eq_true.mp h k (List.mem_range.mpr bound)

private theorem ends_before_sound {left right : SlotTiming} {o : Observations A B M}
    {n : Nat} {time : Rat} (h : checkEndsBefore left right o n time = true) :
    (∀ a, (o.teach n a).start + left.duration ≤ time) ∧
      (o.secondTrain n).start + right.duration ≤ time := by
  obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨fun a => of_decide_eq_true (allPorts first a), of_decide_eq_true second⟩

private theorem arrivals_sound {r : ReadObservation M} {ok : Rat → Bool}
    (h : checkArrivals r ok = true) (j : Fin M) {t : Rat} (arrival : r.arrival j = some t) :
    ok t = true := by
  have valid := allPorts h j
  simpa [Option.all, arrival] using valid

private theorem emissions_sound {timing : SlotTiming} {r : ReadObservation M}
    (h : checkEmissions timing r = true) :
    match r.emissions with
    | [] => True
    | [t] =>
      r.start ≤ t ∧ t ≤ r.start + timing.deadline ∧
      ∀ j v, r.arrival j = some v → v ≤ t
    | _ => False := by
  cases emissions : r.emissions with
  | nil => trivial
  | cons t rest =>
    cases rest with
    | nil =>
      rw [checkEmissions, emissions] at h
      obtain ⟨date, arrivals⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨start, deadline⟩ := of_decide_eq_true date
      exact ⟨start, deadline, fun j _ arrival => of_decide_eq_true (arrivals_sound arrivals j arrival)⟩
    | cons u rest =>
      simp [checkEmissions, emissions] at h

private theorem threshold_read_sound {level : Nat} {timing : SlotTiming} {r : ReadObservation M}
    (h : checkThresholdRead level timing r = true) : ThresholdRead level timing r := by
  simp only [checkThresholdRead, Bool.and_eq_true, and_assoc] at h
  obtain ⟨valid, arrivals, emissions, decoder⟩ := h
  exact ⟨by unfold TwoLayer.SlotTiming.Valid; exact of_decide_eq_true valid,
    fun j _ arrival => of_decide_eq_true (arrivals_sound arrivals j arrival),
    emissions_sound emissions, beq_iff_eq.mp decoder⟩

private theorem additive_read_sound {p : Parameters N M} {i : Fin N} {writes : Nat}
    {x : Pattern M} {budget : Nat} {timing : SlotTiming} {r : ReadObservation M}
    (h : checkAdditiveRead p i writes x budget timing r = true) :
    CalibratedAdditiveRead p i writes x budget timing r := by
  simp only [checkAdditiveRead, Bool.and_eq_true, and_assoc] at h
  obtain ⟨timed, input, residual⟩ := h
  obtain ⟨valid, arrivals, emissions, decoder⟩ := threshold_read_sound timed
  exact ⟨valid, funext fun j => beq_iff_eq.mp (allPorts input j),
    arrivals, emissions, decoder, by unfold admissible; exact of_decide_eq_true residual⟩

private theorem route_sound {delay : Fin A → Rat} {left : Fin A → ReadObservation M}
    {right : ReadObservation A} (h : checkRoute delay left right = true) :
    RoutedBatch delay left right :=
  fun a => of_decide_eq_true (allPorts h a)

private theorem firing_mask_sound {p : Disjunctions B A} {writes : Counts B A} {i : Fin B}
    {timing : SlotTiming} {r : ReadObservation A} {scoreAt : Pattern A → Int}
    (h : checkFiringMask p writes i timing r scoreAt = true) :
    FiringMaskRead p writes i timing r scoreAt := by
  simp only [checkFiringMask, Bool.and_eq_true, and_assoc] at h
  obtain ⟨timed, measured, masks, anchors⟩ := h
  refine ⟨threshold_read_sound timed, of_decide_eq_true measured, ?_, ?_⟩
  · intro y included fires
    have comparison := all_patterns masks y
    simpa [included, fires] using comparison
  · cases mode : p.alwaysFire i with
    | true =>
      rw [ite_eq_left mode] at anchors
      simp only [ite_true]
      exact of_decide_eq_true anchors
    | false =>
      have inactive : ¬p.alwaysFire i = true := by simp [mode]
      rw [ite_eq_right inactive] at anchors
      simp only [Bool.false_eq_true, ite_false]
      intro a selected arrived
      have anchor := allPorts anchors a
      simpa [selected, arrived] using anchor

theorem cascade_valid_checker_sound : CascadeValidCheckerSound := by
  intro A B M p valid
  exact valid

theorem training_separation_checker_sound : TrainingSeparationCheckerSound := by
  intro A B M p left right o checked
  simp only [checkTrainingSeparation, Bool.and_eq_true, and_assoc] at checked
  obtain ⟨rounds, enters, ordered, firstTests, secondTests⟩ := checked
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r bound a b
    exact of_decide_eq_true (allPorts (allPorts (all_indices rounds bound) a) b)
  · intro n bound a
    have h := Bool.and_eq_true_iff.mp (allPorts (all_indices enters bound) a)
    exact ⟨fun b => of_decide_eq_true (allPorts h.1 b), of_decide_eq_true h.2⟩
  · intro n s before bound
    have h := all_indices (all_indices ordered (Nat.lt_trans before bound)) bound
    rw [ite_eq_left before] at h
    obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨fun a => ends_before_sound (allPorts first a), ends_before_sound second⟩
  · intro x a
    have h := Bool.and_eq_true_iff.mp (allPorts (all_patterns firstTests x) a)
    exact ⟨fun b => of_decide_eq_true (allPorts h.1 b), fun i => of_decide_eq_true (allPorts h.2 i)⟩
  · intro x n bound
    have h := Bool.and_eq_true_iff.mp (all_indices (all_patterns secondTests x) bound)
    exact ⟨fun a => ends_before_sound (allPorts h.1 a), fun i => ends_before_sound (allPorts h.2 i)⟩

theorem cascade_calibration_one_sided_checker_sound : CascadeCalibrationOneSidedCheckerSound := by
  intro A B M p left right o scores checked
  simp only [checkCascadeCalibrationOneSided, Bool.and_eq_true, and_assoc] at checked
  obtain ⟨firstTrain, lessonsChecked, firstTests, secondTests⟩ := checked
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r bound a
    exact additive_read_sound (allPorts (all_indices firstTrain (Nat.lt_succ_of_le bound)) a)
  · intro n L atIndex
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp atIndex
    have h := all_indices lessonsChecked bound
    rw [atIndex] at h
    simp only [Bool.and_eq_true, and_assoc] at h
    exact ⟨fun a => additive_read_sound (allPorts h.1 a), route_sound h.2.1, additive_read_sound h.2.2⟩
  · intro x a
    exact additive_read_sound (allPorts (all_patterns firstTests x) a)
  · intro x i
    have h := Bool.and_eq_true_iff.mp (allPorts (all_patterns secondTests x) i)
    refine ⟨route_sound h.1, ?_⟩
    by_cases fires : (p.second.alwaysFire i ||
        (List.finRange A).any (fun a => p.second.lines i a && (o.secondTest x i).input a)) = true
    · have valid := h.2
      rw [ite_eq_left fires] at valid ⊢
      exact firing_mask_sound valid
    · have valid := h.2
      rw [ite_eq_right fires] at valid ⊢
      exact additive_read_sound valid

end LearnedCoincidence.MonotoneDNF
