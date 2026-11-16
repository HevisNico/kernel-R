import MonotonePremiseCompletenessTargets

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch)
open PremiseCheck

private theorem check_arrivals_complete {r : ReadObservation M} {ok : Rat → Bool}
    (h : ∀ j t, r.arrival j = some t → ok t = true) : checkArrivals r ok = true := by
  apply List.all_eq_true.mpr
  intro j _
  cases arrival : r.arrival j with
  | none => rfl
  | some t => exact h j t arrival

private theorem check_emissions_complete {timing : SlotTiming} {r : ReadObservation M}
    (h : match r.emissions with
      | [] => True
      | [t] =>
        r.start ≤ t ∧ t ≤ r.start + timing.deadline ∧
        ∀ j v, r.arrival j = some v → v ≤ t
      | _ => False) :
    checkEmissions timing r = true := by
  cases emissions : r.emissions with
  | nil => simp [checkEmissions, emissions]
  | cons t rest =>
    cases rest with
    | nil =>
      rw [emissions] at h
      rw [checkEmissions, emissions]
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ⟨h.1, h.2.1⟩,
        check_arrivals_complete fun j _ arrival => decide_eq_true (h.2.2 j _ arrival)⟩
    | cons u rest =>
      rw [emissions] at h
      exact False.elim h

theorem check_threshold_read_complete {level : Nat} {timing : SlotTiming}
    {r : ReadObservation M} (h : ThresholdRead level timing r) :
    checkThresholdRead level timing r = true := by
  obtain ⟨valid, arrivals, emissions, decoder⟩ := h
  simp only [checkThresholdRead, Bool.and_eq_true, and_assoc]
  exact ⟨decide_eq_true valid,
    check_arrivals_complete fun j _ arrival => decide_eq_true (arrivals j _ arrival),
    check_emissions_complete emissions, beq_iff_eq.mpr decoder⟩

private theorem check_additive_read_complete {p : Parameters N M} {i : Fin N} {writes : Nat}
    {x : Pattern M} {budget : Nat} {timing : SlotTiming} {r : ReadObservation M}
    (h : CalibratedAdditiveRead p i writes x budget timing r) :
    checkAdditiveRead p i writes x budget timing r = true := by
  obtain ⟨valid, input, arrivals, emissions, decoder, residual⟩ := h
  simp only [checkAdditiveRead, Bool.and_eq_true, and_assoc]
  exact ⟨check_threshold_read_complete ⟨valid, arrivals, emissions, decoder⟩,
    List.all_eq_true.mpr fun j _ => beq_iff_eq.mpr (congrFun input j), decide_eq_true residual⟩

private theorem check_route_complete {delay : Fin A → Rat} {left : Fin A → ReadObservation M}
    {right : ReadObservation A} (h : RoutedBatch delay left right) :
    checkRoute delay left right = true :=
  List.all_eq_true.mpr fun a _ => decide_eq_true (h a)

private theorem check_firing_mask_complete {p : Disjunctions B A} {writes : Counts B A}
    {i : Fin B} {timing : SlotTiming} {r : ReadObservation A} {scoreAt : Pattern A → Int}
    (h : FiringMaskRead p writes i timing r scoreAt) :
    checkFiringMask p writes i timing r scoreAt = true := by
  obtain ⟨timed, measured, masks, anchors⟩ := h
  simp only [checkFiringMask, Bool.and_eq_true, and_assoc]
  refine ⟨check_threshold_read_complete timed, decide_eq_true measured, ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro y _
    split
    · rename_i active
      exact decide_eq_true (masks y active.1 (of_decide_eq_true active.2))
    · rfl
  · split
    · rename_i mode
      rw [ite_eq_left mode] at anchors
      exact decide_eq_true anchors
    · rename_i mode
      rw [ite_eq_right mode] at anchors
      apply List.all_eq_true.mpr
      intro a _
      split
      · rename_i active
        exact decide_eq_true (anchors a active.1 active.2)
      · rfl

private theorem check_ends_before_complete {left right : SlotTiming} {o : Observations A B M}
    {n : Nat} {time : Rat}
    (h : (∀ a, (o.teach n a).start + left.duration ≤ time) ∧
      (o.secondTrain n).start + right.duration ≤ time) :
    checkEndsBefore left right o n time = true :=
  Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr fun a _ => decide_eq_true (h.1 a), decide_eq_true h.2⟩

theorem cascade_valid_checker_complete : CascadeValidCheckerComplete := by
  intro A B M p valid
  exact valid

theorem training_separation_checker_complete : TrainingSeparationCheckerComplete := by
  intro A B M p left right o valid
  obtain ⟨rounds, enters, ordered, firstTests, secondTests⟩ := valid
  simp only [checkTrainingSeparation, Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact List.all_eq_true.mpr fun r hr => List.all_eq_true.mpr fun a _ =>
      List.all_eq_true.mpr fun b _ => decide_eq_true (rounds r (List.mem_range.mp hr) a b)
  · apply List.all_eq_true.mpr
    intro n hn
    exact List.all_eq_true.mpr fun a _ =>
      let h := enters n (List.mem_range.mp hn) a
      Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr fun b _ => decide_eq_true (h.1 b),
        decide_eq_true h.2⟩
  · apply List.all_eq_true.mpr
    intro n _
    apply List.all_eq_true.mpr
    intro s hs
    split
    · rename_i before
      have h := ordered n s before (List.mem_range.mp hs)
      exact Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr fun a _ => check_ends_before_complete (h.1 a),
        check_ends_before_complete h.2⟩
    · rfl
  · exact List.all_eq_true.mpr fun x _ => List.all_eq_true.mpr fun a _ =>
      Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr fun b _ => decide_eq_true ((firstTests x a).1 b),
        List.all_eq_true.mpr fun i _ => decide_eq_true ((firstTests x a).2 i)⟩
  · exact List.all_eq_true.mpr fun x _ => List.all_eq_true.mpr fun n hn =>
      let h := secondTests x n (List.mem_range.mp hn)
      Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr fun a _ => check_ends_before_complete (h.1 a),
        List.all_eq_true.mpr fun i _ => check_ends_before_complete (h.2 i)⟩

theorem cascade_calibration_one_sided_checker_complete : CascadeCalibrationOneSidedCheckerComplete := by
  intro A B M p left right o scores valid
  obtain ⟨⟨firstTrain, lessonsValid⟩, firstTests, secondTests⟩ := valid
  simp only [checkCascadeCalibrationOneSided, Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.all_eq_true.mpr fun r hr => List.all_eq_true.mpr fun a _ =>
      check_additive_read_complete (firstTrain r (Nat.le_of_lt_succ (List.mem_range.mp hr)) a)
  · apply List.all_eq_true.mpr
    intro n hn
    have bound := List.mem_range.mp hn
    rw [List.getElem?_eq_getElem bound]
    obtain ⟨teach, route, read⟩ := lessonsValid n _ (List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩)
    simp only [Bool.and_eq_true, and_assoc]
    exact ⟨List.all_eq_true.mpr fun a _ => check_additive_read_complete (teach a),
      check_route_complete route, check_additive_read_complete read⟩
  · exact List.all_eq_true.mpr fun x _ => List.all_eq_true.mpr fun a _ =>
      check_additive_read_complete (firstTests x a)
  · apply List.all_eq_true.mpr
    intro x _
    apply List.all_eq_true.mpr
    intro i _
    obtain ⟨route, read⟩ := secondTests x i
    refine Bool.and_eq_true_iff.mpr ⟨check_route_complete route, ?_⟩
    split
    · rename_i fires
      dsimp only at read
      rw [ite_eq_left fires] at read
      exact check_firing_mask_complete read
    · rename_i fires
      dsimp only at read
      rw [ite_eq_right fires] at read
      exact check_additive_read_complete read

end LearnedCoincidence.MonotoneDNF
