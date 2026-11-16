import LayeredMonotoneTarget

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF (contains_iff singleton)

private theorem additive_fires {p : Cell} {w : Writes} {budget : Nat} {timing : SlotTiming}
    {r : ReadObservation 2} (read : AdditiveSlot p w budget timing r)
    (margin : p.threshold + budget ≤ p.score w r.input) : r.fired = true := by
  rw [read.1.2.2.2]
  have lower := read.2.1
  exact decide_eq_true (by omega)

private theorem additive_silent {p : Cell} {w : Writes} {budget : Nat} {timing : SlotTiming}
    {r : ReadObservation 2} (read : AdditiveSlot p w budget timing r)
    (margin : p.score w r.input + budget < p.threshold) : r.fired = false := by
  rw [read.1.2.2.2]
  have upper := read.2.2
  exact decide_eq_false (by omega)

private theorem score_congr (p : Cell) (x : Pattern 2) {u v : Writes}
    (agree : ∀ a, x a = true → u a = v a) : p.score u x = p.score v x := by
  have atPort (a : Fin 2) : (if x a then p.gain u a else 0) = (if x a then p.gain v a else 0) := by
    by_cases active : x a = true
    · simp [active, Cell.gain, agree a active]
    · simp [active]
  unfold Cell.score
  rw [atPort 0, atPort 1]

private theorem group_cases (g : Fin 2) : g = 0 ∨ g = 1 := by omega

private theorem second_group {k : Gate} (active : 1 < k.groups) : k = .either := by
  cases k <;> first | rfl | contradiction

private theorem second_group_disjoint {k : Gate} (active : 1 < k.groups) {a : Fin 2}
    (on : k.groupMask 1 a = true) : k.groupMask 0 a = false := by
  rw [second_group active] at on ⊢
  have h : a = 1 := of_decide_eq_true on
  subst a
  rfl

private theorem train_group (p : Cell) (train : CellTrain) (g : Fin 2) (timing : SlotTiming)
    (valid : p.Valid) (active : g.val < p.gate.groups)
    (input : ∀ r, r ≤ p.maxWrites → (train g r).input = p.gate.groupMask g)
    (calibrated : ∀ r, r ≤ p.maxWrites →
      AdditiveSlot p (p.writesBefore train g r) p.trainError timing (train g r))
    (prior : ∀ a, p.gate.groupMask g a = true →
      (if g = 0 then 0 else groupObserved train 0 a (p.maxWrites + 1)) = 0) :
    (∀ r, r ≤ p.maxWrites + 1 → ∀ a,
      groupObserved train g a r = p.groupWrites g (min r (p.stop g)) a) ∧
    ∀ r, r ≤ p.maxWrites → (train g r).fired = decide (p.stop g ≤ r) := by
  obtain ⟨_, early, stopped⟩ := valid.2.1 g active
  have step (r : Nat) (bound : r ≤ p.maxWrites)
      (counts : ∀ a, groupObserved train g a r = p.groupWrites g (min r (p.stop g)) a) :
      (train g r).fired = decide (p.stop g ≤ r) := by
    have scoreEq : p.score (p.writesBefore train g r) (train g r).input =
        p.groupScore g (min r (p.stop g)) := by
      rw [input r bound]
      apply score_congr
      intro a on
      simp [Cell.writesBefore, prior a on, counts a]
    by_cases done : p.stop g ≤ r
    · rw [decide_eq_true done]
      exact additive_fires (calibrated r bound) (by simpa [scoreEq, Nat.min_eq_right done] using stopped)
    · have before : r < p.stop g := by omega
      rw [decide_eq_false done]
      exact additive_silent (calibrated r bound)
        (by simpa [scoreEq, Nat.min_eq_left (Nat.le_of_lt before)] using early r before)
  have counts : ∀ r, r ≤ p.maxWrites + 1 → ∀ a,
      groupObserved train g a r = p.groupWrites g (min r (p.stop g)) a := by
    intro r
    induction r with
    | zero => intro _ a; simp [groupObserved, Cell.groupWrites]
    | succ r ih =>
      intro bound a
      have known := ih (by omega)
      rw [groupObserved, known a, input r (by omega), step r (by omega) known]
      by_cases done : p.stop g ≤ r
      · have next : p.stop g ≤ r + 1 := by omega
        simp [done, Nat.min_eq_right done, Nat.min_eq_right next]
      · have before : r ≤ p.stop g := by omega
        have next : r + 1 ≤ p.stop g := by omega
        cases on : p.gate.groupMask g a <;>
          simp [Cell.groupWrites, done, Nat.min_eq_left before, Nat.min_eq_left next, on]
  exact ⟨counts, fun r bound => step r bound (counts r (by omega))⟩

private theorem local_training (p : Cell) (train : CellTrain) (timing : SlotTiming)
    (valid : p.Valid)
    (input : ∀ g : Fin 2, g.val < p.gate.groups → ∀ r, r ≤ p.maxWrites →
      (train g r).input = p.gate.groupMask g)
    (calibrated : ∀ g : Fin 2, g.val < p.gate.groups → ∀ r, r ≤ p.maxWrites →
      AdditiveSlot p (p.writesBefore train g r) p.trainError timing (train g r)) :
    p.Trained train := by
  have zero (active : 0 < p.gate.groups) :=
    train_group p train 0 timing valid active (input 0 active) (calibrated 0 active) (by simp)
  have one (active : 1 < p.gate.groups) :=
    train_group p train 1 timing valid active (input 1 active) (calibrated 1 active) (by
      intro a on
      rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      rw [(zero (by omega)).1 _ (Nat.le_refl _) a]
      simp [Cell.groupWrites, second_group_disjoint active on])
  have group (g : Fin 2) (active : g.val < p.gate.groups) :
      (∀ r, r ≤ p.maxWrites + 1 → ∀ a,
        groupObserved train g a r = p.groupWrites g (min r (p.stop g)) a) ∧
      ∀ r, r ≤ p.maxWrites → (train g r).fired = decide (p.stop g ≤ r) := by
    rcases group_cases g with rfl | rfl
    · exact zero active
    · exact one active
  have final (g : Fin 2) (active : g.val < p.gate.groups) (a : Fin 2) :
      groupObserved train g a (p.maxWrites + 1) = p.groupWrites g (p.stop g) a := by
    have bound := (valid.2.1 g active).1.2
    simpa [Nat.min_eq_right (show p.stop g ≤ p.maxWrites + 1 by omega)] using
      (group g active).1 _ (Nat.le_refl _) a
  have contribution (g : Fin 2) (active : g.val < p.gate.groups) (r : Nat)
      (bound : r ≤ p.maxWrites + 1) (a : Fin 2) :
      groupObserved train g a r ≤ p.groupWrites g (p.stop g) a := by
    rw [(group g active).1 r bound a]
    unfold Cell.groupWrites
    split
    · exact Nat.min_le_right _ _
    · exact Nat.le_refl _
  refine ⟨fun g on r bound => ⟨input g on r bound, (group g on).2 r bound⟩, ?_, ?_⟩
  · intro g on r bound a
    have le : p.writesBefore train g r a ≤ p.expectedWrites a := by
      rcases group_cases g with rfl | rfl
      · simpa [Cell.writesBefore, Cell.expectedWrites, show 0 < p.gate.groups from on] using
          (Nat.le_trans (contribution 0 on r bound a)
            (Nat.le_add_right (p.groupWrites 0 (p.stop 0) a)
              (if 1 < p.gate.groups then p.groupWrites 1 (p.stop 1) a else 0)))
      · have first : 0 < p.gate.groups := by omega
        have next : 1 < p.gate.groups := on
        rw [Cell.writesBefore, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), final 0 first a,
          Cell.expectedWrites, ite_eq_left first, ite_eq_left next]
        exact Nat.add_le_add_left (contribution 1 on r bound a) _
    have gain := Nat.add_le_add_left (Nat.mul_le_mul_left p.dose le) (p.initialGain a)
    exact ⟨(group g on).1 r bound a, le, Nat.lt_of_le_of_lt gain (valid.2.2.1 a)⟩
  · intro a
    unfold Cell.settledWrites Cell.expectedWrites
    congr 1
    · split
      · rename_i active
        exact final 0 active a
      · rfl
    · split
      · rename_i active
        exact final 1 active a
      · rfl

private theorem contains_singleton {x : Pattern 2} {a : Fin 2} (on : x a = true) :
    contains x (singleton a) = true := by
  apply contains_iff.mpr
  intro j hj
  have same : j = a := of_decide_eq_true hj
  simpa [same] using on

private theorem gate_anchor {g : Gate} {x : Pattern 2} (fires : g.eval x = true) :
    ∃ y ∈ g.anchors, contains x y = true := by
  cases g with
  | off => contradiction
  | on => exact ⟨emptyMask, by simp [Gate.anchors], contains_iff.mpr (by simp [emptyMask])⟩
  | copy => exact ⟨singleton 0, by simp [Gate.anchors], contains_singleton fires⟩
  | both =>
    have both := Bool.and_eq_true_iff.mp (show x 0 && x 1 = true from fires)
    exact ⟨fullMask, by simp [Gate.anchors], contains_iff.mpr (by
      simp only [Fin.forall_fin_two, fullMask, true_implies]
      exact both)⟩
  | either =>
    rcases Bool.or_eq_true_iff.mp (show x 0 || x 1 = true from fires) with on | on
    · exact ⟨singleton 0, by simp [Gate.anchors], contains_singleton on⟩
    · exact ⟨singleton 1, by simp [Gate.anchors], contains_singleton on⟩

private theorem firing_slot_fires {p : Cell} {timing : SlotTiming} {r : ReadObservation 2}
    {scores : Pattern 2 → Int} (valid : p.Valid) (active : p.gate.eval r.input = true)
    (read : FiringSlot p p.expectedWrites timing r scores) : r.fired = true := by
  obtain ⟨y, anchor, included⟩ := gate_anchor active
  have lower := read.2.2.2 y anchor included
  have margin := valid.2.2.2.2 y anchor
  have fire : (p.threshold : Int) ≤ scores y := by omega
  rw [read.1.2.2.2, ← read.2.1]
  exact decide_eq_true (Int.le_trans fire (read.2.2.1 y included fire))

private theorem pulseDates_observed (c : Cascade M L N) (r : ReadTrace c) (i : Fin N) :
    (pulseDates c r i).isSome = observed c r i := by
  cases c with
  | input => rfl
  | layer lower timing nodes =>
    change ((r.2.1 i).emissions.head?).isSome = !(r.2.1 i).emissions.isEmpty
    cases (r.2.1 i).emissions <;> rfl

private theorem routed_input {c : Cascade M L N} {d : Node M N} {s : ReadTrace c}
    {r : ReadObservation 2} (route : Routed d (pulseDates c s) r) :
    r.input = d.inputs (observed c s) := by
  funext a
  simp only [ReadObservation.input, Node.inputs, route a]
  cases h : d.source a with
  | none => rfl
  | some i =>
    change ((pulseDates c s i).map (fun t => t + d.delay a)).isSome = observed c s i
    rw [← pulseDates_observed c s i]
    cases pulseDates c s i <;> rfl

private theorem read_predict (c : Cascade M L N) (valid : c.Valid) (train : TrainingTrace c)
    (trained : c.Trained train) (x : Pattern M) (test : ReadTrace c)
    (calibrated : ReadCalibration c train x test) :
    observed c test = c.predict x := by
  induction c with
  | input => exact calibrated
  | layer lower timing nodes ih =>
    have prior := ih valid.1 train.1 trained.1 test.1 calibrated.1
    funext i
    obtain ⟨route, read⟩ := calibrated.2 i
    have input := (routed_input route).trans (congrArg (nodes i).inputs prior)
    have counts : (nodes i).cell.settledWrites (train.2.2 i) = (nodes i).cell.expectedWrites :=
      funext (trained.2 i).2.2
    rw [counts] at read
    change (test.2.1 i).fired = (nodes i).cell.gate.eval ((nodes i).inputs (lower.predict x))
    rw [← input]
    cases fire : (nodes i).cell.gate.eval (test.2.1 i).input with
    | false =>
      rw [ite_eq_right (by simp [fire])] at read
      exact additive_silent read ((valid.2.2 i).1.2.2.2.1 _ fire)
    | true =>
      rw [ite_eq_left fire] at read
      exact firing_slot_fires (valid.2.2 i).1 fire read

private theorem train_correct (c : Cascade M L N) (valid : c.Valid) (train : TrainingTrace c)
    (calibrated : TrainingCalibration c train) : c.Trained train := by
  induction c with
  | input => trivial
  | layer lower timing nodes ih =>
    have prior := ih valid.1 train.1 calibrated.1
    refine ⟨prior, ?_⟩
    intro i
    apply local_training (nodes i).cell (train.2.2 i) timing (valid.2.2 i).1
    · intro g active r bound
      obtain ⟨replay, route, _⟩ := calibrated.2 i g active r bound
      rw [routed_input route, read_predict lower valid.1 train.1 prior _ _ replay]
      exact (valid.2.2 i).2.2 g active
    · intro g active r bound
      exact (calibrated.2 i g active r bound).2.2

/-- The dated routed pulses supply every lesson and determine each settled output.
Training separation is a calendar premise of the protocol. The proof derives its
conclusion from validity and the two calibration premises alone. -/
theorem layered_monotone_recognition_one_sided : LayeredMonotoneRecognitionOneSided := by
  intro M L N c valid train test _separation training readings
  have trained := train_correct c valid train training
  exact ⟨trained, fun x => read_predict c valid train trained x (test x) (readings x)⟩

end LearnedCoincidence.Layered
