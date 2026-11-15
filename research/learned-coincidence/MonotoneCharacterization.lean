import MonotoneRecognition

namespace LearnedCoincidence.MonotoneDNF

private def emptyPattern : Pattern M := fun _ => false

private theorem empty_included (x : Pattern M) : contains x emptyPattern = true :=
  contains_iff.mpr (by simp [emptyPattern])

private theorem contains_trans {x y z : Pattern M} (hy : contains y x = true)
    (hz : contains z y = true) : contains z x = true :=
  contains_iff.mpr fun j h => contains_iff.mp hz j (contains_iff.mp hy j h)

private theorem active_sublist {x y : Pattern M} (h : contains y x = true) :
    ((List.finRange M).filter x).Sublist ((List.finRange M).filter y) := by
  have eq : ((List.finRange M).filter y).filter x = (List.finRange M).filter x := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro j _
    cases hx : x j
    · rfl
    · simpa using contains_iff.mp h j hx
  rw [← eq]
  exact List.filter_sublist

private theorem card_lt_of_proper {x y : Pattern M} (h : contains y x = true)
    (different : x ≠ y) : card x < card y := by
  have sub := active_sublist h
  have le : card x ≤ card y := sub.length_le
  refine Nat.lt_of_le_of_ne le ?_
  intro equal
  apply different
  have lists := sub.eq_of_length equal
  funext j
  have eq : x j = true ↔ y j = true := by
    have hx : j ∈ (List.finRange M).filter x ↔ x j = true := by simp
    have hy : j ∈ (List.finRange M).filter y ↔ y j = true := by simp
    rw [← hx, ← hy, lists]
  exact Bool.eq_iff_iff.mpr eq

private def IsTerm (f : Pattern M → Bool) (t : Pattern M) : Prop :=
  f t = true ∧ ∀ y, contains t y = true → f y = true → y = t

private theorem has_term (f : Pattern M → Bool) (x : Pattern M) (hx : f x = true) :
    ∃ t, contains x t = true ∧ IsTerm f t := by
  classical
  generalize rank : card x = n
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    by_cases smallest : IsTerm f x
    · exact ⟨x, contains_iff.mpr (fun _ h => h), smallest⟩
    · have smaller : ∃ y, contains x y = true ∧ f y = true ∧ y ≠ x := by
        by_cases someSmaller : ∃ y, contains x y = true ∧ f y = true ∧ y ≠ x
        · exact someSmaller
        · exact False.elim (smallest ⟨hx, fun y sub hy =>
            Classical.byContradiction fun ne => someSmaller ⟨y, sub, hy, ne⟩⟩)
      obtain ⟨y, sub, hy, different⟩ := smaller
      have lt : card y < n := rank ▸ card_lt_of_proper sub different
      obtain ⟨t, included, term⟩ := ih (card y) lt y hy rfl
      exact ⟨t, contains_trans included sub, term⟩

private def prependBit (b : Bool) (x : Pattern M) : Pattern (M + 1) :=
  Fin.cases b x

private def allPatterns : (M : Nat) → List (Pattern M)
  | 0 => [Fin.elim0]
  | M + 1 => (allPatterns M).map (prependBit false) ++ (allPatterns M).map (prependBit true)

private theorem prepend_injective (b : Bool) {x y : Pattern M}
    (h : prependBit b x = prependBit b y) : x = y := by
  funext j
  exact congrFun h j.succ

private theorem allPatterns_complete (x : Pattern M) : x ∈ allPatterns M := by
  induction M with
  | zero =>
    have h : x = Fin.elim0 := funext (fun j => j.elim0)
    simp [allPatterns, h]
  | succ M ih =>
    have reconstruct : prependBit (x 0) (fun j => x j.succ) = x := by
      funext j
      refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
    have member := ih (fun j => x j.succ)
    rw [← reconstruct, allPatterns, List.mem_append]
    generalize x 0 = b
    cases b
    · exact Or.inl (List.mem_map.mpr ⟨_, member, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨_, member, rfl⟩)

private theorem allPatterns_nodup (M : Nat) : (allPatterns M).Nodup := by
  induction M with
  | zero => simp [allPatterns]
  | succ M ih =>
    rw [allPatterns, List.nodup_append]
    have mapped (b : Bool) : ((allPatterns M).map (prependBit b)).Nodup := by
      rw [List.Nodup, List.pairwise_map]
      exact ih.imp (fun h equal => h (prepend_injective b equal))
    refine ⟨mapped false, mapped true, ?_⟩
    intro x hx y hy same
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
    have impossible : false = true := congrFun same 0
    contradiction

private def constructed (terms : Fin A → Pattern M) (constant : Bool) : Cascade A 1 M where
  first := {
    target := terms, tests := [], initialGain := fun _ _ => 0, help := fun _ => 0
    threshold := fun a => 4 * card (terms a) - 2
    trainingError := fun _ => 1, testingError := fun _ => 1, dose := 4, maxWrites := 1, rail := 5
  }
  second := {
    lines := fun _ _ => !constant, alwaysFire := fun _ => constant
    initialGain := fun _ _ => 0, help := fun _ => if constant then 3 else 0, threshold := fun _ => 2
    trainingError := fun _ => 1, testingError := fun _ => 1, dose := 4, maxWrites := 1, rail := 5
  }
  delay := fun _ _ => 0
  heldOut := []

private theorem constructed_zero_score (terms : Fin A → Pattern M) (a : Fin A) :
    score (constructed terms false).first a 0 (terms a) = 0 := by
  unfold score
  have zeroGain : gain (constructed terms false).first a 0 = fun _ => 0 := by
    funext j
    simp [gain, portWrites, constructed]
  rw [zeroGain]
  simp [constructed, List.map_const', List.sum_replicate_nat]

private theorem active_score (terms : Fin A → Pattern M) (a : Fin A) (x : Pattern M) :
    score (constructed terms false).first a 1 x = 4 * card (fun j => x j && terms a j) := by
  unfold score
  have gains : gain (constructed terms false).first a 1 =
      fun j => 4 * (if terms a j then 1 else 0) := by
    funext j
    simp [gain, portWrites, constructed]
  rw [gains]
  change 0 + _ = _
  unfold card
  have filterEq : (List.finRange M).filter (fun j => x j && terms a j) =
      ((List.finRange M).filter x).filter (terms a) := by
    rw [List.filter_filter]
    exact List.filter_congr (fun j _ => Bool.and_comm (x j) (terms a j))
  rw [filterEq]
  generalize List.filter x (List.finRange M) = ports
  simp only [Nat.zero_add]
  induction ports with
  | nil => rfl
  | cons j rest ih =>
    cases h : terms a j <;> simp [h, ih, Nat.mul_succ, Nat.add_comm]

private theorem constructed_need (terms : Fin A → Pattern M) (a : Fin A)
    (nonempty : 0 < card (terms a)) :
    need (constructed terms false).first a = 1 := by
  have one : score (constructed terms false).first a 1 (terms a) = 4 * card (terms a) := by
    simpa using active_score terms a (terms a)
  unfold need
  change (([0, 1] : List Nat).find? fun k => fires (constructed terms false).first a k (terms a) 0).getD 2 = 1
  have silent : fires (constructed terms false).first a 0 (terms a) 0 = false := by
    unfold fires
    rw [constructed_zero_score]
    change decide ((↑(4 * card (terms a) - 2 : Nat) : Int) ≤ 0) = false
    exact decide_eq_false (by omega)
  have firing : fires (constructed terms false).first a 1 (terms a) 0 = true := by
    unfold fires
    rw [one]
    change decide ((↑(4 * card (terms a) - 2 : Nat) : Int) ≤ ↑(4 * card (terms a) : Nat)) = true
    exact decide_eq_true (by omega)
  simp [silent, firing]

private theorem constructed_first_valid (terms : Fin A → Pattern M)
    (nonempty : ∀ a, 0 < card (terms a)) :
    checkConjunctions (constructed terms false).first = true := by
  have getNeed (a : Fin A) := constructed_need terms a (nonempty a)
  have targetScore (a : Fin A) :
      score (constructed terms false).first a 1 (terms a) = 4 * card (terms a) := by
    simpa using active_score terms a (terms a)
  simp only [checkConjunctions, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr fun a _ => decide_eq_true (nonempty a)
  · apply List.all_eq_true.mpr
    intro a _
    rw [getNeed]
    change robustSilence _ 1 (score (constructed terms false).first a 0 (terms a)) && true = true
    rw [constructed_zero_score]
    simp only [decide_true, Bool.and_true]
    exact decide_eq_true (by have h := nonempty a; change 0 + 1 < 4 * card (terms a) - 2; omega)
  · apply List.all_eq_true.mpr
    intro a _
    rw [getNeed]
    change (decide (0 < 1 ∧ 1 ≤ 1) && robustFire _ 1 (score (constructed terms false).first a 1 (terms a))) = true
    rw [targetScore]
    exact Bool.and_eq_true_iff.mpr ⟨rfl,
      decide_eq_true (by
        have h := nonempty a
        change 4 * card (terms a) - 2 + 1 ≤ 4 * card (terms a)
        omega)⟩
  · apply List.all_eq_true.mpr
    intro a _
    apply List.all_eq_true.mpr
    intro j _
    rw [getNeed]
    unfold gain portWrites
    apply decide_eq_true
    change 0 + 4 * (if terms a j then 1 else 0) < 5
    split <;> decide
  · apply List.all_eq_true.mpr
    intro a _
    rw [getNeed]
    change robustFire _ 1 (score (constructed terms false).first a 1 (terms a)) = true
    rw [targetScore]
    exact decide_eq_true (by
      have h := nonempty a
      change 4 * card (terms a) - 2 + 1 ≤ 4 * card (terms a)
      omega)
  · apply List.all_eq_true.mpr
    intro a _
    apply List.all_eq_true.mpr
    intro j member
    have active : terms a j = true := (List.mem_filter.mp member).2
    rw [getNeed, active_score]
    have sub : contains (terms a) (fun k => omits j k && terms a k) = true :=
      contains_iff.mpr fun k h => (Bool.and_eq_true_iff.mp h).2
    have distinct : (fun k => omits j k && terms a k) ≠ terms a := by
      intro eq
      have h := congrFun eq j
      simp [omits, active] at h
    have lt := card_lt_of_proper sub distinct
    exact decide_eq_true (by
      change 4 * card (fun k => omits j k && terms a k) + 1 < 4 * card (terms a) - 2
      omega)

private theorem constructed_second_valid (terms : Fin A → Pattern M) :
    (constructed terms false).second.check = true := by
  unfold Disjunctions.check
  apply Bool.and_eq_true_iff.mpr
  refine ⟨rfl, List.all_eq_true.mpr ?_⟩
  intro i _
  apply Bool.and_eq_true_iff.mpr
  refine ⟨List.all_eq_true.mpr (fun a _ => ?_), ?_⟩
  · rfl
  · change ((List.finRange A).all (fun _ => true)) &&
      robustSilence 2 1 (score (readView (constructed terms false).second
        (expectedWrites (constructed terms false).second)) i 0 (fun _ => false)) = true
    have noInputs : (List.finRange A).filter (fun _ => false) = [] :=
      List.filter_eq_nil_iff.mpr (by simp)
    simp [score, noInputs, readView, constructed, robustSilence]

private theorem constructed_valid (terms : Fin A → Pattern M)
    (nonempty : ∀ a, 0 < card (terms a))
    (antichain : ∀ a b, contains (terms a) (terms b) = true → b = a) :
    (constructed terms false).Valid := by
  simp only [Cascade.Valid, Cascade.check, Bool.and_eq_true]
  refine ⟨⟨⟨⟨constructed_first_valid terms nonempty, constructed_second_valid terms⟩, ?_⟩, ?_⟩, rfl⟩
  · unfold Cascade.reachable
    apply List.all_eq_true.mpr
    intro a _
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.all_eq_true.mpr
    intro b _
    apply (beq_iff_eq ..).mpr
    change contains (terms a) (terms b) = decide (b = a)
    by_cases equal : b = a
    · subst b
      simpa using (contains_iff.mpr (fun _ h => h) : contains (terms a) (terms a) = true)
    · rw [decide_eq_false equal]
      exact Bool.eq_false_iff.mpr (fun included => equal (antichain a b included))
  · exact List.all_eq_true.mpr (fun _ _ => List.all_eq_true.mpr (fun _ _ => decide_eq_true (show (0 : Rat) ≤ 0 from by decide)))

/-- Every accepted predictor is increasing under inclusion of active input
bits. Conversely, the distinct minimal true patterns supply isolatable
conjunctions for one learned OR. -/
theorem monotone_characterization : MonotoneCharacterization := by
  intro M f
  constructor
  · intro monotone
    classical
    cases constant : f emptyPattern with
    | true =>
      refine ⟨0, 1, constructed Fin.elim0 true, 0, ?_, ?_⟩
      · change (constructed (A := 0) (M := M) Fin.elim0 true).check = true
        rfl
      · intro x
        exact (monotone emptyPattern x (empty_included x) constant).symm
    | false =>
      let terms := (allPatterns M).filter (fun t => decide (IsTerm f t))
      let term (a : Fin terms.length) := terms[a.val]
      have terms_mem {x : Pattern M} : x ∈ terms ↔ IsTerm f x := by
        simp [terms, allPatterns_complete x]
      have term_minimal (a : Fin terms.length) : IsTerm f (term a) :=
        terms_mem.mp (List.getElem_mem a.isLt)
      refine ⟨terms.length, 1, constructed term false, 0, constructed_valid term ?_ ?_, ?_⟩
      · intro a
        apply Classical.byContradiction
        intro zero
        have noPorts : term a = emptyPattern := by
          funext j
          cases h : term a j
          · rfl
          · have member : j ∈ (List.finRange M).filter (term a) := by simp [h]
            have pos : 0 < card (term a) := List.length_pos_of_mem member
            omega
        have h := (term_minimal a).1
        rw [noPorts, constant] at h
        contradiction
      · intro a b included
        have equal : term b = term a :=
          (term_minimal a).2 _ included (term_minimal b).1
        have unique : terms.Nodup := (allPatterns_nodup M).filter _
        exact Fin.ext ((unique.getElem_inj).mp equal)
      · intro x
        change (false || (List.finRange terms.length).any
          (fun a => true && contains x (term a))) = f x
        simp only [Bool.false_or, Bool.true_and]
        apply Bool.eq_iff_iff.mpr
        rw [List.any_eq_true]
        constructor
        · rintro ⟨a, _, included⟩
          exact monotone _ _ included (term_minimal a).1
        · intro trueAtX
          obtain ⟨t, included, minimal⟩ := has_term f x trueAtX
          obtain ⟨a, ha, haTerm⟩ := List.getElem_of_mem (terms_mem.mpr minimal)
          refine ⟨⟨a, ha⟩, List.mem_finRange _, ?_⟩
          simpa [term, haTerm] using included
  · rintro ⟨A, B, p, i, valid, realizes⟩ x y included trueAtX
    rw [← realizes x] at trueAtX
    rw [← realizes y]
    exact output_monotone p valid i x y included trueAtX

end LearnedCoincidence.MonotoneDNF
