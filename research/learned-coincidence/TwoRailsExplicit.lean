import MonotoneRecognition
import TwoRailsTarget

/-! A constructive, public form of `every_function_on_two_rails`. It exposes the
cascade: every first-layer target is the pair of rails of an input pattern that
makes the function true. Training through inverters needs that, since the
inverters can only produce rails patterns.

The construction and its validity proof are copied from
`MonotoneCharacterization.lean` and `TwoRails.lean`, where they are private;
those files are not changed. -/

namespace LearnedCoincidence.MonotoneDNF.RailsExplicit

open LearnedCoincidence.MonotoneDNF

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


/-- Copied from `TwoRails.lean`, where it is private. -/
private theorem same_of_rails_contained {M : Nat} {x y : Pattern M}
    (inside : contains (rails x) (rails y) = true) : y = x := by
  funext j
  have low := contains_iff.mp inside ⟨j.val, by omega⟩
  have high := contains_iff.mp inside ⟨M + j.val, by omega⟩
  have hj : j.val < M := j.isLt
  simp only [rails, hj, dite_true] at low
  have nj : ¬ (M + j.val < M) := by omega
  have idx : (⟨M + j.val - M, by omega⟩ : Fin M) = j := Fin.ext (by simp)
  simp only [rails, nj, dite_false, idx] at high
  cases hy : y j <;> cases hx : x j <;> simp_all

private theorem rails_card_pos {M : Nat} (positive : 0 < M) (x : Pattern M) : 0 < card (rails x) := by
  cases h : x ⟨0, positive⟩
  · have on : rails x ⟨M, by omega⟩ = true := by
      simp only [rails, show ¬ (M < M) from by omega, dite_false]
      have idx : (⟨M - M, by omega⟩ : Fin M) = ⟨0, positive⟩ := Fin.ext (by simp)
      rw [idx, h]; rfl
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_finRange _, on⟩)
  · have on : rails x ⟨0, by omega⟩ = true := by
      simp only [rails, show (0 < M) from positive, dite_true]
      exact h
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_finRange _, on⟩)

/-- Frozen target: for every Boolean function `f` of `M` inputs there is an
admissible cascade on `2 M` lines whose predicted answer on the rails is `f`,
and whose first-layer targets are all rails of input patterns where `f` is true. -/
def EveryFunctionOnTwoRailsExplicit : Prop :=
  ∀ (M : Nat) (f : Pattern M → Bool),
    ∃ (A B : Nat) (p : Cascade A B (M + M)) (i : Fin B),
      p.Valid ∧ (∀ x, output p i (rails x) = f x) ∧
      ∀ a, ∃ x, f x = true ∧ p.first.target a = rails x

theorem every_function_on_two_rails_explicit : EveryFunctionOnTwoRailsExplicit := by
  intro M f
  by_cases zero : M = 0
  · subst zero
    let only : Pattern 0 := Fin.elim0
    have unique : ∀ x : Pattern 0, x = only := fun x => funext fun j => j.elim0
    cases value : f only with
    | false =>
      refine ⟨0, 1, constructed (M := 0 + 0) Fin.elim0 false, 0,
        constructed_valid _ (fun a => a.elim0) (fun a => a.elim0), ?_, fun a => a.elim0⟩
      intro x
      rw [unique x, value]
      rfl
    | true =>
      refine ⟨0, 1, constructed (M := 0 + 0) Fin.elim0 true, 0, ?_, ?_, fun a => a.elim0⟩
      · change (constructed (A := 0) (M := 0 + 0) Fin.elim0 true).check = true
        rfl
      · intro x
        rw [unique x, value]
        rfl
  · have positive : 0 < M := Nat.pos_of_ne_zero zero
    let xs := (allPatterns M).filter f
    let term (a : Fin xs.length) : Pattern (M + M) := rails xs[a.val]
    have member (a : Fin xs.length) : xs[a.val] ∈ xs := List.getElem_mem a.isLt
    have good (a : Fin xs.length) : f xs[a.val] = true := (List.mem_filter.mp (member a)).2
    have unique : xs.Nodup := (allPatterns_nodup M).filter _
    have antichain : ∀ a b, contains (term a) (term b) = true → b = a := by
      intro a b inside
      have same : xs[b.val] = xs[a.val] := same_of_rails_contained inside
      exact Fin.ext ((unique.getElem_inj).mp same)
    refine ⟨xs.length, 1, constructed term false, 0,
      constructed_valid term (fun a => rails_card_pos positive _) antichain, ?_,
      fun a => ⟨xs[a.val], good a, rfl⟩⟩
    intro y
    change (false || (List.finRange xs.length).any
      (fun a => true && contains (rails y) (term a))) = f y
    simp only [Bool.false_or, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true]
    constructor
    · rintro ⟨a, _, inside⟩
      have same : xs[a.val] = y := same_of_rails_contained inside
      rw [← same]
      exact good a
    · intro holds
      have mem : y ∈ xs := List.mem_filter.mpr ⟨allPatterns_complete y, holds⟩
      obtain ⟨k, hk, at_k⟩ := List.getElem_of_mem mem
      refine ⟨⟨k, hk⟩, List.mem_finRange _, ?_⟩
      change contains (rails y) (rails xs[k]) = true
      rw [at_k]
      exact contains_iff.mpr fun _ h => h

end LearnedCoincidence.MonotoneDNF.RailsExplicit
