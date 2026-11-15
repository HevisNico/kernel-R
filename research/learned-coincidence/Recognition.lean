import Target

namespace LearnedCoincidence

private theorem allPorts {P : Fin M → Bool} (h : (List.finRange M).all P = true) (j : Fin M) :
    P j = true :=
  List.all_eq_true.mp h j (List.mem_finRange j)

private theorem fire_of_margin {p : Parameters N M} {i : Fin N} {k : Nat} {x : Pattern M}
    {budget : Nat} {e : Int} (margin : p.threshold i + budget ≤ score p i k x)
    (error : admissible budget e) : fires p i k x e = true := by
  unfold fires
  exact decide_eq_true (by
    have lower := error.1
    omega)

private theorem silence_of_margin {p : Parameters N M} {i : Fin N} {k : Nat} {x : Pattern M}
    {budget : Nat} {e : Int} (margin : score p i k x + budget < p.threshold i)
    (error : admissible budget e) : fires p i k x e = false := by
  unfold fires
  exact decide_eq_false (by
    have upper := error.2
    omega)

private theorem sum_order {α : Type} (ports : List α) (x y : α → Bool) (g h : α → Nat)
    (subset : ∀ j, x j = true → y j = true) (gains : ∀ j, g j ≤ h j) :
    ((ports.filter x).map g).sum ≤ ((ports.filter y).map h).sum := by
  induction ports with
  | nil => exact Nat.le_refl 0
  | cons j rest ih =>
    cases inside : x j with
    | false =>
      cases seen : y j with
      | false => simpa [inside, seen] using ih
      | true => simpa [inside, seen] using (Nat.le_trans ih (Nat.le_add_left _ (h j)))
    | true =>
      have seen := subset j inside
      simpa [inside, seen] using Nat.add_le_add (gains j) ih

private theorem gain_order (p : Parameters N M) (i : Fin N) (j : Fin M) {k l : Nat} (hle : k ≤ l) :
    gain p i k j ≤ gain p i l j := by
  unfold gain portWrites
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  split
  · exact hle
  · exact Nat.le_refl 0

private theorem score_order (p : Parameters N M) (i : Fin N) {k l : Nat} {x y : Pattern M}
    (rounds : k ≤ l) (subset : ∀ j, x j = true → y j = true) :
    score p i k x ≤ score p i l y :=
  Nat.add_le_add_left (sum_order _ x y _ _ subset (fun j => gain_order p i j rounds)) _

private theorem contains_ports {x t : Pattern M} (h : contains x t = true) (j : Fin M)
    (active : t j = true) : x j = true := by
  have h := allPorts h j
  simpa [active] using h

private theorem missing_port {x t : Pattern M} (h : contains x t = false) :
    ∃ j, t j = true ∧ x j = false := by
  obtain ⟨j, _, missing⟩ := List.all_eq_false.mp h
  cases needed : t j with
  | false => simp [needed] at missing
  | true =>
    cases present : x j with
    | false => exact ⟨j, needed, present⟩
    | true => simp [needed, present] at missing

private theorem training_count_on_path (p : Parameters N M) (errors : Nat → Fin N → Int)
    (decision : ∀ r i, fires p i (min r (need p i)) (p.target i) (errors r i) = decide (need p i ≤ r)) :
    ∀ r i, trainingCount p errors i r = min r (need p i) := by
  intro r i
  induction r with
  | zero => simp [trainingCount]
  | succ r ih =>
    rw [trainingCount, ih, decision]
    by_cases stopped : need p i ≤ r
    · have next : need p i ≤ r + 1 := by omega
      simp [stopped, Nat.min_eq_right next]
    · have now : r ≤ need p i := by omega
      have next : r + 1 ≤ need p i := by omega
      simp [stopped, Nat.min_eq_left now, Nat.min_eq_left next]

/-- All bounded errors preserve the predicted stopping counts and all test
decisions. The proof uses the same checker and transition as the frozen target. -/
theorem learned_coincidence_recognition : LearnedCoincidenceRecognition := by
  intro N M p valid errors bounds
  simp only [Parameters.Valid, Parameters.check, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨⟨_, early⟩, stop⟩, rail⟩, positive⟩, negative⟩ := valid
  have stops (i : Fin N) : need p i ≤ p.maxWrites ∧
      p.threshold i + p.trainingError i ≤ score p i (need p i) (p.target i) := by
    have h := Bool.and_eq_true_iff.mp (allPorts stop i)
    exact ⟨(of_decide_eq_true h.1 : 0 < need p i ∧ need p i ≤ p.maxWrites).2,
      of_decide_eq_true h.2⟩
  have path (r : Nat) (i : Fin N) :
      fires p i (min r (need p i)) (p.target i) (errors r i) = decide (need p i ≤ r) := by
    by_cases stopped : need p i ≤ r
    · rw [Nat.min_eq_right stopped, decide_eq_true stopped]
      exact fire_of_margin (stops i).2 (bounds r i)
    · have before : r < need p i := by omega
      have h := List.all_eq_true.mp (allPorts early i) r (List.mem_range.mpr before)
      rw [Nat.min_eq_left (Nat.le_of_lt before), decide_eq_false stopped]
      exact silence_of_margin (of_decide_eq_true h) (bounds r i)
  have count := training_count_on_path p errors path
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r i
    exact ⟨count r i, by rw [trainingFire, count]; exact path r i⟩
  · intro r i j
    rw [count]
    have hle : min r (need p i) ≤ need p i := Nat.min_le_right _ _
    refine ⟨?_, Nat.lt_of_le_of_lt (gain_order p i j hle) (of_decide_eq_true (allPorts (allPorts rail i) j))⟩
    unfold portWrites
    split
    · exact Nat.le_trans hle (stops i).1
    · exact Nat.zero_le _
  · intro r enough i j
    rw [count r i, Nat.min_eq_right (Nat.le_trans (stops i).1 enough)]
  · intro x readErrors testBounds i
    have enough : need p i ≤ p.maxWrites + 1 := by have h := (stops i).1; omega
    rw [testFire, count, Nat.min_eq_right enough]
    unfold predicted
    cases hit : contains x (p.target i) with
    | true =>
      have margin : p.threshold i + p.testingError i ≤ score p i (need p i) (p.target i) :=
        of_decide_eq_true (allPorts positive i)
      exact fire_of_margin (Nat.le_trans margin (score_order p i (Nat.le_refl _) (contains_ports hit)))
        (testBounds i)
    | false =>
      obtain ⟨j, target, absent⟩ := missing_port hit
      have h := List.all_eq_true.mp (allPorts negative i) j
        (List.mem_filter.mpr ⟨List.mem_finRange j, target⟩)
      have margin : score p i (need p i) (omits j) + p.testingError i < p.threshold i :=
        of_decide_eq_true h
      have subset (q : Fin M) (active : x q = true) : omits j q = true := by
        unfold omits
        apply decide_eq_true
        intro same
        subst q
        rw [absent] at active
        contradiction
      have smaller := score_order p i (Nat.le_refl (need p i)) subset
      exact silence_of_margin (Nat.lt_of_le_of_lt (Nat.add_le_add_right smaller _) margin)
        (testBounds i)

end LearnedCoincidence
