import NativePeriodicRingTarget

namespace NetworkStability.NativePeriodicRing

open KernelR.Hybrid
open NativeRing (Input inputCell inputPort root successor)

def planFor (p : Parameters N) : Input N → Option Nat
  | .inl i => dosePlan (p.ring.forwardAmplitude i)
  | .inr _ => dosePlan p.ring.returnAmplitude

def initialAmplitude (p : Parameters N) : Input N → ℚ
  | .inl i => p.ring.forwardAmplitude i
  | .inr _ => p.ring.returnAmplitude

def planned (p : Parameters N) (key : Input N) : Nat := (planFor p key).getD 0

def earned (p : Parameters N) (lap : Nat) (key : Input N) : Nat :=
  ((trainingOrder p).take lap).count key

theorem physical_amplitude_bounds :
    (911 / 500 : ℝ) ≤ Real.exp (3 / 5) ∧ Real.exp (3 / 5) ≤ 1823 / 1000 := by
  have estimate := Real.exp_bound (x := (3 / 5 : ℝ)) (n := 8) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at estimate
  have h := abs_le.mp estimate
  constructor <;> linarith [h.1, h.2]

theorem amplitude_enclosure {a : ℚ} (positive : 0 < a) (k : Nat) :
    (lowerAmplitude a k : ℝ) ≤ Real.exp (Real.log a + (3 / 5 : ℝ) * k) ∧
    Real.exp (Real.log a + (3 / 5 : ℝ) * k) ≤ (upperAmplitude a k : ℝ) := by
  have pos : (0 : ℝ) < a := by exact_mod_cast positive
  rw [Real.exp_add, Real.exp_log pos, mul_comm (3 / 5 : ℝ), Real.exp_nat_mul]
  push_cast [lowerAmplitude, upperAmplitude]
  exact ⟨mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) physical_amplitude_bounds.1 _) pos.le,
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.exp_pos _).le physical_amplitude_bounds.2 _) pos.le⟩

theorem checked_plan {a : ℚ} {total : Nat} (plan : dosePlan a = some total) :
    total ≤ Q ∧ strongAt a total = true ∧ ∀ k < total, weakAt a k = true := by
  have seen := List.mem_of_find?_eq_some plan
  have cert := List.find?_some plan
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at cert
  exact ⟨Nat.le_of_lt_succ (List.mem_range.mp seen), cert.1, cert.2⟩

theorem plan_exists {p : Parameters N} (member : p.Valid) (key : Input N) :
    dosePlan (initialAmplitude p key) = some (planned p key) := by
  have present : (planFor p key).isSome = true := by
    rcases key with i | ⟨⟩
    · have branch := member.2.2.2.1 i
      split at branch
      · simp [planFor, branch]
      · exact branch
    · exact member.2.2.2.2.1
  rw [show dosePlan (initialAmplitude p key) = planFor p key by cases key <;> rfl]
  cases found : planFor p key with
  | none => simp [found] at present
  | some k => simp [planned, found]

theorem initial_positive {p : Parameters N} (member : p.Valid) (key : Input N) :
    0 < initialAmplitude p key := by
  have cert := (checked_plan (plan_exists member key)).2
  by_cases zero : planned p key = 0
  · have strong := of_decide_eq_true (show strongAt (initialAmplitude p key) 0 = true by
      simpa only [zero] using cert.1)
    unfold strongAt at *
    norm_num [lowerAmplitude] at strong
    linarith [strong.1]
  · have weak := cert.2 0 (Nat.pos_of_ne_zero zero)
    exact (of_decide_eq_true weak : 0 < initialAmplitude p key ∧
      upperAmplitude (initialAmplitude p key) 0 ≤ 1).1

theorem checked_native_strong {p : Parameters N} (member : p.Valid) (key : Input N) :
    (9 / 5 : ℝ) ≤ Real.exp (Real.log (initialAmplitude p key) + (3 / 5 : ℝ) * planned p key) ∧
    Real.exp (Real.log (initialAmplitude p key) + (3 / 5 : ℝ) * planned p key) ≤ 2 := by
  have h := (checked_plan (plan_exists member key)).2.1
  have bounds : 9 / 5 ≤ lowerAmplitude (initialAmplitude p key) (planned p key) ∧
      upperAmplitude (initialAmplitude p key) (planned p key) ≤ 2 := of_decide_eq_true h
  have encl := amplitude_enclosure (initial_positive member key) (planned p key)
  exact ⟨(by simpa using (Rat.cast_le (K := ℝ)).2 bounds.1 : (9 / 5 : ℝ) ≤ _).trans encl.1,
    encl.2.trans (by exact_mod_cast bounds.2)⟩

theorem checked_native_weak {p : Parameters N} (member : p.Valid) (key : Input N) (k : Nat)
    (before : k < planned p key) :
    Real.exp (Real.log (initialAmplitude p key) + (3 / 5 : ℝ) * k) ≤ 1 := by
  have h := (checked_plan (plan_exists member key)).2.2 k before
  have upper : upperAmplitude (initialAmplitude p key) k ≤ 1 :=
    (of_decide_eq_true h : 0 < initialAmplitude p key ∧ upperAmplitude (initialAmplitude p key) k ≤ 1).2
  exact (amplitude_enclosure (initial_positive member key) k).2.trans (by exact_mod_cast upper)

private theorem training_eq_expand (p : Parameters N) :
    trainingOrder p = (ports N).flatMap (fun key => List.replicate (planned p key) key) := by
  simp [trainingOrder, ports, List.flatMap_append, List.flatMap_map, planned, planFor]

theorem ports_nodup (N : Nat) : (ports N).Nodup := by
  have h : ((List.finRange N).map (Sum.inl : Fin N → Input N)).Nodup :=
    (List.nodup_finRange N).map Sum.inl_injective
  rw [ports, List.nodup_append]
  refine ⟨h, by simp, ?_⟩
  simp

theorem key_in_ports (key : Input N) : key ∈ ports N := by
  rcases key with i | ⟨⟩ <;> simp [ports, List.mem_finRange]

private theorem mem_expanded {α : Type} (n : α → Nat) (ys : List α) {k : α}
    (seen : k ∈ ys.flatMap (fun x => List.replicate (n x) x)) : k ∈ ys := by
  obtain ⟨x, hx, found⟩ := List.mem_flatMap.mp seen
  exact (List.eq_of_mem_replicate found).symm ▸ hx

private theorem count_expanded {α : Type} [BEq α] [LawfulBEq α] (n : α → Nat) (ys : List α)
    (distinct : ys.Nodup) (k : α) (seen : k ∈ ys) :
    (ys.flatMap (fun x => List.replicate (n x) x)).count k = n k := by
  induction ys with
  | nil => simp at seen
  | cons x xs ih =>
    have d := List.nodup_cons.mp distinct
    simp only [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp seen with rfl | tail
    · rw [List.count_replicate_self, List.count_eq_zero_of_not_mem (fun seen =>
        d.1 (mem_expanded n xs seen)), Nat.add_zero]
    · have different : x ≠ k := fun eq => d.1 (eq ▸ tail)
      rw [List.count_eq_zero_of_not_mem (fun h => different (List.eq_of_mem_replicate h).symm),
        ih d.2 tail, Nat.zero_add]

theorem total_count (p : Parameters N) (key : Input N) :
    (trainingOrder p).count key = planned p key := by
  rw [training_eq_expand]
  exact count_expanded _ _ (ports_nodup N) key (key_in_ports key)

theorem earned_bound (p : Parameters N) (lap : Nat) (key : Input N) :
    earned p lap key ≤ planned p key := by
  rw [← total_count p key]
  exact (List.take_sublist lap (trainingOrder p)).count_le key

private theorem split_expanded {α : Type} (n : α → Nat) (ys : List α) (lap : Nat) (k : α)
    (next : (ys.flatMap (fun x => List.replicate (n x) x))[lap]? = some k) :
    ∃ left right used, ys = left ++ k :: right ∧ used < n k ∧
      (ys.flatMap (fun x => List.replicate (n x) x)).take lap =
        left.flatMap (fun x => List.replicate (n x) x) ++ List.replicate used k := by
  induction ys generalizing lap with
  | nil => simp at next
  | cons x xs ih =>
    rw [List.flatMap_cons] at next ⊢
    by_cases before : lap < n x
    · have within : lap < (List.replicate (n x) x).length := by simpa using before
      rw [List.getElem?_append_left within] at next
      have same : x = k := by
        simpa [List.getElem?_replicate_of_lt before] using next
      subst k
      refine ⟨[], xs, lap, rfl, before, ?_⟩
      rw [List.take_append_of_le_length within.le]
      simp [Nat.min_eq_left before.le]
    · have beyond : (List.replicate (n x) x).length ≤ lap := by simpa using Nat.le_of_not_gt before
      rw [List.getElem?_append_right beyond, List.length_replicate] at next
      obtain ⟨left, right, used, split, lt, taken⟩ := ih (lap - n x) next
      refine ⟨x :: left, right, used, ?_, lt, ?_⟩
      · simp only [List.cons_append, List.cons.injEq, true_and]
        exact split
      · rw [List.take_append, List.take_of_length_le beyond, List.length_replicate, taken,
          List.flatMap_cons, List.append_assoc]

/-- The first untrained port follows a prefix of fully trained relays. -/
theorem training_branch (p : Parameters N) (lap : Nat) {key : Input N}
    (next : (trainingOrder p)[lap]? = some key) :
    ∃ left right, ports N = left ++ key :: right ∧ firingKeys p lap = left ∧
      admittedKeys p lap = left ++ [key] ∧ earned p lap key < planned p key ∧
      ∀ k ∈ left, earned p lap k = planned p k := by
  have atKey := next
  rw [training_eq_expand] at atKey
  obtain ⟨left, right, used, order, lt, counts⟩ :=
    split_expanded (planned p) (ports N) lap key atKey
  have nodup := ports_nodup N
  rw [order, List.nodup_append] at nodup
  have absent : key ∉ left := fun seen => nodup.2.2 key seen key (by simp) rfl
  have firing : firingKeys p lap = left := by
    unfold firingKeys
    rw [next, order, List.takeWhile_append_of_pos (fun k seen => by
      simp [show k ≠ key from fun h => absent (h ▸ seen)])]
    simp
  have expand : (trainingOrder p).take lap =
      left.flatMap (fun k => List.replicate (planned p k) k) ++ List.replicate used key := by
    rw [training_eq_expand]
    exact counts
  refine ⟨left, right, order, firing, by simp [admittedKeys, firing, next], ?_, ?_⟩
  · unfold earned
    rw [expand, List.count_append, List.count_eq_zero_of_not_mem
        (fun seen => absent (mem_expanded _ _ seen)), List.count_replicate_self, Nat.zero_add]
    exact lt
  · intro k seen
    have different : key ≠ k := fun eq => absent (eq.symm ▸ seen)
    unfold earned
    rw [expand, List.count_append, count_expanded _ _ nodup.1 k seen,
      List.count_eq_zero_of_not_mem (fun h => different (List.eq_of_mem_replicate h).symm), Nat.add_zero]

theorem trained_branch (p : Parameters N) (lap : Nat) (next : (trainingOrder p)[lap]? = none) :
    firingKeys p lap = ports N ∧ admittedKeys p lap = ports N ∧
      ∀ key, earned p lap key = planned p key := by
  have full : (trainingOrder p).length ≤ lap := List.getElem?_eq_none_iff.mp next
  have word : firingKeys p lap = ports N := by
    rw [firingKeys, next]
    have pred : (fun key : Input N => decide (some key ≠ none)) = (fun _ => true) := by
      funext key
      simp
    rw [pred]
    induction ports N with
    | nil => rfl
    | cons key rest ih => rw [List.takeWhile_cons_of_pos (by decide), ih]
  exact ⟨word, by simp [admittedKeys, word, next], fun k => by
    rw [earned, List.take_of_length_le full, total_count]⟩

theorem earned_next (p : Parameters N) (lap : Nat) (k : Input N) :
    earned p (lap + 1) k = earned p lap k +
      if (trainingOrder p)[lap]? = some k then 1 else 0 := by
  rcases next : (trainingOrder p)[lap]? with _ | key
  · have full : (trainingOrder p).length ≤ lap := List.getElem?_eq_none_iff.mp next
    simp [earned, List.take_of_length_le full, List.take_of_length_le (full.trans (Nat.le_succ _))]
  · obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp next
    by_cases eq : key = k
    · subst k
      simp [earned, List.take_succ_eq_append_getElem within, same]
    · simp [earned, List.take_succ_eq_append_getElem within, same, eq]

end NetworkStability.NativePeriodicRing
