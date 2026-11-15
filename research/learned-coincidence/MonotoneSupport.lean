import MonotoneTarget

namespace LearnedCoincidence.MonotoneDNF

theorem allPorts {P : Fin M → Bool} (h : (List.finRange M).all P = true) (j : Fin M) :
    P j = true :=
  List.all_eq_true.mp h j (List.mem_finRange j)

theorem contains_iff {x t : Pattern M} :
    contains x t = true ↔ ∀ j, t j = true → x j = true := by
  constructor
  · intro h j active
    simpa [active] using allPorts h j
  · intro h
    apply List.all_eq_true.mpr
    intro j _
    cases active : t j with
    | false => rfl
    | true => simpa using h j active

theorem missingPort {x t : Pattern M} (h : contains x t = false) :
    ∃ j, t j = true ∧ x j = false := by
  obtain ⟨j, _, missing⟩ := List.all_eq_false.mp h
  cases ht : t j <;> cases hx : x j <;> simp_all
  exact ⟨j, ht, hx⟩

theorem filteredSum_le {α : Type} (ports : List α) (x y : α → Bool) (g h : α → Nat)
    (subset : ∀ j, x j = true → y j = true) (gains : ∀ j, g j ≤ h j) :
    ((ports.filter x).map g).sum ≤ ((ports.filter y).map h).sum := by
  induction ports with
  | nil => exact Nat.le_refl 0
  | cons j rest ih =>
    cases active : x j with
    | false =>
      cases seen : y j with
      | false => simpa [active, seen] using ih
      | true => simpa [active, seen] using Nat.le_trans ih (Nat.le_add_left _ (h j))
    | true =>
      simpa [active, subset j active] using Nat.add_le_add (gains j) ih

theorem gain_le (p : Parameters N M) (i : Fin N) (a : Fin M) {k l : Nat} (h : k ≤ l) :
    gain p i k a ≤ gain p i l a := by
  unfold gain portWrites
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  split
  · exact h
  · exact Nat.le_refl 0

theorem score_le (p : Parameters N M) (i : Fin N) {k l : Nat} {x y : Pattern M}
    (rounds : k ≤ l) (subset : ∀ j, x j = true → y j = true) :
    score p i k x ≤ score p i l y :=
  Nat.add_le_add_left (filteredSum_le _ x y _ _ subset (fun j => gain_le p i j rounds)) _

theorem filter_single {α : Type} [DecidableEq α] {xs : List α} (unique : xs.Nodup)
    {a : α} (inList : a ∈ xs) : xs.filter (fun b => decide (b = a)) = [a] := by
  induction xs with
  | nil => simp at inList
  | cons b rest ih =>
    have h := List.nodup_cons.mp unique
    by_cases same : b = a
    · subst b
      have none : rest.filter (fun b => decide (b = a)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c member equal
        have equal := of_decide_eq_true equal
        subst c
        exact h.1 member
      simp [none]
    · have member : a ∈ rest := (List.mem_cons.mp inList).resolve_left (Ne.symm same)
      simp [same, ih h.2 member]

end LearnedCoincidence.MonotoneDNF
