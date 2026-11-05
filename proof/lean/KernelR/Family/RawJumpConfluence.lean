import KernelR.Family.Model
import KernelR.HybridSnapshotObservational

/-! The raw-current critical pairs of zero-time jump confluence. No ordering
priority is imposed: independent RAW expiries and due deliveries commute,
while duplicate presentations of the same due token have equivalent results. -/
/-! Parametric port of the corresponding `KernelR.Hybrid` critical-pair proof.
Threshold values and pulse width are parameters; no numerical inequality is used. -/
namespace KernelR.Family
open KernelR.Hybrid

/-- The concrete target of an operational delivery. -/
def Snapshot.afterArrival {n} (s : Snapshot n) (d : Delivery n)
    (before after : List (Delivery n)) : Snapshot n :=
  { (setRaw s d.cell d.port (some s.time)) with pending:=before++after }

/-- A local diamond allows either the same observation already, or one legal
jump on each arm to observations which agree. -/
def JumpDiamond {n} (c : Constants) (route : Router n) (u v : Snapshot n) : Prop :=
  u.ObservationalEq v ∨ ∃ u' v', Nonempty (Jump c route u u') ∧
    Nonempty (Jump c route v v') ∧ u'.ObservationalEq v'

theorem setRaw_other {n} (s : Snapshot n) (i j : Fin n) (p q : Port)
    (r : Option ℝ) (h : i≠j ∨ p≠q) :
    (setRaw s i p r).raw j q=s.raw j q := by
  by_cases hc : j=i <;> by_cases hp : q=p <;>
    simp_all [setRaw]

theorem setRaw_commute {n} (s : Snapshot n) (i j : Fin n) (p q : Port)
    (r t : Option ℝ) (h : i≠j ∨ p≠q) :
    setRaw (setRaw s i p r) j q t=setRaw (setRaw s j q t) i p r := by
  cases s
  simp only [setRaw]
  congr 1
  funext k a
  by_cases hk : k=i <;> by_cases hl : k=j <;>
    by_cases hp : a=p <;> by_cases hq : a=q <;>
    simp_all [Function.update_apply]

/-- Two distinct removals from a multiset presentation can be continued in
either order, leaving permutation-equivalent residual lists. -/
theorem queue_removal_diamond {α} {Q A B : List α} {d e : α}
    (hA : Q.Perm (d::A)) (hB : Q.Perm (e::B)) (hne : d≠e) :
    ∃ ba aa bb ab, A=ba++e::aa ∧ B=bb++d::ab ∧
      (ba++aa).Perm (bb++ab) := by
  have heA : e∈A := by
    have hm : e∈d::A := hA.mem_iff.mp (hB.mem_iff.mpr (by simp))
    simpa only [List.mem_cons,Ne.symm hne,false_or] using hm
  have hdB : d∈B := by
    have hm : d∈e::B := hB.mem_iff.mp (hA.mem_iff.mpr (by simp))
    simpa only [List.mem_cons,hne,false_or] using hm
  obtain ⟨ba,aa,ha⟩ := List.mem_iff_append.mp heA
  obtain ⟨bb,ab,hb⟩ := List.mem_iff_append.mp hdB
  refine ⟨ba,aa,bb,ab,ha,hb,?_⟩
  have hAA : Q.Perm (d::e::(ba++aa)) := by
    rw [ha] at hA
    exact hA.trans (List.Perm.cons _ List.perm_middle)
  have hBB : Q.Perm (e::d::(bb++ab)) := by
    rw [hb] at hB
    exact hB.trans (List.Perm.cons _ List.perm_middle)
  exact List.Perm.cons_inv (List.Perm.cons_inv
    (hAA.symm.trans (hBB.trans (List.Perm.swap _ _ _))))

/-- Due deliveries at one RAW address are the same token value. -/
theorem due_delivery_eq_of_address {n} {s : Snapshot n} {d e : Delivery n}
    (hd : d.due=s.time) (he : e.due=s.time)
    (hc : d.cell=e.cell) (hp : d.port=e.port) : d=e := by
  cases d; cases e
  simp_all

/-- RAW expiries either coincide or commute; each expiry has no FIRE label. -/
theorem rawEnd_rawEnd_diamond {n c route} (s : Snapshot n)
    (i j : Fin n) (p q : Port) (o r : ℝ)
    (hi : s.raw i p=some o) (hj : s.raw j q=some r)
    (hti : s.time=o+c.pulseWidth) (htj : s.time=r+c.pulseWidth) :
    JumpDiamond c route (setRaw s i p none) (setRaw s j q none) := by
  by_cases hc : i=j
  · subst j
    by_cases hp : p=q
    · subst q
      exact Or.inl (.refl _)
    · refine Or.inr ⟨_,_,⟨Jump.rawEnd _ i q r ?_ htj⟩,
        ⟨Jump.rawEnd _ i p o ?_ hti⟩,?_⟩
      · simpa only [setRaw_other s i i p q none (Or.inr hp)] using hj
      · simpa only [setRaw_other s i i q p none (Or.inr (Ne.symm hp))] using hi
      · rw [setRaw_commute s i i p q none none (Or.inr hp)]
        exact .refl _
  · refine Or.inr ⟨_,_,⟨Jump.rawEnd _ j q r ?_ htj⟩,
      ⟨Jump.rawEnd _ i p o ?_ hti⟩,?_⟩
    · simpa only [setRaw_other s i j p q none (Or.inl hc)] using hj
    · simpa only [setRaw_other s j i q p none (Or.inl (Ne.symm hc))] using hi
    · rw [setRaw_commute s i j p q none none (Or.inl hc)]
      exact .refl _

/-- An enabled delivery and an enabled expiry cannot share a RAW address.
Consequently their residual physical state is independent of jump order. -/
theorem arrive_rawEnd_diamond {n c route} (s : Snapshot n) (d : Delivery n)
    (before after : List (Delivery n)) (hq : s.pending=before++d::after)
    (hd : d.due=s.time) (hf : s.raw d.cell d.port=none)
    (i : Fin n) (p : Port) (o : ℝ) (ha : s.raw i p=some o)
    (ht : s.time=o+c.pulseWidth) :
    JumpDiamond c route (Snapshot.afterArrival s d before after) (setRaw s i p none) := by
  have hdiff : d.cell≠i ∨ d.port≠p := by
    by_cases hc : d.cell=i
    · right
      intro hp
      rw [hc,hp,ha] at hf
      contradiction
    · exact Or.inl hc
  refine Or.inr ⟨_,_,⟨Jump.rawEnd _ i p o ?_ ht⟩,
    ⟨Jump.arrive _ d before after hq hd ?_⟩,?_⟩
  · change (setRaw s d.cell d.port (some s.time)).raw i p=some o
    rw [setRaw_other s d.cell i d.port p (some s.time) hdiff]
    exact ha
  · rw [setRaw_other s i d.cell p d.port none (hdiff.elim
      (fun h => Or.inl (Ne.symm h)) (fun h => Or.inr (Ne.symm h)))]
    exact hf
  · refine ⟨rfl,rfl,rfl,rfl,?_,List.Perm.refl _⟩
    have h := congrArg Snapshot.raw (setRaw_commute s d.cell i d.port p
      (some s.time) none hdiff)
    exact h

/-- Two enabled deliveries either name the same due token (including duplicate
queue positions), or legally commute at independent RAW addresses. -/
theorem arrive_arrive_diamond {n c route} (s : Snapshot n) (d e : Delivery n)
    (b₁ a₁ b₂ a₂ : List (Delivery n))
    (hq₁ : s.pending=b₁++d::a₁) (hq₂ : s.pending=b₂++e::a₂)
    (hd : d.due=s.time) (he : e.due=s.time)
    (hf₁ : s.raw d.cell d.port=none) (hf₂ : s.raw e.cell e.port=none) :
    JumpDiamond c route (Snapshot.afterArrival s d b₁ a₁) (Snapshot.afterArrival s e b₂ a₂) := by
  have hA : s.pending.Perm (d::(b₁++a₁)) := by rw [hq₁]; exact List.perm_middle
  have hB : s.pending.Perm (e::(b₂++a₂)) := by rw [hq₂]; exact List.perm_middle
  by_cases hde : d=e
  · subst e
    exact Or.inl ⟨rfl,rfl,rfl,rfl,rfl,List.Perm.cons_inv (hA.symm.trans hB)⟩
  · have hdiff : d.cell≠e.cell ∨ d.port≠e.port := by
      by_cases hc : d.cell=e.cell
      · right
        intro hp
        exact hde (due_delivery_eq_of_address hd he hc hp)
      · exact Or.inl hc
    obtain ⟨ba,aa,bb,ab,hAA,hBB,hrest⟩ := queue_removal_diamond hA hB hde
    refine Or.inr ⟨_,_,⟨Jump.arrive _ e ba aa hAA he ?_⟩,
      ⟨Jump.arrive _ d bb ab hBB hd ?_⟩,?_⟩
    · change (setRaw s d.cell d.port (some s.time)).raw e.cell e.port=none
      rw [setRaw_other s d.cell e.cell d.port e.port (some s.time) hdiff]
      exact hf₂
    · change (setRaw s e.cell e.port (some s.time)).raw d.cell d.port=none
      rw [setRaw_other s e.cell d.cell e.port d.port (some s.time) (hdiff.elim
        (fun h => Or.inl (Ne.symm h)) (fun h => Or.inr (Ne.symm h)))]
      exact hf₁
    · refine ⟨rfl,rfl,rfl,rfl,?_,hrest⟩
      have h := congrArg Snapshot.raw (setRaw_commute s d.cell e.cell d.port e.port
        (some s.time) (some s.time) hdiff)
      simpa only [Snapshot.afterArrival,setRaw] using h

end KernelR.Family
