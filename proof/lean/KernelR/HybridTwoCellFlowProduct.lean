import KernelR.HybridStagedBirth
import KernelR.HybridFlowCuts

/-! Synchronous products of genuine one-cell flows. The global queue is supplied
once and remains fixed; local queues are never inserted into it. -/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- The physical vector field at one cell depends only on that cell's data.
Clock and pending queues are deliberately absent from these hypotheses. -/
theorem field_cell_congr {n m} {θ : Fin n → Parameters} {η : Fin m → Parameters}
    {s : Snapshot n} {v : Snapshot m} {x : Values n} {y : Values m}
    (i : Fin n) (j : Fin m) (hθ : θ i = η j) (hm : s.main i = v.main j)
    (ha : s.aux i = v.aux j) (hr : s.raw i = v.raw j) (hx : x i = y j)
    (t : ℝ) (c : Coord) : field θ s x t i c = field η v y t j c := by
  simp only [field,work,drive,errorAct,markAct,current,hθ,hm,ha,hr,hx]

noncomputable def Values.product (xA xB : Values 1) : Values 2 :=
  Fin.cases (xA 0) (fun _ => xB 0)

noncomputable def Snapshot.product (sA sB : Snapshot 1) (Q : List (Delivery 2)) : Snapshot 2 where
  time := sA.time
  x := sA.x.product sB.x
  main := Fin.cases (sA.main 0) (fun _ => sB.main 0)
  aux := Fin.cases (sA.aux 0) (fun _ => sB.aux 0)
  raw := Fin.cases (sA.raw 0) (fun _ => sB.raw 0)
  pending := Q

@[simp] theorem Values.product_zero (xA xB : Values 1) : xA.product xB 0 = xA 0 := rfl
@[simp] theorem Values.product_one (xA xB : Values 1) : xA.product xB 1 = xB 0 := rfl

theorem product_field_zero (θA θB : Fin 1 → Parameters) (sA sB : Snapshot 1)
    (Q : List (Delivery 2)) (xA xB : Values 1) (t : ℝ) (c : Coord) :
    field (extendParameters θA (θB 0)) (sA.product sB Q) (xA.product xB) t 0 c =
      field θA sA xA t 0 c := by
  apply field_cell_congr <;> rfl

theorem product_field_one (θA θB : Fin 1 → Parameters) (sA sB : Snapshot 1)
    (Q : List (Delivery 2)) (xA xB : Values 1) (t : ℝ) (c : Coord) :
    field (extendParameters θA (θB 0)) (sA.product sB Q) (xA.product xB) t 1 c =
      field θB sB xB t 0 c := by
  apply field_cell_congr <;> rfl

theorem product_mark_zero (θA θB : Fin 1 → Parameters) (sA sB : Snapshot 1)
    (Q : List (Delivery 2)) (xA xB : Values 1) (p : Port) :
    markAct (extendParameters θA (θB 0)) (sA.product sB Q) (xA.product xB) 0 p =
      markAct θA sA xA 0 p := rfl

theorem product_mark_one (θA θB : Fin 1 → Parameters) (sA sB : Snapshot 1)
    (Q : List (Delivery 2)) (xA xB : Values 1) (p : Port) :
    markAct (extendParameters θA (θB 0)) (sA.product sB Q) (xA.product xB) 1 p =
      markAct θB sB xB 0 p := rfl

/-- Pair actual local flows on the same interval. Only the global pending
queue controls the permissible shared endpoint. -/
noncomputable def Flow.product {θA θB : Fin 1 → Parameters} {sA uA sB uB : Snapshot 1}
    (fA : Flow θA sA uA) (fB : Flow θB sB uB)
    (hstart : sA.time = sB.time) (hfinish : uA.time = uB.time)
    (Q : List (Delivery 2)) (hp : ∀ d ∈ Q, uA.time ≤ d.due) :
    Flow (extendParameters θA (θB 0)) (sA.product sB Q) (uA.product uB Q) where
  positive := fA.positive
  path := fun t => (fA.path t).product (fB.path t)
  initial := by
    change (fA.path sA.time).product (fB.path sA.time) = sA.x.product sB.x
    rw [fA.initial,hstart,fB.initial]
  final := by
    change (fA.path uA.time).product (fB.path uA.time) = uA.x.product uB.x
    rw [fA.final,hfinish,fB.final]
  main_fixed := by
    funext i
    fin_cases i
    · exact congrFun fA.main_fixed 0
    · exact congrFun fB.main_fixed 0
  aux_fixed := by
    funext i
    fin_cases i
    · exact congrFun fA.aux_fixed 0
    · exact congrFun fB.aux_fixed 0
  raw_fixed := by
    funext i
    fin_cases i
    · exact congrFun fA.raw_fixed 0
    · exact congrFun fB.raw_fixed 0
  queue_fixed := rfl
  continuous := by
    intro i c
    fin_cases i
    · exact fA.continuous 0 c
    · change ContinuousOn (fun t => fB.path t 0 c) (Icc sA.time uA.time)
      rw [hstart,hfinish]
      exact fB.continuous 0 c
  integrable := by
    intro i c
    fin_cases i
    · exact fA.integrable 0 c
    · change IntervalIntegrable
        (fun t => field (extendParameters θA (θB 0)) (sA.product sB Q)
          ((fA.path t).product (fB.path t)) t 1 c) volume sA.time uA.time
      simp only [product_field_one]
      rw [hstart,hfinish]
      exact fB.integrable 0 c
  mark_integrable := by
    intro i p
    fin_cases i
    · exact fA.mark_integrable 0 p
    · change IntervalIntegrable
        (fun t => markAct (extendParameters θA (θB 0)) (sA.product sB Q)
          ((fA.path t).product (fB.path t)) 1 p) volume sA.time uA.time
      simp only [product_mark_one]
      rw [hstart,hfinish]
      exact fB.mark_integrable 0 p
  integral_eq := by
    intro t ht i c
    change t ∈ Icc sA.time uA.time at ht
    fin_cases i
    · change fA.path t 0 c = sA.x 0 c + ∫ v in sA.time..t,
        field (extendParameters θA (θB 0)) (sA.product sB Q)
          ((fA.path v).product (fB.path v)) v 0 c
      simp only [product_field_zero]
      exact fA.integral_eq t ht 0 c
    · change fB.path t 0 c = sB.x 0 c + ∫ v in sA.time..t,
        field (extendParameters θA (θB 0)) (sA.product sB Q)
          ((fA.path v).product (fB.path v)) v 1 c
      simp only [product_field_one]
      rw [hstart]
      exact fB.integral_eq t (by simpa only [hstart,hfinish] using ht) 0 c
  guards := by
    intro t ht
    change t ∈ Ico sA.time uA.time at ht
    have ha := fA.guards t ht
    have hb := fB.guards t (by simpa only [hstart,hfinish] using ht)
    constructor
    · intro i
      fin_cases i
      · exact ha.1 0
      · exact hb.1 0
    · intro i p
      fin_cases i
      · exact ha.2 0 p
      · exact hb.2 0 p
  raw_support := by
    intro i p origin hr
    fin_cases i
    · exact fA.raw_support 0 p origin hr
    · have h := fB.raw_support 0 p origin hr
      simpa only [Snapshot.product,hstart,hfinish] using h
  pending_urgent := hp

end KernelR.Hybrid
