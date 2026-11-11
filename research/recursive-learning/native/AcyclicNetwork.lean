import FreeRead

/-! Composition of cells along forward wires. Every wire goes from a
cell to a cell of higher index. Each cell is described alone: for the
pulses it receives, it has a run that ends at rest. The network then has
a complete run, and its FIRE dates are the same in every complete run. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- A delivery of the network, seen from cell `j`. -/
def Delivery.toCell {n : ℕ} (j : Fin n) (d : Delivery n) : Option (Delivery 1) :=
  if d.cell = j then some ⟨0, d.port, d.due⟩ else none

/-- The pulses that the FIRE dates `dates` send to cell `j`. -/
def incoming {n : ℕ} (route : Router n) (dates : Fin n → List ℝ) (j : Fin n) :
    Multiset (Delivery 1) :=
  ∑ i, ((((dates i).flatMap (route i)).filterMap (Delivery.toCell j) : List (Delivery 1)) :
    Multiset (Delivery 1))

/-- With forward wires, the pulses received by cell `j` depend only on
the FIRE dates of the cells before it. -/
theorem incoming_congr {n : ℕ} {route : Router n} (forward : ∀ i t d, d ∈ route i t → i < d.cell)
    {dates dates' : Fin n → List ℝ} {j : Fin n} (agree : ∀ i, i < j → dates i = dates' i) :
    incoming route dates j = incoming route dates' j := by
  unfold incoming
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i < j
  · rw [agree i h]
  · have none (l : List ℝ) : (l.flatMap (route i)).filterMap (Delivery.toCell j) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro d hd
      obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hd
      have lt := forward i t d ht
      have ne : d.cell ≠ j := fun e => h (e ▸ lt)
      simp [Delivery.toCell, ne]
    rw [none, none]

theorem familyQueue_coe {n : ℕ} (s : Fin n → Snapshot 1) :
    (familyQueue s : Multiset (Delivery n)) =
      ∑ j, Multiset.map (Delivery.inCell j) ((s j).pending : Multiset (Delivery 1)) := by
  have general (l : List (Fin n)) :
      ((l.flatMap (fun i => (s i).pending.map (Delivery.inCell i)) : List (Delivery n)) :
        Multiset (Delivery n)) =
      (l.map (fun j => Multiset.map (Delivery.inCell j)
        ((s j).pending : Multiset (Delivery 1)))).sum := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons,
        Multiset.map_coe]
  rw [Fin.sum_univ_def]
  exact general (List.finRange n)

/-- Every delivery belongs to exactly one cell. -/
theorem split_cells {n : ℕ} (L : List (Delivery n)) :
    ∑ j, Multiset.map (Delivery.inCell j)
      ((L.filterMap (Delivery.toCell j) : List (Delivery 1)) : Multiset (Delivery 1)) =
      (L : Multiset (Delivery n)) := by
  induction L with
  | nil => simp
  | cons d L ih =>
    have head (j : Fin n) : Multiset.map (Delivery.inCell j)
        (((d :: L).filterMap (Delivery.toCell j) : List (Delivery 1)) : Multiset (Delivery 1)) =
        (if d.cell = j then ({d} : Multiset (Delivery n)) else 0) +
          Multiset.map (Delivery.inCell j)
            ((L.filterMap (Delivery.toCell j) : List (Delivery 1)) : Multiset (Delivery 1)) := by
      by_cases h : d.cell = j
      · subst h
        have same : Delivery.inCell d.cell (⟨0, d.port, d.due⟩ : Delivery 1) = d := by
          cases d; rfl
        simp [Delivery.toCell, same]
      · simp [Delivery.toCell, h]
    simp only [head, Finset.sum_add_distrib, ih, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl

/-- The pulses received by all the cells are the pulses sent. -/
theorem incoming_total {n : ℕ} (route : Router n) (dates : Fin n → List ℝ) :
    ∑ j, Multiset.map (Delivery.inCell j) (incoming route dates j) = promised route dates := by
  have push (j : Fin n) (g : Fin n → Multiset (Delivery 1)) :
      Multiset.map (Delivery.inCell j) (∑ i, g i) = ∑ i, Multiset.map (Delivery.inCell j) (g i) :=
    map_sum (Multiset.mapAddMonoidHom (Delivery.inCell j)) g Finset.univ
  unfold incoming promised
  simp only [push]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => split_cells _)

/-- Composition along forward wires, with the final states. Each cell
`j` has a rested start, its own parameters in the fabrication box, a
description `Spec j` of its FIRE dates, which can mention the FIRE dates
of the cells before it, and a description `Final j` of its final state.
If every cell, fed by cells that follow their descriptions, has a run to
rest that follows its own, then the network has a complete run in which
every cell follows its descriptions. In every complete run the FIRE
dates and the final values of every cell are those of that run. -/
theorem acyclic_network_states {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters} {ε T rest : ℝ}
    {level : Fin n → ℝ} (route : Router n) (causal : ∀ i t d, d ∈ route i t → t < d.due)
    (forward : ∀ i t d, d ∈ route i t → i < d.cell)
    (s : Fin n → Snapshot 1) (start : ∀ i, (s i).time = T)
    (box : ∀ i, @PhysicalBox 1 (θ i) ε) (config : ∀ i, CellConfig (θ i) (level i))
    (fire : ∀ i, 19 / 20 ≤ level i ∧ level i ≤ 21 / 20) (state : ∀ i, RestState (θ i) (s i))
    (Spec : Fin n → (Fin n → List ℝ) → Prop) (Final : Fin n → Snapshot 1 → Prop)
    (past : ∀ (j : Fin n) (dates dates' : Fin n → List ℝ),
      (∀ i, i ≤ j → dates i = dates' i) → Spec j dates → Spec j dates')
    (cellRun : ∀ (dates : Fin n → List ℝ) (j : Fin n), (∀ i, i < j → Spec i dates) →
      ∃ (P : List (Delivery 1)) (u : Snapshot 1) (out : List ℝ) (count : ℕ),
        (P : Multiset (Delivery 1)) =
          ((s j).pending : Multiset (Delivery 1)) + incoming route dates j ∧
        Reach (θ j) (requeued (s j) P) u out count ∧ RestState (θ j) u ∧ u.time = rest ∧
        u.pending = [] ∧ Spec j (Function.update dates j out) ∧ Final j u) :
    ∃ (dates : Fin n → List ℝ) (u : Fin n → Snapshot 1),
      (∀ j, Spec j dates) ∧ (∀ j, Final j (u j)) ∧
      (∃ ref : ParameterExecution (familyParameters θ) route
        (Snapshot.family T s) (Snapshot.family rest u), ParameterCompleteThrough ref rest) ∧
      ∀ {w : Snapshot n} (ex : ParameterExecution (familyParameters θ) route
        (Snapshot.family T s) w), ParameterCompleteThrough ex rest →
        (∀ i, ex.emissionTimes i = dates i) ∧ ∀ i c, w.x i c = (u i).x 0 c := by
  -- The FIRE dates, cell after cell.
  have build : ∀ m, m ≤ n → ∃ dates : Fin n → List ℝ, ∀ j : Fin n, j.val < m →
      ∃ (P : List (Delivery 1)) (u : Snapshot 1) (count : ℕ),
        (P : Multiset (Delivery 1)) =
          ((s j).pending : Multiset (Delivery 1)) + incoming route dates j ∧
        Reach (θ j) (requeued (s j) P) u (dates j) count ∧ RestState (θ j) u ∧ u.time = rest ∧
        u.pending = [] ∧ Spec j dates ∧ Final j u := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨fun _ => [], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨dates, good⟩ := ih (Nat.le_of_succ_le hm)
      let j : Fin n := ⟨m, hm⟩
      obtain ⟨P, u, out, count, hP, reach, rested, date, pend, spec, fin⟩ :=
        cellRun dates j (fun i hi => by
          obtain ⟨_, _, _, _, _, _, _, _, sp, _⟩ := good i hi
          exact sp)
      have same (i : Fin n) (hi : i ≤ j) :
          incoming route (Function.update dates j out) i = incoming route dates i :=
        incoming_congr forward (fun k hk => Function.update_of_ne (ne_of_lt (hk.trans_le hi)) _ _)
      refine ⟨Function.update dates j out, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with lt | eq
      · have ne : i ≠ j := ne_of_lt lt
        obtain ⟨P', u', count', hP', reach', rested', date', pend', spec', fin'⟩ := good i lt
        rw [same i (le_of_lt lt), Function.update_of_ne ne]
        exact ⟨P', u', count', hP', reach', rested', date', pend',
          past i dates _ (fun k hk =>
            (Function.update_of_ne (ne_of_lt (lt_of_le_of_lt hk lt)) _ _).symm) spec', fin'⟩
      · have ij : i = j := Fin.ext eq
        subst ij
        rw [same j le_rfl, Function.update_self]
        exact ⟨P, u, count, hP, reach, rested, date, pend, spec, fin⟩
  obtain ⟨dates, good⟩ := build n le_rfl
  choose P u count hP reach rested date pend spec fin using fun j => good j j.isLt
  let sLoc : Fin n → Snapshot 1 := fun j => requeued (s j) (P j)
  have balance : (familyQueue sLoc : Multiset (Delivery n)) =
      (familyQueue s : Multiset (Delivery n)) + promised route dates := by
    rw [familyQueue_coe, familyQueue_coe, ← incoming_total, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    show Multiset.map (Delivery.inCell j) ((P j : List (Delivery 1)) : Multiset (Delivery 1)) = _
    rw [hP j, Multiset.map_add]
  obtain ⟨P', E, times, final⟩ := routed_execution pos (θ := θ) route causal _ T rest sLoc u
    dates count (familyQueue s) rfl reach start date balance
  have hP' : P' = [] := by
    rw [familyQueue_empty pend] at final
    exact (Multiset.coe_eq_coe.mp final).eq_nil
  have startEq : Snapshot.familyWith T sLoc (familyQueue s) = Snapshot.family T s :=
    Snapshot.family_congr rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) rfl
  have endEq : Snapshot.familyWith rest u P' = Snapshot.family rest u := by
    rw [hP']
    exact Snapshot.family_congr rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (familyQueue_empty pend).symm
  obtain ⟨E', keep⟩ := execution_cast startEq endEq E
  have times' : ∀ i, E'.emissionTimes i = dates i := fun i => (keep i).trans (times i)
  have complete : ParameterCompleteThrough E' rest :=
    family_complete config (fun i => (fire i).1) rested pend E'
  have boxAll : PhysicalBox (familyParameters θ) ε :=
    ⟨(box ⟨0, pos⟩).1, fun i p => (box i).2 0 p⟩
  have b (i : Fin n) := cell_threshold_bounds (config i) (fire i)
  have bounds : ParameterThresholdBounds (familyParameters θ) :=
    ⟨fun i => (b i).fire 0, fun i => (b i).fastEnd 0, fun i => (b i).fastBelowFire 0,
      fun i => (b i).reopen 0, fun i p => (b i).mark 0 p, fun i p => (b i).silent 0 p,
      fun i p => (b i).error 0 p, fun i p => (b i).auxReady 0 p⟩
  have inv (i : Fin n) := (state i).physical
  have birth : ParameterPhysicalInvariant (familyParameters θ) (Snapshot.family T s) :=
    ⟨fun i => (inv i).charge 0, fun i p => (inv i).sensor 0 p, fun i p => (inv i).gain 0 p,
      fun i => (inv i).recovery 0, fun i => (inv i).reserve 0⟩
  refine ⟨dates, u, spec, fin, ⟨E', complete⟩, ?_⟩
  intro w ex done
  refine ⟨fun i => ?_, fun i c => ?_⟩
  · rw [ex.emissionTimes_unique E' boxAll bounds birth done complete i, times' i]
  · have same := (ParameterExecution.observational_unique boxAll bounds E' ex birth complete
      done).1.values
    exact (congrFun (congrFun same i) c).symm

/-- Composition along forward wires. Each cell `j` has a rested start,
its own parameters in the fabrication box and a description `Spec j` of
its FIRE dates, which can mention the FIRE dates of the cells before it.
If every cell, fed by cells that follow their descriptions, has a run to
rest that follows its own, then the network has a complete run, every
cell follows its description, and the FIRE dates are the same in every
complete run. -/
theorem acyclic_network {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters} {ε T rest : ℝ}
    {level : Fin n → ℝ} (route : Router n) (causal : ∀ i t d, d ∈ route i t → t < d.due)
    (forward : ∀ i t d, d ∈ route i t → i < d.cell)
    (s : Fin n → Snapshot 1) (start : ∀ i, (s i).time = T)
    (box : ∀ i, @PhysicalBox 1 (θ i) ε) (config : ∀ i, CellConfig (θ i) (level i))
    (fire : ∀ i, 19 / 20 ≤ level i ∧ level i ≤ 21 / 20) (state : ∀ i, RestState (θ i) (s i))
    (Spec : Fin n → (Fin n → List ℝ) → Prop)
    (past : ∀ (j : Fin n) (dates dates' : Fin n → List ℝ),
      (∀ i, i ≤ j → dates i = dates' i) → Spec j dates → Spec j dates')
    (cellRun : ∀ (dates : Fin n → List ℝ) (j : Fin n), (∀ i, i < j → Spec i dates) →
      ∃ (P : List (Delivery 1)) (u : Snapshot 1) (out : List ℝ) (count : ℕ),
        (P : Multiset (Delivery 1)) =
          ((s j).pending : Multiset (Delivery 1)) + incoming route dates j ∧
        Reach (θ j) (requeued (s j) P) u out count ∧ RestState (θ j) u ∧ u.time = rest ∧
        u.pending = [] ∧ Spec j (Function.update dates j out)) :
    ∃ dates : Fin n → List ℝ,
      (∀ j, Spec j dates) ∧
      (∃ (u : Snapshot n) (ref : ParameterExecution (familyParameters θ) route
        (Snapshot.family T s) u), ParameterCompleteThrough ref rest) ∧
      ∀ {u : Snapshot n} (ex : ParameterExecution (familyParameters θ) route
        (Snapshot.family T s) u), ParameterCompleteThrough ex rest →
        ∀ i, ex.emissionTimes i = dates i := by
  obtain ⟨dates, u, spec, _, ⟨ref, complete⟩, all⟩ :=
    acyclic_network_states pos (θ := θ) (ε := ε) (level := level) route causal forward s start
      box config fire state Spec (fun _ _ => True) past (fun dates j below => by
        obtain ⟨P, u, out, count, h⟩ := cellRun dates j below
        exact ⟨P, u, out, count, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
          trivial⟩)
  exact ⟨dates, spec, ⟨_, ref, complete⟩, fun ex done => (all ex done).1⟩

end RecursiveLearning.Native
