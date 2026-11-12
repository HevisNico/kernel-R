import Network.WiredNetwork

/-! Networks of report windows in the parameterized semantics. Each cell
has a window. A FIRE in the window is a signal. A signal sends pulses at
fixed dates to later cells. A cell that does not signal sends nothing:
its other FIRE events come before its window. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- An input wire of a cell: the cell whose signal sends the pulse, the
port that receives it and the fixed date at which it arrives. -/
structure Wire (n : ℕ) where
  sender : Fin n
  port : Port
  date : ℝ

/-- The pulse of a wire into cell `j`, sent by cell `i`. -/
def Wire.sent {n : ℕ} (i j : Fin n) (w : Wire n) : Option (Delivery n) :=
  if w.sender = i then some ⟨j, w.port, w.date⟩ else none

/-- The pulse of a wire, seen from the receiving cell. -/
def Wire.pulse {n : ℕ} (w : Wire n) : Delivery 1 := ⟨0, w.port, w.date⟩

/-- A FIRE of cell `i` inside its window `(lo i, hi i]` sends a pulse on
every wire that leaves cell `i`. -/
noncomputable def signalRoute {n : ℕ} (lo hi : Fin n → ℝ) (inputs : Fin n → List (Wire n)) :
    Router n := fun i t =>
  if lo i < t ∧ t ≤ hi i then
    (List.finRange n).flatMap (fun j => (inputs j).filterMap (Wire.sent i j))
  else []

/-- The FIRE dates `l` carry the bit `b` in the window `(lo, hi]`. For a
true bit the last FIRE is in the window and the others are before it.
For a false bit every FIRE is before the window. -/
def Signal (lo hi : ℝ) (l : List ℝ) (b : Bool) : Prop :=
  (b = true ∧ ∃ pre tr, l = pre ++ [tr] ∧ (∀ t ∈ pre, t ≤ lo) ∧ lo < tr ∧ tr ≤ hi) ∨
  (b = false ∧ ∀ t ∈ l, t ≤ lo)

theorem signal_flatMap {α : Type} {lo hi : ℝ} {l : List ℝ} {b : Bool} (h : Signal lo hi l b)
    (g : List α) :
    l.flatMap (fun t => if lo < t ∧ t ≤ hi then g else []) = if b then g else [] := by
  have quiet (pre : List ℝ) (early : ∀ t ∈ pre, t ≤ lo) :
      pre.flatMap (fun t => if lo < t ∧ t ≤ hi then g else []) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro t ht
    simp [not_lt.mpr (early t ht)]
  rcases h with ⟨rfl, pre, tr, rfl, early, after, before⟩ | ⟨rfl, early⟩
  · rw [List.flatMap_append, quiet pre early]
    simp [after, before]
  · rw [quiet l early]
    rfl

/-- The pulses that cell `j` receives when the cells signal the bits
`bit`. -/
def received {n : ℕ} (inputs : Fin n → List (Wire n)) (bit : Fin n → Bool) (j : Fin n) :
    List (Delivery 1) :=
  ((inputs j).filter (fun w => bit w.sender)).map Wire.pulse

theorem mem_signalRoute {n : ℕ} {lo hi : Fin n → ℝ} {inputs : Fin n → List (Wire n)}
    {i : Fin n} {t : ℝ} {d : Delivery n} (h : d ∈ signalRoute lo hi inputs i t) :
    t ≤ hi i ∧ ∃ w ∈ inputs d.cell, w.sender = i ∧ d.due = w.date := by
  unfold signalRoute at h
  split_ifs at h with window
  · obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp h
    obtain ⟨w, hw, sent⟩ := List.mem_filterMap.mp hj
    unfold Wire.sent at sent
    split_ifs at sent with from_
    obtain rfl := Option.some.inj sent
    exact ⟨window.2, w, hw, from_, rfl⟩
  · cases h

/-- What the signals of the cells send to cell `j`. -/
theorem signal_incoming {n : ℕ} {lo hi : Fin n → ℝ} {inputs : Fin n → List (Wire n)}
    (wires : ∀ j, ∀ w ∈ inputs j, w.sender < j) (bit : Fin n → Bool)
    (dates : Fin n → List ℝ) (j : Fin n)
    (below : ∀ i, i < j → Signal (lo i) (hi i) (dates i) (bit i)) :
    incoming (signalRoute lo hi inputs) dates j =
      ((received inputs bit j : List (Delivery 1)) : Multiset (Delivery 1)) := by
  -- The pulses of cell `i` that reach cell `j`.
  have each (i : Fin n) :
      ((dates i).flatMap (signalRoute lo hi inputs i)).filterMap (Delivery.toCell j) =
        ((inputs j).filter (fun w => decide (w.sender = i) && bit i)).map Wire.pulse := by
    by_cases h : i < j
    · have fired : (dates i).flatMap (signalRoute lo hi inputs i) =
          if bit i then (List.finRange n).flatMap (fun k => (inputs k).filterMap (Wire.sent i k))
          else [] :=
        signal_flatMap (below i h) _
      rw [fired]
      cases hb : bit i
      · simp
      · simp only [ite_true, Bool.and_true]
        rw [List.filterMap_flatMap,
          flatMap_single (List.nodup_finRange n) (List.mem_finRange j) _ (fun k _ ne => by
            apply List.filterMap_eq_nil_iff.mpr
            intro d hd
            obtain ⟨w, _, sent⟩ := List.mem_filterMap.mp hd
            unfold Wire.sent at sent
            split_ifs at sent
            obtain rfl := Option.some.inj sent
            simp [Delivery.toCell, ne]),
          List.filterMap_filterMap]
        have point : (fun x : Wire n => (Wire.sent i j x).bind (Delivery.toCell j)) =
            fun x => if x.sender = i then some x.pulse else none := by
          funext x
          by_cases e : x.sender = i <;> simp [Wire.sent, Delivery.toCell, Wire.pulse, e]
        rw [point]
        induction inputs j with
        | nil => rfl
        | cons w rest ih =>
          by_cases from_ : w.sender = i <;> simp [from_, ih]
    · have none : ((dates i).flatMap (signalRoute lo hi inputs i)).filterMap
          (Delivery.toCell j) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro d hd
        obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hd
        obtain ⟨_, w, hw, from_, _⟩ := mem_signalRoute ht
        have lt : i < d.cell := from_ ▸ wires d.cell w hw
        have ne : d.cell ≠ j := fun e => h (e ▸ lt)
        simp [Delivery.toCell, ne]
      have empty : (inputs j).filter (fun w => decide (w.sender = i) && bit i) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro w hw
        have ne : w.sender ≠ i := fun e => h (e ▸ wires j w hw)
        simp [ne]
      rw [none, empty]
      rfl
  unfold incoming received
  simp only [each]
  induction inputs j with
  | nil => simp
  | cons w rest ih =>
    have head (i : Fin n) :
        (((w :: rest).filter (fun v => decide (v.sender = i) && bit i)).map Wire.pulse :
          List (Delivery 1)) =
        (if w.sender = i then (if bit w.sender then [w.pulse] else []) else []) ++
          (rest.filter (fun v => decide (v.sender = i) && bit i)).map Wire.pulse := by
      by_cases from_ : w.sender = i
      · subst from_
        cases hb : bit w.sender <;> simp
      · simp [from_]
    simp only [head, ← Multiset.coe_add, Finset.sum_add_distrib, ih]
    have one : ∑ i : Fin n, (((if w.sender = i then (if bit w.sender then [w.pulse] else [])
        else [] : List (Delivery 1)) : Multiset (Delivery 1))) =
        ((if bit w.sender then [w.pulse] else [] : List (Delivery 1)) :
          Multiset (Delivery 1)) := by
      have push (i : Fin n) : (((if w.sender = i then (if bit w.sender then [w.pulse] else [])
          else [] : List (Delivery 1)) : Multiset (Delivery 1))) =
          if w.sender = i then ((if bit w.sender then [w.pulse] else [] : List (Delivery 1)) :
            Multiset (Delivery 1)) else 0 := by
        split_ifs <;> rfl
      simp only [push, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [one]
    cases hb : bit w.sender <;> simp [hb]

/-- A network of report windows, with the final states and the pulses
sent. Cell `j` has a rested start, a window `(lo j, hi j]`, input wires
from earlier cells and a bit `bit j`. Every wire delivers after the
window of its sender. The hypothesis is local: when cell `j` receives
the pulses of the wires whose senders have a true bit, it has a run to
rest whose FIRE dates carry `bit j` and satisfy `Q j`, and whose final
state satisfies `Final j`. Then the network has a complete run in which
every cell carries its bit and ends in such a state. The pulses sent to
a cell by the FIRE events of that run are those of the wires whose
senders have a true bit. In every complete run the FIRE dates and the
final values of every cell are those of that run. -/
theorem signal_network_states {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters} {ε T rest : ℝ}
    {level : Fin n → ℝ} (lo hi : Fin n → ℝ) (inputs : Fin n → List (Wire n))
    (wires : ∀ j, ∀ w ∈ inputs j, w.sender < j ∧ hi w.sender < w.date)
    (s : Fin n → Snapshot 1) (start : ∀ i, (s i).time = T)
    (box : ∀ i, @PhysicalBox 1 (θ i) ε) (config : ∀ i, CellConfig (θ i) (level i))
    (fire : ∀ i, 19 / 20 ≤ level i ∧ level i ≤ 21 / 20) (state : ∀ i, RestState (θ i) (s i))
    (bit : Fin n → Bool) (Q : Fin n → List ℝ → Prop) (Final : Fin n → Snapshot 1 → Prop)
    (cellRun : ∀ j, ∃ (P : List (Delivery 1)) (u : Snapshot 1) (l : List ℝ) (count : ℕ),
      (P : Multiset (Delivery 1)) = ((s j).pending : Multiset (Delivery 1)) +
        ((received inputs bit j : List (Delivery 1)) : Multiset (Delivery 1)) ∧
      Reach (θ j) (requeued (s j) P) u l count ∧ RestState (θ j) u ∧ u.time = rest ∧
      u.pending = [] ∧ Signal (lo j) (hi j) l (bit j) ∧ Q j l ∧ Final j u) :
    ∃ (dates : Fin n → List ℝ) (u : Fin n → Snapshot 1),
      (∀ j, Signal (lo j) (hi j) (dates j) (bit j) ∧ Q j (dates j)) ∧ (∀ j, Final j (u j)) ∧
      (∀ j, incoming (signalRoute lo hi inputs) dates j =
        ((received inputs bit j : List (Delivery 1)) : Multiset (Delivery 1))) ∧
      (∃ ref : ParameterExecution (familyParameters θ) (signalRoute lo hi inputs)
        (Snapshot.family T s) (Snapshot.family rest u), ParameterCompleteThrough ref rest) ∧
      ∀ {w : Snapshot n} (ex : ParameterExecution (familyParameters θ)
        (signalRoute lo hi inputs) (Snapshot.family T s) w), ParameterCompleteThrough ex rest →
        (∀ i, ex.emissionTimes i = dates i) ∧ ∀ i c, w.x i c = (u i).x 0 c := by
  have causal : ∀ i t d, d ∈ signalRoute lo hi inputs i t → t < d.due := by
    intro i t d hd
    obtain ⟨before, w, hw, from_, due⟩ := mem_signalRoute hd
    have late := (wires d.cell w hw).2
    rw [from_] at late
    rw [due]
    linarith
  have forward : ∀ i t d, d ∈ signalRoute lo hi inputs i t → i < d.cell := by
    intro i t d hd
    obtain ⟨_, w, hw, from_, _⟩ := mem_signalRoute hd
    exact from_ ▸ (wires d.cell w hw).1
  obtain ⟨dates, u, spec, fin, ref, all⟩ :=
    acyclic_network_states pos (θ := θ) (ε := ε) (T := T) (rest := rest) (level := level)
      (signalRoute lo hi inputs) causal forward s start box config fire state
      (fun j dates => Signal (lo j) (hi j) (dates j) (bit j) ∧ Q j (dates j)) Final
      (fun j dates dates' agree spec => by rw [← agree j le_rfl]; exact spec)
      (fun dates j below => by
        obtain ⟨P, u, l, count, hP, reach, rested, date, pend, signal, extra, fin⟩ := cellRun j
        refine ⟨P, u, l, count, ?_, reach, rested, date, pend, ?_, fin⟩
        · rw [signal_incoming (fun k w hw => (wires k w hw).1) bit dates j
            (fun i hi => (below i hi).1)]
          exact hP
        · rw [Function.update_self]
          exact ⟨signal, extra⟩)
  exact ⟨dates, u, spec, fin,
    fun j => signal_incoming (fun k w hw => (wires k w hw).1) bit dates j (fun i _ => (spec i).1),
    ref, all⟩

/-- A network of report windows. Cell `j` has a rested start, a window
`(lo j, hi j]`, input wires from earlier cells and a bit `bit j`. Every
wire delivers after the window of its sender. The hypothesis is local:
when cell `j` receives the pulses of the wires whose senders have a true
bit, it has a run to rest whose FIRE dates carry `bit j` and satisfy
`Q j`. Then the network has a complete run, every cell carries its bit,
and the FIRE dates are the same in every complete run. -/
theorem signal_network {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters} {ε T rest : ℝ}
    {level : Fin n → ℝ} (lo hi : Fin n → ℝ) (inputs : Fin n → List (Wire n))
    (wires : ∀ j, ∀ w ∈ inputs j, w.sender < j ∧ hi w.sender < w.date)
    (s : Fin n → Snapshot 1) (start : ∀ i, (s i).time = T)
    (box : ∀ i, @PhysicalBox 1 (θ i) ε) (config : ∀ i, CellConfig (θ i) (level i))
    (fire : ∀ i, 19 / 20 ≤ level i ∧ level i ≤ 21 / 20) (state : ∀ i, RestState (θ i) (s i))
    (bit : Fin n → Bool) (Q : Fin n → List ℝ → Prop)
    (cellRun : ∀ j, ∃ (P : List (Delivery 1)) (u : Snapshot 1) (l : List ℝ) (count : ℕ),
      (P : Multiset (Delivery 1)) = ((s j).pending : Multiset (Delivery 1)) +
        ((received inputs bit j : List (Delivery 1)) : Multiset (Delivery 1)) ∧
      Reach (θ j) (requeued (s j) P) u l count ∧ RestState (θ j) u ∧ u.time = rest ∧
      u.pending = [] ∧ Signal (lo j) (hi j) l (bit j) ∧ Q j l) :
    ∃ dates : Fin n → List ℝ,
      (∀ j, Signal (lo j) (hi j) (dates j) (bit j) ∧ Q j (dates j)) ∧
      (∃ (u : Snapshot n) (ref : ParameterExecution (familyParameters θ)
        (signalRoute lo hi inputs) (Snapshot.family T s) u), ParameterCompleteThrough ref rest) ∧
      ∀ {u : Snapshot n} (ex : ParameterExecution (familyParameters θ)
        (signalRoute lo hi inputs) (Snapshot.family T s) u), ParameterCompleteThrough ex rest →
        ∀ i, ex.emissionTimes i = dates i := by
  obtain ⟨dates, u, spec, _, _, ⟨ref, complete⟩, all⟩ :=
    signal_network_states pos (θ := θ) (ε := ε) (level := level) lo hi inputs wires s start box
      config fire state bit Q (fun _ _ => True) (fun j => by
        obtain ⟨P, u, l, count, h⟩ := cellRun j
        exact ⟨P, u, l, count, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
          h.2.2.2.2.2.2, trivial⟩)
  exact ⟨dates, spec, ⟨_, ref, complete⟩, fun ex done => (all ex done).1⟩

end RecursiveLearning.Native
