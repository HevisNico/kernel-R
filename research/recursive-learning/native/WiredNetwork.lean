import AcyclicNetwork

/-! Networks of trained cells of any depth. Each of the two read pulses
of a cell comes from a source at a fixed date or from the read FIRE of an
earlier cell, through a wire. The two read pulses of a cell can arrive in
either order. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- Where a read pulse comes from: a source at a fixed date, or the read
FIRE of a cell, through a wire with a delay. -/
inductive ReadInput (n : ℕ)
  | source (date : ℝ)
  | wire (cell : Fin n) (delay : ℝ)

/-- The date at which the read pulse arrives, for read FIRE dates `tf`. -/
def ReadInput.arrival {n : ℕ} (tf : Fin n → ℝ) : ReadInput n → ℝ
  | .source date => date
  | .wire k w => tf k + w

/-- A wire comes from an earlier cell and has a positive delay. -/
def ReadInput.Before {n : ℕ} (j : Fin n) : ReadInput n → Prop
  | .source _ => True
  | .wire k w => k < j ∧ 0 < w

/-- The pulse put in the queue of the cell at the start. -/
def ReadInput.initial {n : ℕ} (p : Port) : ReadInput n → List (Delivery 1)
  | .source date => [⟨0, p, date⟩]
  | .wire _ _ => []

/-- What a FIRE of cell `i` at date `t` sends on this input of cell `j`. -/
def ReadInput.sent {n : ℕ} (i : Fin n) (t : ℝ) (j : Fin n) (p : Port) :
    ReadInput n → List (Delivery n)
  | .source _ => []
  | .wire k w => if k = i then [⟨j, p, t + w⟩] else []

/-- The same pulse, seen from the receiving cell. -/
def ReadInput.received {n : ℕ} (i : Fin n) (t : ℝ) (p : Port) : ReadInput n → List (Delivery 1)
  | .source _ => []
  | .wire k w => if k = i then [⟨0, p, t + w⟩] else []

theorem ReadInput.arrival_congr {n : ℕ} {j : Fin n} {tf tf' : Fin n → ℝ} {input : ReadInput n}
    (before : input.Before j) (agree : ∀ i, i < j → tf i = tf' i) :
    input.arrival tf = input.arrival tf' := by
  cases input with
  | source date => rfl
  | wire k w => exact congrArg (· + w) (agree k before.1)

theorem ReadInput.mem_sent {n : ℕ} {i j : Fin n} {t : ℝ} {p : Port} {input : ReadInput n}
    {d : Delivery n} (h : d ∈ input.sent i t j p) :
    ∃ w, input = .wire i w ∧ d = ⟨j, p, t + w⟩ := by
  cases input with
  | source date => cases h
  | wire k w =>
    by_cases e : k = i
    · subst e
      simp only [ReadInput.sent, ite_true] at h
      exact ⟨w, rfl, List.mem_singleton.mp h⟩
    · simp [ReadInput.sent, e] at h

theorem ReadInput.sent_same {n : ℕ} (i j : Fin n) (t : ℝ) (p : Port) (input : ReadInput n) :
    (input.sent i t j p).filterMap (Delivery.toCell j) = input.received i t p := by
  cases input with
  | source date => rfl
  | wire k w =>
    by_cases e : k = i <;> simp [ReadInput.sent, ReadInput.received, Delivery.toCell, e]

theorem ReadInput.sent_other {n : ℕ} (i : Fin n) {j j' : Fin n} (t : ℝ) (p : Port)
    (input : ReadInput n) (ne : j' ≠ j) :
    (input.sent i t j' p).filterMap (Delivery.toCell j) = [] := by
  cases input with
  | source date => rfl
  | wire k w =>
    by_cases e : k = i <;> simp [ReadInput.sent, Delivery.toCell, e, ne]

/-- A source pulse is in the queue at the start; a wired pulse is sent
by exactly one cell. Either way exactly one pulse arrives. -/
theorem ReadInput.one_pulse {n : ℕ} (tf : Fin n → ℝ) (p : Port) (input : ReadInput n) :
    ((input.initial p : List (Delivery 1)) : Multiset (Delivery 1)) +
      ∑ i, ((input.received i (tf i) p : List (Delivery 1)) : Multiset (Delivery 1)) =
      {(⟨0, p, input.arrival tf⟩ : Delivery 1)} := by
  cases input with
  | source date => simp [ReadInput.initial, ReadInput.received, ReadInput.arrival]
  | wire k w =>
    have each (i : Fin n) : (((ReadInput.wire k w).received i (tf i) p : List (Delivery 1)) :
        Multiset (Delivery 1)) = if k = i then {(⟨0, p, tf i + w⟩ : Delivery 1)} else 0 := by
      by_cases e : k = i <;> simp [ReadInput.received, e]
    simp only [each, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [ReadInput.initial, ReadInput.arrival]

/-- The wires of the network. A FIRE of cell `i` after `gate i` travels
on every wire that leaves cell `i`. The gates keep the FIRE events of
training off the wires. -/
noncomputable def wiredRoute {n : ℕ} (gate : Fin n → ℝ) (p₁ p₂ : Fin n → Port)
    (in₁ in₂ : Fin n → ReadInput n) : Router n := fun i t =>
  if gate i < t then
    (List.finRange n).flatMap (fun j => (in₁ j).sent i t j (p₁ j) ++ (in₂ j).sent i t j (p₂ j))
  else []

theorem mem_wiredRoute {n : ℕ} {gate : Fin n → ℝ} {p₁ p₂ : Fin n → Port}
    {in₁ in₂ : Fin n → ReadInput n} {i : Fin n} {t : ℝ} {d : Delivery n}
    (h : d ∈ wiredRoute gate p₁ p₂ in₁ in₂ i t) :
    ∃ j w, d.cell = j ∧ d.due = t + w ∧ (in₁ j = .wire i w ∨ in₂ j = .wire i w) := by
  unfold wiredRoute at h
  split_ifs at h
  · obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp h
    rcases List.mem_append.mp hj with h₁ | h₂
    · obtain ⟨w, e, rfl⟩ := ReadInput.mem_sent h₁
      exact ⟨j, w, rfl, rfl, Or.inl e⟩
    · obtain ⟨w, e, rfl⟩ := ReadInput.mem_sent h₂
      exact ⟨j, w, rfl, rfl, Or.inr e⟩
  · cases h

theorem flatMap_single {ι β : Type} {l : List ι} (nodup : l.Nodup) {j : ι} (mem : j ∈ l)
    (G : ι → List β) (h : ∀ k ∈ l, k ≠ j → G k = []) : l.flatMap G = G j := by
  induction l with
  | nil => cases mem
  | cons a l ih =>
    rw [List.flatMap_cons]
    obtain ⟨notin, nodup'⟩ := List.nodup_cons.mp nodup
    by_cases e : a = j
    · subst e
      have rest : l.flatMap G = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro k hk
        exact h k (List.mem_cons_of_mem _ hk) (fun e => notin (e ▸ hk))
      rw [rest, List.append_nil]
    · rw [h a List.mem_cons_self e, List.nil_append]
      exact ih nodup' ((List.mem_cons.mp mem).resolve_left (fun e' => e e'.symm))
        (fun k hk => h k (List.mem_cons_of_mem _ hk))

theorem gated_flatMap_list {α : Type} (training : List ℝ) (tf gate : ℝ) (g : ℝ → List α)
    (early : ∀ t ∈ training, t ≤ gate) (late : gate < tf) :
    (training ++ [tf]).flatMap (fun t => if gate < t then g t else []) = g tf := by
  rw [List.flatMap_append]
  have quiet : training.flatMap (fun t => if gate < t then g t else []) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro t ht
    simp [not_lt.mpr (early t ht)]
  rw [quiet]
  simp [late]

/-- The pulses received by cell `j` when every earlier cell fires its
training before its gate and its read after it: the pulses of the start
queue and the pulses of the wires are the two read pulses of the cell. -/
theorem wired_incoming {n : ℕ} {gate : Fin n → ℝ} {p₁ p₂ : Fin n → Port}
    {in₁ in₂ : Fin n → ReadInput n} (order₁ : ∀ j, (in₁ j).Before j)
    (order₂ : ∀ j, (in₂ j).Before j) (dates : Fin n → List ℝ) (tf : Fin n → ℝ) (j : Fin n)
    (shape : ∀ i, i < j → ∃ training, dates i = training ++ [tf i] ∧
      (∀ t ∈ training, t ≤ gate i) ∧ gate i < tf i) :
    (((in₁ j).initial (p₁ j) ++ (in₂ j).initial (p₂ j) : List (Delivery 1)) :
        Multiset (Delivery 1)) + incoming (wiredRoute gate p₁ p₂ in₁ in₂) dates j =
      {(⟨0, p₁ j, (in₁ j).arrival tf⟩ : Delivery 1), (⟨0, p₂ j, (in₂ j).arrival tf⟩ : Delivery 1)} := by
  have each (i : Fin n) :
      ((dates i).flatMap (wiredRoute gate p₁ p₂ in₁ in₂ i)).filterMap (Delivery.toCell j) =
        (in₁ j).received i (tf i) (p₁ j) ++ (in₂ j).received i (tf i) (p₂ j) := by
    by_cases h : i < j
    · obtain ⟨training, form, early, late⟩ := shape i h
      rw [form]
      have fired : (training ++ [tf i]).flatMap (wiredRoute gate p₁ p₂ in₁ in₂ i) =
          (List.finRange n).flatMap (fun k =>
            (in₁ k).sent i (tf i) k (p₁ k) ++ (in₂ k).sent i (tf i) k (p₂ k)) :=
        gated_flatMap_list training (tf i) (gate i) _ early late
      rw [fired, List.filterMap_flatMap,
        flatMap_single (List.nodup_finRange n) (List.mem_finRange j) _ (fun k _ ne => by
          rw [List.filterMap_append, ReadInput.sent_other i _ _ _ ne,
            ReadInput.sent_other i _ _ _ ne, List.append_nil]),
        List.filterMap_append, ReadInput.sent_same, ReadInput.sent_same]
    · have none : ((dates i).flatMap (wiredRoute gate p₁ p₂ in₁ in₂ i)).filterMap
          (Delivery.toCell j) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro d hd
        obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hd
        obtain ⟨k, w, cell, _, from_⟩ := mem_wiredRoute ht
        have lt : i < k := by
          rcases from_ with e | e
          · have b := order₁ k; rw [e] at b; exact b.1
          · have b := order₂ k; rw [e] at b; exact b.1
        have ne : d.cell ≠ j := fun e => h (e ▸ cell ▸ lt)
        simp [Delivery.toCell, ne]
      have quiet (input : ReadInput n) (before : input.Before j) (p : Port) :
          input.received i (tf i) p = [] := by
        cases input with
        | source date => rfl
        | wire k w =>
          have ne : k ≠ i := fun e => h (e ▸ before.1)
          simp [ReadInput.received, ne]
      rw [none, quiet _ (order₁ j), quiet _ (order₂ j), List.append_nil]
  unfold incoming
  simp only [each, ← Multiset.coe_add, Finset.sum_add_distrib]
  have one₁ := ReadInput.one_pulse tf (p₁ j) (in₁ j)
  have one₂ := ReadInput.one_pulse tf (p₂ j) (in₂ j)
  rw [show ({(⟨0, p₁ j, (in₁ j).arrival tf⟩ : Delivery 1),
      (⟨0, p₂ j, (in₂ j).arrival tf⟩ : Delivery 1)} : Multiset (Delivery 1)) =
      {(⟨0, p₁ j, (in₁ j).arrival tf⟩ : Delivery 1)} +
        {(⟨0, p₂ j, (in₂ j).arrival tf⟩ : Delivery 1)} from rfl, ← one₁, ← one₂]
  abel

/-- The last FIRE date of a cell. -/
def lastDate (l : List ℝ) : ℝ := l.getLastD 0

theorem lastDate_concat (l : List ℝ) (x : ℝ) : lastDate (l ++ [x]) = x := by
  simp [lastDate]

/-- The read FIRE of cell `j` lies in its window: later than 0.239 units
after its first read pulse, no later than 0.256 units after its second. -/
def ReadWindow {n : ℕ} (in₁ in₂ : Fin n → ReadInput n) (tf : Fin n → ℝ) (j : Fin n) : Prop :=
  min ((in₁ j).arrival tf) ((in₂ j).arrival tf) + 239 / 1000 < tf j ∧
    tf j ≤ max ((in₁ j).arrival tf) ((in₂ j).arrival tf) + 32 / 125

/-- The start of cell `j` in the network: its training queue, followed
by its read pulses that come from sources. -/
def wiredStart {n : ℕ} (b : Fin n → Snapshot 1) (p₁ p₂ : Fin n → Port)
    (in₁ in₂ : Fin n → ReadInput n) (j : Fin n) : Snapshot 1 :=
  requeued (b j) ((b j).pending ++ ((in₁ j).initial (p₁ j) ++ (in₂ j).initial (p₂ j)))

/-- A network of trained cells of any depth. Each cell is trained by its
own pulse trains. Each of its two read pulses comes from a source or from
the read FIRE of an earlier cell, through a wire. Whenever the earlier
cells fire their reads in their windows, the two read pulses of a cell
arrive after its training, at most a quarter of a unit apart, in either
order. Then the network has a complete run, and in every complete run
each cell fires its read in its window, after the FIRE events of its
training. No gain and no FIRE level is set by hand in any cell. -/
theorem trained_wired_network {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters}
    {ε T rest : ℝ} {b : Fin n → Snapshot 1} {p₁ p₂ : Fin n → Port}
    {u₁ l₁ u₂ l₂ level : Fin n → ℝ} {dates₁ dates₂ : Fin n → List ℝ}
    {middle horizon : Fin n → ℝ} {r₁ r₂ : Fin n → ℕ} (in₁ in₂ : Fin n → ReadInput n)
    (cells : ∀ i, OpenCell (θ i) ε (b i) (p₁ i) (p₂ i) (u₁ i) (l₁ i) (u₂ i) (l₂ i) (level i)
      (dates₁ i) (dates₂ i) (middle i) (horizon i) (r₁ i) (r₂ i))
    (start : ∀ i, (b i).time = T)
    (order₁ : ∀ j, (in₁ j).Before j) (order₂ : ∀ j, (in₂ j).Before j)
    (admissible : ∀ (tf : Fin n → ℝ) (j : Fin n), (∀ i, i < j → ReadWindow in₁ in₂ tf i) →
      horizon j ≤ (in₁ j).arrival tf ∧ horizon j ≤ (in₂ j).arrival tf ∧
      |(in₁ j).arrival tf - (in₂ j).arrival tf| ≤ 1 / 4 ∧
      min ((in₁ j).arrival tf) ((in₂ j).arrival tf) + 22 ≤ rest) :
    ∃ (tf : Fin n → ℝ) (training : Fin n → List ℝ),
      (∀ j, ReadWindow in₁ in₂ tf j) ∧ (∀ j, ∀ t ∈ training j, t ≤ horizon j) ∧
      (∃ (u : Snapshot n) (ref : ParameterExecution (familyParameters θ)
        (wiredRoute horizon p₁ p₂ in₁ in₂) (Snapshot.family T (wiredStart b p₁ p₂ in₁ in₂)) u),
        ParameterCompleteThrough ref rest) ∧
      ∀ {u : Snapshot n} (ex : ParameterExecution (familyParameters θ)
        (wiredRoute horizon p₁ p₂ in₁ in₂) (Snapshot.family T (wiredStart b p₁ p₂ in₁ in₂)) u),
        ParameterCompleteThrough ex rest → ∀ i, ex.emissionTimes i = training i ++ [tf i] := by
  let route := wiredRoute horizon p₁ p₂ in₁ in₂
  let last : (Fin n → List ℝ) → Fin n → ℝ := fun dates i => lastDate (dates i)
  let Spec : Fin n → (Fin n → List ℝ) → Prop := fun j dates =>
    ∃ training, dates j = training ++ [last dates j] ∧ (∀ t ∈ training, t ≤ horizon j) ∧
      horizon j ≤ (in₁ j).arrival (last dates) ∧ horizon j ≤ (in₂ j).arrival (last dates) ∧
      ReadWindow in₁ in₂ (last dates) j
  have arrivals (j : Fin n) (dates dates' : Fin n → List ℝ)
      (agree : ∀ i, i < j → dates i = dates' i) :
      (in₁ j).arrival (last dates) = (in₁ j).arrival (last dates') ∧
        (in₂ j).arrival (last dates) = (in₂ j).arrival (last dates') :=
    ⟨ReadInput.arrival_congr (order₁ j) (fun i hi => congrArg lastDate (agree i hi)),
      ReadInput.arrival_congr (order₂ j) (fun i hi => congrArg lastDate (agree i hi))⟩
  have past : ∀ (j : Fin n) (dates dates' : Fin n → List ℝ),
      (∀ i, i ≤ j → dates i = dates' i) → Spec j dates → Spec j dates' := by
    rintro j dates dates' agree ⟨training, form, early, late₁, late₂, window⟩
    obtain ⟨a₁, a₂⟩ := arrivals j dates dates' (fun i hi => agree i hi.le)
    have self : last dates' j = last dates j := congrArg lastDate (agree j le_rfl).symm
    refine ⟨training, ?_, early, a₁ ▸ late₁, a₂ ▸ late₂, ?_⟩
    · rw [self, ← agree j le_rfl]
      exact form
    · unfold ReadWindow at window ⊢
      rw [← a₁, ← a₂, self]
      exact window
  have causal : ∀ i t d, d ∈ route i t → t < d.due := by
    intro i t d hd
    obtain ⟨k, w, _, due, from_⟩ := mem_wiredRoute hd
    have positive : 0 < w := by
      rcases from_ with e | e
      · have h := order₁ k; rw [e] at h; exact h.2
      · have h := order₂ k; rw [e] at h; exact h.2
    rw [due]
    linarith
  have forward : ∀ i t d, d ∈ route i t → i < d.cell := by
    intro i t d hd
    obtain ⟨k, w, cell, _, from_⟩ := mem_wiredRoute hd
    rw [cell]
    rcases from_ with e | e
    · have h := order₁ k; rw [e] at h; exact h.1
    · have h := order₂ k; rw [e] at h; exact h.1
  obtain ⟨dates, spec, ref, all⟩ := acyclic_network pos (θ := θ) (ε := ε) (T := T) (rest := rest)
    (level := level) route causal forward (wiredStart b p₁ p₂ in₁ in₂) start
    (fun i => (cells i).box) (fun i => (cells i).config₁.cell) (fun i => (cells i).fire)
    (fun i => (cells i).state.requeued _) Spec past (by
      intro dates j below
      have shape : ∀ i, i < j → ∃ training, dates i = training ++ [last dates i] ∧
          (∀ t ∈ training, t ≤ horizon i) ∧ horizon i < last dates i := by
        intro i hi
        obtain ⟨training, form, early, late₁, late₂, window⟩ := below i hi
        exact ⟨training, form, early, by
          have low := le_min late₁ late₂
          linarith [window.1]⟩
      obtain ⟨late₁, late₂, close, wait⟩ :=
        admissible (last dates) j (fun i hi => (below i hi).choose_spec.2.2.2.2)
      obtain ⟨Q, u, tf, training, count, hQ, after, before, reach, rested, date, pend, early⟩ :=
        (cells j).read late₁ late₂ close wait
      have received := wired_incoming (gate := horizon) (p₁ := p₁) (p₂ := p₂) order₁ order₂ dates
        (last dates) j shape
      refine ⟨(b j).pending ++ Q, u, training ++ [tf], count, ?_, reach, rested, date, pend, ?_⟩
      · show (((b j).pending ++ Q : List (Delivery 1)) : Multiset (Delivery 1)) =
          (((b j).pending ++ ((in₁ j).initial (p₁ j) ++ (in₂ j).initial (p₂ j)) :
            List (Delivery 1)) : Multiset (Delivery 1)) + incoming route dates j
        rw [← Multiset.coe_add, ← Multiset.coe_add, hQ, add_assoc, received]
      · obtain ⟨a₁, a₂⟩ := arrivals j (Function.update dates j (training ++ [tf])) dates
          (fun i hi => Function.update_of_ne (ne_of_lt hi) _ _)
        have self : last (Function.update dates j (training ++ [tf])) j = tf := by
          show lastDate (Function.update dates j (training ++ [tf]) j) = tf
          rw [Function.update_self, lastDate_concat]
        refine ⟨training, ?_, early, a₁ ▸ late₁, a₂ ▸ late₂, ?_⟩
        · rw [self, Function.update_self]
        · unfold ReadWindow
          rw [a₁, a₂, self]
          exact ⟨after, before⟩)
  choose training form early _ _ window using spec
  exact ⟨last dates, training, window, early, ref,
    fun ex done i => (all ex done i).trans (form i)⟩

/-! ### The hypotheses are satisfiable at every depth -/

/-- The explicit cell without its read pulses is an open cell. -/
theorem openCell_witness : OpenCell (fun _ => witnessParameters) (1 / 10) witnessSource 0 1
    (2 / 25) (59 / 800) (2 / 25) (59 / 800) 1 (train 0 21) (train 484 21) 484 968 10 10 :=
  let c := trainedCell_witness
  { box := c.box
    distinct := c.distinct
    config₁ := c.config₁
    config₂ := c.config₂
    fire := c.fire
    entry₁ := c.entry₁
    exit₁ := c.exit₁
    entry₂ := c.entry₂
    exit₂ := c.exit₂
    dose₁ := c.dose₁
    dose₂ := c.dose₂
    state := ⟨c.state.main, c.state.aux, c.state.raw, c.state.charge, c.state.sensors,
      c.state.recovery, c.state.energy, c.state.caps⟩
    recovery := c.recovery
    queue := rfl
    spaced₁ := c.spaced₁
    spaced₂ := train_spaced 484 21 968 (by norm_num)
    below₁ := c.below₁
    below₂ := c.below₂
    reach₁ := c.reach₁
    reach₂ := c.reach₂
    enough₁ := c.enough₁
    enough₂ := c.enough₂ }

/-- The inputs of a chain. The first cell is read by a source at date
968. Every other cell is read by the read FIRE of the cell before it,
after one unit. -/
noncomputable def chainInput (n : ℕ) (j : Fin n) : ReadInput n :=
  if j.val = 0 then .source 968
  else .wire ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ 1

theorem chainInput_before (n : ℕ) (j : Fin n) : (chainInput n j).Before j := by
  unfold chainInput
  split_ifs with h
  · trivial
  · exact ⟨Fin.mk_lt_of_lt_val (Nat.sub_lt (Nat.pos_of_ne_zero h) one_pos), one_pos⟩

/-- A chain of `n` copies of the explicit cell, for every `n`. The
first cell is read by a source on its two ports. The read FIRE of each
cell reads the two ports of the next one, one unit later. In every
complete run, each cell fires its read between 1.239 and 1.256 units
after the cell before it. -/
theorem trained_chain_witness (n : ℕ) (pos : 0 < n) :
    ∃ (tf : Fin n → ℝ) (training : Fin n → List ℝ),
      (968 + 239 / 1000 < tf ⟨0, pos⟩ ∧ tf ⟨0, pos⟩ ≤ 968 + 32 / 125) ∧
      (∀ i j : Fin n, j.val = i.val + 1 →
        tf i + 1 + 239 / 1000 < tf j ∧ tf j ≤ tf i + 1 + 32 / 125) ∧
      (∃ (u : Snapshot n) (ref : ParameterExecution
        (familyParameters (fun (_ : Fin n) (_ : Fin 1) => witnessParameters))
        (wiredRoute (fun _ => 968) (fun _ => 0) (fun _ => 1) (chainInput n) (chainInput n))
        (Snapshot.family 0 (wiredStart (fun _ => witnessSource) (fun _ => 0) (fun _ => 1)
          (chainInput n) (chainInput n))) u), ParameterCompleteThrough ref (990 + 2 * n)) ∧
      ∀ {u : Snapshot n} (ex : ParameterExecution
        (familyParameters (fun (_ : Fin n) (_ : Fin 1) => witnessParameters))
        (wiredRoute (fun _ => 968) (fun _ => 0) (fun _ => 1) (chainInput n) (chainInput n))
        (Snapshot.family 0 (wiredStart (fun _ => witnessSource) (fun _ => 0) (fun _ => 1)
          (chainInput n) (chainInput n))) u), ParameterCompleteThrough ex (990 + 2 * n) →
        ∀ i, ex.emissionTimes i = training i ++ [tf i] := by
  have bound : ∀ (k : ℕ) (tf : Fin n → ℝ) (j : Fin n), j.val = k →
      (∀ i, i < j → ReadWindow (chainInput n) (chainInput n) tf i) →
      968 ≤ (chainInput n j).arrival tf ∧ (chainInput n j).arrival tf ≤ 968 + 2 * k := by
    intro k
    induction k with
    | zero =>
      intro tf j hj _
      have e : chainInput n j = .source 968 := by simp [chainInput, hj]
      rw [e]
      exact ⟨le_rfl, by norm_num [ReadInput.arrival]⟩
    | succ k ih =>
      intro tf j hj windows
      have ne : j.val ≠ 0 := by omega
      have e : chainInput n j = .wire ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ 1 := by
        simp [chainInput, ne]
      let i : Fin n := ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
      have lt : i < j := Fin.mk_lt_of_lt_val (Nat.sub_lt (Nat.pos_of_ne_zero ne) one_pos)
      obtain ⟨lo, hi⟩ := ih tf i (by show j.val - 1 = k; omega)
        (fun i' hi' => windows i' (hi'.trans lt))
      have window := windows i lt
      unfold ReadWindow at window
      rw [min_self, max_self] at window
      rw [e]
      show 968 ≤ tf i + 1 ∧ tf i + 1 ≤ 968 + 2 * ((k + 1 : ℕ) : ℝ)
      push_cast
      constructor <;> linarith [window.1, window.2]
  obtain ⟨tf, training, windows, _, ref, all⟩ :=
    trained_wired_network pos (θ := fun _ _ => witnessParameters) (ε := 1 / 10) (T := 0)
      (rest := 990 + 2 * n) (b := fun _ => witnessSource) (chainInput n) (chainInput n)
      (fun _ => openCell_witness) (fun _ => rfl) (chainInput_before n) (chainInput_before n)
      (by
        intro tf j below
        obtain ⟨lo, hi⟩ := bound j.val tf j rfl below
        have small : ((j.val : ℕ) : ℝ) ≤ n := by exact_mod_cast j.isLt.le
        rw [sub_self, abs_zero, min_self]
        exact ⟨lo, lo, by norm_num, by linarith⟩)
  refine ⟨tf, training, ?_, ?_, ref, all⟩
  · have window := windows ⟨0, pos⟩
    unfold ReadWindow at window
    have e : chainInput n ⟨0, pos⟩ = .source 968 := by simp [chainInput]
    rw [e, min_self, max_self] at window
    exact window
  · intro i j next
    have ne : j.val ≠ 0 := by omega
    have window := windows j
    unfold ReadWindow at window
    have e : chainInput n j = .wire i 1 := by
      rw [show chainInput n j = .wire ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ 1 by
        simp [chainInput, ne]]
      congr 1
      exact Fin.ext (by show j.val - 1 = i.val; omega)
    rw [e, min_self, max_self] at window
    exact window

end RecursiveLearning.Native
