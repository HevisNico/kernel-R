import SearchCells

/-! A search by questions, with trained cells only.

Each node of a tree asks one question: is the hidden need at most the
number of training pulses of this node? The node has a probe cell and a
gate cell. The probe answers yes by a FIRE in its report window. The gate
is a trained cell read by a clock pulse. With the report of the probe it
fires early, without it it fires late: its late FIRE is the answer no.
Each answer sends the pulses of the next question, at fixed dates. No
gain and no FIRE level is set by hand in any cell. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The role of a cell in the search. -/
inductive Role (N : ℕ)
  | probe (node : Fin N)
  | gate (node : Fin N)
  deriving DecidableEq

/-- The fixed dates of one question: the first training pulse, the later
training pulses, the read pulse and the clock pulse of the gate. -/
structure Question where
  first : ℝ
  dates : List ℝ
  read : ℝ
  clock : ℝ

/-- The number of training pulses of a question. -/
def Question.count (π : Question) : ℕ := π.dates.length + 1

/-- The wires that carry one question from the cell `i`. -/
def lessonWires {n : ℕ} (i : Fin n) (p : Port) (π : Question) : List (Wire n) :=
  (⟨i, p, π.first⟩ : Wire n) ::
    (π.dates.map (fun D => (⟨i, p, D⟩ : Wire n)) ++ [(⟨i, p, π.read⟩ : Wire n)])

theorem lessonWires_received {n : ℕ} (bit : Fin n → Bool) (i : Fin n) (p : Port) (π : Question) :
    ((lessonWires i p π).filter (fun w => bit w.sender)).map Wire.pulse =
      if bit i then lesson p π.first π.dates π.read else [] := by
  cases hb : bit i
  · have none : (lessonWires i p π).filter (fun w => bit w.sender) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw
      have from_ : w.sender = i := by
        simp only [lessonWires, List.mem_cons, List.mem_append, List.mem_map,
          List.not_mem_nil, or_false] at hw
        rcases hw with rfl | ⟨D, _, rfl⟩ | rfl <;> rfl
      simp [from_, hb]
    rw [none]
    rfl
  · have all : (lessonWires i p π).filter (fun w => bit w.sender) = lessonWires i p π := by
      apply List.filter_eq_self.mpr
      intro w hw
      have from_ : w.sender = i := by
        simp only [lessonWires, List.mem_cons, List.mem_append, List.mem_map,
          List.not_mem_nil, or_false] at hw
        rcases hw with rfl | ⟨D, _, rfl⟩ | rfl <;> rfl
      simp [from_, hb]
    rw [all]
    simp [lessonWires, lesson, Wire.pulse, Function.comp_def]

/-- The layout of a search: the role of each cell, the probe and the gate
of each node, the parent of each node with the answer that leads to it,
the dates of each question and the ports used. -/
structure SearchLayout (N n : ℕ) where
  role : Fin n → Role N
  probe : Fin N → Fin n
  gate : Fin N → Fin n
  parent : Fin N → Option (Fin N × Bool)
  plan : Fin N → Question
  probePort : Fin N → Port
  clockPort : Fin N → Port
  reportPort : Fin N → Port

namespace SearchLayout

variable {N n : ℕ} (L : SearchLayout N n)

/-- The cell whose signal starts the question of node `κ`: the probe of
its parent after a yes, the gate of its parent after a no. A root has no
such cell: its question is started by sources. -/
def enabler (κ : Fin N) : Option (Fin n) :=
  (L.parent κ).map (fun a => if a.2 then L.probe a.1 else L.gate a.1)

/-- The input wires of a cell. A probe receives its question. A gate
receives the report of its probe and its clock pulse. -/
def inputsOf : Role N → List (Wire n)
  | .probe κ =>
    match L.enabler κ with
    | none => []
    | some i => lessonWires i (L.probePort κ) (L.plan κ)
  | .gate κ =>
    (⟨L.probe κ, L.reportPort κ, (L.plan κ).clock⟩ : Wire n) ::
      match L.enabler κ with
      | none => []
      | some i => [(⟨i, L.clockPort κ, (L.plan κ).clock⟩ : Wire n)]

def inputs (j : Fin n) : List (Wire n) := L.inputsOf (L.role j)

/-- The report window of a probe starts one unit before its read pulse.
The window of a gate starts 0.355 units after its clock pulse. -/
noncomputable def loOf : Role N → ℝ
  | .probe κ => (L.plan κ).read - 1
  | .gate κ => (L.plan κ).clock + 71 / 200

noncomputable def hiOf : Role N → ℝ
  | .probe κ => (L.plan κ).read + 1
  | .gate κ => (L.plan κ).clock + 1

noncomputable def lo (j : Fin n) : ℝ := L.loOf (L.role j)

noncomputable def hi (j : Fin n) : ℝ := L.hiOf (L.role j)

/-- The bit of a cell for the need `m`. A probe signals yes: its node is
reached and the need is at most its count. A gate signals no: its node
is reached and the need is larger than its count. -/
def bitOf (reached : Fin N → Bool) (need : Fin N → ℕ) : Role N → Bool
  | .probe κ => reached κ && decide (need κ ≤ (L.plan κ).count)
  | .gate κ => reached κ && decide ((L.plan κ).count < need κ)

def bit (reached : Fin N → Bool) (need : Fin N → ℕ) (j : Fin n) : Bool := L.bitOf reached need (L.role j)

/-- The start of a cell. The question and the clock pulse of a root are
in the queues at the start. -/
def startOf (sp sg : Fin N → Snapshot 1) : Role N → Snapshot 1
  | .probe κ => requeued (sp κ)
      (match L.parent κ with
        | none => lesson (L.probePort κ) (L.plan κ).first (L.plan κ).dates (L.plan κ).read
        | some _ => [])
  | .gate κ => requeued (sg κ) ((sg κ).pending ++
      (match L.parent κ with
        | none => [(⟨0, L.clockPort κ, (L.plan κ).clock⟩ : Delivery 1)]
        | some _ => []))

def start (sp sg : Fin N → Snapshot 1) (j : Fin n) : Snapshot 1 := L.startOf sp sg (L.role j)

def pick {α : Type} (fp fg : Fin N → α) : Role N → α
  | .probe κ => fp κ
  | .gate κ => fg κ

/-- The order of the cells and the dates of the questions. Every signal
goes to a later cell. The report of a probe ends before the clock pulse
of its gate, the gate is trained before its clock pulse, and the next
question starts after the gate has answered. -/
structure Sound (T rest : ℝ) (horizon : Fin N → ℝ) : Prop where
  roleProbe : ∀ κ, L.role (L.probe κ) = .probe κ
  roleGate : ∀ κ, L.role (L.gate κ) = .gate κ
  reportOrder : ∀ j κ, L.role j = .gate κ → L.probe κ < j
  parentOrder : ∀ j κ π b, (L.role j = .probe κ ∨ L.role j = .gate κ) →
    L.parent κ = some (π, b) → L.probe π < j ∧ L.gate π < j
  first : ∀ κ, T ≤ (L.plan κ).first
  spaced : ∀ κ, Spaced (L.plan κ).first (L.plan κ).dates ((L.plan κ).read - 1)
  clock : ∀ κ, (L.plan κ).read + 1 < (L.plan κ).clock
  trained : ∀ κ, horizon κ ≤ (L.plan κ).clock
  wait : ∀ κ, (L.plan κ).clock + 22 ≤ rest
  after : ∀ κ π b, L.parent κ = some (π, b) → (L.plan π).clock + 1 < (L.plan κ).first

/-- The nodes reached by the search for the need `m`: the roots, and the
children whose parent is reached and gives the answer that leads to
them. -/
def Consistent (reached : Fin N → Bool) (need : Fin N → ℕ) : Prop :=
  ∀ κ, reached κ = match L.parent κ with
    | none => true
    | some (π, b) =>
      if b then reached π && decide (need π ≤ (L.plan π).count)
      else reached π && decide ((L.plan π).count < need π)

variable {L}

theorem enabler_root {κ : Fin N} (h : L.parent κ = none) : L.enabler κ = none := by
  simp [enabler, h]

/-- The cell that starts the question of a child signals exactly when
the child is reached. -/
theorem enabler_child {T rest : ℝ} {horizon : Fin N → ℝ} (sound : L.Sound T rest horizon)
    {reached : Fin N → Bool} {need : Fin N → ℕ} (rule : L.Consistent reached need) {κ π : Fin N} {b : Bool}
    (h : L.parent κ = some (π, b)) :
    ∃ i, L.enabler κ = some i ∧ L.bit reached need i = reached κ ∧
      (i = L.probe π ∨ i = L.gate π) := by
  have r := rule κ
  rw [h] at r
  cases b
  · refine ⟨L.gate π, by simp [enabler, h], ?_, Or.inr rfl⟩
    simp only [bit, sound.roleGate, bitOf]
    simpa using r.symm
  · refine ⟨L.probe π, by simp [enabler, h], ?_, Or.inl rfl⟩
    simp only [bit, sound.roleProbe, bitOf]
    simpa using r.symm

/-- The pulses of a probe: its question when its node is reached,
nothing otherwise. -/
theorem probe_total {T rest : ℝ} {horizon : Fin N → ℝ} (sound : L.Sound T rest horizon)
    {reached : Fin N → Bool} {need : Fin N → ℕ} (rule : L.Consistent reached need)
    (sp sg : Fin N → Snapshot 1) (κ : Fin N) :
    (L.startOf sp sg (.probe κ)).pending ++
      ((L.inputsOf (.probe κ)).filter (fun w => L.bit reached need w.sender)).map Wire.pulse =
      if reached κ then
        lesson (L.probePort κ) (L.plan κ).first (L.plan κ).dates (L.plan κ).read
      else [] := by
  cases hp : L.parent κ with
  | none =>
    have root : reached κ = true := by
      have r := rule κ
      rw [hp] at r
      exact r
    simp [startOf, requeued, inputsOf, enabler_root hp, hp, root]
  | some a =>
    obtain ⟨π, b⟩ := a
    obtain ⟨i, en, bi, _⟩ := enabler_child sound rule hp
    simp only [startOf, requeued, inputsOf, en, hp, List.nil_append]
    rw [lessonWires_received, bi]

/-- The pulses of a gate: its training queue, its clock pulse when its
node is reached, and the report of its probe when the answer is yes. -/
theorem gate_total {T rest : ℝ} {horizon : Fin N → ℝ} (sound : L.Sound T rest horizon)
    {reached : Fin N → Bool} {need : Fin N → ℕ} (rule : L.Consistent reached need)
    (sp sg : Fin N → Snapshot 1) (κ : Fin N) :
    (((L.startOf sp sg (.gate κ)).pending : List (Delivery 1)) : Multiset (Delivery 1)) +
      ((((L.inputsOf (.gate κ)).filter (fun w => L.bit reached need w.sender)).map Wire.pulse :
        List (Delivery 1)) : Multiset (Delivery 1)) =
      (((sg κ).pending : List (Delivery 1)) : Multiset (Delivery 1)) +
        ((if reached κ then
            ({(⟨0, L.clockPort κ, (L.plan κ).clock⟩ : Delivery 1)} : Multiset (Delivery 1))
          else 0) +
          (if reached κ && decide (need κ ≤ (L.plan κ).count) then
            ({(⟨0, L.reportPort κ, (L.plan κ).clock⟩ : Delivery 1)} : Multiset (Delivery 1))
          else 0)) := by
  have report : L.bit reached need (L.probe κ) = (reached κ && decide (need κ ≤ (L.plan κ).count)) := by
    simp only [bit, sound.roleProbe, bitOf]
  have close (c r : Delivery 1) (Q : List (Delivery 1)) :
      ((Q ++ [c] : List (Delivery 1)) : Multiset (Delivery 1)) + (([r] : List (Delivery 1)) :
        Multiset (Delivery 1)) = (Q : Multiset (Delivery 1)) + ({c} + {r}) := by
    rw [← Multiset.coe_add, add_assoc]
    rfl
  cases hp : L.parent κ with
  | none =>
    have root : reached κ = true := by
      have r := rule κ
      rw [hp] at r
      exact r
    simp only [startOf, requeued, inputsOf, enabler_root hp, hp, List.filter_cons, report, root,
      Bool.true_and, ite_true, List.filter_nil]
    by_cases ans : need κ ≤ (L.plan κ).count
    · simp only [ans, decide_true, ite_true, List.map_cons, List.map_nil, Wire.pulse]
      exact close _ _ _
    · simp only [ans, decide_false, Bool.false_eq_true, ite_false, List.map_nil, add_zero,
        Multiset.coe_nil]
      rw [← Multiset.coe_add]
      rfl
  | some a =>
    obtain ⟨π, b⟩ := a
    obtain ⟨i, en, bi, _⟩ := enabler_child sound rule hp
    simp only [startOf, requeued, inputsOf, en, hp, List.filter_cons, report, bi,
      List.append_nil, List.filter_nil]
    cases hr : reached κ
    · simp only [Bool.false_and, Bool.false_eq_true, ite_false, List.map_nil, add_zero,
        Multiset.coe_nil]
    · by_cases ans : need κ ≤ (L.plan κ).count
      · simp only [ans, decide_true, Bool.true_and, ite_true, List.map_cons, List.map_nil,
          Wire.pulse]
        rw [add_comm ({_} : Multiset (Delivery 1)) {_}]
        rfl
      · simp only [ans, decide_false, Bool.true_and, Bool.false_eq_true, ite_false, ite_true,
          List.map_cons, List.map_nil, add_zero, Wire.pulse]
        rfl

end SearchLayout

/-- The run of a probe cell in the search. It signals yes exactly when
its node is reached and the need is at most its count. A probe whose
node is not reached never fires. -/
theorem search_probe_run {N n : ℕ} {L : SearchLayout N n} {T rest ε : ℝ} {horizon : Fin N → ℝ}
    (sound : L.Sound T rest horizon) {reached : Fin N → Bool} {need : Fin N → ℕ}
    (rule : L.Consistent reached need) {θp : Fin N → Fin 1 → Parameters}
    {sp : Fin N → Snapshot 1} (sg : Fin N → Snapshot 1) {up lp levelp : Fin N → ℝ}
    (probes : ∀ κ, ProbeCell (θp κ) ε (sp κ) (L.probePort κ) (up κ) (lp κ) (levelp κ) (need κ))
    (startP : ∀ κ, (sp κ).time = T) (κ : Fin N) :
    ∃ (P : List (Delivery 1)) (u : Snapshot 1) (l : List ℝ) (count : ℕ),
      (P : Multiset (Delivery 1)) =
        (((L.startOf sp sg (.probe κ)).pending : List (Delivery 1)) : Multiset (Delivery 1)) +
          ((((L.inputsOf (.probe κ)).filter (fun w => L.bit reached need w.sender)).map Wire.pulse :
            List (Delivery 1)) : Multiset (Delivery 1)) ∧
      Reach (θp κ) (requeued (L.startOf sp sg (.probe κ)) P) u l count ∧
      RestState (θp κ) u ∧ u.time = rest ∧ u.pending = [] ∧
      Signal ((L.plan κ).read - 1) ((L.plan κ).read + 1) l
        (reached κ && decide (need κ ≤ (L.plan κ).count)) ∧
      (reached κ = false → l = []) ∧
      u.x 0 (.z (L.probePort κ)) = (sp κ).x 0 (.z (L.probePort κ)) +
        ((if reached κ then min ((L.plan κ).count + 1) (need κ) else 0 : ℕ) : ℝ) *
          (8 * (up κ - lp κ)) := by
  have total := SearchLayout.probe_total sound rule sp sg κ
  rw [Multiset.coe_add, total]
  have far := Spaced.horizon_later (sound.spaced κ)
  cases hr : reached κ
  · obtain ⟨u, count, reach, rested, date, pend, gains⟩ :=
      (probes κ).idle (rest := rest) (by
        rw [startP]
        linarith [sound.first κ, sound.clock κ, sound.wait κ])
    exact ⟨[], u, [], count, by simp, reach, rested, date, pend,
      Or.inr ⟨by simp, by simp⟩, fun _ => rfl, by simp [gains]⟩
  · obtain ⟨u, l, count, reach, rested, date, pend, signal, learned⟩ :=
      (probes κ).asked (first := (L.plan κ).first) (read := (L.plan κ).read)
        (dates := (L.plan κ).dates) (rest := rest) (by rw [startP]; exact sound.first κ)
        (sound.spaced κ) (by linarith [sound.clock κ, sound.wait κ])
    exact ⟨_, u, l, count, by simp, reach, rested, date, pend,
      by rw [Bool.true_and]; exact signal, (fun h => by cases h), by
        simp only [reduceIte]
        exact learned⟩

/-- The run of a gate cell in the search. It signals no exactly when its
node is reached and the need is larger than the count of its probe. -/
theorem search_gate_run {N n : ℕ} {L : SearchLayout N n} {T rest ε : ℝ} {horizon : Fin N → ℝ}
    (sound : L.Sound T rest horizon) {reached : Fin N → Bool} {need : Fin N → ℕ}
    (rule : L.Consistent reached need) {θg : Fin N → Fin 1 → Parameters}
    (sp : Fin N → Snapshot 1) {sg : Fin N → Snapshot 1}
    {u₁ l₁ u₂ l₂ levelg : Fin N → ℝ} {dates₁ dates₂ : Fin N → List ℝ} {middle : Fin N → ℝ}
    {r₁ r₂ : Fin N → ℕ}
    (gates : ∀ κ, OpenCell (θg κ) ε (sg κ) (L.clockPort κ) (L.reportPort κ) (u₁ κ) (l₁ κ)
      (u₂ κ) (l₂ κ) (levelg κ) (dates₁ κ) (dates₂ κ) (middle κ) (horizon κ) (r₁ κ) (r₂ κ))
    (κ : Fin N) :
    ∃ (P : List (Delivery 1)) (u : Snapshot 1) (l : List ℝ) (count : ℕ),
      (P : Multiset (Delivery 1)) =
        (((L.startOf sp sg (.gate κ)).pending : List (Delivery 1)) : Multiset (Delivery 1)) +
          ((((L.inputsOf (.gate κ)).filter (fun w => L.bit reached need w.sender)).map Wire.pulse :
            List (Delivery 1)) : Multiset (Delivery 1)) ∧
      Reach (θg κ) (requeued (L.startOf sp sg (.gate κ)) P) u l count ∧
      RestState (θg κ) u ∧ u.time = rest ∧ u.pending = [] ∧
      Signal ((L.plan κ).clock + 71 / 200) ((L.plan κ).clock + 1) l
        (reached κ && decide ((L.plan κ).count < need κ)) := by
  rw [SearchLayout.gate_total sound rule sp sg κ]
  have trained := sound.trained κ
  have wait := sound.wait κ
  cases hr : reached κ
  · obtain ⟨u, training, count, reach, rested, date, pend, early⟩ :=
      (gates κ).idle (rest := rest) (by linarith)
    refine ⟨_, u, training, count, by simp, reach, rested, date, pend, Or.inr ⟨by simp, ?_⟩⟩
    intro t ht
    linarith [early t ht]
  · by_cases ans : need κ ≤ (L.plan κ).count
    · obtain ⟨Q, u, tf, training, count, hQ, _, before, reach, rested, date, pend, early⟩ :=
        (gates κ).read (ρ₁ := (L.plan κ).clock) (ρ₂ := (L.plan κ).clock) (rest := rest)
          trained trained (by rw [sub_self, abs_zero]; norm_num) (by rw [min_self]; exact wait)
      rw [max_self] at before
      refine ⟨(sg κ).pending ++ Q, u, training ++ [tf], count, ?_, reach, rested, date, pend,
        Or.inr ⟨by simp [not_lt.mpr ans], ?_⟩⟩
      · rw [← Multiset.coe_add, hQ]
        simp [ans]
      · intro t ht
        rcases List.mem_append.mp ht with h | h
        · linarith [early t h]
        · obtain rfl := List.mem_singleton.mp h
          linarith
    · obtain ⟨u, tf, training, count, after, before, reach, rested, date, pend, early⟩ :=
        (gates κ).read_one (ρ := (L.plan κ).clock) (rest := rest) trained wait
      refine ⟨_, u, training ++ [tf], count, ?_, reach, rested, date, pend,
        Or.inl ⟨by simp [not_le.mp ans], training, tf, rfl, ?_, after, before⟩⟩
      · rw [← Multiset.coe_add]
        simp [ans]
      · intro t ht
        linarith [early t ht]

theorem mem_lessonWires {n : ℕ} {i : Fin n} {p : Port} {π : Question} {w : Wire n}
    (h : w ∈ lessonWires i p π) (spaced : Spaced π.first π.dates (π.read - 1)) :
    w.sender = i ∧ π.first ≤ w.date := by
  simp only [lessonWires, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at h
  rcases h with rfl | ⟨D, hD, rfl⟩ | rfl
  · exact ⟨rfl, le_rfl⟩
  · exact ⟨rfl, by have next := Spaced.later spaced D hD; show π.first ≤ D; linarith⟩
  · exact ⟨rfl, by have far := Spaced.horizon_later spaced; show π.first ≤ π.read; linarith⟩

theorem lesson_length (p : Port) (first : ℝ) (dates : List ℝ) (read : ℝ) :
    (lesson p first dates read).length = dates.length + 2 := by
  simp [lesson]

/-- The final state of a cell in the search. The gain of a probe has
received one dose for each pulse of its question, up to its need, when
its node is reached. It has not moved otherwise. -/
def SearchLayout.finalOf {N n : ℕ} (L : SearchLayout N n) (sp : Fin N → Snapshot 1)
    (dose : Fin N → ℝ) (reached : Fin N → Bool) (need : Fin N → ℕ) :
    Role N → Snapshot 1 → Prop
  | .probe κ, u => u.x 0 (.z (L.probePort κ)) = (sp κ).x 0 (.z (L.probePort κ)) +
      ((if reached κ then min ((L.plan κ).count + 1) (need κ) else 0 : ℕ) : ℝ) * dose κ
  | .gate _, _ => True

/-- What the search proves about a cell beyond its bit: a probe whose
node is not reached never fires. -/
def SearchLayout.extraOf {N : ℕ} (reached : Fin N → Bool) : Role N → List ℝ → Prop
  | .probe κ, l => reached κ = false → l = []
  | .gate _, _ => True

/-- A search by questions with trained cells only. The nodes form a
forest. Each node has a probe cell with its own need and a gate cell
trained by its own pulse trains. The questions of the roots are started
by sources. The answer yes of a node is a FIRE of its probe in its
report window. The answer no is a late FIRE of its gate. Each answer
sends the pulses of the questions of the children it leads to.

For the nodes `reached` that the needs select, the network has a
complete run, and in every complete run:

- the probe of a node fires in its report window exactly when the node
  is reached and its need is at most its count;
- the gate of a node fires late exactly when the node is reached and
  its need is larger than its count;
- the probe of a node that is not reached never fires;
- the gain of a probe ends one dose higher for each pulse of its
  question, up to its need, when its node is reached, and unchanged
  otherwise;
- the pulses sent to the probe of a child are its question when the
  child is reached, and none otherwise.

The FIRE dates and the final values are the same in every complete
run. -/
theorem trained_search {N n : ℕ} (pos : 0 < n) (L : SearchLayout N n) {T rest ε : ℝ}
    {horizon : Fin N → ℝ} (sound : L.Sound T rest horizon) {reached : Fin N → Bool}
    {need : Fin N → ℕ} (rule : L.Consistent reached need)
    {θp θg : Fin N → Fin 1 → Parameters}
    {sp sg : Fin N → Snapshot 1} {up lp levelp u₁ l₁ u₂ l₂ levelg : Fin N → ℝ}
    {dates₁ dates₂ : Fin N → List ℝ} {middle : Fin N → ℝ} {r₁ r₂ : Fin N → ℕ}
    (probes : ∀ κ, ProbeCell (θp κ) ε (sp κ) (L.probePort κ) (up κ) (lp κ) (levelp κ) (need κ))
    (gates : ∀ κ, OpenCell (θg κ) ε (sg κ) (L.clockPort κ) (L.reportPort κ) (u₁ κ) (l₁ κ)
      (u₂ κ) (l₂ κ) (levelg κ) (dates₁ κ) (dates₂ κ) (middle κ) (horizon κ) (r₁ κ) (r₂ κ))
    (startP : ∀ κ, (sp κ).time = T) (startG : ∀ κ, (sg κ).time = T) :
    ∃ (dates : Fin n → List ℝ) (u : Fin n → Snapshot 1),
      (∀ κ, Signal ((L.plan κ).read - 1) ((L.plan κ).read + 1) (dates (L.probe κ))
        (reached κ && decide (need κ ≤ (L.plan κ).count))) ∧
      (∀ κ, Signal ((L.plan κ).clock + 71 / 200) ((L.plan κ).clock + 1) (dates (L.gate κ))
        (reached κ && decide ((L.plan κ).count < need κ))) ∧
      (∀ κ, reached κ = false → dates (L.probe κ) = []) ∧
      (∀ κ, (u (L.probe κ)).x 0 (.z (L.probePort κ)) = (sp κ).x 0 (.z (L.probePort κ)) +
        ((if reached κ then min ((L.plan κ).count + 1) (need κ) else 0 : ℕ) : ℝ) *
          (8 * (up κ - lp κ))) ∧
      (∀ κ π b, L.parent κ = some (π, b) →
        incoming (signalRoute L.lo L.hi L.inputs) dates (L.probe κ) =
          if reached κ then
            ((lesson (L.probePort κ) (L.plan κ).first (L.plan κ).dates (L.plan κ).read :
              List (Delivery 1)) : Multiset (Delivery 1))
          else 0) ∧
      (∃ ref : ParameterExecution
        (familyParameters (fun j => SearchLayout.pick θp θg (L.role j)))
        (signalRoute L.lo L.hi L.inputs) (Snapshot.family T (L.start sp sg))
        (Snapshot.family rest u), ParameterCompleteThrough ref rest) ∧
      ∀ {w : Snapshot n} (ex : ParameterExecution
        (familyParameters (fun j => SearchLayout.pick θp θg (L.role j)))
        (signalRoute L.lo L.hi L.inputs) (Snapshot.family T (L.start sp sg)) w),
        ParameterCompleteThrough ex rest →
        (∀ i, ex.emissionTimes i = dates i) ∧ ∀ i c, w.x i c = (u i).x 0 c := by
  have nodeRun : ∀ r : Role N,
      ∃ (P : List (Delivery 1)) (u : Snapshot 1) (l : List ℝ) (count : ℕ),
        (P : Multiset (Delivery 1)) =
          (((L.startOf sp sg r).pending : List (Delivery 1)) : Multiset (Delivery 1)) +
            ((((L.inputsOf r).filter (fun w => L.bit reached need w.sender)).map Wire.pulse :
              List (Delivery 1)) : Multiset (Delivery 1)) ∧
        Reach (SearchLayout.pick θp θg r) (requeued (L.startOf sp sg r) P) u l count ∧
        RestState (SearchLayout.pick θp θg r) u ∧ u.time = rest ∧ u.pending = [] ∧
        Signal (L.loOf r) (L.hiOf r) l (L.bitOf reached need r) ∧
        SearchLayout.extraOf reached r l ∧
        L.finalOf sp (fun κ => 8 * (up κ - lp κ)) reached need r u := by
    intro r
    cases r with
    | probe κ => exact search_probe_run sound rule sg probes startP κ
    | gate κ =>
      obtain ⟨P, u, l, count, hP, reach, rested, date, pend, signal⟩ :=
        search_gate_run sound rule sp gates κ
      exact ⟨P, u, l, count, hP, reach, rested, date, pend, signal, trivial, trivial⟩
  have wires : ∀ j, ∀ w ∈ L.inputs j, w.sender < j ∧ L.hi w.sender < w.date := by
    intro j w hw
    have child (κ π : Fin N) (b : Bool) (role : L.role j = .probe κ ∨ L.role j = .gate κ)
        (hp : L.parent κ = some (π, b)) (i : Fin n) (which : i = L.probe π ∨ i = L.gate π) :
        i < j ∧ L.hi i < (L.plan κ).first := by
      obtain ⟨o₁, o₂⟩ := sound.parentOrder j κ π b role hp
      have late := sound.after κ π b hp
      have clock := sound.clock π
      rcases which with rfl | rfl
      · refine ⟨o₁, ?_⟩
        show L.hiOf (L.role (L.probe π)) < _
        rw [sound.roleProbe]
        show (L.plan π).read + 1 < _
        linarith
      · refine ⟨o₂, ?_⟩
        show L.hiOf (L.role (L.gate π)) < _
        rw [sound.roleGate]
        exact late
    have far (κ : Fin N) := Spaced.horizon_later (sound.spaced κ)
    have hw' : w ∈ L.inputsOf (L.role j) := hw
    cases hr : L.role j with
    | probe κ =>
      rw [hr] at hw'
      cases hp : L.parent κ with
      | none => simp [SearchLayout.inputsOf, SearchLayout.enabler_root hp] at hw'
      | some a =>
        obtain ⟨π, b⟩ := a
        obtain ⟨i, en, _, which⟩ := SearchLayout.enabler_child sound rule hp
        simp only [SearchLayout.inputsOf, en] at hw'
        obtain ⟨from_, date⟩ := mem_lessonWires hw' (sound.spaced κ)
        obtain ⟨lt, hi⟩ := child κ π b (Or.inl hr) hp i which
        rw [from_]
        exact ⟨lt, by linarith⟩
    | gate κ =>
      rw [hr] at hw'
      simp only [SearchLayout.inputsOf, List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · refine ⟨sound.reportOrder j κ hr, ?_⟩
        show L.hiOf (L.role (L.probe κ)) < (L.plan κ).clock
        rw [sound.roleProbe]
        exact sound.clock κ
      · cases hp : L.parent κ with
        | none => simp [SearchLayout.enabler_root hp] at hw'
        | some a =>
          obtain ⟨π, b⟩ := a
          obtain ⟨i, en, _, which⟩ := SearchLayout.enabler_child sound rule hp
          simp only [en, List.mem_singleton] at hw'
          obtain ⟨lt, hi⟩ := child κ π b (Or.inr hr) hp i which
          rw [hw']
          exact ⟨lt, by
            show L.hi i < (L.plan κ).clock
            linarith [far κ, sound.clock κ]⟩
  obtain ⟨dates, u, spec, fin, sent, ref, all⟩ := signal_network_states pos
    (θ := fun j => SearchLayout.pick θp θg (L.role j))
    (ε := ε) (T := T) (rest := rest) (level := fun j => SearchLayout.pick levelp levelg (L.role j))
    L.lo L.hi L.inputs wires (L.start sp sg)
    (fun j => by
      show (L.startOf sp sg (L.role j)).time = T
      cases L.role j with
      | probe κ => exact startP κ
      | gate κ => exact startG κ)
    (fun j => by
      show @PhysicalBox 1 (SearchLayout.pick θp θg (L.role j)) ε
      cases L.role j with
      | probe κ => exact (probes κ).box
      | gate κ => exact (gates κ).box)
    (fun j => by
      show CellConfig (SearchLayout.pick θp θg (L.role j))
        (SearchLayout.pick levelp levelg (L.role j))
      cases L.role j with
      | probe κ => exact (probes κ).config.cell
      | gate κ => exact (gates κ).config₁.cell)
    (fun j => by
      show 19 / 20 ≤ SearchLayout.pick levelp levelg (L.role j) ∧
        SearchLayout.pick levelp levelg (L.role j) ≤ 21 / 20
      cases L.role j with
      | probe κ => exact (probes κ).fire
      | gate κ => exact (gates κ).fire)
    (fun j => by
      show RestState (SearchLayout.pick θp θg (L.role j)) (L.startOf sp sg (L.role j))
      cases L.role j with
      | probe κ => exact (probes κ).state.requeued _
      | gate κ => exact (gates κ).state.requeued _)
    (L.bit reached need) (fun j l => SearchLayout.extraOf reached (L.role j) l)
    (fun j v => L.finalOf sp (fun κ => 8 * (up κ - lp κ)) reached need (L.role j) v)
    (fun j => nodeRun (L.role j))
  refine ⟨dates, u, fun κ => ?_, fun κ => ?_, fun κ => ?_, fun κ => ?_, fun κ π b hp => ?_,
    ref, all⟩
  · have h := (spec (L.probe κ)).1
    simp only [SearchLayout.lo, SearchLayout.hi, SearchLayout.bit, sound.roleProbe,
      SearchLayout.loOf, SearchLayout.hiOf, SearchLayout.bitOf] at h
    exact h
  · have h := (spec (L.gate κ)).1
    simp only [SearchLayout.lo, SearchLayout.hi, SearchLayout.bit, sound.roleGate,
      SearchLayout.loOf, SearchLayout.hiOf, SearchLayout.bitOf] at h
    exact h
  · have h := (spec (L.probe κ)).2
    simp only [sound.roleProbe, SearchLayout.extraOf] at h
    exact h
  · have h := fin (L.probe κ)
    simp only [sound.roleProbe, SearchLayout.finalOf] at h
    exact h
  · rw [sent (L.probe κ)]
    have total := SearchLayout.probe_total sound rule sp sg κ
    simp only [SearchLayout.startOf, requeued, hp, List.nil_append] at total
    show ((((L.inputsOf (L.role (L.probe κ))).filter
      (fun w => L.bit reached need w.sender)).map Wire.pulse : List (Delivery 1)) :
        Multiset (Delivery 1)) = _
    rw [sound.roleProbe, total]
    cases reached κ <;> rfl

/-! ### The hypotheses are satisfiable: a binary search over four needs -/

/-- A rested probe cell whose port needs `m` doses. Its start gain is
`m` doses of 1/20 below the gain that just reaches the FIRE level. -/
noncomputable def needStart (m : ℕ) : Snapshot 1 where
  time := 0
  x := fun _ c => match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z _ => Real.log ((9 / 10) / response 1) - m * (1 / 20)
    | .b => 2 / 25
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := []

theorem probeCell_witness (m : ℕ) :
    ProbeCell (fun _ => witnessParameters) (1 / 10) (needStart m) 0 (2 / 25) (59 / 800) 1 m := by
  have c := trainedCell_witness
  have rPos := response_one_pos
  have rLow := response_one_lower
  have gPos : (0 : ℝ) < (9 / 10) / response 1 := div_pos (by norm_num) rPos
  have peak : Real.exp (Real.log ((9 / 10) / response 1)) * response 1 = 9 / 10 := by
    rw [Real.exp_log gPos]
    field_simp
  have dose : (8 : ℝ) * (2 / 25 - 59 / 800) = 1 / 20 := by norm_num
  exact {
    box := c.box
    config := c.config₁
    fire := c.fire
    entry := c.entry₁
    exit := c.exit₁
    state := {
      main := rfl
      aux := fun _ => rfl
      raw := fun _ => rfl
      charge := by show (1 / 10 : ℝ) ≤ 1 / 10 ∧ (1 / 10 : ℝ) ≤ 1 / 10 + 1 / 10000; norm_num
      sensors := fun _ => by
        show (1 / 40 - 1 / 100000 : ℝ) ≤ 1 / 40 ∧ (1 / 40 : ℝ) ≤ 1 / 40 + 1 / 100000
        norm_num
      recovery := by show (0 : ℝ) ≤ 2 / 25 ∧ (2 / 25 : ℝ) ≤ 11 / 10; norm_num
      energy := by show (50 : ℝ) ≤ 100 ∧ (100 : ℝ) ≤ 100; norm_num
      caps := fun _ => by
        show Real.log ((9 / 10) / response 1) - m * (1 / 20) ≤ Real.log 4
        have small : (9 / 10) / response 1 ≤ 4 := by
          rw [div_le_iff₀ rPos]
          linarith
        have steps : (0 : ℝ) ≤ m * (1 / 20) := by positivity
        linarith [Real.log_le_log gPos small] }
    recovery := by show (7 / 100 : ℝ) ≤ 2 / 25 ∧ (2 / 25 : ℝ) ≤ 1 / 10; norm_num
    need := by
      show NeedIs 1 (8 * (2 / 25 - 59 / 800))
        (Real.log ((9 / 10) / response 1) - m * (1 / 20)) m
      rw [dose]
      apply needIs_of_peaks (by norm_num)
      · intro k hk
        have form : Real.log ((9 / 10) / response 1) - (m : ℝ) * (1 / 20) + k * (1 / 20) =
            Real.log ((9 / 10) / response 1) + -(1 / 20) := by
          rw [← hk]
          push_cast
          ring
        rw [form, Real.exp_add, mul_right_comm, peak]
        have step : Real.exp (-(1 / 20 : ℝ)) ≤ 20 / 21 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          linarith [Real.add_one_le_exp (1 / 20 : ℝ)]
        linarith
      · have form : Real.log ((9 / 10) / response 1) - (m : ℝ) * (1 / 20) + m * (1 / 20) =
            Real.log ((9 / 10) / response 1) := by ring
        rw [form, peak]
        norm_num }

/-- A search with three questions. The root asks whether the need is at
most 2. After a yes, node 1 asks whether it is at most 1. After a no,
node 2 asks whether it is at most 3. Cells 0, 2, 4 are the probes and
cells 1, 3, 5 are the gates. -/
noncomputable def searchWitness : SearchLayout 3 6 where
  role := ![.probe 0, .gate 0, .probe 1, .gate 1, .probe 2, .gate 2]
  probe := ![0, 2, 4]
  gate := ![1, 3, 5]
  parent := ![none, some (0, true), some (0, false)]
  plan := ![⟨1000, [1022], 1045, 1047⟩, ⟨1050, [], 1073, 1075⟩, ⟨1050, [1072, 1094], 1117, 1119⟩]
  probePort := fun _ => 0
  clockPort := fun _ => 0
  reportPort := fun _ => 1

theorem searchWitness_sound : searchWitness.Sound 0 1150 (fun _ => 968) where
  roleProbe := by intro κ; fin_cases κ <;> rfl
  roleGate := by intro κ; fin_cases κ <;> rfl
  reportOrder := by
    intro j κ
    fin_cases j <;> fin_cases κ <;> simp [searchWitness]
  parentOrder := by
    intro j κ π b
    fin_cases j <;> fin_cases κ <;> simp [searchWitness] <;> rintro rfl _ <;> decide
  first := by intro κ; fin_cases κ <;> norm_num [searchWitness]
  spaced := by intro κ; fin_cases κ <;> norm_num [searchWitness, Spaced]
  clock := by intro κ; fin_cases κ <;> norm_num [searchWitness]
  trained := by intro κ; fin_cases κ <;> norm_num [searchWitness]
  wait := by intro κ; fin_cases κ <;> norm_num [searchWitness]
  after := by
    intro κ π b
    fin_cases κ <;> simp [searchWitness] <;> rintro rfl _ <;> norm_num

/-- The nodes reached for the need `m`. -/
def searchReached (m : ℕ) : Fin 3 → Bool := ![true, decide (m ≤ 2), decide (2 < m)]

theorem searchWitness_consistent (m : ℕ) : searchWitness.Consistent (searchReached m) (fun _ => m) := by
  intro κ
  fin_cases κ <;> simp [searchWitness, searchReached, Question.count]

/-- A binary search over the needs 1 to 4, with six explicit cells. For
every need `m`, in every complete run:

- the root probe fires in its report window exactly when `m ≤ 2`, and
  the root gate fires late exactly when `2 < m`;
- the probe of node 1 fires in its window exactly when `m ≤ 1`, and its
  gate fires late exactly when `m = 2`;
- the probe of node 2 fires in its window exactly when `m = 3`, and its
  gate fires late exactly when `3 < m`.

The pair of answers separates the needs 1, 2, 3 and 4 or more. -/
theorem trained_search_witness (m : ℕ) :
    ∃ dates : Fin 6 → List ℝ,
      Signal (1045 - 1) (1045 + 1) (dates 0) (decide (m ≤ 2)) ∧
      Signal (1047 + 71 / 200) (1047 + 1) (dates 1) (decide (2 < m)) ∧
      Signal (1073 - 1) (1073 + 1) (dates 2) (decide (m ≤ 2) && decide (m ≤ 1)) ∧
      Signal (1075 + 71 / 200) (1075 + 1) (dates 3) (decide (m ≤ 2) && decide (1 < m)) ∧
      Signal (1117 - 1) (1117 + 1) (dates 4) (decide (2 < m) && decide (m ≤ 3)) ∧
      Signal (1119 + 71 / 200) (1119 + 1) (dates 5) (decide (2 < m) && decide (3 < m)) ∧
      (∃ (u : Snapshot 6) (ref : ParameterExecution
        (familyParameters (fun (_ : Fin 6) (_ : Fin 1) => witnessParameters))
        (signalRoute searchWitness.lo searchWitness.hi searchWitness.inputs)
        (Snapshot.family 0 (searchWitness.start (fun _ => needStart m) (fun _ => witnessSource)))
        u), ParameterCompleteThrough ref 1150) ∧
      ∀ {u : Snapshot 6} (ex : ParameterExecution
        (familyParameters (fun (_ : Fin 6) (_ : Fin 1) => witnessParameters))
        (signalRoute searchWitness.lo searchWitness.hi searchWitness.inputs)
        (Snapshot.family 0 (searchWitness.start (fun _ => needStart m) (fun _ => witnessSource)))
        u), ParameterCompleteThrough ex 1150 → ∀ i, ex.emissionTimes i = dates i := by
  obtain ⟨dates, _, yes, no, _, _, _, ref, all⟩ :=
    trained_search (by norm_num : 0 < 6) searchWitness searchWitness_sound
      (searchWitness_consistent m) (θp := fun _ _ => witnessParameters)
      (θg := fun _ _ => witnessParameters) (sp := fun _ => needStart m)
      (sg := fun _ => witnessSource) (fun _ => probeCell_witness m) (fun _ => openCell_witness)
      (fun _ => rfl) (fun _ => rfl)
  have same : (fun j => SearchLayout.pick (fun (_ : Fin 3) (_ : Fin 1) => witnessParameters)
      (fun _ _ => witnessParameters) (searchWitness.role j)) =
      fun (_ : Fin 6) (_ : Fin 1) => witnessParameters := by
    funext j
    cases searchWitness.role j <;> rfl
  rw [same] at ref all
  obtain ⟨run, complete⟩ := ref
  exact ⟨dates, yes 0, no 0, yes 1, no 1, yes 2, no 2, ⟨_, run, complete⟩,
    fun ex done => (all ex done).1⟩

end RecursiveLearning.Native
