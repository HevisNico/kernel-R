import BisectionSearch

/-! A binary search by successive approximation. There is one probe and
one gate for each depth, not for each node. The probe of depth `t` has
its own block of `2 ^ (k - 1 - t)` pulses. Each earlier gate that
answered no adds a block of its own weight. The answers no are therefore
the binary digits of the need, and the count of each question is the
middle of the interval that remains.

A block sent by a gate goes to all the later probes at the same dates.
The last stage has the weight 1 and is the learner: it receives exactly
as many training pulses as its need. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-! ### Spacing of joined pulse trains -/

theorem Spaced.start_le {H : ℝ} : ∀ {dates : List ℝ} {a a' : ℝ},
    Spaced a dates H → a' ≤ a → Spaced a' dates H
  | [], a, a', h, le => by
    have h' : a + 22 ≤ H := h
    show a' + 22 ≤ H
    linarith
  | D :: rest, _, _, h, le => by
    obtain ⟨first, tail⟩ := h
    exact ⟨by linarith, tail⟩

theorem Spaced.horizon_le : ∀ {dates : List ℝ} {a H H' : ℝ},
    Spaced a dates H → H ≤ H' → Spaced a dates H'
  | [], a, H, H', h, le => by
    have h' : a + 22 ≤ H := h
    show a + 22 ≤ H'
    linarith
  | D :: rest, _, _, _, h, le => by
    obtain ⟨first, tail⟩ := h
    exact ⟨first, Spaced.horizon_le tail le⟩

/-- Two spaced trains, the second starting where the first ends, form
one spaced train. -/
theorem Spaced.append : ∀ {first second : List ℝ} {a b H : ℝ},
    Spaced a first b → Spaced (b - 22) second H → Spaced a (first ++ second) H
  | [], second, a, b, H, h₁, h₂ => by
    have h : a + 22 ≤ b := h₁
    exact Spaced.start_le h₂ (by linarith)
  | D :: rest, second, a, b, H, h₁, h₂ => by
    obtain ⟨head, tail⟩ := h₁
    exact ⟨head, Spaced.append tail h₂⟩

theorem train_ge (start : ℝ) (n : ℕ) {D : ℝ} (h : D ∈ train start n) : start + 22 ≤ D :=
  Spaced.later (train_spaced start n (start + 22 * ((n : ℝ) + 1)) le_rfl) D h

/-! ### The arithmetic of the approximation -/

/-- The weight of depth `t`: half of the interval that remains. The last
stage, at depth `k`, has the weight 1. -/
def sarWeight (k t : ℕ) : ℕ := 2 ^ (k - 1 - t)

/-- The lower end of the interval at depth `t`: the weights of the
earlier depths that answered no. -/
def sarLo (k m : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => sarLo k m t + (if sarLo k m t + sarWeight k t < m then sarWeight k t else 0)

/-- The answer of depth `t` is no when the need is above the middle. -/
def sarNo (k m t : ℕ) : Bool := decide (sarLo k m t + sarWeight k t < m)

theorem sarWeight_pos (k t : ℕ) : 1 ≤ sarWeight k t := Nat.one_le_two_pow

theorem sarWeight_double (k t : ℕ) (h : t < k) : 2 ^ (k - t) = 2 * sarWeight k t := by
  unfold sarWeight
  rw [show k - t = (k - 1 - t) + 1 by omega, pow_succ]
  ring

/-- At every depth the need lies in the interval that remains. -/
theorem sarLo_interval (k : ℕ) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) :
    ∀ t, t ≤ k → sarLo k m t < m ∧ m ≤ sarLo k m t + 2 ^ (k - t) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨lo, by simpa [sarLo] using hi⟩
  | succ t ih =>
    intro ht
    obtain ⟨below, above⟩ := ih (by omega)
    have double := sarWeight_double k t (by omega)
    have next : k - (t + 1) = k - 1 - t := by omega
    rw [double] at above
    show sarLo k m t + (if sarLo k m t + sarWeight k t < m then sarWeight k t else 0) < m ∧
      m ≤ sarLo k m t + (if sarLo k m t + sarWeight k t < m then sarWeight k t else 0) +
        2 ^ (k - (t + 1))
    rw [next]
    show _ ∧ m ≤ _ + sarWeight k t
    split_ifs with no <;> omega

/-- The answers no are the binary digits of the need minus one. -/
theorem sarLo_last (k : ℕ) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) : sarLo k m k = m - 1 := by
  obtain ⟨below, above⟩ := sarLo_interval k lo hi k le_rfl
  rw [Nat.sub_self, pow_zero] at above
  omega

/-- The last stage has the weight 1, and its question counts exactly the
need. -/
theorem sar_learner (k : ℕ) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) :
    sarLo k m k + sarWeight k k = m := by
  have w : sarWeight k k = 1 := by
    unfold sarWeight
    rw [show k - 1 - k = 0 by omega, pow_zero]
  rw [sarLo_last k lo hi, w]
  omega

theorem sarWeight_sum (k : ℕ) : ∀ t, t ≤ k →
    ∑ s ∈ Finset.range t, sarWeight k s + 2 ^ (k - t) = 2 ^ k := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have double := sarWeight_double k t (by omega)
    have next : k - (t + 1) = k - 1 - t := by omega
    have prev := ih (by omega)
    rw [Finset.sum_range_succ, next]
    show _ + sarWeight k t + sarWeight k t = _
    omega

/-- The cost of the `k` questions: the sum of their counts is at most
`k (m - 1) + 2 ^ k - 1`. -/
theorem sar_cost (k : ℕ) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) :
    ∑ t ∈ Finset.range k, (sarLo k m t + sarWeight k t) ≤ k * (m - 1) + 2 ^ k - 1 := by
  have weights := sarWeight_sum k k le_rfl
  rw [Nat.sub_self, pow_zero] at weights
  have los : ∑ t ∈ Finset.range k, sarLo k m t ≤ k * (m - 1) := by
    have each : ∀ t ∈ Finset.range k, sarLo k m t ≤ m - 1 := by
      intro t ht
      have := (sarLo_interval k lo hi t (Finset.mem_range.mp ht).le).1
      omega
    simpa using Finset.sum_le_card_nsmul _ _ _ each
  rw [Finset.sum_add_distrib]
  omega

/-! ### The dates -/

/-- The clock pulse of the gate of depth `t`. The probes receive their
own blocks first, all at the same dates. After each answer there is room
for the block of that depth. -/
noncomputable def sarClock (k : ℕ) : ℕ → ℝ
  | 0 => 1000 + 22 * sarWeight k 0 + 3
  | t + 1 => sarClock k t + 22 * (sarWeight k t + 1) + 3

/-- The read pulse of the probe of depth `t`. -/
noncomputable def sarRead (k t : ℕ) : ℝ := sarClock k t - 2

theorem sarClock_step (k t : ℕ) : sarClock k t + 47 ≤ sarClock k (t + 1) := by
  have w : (1 : ℝ) ≤ sarWeight k t := by exact_mod_cast sarWeight_pos k t
  show sarClock k t + 47 ≤ sarClock k t + 22 * (sarWeight k t + 1) + 3
  linarith

theorem sarClock_mono (k : ℕ) {s t : ℕ} (h : s ≤ t) : sarClock k s ≤ sarClock k t := by
  induction h with
  | refl => exact le_rfl
  | @step n _ ih => exact ih.trans (by linarith [sarClock_step k n])

theorem sarClock_ge (k t : ℕ) : 1025 ≤ sarClock k t := by
  have w : (1 : ℝ) ≤ sarWeight k 0 := by exact_mod_cast sarWeight_pos k 0
  have zero : (1025 : ℝ) ≤ sarClock k 0 := by
    show (1025 : ℝ) ≤ 1000 + 22 * sarWeight k 0 + 3
    linarith
  exact zero.trans (sarClock_mono k (Nat.zero_le t))

/-- The date of the last clock pulse: the run of depth `k` lasts about
`33 * 2 ^ k` units. -/
theorem sarClock_closed (k : ℕ) : ∀ t, t ≤ k →
    sarClock k t + 22 * (2 : ℝ) ^ (k - t) =
      1003 + 22 * sarWeight k 0 + 22 * (2 : ℝ) ^ k + 25 * t := by
  intro t
  induction t with
  | zero => intro _; show 1000 + 22 * (sarWeight k 0 : ℝ) + 3 + _ = _; simp; ring
  | succ t ih =>
    intro ht
    have prev := ih (by omega)
    have double : ((2 : ℝ) ^ (k - t)) = 2 * sarWeight k t := by
      exact_mod_cast sarWeight_double k t (by omega)
    have next : ((2 : ℝ) ^ (k - (t + 1))) = sarWeight k t := by
      rw [show k - (t + 1) = k - 1 - t by omega]
      simp [sarWeight]
    show sarClock k t + 22 * (sarWeight k t + 1) + 3 + _ = _
    rw [next]
    push_cast
    linarith

/-- The pulses that the earlier gates send to the probe of depth `t`:
the block of each depth that answered no. -/
noncomputable def gateBlocks (k m : ℕ) : ℕ → List ℝ
  | 0 => []
  | t + 1 => gateBlocks k m t ++
      (if sarNo k m t then train (sarClock k t) (sarWeight k t) else [])

/-- The training pulses of the probe of depth `t` after the first: the
rest of its own block, then the blocks of the earlier gates. -/
noncomputable def probeDates (k m t : ℕ) : List ℝ :=
  train 1000 (sarWeight k t - 1) ++ gateBlocks k m t

theorem gateBlocks_length (k m : ℕ) : ∀ t, (gateBlocks k m t).length = sarLo k m t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show (gateBlocks k m t ++ (if sarNo k m t then train (sarClock k t) (sarWeight k t)
      else [])).length = sarLo k m t + (if sarLo k m t + sarWeight k t < m then sarWeight k t
        else 0)
    rw [List.length_append, ih]
    by_cases no : sarLo k m t + sarWeight k t < m
    · simp [sarNo, no, train_length]
    · simp [sarNo, no]

/-- The probe of depth `t` receives as many training pulses as the
middle of the interval that remains. -/
theorem probeDates_count (k m t : ℕ) :
    (probeDates k m t).length + 1 = sarLo k m t + sarWeight k t := by
  have w := sarWeight_pos k t
  unfold probeDates
  rw [List.length_append, train_length, gateBlocks_length]
  omega

theorem gateBlocks_spaced (k m : ℕ) : ∀ t {a : ℝ} {own : List ℝ},
    Spaced a own (sarRead k 0 - 1) → Spaced a (own ++ gateBlocks k m t) (sarRead k t - 1) := by
  intro t
  induction t with
  | zero =>
    intro a own h
    show Spaced a (own ++ []) _
    rw [List.append_nil]
    exact h
  | succ t ih =>
    intro a own h
    have prev := ih h
    have step : sarRead k (t + 1) - 1 = sarClock k t + 22 * (sarWeight k t + 1) := by
      show sarClock k t + 22 * (sarWeight k t + 1) + 3 - 2 - 1 = _
      ring
    show Spaced a (own ++ (gateBlocks k m t ++ _)) _
    rw [← List.append_assoc, step]
    cases sarNo k m t
    · have w : (0 : ℝ) ≤ sarWeight k t := Nat.cast_nonneg _
      rw [show (if false = true then train (sarClock k t) (sarWeight k t) else []) = [] from rfl,
        List.append_nil]
      exact Spaced.horizon_le prev (by unfold sarRead; linarith)
    · refine Spaced.append prev (Spaced.start_le
        (train_spaced (sarClock k t) (sarWeight k t) _ le_rfl) ?_)
      unfold sarRead
      linarith

/-- The pulses of the probe of depth `t` are spaced, whatever the
answers. -/
theorem probeDates_spaced (k m t : ℕ) (ht : t ≤ k) :
    Spaced 1000 (probeDates k m t) (sarRead k t - 1) := by
  apply gateBlocks_spaced
  have one := sarWeight_pos k t
  have small : sarWeight k t ≤ sarWeight k 0 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have cast : (sarWeight k t : ℝ) ≤ sarWeight k 0 := by exact_mod_cast small
  apply train_spaced
  rw [Nat.cast_pred one]
  show 1000 + 22 * ((sarWeight k t : ℝ) - 1 + 1) ≤ 1000 + 22 * sarWeight k 0 + 3 - 2 - 1
  linarith

/-! ### The network -/

/-- Cell `i` of the network of depth `k`. Cell `2 t` is the probe of
depth `t`, for `t ≤ k`. Cell `2 t + 1` is the gate of depth `t`, for
`t < k`. The probe of depth `k` is the learner. -/
def sarCell (k i : ℕ) : Fin (2 * k + 1) := ⟨i % (2 * k + 1), Nat.mod_lt _ (by omega)⟩

theorem sarCell_val (k : ℕ) {i : ℕ} (h : i < 2 * k + 1) : (sarCell k i).val = i :=
  Nat.mod_eq_of_lt h

/-- A statement about every cell follows from the same statement about
every probe and every gate. -/
theorem sar_cases {k : ℕ} {motive : Bool → ℕ → Prop} (j : Fin (2 * k + 1))
    (probe : ∀ t, t ≤ k → motive true t) (gate : ∀ t, t < k → motive false t) :
    motive (decide (j.val % 2 = 0)) (j.val / 2) := by
  have := j.isLt
  by_cases even : j.val % 2 = 0
  · rw [decide_eq_true even]
    exact probe _ (by omega)
  · rw [decide_eq_false even]
    exact gate _ (by omega)

/-- The wires from the earlier gates to the probe of depth `t`: the
block of each gate, at the dates that follow its clock pulse. -/
noncomputable def sarWires (k : ℕ) : ℕ → List (Wire (2 * k + 1))
  | 0 => []
  | t + 1 => sarWires k t ++ (train (sarClock k t) (sarWeight k t)).map
      (fun D => (⟨sarCell k (2 * t + 1), 0, D⟩ : Wire (2 * k + 1)))

noncomputable def sarInputsOf (k : ℕ) : Bool → ℕ → List (Wire (2 * k + 1))
  | true, t => sarWires k t
  | false, t => [(⟨sarCell k (2 * t), 1, sarClock k t⟩ : Wire (2 * k + 1))]

noncomputable def sarLoDateOf (k : ℕ) : Bool → ℕ → ℝ
  | true, t => sarRead k t - 1
  | false, t => sarClock k t + 71 / 200

noncomputable def sarHiDateOf (k : ℕ) : Bool → ℕ → ℝ
  | true, t => sarRead k t + 1
  | false, t => sarClock k t + 1

def sarBitOf (k m : ℕ) : Bool → ℕ → Bool
  | true, t => decide (m ≤ sarLo k m t + sarWeight k t)
  | false, t => sarNo k m t

/-- The start of a cell. A probe holds its own block and its read
pulse. A gate holds its training queue and its clock pulse. -/
noncomputable def sarStartOf (k : ℕ) (sp sg : ℕ → Snapshot 1) : Bool → ℕ → Snapshot 1
  | true, t => requeued (sp t) (lesson 0 1000 (train 1000 (sarWeight k t - 1)) (sarRead k t))
  | false, t => requeued (sg t)
      ((sg t).pending ++ [(⟨0, 0, sarClock k t⟩ : Delivery 1)])

def sarPick {α : Type} (fp fg : ℕ → α) : Bool → ℕ → α
  | true, t => fp t
  | false, t => fg t

noncomputable def sarInputs (k : ℕ) (j : Fin (2 * k + 1)) : List (Wire (2 * k + 1)) :=
  sarInputsOf k (decide (j.val % 2 = 0)) (j.val / 2)

noncomputable def sarLoDate (k : ℕ) (j : Fin (2 * k + 1)) : ℝ :=
  sarLoDateOf k (decide (j.val % 2 = 0)) (j.val / 2)

noncomputable def sarHiDate (k : ℕ) (j : Fin (2 * k + 1)) : ℝ :=
  sarHiDateOf k (decide (j.val % 2 = 0)) (j.val / 2)

def sarBit (k m : ℕ) (j : Fin (2 * k + 1)) : Bool :=
  sarBitOf k m (decide (j.val % 2 = 0)) (j.val / 2)

noncomputable def sarStart (k : ℕ) (sp sg : ℕ → Snapshot 1) (j : Fin (2 * k + 1)) :
    Snapshot 1 :=
  sarStartOf k sp sg (decide (j.val % 2 = 0)) (j.val / 2)

theorem sar_probe_view (k : ℕ) {t : ℕ} (ht : t ≤ k) :
    decide ((sarCell k (2 * t)).val % 2 = 0) = true ∧ (sarCell k (2 * t)).val / 2 = t := by
  rw [sarCell_val k (by omega)]
  exact ⟨decide_eq_true (by omega), by omega⟩

theorem sar_gate_view (k : ℕ) {t : ℕ} (ht : t < k) :
    decide ((sarCell k (2 * t + 1)).val % 2 = 0) = false ∧
      (sarCell k (2 * t + 1)).val / 2 = t := by
  rw [sarCell_val k (by omega)]
  exact ⟨decide_eq_false (by omega), by omega⟩

theorem mem_sarWires (k : ℕ) : ∀ t {w : Wire (2 * k + 1)}, w ∈ sarWires k t →
    ∃ s, s < t ∧ w.sender = sarCell k (2 * s + 1) ∧ sarClock k s + 22 ≤ w.date := by
  intro t
  induction t with
  | zero => intro w h; cases h
  | succ t ih =>
    intro w h
    rcases List.mem_append.mp h with old | new
    · obtain ⟨s, hs, rest⟩ := ih old
      exact ⟨s, by omega, rest⟩
    · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp new
      exact ⟨t, by omega, rfl, train_ge _ _ hD⟩

theorem filter_one_sender {n : ℕ} (bit : Fin n → Bool) (c : Fin n) (p : Port) (dates : List ℝ) :
    (((dates.map (fun D => (⟨c, p, D⟩ : Wire n))).filter (fun w => bit w.sender)).map
      Wire.pulse) = if bit c then dates.map (fun D => (⟨0, p, D⟩ : Delivery 1)) else [] := by
  cases h : bit c
  · have none : (dates.map (fun D => (⟨c, p, D⟩ : Wire n))).filter (fun w => bit w.sender) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw
      obtain ⟨D, _, rfl⟩ := List.mem_map.mp hw
      simp [h]
    rw [none]
    rfl
  · have all : (dates.map (fun D => (⟨c, p, D⟩ : Wire n))).filter (fun w => bit w.sender) =
        dates.map (fun D => (⟨c, p, D⟩ : Wire n)) := by
      apply List.filter_eq_self.mpr
      intro w hw
      obtain ⟨D, _, rfl⟩ := List.mem_map.mp hw
      simp [h]
    rw [all]
    simp [Wire.pulse, Function.comp_def]

/-- The pulses that the probe of depth `t` receives from the gates: the
blocks of the depths that answered no. -/
theorem sarWires_received (k m : ℕ) (bit : Fin (2 * k + 1) → Bool) : ∀ t,
    (∀ s, s < t → bit (sarCell k (2 * s + 1)) = sarNo k m s) →
    ((sarWires k t).filter (fun w => bit w.sender)).map Wire.pulse =
      (gateBlocks k m t).map (fun D => (⟨0, 0, D⟩ : Delivery 1)) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro hb
    show (((sarWires k t ++ _).filter _).map _) = (gateBlocks k m t ++ _).map _
    rw [List.filter_append, List.map_append, List.map_append, ih (fun s hs => hb s (by omega)),
      filter_one_sender, hb t (by omega)]
    cases sarNo k m t <;> rfl

/-- The run of the probe of depth `t`. Its question counts the middle of
the interval that remains, and it answers yes exactly when the need is
at most that count. -/
theorem sar_probe_run (k m : ℕ) {t : ℕ} (ht : t ≤ k) {θ : Fin 1 → Parameters} {ε : ℝ}
    {s : Snapshot 1} {upper lower level : ℝ} (cell : ProbeCell θ ε s 0 upper lower level m)
    (start : s.time = 0) (bit : Fin (2 * k + 1) → Bool)
    (hb : ∀ r, r < t → bit (sarCell k (2 * r + 1)) = sarNo k m r) :
    ∃ (P : List (Delivery 1)) (u : Snapshot 1) (l : List ℝ) (count : ℕ),
      (P : Multiset (Delivery 1)) =
        ((lesson 0 1000 (train 1000 (sarWeight k t - 1)) (sarRead k t) : List (Delivery 1)) :
          Multiset (Delivery 1)) +
        ((((sarWires k t).filter (fun w => bit w.sender)).map Wire.pulse : List (Delivery 1)) :
          Multiset (Delivery 1)) ∧
      Reach θ (requeued s P) u l count ∧ RestState θ u ∧ u.time = sarClock k k + 22 ∧
      u.pending = [] ∧
      Signal (sarRead k t - 1) (sarRead k t + 1) l
        (decide (m ≤ sarLo k m t + sarWeight k t)) ∧ True ∧
      u.x 0 (.z 0) = s.x 0 (.z 0) +
        ((min (sarLo k m t + sarWeight k t + 1) m : ℕ) : ℝ) * (8 * (upper - lower)) := by
  have late := sarClock_mono k ht
  obtain ⟨u, l, count, reach, rested, date, pend, signal, gain⟩ :=
    cell.asked (first := 1000) (read := sarRead k t) (dates := probeDates k m t)
      (rest := sarClock k k + 22) (by rw [start]; norm_num) (probeDates_spaced k m t ht)
      (by unfold sarRead; linarith)
  have count' := probeDates_count k m t
  refine ⟨lesson 0 1000 (probeDates k m t) (sarRead k t), u, l, count, ?_, reach, rested, date,
    pend, by rw [count'] at signal; exact signal, trivial, ?_⟩
  · rw [sarWires_received k m bit t hb, Multiset.coe_add]
    apply Multiset.coe_eq_coe.mpr
    unfold lesson probeDates
    rw [List.map_append]
    simp only [List.cons_append, List.append_assoc]
    exact List.Perm.cons _ (List.Perm.append_left _ List.perm_append_comm)
  · have steps : (probeDates k m t).length + 2 = sarLo k m t + sarWeight k t + 1 := by omega
    rw [steps] at gain
    exact gain

/-- The run of the gate of depth `t`. It fires late exactly when its
probe was silent: the need is above the count. -/
theorem sar_gate_run (k m : ℕ) {t : ℕ} (ht : t < k) {θ : Fin 1 → Parameters} {ε : ℝ}
    {s : Snapshot 1} {u₁ l₁ u₂ l₂ level : ℝ} {dates₁ dates₂ : List ℝ} {middle horizon : ℝ}
    {r₁ r₂ : ℕ}
    (cell : OpenCell θ ε s 0 1 u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂)
    (trained : horizon ≤ 1000) (bit : Fin (2 * k + 1) → Bool)
    (hb : bit (sarCell k (2 * t)) = decide (m ≤ sarLo k m t + sarWeight k t)) :
    ∃ (P : List (Delivery 1)) (u : Snapshot 1) (l : List ℝ) (count : ℕ),
      (P : Multiset (Delivery 1)) =
        ((s.pending ++ [(⟨0, 0, sarClock k t⟩ : Delivery 1)] : List (Delivery 1)) :
          Multiset (Delivery 1)) +
        ((([(⟨sarCell k (2 * t), 1, sarClock k t⟩ : Wire (2 * k + 1))].filter
          (fun w => bit w.sender)).map Wire.pulse : List (Delivery 1)) :
            Multiset (Delivery 1)) ∧
      Reach θ (requeued s P) u l count ∧ RestState θ u ∧ u.time = sarClock k k + 22 ∧
      u.pending = [] ∧
      Signal (sarClock k t + 71 / 200) (sarClock k t + 1) l (sarNo k m t) ∧ True ∧ True := by
  have late := sarClock_mono k ht.le
  have after := sarClock_ge k t
  by_cases ans : m ≤ sarLo k m t + sarWeight k t
  · obtain ⟨Q, u, tf, training, count, hQ, _, before, reach, rested, date, pend, early⟩ :=
      cell.read (ρ₁ := sarClock k t) (ρ₂ := sarClock k t) (rest := sarClock k k + 22)
        (by linarith) (by linarith) (by rw [sub_self, abs_zero]; norm_num)
        (by rw [min_self]; linarith)
    rw [max_self] at before
    refine ⟨s.pending ++ Q, u, training ++ [tf], count, ?_, reach, rested, date, pend,
      Or.inr ⟨by simp [sarNo, not_lt.mpr ans], ?_⟩, trivial, trivial⟩
    · simp only [List.filter_cons, hb, ans, decide_true, ite_true, List.filter_nil,
        List.map_cons, List.map_nil, Wire.pulse]
      rw [← Multiset.coe_add, hQ, ← Multiset.coe_add, add_assoc]
      rfl
    · intro d hd
      rcases List.mem_append.mp hd with h | h
      · linarith [early d h]
      · obtain rfl := List.mem_singleton.mp h
        linarith
  · obtain ⟨u, tf, training, count, after', before, reach, rested, date, pend, early⟩ :=
      cell.read_one (ρ := sarClock k t) (rest := sarClock k k + 22) (by linarith) (by linarith)
    refine ⟨_, u, training ++ [tf], count, ?_, reach, rested, date, pend,
      Or.inl ⟨by simp [sarNo, not_le.mp ans], training, tf, rfl, ?_, after', before⟩,
      trivial, trivial⟩
    · simp only [List.filter_cons, hb, ans, decide_false, Bool.false_eq_true, ite_false,
        List.filter_nil, List.map_nil, Multiset.coe_nil, add_zero]
    · intro d hd
      linarith [early d hd]

/-- The final state of a cell: the gain of a probe has received one dose
for each pulse of its question, up to its need. -/
def sarFinalOf (k m : ℕ) (sp : ℕ → Snapshot 1) (dose : ℕ → ℝ) : Bool → ℕ → Snapshot 1 → Prop
  | true, t, u => u.x 0 (.z 0) = (sp t).x 0 (.z 0) +
      ((min (sarLo k m t + sarWeight k t + 1) m : ℕ) : ℝ) * dose t
  | false, _, _ => True

theorem sarBit_gate (k m : ℕ) {s : ℕ} (hs : s < k) :
    sarBit k m (sarCell k (2 * s + 1)) = sarNo k m s := by
  unfold sarBit
  rw [(sar_gate_view k hs).1, (sar_gate_view k hs).2]
  rfl

theorem sarBit_probe (k m : ℕ) {t : ℕ} (ht : t ≤ k) :
    sarBit k m (sarCell k (2 * t)) = decide (m ≤ sarLo k m t + sarWeight k t) := by
  unfold sarBit
  rw [(sar_probe_view k ht).1, (sar_probe_view k ht).2]
  rfl

/-- A binary search by successive approximation, with `2 k + 1` cells:
a probe and a gate for each depth below `k`, and the learner. Every
probe has the need `m`, with its own parameters, start gain, dose and
FIRE level. Every gate is trained before the date 1000. The network has
a complete run, and in every complete run:

- the probe of depth `t` fires in its report window exactly when `m` is
  at most the count of its question, the middle of the interval that
  remains;
- the gate of depth `t` fires late exactly when `m` is above that count;
- the gain of each probe ends one dose higher for each pulse of its
  question, up to its need.

The FIRE dates and the final values are the same in every complete
run. -/
theorem successive_search (k m : ℕ) {ε : ℝ} {θp θg : ℕ → Fin 1 → Parameters}
    {sp sg : ℕ → Snapshot 1} {up lp levelp u₁ l₁ u₂ l₂ levelg middle horizon : ℕ → ℝ}
    {dates₁ dates₂ : ℕ → List ℝ} {r₁ r₂ : ℕ → ℕ}
    (probes : ∀ t, t ≤ k → ProbeCell (θp t) ε (sp t) 0 (up t) (lp t) (levelp t) m)
    (gates : ∀ t, t < k → OpenCell (θg t) ε (sg t) 0 1 (u₁ t) (l₁ t) (u₂ t) (l₂ t) (levelg t)
      (dates₁ t) (dates₂ t) (middle t) (horizon t) (r₁ t) (r₂ t))
    (trained : ∀ t, t < k → horizon t ≤ 1000)
    (startP : ∀ t, t ≤ k → (sp t).time = 0) (startG : ∀ t, t < k → (sg t).time = 0) :
    ∃ (dates : Fin (2 * k + 1) → List ℝ) (u : Fin (2 * k + 1) → Snapshot 1),
      (∀ t, t ≤ k → Signal (sarRead k t - 1) (sarRead k t + 1) (dates (sarCell k (2 * t)))
        (decide (m ≤ sarLo k m t + sarWeight k t))) ∧
      (∀ t, t < k → Signal (sarClock k t + 71 / 200) (sarClock k t + 1)
        (dates (sarCell k (2 * t + 1))) (sarNo k m t)) ∧
      (∀ t, t ≤ k → (u (sarCell k (2 * t))).x 0 (.z 0) = (sp t).x 0 (.z 0) +
        ((min (sarLo k m t + sarWeight k t + 1) m : ℕ) : ℝ) * (8 * (up t - lp t))) ∧
      (∃ ref : ParameterExecution
        (familyParameters (fun j : Fin (2 * k + 1) =>
          sarPick θp θg (decide (j.val % 2 = 0)) (j.val / 2)))
        (signalRoute (sarLoDate k) (sarHiDate k) (sarInputs k))
        (Snapshot.family 0 (sarStart k sp sg)) (Snapshot.family (sarClock k k + 22) u),
        ParameterCompleteThrough ref (sarClock k k + 22)) ∧
      ∀ {w : Snapshot (2 * k + 1)} (ex : ParameterExecution
        (familyParameters (fun j : Fin (2 * k + 1) =>
          sarPick θp θg (decide (j.val % 2 = 0)) (j.val / 2)))
        (signalRoute (sarLoDate k) (sarHiDate k) (sarInputs k))
        (Snapshot.family 0 (sarStart k sp sg)) w),
        ParameterCompleteThrough ex (sarClock k k + 22) →
        (∀ i, ex.emissionTimes i = dates i) ∧ ∀ i c, w.x i c = (u i).x 0 c := by
  have wires : ∀ j, ∀ w ∈ sarInputs k j, w.sender < j ∧ sarHiDate k w.sender < w.date := by
    intro j w hw
    have bound := j.isLt
    have hw' : w ∈ sarInputsOf k (decide (j.val % 2 = 0)) (j.val / 2) := hw
    by_cases even : j.val % 2 = 0
    · rw [decide_eq_true even] at hw'
      obtain ⟨s, hs, from_, date⟩ := mem_sarWires k _ hw'
      have sk : s < k := by omega
      rw [from_]
      refine ⟨?_, ?_⟩
      · show (sarCell k (2 * s + 1)).val < j.val
        rw [sarCell_val k (by omega)]
        omega
      · unfold sarHiDate
        rw [(sar_gate_view k sk).1, (sar_gate_view k sk).2]
        show sarClock k s + 1 < w.date
        linarith
    · rw [decide_eq_false even] at hw'
      obtain rfl := List.mem_singleton.mp hw'
      have tk : j.val / 2 ≤ k := by omega
      refine ⟨?_, ?_⟩
      · show (sarCell k (2 * (j.val / 2))).val < j.val
        rw [sarCell_val k (by omega)]
        omega
      · unfold sarHiDate
        rw [(sar_probe_view k tk).1, (sar_probe_view k tk).2]
        show sarRead k (j.val / 2) + 1 < sarClock k (j.val / 2)
        unfold sarRead
        linarith
  obtain ⟨dates, u, spec, fin, _, ref, all⟩ := signal_network_states (by omega : 0 < 2 * k + 1)
    (θ := fun j : Fin (2 * k + 1) => sarPick θp θg (decide (j.val % 2 = 0)) (j.val / 2))
    (ε := ε) (T := 0) (rest := sarClock k k + 22)
    (level := fun j : Fin (2 * k + 1) => sarPick levelp levelg (decide (j.val % 2 = 0)) (j.val / 2))
    (sarLoDate k) (sarHiDate k) (sarInputs k) wires (sarStart k sp sg)
    (fun j => sar_cases (motive := fun b t => (sarStartOf k sp sg b t).time = 0) j
      (fun t ht => startP t ht) (fun t ht => startG t ht))
    (fun j => sar_cases (motive := fun b t => @PhysicalBox 1 (sarPick θp θg b t) ε) j
      (fun t ht => (probes t ht).box) (fun t ht => (gates t ht).box))
    (fun j => sar_cases
      (motive := fun b t => CellConfig (sarPick θp θg b t) (sarPick levelp levelg b t)) j
      (fun t ht => (probes t ht).config.cell) (fun t ht => (gates t ht).config₁.cell))
    (fun j => sar_cases (motive := fun b t => 19 / 20 ≤ sarPick levelp levelg b t ∧
        sarPick levelp levelg b t ≤ 21 / 20) j
      (fun t ht => (probes t ht).fire) (fun t ht => (gates t ht).fire))
    (fun j => sar_cases
      (motive := fun b t => RestState (sarPick θp θg b t) (sarStartOf k sp sg b t)) j
      (fun t ht => (probes t ht).state.requeued _) (fun t ht => (gates t ht).state.requeued _))
    (sarBit k m) (fun _ _ => True)
    (fun j v => sarFinalOf k m sp (fun t => 8 * (up t - lp t)) (decide (j.val % 2 = 0))
      (j.val / 2) v)
    (fun j => sar_cases (motive := fun b t =>
        ∃ (P : List (Delivery 1)) (v : Snapshot 1) (l : List ℝ) (count : ℕ),
          (P : Multiset (Delivery 1)) =
            (((sarStartOf k sp sg b t).pending : List (Delivery 1)) : Multiset (Delivery 1)) +
              ((((sarInputsOf k b t).filter (fun w => sarBit k m w.sender)).map Wire.pulse :
                List (Delivery 1)) : Multiset (Delivery 1)) ∧
          Reach (sarPick θp θg b t) (requeued (sarStartOf k sp sg b t) P) v l count ∧
          RestState (sarPick θp θg b t) v ∧ v.time = sarClock k k + 22 ∧ v.pending = [] ∧
          Signal (sarLoDateOf k b t) (sarHiDateOf k b t) l (sarBitOf k m b t) ∧ True ∧
          sarFinalOf k m sp (fun t => 8 * (up t - lp t)) b t v) j
      (fun t ht => sar_probe_run k m ht (probes t ht) (startP t ht) (sarBit k m)
        (fun r hr => sarBit_gate k m (by omega)))
      (fun t ht => sar_gate_run k m ht (gates t ht) (trained t ht) (sarBit k m)
        (sarBit_probe k m ht.le)))
  refine ⟨dates, u, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ref, all⟩
  · have h := (spec (sarCell k (2 * t))).1
    unfold sarLoDate sarHiDate sarBit at h
    rw [(sar_probe_view k ht).1, (sar_probe_view k ht).2] at h
    exact h
  · have h := (spec (sarCell k (2 * t + 1))).1
    unfold sarLoDate sarHiDate sarBit at h
    rw [(sar_gate_view k ht).1, (sar_gate_view k ht).2] at h
    exact h
  · have h := fin (sarCell k (2 * t))
    rw [(sar_probe_view k ht).1, (sar_probe_view k ht).2] at h
    exact h

/-! ### What the run means -/

/-- The lower end of the interval is the sum of the weights of the
depths that answered no. -/
theorem sarLo_sum (k m : ℕ) : ∀ t,
    sarLo k m t = ∑ s ∈ Finset.range t, (if sarNo k m s then sarWeight k s else 0) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    show sarLo k m t + (if sarLo k m t + sarWeight k t < m then sarWeight k t else 0) = _
    simp [sarNo]

/-- The gates that fire late give the binary digits of the need minus
one. -/
theorem successive_digits (k : ℕ) {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 2 ^ k) :
    ∑ s ∈ Finset.range k, (if sarNo k m s then sarWeight k s else 0) = m - 1 := by
  rw [← sarLo_sum, sarLo_last k lo hi]

/-- The run of depth `k` ends at the date `1003 + 33 * 2 ^ k + 25 k`. -/
theorem sar_duration (k : ℕ) (kPos : 0 < k) :
    sarClock k k + 22 = 1003 + 33 * (2 : ℝ) ^ k + 25 * k := by
  have closed := sarClock_closed k k le_rfl
  rw [Nat.sub_self, pow_zero] at closed
  have first : (2 : ℝ) ^ k = 2 * sarWeight k 0 := by
    exact_mod_cast sarWeight_double k 0 kPos
  linarith

/-! ### The hypotheses are satisfiable at every depth -/

/-- The explicit cell with its own ERROR thresholds, hence its own
dose. -/
noncomputable def doseParameters (upper lower : ℝ) : Parameters :=
  { witnessParameters with thresholds := { error := fun _ => upper, auxReady := fun _ => lower } }

/-- A probe of need `m` with a start gain within `a` of the centre of
the band and a dose within `b` of 1/20. -/
theorem probeCell_dose (m : ℕ) {z upper lower a b : ℝ}
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25) (exit : 1 / 200 ≤ lower ∧ lower < upper)
    (gain : |z - needCentre 1 (1 / 20) m| ≤ a) (small : a ≤ 3 / 125)
    (dose : |8 * (upper - lower) - 1 / 20| ≤ b) (room : a + m * b + 1 / 8000 < 1 / 40) :
    ProbeCell (fun _ => doseParameters upper lower) (1 / 10) (probeAt z) 0 upper lower 1 m := by
  have c := probeCell_band m (gain.trans small)
  have st := c.state
  exact {
    box := c.box
    config := ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl,
      fun _ => ⟨by show 0 < lower; linarith [exit.1], by show lower ≤ upper; linarith [exit.2],
        by show upper < 1; linarith [entry.2]⟩⟩
    fire := c.fire
    entry := entry
    exit := exit
    state := ⟨st.main, st.aux, st.raw, st.charge, st.sensors, st.recovery, st.energy, st.caps⟩
    recovery := c.recovery
    need := needIs_of_tolerance (level₀ := 1) (d₀ := 1 / 20) (ℓ := 0) (by norm_num)
      (by norm_num) (by linarith [exit.2]) gain dose (by norm_num) (by linarith) }

/-- The search of depth `k` with explicit cells, for every `k ≥ 1`. Each
probe has its own start gain, within 1/100 of the centre of the band of
need `m`, and its own dose, within `1 / (100 * 2 ^ k)` of 1/20. For
every need `m` from 1 to `2 ^ k`, in every complete run:

- the gate of depth `t` fires late exactly when the digit of weight
  `2 ^ (k - 1 - t)` of `m - 1` is one, and those weights add up to
  `m - 1`;
- the learner receives `m` training pulses and its read pulse, its gain
  ends exactly `m` doses higher, and it fires in its report window.

The run ends at the date `1003 + 33 * 2 ^ k + 25 k`. -/
theorem successive_search_witness (k : ℕ) (kPos : 0 < k) (m : ℕ) (lo : 1 ≤ m) (hi : m ≤ 2 ^ k)
    (z upper lower : ℕ → ℝ)
    (entry : ∀ t, 7 / 100 ≤ upper t ∧ upper t ≤ 2 / 25)
    (exit : ∀ t, 1 / 200 ≤ lower t ∧ lower t < upper t)
    (gain : ∀ t, |z t - needCentre 1 (1 / 20) m| ≤ 1 / 100)
    (dose : ∀ t, |8 * (upper t - lower t) - 1 / 20| ≤ 1 / (100 * 2 ^ k)) :
    ∃ (dates : Fin (2 * k + 1) → List ℝ) (u : Fin (2 * k + 1) → Snapshot 1),
      (∀ t, t < k → Signal (sarClock k t + 71 / 200) (sarClock k t + 1)
        (dates (sarCell k (2 * t + 1))) (sarNo k m t)) ∧
      ∑ s ∈ Finset.range k, (if sarNo k m s then sarWeight k s else 0) = m - 1 ∧
      Signal (sarRead k k - 1) (sarRead k k + 1) (dates (sarCell k (2 * k))) true ∧
      (u (sarCell k (2 * k))).x 0 (.z 0) = z k + m * (8 * (upper k - lower k)) ∧
      sarClock k k + 22 = 1003 + 33 * (2 : ℝ) ^ k + 25 * k ∧
      (∃ ref : ParameterExecution
        (familyParameters (fun j : Fin (2 * k + 1) =>
          sarPick (fun t _ => doseParameters (upper t) (lower t)) (fun _ _ => witnessParameters)
            (decide (j.val % 2 = 0)) (j.val / 2)))
        (signalRoute (sarLoDate k) (sarHiDate k) (sarInputs k))
        (Snapshot.family 0 (sarStart k (fun t => probeAt (z t)) (fun _ => witnessSource)))
        (Snapshot.family (sarClock k k + 22) u),
        ParameterCompleteThrough ref (sarClock k k + 22)) ∧
      ∀ {w : Snapshot (2 * k + 1)} (ex : ParameterExecution
        (familyParameters (fun j : Fin (2 * k + 1) =>
          sarPick (fun t _ => doseParameters (upper t) (lower t)) (fun _ _ => witnessParameters)
            (decide (j.val % 2 = 0)) (j.val / 2)))
        (signalRoute (sarLoDate k) (sarHiDate k) (sarInputs k))
        (Snapshot.family 0 (sarStart k (fun t => probeAt (z t)) (fun _ => witnessSource))) w),
        ParameterCompleteThrough ex (sarClock k k + 22) →
        (∀ i, ex.emissionTimes i = dates i) ∧ ∀ i c, w.x i c = (u i).x 0 c := by
  have room : (1 / 100 : ℝ) + m * (1 / (100 * 2 ^ k)) + 1 / 8000 < 1 / 40 := by
    have power : (0 : ℝ) < 2 ^ k := by positivity
    have top : (m : ℝ) ≤ 2 ^ k := by exact_mod_cast hi
    have share : (m : ℝ) * (1 / (100 * 2 ^ k)) ≤ 1 / 100 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  obtain ⟨dates, u, yes, no, gains, ref, all⟩ :=
    successive_search k m (ε := 1 / 10)
      (θp := fun t _ => doseParameters (upper t) (lower t)) (θg := fun _ _ => witnessParameters)
      (sp := fun t => probeAt (z t)) (sg := fun _ => witnessSource) (horizon := fun _ => 968)
      (fun t _ => probeCell_dose m (entry t) (exit t) (gain t) (by norm_num) (dose t) room)
      (fun _ _ => openCell_witness) (fun _ _ => by norm_num) (fun _ _ => rfl) (fun _ _ => rfl)
  have last := sar_learner k lo hi
  have learner := yes k le_rfl
  have learned := gains k le_rfl
  rw [last] at learner learned
  have steps : min (m + 1) m = m := by omega
  rw [steps] at learned
  exact ⟨dates, u, no, successive_digits k lo hi, by simpa using learner, learned,
    sar_duration k kPos, ref, all⟩

end RecursiveLearning.Native
