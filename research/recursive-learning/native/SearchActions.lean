import NeedTolerance

/-! A search that ends by an action. After the three questions of the
binary search, the last answer sends a lesson to one learner cell: the
one that stands for the need that was found. The lesson has one pulse
more than that need. The learner ends exactly at its firing gain and
confirms it by a FIRE. The three other learners receive no pulse. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- Seven nodes. Nodes 0, 1 and 2 are the questions of the binary search
over the needs 1 to 4. Nodes 3 to 6 are the lessons: node `m + 2` is
reached exactly when the need is `m`, and its question has `m` training
pulses and one last pulse. Cell `2 κ` is the probe of node `κ` and cell
`2 κ + 1` is its gate. -/
noncomputable def actionSearch : SearchLayout 7 14 where
  role := ![.probe 0, .gate 0, .probe 1, .gate 1, .probe 2, .gate 2, .probe 3, .gate 3,
    .probe 4, .gate 4, .probe 5, .gate 5, .probe 6, .gate 6]
  probe := ![0, 2, 4, 6, 8, 10, 12]
  gate := ![1, 3, 5, 7, 9, 11, 13]
  parent := ![none, some (0, true), some (0, false), some (1, true), some (1, false),
    some (2, true), some (2, false)]
  plan := ![⟨1000, [1022], 1045, 1047⟩, ⟨1050, [], 1073, 1075⟩,
    ⟨1050, [1072, 1094], 1117, 1119⟩, ⟨1080, [], 1103, 1105⟩, ⟨1080, [1102], 1125, 1127⟩,
    ⟨1130, [1152, 1174], 1197, 1199⟩, ⟨1130, [1152, 1174, 1196], 1219, 1221⟩]
  probePort := fun _ => 0
  clockPort := fun _ => 0
  reportPort := fun _ => 1

theorem actionSearch_sound : actionSearch.Sound 0 1250 (fun _ => 968) where
  roleProbe := by intro κ; fin_cases κ <;> rfl
  roleGate := by intro κ; fin_cases κ <;> rfl
  reportOrder := by
    intro j κ
    fin_cases j <;> fin_cases κ <;> simp [actionSearch]
  parentOrder := by
    intro j κ π b
    fin_cases j <;> fin_cases κ <;> simp [actionSearch] <;> rintro rfl _ <;> decide
  first := by intro κ; fin_cases κ <;> norm_num [actionSearch]
  spaced := by intro κ; fin_cases κ <;> norm_num [actionSearch, Spaced]
  clock := by intro κ; fin_cases κ <;> norm_num [actionSearch]
  trained := by intro κ; fin_cases κ <;> norm_num [actionSearch]
  wait := by intro κ; fin_cases κ <;> norm_num [actionSearch]
  after := by
    intro κ π b
    fin_cases κ <;> simp [actionSearch] <;> rintro rfl _ <;> norm_num

/-- The nodes reached for the need `m`. -/
def actionReached (m : ℕ) : Fin 7 → Bool :=
  ![true, decide (m ≤ 2), decide (2 < m), decide (m ≤ 2) && decide (m ≤ 1),
    decide (m ≤ 2) && decide (1 < m), decide (2 < m) && decide (m ≤ 3),
    decide (2 < m) && decide (3 < m)]

theorem actionSearch_consistent (m : ℕ) :
    actionSearch.Consistent (actionReached m) (fun _ => m) := by
  intro κ
  fin_cases κ <;> simp [actionSearch, actionReached, Question.count]

/-- For a need from 1 to 4, the lesson reached is the lesson of that
need, and its question has that many training pulses. -/
theorem action_selected {m : ℕ} (lo : 1 ≤ m) (hi : m ≤ 4) (κ : Fin 7) (leaf : 3 ≤ κ.val) :
    actionReached m κ = decide (κ.val = m + 2) ∧
      (κ.val = m + 2 → (actionSearch.plan κ).count = m) := by
  interval_cases m <;> fin_cases κ <;> simp [actionSearch, actionReached, Question.count] at leaf ⊢

/-- A binary search that ends by a lesson, with fourteen explicit cells.
Every probe has its own start gain, anywhere within 3/125 of the centre
of the band of need `m`. For every need `m` from 1 to 4, the network has
a complete run, and in every complete run:

- the learner of node `m + 2` receives its lesson of `m + 1` pulses, its
  gain ends exactly `m` doses higher, and it fires in its report window;
- the three other learners receive no pulse from the network, keep
  their gain and never fire.

The FIRE dates and the final values are the same in every complete
run. -/
theorem search_action_witness (m : ℕ) (lo : 1 ≤ m) (hi : m ≤ 4) (z : Fin 7 → ℝ)
    (band : ∀ κ, |z κ - needCentre 1 (1 / 20) m| ≤ 3 / 125) :
    ∃ (dates : Fin 14 → List ℝ) (u : Fin 14 → Snapshot 1),
      (∀ κ : Fin 7, κ.val = m + 2 →
        Signal ((actionSearch.plan κ).read - 1) ((actionSearch.plan κ).read + 1)
          (dates (actionSearch.probe κ)) true ∧
        (u (actionSearch.probe κ)).x 0 (.z 0) = z κ + m * (8 * (2 / 25 - 59 / 800)) ∧
        incoming (signalRoute actionSearch.lo actionSearch.hi actionSearch.inputs) dates
          (actionSearch.probe κ) =
          ((questionPulses 0 (actionSearch.plan κ).first (actionSearch.plan κ).dates
            (actionSearch.plan κ).read : List (Delivery 1)) : Multiset (Delivery 1)) ∧
        (questionPulses 0 (actionSearch.plan κ).first (actionSearch.plan κ).dates
          (actionSearch.plan κ).read).length = m + 1) ∧
      (∀ κ : Fin 7, 3 ≤ κ.val → κ.val ≠ m + 2 →
        dates (actionSearch.probe κ) = [] ∧
        (u (actionSearch.probe κ)).x 0 (.z 0) = z κ ∧
        incoming (signalRoute actionSearch.lo actionSearch.hi actionSearch.inputs) dates
          (actionSearch.probe κ) = 0) ∧
      (∃ ref : ParameterExecution
        (familyParameters (fun (_ : Fin 14) (_ : Fin 1) => witnessParameters))
        (signalRoute actionSearch.lo actionSearch.hi actionSearch.inputs)
        (Snapshot.family 0 (actionSearch.start (fun κ => probeAt (z κ)) (fun _ => witnessSource)))
        (Snapshot.family 1250 u), ParameterCompleteThrough ref 1250) ∧
      ∀ {w : Snapshot 14} (ex : ParameterExecution
        (familyParameters (fun (_ : Fin 14) (_ : Fin 1) => witnessParameters))
        (signalRoute actionSearch.lo actionSearch.hi actionSearch.inputs)
        (Snapshot.family 0 (actionSearch.start (fun κ => probeAt (z κ)) (fun _ => witnessSource)))
        w), ParameterCompleteThrough ex 1250 →
        (∀ i, ex.emissionTimes i = dates i) ∧ ∀ i c, w.x i c = (u i).x 0 c := by
  obtain ⟨dates, u, yes, _, silent, gains, sent, ref, all⟩ :=
    trained_search (by norm_num : 0 < 14) actionSearch actionSearch_sound
      (actionSearch_consistent m) (θp := fun _ _ => witnessParameters)
      (θg := fun _ _ => witnessParameters) (sp := fun κ => probeAt (z κ))
      (sg := fun _ => witnessSource) (fun κ => probeCell_band m (band κ))
      (fun _ => openCell_witness) (fun _ => rfl) (fun _ => rfl)
  have same : (fun j => SearchLayout.pick (fun (_ : Fin 7) (_ : Fin 1) => witnessParameters)
      (fun _ _ => witnessParameters) (actionSearch.role j)) =
      fun (_ : Fin 14) (_ : Fin 1) => witnessParameters := by
    funext j
    cases actionSearch.role j <;> rfl
  rw [same] at ref all
  have child (κ : Fin 7) (leaf : 3 ≤ κ.val) :
      ∃ π b, actionSearch.parent κ = some (π, b) := by
    fin_cases κ <;> simp [actionSearch] at leaf ⊢
  refine ⟨dates, u, fun κ hκ => ?_, fun κ leaf other => ?_, ref, all⟩
  · obtain ⟨reached, count⟩ := action_selected lo hi κ (by omega)
    have here : actionReached m κ = true := by rw [reached]; simpa using hκ
    obtain ⟨π, b, hp⟩ := child κ (by omega)
    have signal := yes κ
    have gain := gains κ
    have pulses := sent κ π b hp
    rw [here] at signal gain pulses
    rw [count hκ] at signal gain
    simp only [reduceIte] at gain pulses
    refine ⟨by simpa using signal, ?_, pulses, ?_⟩
    · have steps : min (m + 1) m = m := by omega
      rw [steps] at gain
      exact gain
    · rw [questionPulses_length]
      have c := count hκ
      unfold Question.count at c
      omega
  · obtain ⟨reached, _⟩ := action_selected lo hi κ leaf
    have away : actionReached m κ = false := by rw [reached]; simpa using other
    obtain ⟨π, b, hp⟩ := child κ leaf
    have gain := gains κ
    have pulses := sent κ π b hp
    rw [away] at gain pulses
    simp only [Bool.false_eq_true, reduceIte, Nat.cast_zero, zero_mul, add_zero] at gain pulses
    exact ⟨silent κ away, gain, pulses⟩

end RecursiveLearning.Native
