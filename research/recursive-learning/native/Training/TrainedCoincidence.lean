import Training.JointRead
import Coincidence.ParameterExecutionProduct

/-! The coincidence decision of two trained cells. Each cell trains two
ports until it stops by itself, then reads them. A receiver compares the
two read FIRE dates. No gain and no FIRE level is set by hand. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- One cell of the experiment: its thresholds, its rested start, its two
pulse trains and its two read pulses. The start gains do not fire, each
dose is at most 1/20, and each train is long enough for training to stop. -/
structure TrainedCell (θ : Fin 1 → Parameters) (ε : ℝ) (s : Snapshot 1)
    (p₁ p₂ : Port) (u₁ l₁ u₂ l₂ level : ℝ) (dates₁ dates₂ : List ℝ)
    (middle read₁ read₂ rest : ℝ) (r₁ r₂ : ℕ) : Prop where
  box : @PhysicalBox 1 θ ε
  distinct : p₁ ≠ p₂
  config₁ : PortConfig θ p₁ u₁ l₁ level
  config₂ : PortConfig θ p₂ u₂ l₂ level
  fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20
  entry₁ : 7 / 100 ≤ u₁ ∧ u₁ ≤ 2 / 25
  exit₁ : 1 / 200 ≤ l₁ ∧ l₁ < u₁
  entry₂ : 7 / 100 ≤ u₂ ∧ u₂ ≤ 2 / 25
  exit₂ : 1 / 200 ≤ l₂ ∧ l₂ < u₂
  dose₁ : 8 * (u₁ - l₁) ≤ 1 / 20
  dose₂ : 8 * (u₂ - l₂) ≤ 1 / 20
  state : RestState θ s
  recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10
  queue : s.pending = (⟨0, p₁, s.time⟩ : Delivery 1) ::
    (dates₁.map (fun D => (⟨0, p₁, D⟩ : Delivery 1)) ++
      (⟨0, p₂, middle⟩ : Delivery 1) ::
        (dates₂.map (fun D => (⟨0, p₂, D⟩ : Delivery 1)) ++
          [(⟨0, p₁, read₁⟩ : Delivery 1), (⟨0, p₂, read₂⟩ : Delivery 1)]))
  spaced₁ : Spaced s.time dates₁ middle
  spaced₂ : Spaced middle dates₂ read₁
  order : read₁ ≤ read₂ ∧ read₂ ≤ read₁ + 1 / 4
  wait : read₁ + 22 ≤ rest
  below₁ : ¬ PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₁))) level
  below₂ : ¬ PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₂))) level
  reach₁ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₁) + r₁ * (8 * (u₁ - l₁))) * response 1
  reach₂ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₂) + r₂ * (8 * (u₂ - l₂))) * response 1
  enough₁ : 2 * r₁ + 2 ≤ dates₁.length + 1
  enough₂ : 2 * r₂ + 2 ≤ dates₂.length + 1

/-- The complete local run of one trained cell, with its read FIRE date. -/
theorem TrainedCell.run {θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle read₁ read₂ rest r₁ r₂}
    (cell : TrainedCell θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle read₁ read₂ rest r₁ r₂) :
    ∃ (u : Snapshot 1) (tf : ℝ) (training : List ℝ)
      (e : ParameterExecution θ (fun _ _ => []) s u),
      read₁ + 239 / 1000 < tf ∧ tf ≤ read₂ + 32 / 125 ∧
      e.emissionTimes 0 = training ++ [tf] ∧ ParameterCompleteThrough e rest := by
  obtain ⟨u, tf, training, after, before, ⟨e, times⟩, rested, date, pend, _, _, _⟩ :=
    trained_read_exists cell.box cell.distinct cell.config₁ cell.config₂ cell.fire cell.entry₁
      cell.exit₁ cell.entry₂ cell.exit₂ cell.dose₁ cell.dose₂ cell.state cell.recovery cell.queue
      cell.spaced₁ cell.spaced₂ cell.order cell.wait cell.below₁ cell.below₂ r₁ r₂ cell.reach₁
      cell.reach₂ cell.enough₁ cell.enough₂
  exact ⟨u, tf, training, e, after, before, times,
    date ▸ rested.complete cell.config₁ cell.fire.1 e pend⟩

/-- The receiver accepts when the two read FIRE dates are closer than
3/20. With the second read pulse of each cell at most 1/10 after the
first, it accepts exactly when the two cells are read at the same date. -/
theorem trained_dates_decide {readL₁ readL₂ readR₁ readR₂ tfL tfR offset : ℝ}
    (leftAfter : readL₁ + 239 / 1000 < tfL) (leftBefore : tfL ≤ readL₂ + 32 / 125)
    (rightAfter : readR₁ + 239 / 1000 < tfR) (rightBefore : tfR ≤ readR₂ + 32 / 125)
    (leftOrder : readL₁ ≤ readL₂ ∧ readL₂ ≤ readL₁ + 1 / 10)
    (rightOrder : readR₁ ≤ readR₂ ∧ readR₂ ≤ readR₁ + 1 / 10)
    (schedule : readR₁ = readL₁ + offset)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10) :
    |tfR - tfL| < 3 / 20 ↔ offset = 0 := by
  constructor
  · intro close
    obtain ⟨lo, hi⟩ := abs_lt.mp close
    rcases offsets with h | h | h
    · exfalso; linarith
    · exact h
    · exfalso; linarith
  · intro zero
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The coincidence decision of two trained cells, for every complete
run of the two-cell network. Each cell has its own parameters in the
fabrication box, its own start gains and its own FIRE level between
19/20 and 21/20. In every complete run, each cell's last FIRE is its read
FIRE at the date of its local run, and the two dates are closer than 3/20
exactly when the two cells are read at the same date. -/
theorem trained_coincidence_network {θL θR : Fin 1 → Parameters} {ε : ℝ}
    {sL sR : Snapshot 1} {pL₁ pL₂ pR₁ pR₂ : Port}
    {uL₁ lL₁ uL₂ lL₂ levelL uR₁ lR₁ uR₂ lR₂ levelR : ℝ}
    {datesL₁ datesL₂ datesR₁ datesR₂ : List ℝ}
    {middleL readL₁ readL₂ middleR readR₁ readR₂ rest offset : ℝ} {rL₁ rL₂ rR₁ rR₂ : ℕ}
    (left : TrainedCell θL ε sL pL₁ pL₂ uL₁ lL₁ uL₂ lL₂ levelL datesL₁ datesL₂
      middleL readL₁ readL₂ rest rL₁ rL₂)
    (right : TrainedCell θR ε sR pR₁ pR₂ uR₁ lR₁ uR₂ lR₂ levelR datesR₁ datesR₂
      middleR readR₁ readR₂ rest rR₁ rR₂)
    (start : sL.time = sR.time)
    (staggerL : readL₂ ≤ readL₁ + 1 / 10) (staggerR : readR₂ ≤ readR₁ + 1 / 10)
    (schedule : readR₁ = readL₁ + offset)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10) :
    ∃ (tfL tfR : ℝ) (trainingL trainingR : List ℝ),
      (∃ (u : Snapshot 2) (ref : ParameterExecution (extendParameters θL (θR 0)) (fun _ _ => [])
        (sL.independentPair sR) u), ParameterCompleteThrough ref rest) ∧
      ∀ {u : Snapshot 2} (ex : ParameterExecution (extendParameters θL (θR 0)) (fun _ _ => [])
        (sL.independentPair sR) u), ParameterCompleteThrough ex rest →
        ex.emissionTimes 0 = trainingL ++ [tfL] ∧ ex.emissionTimes 1 = trainingR ++ [tfR] ∧
        (|tfR - tfL| < 3 / 20 ↔ offset = 0) := by
  obtain ⟨uL, tfL, trainingL, eL, afterL, beforeL, timesL, doneL⟩ := left.run
  obtain ⟨uR, tfR, trainingR, eR, afterR, beforeR, timesR, doneR⟩ := right.run
  obtain ⟨ref, l, r⟩ := eL.independentPair eR start (doneL.1.trans doneR.1.symm)
  have complete := doneL.independentPair doneR ref
  have box : PhysicalBox (extendParameters θL (θR 0)) ε := by
    refine ⟨left.box.1, ?_⟩
    intro i p
    fin_cases i
    · exact left.box.2 0 p
    · exact right.box.2 0 p
  have bL := cell_threshold_bounds left.config₁.cell left.fire
  have bR := cell_threshold_bounds right.config₁.cell right.fire
  have bounds : ParameterThresholdBounds (extendParameters θL (θR 0)) := by
    constructor
    · intro i; fin_cases i; exact bL.fire 0; exact bR.fire 0
    · intro i; fin_cases i; exact bL.fastEnd 0; exact bR.fastEnd 0
    · intro i; fin_cases i; exact bL.fastBelowFire 0; exact bR.fastBelowFire 0
    · intro i; fin_cases i; exact bL.reopen 0; exact bR.reopen 0
    · intro i p; fin_cases i; exact bL.mark 0 p; exact bR.mark 0 p
    · intro i p; fin_cases i; exact bL.silent 0 p; exact bR.silent 0 p
    · intro i p; fin_cases i; exact bL.error 0 p; exact bR.error 0 p
    · intro i p; fin_cases i; exact bL.auxReady 0 p; exact bR.auxReady 0 p
  have iL := left.state.physical
  have iR := right.state.physical
  have birth : ParameterPhysicalInvariant (extendParameters θL (θR 0))
      (sL.independentPair sR) := by
    constructor
    · intro i; fin_cases i; exact iL.charge 0; exact iR.charge 0
    · intro i p; fin_cases i; exact iL.sensor 0 p; exact iR.sensor 0 p
    · intro i p; fin_cases i; exact iL.gain 0 p; exact iR.gain 0 p
    · intro i; fin_cases i; exact iL.recovery 0; exact iR.recovery 0
    · intro i; fin_cases i; exact iL.reserve 0; exact iR.reserve 0
  refine ⟨tfL, tfR, trainingL, trainingR, ⟨_, ref, complete⟩, ?_⟩
  intro u ex done
  refine ⟨?_, ?_, trained_dates_decide afterL beforeL afterR beforeR
    ⟨left.order.1, staggerL⟩ ⟨right.order.1, staggerR⟩ schedule offsets⟩
  · rw [ex.emissionTimes_unique ref box bounds birth done complete 0, l, timesL]
  · rw [ex.emissionTimes_unique ref box bounds birth done complete 1, r, timesR]

/-! ### The hypotheses are satisfiable -/

/-- A train of `n` dates, 22 units apart, after `start`. -/
noncomputable def train (start : ℝ) : ℕ → List ℝ
  | 0 => []
  | n + 1 => (start + 22) :: train (start + 22) n

theorem train_length (start : ℝ) (n : ℕ) : (train start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [train, ih]

theorem train_spaced (start : ℝ) (n : ℕ) (H : ℝ) (h : start + 22 * ((n : ℝ) + 1) ≤ H) :
    Spaced start (train start n) H := by
  induction n generalizing start with
  | zero =>
    show start + 22 ≤ H
    simpa using h
  | succ n ih =>
    refine ⟨le_rfl, ih (start + 22) ?_⟩
    push_cast at h
    linarith

theorem inBox_self {N : ℝ} (h : 0 ≤ N) : InRelativeBox (1 / 10) N N := by
  constructor <;> linarith

/-- A nominal cell with a low ERROR entry threshold and a dose of 1/20
on every port. -/
noncomputable def witnessParameters : Parameters where
  cap := fun _ => 4
  lm := fun _ => Real.log (5 / 4) / (1 / 50)
  ls := fun _ => Real.log 8 / (53 / 50)
  le := fun _ => a / (3 / 20)
  inputGain := fun _ => (1 - 1 / 40) / response (1 / 50)
  thresholds := { error := fun _ => 2 / 25, auxReady := fun _ => 59 / 800 }

/-- A rested cell at gain 6/5 on every port, with two trains of 22 pulses
and two read pulses at the same date. -/
noncomputable def witnessStart : Snapshot 1 where
  time := 0
  x := fun _ c => match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z _ => Real.log (6 / 5)
    | .b => 2 / 25
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := (⟨0, 0, 0⟩ : Delivery 1) ::
    ((train 0 21).map (fun D => (⟨0, 0, D⟩ : Delivery 1)) ++
      (⟨0, 1, 484⟩ : Delivery 1) ::
        ((train 484 21).map (fun D => (⟨0, 1, D⟩ : Delivery 1)) ++
          [(⟨0, 0, 968⟩ : Delivery 1), (⟨0, 1, 968⟩ : Delivery 1)]))

/-- The hypotheses of the trained cell hold for an explicit cell and an
explicit schedule. The theorems above are therefore not vacuous. -/
theorem trainedCell_witness :
    TrainedCell (fun _ => witnessParameters) (1 / 10) witnessStart 0 1
      (2 / 25) (59 / 800) (2 / 25) (59 / 800) 1 (train 0 21) (train 484 21) 484 968 968 990
      10 10 := by
  have apos : 0 < a := by linarith [a_coarse_bounds.1]
  have config (p : Port) :
      PortConfig (fun _ => witnessParameters) p (2 / 25) (59 / 800) 1 :=
    ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl,
      fun _ => ⟨by show (0 : ℝ) < 59 / 800; norm_num,
        by show (59 / 800 : ℝ) ≤ 2 / 25; norm_num, by show (2 / 25 : ℝ) < 1; norm_num⟩⟩
  have gain : Real.exp (Real.log (6 / 5 : ℝ)) = 6 / 5 := Real.exp_log (by norm_num)
  have below : ¬ PulseFires (1 / 10) (Real.exp (Real.log (6 / 5 : ℝ))) 1 := by
    rintro ⟨τ, hτ, reach⟩
    rw [readyPulse_at_rest, gain] at reach
    have cap := response_uniform_upper hτ.1
    linarith
  have reach : (1 : ℝ) ≤ 1 / 10 + Real.exp (Real.log (6 / 5 : ℝ) +
      ((10 : ℕ) : ℝ) * (8 * (2 / 25 - 59 / 800))) * response 1 := by
    have dose : ((10 : ℕ) : ℝ) * (8 * (2 / 25 - 59 / 800 : ℝ)) = 1 / 2 := by norm_num
    rw [dose, Real.exp_add, gain]
    have half : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have product := mul_le_mul (mul_le_mul_of_nonneg_left half (by norm_num : (0 : ℝ) ≤ 6 / 5))
      response_one_lower (by norm_num) (by positivity)
    linarith
  exact {
    box := ⟨Or.inr rfl, fun _ _ =>
      ⟨inBox_self (by norm_num),
        inBox_self (div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)),
        inBox_self (div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)),
        inBox_self (div_nonneg apos.le (by norm_num)),
        inBox_self (div_nonneg (by norm_num) (response_nonnegative (by norm_num)))⟩⟩
    distinct := by decide
    config₁ := config 0
    config₂ := config 1
    fire := ⟨by norm_num, by norm_num⟩
    entry₁ := ⟨by norm_num, by norm_num⟩
    exit₁ := ⟨by norm_num, by norm_num⟩
    entry₂ := ⟨by norm_num, by norm_num⟩
    exit₂ := ⟨by norm_num, by norm_num⟩
    dose₁ := by norm_num
    dose₂ := by norm_num
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
        show Real.log (6 / 5 : ℝ) ≤ Real.log 4
        exact Real.log_le_log (by norm_num) (by norm_num) }
    recovery := by show (7 / 100 : ℝ) ≤ 2 / 25 ∧ (2 / 25 : ℝ) ≤ 1 / 10; norm_num
    queue := rfl
    spaced₁ := train_spaced 0 21 484 (by norm_num)
    spaced₂ := train_spaced 484 21 968 (by norm_num)
    order := ⟨le_rfl, by norm_num⟩
    wait := by norm_num
    below₁ := below
    below₂ := below
    reach₁ := reach
    reach₂ := reach
    enough₁ := by rw [train_length]
    enough₂ := by rw [train_length] }

/-- Two copies of the explicit cell, read at the same date, satisfy the
network contract: every complete run of the pair is accepted. -/
theorem trained_coincidence_witness :
    ∃ (tfL tfR : ℝ) (trainingL trainingR : List ℝ),
      (∃ (u : Snapshot 2) (ref : ParameterExecution
        (extendParameters (fun _ => witnessParameters) witnessParameters) (fun _ _ => [])
        (witnessStart.independentPair witnessStart) u), ParameterCompleteThrough ref 990) ∧
      ∀ {u : Snapshot 2} (ex : ParameterExecution
        (extendParameters (fun _ => witnessParameters) witnessParameters) (fun _ _ => [])
        (witnessStart.independentPair witnessStart) u), ParameterCompleteThrough ex 990 →
        ex.emissionTimes 0 = trainingL ++ [tfL] ∧ ex.emissionTimes 1 = trainingR ++ [tfR] ∧
        |tfR - tfL| < 3 / 20 := by
  obtain ⟨tfL, tfR, trainingL, trainingR, ref, all⟩ :=
    trained_coincidence_network (offset := 0) trainedCell_witness trainedCell_witness rfl
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl rfl))
  refine ⟨tfL, tfR, trainingL, trainingR, ref, ?_⟩
  intro u ex done
  obtain ⟨l, r, decide⟩ := all ex done
  exact ⟨l, r, decide.mpr rfl⟩

end RecursiveLearning.Native
