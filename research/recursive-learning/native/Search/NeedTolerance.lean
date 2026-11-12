import Search.TrainedSearch

/-! The need of a probe, from fabrication tolerances.

The search assumes that every probe has the same need `m`. Here that
hypothesis follows from a tolerance. The start gain of a probe is placed
at the centre of the band of need `m` of a nominal design. A real probe
keeps the need `m` when the errors on its start gain, its dose and its
FIRE level are small enough. The error on the dose counts `m` times. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The log-gain that just reaches the FIRE level from the rest charge. -/
noncomputable def firingLogGain (level : ℝ) : ℝ := Real.log ((level - 1 / 10) / response 1)

/-- The centre of the band of need `m`: half a dose above the start gain
that would reach the FIRE level after exactly `m` doses. -/
noncomputable def needCentre (level dose : ℝ) (m : ℕ) : ℝ :=
  firingLogGain level - (m - 1 / 2) * dose

/-- A shift of the FIRE level by `ℓ` moves the firing log-gain by at most
`20/17 ℓ`. -/
theorem firingLogGain_shift {level level₀ ℓ : ℝ} (fire : 19 / 20 ≤ level)
    (fire₀ : 19 / 20 ≤ level₀) (close : |level - level₀| ≤ ℓ) :
    |firingLogGain level - firingLogGain level₀| ≤ 20 / 17 * ℓ := by
  have rPos := response_one_pos
  obtain ⟨lo, hi⟩ := abs_le.mp close
  have one (x y : ℝ) (hx : 17 / 20 ≤ x) (hy : 17 / 20 ≤ y) (near : x - y ≤ ℓ) :
      Real.log (x / response 1) - Real.log (y / response 1) ≤ 20 / 17 * ℓ := by
    have xPos : 0 < x := by linarith
    have yPos : 0 < y := by linarith
    rw [Real.log_div xPos.ne' rPos.ne', Real.log_div yPos.ne' rPos.ne']
    have ratio := Real.log_le_sub_one_of_pos (div_pos xPos yPos)
    rw [Real.log_div xPos.ne' yPos.ne'] at ratio
    have bound : x / y - 1 ≤ 20 / 17 * ℓ := by
      rw [div_sub_one yPos.ne', div_le_iff₀ yPos]
      have wide : 0 ≤ ℓ := (abs_nonneg _).trans close
      nlinarith
    linarith
  unfold firingLogGain
  exact abs_le.mpr
    ⟨by linarith [one (level₀ - 1 / 10) (level - 1 / 10) (by linarith) (by linarith) (by linarith)],
      one (level - 1 / 10) (level₀ - 1 / 10) (by linarith) (by linarith) (by linarith)⟩

/-- The need of a probe from tolerances. A nominal design has the FIRE
level `level₀` and the dose `d₀`. The real probe has its start gain
within `a` of the centre of the band of need `m`, its dose within `b` of
`d₀` and its FIRE level within `ℓ` of `level₀`. If

`a + m b + 20/17 ℓ + 1/8000 < d₀ / 2`

then the probe needs exactly `m` doses. The error on the dose is counted
once for each dose. -/
theorem needIs_of_tolerance {level level₀ dose d₀ z₀ a b ℓ : ℝ} {m : ℕ}
    (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀) (dosePos : 0 ≤ dose)
    (gain : |z₀ - needCentre level₀ d₀ m| ≤ a) (doseTol : |dose - d₀| ≤ b)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + m * b + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedIs level dose z₀ m := by
  have rPos := response_one_pos
  obtain ⟨gLo, gHi⟩ := abs_le.mp gain
  obtain ⟨dLo, dHi⟩ := abs_le.mp doseTol
  obtain ⟨sLo, sHi⟩ := abs_le.mp (firingLogGain_shift fire fire₀ levelTol)
  have bPos : 0 ≤ b := (abs_nonneg _).trans doseTol
  unfold needCentre at gLo gHi
  apply needIs_of_peaks dosePos
  · intro k hk
    have mk : (m : ℝ) = k + 1 := by rw [← hk]; push_cast; ring
    have steps : (k : ℝ) * dose ≤ k * (d₀ + b) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)
    have kb : (0 : ℝ) ≤ k * b := mul_nonneg (Nat.cast_nonneg k) bPos
    rw [mk] at room gHi
    -- The silence bound, with the largest rest charge.
    have xPos : (0 : ℝ) < level - 1 / 10 - 1 / 10000 := by linarith
    have gap : firingLogGain level -
        Real.log ((level - 1 / 10 - 1 / 10000) / response 1) ≤ 1 / 8000 := by
      unfold firingLogGain
      rw [Real.log_div (by linarith) rPos.ne', Real.log_div xPos.ne' rPos.ne']
      have ratio := Real.log_le_sub_one_of_pos
        (div_pos (show (0 : ℝ) < level - 1 / 10 by linarith) xPos)
      rw [Real.log_div (by linarith) xPos.ne'] at ratio
      have bound : (level - 1 / 10) / (level - 1 / 10 - 1 / 10000) - 1 ≤ 1 / 8000 := by
        rw [div_sub_one xPos.ne', div_le_iff₀ xPos]
        linarith
      linarith
    have under : z₀ + k * dose < Real.log ((level - 1 / 10 - 1 / 10000) / response 1) := by
      nlinarith
    have grow := Real.exp_lt_exp.mpr under
    rw [Real.exp_log (div_pos xPos rPos)] at grow
    have scaled := mul_lt_mul_of_pos_right grow rPos
    rw [div_mul_cancel₀ _ rPos.ne'] at scaled
    linarith
  · have steps : (m : ℝ) * (d₀ - b) ≤ m * dose :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg m)
    have reachGain : firingLogGain level ≤ z₀ + m * dose := by nlinarith
    have xPos : (0 : ℝ) < level - 1 / 10 := by linarith
    have grow := Real.exp_le_exp.mpr reachGain
    unfold firingLogGain at grow
    rw [Real.exp_log (div_pos xPos rPos)] at grow
    have scaled := mul_le_mul_of_nonneg_right grow rPos.le
    rw [div_mul_cancel₀ _ rPos.ne'] at scaled
    linarith

/-! ### The binary search with start gains off the lattice -/

/-- A rested probe cell with the start log-gain `z` on every port. -/
noncomputable def probeAt (z : ℝ) : Snapshot 1 where
  time := 0
  x := fun _ c => match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z _ => z
    | .b => 2 / 25
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := []

/-- The explicit cell is a probe of need `m` for every start gain within
3/125 of the centre of the band of need `m`. The band is 6/125 wide and
the dose is 1/20. -/
theorem probeCell_band (m : ℕ) {z : ℝ} (band : |z - needCentre 1 (1 / 20) m| ≤ 3 / 125) :
    ProbeCell (fun _ => witnessParameters) (1 / 10) (probeAt z) 0 (2 / 25) (59 / 800) 1 m := by
  have c := trainedCell_witness
  have rPos := response_one_pos
  have rLow := response_one_lower
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
        show z ≤ Real.log 4
        have gPos : (0 : ℝ) < (1 - 1 / 10) / response 1 := div_pos (by norm_num) rPos
        have small : (1 - 1 / 10) / response 1 ≤ 18 / 11 := by
          rw [div_le_iff₀ rPos]
          linarith
        have top := Real.log_le_sub_one_of_pos gPos
        have four := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 by norm_num)
        have steps : (0 : ℝ) ≤ m * (1 / 20) := by positivity
        have hi := (abs_le.mp band).2
        unfold needCentre firingLogGain at hi
        norm_num at four
        linarith }
    recovery := by show (7 / 100 : ℝ) ≤ 2 / 25 ∧ (2 / 25 : ℝ) ≤ 1 / 10; norm_num
    need := by
      show NeedIs 1 (8 * (2 / 25 - 59 / 800)) z m
      rw [dose]
      exact needIs_of_tolerance (level₀ := 1) (d₀ := 1 / 20) (a := 3 / 125) (b := 0) (ℓ := 0)
        (by norm_num) (by norm_num) (by norm_num) band (by norm_num) (by norm_num)
        (by norm_num) }

/-- A binary search over the needs 1 to 4, with six explicit cells and
start gains off the lattice. Each of the three probes has its own start
gain, anywhere within 3/125 of the centre of the band of need `m`. For
every need `m`, in every complete run:

- the root probe fires in its report window exactly when `m ≤ 2`, and
  the root gate fires late exactly when `2 < m`;
- the probe of node 1 fires in its window exactly when `m ≤ 1`, and its
  gate fires late exactly when `m = 2`;
- the probe of node 2 fires in its window exactly when `m = 3`, and its
  gate fires late exactly when `3 < m`.

The pair of answers separates the needs 1, 2, 3 and 4 or more. -/
theorem trained_search_band_witness (m : ℕ) (z : Fin 3 → ℝ)
    (band : ∀ κ, |z κ - needCentre 1 (1 / 20) m| ≤ 3 / 125) :
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
        (Snapshot.family 0 (searchWitness.start (fun κ => probeAt (z κ)) (fun _ => witnessSource)))
        u), ParameterCompleteThrough ref 1150) ∧
      ∀ {u : Snapshot 6} (ex : ParameterExecution
        (familyParameters (fun (_ : Fin 6) (_ : Fin 1) => witnessParameters))
        (signalRoute searchWitness.lo searchWitness.hi searchWitness.inputs)
        (Snapshot.family 0 (searchWitness.start (fun κ => probeAt (z κ)) (fun _ => witnessSource)))
        u), ParameterCompleteThrough ex 1150 → ∀ i, ex.emissionTimes i = dates i := by
  obtain ⟨dates, _, yes, no, _, _, _, ref, all⟩ :=
    trained_search (by norm_num : 0 < 6) searchWitness searchWitness_sound
      (searchWitness_consistent m) (θp := fun _ _ => witnessParameters)
      (θg := fun _ _ => witnessParameters) (sp := fun κ => probeAt (z κ))
      (sg := fun _ => witnessSource) (fun κ => probeCell_band m (band κ))
      (fun _ => openCell_witness) (fun _ => rfl) (fun _ => rfl)
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
