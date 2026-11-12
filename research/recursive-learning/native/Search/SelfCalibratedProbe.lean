import Training.TrainingLoop

/-! A count probe that calibrates itself. The hidden need of a port is the
number of doses its gain must receive before a pulse makes the cell fire.
It is a property of the cell: its start gain, its dose and its FIRE level.
No birth gain is placed on a lattice. A train of pulses followed by a read
pulse reports whether the count of training pulses reaches that need. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The port needs `m` doses: below `m` doses no pulse fires, and from `m`
doses on every pulse fires, whatever the rest charge within `10⁻⁴` above
1/10. -/
def NeedIs (level dose z₀ : ℝ) (m : ℕ) : Prop :=
  (∀ k : ℕ, k < m → ∀ c, 1 / 10 ≤ c → c ≤ 1 / 10 + 1 / 10000 →
    ¬ PulseFires c (Real.exp (z₀ + k * dose)) level) ∧
  (∀ k : ℕ, m ≤ k → ∀ c, 1 / 10 ≤ c → c ≤ 1 / 10 + 1 / 10000 →
    PulseFires c (Real.exp (z₀ + k * dose)) level)

theorem NeedIs.shift {level dose z₀ : ℝ} {m : ℕ} (h : NeedIs level dose z₀ (m + 1)) :
    NeedIs level dose (z₀ + dose) m := by
  have form (k : ℕ) : z₀ + dose + k * dose = z₀ + ((k + 1 : ℕ) : ℝ) * dose := by
    push_cast
    ring
  refine ⟨fun k hk c lo hi => ?_, fun k hk c lo hi => ?_⟩
  · rw [form]
    exact h.1 (k + 1) (by omega) c lo hi
  · rw [form]
    exact h.2 (k + 1) (by omega) c lo hi

/-- The need follows from two inequalities on the gain ladder. The gain
one dose below the need stays under the FIRE level with the largest rest
charge, and the gain at the need reaches it from the exact rest charge.
The start gains excluded are those within `10⁻⁴` of a firing boundary. -/
theorem needIs_of_peaks {level dose z₀ : ℝ} {m : ℕ} (dosePos : 0 ≤ dose)
    (below : ∀ k : ℕ, k + 1 = m →
      1 / 10 + 1 / 10000 + Real.exp (z₀ + k * dose) * response 1 < level)
    (above : level ≤ 1 / 10 + Real.exp (z₀ + m * dose) * response 1) :
    NeedIs level dose z₀ m := by
  have hPos := response_one_pos
  refine ⟨fun k hk c lo hi => ?_, fun k hk c lo _ => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, j + 1 = m := ⟨m - 1, by omega⟩
    rintro ⟨τ, hτ, reach⟩
    rw [readyPulse_from] at reach
    have decay := decay_upper (show c - 1 / 10 ≤ 1 / 10000 by linarith) (by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) hτ.1
    have rise := response_strictMono_pulse.monotoneOn hτ
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) hτ.2
    have order : Real.exp (z₀ + k * dose) ≤ Real.exp (z₀ + j * dose) := by
      apply Real.exp_le_exp.mpr
      have steps : (k : ℝ) ≤ j := by exact_mod_cast (by omega : k ≤ j)
      nlinarith [mul_le_mul_of_nonneg_right steps dosePos]
    have drive := mul_le_mul order rise (response_nonnegative hτ.1) (Real.exp_pos _).le
    linarith [below j rfl]
  · apply pulseFires_of_peak lo
    have order : Real.exp (z₀ + m * dose) ≤ Real.exp (z₀ + k * dose) := by
      apply Real.exp_le_exp.mpr
      have steps : (m : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [mul_le_mul_of_nonneg_right steps dosePos]
    have grow := mul_le_mul_of_nonneg_right order hPos.le
    linarith

/-- With a known need, a train of `n` pulses writes exactly `min n m`
doses, and every other pulse fires. -/
theorem Trained.counts {level dose : ℝ} {n f : ℕ} {q₀ z₀ q z : ℝ}
    (h : Trained level dose n f q₀ z₀ q z) :
    ∀ m : ℕ, NeedIs level dose z₀ m → 1 / 10 ≤ q₀ → q₀ ≤ 1 / 10 + 1 / 10000 →
      z = z₀ + ((min n m : ℕ) : ℝ) * dose ∧ f = n - min n m := by
  induction h with
  | done q z =>
    intro m _ _ _
    simp
  | @silent n f q₀ z₀ q₁ q z quiet band rest ih =>
    intro m need lo hi
    rcases m with _ | m
    · have fires := need.2 0 le_rfl q₀ lo hi
      simp only [Nat.cast_zero, zero_mul, add_zero] at fires
      exact absurd fires quiet
    · obtain ⟨hz, hf⟩ := ih m need.shift band.1 band.2
      refine ⟨?_, by rw [Nat.succ_min_succ]; omega⟩
      rw [hz, Nat.succ_min_succ]
      push_cast
      ring
  | @fire n f q₀ z₀ q z fired rest ih =>
    intro m need lo hi
    rcases m with _ | m
    · obtain ⟨hz, hf⟩ := ih 0 need le_rfl (by norm_num)
      refine ⟨?_, by simp at hf ⊢; omega⟩
      rw [hz]
      simp
    · have quiet := need.1 0 (by omega) q₀ lo hi
      simp only [Nat.cast_zero, zero_mul, add_zero] at quiet
      exact absurd fired quiet

/-- A self-calibrated count probe. A port of a rested cell needs `m`
doses before it fires. It receives `n` training pulses and then one read
pulse. The read pulse makes the cell fire exactly when `m ≤ n`. The need
is not encoded in a birth gain: it is the number of doses that the cell's
own start gain, dose and FIRE level require. Every complete run has the
same end state and the same number of FIRE events. -/
theorem self_calibrated_probe_exists {θ ε p upper lower level} {dates : List ℝ}
    {s : Snapshot 1} {read rest : ℝ} {m : ℕ} (box : @PhysicalBox 1 θ ε)
    (config : PortConfig θ p upper lower level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25) (exit : 1 / 200 ≤ lower ∧ lower < upper)
    (state : RestState θ s) (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending = (⟨0, p, s.time⟩ : Delivery 1) ::
      (dates.map (fun D => (⟨0, p, D⟩ : Delivery 1)) ++ [(⟨0, p, read⟩ : Delivery 1)]))
    (spaced : Spaced s.time dates read) (wait : read + 22 ≤ rest)
    (need : NeedIs level (8 * (upper - lower)) (s.x 0 (.z p)) m) :
    let n := dates.length + 1
    ∃ (mid u : Snapshot 1) (report : ℕ),
      Runs θ s mid (n - min n m) ∧ mid.time = read ∧ Runs θ mid u report ∧
      (report = 1 ↔ m ≤ n) ∧ (report = 0 ↔ n < m) ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = [] ∧
      u.x 0 (.z p) = s.x 0 (.z p) + ((min (n + 1) m : ℕ) : ℝ) * (8 * (upper - lower)) ∧
      (∀ q ≠ p, u.x 0 (.z q) = s.x 0 (.z q)) ∧
      ∀ (v : Snapshot 1) (other : ParameterExecution θ (fun _ _ => []) s v),
        ParameterCompleteThrough other rest →
        u.ObservationalEq v ∧ other.emissions.length = n - min n m + report := by
  intro n
  obtain ⟨mid, f, run, rested, date, pend, others, b, trained⟩ :=
    training_loop_exists box config fire entry exit dates s read
      [(⟨0, p, read⟩ : Delivery 1)] state recovery queue spaced
      (by intro d hd; rw [List.mem_singleton.mp hd])
  obtain ⟨gain, count⟩ := trained.counts m need state.charge.1 state.charge.2
  rw [count] at run
  obtain ⟨u, restedEnd, dateEnd, pendEnd, othersEnd, _, outcome⟩ :=
    training_step_exists (later := []) (rest := rest) box config fire entry exit rested
      (by rw [b]; exact recovery) (by rw [pend, date]) (by rw [date]; exact wait)
      (by intro d hd; cases hd)
  have unique (report : ℕ) (last : Runs θ mid u report) :
      ∀ (v : Snapshot 1) (other : ParameterExecution θ (fun _ _ => []) s v),
        ParameterCompleteThrough other rest →
        u.ObservationalEq v ∧ other.emissions.length = n - min n m + report :=
    fun v other complete => rest_run_unique box config fire state (run.append last) restedEnd
      pendEnd other (dateEnd ▸ complete)
  by_cases reach : m ≤ n
  · have fires := need.2 (min n m) (by omega) (mid.x 0 .q) rested.charge.1 rested.charge.2
    rw [← gain] at fires
    rcases outcome with ⟨quiet, _, _⟩ | ⟨_, last, same, _⟩
    · exact absurd fires quiet
    · refine ⟨mid, u, 1, run, date, last, ⟨fun _ => reach, fun _ => rfl⟩,
        ⟨fun h => absurd h (by norm_num), fun h => absurd reach (not_le.mpr h)⟩,
        restedEnd, dateEnd, pendEnd, ?_,
        fun q hq => (othersEnd q hq).trans (others q hq), unique 1 last⟩
      have steps : min (n + 1) m = min n m := by omega
      rw [same, gain, steps]
  · have quiet := need.1 (min n m) (by omega) (mid.x 0 .q) rested.charge.1 rested.charge.2
    rw [← gain] at quiet
    rcases outcome with ⟨_, last, learned⟩ | ⟨fires, _, _, _⟩
    · refine ⟨mid, u, 0, run, date, last,
        ⟨fun h => absurd h (by norm_num), fun h => absurd h reach⟩,
        ⟨fun _ => not_le.mp reach, fun _ => rfl⟩, restedEnd, dateEnd, pendEnd, ?_,
        fun q hq => (othersEnd q hq).trans (others q hq), unique 0 last⟩
      have steps : min (n + 1) m = min n m + 1 := by omega
      rw [learned, gain, steps, Nat.cast_add, Nat.cast_one]
      ring
    · exact absurd fires quiet

end RecursiveLearning.Native
