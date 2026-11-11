import SignalNetwork
import SelfCalibratedProbe

/-! The two cells of a search by questions, each described alone.

A probe cell answers one question about its hidden need. It receives a
train of pulses and a read pulse, or nothing at all. A gate cell turns
the silence of a probe into a FIRE. It is a trained cell read by a clock
pulse, with or without the report of the probe: with the report it fires
early, without it it fires late. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

theorem quiet_times {θ : Fin 1 → Parameters} {s u : Snapshot 1}
    (e : ParameterExecution θ (fun _ _ => []) s u) (h : e.emissions.length = 0) :
    e.emissionTimes 0 = [] := by
  simp [ParameterExecution.emissionTimes, List.length_eq_zero_iff.mp h]

/-! ### The probe cell -/

/-- The pulses of one question: a first training pulse, the later
training pulses and the read pulse, all on the port `p`. -/
def lesson (p : Port) (first : ℝ) (dates : List ℝ) (read : ℝ) : List (Delivery 1) :=
  (⟨0, p, first⟩ : Delivery 1) ::
    (dates.map (fun D => (⟨0, p, D⟩ : Delivery 1)) ++ [(⟨0, p, read⟩ : Delivery 1)])

/-- A probe cell: a rested cell whose port `p` needs `m` doses before a
pulse makes the cell fire. The need is a property of its start gain, its
dose and its FIRE level. Its queue is empty. -/
structure ProbeCell (θ : Fin 1 → Parameters) (ε : ℝ) (s : Snapshot 1) (p : Port)
    (upper lower level : ℝ) (m : ℕ) : Prop where
  box : @PhysicalBox 1 θ ε
  config : PortConfig θ p upper lower level
  fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20
  entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25
  exit : 1 / 200 ≤ lower ∧ lower < upper
  state : RestState θ s
  recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10
  need : NeedIs level (8 * (upper - lower)) (s.x 0 (.z p)) m

/-- A probe cell that is asked. It receives `dates.length + 1` training
pulses and one read pulse. It fires on the read pulse exactly when its
need is at most the number of training pulses. That FIRE comes within
one unit after the read pulse. Every FIRE of training comes more than one
unit before the read pulse. The cell ends at rest. -/
theorem ProbeCell.asked {θ ε s p upper lower level m}
    (cell : ProbeCell θ ε s p upper lower level m) {first read rest : ℝ} {dates : List ℝ}
    (start : s.time ≤ first) (spaced : Spaced first dates (read - 1)) (wait : read + 22 ≤ rest) :
    ∃ (u : Snapshot 1) (l : List ℝ) (count : ℕ),
      Reach θ (requeued s (lesson p first dates read)) u l count ∧ RestState θ u ∧
      u.time = rest ∧ u.pending = [] ∧
      Signal (read - 1) (read + 1) l (decide (m ≤ dates.length + 1)) := by
  have far := Spaced.horizon_later spaced
  obtain ⟨w₀, ⟨e₀, quiet₀⟩, rested₀, date₀, pend₀, gains₀, b₀, _⟩ :=
    rest_wait (s := requeued s (lesson p first dates read)) cell.config cell.fire.1
      (cell.state.requeued _) start (by
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact le_rfl
        · rcases List.mem_append.mp hd with hm | hr
          · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hm
            have next := Spaced.later spaced D hD
            show first ≤ D
            linarith
          · obtain rfl := List.mem_singleton.mp hr
            show first ≤ read
            linarith)
  obtain ⟨mid, f, ⟨e₁, _⟩, rested₁, date₁, pend₁, _, b₁, trained⟩ :=
    training_loop_exists cell.box cell.config cell.fire cell.entry cell.exit dates w₀ (read - 1)
      [(⟨0, p, read⟩ : Delivery 1)] rested₀ (by rw [b₀]; exact cell.recovery)
      (by rw [pend₀, date₀]; rfl) (by rw [date₀]; exact spaced)
      (by
        intro d hd
        obtain rfl := List.mem_singleton.mp hd
        show read - 1 ≤ read
        linarith)
  have need₀ : NeedIs level (8 * (upper - lower)) (w₀.x 0 (.z p)) m := by
    rw [gains₀]
    exact cell.need
  obtain ⟨gain, _⟩ := trained.counts m need₀ rested₀.charge.1 rested₀.charge.2
  obtain ⟨w₁, ⟨e₂, quiet₂⟩, rested₂, date₂, pend₂, gains₂, b₂, _⟩ :=
    rest_wait (T := read) cell.config cell.fire.1 rested₁ (by rw [date₁]; linarith) (by
      rw [pend₁]
      intro d hd
      obtain rfl := List.mem_singleton.mp hd
      exact le_rfl)
  have queue₂ : w₁.pending = (⟨0, p, w₁.time⟩ : Delivery 1) :: [] := by rw [pend₂, pend₁, date₂]
  have recov₂ : 7 / 100 ≤ w₁.x 0 .b ∧ w₁.x 0 .b ≤ 1 / 10 := by
    rw [b₂, b₁, b₀]
    exact cell.recovery
  have early : ∀ t ∈ e₁.emissionTimes 0, t ≤ read - 1 :=
    fun t ht => date₁ ▸ emissionTimes_le e₁ 0 t ht
  have z₂ : w₁.x 0 (.z p) =
      s.x 0 (.z p) + ((min (dates.length + 1) m : ℕ) : ℝ) * (8 * (upper - lower)) := by
    rw [gains₂, gain, gains₀]
    rfl
  by_cases reach : m ≤ dates.length + 1
  · have fires := cell.need.2 (min (dates.length + 1) m) (by omega) (w₁.x 0 .q)
      rested₂.charge.1 rested₂.charge.2
    rw [← z₂] at fires
    obtain ⟨u, tf, ⟨e₃, emitted⟩, late, before, _, _, restedEnd, dateEnd, pendEnd, _⟩ :=
      firing_step_dated (later := []) (rest := rest) cell.box cell.config cell.fire cell.entry
        cell.exit rested₂ recov₂ queue₂ (by rw [date₂]; exact wait) (by intro d hd; cases hd)
        (pulseFires_iff.mpr fires)
    rw [date₂] at late before
    refine ⟨u, e₁.emissionTimes 0 ++ [tf], _, ⟨e₀.append (e₁.append (e₂.append e₃)), ?_, rfl⟩,
      restedEnd, dateEnd, pendEnd,
      Or.inl ⟨by simp [reach], _, tf, rfl, early, by linarith, before⟩⟩
    rw [emissionTimes_append, emissionTimes_append, emissionTimes_append, quiet_times e₀ quiet₀,
      quiet_times e₂ quiet₂]
    simp [ParameterExecution.emissionTimes, emitted]
  · have quiet := cell.need.1 (min (dates.length + 1) m) (by omega) (w₁.x 0 .q)
      rested₂.charge.1 rested₂.charge.2
    rw [← z₂] at quiet
    obtain ⟨u, restedEnd, dateEnd, pendEnd, _, _, outcome⟩ :=
      training_step_exists (later := []) (rest := rest) cell.box cell.config cell.fire cell.entry
        cell.exit rested₂ recov₂ queue₂ (by rw [date₂]; exact wait) (by intro d hd; cases hd)
    rcases outcome with ⟨_, ⟨e₃, quiet₃⟩, _⟩ | ⟨fires, _⟩
    · refine ⟨u, e₁.emissionTimes 0, _, ⟨e₀.append (e₁.append (e₂.append e₃)), ?_, rfl⟩,
        restedEnd, dateEnd, pendEnd, Or.inr ⟨by simp [reach], early⟩⟩
      rw [emissionTimes_append, emissionTimes_append, emissionTimes_append,
        quiet_times e₀ quiet₀, quiet_times e₂ quiet₂, quiet_times e₃ quiet₃]
      simp
    · exact absurd fires quiet

/-- A probe cell that is not asked receives nothing, stays at rest and
never fires. -/
theorem ProbeCell.idle {θ ε s p upper lower level m}
    (cell : ProbeCell θ ε s p upper lower level m) {rest : ℝ} (later : s.time ≤ rest) :
    ∃ (u : Snapshot 1) (count : ℕ),
      Reach θ (requeued s []) u [] count ∧ RestState θ u ∧ u.time = rest ∧ u.pending = [] := by
  obtain ⟨u, ⟨e, quiet⟩, rested, date, pend, _⟩ :=
    rest_wait (s := requeued s []) cell.config cell.fire.1 (cell.state.requeued _) later
      (by intro d hd; cases hd)
  exact ⟨u, _, ⟨e, quiet_times e quiet, rfl⟩, rested, date, pend⟩

/-! ### The gate cell -/

/-- A gain that was silent one dose lower stays under the FIRE level at
`exp(-1/20)` times the peak of its response. -/
theorem trained_port_low {level z d : ℝ} (dose : d ≤ 1 / 20)
    (silent : ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
      ¬ PulseFires c (Real.exp (z - d)) level) :
    1 / 10 + Real.exp z * (Real.exp (-(1 / 20 : ℝ)) * response 1) < level := by
  obtain ⟨c, hc, _, quiet⟩ := silent
  have below : 1 / 10 + Real.exp (z - d) * response 1 < level := by
    by_contra h
    exact quiet (pulseFires_of_peak hc (not_lt.mp h))
  rw [sub_eq_add_neg, Real.exp_add] at below
  have decay : Real.exp (-(1 / 20 : ℝ)) ≤ Real.exp (-d) := Real.exp_le_exp.mpr (by linarith)
  have weaker : Real.exp z * (Real.exp (-(1 / 20 : ℝ)) * response 1) ≤
      Real.exp z * Real.exp (-d) * response 1 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left decay (Real.exp_pos z).le) response_one_pos.le
  linarith

/-- A trained cell read by one pulse, on its first trained port. The
cell fires once, later than 0.355 units after the pulse and within one
unit of it. Two read pulses together make it fire before 0.256 units, so
the date of the FIRE tells whether the second pulse was there. -/
theorem OpenCell.read_one {θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂}
    (cell : OpenCell θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂)
    {ρ rest : ℝ} (late : horizon ≤ ρ) (wait : ρ + 22 ≤ rest) :
    ∃ (u : Snapshot 1) (tf : ℝ) (training : List ℝ) (count : ℕ),
      ρ + 71 / 200 < tf ∧ tf ≤ ρ + 1 ∧
      Reach θ (requeued s (s.pending ++ [(⟨0, p₁, ρ⟩ : Delivery 1)])) u (training ++ [tf]) count ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = [] ∧ ∀ t ∈ training, t ≤ horizon := by
  obtain ⟨w, e₁, early, rested, date, pend, charge, recov, fires₁, _, silent₁, _⟩ :=
    cell.trained (tail := [(⟨0, p₁, ρ⟩ : Delivery 1)]) late
      (by intro d hd; rw [List.mem_singleton.mp hd])
  obtain ⟨u, tf, ⟨e₂, emitted⟩, start, before, hit, _, restedEnd, dateEnd, pendEnd, _⟩ :=
    firing_step_dated (later := []) (rest := rest) cell.box cell.config₁ cell.fire cell.entry₁
      cell.exit₁ rested recov (by rw [pend, date]) (by rw [date]; exact wait)
      (by intro d hd; cases hd) (pulseFires_iff.mpr (by rw [charge]; exact fires₁))
  have low := trained_port_low cell.dose₁ silent₁
  rw [charge, readyPulse_rest] at hit
  have lower : Real.exp (-(1 / 20 : ℝ)) * response 1 < response (tf - w.time) := by
    have scaled : Real.exp (w.x 0 (.z p₁)) * (Real.exp (-(1 / 20 : ℝ)) * response 1) <
        Real.exp (w.x 0 (.z p₁)) * response (tf - w.time) := by linarith
    exact lt_of_mul_lt_mul_left scaled (Real.exp_pos _).le
  have after : w.time + 71 / 200 < tf := by
    by_contra h
    have short : tf - w.time ≤ 71 / 200 := by linarith [not_lt.mp h]
    have mono := response_strictMono_pulse.monotoneOn
      (show tf - w.time ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
      (show (71 / 200 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, by norm_num⟩) short
    linarith [window_alone]
  rw [date] at after before
  refine ⟨u, tf, e₁.emissionTimes 0, _, after, before, ⟨e₁.append e₂, ?_, rfl⟩, restedEnd,
    dateEnd, pendEnd, early⟩
  rw [emissionTimes_append]
  congr 1
  simp [ParameterExecution.emissionTimes, emitted]

/-- A trained cell that receives no read pulse. It ends at rest, and
every FIRE of its training comes before `horizon`. -/
theorem OpenCell.idle {θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂}
    (cell : OpenCell θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂)
    {rest : ℝ} (late : horizon ≤ rest) :
    ∃ (u : Snapshot 1) (training : List ℝ) (count : ℕ),
      Reach θ (requeued s (s.pending ++ [])) u training count ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = [] ∧ ∀ t ∈ training, t ≤ horizon := by
  obtain ⟨w, e, early, rested, date, pend, _⟩ :=
    cell.trained (tail := []) late (by intro d hd; cases hd)
  exact ⟨w, _, _, ⟨e, rfl, rfl⟩, rested, date, pend, early⟩

end RecursiveLearning.Native
