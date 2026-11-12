import Training.FiringStep

/-! The training loop. Each pulse of a train either stays below the FIRE
level and writes one dose, or reaches it and writes nothing. With enough
pulses the gain stops at a value that fires from the exact rest charge. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

theorem response_one_lower : 11 / 20 ≤ response 1 := by
  have expBound : Real.exp (-(1 / 2 : ℝ)) ∈ Icc (606530 / 1000000 : ℝ) 1 :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  unfold response
  rw [mul_one, mul_one, exp_neg_a]
  have h := mul_le_mul response_ratio_bounds.1 (sub_le_sub_right expBound.1 (1 / 4))
    (by norm_num) (by linarith [response_ratio_bounds.1])
  linarith

/-- A pulse at `gain` from the rest charge `charge` reaches `level`. -/
def PulseFires (charge gain level : ℝ) : Prop :=
  ∃ τ ∈ Icc (0 : ℝ) 1, level ≤ readyPulse charge gain 0 τ

theorem readyPulse_shift (charge gain start t : ℝ) :
    readyPulse charge gain start t = readyPulse charge gain 0 (t - start) := by
  simp [readyPulse]

theorem pulseFires_iff {charge gain level start : ℝ} :
    (∃ t ∈ Icc start (start + 1), level ≤ readyPulse charge gain start t) ↔
      PulseFires charge gain level := by
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t - start, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by rwa [← readyPulse_shift]⟩
  · rintro ⟨τ, hτ, h⟩
    refine ⟨start + τ, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩, ?_⟩
    rw [readyPulse_shift, add_sub_cancel_left]
    exact h

theorem not_pulseFires {charge gain level : ℝ} (start : ℝ)
    (h : ¬ PulseFires charge gain level) :
    ∀ t ∈ Icc start (start + 1), readyPulse charge gain start t < level := by
  intro t ht
  by_contra hn
  exact h (pulseFires_iff.mp ⟨t, ht, not_lt.mp hn⟩)

theorem pulseFires_of_peak {charge gain level : ℝ} (hc : 1 / 10 ≤ charge)
    (peak : level ≤ 1 / 10 + gain * response 1) : PulseFires charge gain level := by
  refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
  have decay := mul_nonneg (sub_nonneg.mpr hc) (Real.exp_pos (-(1 / 2) * (1 - 0))).le
  simp only [readyPulse, sub_zero] at decay ⊢
  linarith

/-- A silent pulse leaves room for one more dose under the gain cap. -/
theorem silent_room {charge z level upper lower : ℝ} (hc : 1 / 10 ≤ charge)
    (fire : level ≤ 21 / 20) (bounds : 1 / 200 ≤ lower ∧ lower < upper ∧ upper ≤ 2 / 25)
    (silent : ¬ PulseFires charge (Real.exp z) level) :
    Real.exp (z + 8 * (upper - lower)) ≤ 7 / 2 := by
  have below : 1 / 10 + Real.exp z * response 1 < level := by
    by_contra h
    exact silent (pulseFires_of_peak hc (not_lt.mp h))
  have drive := mul_le_mul_of_nonneg_left response_one_lower (Real.exp_pos z).le
  have gain : Real.exp z ≤ 19 / 11 := by linarith
  have two : Real.exp (3 / 5 : ℝ) ∈ Icc (0 : ℝ) 2 :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  have dose : Real.exp (8 * (upper - lower)) ≤ 2 :=
    (Real.exp_le_exp.mpr (by linarith [bounds.1, bounds.2.2])).trans two.2
  rw [Real.exp_add]
  have product := mul_le_mul gain dose (Real.exp_pos _).le (by norm_num)
  linarith

/-- One training pulse on a rested cell, whatever its gain. -/
theorem training_step_exists {θ ε s p upper lower level rest} {later : List (Delivery 1)}
    (box : @PhysicalBox 1 θ ε)
    (config : PortConfig θ p upper lower level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25) (exit : 1 / 200 ≤ lower ∧ lower < upper)
    (state : RestState θ s) (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending = (⟨0, p, s.time⟩ : Delivery 1) :: later)
    (wait : s.time + 22 ≤ rest) (laterDue : ∀ d ∈ later, rest ≤ d.due) :
    ∃ u, RestState θ u ∧ u.time = rest ∧
      u.pending = later ∧ (∀ q ≠ p, u.x 0 (.z q) = s.x 0 (.z q)) ∧ u.x 0 .b = s.x 0 .b ∧
      ((¬ PulseFires (s.x 0 .q) (Real.exp (s.x 0 (.z p))) level ∧ Runs θ s u 0 ∧
          u.x 0 (.z p) = s.x 0 (.z p) + 8 * (upper - lower)) ∨
        (PulseFires (s.x 0 .q) (Real.exp (s.x 0 (.z p))) level ∧ Runs θ s u 1 ∧
          u.x 0 (.z p) = s.x 0 (.z p) ∧ u.x 0 .q = 1 / 10)) := by
  by_cases h : PulseFires (s.x 0 .q) (Real.exp (s.x 0 (.z p))) level
  · obtain ⟨u, run, rested, date, pend, gains, b, charge⟩ :=
      firing_step_exists box config fire entry exit state recovery queue wait laterDue
        (pulseFires_iff.mpr h)
    exact ⟨u, rested, date, pend, fun q _ => gains q, b, Or.inr ⟨h, run, gains p, charge⟩⟩
  · obtain ⟨u, run, rested, date, pend, learned, others, b⟩ :=
      silent_step_exists box config fire entry exit state queue wait laterDue
        (not_pulseFires s.time h)
        (silent_room state.charge.1 fire.2 ⟨exit.1, exit.2, entry.2⟩ h)
    exact ⟨u, rested, date, pend, others, b, Or.inl ⟨h, run, learned⟩⟩

/-- The effect of a train of pulses on the rest charge and the log-gain
of the pulsed port. The indices are the number of pulses and the number
of those that fired. A firing pulse leaves the exact rest charge. -/
inductive Trained (level dose : ℝ) : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → Prop
  | done (q z : ℝ) : Trained level dose 0 0 q z q z
  | silent {n f : ℕ} {q₀ z₀ q₁ q z : ℝ} (quiet : ¬ PulseFires q₀ (Real.exp z₀) level)
      (band : 1 / 10 ≤ q₁ ∧ q₁ ≤ 1 / 10 + 1 / 10000)
      (rest : Trained level dose n f q₁ (z₀ + dose) q z) :
      Trained level dose (n + 1) f q₀ z₀ q z
  | fire {n f : ℕ} {q₀ z₀ q z : ℝ} (fired : PulseFires q₀ (Real.exp z₀) level)
      (rest : Trained level dose n f (1 / 10) z₀ q z) :
      Trained level dose (n + 1) (1 + f) q₀ z₀ q z

/-- Each pulse either fires or writes one dose. -/
theorem Trained.gain {level dose : ℝ} {n f : ℕ} {q₀ z₀ q z : ℝ}
    (h : Trained level dose n f q₀ z₀ q z) : ∃ k : ℕ, k + f = n ∧ z = z₀ + k * dose := by
  induction h with
  | done q z => exact ⟨0, rfl, by simp⟩
  | silent quiet band rest ih =>
    obtain ⟨k, hk, e⟩ := ih
    exact ⟨k + 1, by omega, by rw [e]; push_cast; ring⟩
  | fire fired rest ih =>
    obtain ⟨k, hk, e⟩ := ih
    exact ⟨k, by omega, e⟩

/-- Once a pulse fires from the exact rest charge, every later pulse
fires and the gain stays. -/
theorem Trained.stable {level dose : ℝ} {n f : ℕ} {q₀ z₀ q z : ℝ}
    (h : Trained level dose n f q₀ z₀ q z) (exact : q₀ = 1 / 10)
    (fires : PulseFires q₀ (Real.exp z₀) level) : q = 1 / 10 ∧ z = z₀ := by
  induction h with
  | done q z => exact ⟨exact, rfl⟩
  | silent quiet band rest ih => exact absurd fires quiet
  | fire fired rest ih => exact ih rfl (exact ▸ fires)

/-- With enough pulses the training stops: the final gain fires from the
exact rest charge. `r` bounds the number of doses needed to reach a gain
that always fires. -/
theorem Trained.stops {level dose Z : ℝ} {n f : ℕ} {q₀ z₀ q z : ℝ}
    (limit : ∀ c w, 1 / 10 ≤ c → Z ≤ w → PulseFires c (Real.exp w) level)
    (h : Trained level dose n f q₀ z₀ q z) :
    ∀ r : ℕ, Z ≤ z₀ + r * dose → 1 / 10 ≤ q₀ →
      ((q₀ = 1 / 10 ∧ 2 * r + 1 ≤ n) ∨ 2 * r + 2 ≤ n) →
      q = 1 / 10 ∧ PulseFires (1 / 10) (Real.exp z) level := by
  induction h with
  | done q z =>
    intro r _ _ count
    rcases count with ⟨_, c⟩ | c <;> omega
  | @silent n f q₀ z₀ q₁ q z quiet band rest ih =>
    intro r reach charge count
    rcases r with _ | r
    · exact absurd (limit q₀ z₀ charge (by simpa using reach)) quiet
    · refine ih r ?_ band.1 (Or.inr (by rcases count with ⟨_, c⟩ | c <;> omega))
      push_cast at reach
      linarith
  | @fire n f q₀ z₀ q z fired rest ih =>
    intro r reach charge count
    rcases count with ⟨exact, c⟩ | c
    · obtain ⟨hq, hz⟩ := rest.stable rfl (exact ▸ fired)
      exact ⟨hq, by rw [hz]; exact exact ▸ fired⟩
    · exact ih r reach le_rfl (Or.inl ⟨rfl, by omega⟩)

/-- Unless no dose was written, the gain one dose below the final one
was silent from some rest charge in the band. -/
theorem Trained.last_silent {level dose : ℝ} {n f : ℕ} {q₀ z₀ q z : ℝ}
    (h : Trained level dose n f q₀ z₀ q z) (band₀ : 1 / 10 ≤ q₀ ∧ q₀ ≤ 1 / 10 + 1 / 10000) :
    z = z₀ ∨ ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
      ¬ PulseFires c (Real.exp (z - dose)) level := by
  induction h with
  | done q z => exact Or.inl rfl
  | @silent n f q₀ z₀ q₁ q z quiet band rest ih =>
    rcases ih band with e | found
    · exact Or.inr ⟨q₀, band₀.1, band₀.2, by rw [e, add_sub_cancel_right]; exact quiet⟩
    · exact Or.inr found
  | fire fired rest ih => exact ih ⟨le_rfl, by norm_num⟩

/-- Pulse dates at least 22 units apart, the last one at least 22 units
before the horizon. -/
def Spaced (start : ℝ) : List ℝ → ℝ → Prop
  | [], horizon => start + 22 ≤ horizon
  | D :: rest, horizon => start + 22 ≤ D ∧ Spaced D rest horizon

theorem Spaced.later {horizon : ℝ} : ∀ {dates : List ℝ} {start : ℝ},
    Spaced start dates horizon → ∀ D ∈ dates, start + 22 ≤ D
  | [], _, _, D, hD => by cases hD
  | D₀ :: rest, start, h, D, hD => by
    rcases List.mem_cons.mp hD with rfl | hmem
    · exact h.1
    · have next := Spaced.later h.2 D hmem
      linarith [h.1]

theorem Spaced.horizon_later {horizon : ℝ} : ∀ {dates : List ℝ} {start : ℝ},
    Spaced start dates horizon → start + 22 ≤ horizon
  | [], _, h => h
  | _ :: _, _, h => by
    have next := Spaced.horizon_later h.2
    linarith [h.1]

/-- A train of training pulses on one port, as an execution. Every pulse
is accounted for: it is silent and writes one dose, or it fires and
writes nothing. -/
theorem training_loop_exists {θ ε p upper lower level}
    (box : @PhysicalBox 1 θ ε)
    (config : PortConfig θ p upper lower level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25) (exit : 1 / 200 ≤ lower ∧ lower < upper) :
    ∀ (dates : List ℝ) (s : Snapshot 1) (horizon : ℝ) (tail : List (Delivery 1)),
      RestState θ s → 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10 →
      s.pending = (⟨0, p, s.time⟩ : Delivery 1) ::
        (dates.map (fun D => (⟨0, p, D⟩ : Delivery 1)) ++ tail) →
      Spaced s.time dates horizon → (∀ d ∈ tail, horizon ≤ d.due) →
      ∃ u f, Runs θ s u f ∧ RestState θ u ∧
        u.time = horizon ∧ u.pending = tail ∧ (∀ q ≠ p, u.x 0 (.z q) = s.x 0 (.z q)) ∧
        u.x 0 .b = s.x 0 .b ∧
        Trained level (8 * (upper - lower)) (dates.length + 1) f (s.x 0 .q) (s.x 0 (.z p))
          (u.x 0 .q) (u.x 0 (.z p)) := by
  intro dates
  induction dates with
  | nil =>
    intro s horizon tail state recovery queue spaced tailDue
    obtain ⟨u, rested, date, pend, others, b, outcome⟩ :=
      training_step_exists (later := tail) box config fire entry exit state recovery queue spaced
        tailDue
    rcases outcome with ⟨quiet, run, learned⟩ | ⟨fired, run, same, charge⟩
    · refine ⟨u, 0, run, rested, date, pend, others, b, ?_⟩
      rw [learned]
      exact .silent quiet rested.charge (.done _ _)
    · refine ⟨u, 1 + 0, run, rested, date, pend, others, b, ?_⟩
      rw [same, charge]
      exact .fire fired (.done _ _)
  | cons D ds ih =>
    intro s horizon tail state recovery queue spaced tailDue
    obtain ⟨u, rested, date, pend, others, b, outcome⟩ :=
      training_step_exists (rest := D)
        (later := (⟨0, p, D⟩ : Delivery 1) ::
          (ds.map (fun D => (⟨0, p, D⟩ : Delivery 1)) ++ tail))
        box config fire entry exit state recovery queue spaced.1
        (by
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hm
          · exact le_rfl
          · rcases List.mem_append.mp hm with hmap | htail
            · obtain ⟨D', hD', rfl⟩ := List.mem_map.mp hmap
              have next := Spaced.later spaced.2 D' hD'
              show D ≤ D'
              linarith
            · have last := Spaced.horizon_later spaced.2
              have due := tailDue d htail
              linarith)
    obtain ⟨v, f, next, rested', date', pend', others', b', trained⟩ :=
      ih u horizon tail rested (by rw [b]; exact recovery) (by rw [pend, date])
        (by rw [date]; exact spaced.2) tailDue
    rcases outcome with ⟨quiet, run, learned⟩ | ⟨fired, run, same, charge⟩
    · refine ⟨v, 0 + f, run.append next, rested', date', pend',
        fun q hq => (others' q hq).trans (others q hq), b'.trans b, ?_⟩
      rw [learned] at trained
      rw [zero_add]
      exact .silent quiet rested.charge trained
    · refine ⟨v, 1 + f, run.append next, rested', date', pend',
        fun q hq => (others' q hq).trans (others q hq), b'.trans b, ?_⟩
      rw [same, charge] at trained
      exact .fire fired trained

/-- A rested cell with an empty queue has no move left at its date. -/
theorem RestState.complete {θ : Fin 1 → Parameters} {p upper lower level} {s u : Snapshot 1}
    (config : PortConfig θ p upper lower level)
    (fire : 19 / 20 ≤ level) (e : ParameterExecution θ (fun _ _ => []) s u)
    (rested : RestState θ u) (empty : u.pending = []) : ParameterCompleteThrough e u.time := by
  refine ⟨rfl, ?_, by simp [empty]⟩
  apply u.no_parameter_jump
  · apply port_guards config rested.main (by linarith [rested.charge.2])
    intro q
    simp only [rested.aux q]
    exact lt_of_le_of_lt (rested.sensors q).2 (by norm_num)
  · simp [empty]
  · intro i q o h
    rw [Subsingleton.elim i 0, rested.raw q] at h
    cases h

/-- Every complete run from a rested cell agrees with a constructed run
that ends at rest with an empty queue: same final state and same number
of FIRE events. -/
theorem rest_run_unique {θ ε p upper lower level} {s u v : Snapshot 1} {n : ℕ}
    (box : @PhysicalBox 1 θ ε)
    (config : PortConfig θ p upper lower level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (start : RestState θ s) (run : Runs θ s u n) (rested : RestState θ u)
    (empty : u.pending = []) (other : ParameterExecution θ (fun _ _ => []) s v)
    (complete : ParameterCompleteThrough other u.time) :
    u.ObservationalEq v ∧ other.emissions.length = n := by
  obtain ⟨e, count⟩ := run
  have h := ParameterExecution.observational_unique box
    (low_threshold_bounds config fire) e other start.physical
    (rested.complete config fire.1 e empty) complete
  exact ⟨h.1, by rw [← h.2.length_eq, count]⟩

/-- Training that stops by itself, for any start gain. `r` doses bring
the gain to a value that always fires, and the train has at least
`2 r + 2` pulses. The final gain fires from the exact rest charge. Unless
no dose was written, the gain one dose below it was silent. The run has
`f` FIRE events and wrote `k` doses, one or the other for each pulse.
Every run complete through the horizon ends in the same state with the
same number of FIRE events. -/
theorem stop_training_exists {θ ε p upper lower level} {dates : List ℝ} {s : Snapshot 1}
    {horizon : ℝ} {tail : List (Delivery 1)} (box : @PhysicalBox 1 θ ε)
    (config : PortConfig θ p upper lower level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry : 7 / 100 ≤ upper ∧ upper ≤ 2 / 25) (exit : 1 / 200 ≤ lower ∧ lower < upper)
    (state : RestState θ s) (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending = (⟨0, p, s.time⟩ : Delivery 1) ::
      (dates.map (fun D => (⟨0, p, D⟩ : Delivery 1)) ++ tail))
    (spaced : Spaced s.time dates horizon) (tailDue : ∀ d ∈ tail, horizon ≤ d.due) (r : ℕ)
    (reach : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p) + r * (8 * (upper - lower))) * response 1)
    (enough : 2 * r + 2 ≤ dates.length + 1) :
    ∃ u f, Runs θ s u f ∧ RestState θ u ∧
      u.time = horizon ∧ u.pending = tail ∧ (∀ q ≠ p, u.x 0 (.z q) = s.x 0 (.z q)) ∧
      u.x 0 .b = s.x 0 .b ∧ u.x 0 .q = 1 / 10 ∧
      (∃ k : ℕ, k + f = dates.length + 1 ∧
        u.x 0 (.z p) = s.x 0 (.z p) + k * (8 * (upper - lower))) ∧
      PulseFires (1 / 10) (Real.exp (u.x 0 (.z p))) level ∧
      (u.x 0 (.z p) = s.x 0 (.z p) ∨ ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
        ¬ PulseFires c (Real.exp (u.x 0 (.z p) - 8 * (upper - lower))) level) ∧
      (tail = [] → ∀ (v : Snapshot 1) (other : ParameterExecution θ (fun _ _ => []) s v),
        ParameterCompleteThrough other horizon →
        u.ObservationalEq v ∧ other.emissions.length = f) := by
  obtain ⟨u, f, run, rested, date, pend, others, b, trained⟩ :=
    training_loop_exists box config fire entry exit dates s horizon tail state recovery queue
      spaced tailDue
  have limit : ∀ c w, 1 / 10 ≤ c → s.x 0 (.z p) + r * (8 * (upper - lower)) ≤ w →
      PulseFires c (Real.exp w) level := by
    intro c w hc hw
    apply pulseFires_of_peak hc
    have grow := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hw) response_one_pos.le
    linarith
  obtain ⟨charge, fires⟩ := trained.stops limit r le_rfl state.charge.1 (Or.inr enough)
  refine ⟨u, f, run, rested, date, pend, others, b, charge, trained.gain, fires,
    trained.last_silent state.charge, ?_⟩
  intro none v other complete
  exact rest_run_unique box config fire state run rested (pend.trans none) other
    (date ▸ complete)

/-- Two ports of one cell, trained one after the other. Each port has its
own realized ERROR thresholds, so its own dose. Both final gains fire
from the exact rest charge, and each is at most one dose above a silent
gain unless no dose was written on it. Every complete run agrees with
the constructed one. -/
theorem two_port_training_exists {θ ε p₁ p₂ u₁ l₁ u₂ l₂ level}
    {dates₁ dates₂ : List ℝ} {s : Snapshot 1} {middle horizon : ℝ} {tail : List (Delivery 1)}
    (box : @PhysicalBox 1 θ ε) (distinct : p₁ ≠ p₂)
    (config₁ : PortConfig θ p₁ u₁ l₁ level) (config₂ : PortConfig θ p₂ u₂ l₂ level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry₁ : 7 / 100 ≤ u₁ ∧ u₁ ≤ 2 / 25) (exit₁ : 1 / 200 ≤ l₁ ∧ l₁ < u₁)
    (entry₂ : 7 / 100 ≤ u₂ ∧ u₂ ≤ 2 / 25) (exit₂ : 1 / 200 ≤ l₂ ∧ l₂ < u₂)
    (state : RestState θ s) (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending = (⟨0, p₁, s.time⟩ : Delivery 1) ::
      (dates₁.map (fun D => (⟨0, p₁, D⟩ : Delivery 1)) ++
        (⟨0, p₂, middle⟩ : Delivery 1) ::
          (dates₂.map (fun D => (⟨0, p₂, D⟩ : Delivery 1)) ++ tail)))
    (spaced₁ : Spaced s.time dates₁ middle) (spaced₂ : Spaced middle dates₂ horizon)
    (tailDue : ∀ d ∈ tail, horizon ≤ d.due) (r₁ r₂ : ℕ)
    (reach₁ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₁) + r₁ * (8 * (u₁ - l₁))) * response 1)
    (reach₂ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₂) + r₂ * (8 * (u₂ - l₂))) * response 1)
    (enough₁ : 2 * r₁ + 2 ≤ dates₁.length + 1) (enough₂ : 2 * r₂ + 2 ≤ dates₂.length + 1) :
    ∃ u f, Runs θ s u f ∧ RestState θ u ∧ u.time = horizon ∧ u.pending = tail ∧
      u.x 0 .q = 1 / 10 ∧ u.x 0 .b = s.x 0 .b ∧
      (∀ q, q ≠ p₁ → q ≠ p₂ → u.x 0 (.z q) = s.x 0 (.z q)) ∧
      (∃ k : ℕ, k ≤ dates₁.length + 1 ∧ u.x 0 (.z p₁) = s.x 0 (.z p₁) + k * (8 * (u₁ - l₁))) ∧
      (∃ k : ℕ, k ≤ dates₂.length + 1 ∧ u.x 0 (.z p₂) = s.x 0 (.z p₂) + k * (8 * (u₂ - l₂))) ∧
      PulseFires (1 / 10) (Real.exp (u.x 0 (.z p₁))) level ∧
      PulseFires (1 / 10) (Real.exp (u.x 0 (.z p₂))) level ∧
      (u.x 0 (.z p₁) = s.x 0 (.z p₁) ∨ ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
        ¬ PulseFires c (Real.exp (u.x 0 (.z p₁) - 8 * (u₁ - l₁))) level) ∧
      (u.x 0 (.z p₂) = s.x 0 (.z p₂) ∨ ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
        ¬ PulseFires c (Real.exp (u.x 0 (.z p₂) - 8 * (u₂ - l₂))) level) ∧
      (tail = [] → ∀ (v : Snapshot 1) (other : ParameterExecution θ (fun _ _ => []) s v),
        ParameterCompleteThrough other horizon →
        u.ObservationalEq v ∧ other.emissions.length = f) := by
  obtain ⟨m, f₁, run₁, rested₁, date₁, pend₁, others₁, b₁, _, ⟨k₁, count₁, gain₁⟩, fires₁,
      last₁, _⟩ :=
    stop_training_exists box config₁ fire entry₁ exit₁ state recovery queue spaced₁
      (by
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hm
        · exact le_rfl
        · rcases List.mem_append.mp hm with hmap | htail
          · obtain ⟨D', hD', rfl⟩ := List.mem_map.mp hmap
            have next := Spaced.later spaced₂ D' hD'
            show middle ≤ D'
            linarith
          · have last := Spaced.horizon_later spaced₂
            have due := tailDue d htail
            linarith)
      r₁ reach₁ enough₁
  have keep₂ : m.x 0 (.z p₂) = s.x 0 (.z p₂) := others₁ p₂ (Ne.symm distinct)
  obtain ⟨u, f₂, run₂, rested₂, date₂, pend₂, others₂, b₂, charge₂, ⟨k₂, count₂, gain₂⟩, fires₂,
      last₂, _⟩ :=
    stop_training_exists (tail := tail) box config₂ fire entry₂ exit₂ rested₁
      (by rw [b₁]; exact recovery) (by rw [pend₁, date₁]) (by rw [date₁]; exact spaced₂)
      tailDue r₂ (by rw [keep₂]; exact reach₂) enough₂
  have keep₁ : u.x 0 (.z p₁) = m.x 0 (.z p₁) := others₂ p₁ distinct
  refine ⟨u, f₁ + f₂, run₁.append run₂, rested₂, date₂, pend₂, charge₂, b₂.trans b₁, ?_,
    ⟨k₁, by omega, by rw [keep₁, gain₁]⟩, ⟨k₂, by omega, by rw [gain₂, keep₂]⟩,
    by rw [keep₁]; exact fires₁, fires₂, ?_, ?_, ?_⟩
  · intro q h₁ h₂
    exact (others₂ q h₂).trans (others₁ q h₁)
  · rw [keep₁]
    exact last₁
  · rw [← keep₂]
    exact last₂
  · intro none v other complete
    exact rest_run_unique box config₂ fire state (run₁.append run₂) rested₂ (pend₂.trans none)
      other (date₂ ▸ complete)

end RecursiveLearning.Native
