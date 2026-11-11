import RoutedProduct

/-! A trained cell whose read pulses are not in its own queue. The cell
trains its two ports from its own pulse trains, then waits at rest. The
two read pulses can come later, from anywhere, in either order. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The same cell with another queue. -/
def requeued (s : Snapshot 1) (Q : List (Delivery 1)) : Snapshot 1 := { s with pending := Q }

/-- A cell at rest stays at rest for as long as no pulse arrives. No
gain moves, the recovery rate is unchanged, and a main charge at its
exact rest value stays there. -/
theorem rest_wait {θ : Fin 1 → Parameters} {p upper lower level} {s : Snapshot 1} {T : ℝ}
    (config : PortConfig θ p upper lower level) (fire : 19 / 20 ≤ level)
    (state : RestState θ s) (ht : s.time ≤ T) (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    ∃ u, Runs θ s u 0 ∧ RestState θ u ∧ u.time = T ∧ u.pending = s.pending ∧
      (∀ q, u.x 0 (.z q) = s.x 0 (.z q)) ∧ u.x 0 .b = s.x 0 .b ∧
      (s.x 0 .q = 1 / 10 → u.x 0 .q = 1 / 10) := by
  rcases ht.eq_or_lt with rfl | lt
  · exact ⟨s, Runs.nil s, state, rfl, rfl, fun _ => rfl, rfl, id⟩
  have ready : ∀ i, s.main i = .ready := fun i => by
    rw [Subsingleton.elim i 0]; exact state.main
  have aux : ∀ i q, s.aux i q = .ready := fun i q => by
    rw [Subsingleton.elim i 0]; exact state.aux q
  have raw : ∀ i q, s.raw i q = none := fun i q => by
    rw [Subsingleton.elim i 0]; exact state.raw q
  have band (t : ℝ) (ht : s.time ≤ t) :
      relax (1 / 2) (1 / 10) (s.x 0 .q) s.time t ∈ Icc (1 / 10 : ℝ) (1 / 10 + 1 / 10000) :=
    relax_mem_band (by norm_num) ht ⟨state.charge.1, state.charge.2⟩ ⟨le_rfl, by norm_num⟩
  let f : ParameterFlow θ s (quietAt s T) := {
    toFlowDynamics := quietDynamics s lt ready aux raw hp
    guards := by
      intro t ht
      have ht₁ : s.time ≤ t := ht.1
      apply port_guards config (ready 0)
      · change relax (1 / 2) (1 / 10) (s.x 0 .q) s.time t < level
        exact (band t ht₁).2.trans_lt (by linarith)
      · intro q
        have h : relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t < 1 :=
          lt_of_le_of_lt (relax_restBand ht₁ (state.sensors q)).2 (by norm_num)
        simp only [aux 0 q]
        exact h }
  refine ⟨quietAt s T, Runs.flow f, ?_, rfl, rfl, fun _ => rfl, rfl, ?_⟩
  · exact {
      main := state.main
      aux := state.aux
      raw := state.raw
      charge := band T lt.le
      sensors := fun q => relax_restBand lt.le (state.sensors q)
      recovery := state.recovery
      energy := relax_mem_band (rate := 10) (target := 100) (by norm_num) lt.le
        ⟨state.energy.1, state.energy.2⟩ ⟨by norm_num, le_rfl⟩
      caps := state.caps }
  · intro h
    show relax (1 / 2) (1 / 10) (s.x 0 .q) s.time T = 1 / 10
    rw [h]
    simp [relax]

/-- A trained cell without its read pulses: its thresholds, its rested
start and its two pulse trains. The start gains do not fire, each dose is
at most 1/20, and each train is long enough for training to stop. After
`horizon` the cell is trained and at rest. -/
structure OpenCell (θ : Fin 1 → Parameters) (ε : ℝ) (s : Snapshot 1)
    (p₁ p₂ : Port) (u₁ l₁ u₂ l₂ level : ℝ) (dates₁ dates₂ : List ℝ)
    (middle horizon : ℝ) (r₁ r₂ : ℕ) : Prop where
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
      (⟨0, p₂, middle⟩ : Delivery 1) :: dates₂.map (fun D => (⟨0, p₂, D⟩ : Delivery 1)))
  spaced₁ : Spaced s.time dates₁ middle
  spaced₂ : Spaced middle dates₂ horizon
  below₁ : ¬ PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₁))) level
  below₂ : ¬ PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₂))) level
  reach₁ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₁) + r₁ * (8 * (u₁ - l₁))) * response 1
  reach₂ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₂) + r₂ * (8 * (u₂ - l₂))) * response 1
  enough₁ : 2 * r₁ + 2 ≤ dates₁.length + 1
  enough₂ : 2 * r₂ + 2 ≤ dates₂.length + 1

/-- The state of a cell is at rest whatever its queue. -/
theorem RestState.requeued {θ : Fin 1 → Parameters} {s : Snapshot 1} (h : RestState θ s)
    (Q : List (Delivery 1)) : RestState θ (requeued s Q) :=
  ⟨h.main, h.aux, h.raw, h.charge, h.sensors, h.recovery, h.energy, h.caps⟩

/-- The training of an open cell, followed by a wait at rest until the
date `H`. Pulses added at the end of the queue and due from `H` on are
still pending. Every FIRE of training comes before `horizon`. Each gain
fires alone from rest, and one dose below it was silent. -/
theorem OpenCell.trained {θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂}
    (cell : OpenCell θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂)
    {tail : List (Delivery 1)} {H : ℝ} (later : horizon ≤ H) (tailDue : ∀ d ∈ tail, H ≤ d.due) :
    ∃ (w : Snapshot 1) (e : ParameterExecution θ (fun _ _ => []) (requeued s (s.pending ++ tail)) w),
      (∀ t ∈ e.emissionTimes 0, t ≤ horizon) ∧ RestState θ w ∧ w.time = H ∧ w.pending = tail ∧
      w.x 0 .q = 1 / 10 ∧ (7 / 100 ≤ w.x 0 .b ∧ w.x 0 .b ≤ 1 / 10) ∧
      PulseFires (1 / 10) (Real.exp (w.x 0 (.z p₁))) level ∧
      PulseFires (1 / 10) (Real.exp (w.x 0 (.z p₂))) level ∧
      (∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
        ¬ PulseFires c (Real.exp (w.x 0 (.z p₁) - 8 * (u₁ - l₁))) level) ∧
      (∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
        ¬ PulseFires c (Real.exp (w.x 0 (.z p₂) - 8 * (u₂ - l₂))) level) := by
  have queue : (requeued s (s.pending ++ tail)).pending = (⟨0, p₁, s.time⟩ : Delivery 1) ::
      (dates₁.map (fun D => (⟨0, p₁, D⟩ : Delivery 1)) ++
        (⟨0, p₂, middle⟩ : Delivery 1) ::
          (dates₂.map (fun D => (⟨0, p₂, D⟩ : Delivery 1)) ++ tail)) := by
    show s.pending ++ tail = _
    rw [cell.queue]
    simp
  obtain ⟨m, f, ⟨e₁, _⟩, rested, date, pend, charge, b, _, _, _, fires₁, fires₂, last₁, last₂, _⟩ :=
    two_port_training_exists (s := requeued s (s.pending ++ tail)) (tail := tail)
      cell.box cell.distinct cell.config₁ cell.config₂ cell.fire cell.entry₁ cell.exit₁
      cell.entry₂ cell.exit₂ (cell.state.requeued _) cell.recovery queue cell.spaced₁ cell.spaced₂
      (fun d hd => later.trans (tailDue d hd)) r₁ r₂ cell.reach₁ cell.reach₂ cell.enough₁
      cell.enough₂
  have silent₁ := last₁.resolve_left (fun same => cell.below₁ (same ▸ fires₁))
  have silent₂ := last₂.resolve_left (fun same => cell.below₂ (same ▸ fires₂))
  obtain ⟨w, ⟨e₂, quiet⟩, restedW, dateW, pendW, gains, bW, chargeW⟩ :=
    rest_wait cell.config₁ cell.fire.1 rested (date ▸ later) (by rw [pend]; exact tailDue)
  have none : e₂.emissionTimes 0 = [] := by
    simp [ParameterExecution.emissionTimes, List.length_eq_zero_iff.mp quiet]
  refine ⟨w, e₁.append e₂, ?_, restedW, dateW, pendW.trans pend, chargeW charge,
    by rw [bW, b]; exact cell.recovery, by rw [gains]; exact fires₁, by rw [gains]; exact fires₂,
    by rw [gains]; exact silent₁, by rw [gains]; exact silent₂⟩
  intro t ht
  rw [emissionTimes_append, none, List.append_nil] at ht
  rw [← date]
  exact emissionTimes_le e₁ 0 t ht

/-- The read of an open cell by two pulses, one on each trained port, in
either order. The two pulses arrive after `horizon`, at most a quarter of
a unit apart. The cell fires its read later than 0.239 units after the
first pulse and no later than 0.256 units after the second, then returns
to rest. Every FIRE of training comes before `horizon`. The list `Q`
holds the two read pulses in their order of arrival. -/
theorem OpenCell.read {θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂}
    (cell : OpenCell θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle horizon r₁ r₂)
    {ρ₁ ρ₂ rest : ℝ} (late₁ : horizon ≤ ρ₁) (late₂ : horizon ≤ ρ₂)
    (close : |ρ₁ - ρ₂| ≤ 1 / 4) (wait : min ρ₁ ρ₂ + 22 ≤ rest) :
    ∃ (Q : List (Delivery 1)) (u : Snapshot 1) (tf : ℝ) (training : List ℝ) (count : ℕ),
      (Q : Multiset (Delivery 1)) = {(⟨0, p₁, ρ₁⟩ : Delivery 1), (⟨0, p₂, ρ₂⟩ : Delivery 1)} ∧
      min ρ₁ ρ₂ + 239 / 1000 < tf ∧ tf ≤ max ρ₁ ρ₂ + 32 / 125 ∧
      Reach θ (requeued s (s.pending ++ Q)) u (training ++ [tf]) count ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = [] ∧ ∀ t ∈ training, t ≤ horizon := by
  obtain ⟨lo, hi⟩ := abs_le.mp close
  rcases le_total ρ₁ ρ₂ with h | h
  · rw [min_eq_left h] at wait ⊢
    rw [max_eq_right h]
    obtain ⟨w, e₁, early, rested, date, pend, charge, recov, fires₁, fires₂, silent₁, silent₂⟩ :=
      cell.trained (tail := [(⟨0, p₁, ρ₁⟩ : Delivery 1), (⟨0, p₂, ρ₂⟩ : Delivery 1)]) late₁
        (by
          intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · exact le_rfl
          · exact h)
    obtain ⟨u, tf, ⟨e₂, emitted⟩, after, before, restedEnd, dateEnd, pendEnd, _⟩ :=
      stopped_staggered_read (later := []) (rest := rest) (D₂ := ρ₂) cell.box cell.distinct
        cell.config₁ cell.config₂ cell.fire cell.entry₁ cell.exit₁ cell.entry₂ cell.exit₂
        cell.dose₁ cell.dose₂ rested charge recov (by rw [pend, date])
        (by rw [date]; exact ⟨h, by linarith⟩) (by rw [date]; exact wait)
        (by intro d hd; cases hd) fires₁ fires₂ silent₁ silent₂
    rw [date] at after
    refine ⟨_, u, tf, e₁.emissionTimes 0, _, rfl, after, before, ⟨e₁.append e₂, ?_, rfl⟩,
      restedEnd, dateEnd, pendEnd, early⟩
    rw [emissionTimes_append]
    congr 1
    simp [ParameterExecution.emissionTimes, emitted]
  · rw [min_eq_right h] at wait ⊢
    rw [max_eq_left h]
    obtain ⟨w, e₁, early, rested, date, pend, charge, recov, fires₁, fires₂, silent₁, silent₂⟩ :=
      cell.trained (tail := [(⟨0, p₂, ρ₂⟩ : Delivery 1), (⟨0, p₁, ρ₁⟩ : Delivery 1)]) late₂
        (by
          intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · exact le_rfl
          · exact h)
    obtain ⟨u, tf, ⟨e₂, emitted⟩, after, before, restedEnd, dateEnd, pendEnd, _⟩ :=
      stopped_staggered_read (later := []) (rest := rest) (D₂ := ρ₁) cell.box cell.distinct.symm
        cell.config₂ cell.config₁ cell.fire cell.entry₂ cell.exit₂ cell.entry₁ cell.exit₁
        cell.dose₂ cell.dose₁ rested charge recov (by rw [pend, date])
        (by rw [date]; exact ⟨h, by linarith⟩) (by rw [date]; exact wait)
        (by intro d hd; cases hd) fires₂ fires₁ silent₂ silent₁
    rw [date] at after
    refine ⟨_, u, tf, e₁.emissionTimes 0, _, ?_, after, before, ⟨e₁.append e₂, ?_, rfl⟩,
      restedEnd, dateEnd, pendEnd, early⟩
    · rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.coe_nil]
      exact Multiset.cons_swap _ _ _
    · rw [emissionTimes_append]
      congr 1
      simp [ParameterExecution.emissionTimes, emitted]

end RecursiveLearning.Native
