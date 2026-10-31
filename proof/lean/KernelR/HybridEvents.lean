import KernelR.HybridWork

/-! Event accounting from the actual hybrid execution. The FAST clock below is
a proof potential, not an extra physical coordinate or a prescribed event word.
The resulting bound concerns main firings; global progress is a separate task. -/
namespace KernelR.Hybrid
open Set

theorem Move.emission_time {n θ route s u} (m : @Move n θ route s u)
    (event : Fin n × ℝ) (he : event ∈ m.ledger.emissions) : event.2 = s.time := by
  cases m with
  | flow f => simp [Move.ledger, Flow.ledger] at he
  | jump j => cases j <;> simp_all [Move.ledger, Jump.ledger, Ledger.zero]

theorem Move.time_monotone {n θ route s u} (m : @Move n θ route s u) : s.time ≤ u.time := by
  cases m with
  | flow f => exact f.positive.le
  | jump j => exact j.time_unchanged.ge

/-- Dates are obtained from actual firings and lie inside the execution interval. -/
theorem Execution.emission_time_bounds {n θ route s u} (e : @Execution n θ route s u)
    (event : Fin n × ℝ) (he : event ∈ e.ledger.emissions) :
    s.time ≤ event.2 ∧ event.2 ≤ u.time := by
  induction e with
  | nil => simp [ledger, Ledger.zero] at he
  | cons step rest ih =>
    have hm : event ∈ step.ledger.emissions ∨ event ∈ rest.ledger.emissions := by
      simpa only [ledger, Ledger.add, List.mem_append] using he
    rcases hm with hm | hm
    · rw [step.emission_time event hm]
      exact ⟨le_rfl, step.time_monotone.trans rest.time_monotone⟩
    · exact ⟨step.time_monotone.trans (ih hm).1, (ih hm).2⟩

/-- Equal-time events retain their actual legal order; no total event priority
is introduced by the chronology statement. -/
theorem Execution.emissions_chronological {n θ route s u} (e : @Execution n θ route s u) :
    e.ledger.emissions.Pairwise (fun x y => x.2 ≤ y.2) := by
  induction e with
  | nil => simp [ledger, Ledger.zero]
  | cons step rest ih =>
    have hs : step.ledger.emissions.Pairwise (fun x y => x.2 ≤ y.2) := by
      cases step with
      | flow f => simp [Move.ledger, Flow.ledger]
      | jump j => cases j <;> simp [Move.ledger, Jump.ledger, Ledger.zero]
    change (step.ledger.emissions ++ rest.ledger.emissions).Pairwise _
    apply List.pairwise_append.mpr
    refine ⟨hs, ih, ?_⟩
    intro x hx y hy
    rw [step.emission_time x hx]
    exact step.time_monotone.trans (rest.emission_time_bounds y hy).1

theorem Execution.emissionTimes_chronological {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) : (e.emissionTimes i).Pairwise (· ≤ ·) := by
  exact List.pairwise_map.mpr (e.emissions_chronological.filter _)

/-- A future queue remains future under causal wiring. This does not assert
that an occupied destination port can accept a due token. -/
def PendingFuture {n} (s : Snapshot n) : Prop := ∀ d ∈ s.pending, s.time ≤ d.due

theorem Jump.pending_future {n route s u} (j : @Jump n route s u)
    (hr : CausalRouter route) (hs : PendingFuture s) : PendingFuture u := by
  cases j with
  | fire i mode guard =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hs d hd
    · exact hr i s.time d hd
  | arrive d before after queue due free =>
    intro e he
    apply hs e
    rw [queue]
    simp only [List.mem_append, List.mem_cons] at he ⊢
    tauto
  | _ => exact hs

theorem Execution.pending_future {n θ route s u} (e : @Execution n θ route s u)
    (hr : CausalRouter route) (hs : PendingFuture s) : PendingFuture u := by
  induction e with
  | nil => exact hs
  | cons step rest ih =>
    apply ih
    cases step with
    | flow f => intro d hd; exact f.pending_urgent d (by simpa [f.queue_fixed] using hd)
    | jump j => exact j.pending_future hr hs

/-- Logarithmic FAST clock, clipped above for a uniform terminal bound. -/
noncomputable def fastPotential {n} (s : Snapshot n) (i : Fin n) : ℝ :=
  if s.main i = .fast then min 1 (Real.log (4 * s.x i .q) / a) else 0

theorem fastPotential_le_one {n} (s : Snapshot n) (i : Fin n) :
    fastPotential s i ≤ 1 := by
  unfold fastPotential
  split_ifs
  · exact min_le_left _ _
  · norm_num

theorem fastPotential_of_fast {n} (s : Snapshot n) (i : Fin n)
    (hm : s.main i = .fast) (hp : 0 < s.x i .q) (hq : s.x i .q ≤ 1) :
    fastPotential s i = Real.log (4 * s.x i .q) / a := by
  have ha : 0 < a := by linarith [a_coarse_bounds.1]
  have hl : Real.log (4 * s.x i .q) ≤ a := by
    exact Real.log_le_log (by positivity) (by linarith)
  simp only [fastPotential, hm, ↓reduceIte]
  exact min_eq_right ((div_le_one ha).mpr hl)

noncomputable def Flow.fastTime {n θ s u} (_f : @Flow n θ s u) (i : Fin n) : ℝ :=
  if s.main i = .fast then u.time - s.time else 0

noncomputable def Move.fastTime {n θ route s u} : @Move n θ route s u → Fin n → ℝ
  | .flow f => f.fastTime
  | .jump _ => fun _ => 0

noncomputable def Execution.fastTime {n θ route s u} : @Execution n θ route s u → Fin n → ℝ
  | .nil _ => fun _ => 0
  | .cons step rest => fun i => step.fastTime i + rest.fastTime i

noncomputable def Move.fireCount {n θ route s u} (m : @Move n θ route s u) (i : Fin n) : ℕ :=
  (m.ledger.emissions.filter (fun ev => ev.1 = i)).length

theorem Execution.signal_count_cons {n θ route s u v} (step : @Move n θ route s u)
    (rest : Execution θ route u v) (i : Fin n) :
    ((Execution.cons step rest).signal i).count = step.fireCount i + (rest.signal i).count := by
  simp [signal, emissionTimes, ledger, Ledger.add, Move.fireCount, List.filter_append]

theorem Flow.fast_potential_balance {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) :
    fastPotential u i + f.fastTime i = fastPotential s i := by
  by_cases hm : s.main i = .fast
  · have ht : u.time ∈ Icc s.time u.time := ⟨f.positive.le, le_rfl⟩
    have hps : 0 < s.x i .q := by
      have hg := (f.guards s.time ⟨le_rfl, f.positive⟩).1 i
      rw [f.initial, hm] at hg
      linarith
    have hpu : 0 < u.x i .q := by
      simpa only [f.final] using f.main_protected_positive i (by simp [hm]) ht
    rw [fastPotential_of_fast u i (by simpa [f.main_fixed] using hm) hpu
      ((f.upper_region hb hi i).2.1), fastPotential_of_fast s i hm hps (hi i).2.1]
    have hsol := f.fast_solution i hm u.time ht
    rw [f.final] at hsol
    have heq : Real.log (4 * u.x i .q) =
        Real.log (4 * s.x i .q) - a * (u.time - s.time) := by
      rw [hsol, ← mul_assoc, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
      ring
    rw [heq]
    simp only [Flow.fastTime, hm, ↓reduceIte]
    have ha : a ≠ 0 := ne_of_gt (by linarith [a_coarse_bounds.1])
    field_simp
    ring
  · simp [fastPotential, Flow.fastTime, hm, f.main_fixed]

/-- Every actual firing contributes one unit, independently of zero-time
interleavings at other cells or auxiliary ports. -/
theorem Jump.fast_potential_balance {n} {θ : Fin n → Parameters} {route s u}
    (j : @Jump n route s u) (i : Fin n) :
    fastPotential u i = fastPotential s i +
      ((Move.jump (θ := θ) j).fireCount i : ℝ) := by
  have ha : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  cases j with
  | fire k mode guard =>
    by_cases hk : i = k
    · subst i
      simp [fastPotential, Move.fireCount, Move.ledger, Jump.ledger, setMain,
        mode, guard, a, ha]
    · simp [fastPotential, Move.fireCount, Move.ledger, Jump.ledger, setMain,
        hk, Ne.symm hk]
  | fastEnd k mode guard =>
    by_cases hk : i = k
    · subst i
      simp [fastPotential, Move.fireCount, Move.ledger, Jump.ledger, Ledger.zero,
        setMain, mode, guard]
    · simp [fastPotential, Move.fireCount, Move.ledger, Jump.ledger, Ledger.zero,
        setMain, hk]
  | reopen k mode guard =>
    by_cases hk : i = k
    · subst i
      simp [fastPotential, Move.fireCount, Move.ledger, Jump.ledger, Ledger.zero,
        setMain, mode]
    · simp [fastPotential, Move.fireCount, Move.ledger, Jump.ledger, Ledger.zero,
        setMain, hk]
  | _ => simp [fastPotential, Move.fireCount, Move.ledger, Jump.ledger, Ledger.zero,
      setAux, setRaw]; rfl

theorem Move.fast_potential_balance {n θ ε route s u} (m : @Move n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) :
    fastPotential u i + m.fastTime i = fastPotential s i + (m.fireCount i : ℝ) := by
  cases m with
  | flow f => simpa [Move.fastTime, Move.fireCount, Move.ledger, Flow.ledger]
      using f.fast_potential_balance hb hi i
  | jump j => simpa [Move.fastTime] using j.fast_potential_balance (θ := θ) i

theorem Execution.fast_potential_balance {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) :
    fastPotential u i + e.fastTime i = fastPotential s i + ((e.signal i).count : ℝ) := by
  induction e with
  | nil => simp [fastTime, signal, emissionTimes, ledger, Ledger.zero]
  | cons step rest ih =>
    have hs := step.fast_potential_balance hb hi i
    have hr := ih (by
      cases step with
      | flow f => exact f.upper_region hb hi
      | jump j => exact j.upper_region hi)
    rw [signal_count_cons, Nat.cast_add]
    simp only [fastTime]
    linarith

theorem Move.fastTime_bounds {n θ route s u} (m : @Move n θ route s u) (i : Fin n) :
    0 ≤ m.fastTime i ∧ m.fastTime i ≤ u.time - s.time := by
  cases m with
  | flow f => simp only [Move.fastTime, Flow.fastTime]; split_ifs <;> constructor <;>
      linarith [f.positive]
  | jump j => simp [Move.fastTime, j.time_unchanged]

theorem Execution.fastTime_bounds {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) :
    0 ≤ e.fastTime i ∧ e.fastTime i ≤ u.time - s.time := by
  induction e with
  | nil => simp [fastTime]
  | cons step rest ih =>
    have h := step.fastTime_bounds i
    simp only [fastTime]
    constructor <;> linarith [h.1, h.2, ih.1, ih.2]

/-- The budget also applies to a reachable suffix, retaining its initial FAST
potential instead of silently resetting the clock at an arbitrary cut. -/
theorem Execution.fire_count_budget {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) :
    ((e.signal i).count : ℝ) + fastPotential s i ≤ u.time - s.time + 1 := by
  have h := e.fast_potential_balance hb hi i
  have ht := (e.fastTime_bounds i).2
  have hp := fastPotential_le_one u i
  linarith

/-- A FAST phase entered at its firing section cannot be left before one time
unit, even across arbitrary legal auxiliary, delivery and other-cell jumps. -/
theorem Execution.fast_departure_not_early {n θ ε route s u}
    (e : @Execution n θ route s u) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (i : Fin n) (hm : s.main i = .fast) (hq : s.x i .q = 1)
    (hu : u.main i ≠ .fast) : s.time + 1 ≤ u.time := by
  have h := e.fast_potential_balance hb hi i
  have ht := (e.fastTime_bounds i).2
  have hp : fastPotential s i = 1 := by
    have ha : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    simp [fastPotential, hm, hq, a, ha]
  have hz : fastPotential u i = 0 := by simp [fastPotential, hu]
  have hc : 0 ≤ ((e.signal i).count : ℝ) := Nat.cast_nonneg _
  rw [hp, hz] at h
  linarith

/-- An actual execution from birth cannot emit more than elapsed time plus one
at a cell, even when its last FAST phase is incomplete. -/
theorem Execution.fire_count_bound {n θ ε route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) :
    ((e.signal i).count : ℝ) ≤ u.time + 1 := by
  have h := e.fast_potential_balance hb hs.upper_region i
  have ht := (e.fastTime_bounds i).2
  have hp := fastPotential_le_one u i
  have hzero : fastPotential s i = 0 := by simp [fastPotential, (hs.2.2 i).1]
  rw [hzero] at h
  rw [hs.1] at ht
  linarith

end KernelR.Hybrid
