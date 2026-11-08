import KernelR.HybridSlowProtection

/-! Recovery-limited firing rates for arbitrary finite native executions.
No input protocol, router causality or completeness premise is required.
The recovery envelope is imposed on actual continuous paths, not only their
initial values. Input sensors may still learn during main-cell protection. -/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- Upper envelope on the actual recovery coordinate along every flow. -/
def Execution.RecoveryBound {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (β : ℝ) : Prop :=
  e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b ≤ β)

theorem Flow.accumulatedRecovery_le_of_bound {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (β : ℝ)
    (hb : ∀ t ∈ Icc s.time u.time, f.path t i .b ≤ β) :
    f.accumulatedRecovery i ≤ β * (u.time - s.time) := by
  have h : (∫ t in s.time..u.time, f.path t i .b) ≤
      ∫ _t in s.time..u.time, β := intervalIntegral.integral_mono_on f.positive.le
    ((f.continuous i .b).intervalIntegrable_of_Icc f.positive.le)
    intervalIntegrable_const hb
  simpa only [Flow.accumulatedRecovery, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm] using h

theorem Execution.accumulatedRecovery_le_of_bound {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (β : ℝ)
    (hb : e.RecoveryBound i β) :
    e.accumulatedRecovery i ≤ β * (u.time - s.time) := by
  induction e with
  | nil => simp [accumulatedRecovery]
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      have hf := f.accumulatedRecovery_le_of_bound i β hb.1
      have hr := ih hb.2
      simp only [accumulatedRecovery]
      nlinarith
    | jump j =>
      simpa only [accumulatedRecovery, j.time_unchanged] using ih hb

theorem Execution.recovery_bound_cap {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hb : s.x i .b ≤ 11 / 10) : e.RecoveryBound i (11 / 10) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨f.recovery_cap_on i hb, ih (f.recovery_cap i hb)⟩
    | jump j => exact ih (by simpa only [j.physical_continuous] using hb)

/-- SLOW needs a fixed integrated recovery, even while MARK changes b. -/
theorem Execution.slow_duration_lower_of_bound {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hm : e.MainFlows i .slow) (hs : s.x i .q = 1 / 4)
    (hu : u.x i .q = 1 / 10) (hb : e.RecoveryBound i β) :
    Real.log (5 / 2) / β ≤ u.time - s.time := by
  have he := e.slow_solution i hm
  rw [hs, hu] at he
  have hex : Real.exp (-e.accumulatedRecovery i) = (2 / 5 : ℝ) := by linarith
  have href : Real.exp (-Real.log (5 / 2)) = (2 / 5 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]
    norm_num
  have hi := neg_injective (Real.exp_injective (hex.trans href.symm))
  have hbnd := e.accumulatedRecovery_le_of_bound i β hb
  rw [hi] at hbnd
  exact (div_le_iff₀ hβ).mpr (by nlinarith)

/-- Reopening cannot precede the integrated SLOW lower bound. -/
theorem Execution.slow_protected_before_of_bound {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hs : s.main i = .slow) (hq : s.x i .q = 1 / 4)
    (hb : e.RecoveryBound i β) :
    e.AllStates (fun v => v.time < s.time + Real.log (5 / 2) / β →
      v.main i ≠ .ready) := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h |
      ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.allStates_mono (fun v hv _ => by rw [hv]; decide) h
  · have hb' := hb
    unfold RecoveryBound at hb'
    rw [he, Execution.allFlows_append] at hb'
    have hg := exit.slow_departure_guard i hv hw
    have hd := segment.slow_duration_lower_of_bound i β hβ
      (segment.allStates_main_flows i .slow hstates) hq hg hb'.1
    have hwtime : s.time + Real.log (5 / 2) / β ≤ w.time := by
      rw [exit.time_unchanged]
      linarith
    have hsegment : segment.AllStates (fun v =>
        v.time < s.time + Real.log (5 / 2) / β → v.main i ≠ .ready) :=
      segment.allStates_mono (fun v hv _ => by rw [hv]; decide) hstates
    have hrest : rest.AllStates (fun v =>
        v.time < s.time + Real.log (5 / 2) / β → v.main i ≠ .ready) :=
      rest.allStates_mono (fun v hv ht => False.elim (by linarith [hv.1]))
        rest.allStates_time_bounds
    rw [he, Execution.allStates_append]
    exact ⟨hsegment, segment.allStates_final hsegment, hrest⟩

/-- The exact FAST unit and bounded SLOW recovery protect against any input. -/
theorem Execution.fast_protected_before_of_bound {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hs : s.main i = .fast) (hq : s.x i .q = 1)
    (hb : e.RecoveryBound i β) :
    e.AllStates (fun v => v.time < s.time + (1 + Real.log (5 / 2) / β) →
      v.main i ≠ .ready) := by
  rcases e.first_state_change (fun v => v.main i) .fast
    (fun f => congrFun f.main_fixed i) hs with h |
      ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.allStates_mono (fun v hv _ => by rw [hv]; decide) h
  · have hg := exit.fast_departure_guard i hv hw
    have hd := segment.fast_duration i
      (segment.allStates_main_flows i .fast hstates) hq hg.1
    have hwtime : w.time = s.time + 1 := by rw [exit.time_unchanged]; linarith
    have hqslow : w.x i .q = 1 / 4 := by rw [exit.physical_continuous, hg.1]
    have hb' := hb
    unfold RecoveryBound at hb'
    rw [he, Execution.allFlows_append] at hb'
    have hslow := rest.slow_protected_before_of_bound i β hβ hg.2 hqslow hb'.2
    have hsegment : segment.AllStates (fun v =>
        v.time < s.time + (1 + Real.log (5 / 2) / β) → v.main i ≠ .ready) :=
      segment.allStates_mono (fun v hv _ => by rw [hv]; decide) hstates
    have hrest : rest.AllStates (fun v =>
        v.time < s.time + (1 + Real.log (5 / 2) / β) → v.main i ≠ .ready) :=
      rest.allStates_mono (fun v hv ht => hv (by rw [hwtime]; linarith)) hslow
    rw [he, Execution.allStates_append]
    exact ⟨hsegment, segment.allStates_final hsegment, hrest⟩

/-- An actual same-cell emission can only come from its READY FIRE jump. -/
theorem Jump.ready_of_emission {n route s u} (j : @Jump n route s u)
    (i : Fin n) (date : ℝ) (h : (i,date) ∈ j.ledger.emissions) :
    s.main i = .ready ∧ date = s.time := by
  cases j with
  | fire k hm hq =>
    simp only [Jump.ledger, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact ⟨hm,rfl⟩
  | _ => simp [Jump.ledger, Ledger.zero] at h

theorem Execution.emissionTimes_lower_of_ready_states {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (lower : ℝ)
    (hs : e.AllStates (fun v => v.main i = .ready → lower ≤ v.time)) :
    ∀ date ∈ e.emissionTimes i, lower ≤ date := by
  induction e with
  | nil => simp [emissionTimes, ledger, Ledger.zero]
  | @cons s v u move rest ih =>
    intro date hd
    rw [emissionTimes_cons] at hd
    rcases List.mem_append.mp hd with hj | hr
    · obtain ⟨event,he,hed⟩ := List.mem_map.mp hj
      have hf := List.mem_filter.mp he
      have hi : event.1 = i := by simpa using hf.2
      have hev : (i,date) ∈ move.ledger.emissions := by
        have heq : event = (i,date) := Prod.ext hi hed
        simpa only [heq] using hf.1
      cases move with
      | flow f => simp [Move.ledger, Flow.ledger] at hev
      | jump j =>
        have h := j.ready_of_emission i date hev
        rw [h.2]
        exact hs.1 h.1
    · exact ih hs.2 date hr

/-- All ordered pairs of same-cell firing dates have the recovery-limited gap.
This includes consecutive firings and does not assume a source calendar. -/
theorem Execution.emissionTimes_separated_of_recovery_bound {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hb : e.RecoveryBound i β) :
    (e.emissionTimes i).Pairwise
      (fun first second => first + (1 + Real.log (5 / 2) / β) ≤ second) := by
  induction e with
  | nil => simp [emissionTimes, ledger, Ledger.zero]
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      simpa [emissionTimes_cons, Move.ledger, Flow.ledger, Ledger.zero] using ih hb.2
    | jump j =>
      have hr := ih hb
      cases j with
      | fire k hm hq =>
        by_cases hi : k = i
        · subst k
          have hp := rest.fast_protected_before_of_bound i β hβ
            (by simp [setMain]) hq hb
          have hstates := rest.allStates_mono
            (fun v hv hready => le_of_not_gt (fun ht => hv ht hready)) hp
          have htimes := rest.emissionTimes_lower_of_ready_states i
            (s.time + (1 + Real.log (5 / 2) / β)) hstates
          simpa [emissionTimes_cons, Move.ledger, Jump.ledger, List.pairwise_cons]
            using And.intro htimes hr
        · simpa [emissionTimes_cons, Move.ledger, Jump.ledger, hi] using hr
      | _ => simpa [emissionTimes_cons, Move.ledger, Jump.ledger, Ledger.zero] using hr

/-- Uniform bound from the model's built-in recovery cap, for any router and queue. -/
theorem Execution.emissionTimes_separated {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (hb : s.x i .b ≤ 11 / 10) :
    (e.emissionTimes i).Pairwise
      (fun first second => first + (1 + Real.log (5 / 2) / (11 / 10)) ≤ second) := by
  exact e.emissionTimes_separated_of_recovery_bound i (11 / 10) (by norm_num)
    (e.recovery_bound_cap i hb)

private theorem list_span_bound (dates : List ℝ) (gap lower upper : ℝ)
    (hgap : 0 ≤ gap) (htime : lower ≤ upper)
    (hp : dates.Pairwise (fun first second => first + gap ≤ second))
    (hlo : ∀ t ∈ dates, lower ≤ t) (hhi : ∀ t ∈ dates, t ≤ upper) :
    ((dates.length : ℝ) - 1) * gap ≤ upper - lower := by
  induction dates generalizing lower with
  | nil => simp only [List.length_nil, Nat.cast_zero]; nlinarith
  | cons first rest ih =>
    have hfirst := List.pairwise_cons.mp hp
    have hstart := hlo first (List.mem_cons_self)
    cases rest with
    | nil =>
      have hend := hhi first List.mem_cons_self
      simp only [List.length_cons, List.length_nil,
        Nat.cast_one, zero_add, sub_self, zero_mul]
      linarith
    | cons next tail =>
      have hnext := hfirst.1 next List.mem_cons_self
      have htop := hhi next (List.mem_cons_of_mem first List.mem_cons_self)
      have hrec := ih (first + gap) (by linarith) hfirst.2 hfirst.1
        (fun t ht => hhi t (List.mem_cons_of_mem first ht))
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hrec ⊢
      nlinarith

theorem Execution.emissionTimes_bounds {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (date : ℝ)
    (hd : date ∈ e.emissionTimes i) : s.time ≤ date ∧ date ≤ u.time := by
  obtain ⟨event,he,hdate⟩ := List.mem_map.mp hd
  have h := e.emission_time_bounds event (List.mem_filter.mp he).1
  simpa only [hdate] using h

/-- The finite-window count includes a boundary allowance of one firing. -/
theorem Execution.firing_count_bound_of_recovery_bound {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hb : e.RecoveryBound i β) :
    (((e.emissionTimes i).length : ℝ) - 1) * (1 + Real.log (5 / 2) / β) ≤
      u.time - s.time := by
  apply list_span_bound (e.emissionTimes i) _ _ _
  · have hlog : 0 < Real.log (5 / 2) := Real.log_pos (by norm_num)
    positivity
  · exact e.time_monotone
  · exact e.emissionTimes_separated_of_recovery_bound i β hβ hb
  · exact fun t ht => (e.emissionTimes_bounds i t ht).1
  · exact fun t ht => (e.emissionTimes_bounds i t ht).2

theorem Execution.firing_count_bound {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (hb : s.x i .b ≤ 11 / 10) :
    (((e.emissionTimes i).length : ℝ) - 1) * (1 + Real.log (5 / 2) / (11 / 10)) ≤
      u.time - s.time :=
  e.firing_count_bound_of_recovery_bound i (11 / 10) (by norm_num)
    (e.recovery_bound_cap i hb)

/-- Count rather than average frequency is bounded in a finite observation window. -/
theorem Execution.firing_count_ceiling_of_recovery_bound {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hb : e.RecoveryBound i β) :
    ((e.emissionTimes i).length : ℝ) ≤
      1 + (u.time - s.time) / (1 + Real.log (5 / 2) / β) := by
  have hlog : 0 < Real.log (5 / 2) := Real.log_pos (by norm_num)
  have hgap : 0 < 1 + Real.log (5 / 2) / β := by positivity
  have h := e.firing_count_bound_of_recovery_bound i β hβ hb
  have hdiv : ((e.emissionTimes i).length : ℝ) - 1 ≤
      (u.time - s.time) / (1 + Real.log (5 / 2) / β) :=
    (le_div_iff₀ hgap).mpr h
  linarith

/-- A weaker recovery envelope can only increase this minimum firing gap. -/
theorem reset_gap_antitone {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    1 + Real.log (5 / 2) / β₂ ≤ 1 + Real.log (5 / 2) / β₁ := by
  have hlog : 0 ≤ Real.log (5 / 2) := (Real.log_pos (by norm_num)).le
  linarith [div_le_div_of_nonneg_left hlog hβ₁ hβ]

/-- Certified decimal bracket; 1.833 is a rounded approximation, not a lower bound. -/
theorem reset_gap_cap_bounds :
    (18329915 / 10000000 : ℝ) < 1 + Real.log (5 / 2) / (11 / 10) ∧
    1 + Real.log (5 / 2) / (11 / 10) < 18329916 / 10000000 := by
  constructor <;> linarith [KernelR.log_recovery_bounds.1, KernelR.log_recovery_bounds.2]

end KernelR.Hybrid
