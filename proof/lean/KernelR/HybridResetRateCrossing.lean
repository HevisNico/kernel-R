import KernelR.HybridResetRate
import KernelR.HybridCrossingExecution
import KernelR.HybridWeakFlowStrictification

/-! Recovery-limited firing gaps in the geometric crossing semantics.
The argument works for the larger weak-execution envelope: tangential READY
contacts are allowed and no native refinement or chain protocol is assumed.
Protected equations are transferred from an individual weak flow by exact
strictification, which leaves protected charge and recovery unchanged. -/
namespace KernelR.Hybrid
open Set MeasureTheory

theorem WeakFlow.fast_solution {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (hm : s.main i = .fast) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i .q = s.x i .q * Real.exp (-a * (t - s.time)) := by
  intro t ht
  have h := (f.strictify 1 (by norm_num)).fast_solution i hm t ht
  simpa [WeakFlow.strictify, weakShiftSnapshot, weakShiftValues,
    weakShiftCorrection, hm] using h

theorem WeakFlow.slow_solution {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (hm : s.main i = .slow) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i .q = s.x i .q *
        Real.exp (-(∫ v in s.time..t, f.path v i .b)) := by
  intro t ht
  have h := (f.strictify 1 (by norm_num)).slow_solution i hm t ht
  simpa [WeakFlow.strictify, weakShiftSnapshot, weakShiftValues,
    weakShiftCorrection, hm] using h

theorem WeakFlow.recovery_cap_on {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (hs : s.x i .b ≤ 11 / 10) :
    ∀ t ∈ Icc s.time u.time, f.path t i .b ≤ 11 / 10 := by
  have hs' : (weakShiftSnapshot s 1 s.time).x i .b ≤ 11 / 10 := by
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using hs
  have h := (f.strictify 1 (by norm_num)).recovery_cap_on i hs'
  simpa [WeakFlow.strictify, weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using h

theorem WeakFlow.recovery_cap {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (hs : s.x i .b ≤ 11 / 10) : u.x i .b ≤ 11 / 10 := by
  simpa only [f.final] using f.recovery_cap_on i hs u.time ⟨f.positive.le,le_rfl⟩

theorem WeakMove.time_monotone {n θ route s u} (m : @WeakMove n θ route s u) :
    s.time ≤ u.time := by
  cases m with
  | flow f => exact f.positive.le
  | jump j => exact j.time_unchanged.ge

theorem WeakMove.emission_time {n θ route s u} (m : @WeakMove n θ route s u)
    (event : Fin n × ℝ) (he : event ∈ m.ledger.emissions) : event.2 = s.time := by
  cases m with
  | flow f => simp [WeakMove.ledger, WeakFlow.ledger] at he
  | jump j => cases j <;> simp_all [WeakMove.ledger, Jump.ledger, Ledger.zero]

theorem WeakExecution.emission_time_bounds {n θ route s u}
    (e : @WeakExecution n θ route s u) (event : Fin n × ℝ)
    (he : event ∈ e.ledger.emissions) :
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

def WeakFlow.mainIs {n θ s u} (_f : @WeakFlow n θ s u) (i : Fin n) (mode : MainMode) : Prop :=
  s.main i = mode

def WeakExecution.MainFlows {n θ route s u} (i : Fin n) (mode : MainMode) :
    @WeakExecution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => f.mainIs i mode ∧ rest.MainFlows i mode
  | .cons (.jump _) rest => rest.MainFlows i mode

theorem WeakExecution.fast_solution {n θ route s u} (e : @WeakExecution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .fast) :
    u.x i .q = s.x i .q * Real.exp (-a * (u.time - s.time)) := by
  induction e with
  | nil => simp
  | @cons s u v step rest ih =>
    cases step with
    | flow f =>
      have hf := f.fast_solution i hm.1 u.time ⟨f.positive.le, le_rfl⟩
      rw [f.final] at hf
      rw [ih hm.2, hf, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    | jump j => rw [ih hm, j.physical_continuous, j.time_unchanged]

noncomputable def WeakFlow.accumulatedRecovery {n θ s u} (f : @WeakFlow n θ s u) (i : Fin n) : ℝ :=
  ∫ t in s.time..u.time, f.path t i .b

noncomputable def WeakExecution.accumulatedRecovery {n θ route s u}
    (i : Fin n) : @WeakExecution n θ route s u → ℝ
  | .nil _ => 0
  | .cons (.flow f) rest =>
      f.accumulatedRecovery i + rest.accumulatedRecovery i
  | .cons (.jump _) rest => rest.accumulatedRecovery i

theorem WeakExecution.slow_solution {n θ route s u} (e : @WeakExecution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .slow) :
    u.x i .q = s.x i .q * Real.exp (-e.accumulatedRecovery i) := by
  induction e with
  | nil => simp [WeakExecution.accumulatedRecovery]
  | @cons s u v step rest ih =>
    cases step with
    | flow f =>
      have hf := f.slow_solution i hm.1 u.time ⟨f.positive.le, le_rfl⟩
      rw [f.final] at hf
      rw [ih hm.2, hf, mul_assoc, ← Real.exp_add]
      simp only [WeakExecution.accumulatedRecovery, WeakFlow.accumulatedRecovery]
      congr 2
      ring
    | jump j =>
      simp only [WeakExecution.accumulatedRecovery]
      rw [ih hm, j.physical_continuous]

theorem WeakExecution.fast_duration {n θ route s u} (e : @WeakExecution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .fast) (hs : s.x i .q = 1) (hu : u.x i .q = 1 / 4) :
    u.time - s.time = 1 := by
  have he := e.fast_solution i hm
  rw [hs, hu] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 4)
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4))) he
  simpa [a, ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4))] using h


def WeakExecution.AllFlows {n θ route s u}
    (P : ∀ {v w : Snapshot n}, WeakFlow θ v w → Prop) : @WeakExecution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => P f ∧ rest.AllFlows P
  | .cons (.jump _) rest => rest.AllFlows P

theorem WeakExecution.allFlows_append {n θ route s v u}
    (segment : @WeakExecution n θ route s v) (rest : WeakExecution θ route v u)
    (P : ∀ {a b : Snapshot n}, WeakFlow θ a b → Prop) :
    (segment.append rest).AllFlows P ↔ segment.AllFlows P ∧ rest.AllFlows P := by
  induction segment with
  | nil => simp [append, AllFlows]
  | cons step tail ih => cases step <;> simp [append, AllFlows, ih, and_assoc]


def WeakExecution.AllStates {n θ route s u} (P : Snapshot n → Prop) : @WeakExecution n θ route s u → Prop
  | .nil _ => P s
  | .cons _ rest => P s ∧ rest.AllStates P

theorem WeakExecution.allStates_initial {n θ route s u} (e : @WeakExecution n θ route s u)
    {P : Snapshot n → Prop} (h : e.AllStates P) : P s := by
  cases e <;> simp_all [AllStates]

theorem WeakExecution.allStates_final {n θ route s u} (e : @WeakExecution n θ route s u)
    {P : Snapshot n → Prop} (h : e.AllStates P) : P u := by
  induction e with
  | nil => exact h
  | cons move rest ih => exact ih h.2

theorem WeakExecution.allStates_main_flows {n θ route s u} (e : @WeakExecution n θ route s u)
    (i : Fin n) (mode : MainMode) (h : e.AllStates (fun v => v.main i = mode)) :
    e.MainFlows i mode := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨h.1, ih h.2⟩
    | jump j => exact ih h.2

theorem WeakExecution.allStates_append {n θ route s v u}
    (segment : @WeakExecution n θ route s v) (rest : WeakExecution θ route v u)
    (P : Snapshot n → Prop) :
    (segment.append rest).AllStates P ↔ segment.AllStates P ∧ rest.AllStates P := by
  induction segment with
  | nil => exact ⟨fun h => ⟨rest.allStates_initial h,h⟩,fun h => h.2⟩
  | cons move tail ih => simp only [append,AllStates,ih,and_assoc]


theorem WeakExecution.first_state_change {n θ route s u α} [DecidableEq α]
    (e : @WeakExecution n θ route s u) (observe : Snapshot n → α) (value : α)
    (hfixed : ∀ {v w}, WeakFlow θ v w → observe w = observe v) (hs : observe s = value) :
    e.AllStates (fun v => observe v = value) ∨
    ∃ (v w : Snapshot n) (segment : WeakExecution θ route s v) (exit : Jump route v w)
      (rest : WeakExecution θ route w u),
      e = segment.append (.cons (.jump exit) rest) ∧
      segment.AllStates (fun v => observe v = value) ∧ observe v = value ∧ observe w ≠ value := by
  induction e with
  | nil => exact Or.inl hs
  | @cons s v u move rest ih =>
    by_cases hv : observe v = value
    · rcases ih hv with h | ⟨a,b,segment,exit,tail,he,hp,ha,hb⟩
      · exact Or.inl ⟨hs,h⟩
      · exact Or.inr ⟨a,b,.cons move segment,exit,tail,by simp only [append,he],⟨hs,hp⟩,ha,hb⟩
    · cases move with
      | flow f => exact False.elim (hv ((hfixed f).trans hs))
      | jump j => exact Or.inr ⟨s,v,.nil s,j,rest,rfl,hs,hs,hv⟩


theorem WeakExecution.allStates_mono {n θ route s u} (e : @WeakExecution n θ route s u)
    {P Q : Snapshot n → Prop} (h : ∀ v, P v → Q v) (hp : e.AllStates P) : e.AllStates Q := by
  induction e with
  | nil => exact h _ hp
  | cons move rest ih => exact ⟨h _ hp.1,ih hp.2⟩


theorem WeakExecution.allStates_time_bounds {n θ route s u} (e : @WeakExecution n θ route s u) :
    e.AllStates (fun v => s.time ≤ v.time ∧ v.time ≤ u.time) := by
  induction e with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | @cons s v u move rest ih =>
    refine ⟨⟨le_rfl,move.time_monotone.trans rest.time_monotone⟩,?_⟩
    exact rest.allStates_mono (fun w hw => ⟨move.time_monotone.trans hw.1,hw.2⟩) ih


/-- Upper envelope on the actual recovery coordinate along every flow. -/
def WeakExecution.RecoveryBound {n θ route s u} (e : @WeakExecution n θ route s u)
    (i : Fin n) (β : ℝ) : Prop :=
  e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b ≤ β)

theorem WeakFlow.accumulatedRecovery_le_of_bound {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (β : ℝ)
    (hb : ∀ t ∈ Icc s.time u.time, f.path t i .b ≤ β) :
    f.accumulatedRecovery i ≤ β * (u.time - s.time) := by
  have h : (∫ t in s.time..u.time, f.path t i .b) ≤
      ∫ _t in s.time..u.time, β := intervalIntegral.integral_mono_on f.positive.le
    ((f.continuous i .b).intervalIntegrable_of_Icc f.positive.le)
    intervalIntegrable_const hb
  simpa only [WeakFlow.accumulatedRecovery, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm] using h

theorem WeakExecution.accumulatedRecovery_le_of_bound {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (β : ℝ)
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

theorem WeakExecution.recovery_bound_cap {n θ route s u} (e : @WeakExecution n θ route s u)
    (i : Fin n) (hb : s.x i .b ≤ 11 / 10) : e.RecoveryBound i (11 / 10) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨f.recovery_cap_on i hb, ih (f.recovery_cap i hb)⟩
    | jump j => exact ih (by simpa only [j.physical_continuous] using hb)

/-- SLOW needs a fixed integrated recovery, even while MARK changes b. -/
theorem WeakExecution.slow_duration_lower_of_bound {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
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
theorem WeakExecution.slow_protected_before_of_bound {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
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
    rw [he, WeakExecution.allFlows_append] at hb'
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
    rw [he, WeakExecution.allStates_append]
    exact ⟨hsegment, segment.allStates_final hsegment, hrest⟩

/-- The exact FAST unit and bounded SLOW recovery protect against any input. -/
theorem WeakExecution.fast_protected_before_of_bound {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
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
    rw [he, WeakExecution.allFlows_append] at hb'
    have hslow := rest.slow_protected_before_of_bound i β hβ hg.2 hqslow hb'.2
    have hsegment : segment.AllStates (fun v =>
        v.time < s.time + (1 + Real.log (5 / 2) / β) → v.main i ≠ .ready) :=
      segment.allStates_mono (fun v hv _ => by rw [hv]; decide) hstates
    have hrest : rest.AllStates (fun v =>
        v.time < s.time + (1 + Real.log (5 / 2) / β) → v.main i ≠ .ready) :=
      rest.allStates_mono (fun v hv ht => hv (by rw [hwtime]; linarith)) hslow
    rw [he, WeakExecution.allStates_append]
    exact ⟨hsegment, segment.allStates_final hsegment, hrest⟩


theorem WeakExecution.emissionTimes_cons {n θ route s v u}
    (move : @WeakMove n θ route s v) (rest : WeakExecution θ route v u)
    (i : Fin n) :
    (WeakExecution.cons move rest).emissionTimes i =
      (move.ledger.emissions.filter (fun event => event.1 = i)).map Prod.snd ++
        rest.emissionTimes i := by
  simp [WeakExecution.emissionTimes, WeakExecution.ledger, Ledger.add,
    List.filter_append, List.map_append]

theorem WeakExecution.emissionTimes_lower_of_ready_states {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (lower : ℝ)
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
      | flow f => simp [WeakMove.ledger, WeakFlow.ledger] at hev
      | jump j =>
        have h := j.ready_of_emission i date hev
        rw [h.2]
        exact hs.1 h.1
    · exact ih hs.2 date hr

/-- All ordered pairs of same-cell firing dates have the recovery-limited gap.
This includes consecutive firings and does not assume a source calendar. -/
theorem WeakExecution.emissionTimes_separated_of_recovery_bound {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hb : e.RecoveryBound i β) :
    (e.emissionTimes i).Pairwise
      (fun first second => first + (1 + Real.log (5 / 2) / β) ≤ second) := by
  induction e with
  | nil => simp [emissionTimes, ledger, Ledger.zero]
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      simpa [emissionTimes_cons, WeakMove.ledger, WeakFlow.ledger, Ledger.zero] using ih hb.2
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
          simpa [emissionTimes_cons, WeakMove.ledger, Jump.ledger, List.pairwise_cons]
            using And.intro htimes hr
        · simpa [emissionTimes_cons, WeakMove.ledger, Jump.ledger, hi] using hr
      | _ => simpa [emissionTimes_cons, WeakMove.ledger, Jump.ledger, Ledger.zero] using hr

/-- Uniform bound from the model's built-in recovery cap, for any router and queue. -/
theorem WeakExecution.emissionTimes_separated {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (hb : s.x i .b ≤ 11 / 10) :
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

theorem WeakExecution.emissionTimes_bounds {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (date : ℝ)
    (hd : date ∈ e.emissionTimes i) : s.time ≤ date ∧ date ≤ u.time := by
  obtain ⟨event,he,hdate⟩ := List.mem_map.mp hd
  have h := e.emission_time_bounds event (List.mem_filter.mp he).1
  simpa only [hdate] using h

/-- The finite-window count includes a boundary allowance of one firing. -/
theorem WeakExecution.firing_count_bound_of_recovery_bound {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
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

theorem WeakExecution.firing_count_bound {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (hb : s.x i .b ≤ 11 / 10) :
    (((e.emissionTimes i).length : ℝ) - 1) * (1 + Real.log (5 / 2) / (11 / 10)) ≤
      u.time - s.time :=
  e.firing_count_bound_of_recovery_bound i (11 / 10) (by norm_num)
    (e.recovery_bound_cap i hb)

theorem WeakExecution.firing_count_ceiling_of_recovery_bound {n θ route s u}
    (e : @WeakExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
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


/-- The written model's crossing executions inherit the bound directly from
their weak paths, for every network, router and queue. -/
theorem CrossingExecution.emissionTimes_separated_of_recovery_bound {n θ route s u}
    (e : @CrossingExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hb : e.execution.RecoveryBound i β) :
    (e.execution.emissionTimes i).Pairwise
      (fun first second => first + (1 + Real.log (5 / 2) / β) ≤ second) :=
  e.execution.emissionTimes_separated_of_recovery_bound i β hβ hb

theorem CrossingExecution.emissionTimes_separated {n θ route s u}
    (e : @CrossingExecution n θ route s u) (i : Fin n)
    (hb : s.x i .b ≤ 11 / 10) :
    (e.execution.emissionTimes i).Pairwise
      (fun first second => first + (1 + Real.log (5 / 2) / (11 / 10)) ≤ second) :=
  e.execution.emissionTimes_separated i hb

theorem CrossingExecution.firing_count_bound_of_recovery_bound {n θ route s u}
    (e : @CrossingExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hb : e.execution.RecoveryBound i β) :
    (((e.execution.emissionTimes i).length : ℝ) - 1) *
      (1 + Real.log (5 / 2) / β) ≤ u.time - s.time :=
  e.execution.firing_count_bound_of_recovery_bound i β hβ hb

theorem CrossingExecution.firing_count_bound {n θ route s u}
    (e : @CrossingExecution n θ route s u) (i : Fin n)
    (hb : s.x i .b ≤ 11 / 10) :
    (((e.execution.emissionTimes i).length : ℝ) - 1) *
      (1 + Real.log (5 / 2) / (11 / 10)) ≤ u.time - s.time :=
  e.execution.firing_count_bound i hb

theorem CrossingExecution.firing_count_ceiling_of_recovery_bound {n θ route s u}
    (e : @CrossingExecution n θ route s u) (i : Fin n) (β : ℝ) (hβ : 0 < β)
    (hb : e.execution.RecoveryBound i β) :
    ((e.execution.emissionTimes i).length : ℝ) ≤
      1 + (u.time - s.time) / (1 + Real.log (5 / 2) / β) :=
  e.execution.firing_count_ceiling_of_recovery_bound i β hβ hb

#print axioms CrossingExecution.emissionTimes_separated
#print axioms CrossingExecution.emissionTimes_separated_of_recovery_bound
#print axioms CrossingExecution.firing_count_ceiling_of_recovery_bound

end KernelR.Hybrid
