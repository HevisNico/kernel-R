import KernelR.HybridClipping
import KernelR.HybridEvents

/-! Select actual first mode departures from executions. Protected phases are
located by their physical guards rather than supplied as a pulse-case word. -/
namespace KernelR.Hybrid
open Set

def Execution.append {n θ route s v u} :
    @Execution n θ route s v → Execution θ route v u → Execution θ route s u
  | .nil _, rest => rest
  | .cons step segment, rest => .cons step (segment.append rest)

def Execution.ConstantFlows {n θ route s u α} (observe : Snapshot n → α) (value : α) :
    @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow _) rest => observe s = value ∧ rest.ConstantFlows observe value
  | .cons (.jump _) rest => rest.ConstantFlows observe value

theorem Execution.constantFlows_main {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (mode : MainMode) :
    e.ConstantFlows (fun v => v.main i) mode ↔ e.MainFlows i mode := by
  induction e with
  | nil => rfl
  | cons step rest ih => cases step <;> simp [ConstantFlows, MainFlows, Flow.mainIs, ih]

theorem Execution.constantFlows_aux {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) :
    e.ConstantFlows (fun v => v.aux i p) mode ↔ e.AuxFlows i p mode := by
  induction e with
  | nil => rfl
  | cons step rest ih => cases step <;> simp [ConstantFlows, AuxFlows, Flow.auxIs, ih]

/-- Either the observation stays fixed, or the execution splits at its first
actual changing jump. The returned segment, jump and suffix reconstruct e. -/
theorem Execution.first_change {n θ route s u α} [DecidableEq α]
    (e : @Execution n θ route s u) (observe : Snapshot n → α) (value : α)
    (hfixed : ∀ {v w}, Flow θ v w → observe w = observe v) (hs : observe s = value) :
    (observe u = value ∧ e.ConstantFlows observe value) ∨
    ∃ (v w : Snapshot n) (segment : Execution θ route s v) (exit : Jump route v w)
      (rest : Execution θ route w u),
      e = segment.append (.cons (.jump exit) rest) ∧ segment.ConstantFlows observe value ∧
      observe v = value ∧ observe w ≠ value := by
  induction e with
  | nil => exact Or.inl ⟨hs, trivial⟩
  | @cons s v u step rest ih =>
    by_cases hv : observe v = value
    · rcases ih hv with hrest | ⟨a, b, segment, exit, tail, he, hp, ha, hb⟩
      · left
        refine ⟨hrest.1, ?_⟩
        cases step with
        | flow f => exact ⟨hs, hrest.2⟩
        | jump j => exact hrest.2
      · right
        refine ⟨a, b, .cons step segment, exit, tail, ?_, ?_, ha, hb⟩
        · simp only [append, he]
        · cases step with
          | flow f => exact ⟨hs, hp⟩
          | jump j => exact hp
    · cases step with
      | flow f => exact False.elim (hv ((hfixed f).trans hs))
      | jump j => exact Or.inr ⟨s, v, .nil s, j, rest, rfl, trivial, hs, hv⟩

theorem Execution.first_main_change {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (mode : MainMode) (hs : s.main i = mode) :
    (u.main i = mode ∧ e.MainFlows i mode) ∨
    ∃ (v w : Snapshot n) (segment : Execution θ route s v) (exit : Jump route v w)
      (rest : Execution θ route w u),
      e = segment.append (.cons (.jump exit) rest) ∧ segment.MainFlows i mode ∧
      v.main i = mode ∧ w.main i ≠ mode := by
  simpa only [constantFlows_main] using
    e.first_change (fun v => v.main i) mode (fun f => congrFun f.main_fixed i) hs

theorem Execution.first_aux_change {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (hs : s.aux i p = mode) :
    (u.aux i p = mode ∧ e.AuxFlows i p mode) ∨
    ∃ (v w : Snapshot n) (segment : Execution θ route s v) (exit : Jump route v w)
      (rest : Execution θ route w u),
      e = segment.append (.cons (.jump exit) rest) ∧ segment.AuxFlows i p mode ∧
      v.aux i p = mode ∧ w.aux i p ≠ mode := by
  simpa only [constantFlows_aux] using e.first_change (fun v => v.aux i p) mode
    (fun f => congrFun (congrFun f.aux_fixed i) p) hs

noncomputable def mainFloor : MainMode → ℝ
  | .ready => 0 | .fast => 1 / 4 | .slow => 1 / 10

theorem Flow.protected_main_floor {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i ≠ .ready) :
    ∀ t ∈ Icc s.time u.time, mainFloor (s.main i) ≤ f.path t i .q := by
  have h := continuous_bound_from_Ico f.positive (f.continuous i .q).neg (cap := -mainFloor (s.main i)) (by
    intro t ht
    have hg := (f.guards t ht).1 i
    cases ha : s.main i <;> simp_all [mainFloor]
    all_goals linarith)
  intro t ht
  have hh : -f.path t i .q ≤ -mainFloor (s.main i) := h t ht
  linarith

theorem Execution.protected_main_floor {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (mode : MainMode) (hne : mode ≠ .ready) (hm : e.MainFlows i mode)
    (hi : mainFloor mode ≤ s.x i .q) : mainFloor mode ≤ u.x i .q := by
  induction e with
  | nil => exact hi
  | @cons s v u step rest ih =>
    cases step with
    | flow f =>
      apply ih hm.2
      have h := f.protected_main_floor i (by rw [hm.1]; exact hne) v.time ⟨f.positive.le, le_rfl⟩
      have hmode : s.main i = mode := hm.1
      simpa only [f.final, hmode] using h
    | jump j => exact ih hm (by simpa only [j.physical_continuous] using hi)

theorem duration_le_of_decay_floor {initial final floor rate duration : ℝ}
    (hi : 0 < initial) (hf : 0 < floor) (hr : 0 < rate) (hfloor : floor ≤ final)
    (he : final = initial * Real.exp (-rate * duration)) :
    duration ≤ Real.log (initial / floor) / rate := by
  have hl := Real.log_le_log hf hfloor
  rw [he, Real.log_mul (ne_of_gt hi) (Real.exp_ne_zero _), Real.log_exp] at hl
  apply (le_div_iff₀ hr).mpr
  rw [Real.log_div (ne_of_gt hi) (ne_of_gt hf)]
  linarith

theorem Execution.fast_no_overrun {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .fast) (hq : s.x i .q = 1) : u.time ≤ s.time + 1 := by
  have he := e.fast_solution i hm
  have hf := e.protected_main_floor i .fast (by decide) hm (by norm_num [mainFloor, hq])
  rw [hq] at he
  have h := duration_le_of_decay_floor (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 4) (by linarith [a_coarse_bounds.1]) hf he
  have ha : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [a, mainFloor, ha] at h
  linarith

/-- A sufficiently long actual execution contains the complete FAST phase,
with its first departure, exact date and SLOW successor extracted from e. -/
theorem Execution.fast_phase_completion {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .fast) (hq : s.x i .q = 1)
    (ht : s.time + 1 < u.time) :
    ∃ (v w : Snapshot n) (segment : Execution θ route s v) (exit : Jump route v w)
      (rest : Execution θ route w u),
      e = segment.append (.cons (.jump exit) rest) ∧ segment.MainFlows i .fast ∧
      v.main i = .fast ∧ w.main i = .slow ∧ v.time = s.time + 1 ∧ v.x i .q = 1 / 4 := by
  rcases e.first_main_change i .fast hs with h | ⟨v, w, segment, exit, rest, he, hm, hv, hw⟩
  · exact False.elim (not_lt_of_ge (e.fast_no_overrun i h.2 hq) ht)
  · have hg := exit.fast_departure_guard i hv hw
    have hd := segment.fast_duration i hm hq hg.1
    exact ⟨v, w, segment, exit, rest, he, hm, hv, hg.2, by linarith, hg.1⟩

def auxSuccessor : AuxMode → AuxMode
  | .ready => .mark | .mark => .silent | .silent => .error | .error => .ready

theorem Jump.protected_aux_departure {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (hne : mode ≠ .ready)
    (hs : s.aux i p = mode) (hu : u.aux i p ≠ mode) :
    s.x i (.m p) = protectedFloor mode ∧ u.aux i p = auxSuccessor mode := by
  cases mode <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply, protectedFloor, auxSuccessor]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem PhysicalBox.aux_rate_positive {n θ ε} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (mode : AuxMode) (hne : mode ≠ .ready) :
    0 < auxRate (θ i) p mode := by
  cases mode with
  | ready => exact False.elim (hne rfl)
  | mark => exact (hb.rates_positive i p).1
  | silent => exact (hb.rates_positive i p).2.1
  | error => exact (hb.rates_positive i p).2.2

theorem protectedFloor_positive (mode : AuxMode) (hne : mode ≠ .ready) :
    0 < protectedFloor mode := by cases mode <;> norm_num [protectedFloor] at *

/-- Remaining protected-phase time uses the actual initial charge, so an ERROR
residue at birth is neither rounded up to a full phase nor discarded. -/
noncomputable def auxRemaining {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mode : AuxMode) : ℝ :=
  Real.log (s.x i (.m p) / protectedFloor mode) / auxRate (θ i) p mode

theorem Execution.aux_no_overrun {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (mode : AuxMode) (hne : mode ≠ .ready)
    (hm : e.AuxFlows i p mode) (hi : protectedFloor mode ≤ s.x i (.m p)) :
    u.time ≤ s.time + auxRemaining θ s i p mode := by
  have hf := protectedFloor_positive mode hne
  have he := e.aux_phase_solution i p mode hne hm
  have hfloor := e.protected_aux_floor i p mode hne hm hi
  have h := duration_le_of_decay_floor (hf.trans_le hi) hf (hb.aux_rate_positive i p mode hne) hfloor he
  change u.time - s.time ≤ auxRemaining θ s i p mode at h
  linarith

/-- This witness selects a phase from the original execution and reconstructs
that execution exactly. Its date and successor come from physical equations. -/
structure AuxDeparture {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) where
  beforeExit : Snapshot n
  afterExit : Snapshot n
  span : Execution θ route s beforeExit
  exit : Jump route beforeExit afterExit
  rest : Execution θ route afterExit u
  reconstruct : e = span.append (.cons (.jump exit) rest)
  flows : span.AuxFlows i p mode
  mode_before : beforeExit.aux i p = mode
  mode_after : afterExit.aux i p = auxSuccessor mode
  date : beforeExit.time = s.time + auxRemaining θ s i p mode
  charge : beforeExit.x i (.m p) = protectedFloor mode

theorem Execution.aux_phase_completion {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (mode : AuxMode) (hne : mode ≠ .ready)
    (hs : s.aux i p = mode) (hi : protectedFloor mode ≤ s.x i (.m p))
    (ht : s.time + auxRemaining θ s i p mode < u.time) : Nonempty (AuxDeparture e i p mode) := by
  rcases e.first_aux_change i p mode hs with h | ⟨v, w, segment, exit, rest, he, hm, hv, hw⟩
  · exact False.elim (not_lt_of_ge (e.aux_no_overrun hb i p mode hne h.2 hi) ht)
  · have hg := exit.protected_aux_departure i p mode hne hv hw
    have hsol := segment.aux_phase_solution i p mode hne hm
    rw [hg.1] at hsol
    have hf := protectedFloor_positive mode hne
    have hd := duration_of_decay (hf.trans_le hi) hf (ne_of_gt (hb.aux_rate_positive i p mode hne)) hsol
    exact ⟨⟨v, w, segment, exit, rest, he, hm, hv, hg.2, by dsimp [auxRemaining]; linarith, hg.1⟩⟩

/-- The complete ERROR exposure follows from reachable energy, actual READY
chronology, and charge headroom. No open-cap premise is repeated at every cut. -/
theorem Execution.error_exposed_of_headroom {n θ ε route born s u}
    (e : @Execution n θ route s u) (past : Execution θ route born s)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (ha : e.AuxFlows i p .error) (hm : e.MainFlows i .ready)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p)) :
    e.ErrorExposed i p := by
  induction e with
  | nil => trivial
  | @cons s v u step rest ih =>
    have progressed : Execution θ route born v := past.append (.cons step (.nil v))
    cases step with
    | flow f =>
      refine ⟨f.error_open_of_reachable past hborn hb i p ha.1 hm.1
        (f.error_cap_open_of_headroom hb i p ha.1 hh), ?_⟩
      apply ih progressed ha.2 hm.2
      have h := f.error_gain_budget hb i p ha.1
      linarith
    | jump j =>
      apply ih progressed ha hm
      simpa only [j.physical_continuous] using hh

end KernelR.Hybrid
