import KernelR.HybridReady

/-! Constructive waiting between sources, from arbitrary READY coordinates. -/
namespace KernelR.Hybrid
open MeasureTheory Set

noncomputable def relax (rate target initial start t : ℝ) : ℝ :=
  target + (initial - target) * Real.exp (-rate * (t - start))

theorem relax_initial (rate target initial start : ℝ) :
    relax rate target initial start start = initial := by simp [relax]

theorem relax_derivative (rate target initial start t : ℝ) :
    HasDerivAt (relax rate target initial start)
      (rate * (target - relax rate target initial start t)) t := by
  convert (((((hasDerivAt_id t).sub_const start).const_mul (-rate)).exp).const_mul
    (initial - target)).const_add target using 1
  · funext v; rfl
  · dsimp [relax]; ring

theorem relax_lt {rate target initial start t upper : ℝ}
    (hr : 0 ≤ rate) (ht : start ≤ t) (hi : initial < upper) (hb : target < upper) :
    relax rate target initial start t < upper := by
  have he := Real.exp_pos (-rate * (t - start))
  have hu : Real.exp (-rate * (t - start)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  by_cases h : initial ≤ target
  · have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) he.le
    dsimp [relax]; linarith
  · have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ initial - target by linarith)
    dsimp [relax]; linarith

noncomputable def quietValues {n} (s : Snapshot n) (t : ℝ) : Values n :=
  fun i c => match c with
  | .q => relax (1 / 2) (1 / 10) (s.x i .q) s.time t
  | .m p => relax (1 / 2) (1 / 40) (s.x i (.m p)) s.time t
  | .z p => s.x i (.z p)
  | .b => s.x i .b
  | .energy => relax 10 100 (s.x i .energy) s.time t

noncomputable def quietAt {n} (s : Snapshot n) (t : ℝ) : Snapshot n :=
  {s with time := t, x := quietValues s t}

theorem quietValues_initial {n} (s : Snapshot n) : quietValues s s.time = s.x := by
  funext i c; cases c <;> simp [quietValues, relax_initial]

theorem quietValues_derivative {n θ} (s : Snapshot n)
    (hm : ∀ i, s.main i = .ready) (ha : ∀ i p, s.aux i p = .ready)
    (hn : ∀ i p, s.raw i p = none) (t : ℝ) (i : Fin n) (c : Coord) :
    HasDerivAt (fun v => quietValues s v i c)
      (field θ s (quietValues s t) t i c) t := by
  have hz (v : ℝ) (j : Port) : current s i j v = 0 := by simp [current, hn]
  have hd (v : ℝ) : drive s (quietValues s v) i v = 0 := by simp [drive, hz]
  have he (v : ℝ) (j : Port) : errorAct θ s (quietValues s v) i j = 0 := by
    simp [errorAct, ha]
  have hb (v : ℝ) (j : Port) : markAct θ s (quietValues s v) i j = 0 := by
    simp [markAct, ha]
  cases c with
  | q => simpa [quietValues, field, hm, hd] using
      relax_derivative (1 / 2) (1 / 10) (s.x i .q) s.time t
  | m p => simpa [quietValues, field, ha, hz] using
      relax_derivative (1 / 2) (1 / 40) (s.x i (.m p)) s.time t
  | z p => simpa [quietValues, field, he] using hasDerivAt_const t (s.x i (.z p))
  | b => simpa [quietValues, field, hb] using hasDerivAt_const t (s.x i .b)
  | energy => simpa [quietValues, field, work, hm, ha, hd, hz, he, hb] using
      relax_derivative 10 100 (s.x i .energy) s.time t

/-- Waiting is constructed, not extracted from a supplied execution. The
queue may contain future sources and all memory coordinates are preserved. -/
noncomputable def quietFlow {n θ} (s : Snapshot n) {T : ℝ} (ht : s.time < T)
    (hm : ∀ i, s.main i = .ready) (ha : ∀ i p, s.aux i p = .ready)
    (hn : ∀ i p, s.raw i p = none)
    (hq : ∀ i, s.x i .q < 1) (hx : ∀ i p, s.x i (.m p) < 1)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) : Flow θ s (quietAt s T) where
  positive := ht
  path := quietValues s
  initial := quietValues_initial s
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by
    intro i c
    exact (continuous_iff_continuousAt.mpr (fun t =>
      (quietValues_derivative (θ := θ) s hm ha hn t i c).continuousAt)).continuousOn
  integrable := by
    intro i c
    have hc : Continuous (fun t => field θ s (quietValues s t) t i c) := by
      cases c <;> simp [field, work, drive, current, errorAct, markAct, hm, ha, hn,
        quietValues, relax] <;> fun_prop
    exact hc.intervalIntegrable _ _
  mark_integrable := by intro i p; simp [markAct, ha]
  integral_eq := by
    intro t ht i c
    have hc : Continuous (fun t => field θ s (quietValues s t) t i c) := by
      cases c <;> simp [field, work, drive, current, errorAct, markAct, hm, ha, hn,
        quietValues, relax] <;> fun_prop
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => quietValues_derivative (θ := θ) s hm ha hn v i c)
      (hc.intervalIntegrable s.time t)
    rw [quietValues_initial] at he
    linarith
  guards := by
    intro t ht
    constructor
    · intro i; simp only [hm, quietValues]
      exact relax_lt (by norm_num) ht.1 (hq i) (by norm_num)
    · intro i p; simp only [ha, quietValues]
      exact relax_lt (by norm_num) ht.1 (hx i p) (by norm_num)
  raw_support := by intro i p origin ho; simp [hn] at ho
  pending_urgent := hp


theorem ready_no_jump {n route} (s : Snapshot n)
    (hm : ∀ i, s.main i = .ready) (ha : ∀ i p, s.aux i p = .ready)
    (hn : ∀ i p, s.raw i p = none)
    (hq : ∀ i, s.x i .q < 1) (hx : ∀ i p, s.x i (.m p) < 1)
    (hp : ∀ d ∈ s.pending, s.time < d.due) (u : Snapshot n) :
    IsEmpty (Jump route s u) := by
  constructor
  intro j
  cases j with
  | fire i mode guard => exact (ne_of_lt (hq i)) guard
  | fastEnd i mode guard => simp [hm] at mode
  | reopen i mode guard => simp [hm] at mode
  | mark i p mode guard => exact (ne_of_lt (hx i p)) guard
  | silent i p mode guard => simp [ha] at mode
  | error i p mode guard => simp [ha] at mode
  | auxReady i p mode guard => simp [ha] at mode
  | arrive d before after queue due free =>
      have hmem : d ∈ s.pending := by rw [queue]; simp
      have hlt := hp d hmem
      rw [due] at hlt
      exact lt_irrefl _ hlt
  | rawEnd i p origin active due => simp [hn] at active

/-- A source-free interval is saturated at its horizon when every queued
source is strictly later. No incoming execution is assumed. -/
theorem quiet_complete_exists {n θ route} (s : Snapshot n) {T : ℝ}
    (ht : s.time < T) (hm : ∀ i, s.main i = .ready)
    (ha : ∀ i p, s.aux i p = .ready) (hn : ∀ i p, s.raw i p = none)
    (hq : ∀ i, s.x i .q < 1) (hx : ∀ i p, s.x i (.m p) < 1)
    (hp : ∀ d ∈ s.pending, T < d.due) :
    ∃ e : Execution θ route s (quietAt s T), CompleteThrough e T := by
  let flow : Flow θ s (quietAt s T) := quietFlow s ht hm ha hn hq hx
    (fun d hd => (hp d hd).le)
  refine ⟨.cons (.flow flow) (.nil _), rfl, ?_, hp⟩
  intro u
  apply ready_no_jump (quietAt s T) hm ha hn
  · intro i
    exact relax_lt (by norm_num) ht.le (hq i) (by norm_num)
  · intro i p
    exact relax_lt (by norm_num) ht.le (hx i p) (by norm_num)
  · exact hp

/-- Waiting applies to every READY member of the declared birth family,
including its perturbations, individual log-gains and reserve coordinates. -/
theorem BirthState.quiet_complete_exists {n θ route born T}
    (hborn : @BirthState n born) (ht : 0 < T)
    (ha : ∀ i p, born.aux i p = .ready)
    (hp : ∀ d ∈ born.pending, T < d.due) :
    ∃ e : Execution θ route born (quietAt born T), CompleteThrough e T := by
  apply KernelR.Hybrid.quiet_complete_exists born (by rw [hborn.1]; exact ht)
    (fun i => (hborn.2.2 i).1) ha hborn.2.1
  · intro i; linarith [(hborn.2.2 i).2.1.2]
  · intro i p
    rcases ((hborn.2.2 i).2.2.2.2 p).2 with h | h
    · linarith [h.2.2]
    · exact False.elim (by simpa [ha i p] using h.1)
  · exact hp

end KernelR.Hybrid
