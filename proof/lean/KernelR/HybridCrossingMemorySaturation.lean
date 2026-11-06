import KernelR.HybridMemorySaturation
import KernelR.HybridWeakFlowStrictification
import KernelR.HybridCrossingExecution

/-! Cap-clipped memory saturation for weak flows and actual upward-crossing runs.

No identification of native and crossing executions is assumed. The existing
coordinate-preserving strictification of a single weak flow leaves z, energy,
and ERROR sensor charge unchanged; the integral result therefore transfers
flow by flow. The weak and crossing execution results are then proved directly.
-/
namespace KernelR.Hybrid
open Set MeasureTheory

def WeakFlow.ErrorAvailable {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (p : Port) : Prop :=
  s.aux i p = .error ∧ s.main i = .ready ∧
    ∀ t ∈ Icc s.time u.time, 0 < f.path t i .energy

def WeakExecution.ErrorAvailable {n θ route s u} (i : Fin n) (p : Port) :
    @WeakExecution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => f.ErrorAvailable i p ∧ rest.ErrorAvailable i p
  | .cons (.jump _) rest => rest.ErrorAvailable i p

theorem WeakFlow.memory_gain_cap {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (p : Port) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) ≤ Real.log ((θ i).cap p) := by
  have h := (f.strictify 1 (by norm_num)).gain_cap i p (by
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using initial)
  simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using h

theorem WeakFlow.memory_gain_nondecreasing {n θ ε s u} (f : @WeakFlow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    s.x i (.z p) ≤ u.x i (.z p) := by
  have h := (f.strictify 1 (by norm_num)).gain_nondecreasing hb i p u.time
    ⟨f.positive.le, le_rfl⟩
  simpa [WeakFlow.strictify, weakShiftSnapshot, weakShiftValues, weakShiftCorrection,
    f.final] using h

theorem WeakFlow.error_capped_transfer {n θ ε s u} (f : @WeakFlow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (available : f.ErrorAvailable i p)
    (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = min (Real.log ((θ i).cap p))
      (s.x i (.z p) + 8 * (s.x i (.m p) - u.x i (.m p))) := by
  let flow := f.strictify 1 (by norm_num)
  let span : Execution θ (fun _ _ => []) (weakShiftSnapshot s 1 s.time)
      (weakShiftSnapshot u 1 s.time) := .cons (.flow flow) (.nil _)
  have hav : span.ErrorAvailable i p := by
    refine ⟨⟨available.1, available.2.1, ?_⟩, trivial⟩
    intro t ht
    simpa [flow, WeakFlow.strictify, weakShiftValues, weakShiftCorrection]
      using available.2.2 t ht
  have hs : (weakShiftSnapshot s 1 s.time).x i (.z p) ≤ Real.log ((θ i).cap p) := by
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using initial
  have hu : u.aux i p = .error := by simpa [f.aux_fixed] using available.1
  have h := span.error_capped_transfer hb i p hav hs
  simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection, available.1, hu] using h

theorem WeakFlow.error_charge_nonincreasing {n θ ε s u} (f : @WeakFlow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (ha : s.aux i p = .error) :
    u.x i (.m p) ≤ s.x i (.m p) := by
  let strict := f.strictify 1 (by norm_num)
  have hmode : (weakShiftSnapshot s 1 s.time).aux i p ≠ .ready := by simp [weakShiftSnapshot, ha]
  have hp := strict.protected_aux_positive i p hmode ⟨le_rfl, f.positive.le⟩
  have initial : 0 ≤ s.x i (.m p) := by
    have h : 0 < s.x i (.m p) := by
      simpa [strict, WeakFlow.strictify, weakShiftSnapshot, weakShiftValues,
        weakShiftCorrection, ha, f.initial] using hp
    exact h.le
  have hu : u.aux i p = .error := by simpa [f.aux_fixed] using ha
  have he := strict.aux_decay_solution i p hmode u.time ⟨f.positive.le, le_rfl⟩
  have solution : u.x i (.m p) = s.x i (.m p) *
      Real.exp (-(θ i).le p * (u.time - s.time)) := by
    simpa [strict, WeakFlow.strictify, weakShiftSnapshot, weakShiftValues,
      weakShiftCorrection, ha, hu, f.final] using he
  have hexp : Real.exp (-(θ i).le p * (u.time - s.time)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [(hb.rates_positive i p).2.2, f.positive])
  rw [solution]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp initial

theorem WeakExecution.memory_gain_cap {n θ route s u} (e : @WeakExecution n θ route s u)
    (i : Fin n) (p : Port) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) ≤ Real.log ((θ i).cap p) := by
  induction e with
  | nil => exact initial
  | cons move rest ih => cases move with
    | flow f => exact ih (f.memory_gain_cap i p initial)
    | jump j => exact ih (by simpa only [j.physical_continuous] using initial)

theorem WeakExecution.memory_gain_nondecreasing {n θ ε route s u}
    (e : @WeakExecution n θ route s u) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    s.x i (.z p) ≤ u.x i (.z p) := by
  induction e with
  | nil => exact le_rfl
  | cons move rest ih => cases move with
    | flow f => exact (f.memory_gain_nondecreasing hb i p).trans ih
    | jump j => simpa only [j.physical_continuous] using ih

theorem WeakExecution.error_charge_nonincreasing {n θ ε route s u}
    (e : @WeakExecution n θ route s u) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (available : e.ErrorAvailable i p) : u.x i (.m p) ≤ s.x i (.m p) := by
  induction e with
  | nil => exact le_rfl
  | cons move rest ih => cases move with
    | flow f => exact (ih available.2).trans (f.error_charge_nonincreasing hb i p available.1.1)
    | jump j => simpa only [j.physical_continuous] using ih available

private theorem memory_min_add_nonnegative (cap value increment : ℝ) (h : 0 ≤ increment) :
    min cap (min cap value + increment) = min cap (value + increment) := by
  by_cases hc : cap ≤ value
  · rw [min_eq_left hc, min_eq_left (by linarith), min_eq_left (by linarith)]
  · rw [min_eq_right (le_of_not_ge hc)]

theorem WeakExecution.error_capped_transfer {n θ ε route s u}
    (e : @WeakExecution n θ route s u) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (available : e.ErrorAvailable i p)
    (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = min (Real.log ((θ i).cap p))
      (s.x i (.z p) + 8 * (s.x i (.m p) - u.x i (.m p))) := by
  induction e with
  | nil => simp [min_eq_right initial]
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hf := f.error_capped_transfer hb i p available.1 initial
      have hd := rest.error_charge_nonincreasing hb i p available.2
      rw [ih available.2 (f.memory_gain_cap i p initial), hf,
        memory_min_add_nonnegative _ _ _ (by linarith)]
      congr 1
      ring
    | jump j =>
      simpa only [j.physical_continuous] using ih available
        (by simpa only [j.physical_continuous] using initial)

theorem WeakExecution.gain_stays_at_cap {n θ ε route s u}
    (e : @WeakExecution n θ route s u) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (initial : s.x i (.z p) = Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) := by
  apply le_antisymm (e.memory_gain_cap i p initial.le)
  rw [← initial]
  exact e.memory_gain_nondecreasing hb i p

/-- Every recorded snapshot of the span really remains in ERROR. -/
def WeakExecution.MemoryErrorStates {n θ route s u} (i : Fin n) (p : Port) :
    @WeakExecution n θ route s u → Prop
  | .nil s => s.aux i p = .error
  | .cons _ rest => s.aux i p = .error ∧ rest.MemoryErrorStates i p

def WeakMove.MemoryErrorInactive {n θ route s u} (move : @WeakMove n θ route s u)
    (i : Fin n) (p : Port) : Prop :=
  match move with
  | .flow _ => s.aux i p ≠ .error ∨ s.main i ≠ .ready
  | .jump _ => True

theorem WeakMove.memory_gain_constant_of_inactive {n θ route s u}
    (move : @WeakMove n θ route s u) (i : Fin n) (p : Port)
    (inactive : move.MemoryErrorInactive i p) : u.x i (.z p) = s.x i (.z p) := by
  cases move with
  | jump j => simp only [j.physical_continuous]
  | flow f =>
    have h := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.z p)
    rcases inactive with ha | hm
    · simpa [field, errorAct, ha, f.final] using h
    · simpa [field, errorAct, hm, f.final] using h

inductive WeakCappedErrorSectionCover {n : ℕ} {θ : Fin n → Parameters} {route : Router n}
    (i : Fin n) (p : Port) : {s u : Snapshot n} → WeakExecution θ route s u → Type
  | nil (s) : WeakCappedErrorSectionCover i p (.nil s)
  | inactive {s v u} (move : WeakMove θ route s v) (rest : WeakExecution θ route v u)
      (physical : move.MemoryErrorInactive i p) (tail : WeakCappedErrorSectionCover i p rest) :
      WeakCappedErrorSectionCover i p (.cons move rest)
  | fullPhase {s a b c u}
      (entry : Jump route s a) (span : WeakExecution θ route a b)
      (exit : Jump route b c) (rest : WeakExecution θ route c u)
      (before : s.aux i p ≠ .error) (entered : a.aux i p = .error)
      (leaving : b.aux i p = .error) (after : c.aux i p ≠ .error)
      (phase : span.MemoryErrorStates i p) (available : span.ErrorAvailable i p)
      (tail : WeakCappedErrorSectionCover i p rest) :
      WeakCappedErrorSectionCover i p
        (.cons (.jump entry) (span.append (.cons (.jump exit) rest)))

def WeakCappedErrorSectionCover.count {n θ route i p s u}
    {e : @WeakExecution n θ route s u} : WeakCappedErrorSectionCover i p e → ℕ
  | .nil _ => 0
  | .inactive _ _ _ tail => tail.count
  | .fullPhase _ _ _ _ _ _ _ _ _ _ tail => tail.count + 1

theorem WeakCappedErrorSectionCover.gain_eq {n θ ε route i p s u}
    {e : @WeakExecution n θ route s u} (cover : WeakCappedErrorSectionCover i p e)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = min (Real.log ((θ i).cap p))
      (s.x i (.z p) + (3 / 5 : ℝ) * cover.count) := by
  induction cover with
  | nil s => simp only [count, Nat.cast_zero, mul_zero, add_zero, min_eq_right initial]
  | @inactive s v u move rest physical tail ih =>
    have hmove := move.memory_gain_constant_of_inactive i p physical
    rw [ih (by simpa only [hmove] using initial), hmove]
    rfl
  | @fullPhase s a b c u entry span exit rest before entered leaving after phase available tail ih =>
    have ha : a.x i (.z p) ≤ Real.log ((θ i).cap p) := by
      simpa only [entry.physical_continuous] using initial
    have hsection := span.error_capped_transfer hb i p available ha
    rw [entry.error_entry_guard i p before entered,
      exit.error_departure_guard i p leaving after] at hsection
    norm_num only at hsection
    have hc : c.x i (.z p) = min (Real.log ((θ i).cap p))
        (s.x i (.z p) + 3 / 5) := by
      rw [exit.physical_continuous, hsection, entry.physical_continuous]
    rw [ih (by rw [hc]; exact min_le_left _ _), hc,
      memory_min_add_nonnegative _ _ _ (mul_nonneg (by norm_num) (Nat.cast_nonneg _))]
    simp only [count, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

theorem WeakCappedErrorSectionCover.saturated_iff_count {n θ ε route i p s u}
    {e : @WeakExecution n θ route s u} (cover : WeakCappedErrorSectionCover i p e)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) ↔
      gainSaturationCount θ s i p ≤ cover.count := by
  rw [cover.gain_eq hb initial, min_eq_left_iff, gainSaturationCount,
    Nat.ceil_le, div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 5)]
  constructor <;> intro h <;> linarith

/-- Direct model-semantics conclusion: the cover belongs to the actual weak
history carried by this upward-crossing execution. No native refinement or
chain-protocol theorem is needed. -/
theorem CrossingExecution.memory_saturated_iff_count {n θ ε route s u}
    (run : @CrossingExecution n θ route s u) (i : Fin n) (p : Port)
    (cover : WeakCappedErrorSectionCover i p run.execution)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) ↔
      gainSaturationCount θ s i p ≤ cover.count :=
  cover.saturated_iff_count hb initial

theorem CrossingExecution.gain_stays_at_cap {n θ ε route s u}
    (run : @CrossingExecution n θ route s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (initial : s.x i (.z p) = Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) :=
  run.execution.gain_stays_at_cap hb i p initial

/-- A stationary READY state with every port memory already at its own cap.
This witnesses consistency of positive-duration saturated executions; it does
not claim that the state is reachable from a declared protocol birth. -/
noncomputable def saturatedResting {n} (θ : Fin n → Parameters) (t : ℝ) : Snapshot n :=
  ⟨t, (fun i c => match c with
    | .q => 1 / 10 | .m _ => 1 / 40 | .z p => Real.log ((θ i).cap p)
    | .b => 2 / 25 | .energy => 100),
    fun _ => .ready, fun _ _ => .ready, fun _ _ => none, []⟩

theorem saturatedResting_field {n} (θ : Fin n → Parameters) (s t : ℝ)
    (i : Fin n) (c : Coord) :
    field θ (saturatedResting θ s) (saturatedResting θ s).x t i c = 0 := by
  cases c <;> simp [field, saturatedResting, drive, current, work, errorAct, markAct]

noncomputable def saturatedRestingFlow {n} (θ : Fin n → Parameters) {T : ℝ}
    (hT : 0 < T) : Flow θ (saturatedResting θ 0) (saturatedResting θ T) where
  positive := hT
  path := fun _ => (saturatedResting θ 0).x
  initial := rfl
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun _ _ => continuousOn_const
  integrable := by intros; simp only [saturatedResting_field]; exact intervalIntegrable_const
  mark_integrable := by intros; simp [markAct, saturatedResting]
  integral_eq := by intros; simp [saturatedResting_field]
  guards := by intros; constructor <;> intros <;> norm_num [BeforeGuards, saturatedResting]
  raw_support := by intros; simp_all [saturatedResting]
  pending_urgent := by intros; simp_all [saturatedResting]

theorem saturatedResting_physical {n} (θ : Fin n → Parameters) (t : ℝ) :
    PhysicalInvariant θ (saturatedResting θ t) := by
  constructor
  · intro i
    norm_num [UpperRegion, saturatedResting, auxUpper]
  · intro i p; exact le_rfl
  · intro i; norm_num [saturatedResting]
  · intro i; norm_num [saturatedResting]

theorem saturatedResting_no_jump {n route T u θ} :
    IsEmpty (@Jump n route (saturatedResting θ T) u) := by
  constructor
  intro j
  cases j <;> simp_all [saturatedResting]

/-- A concrete complete upward-crossing execution of any positive duration
can remain saturated. This is an at-cap witness, not a learning-reachability
or a cap-clipped final-section existence theorem. -/
theorem saturated_resting_crossing_complete_exists {n} (θ : Fin n → Parameters)
    (route : Router n) {T : ℝ} (hT : 0 < T) :
    ∃ run : CrossingExecution θ route (saturatedResting θ 0) (saturatedResting θ T),
      PhysicalInvariant θ (saturatedResting θ 0) ∧ CrossingCompleteThrough run T ∧
        ∀ i p, (saturatedResting θ T).x i (.z p) = Real.log ((θ i).cap p) := by
  let run : CrossingExecution θ route (saturatedResting θ 0) (saturatedResting θ T) :=
    ⟨.cons (.flow (saturatedRestingFlow θ hT).toWeak) (.nil _), trivial⟩
  refine ⟨run, saturatedResting_physical θ 0, ?_, fun _ _ => rfl⟩
  refine ⟨rfl, ?_, ?_⟩
  · intro v j
    exact False.elim (saturatedResting_no_jump.false j)
  · simp [saturatedResting]

#print axioms WeakExecution.error_capped_transfer
#print axioms WeakCappedErrorSectionCover.gain_eq
#print axioms CrossingExecution.memory_saturated_iff_count
#print axioms CrossingExecution.gain_stays_at_cap
#print axioms saturated_resting_crossing_complete_exists

end KernelR.Hybrid
