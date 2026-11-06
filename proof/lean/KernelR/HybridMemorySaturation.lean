import KernelR.HybridDoseCounting
import KernelR.HybridFlowCuts
import KernelR.HybridPhysicalInvariant

/-! Finite saturation of one input memory, with the actual strict cap gate.

Unlike `ErrorExposed`, the exposure predicate here requires only ERROR mode,
READY main mode and positive energy. It deliberately permits the cap to close.
The clipped transfer is deduced from the actual integral dynamics, rather than
assumed as a recurrence. Full-section counts describe a cover of a real trace.
-/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- ERROR and READY persist on this flow and power is available. No headroom
condition is imposed: the automatic cap gate may close during the flow. -/
def Flow.ErrorAvailable {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port) : Prop :=
  s.aux i p = .error ∧ s.main i = .ready ∧
    ∀ t ∈ Icc s.time u.time, 0 < f.path t i .energy

def Execution.ErrorAvailable {n θ route s u} (i : Fin n) (p : Port) :
    @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => f.ErrorAvailable i p ∧ rest.ErrorAvailable i p
  | .cons (.jump _) rest => rest.ErrorAvailable i p

theorem Flow.error_available_of_invariant {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) (i : Fin n) (p : Port)
    (ha : s.aux i p = .error) (hm : s.main i = .ready) : f.ErrorAvailable i p :=
  ⟨ha, hm, f.power_gate_open_of_invariant hb hs i⟩

/-- Physical reserve bounds derive the power premise along an actual ERROR
span. READY exposure still has to be established from its real main modes. -/
theorem Execution.error_available_of_invariant {n θ ε route s u}
    (e : @Execution n θ route s u) (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (i : Fin n) (p : Port) (ha : e.AuxFlows i p .error) (hm : e.MainFlows i .ready) :
    e.ErrorAvailable i p := by
  induction e with
  | nil => trivial
  | @cons s v u move rest ih =>
    have hn := (.cons move (.nil _) : Execution θ route s v).physical_invariant hb hs
    cases move with
    | flow f => exact ⟨f.error_available_of_invariant hb hs i p ha.1 hm.1,
        ih hn ha.2 hm.2⟩
    | jump j => exact ih hn ha hm

theorem Execution.ErrorExposed.available {n θ route s u i p}
    {e : @Execution n θ route s u} (h : e.ErrorExposed i p) : e.ErrorAvailable i p := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨⟨h.1.1, h.1.2.1, fun t ht => (h.1.2.2 t ht).1⟩, ih h.2⟩
    | jump j => exact ih h

theorem Flow.gain_le_final {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    ∀ t ∈ Icc s.time u.time, f.path t i (.z p) ≤ u.x i (.z p) := by
  intro t ht
  rcases ht.2.eq_or_lt with heq | hlt
  · simp only [heq, f.final, le_refl]
  · have h := (f.suffix ht.1 hlt).gain_nondecreasing hb i p u.time ⟨hlt.le, le_rfl⟩
    simpa only [Flow.suffix, Flow.at, f.final] using h

theorem Execution.ErrorAvailable.aux_flows {n θ route s u i p}
    {e : @Execution n θ route s u} (h : e.ErrorAvailable i p) : e.AuxFlows i p .error := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨h.1.1, ih h.2⟩
    | jump j => exact ih h

/-- Below the final cap, nondecreasing gain forces every earlier cap gate
to have remained open. This supplies the old uncapped balance only in the
branch where its strict premise is actually justified. -/
theorem Execution.ErrorAvailable.exposed_of_final_lt {n θ ε route s u i p}
    {e : @Execution n θ route s u} (h : e.ErrorAvailable i p)
    (hb : PhysicalBox θ ε) (hlt : u.x i (.z p) < Real.log ((θ i).cap p)) :
    e.ErrorExposed i p := by
  induction e with
  | nil => trivial
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hv := (rest.gain_nondecreasing hb i p).trans_lt hlt
      refine ⟨⟨h.1.1, h.1.2.1, fun t ht => ⟨h.1.2.2 t ht, ?_⟩⟩, ih h.2 hlt⟩
      exact (f.gain_le_final hb i p t ht).trans_lt hv
    | jump j => exact ih h hlt

/-- An arbitrary interleaved ERROR span obeys the exact clipped transfer.
It may hit the cap before the phase ends; no cap-open premise is assumed. -/
theorem Execution.error_capped_transfer {n θ ε route s u}
    (e : @Execution n θ route s u) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (available : e.ErrorAvailable i p)
    (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = min (Real.log ((θ i).cap p))
      (s.x i (.z p) + 8 * (s.x i (.m p) - u.x i (.m p))) := by
  have hcap := e.gain_cap i p initial
  have hbudget := e.error_gain_budget hb i p available.aux_flows
  by_cases hlt : u.x i (.z p) < Real.log ((θ i).cap p)
  · have he := e.error_charge_balance i p (available.exposed_of_final_lt hb hlt)
    have hz := e.gain_balance i p
    have htransfer : u.x i (.z p) =
        s.x i (.z p) + 8 * (s.x i (.m p) - u.x i (.m p)) := by linarith
    rw [← htransfer, min_eq_right hlt.le]
  · have heq : u.x i (.z p) = Real.log ((θ i).cap p) := le_antisymm hcap (le_of_not_gt hlt)
    have hremaining : Real.log ((θ i).cap p) ≤
        s.x i (.z p) + 8 * (s.x i (.m p) - u.x i (.m p)) := by linarith
    rw [heq, min_eq_left hremaining]

/-- Reaching the cap freezes this port's memory under every later legal
execution, independently of its route, inputs and learning-phase exposure. -/
theorem Execution.gain_stays_at_cap {n θ ε route s u}
    (e : @Execution n θ route s u) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (initial : s.x i (.z p) = Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) := by
  apply le_antisymm (e.gain_cap i p initial.le)
  rw [← initial]
  exact e.gain_nondecreasing hb i p

/-- A counted section has real entry and exit jumps, all actual intermediate
ERROR states and mechanical exposure. The final section may be cap-clipped.
Inactive moves are justified by mode, never by a supplied zero-dose equality. -/
inductive CappedErrorSectionCover {n : ℕ} {θ : Fin n → Parameters} {route : Router n}
    (i : Fin n) (p : Port) : {s u : Snapshot n} → Execution θ route s u → Type
  | nil (s) : CappedErrorSectionCover i p (.nil s)
  | inactive {s v u} (move : Move θ route s v) (rest : Execution θ route v u)
      (physical : move.ErrorInactive i p) (tail : CappedErrorSectionCover i p rest) :
      CappedErrorSectionCover i p (.cons move rest)
  | fullPhase {s a b c u}
      (entry : Jump route s a) (span : Execution θ route a b)
      (exit : Jump route b c) (rest : Execution θ route c u)
      (before : s.aux i p ≠ .error) (entered : a.aux i p = .error)
      (leaving : b.aux i p = .error) (after : c.aux i p ≠ .error)
      (phase : span.AllStates (fun v => v.aux i p = .error))
      (available : span.ErrorAvailable i p) (tail : CappedErrorSectionCover i p rest) :
      CappedErrorSectionCover i p
        (.cons (.jump entry) (span.append (.cons (.jump exit) rest)))

def CappedErrorSectionCover.count {n θ route i p s u} {e : @Execution n θ route s u} :
    CappedErrorSectionCover i p e → ℕ
  | .nil _ => 0
  | .inactive _ _ _ tail => tail.count
  | .fullPhase _ _ _ _ _ _ _ _ _ _ tail => tail.count + 1

/-- Existing genuinely exposed section covers also satisfy the more general
cap-permitting interface, with the same actual sections. -/
noncomputable def ErrorSectionCover.toCapped {n θ route i p s u}
    {e : @Execution n θ route s u} (cover : ErrorSectionCover i p e) :
    CappedErrorSectionCover i p e := by
  induction cover with
  | nil s => exact .nil s
  | inactive move rest physical tail ih => exact .inactive move rest physical ih
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    exact .fullPhase entry span exit rest before entered leaving after phase exposed.available ih

theorem ErrorSectionCover.toCapped_count {n θ route i p s u}
    {e : @Execution n θ route s u} (cover : ErrorSectionCover i p e) :
    cover.toCapped.count = cover.count := by
  induction cover with
  | nil s => rfl
  | inactive move rest physical tail ih => exact ih
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    exact congrArg (fun k : ℕ => k + 1) ih

private theorem min_add_nonnegative (cap value increment : ℝ) (h : 0 ≤ increment) :
    min cap (min cap value + increment) = min cap (value + increment) := by
  by_cases hc : cap ≤ value
  · rw [min_eq_left hc, min_eq_left (by linarith), min_eq_left (by linarith)]
  · rw [min_eq_right (le_of_not_ge hc)]

/-- Complete-section counting with exact automatic clipping, valid for
arbitrary routers and all finite traces admitting the actual section cover. -/
theorem CappedErrorSectionCover.gain_eq {n θ ε route i p s u}
    {e : @Execution n θ route s u} (cover : CappedErrorSectionCover i p e)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = min (Real.log ((θ i).cap p))
      (s.x i (.z p) + (3 / 5 : ℝ) * cover.count) := by
  induction cover with
  | nil s => simp only [count, Nat.cast_zero, mul_zero, add_zero, min_eq_right initial]
  | @inactive s v u move rest physical tail ih =>
    have hmove : v.x i (.z p) = s.x i (.z p) := by
      rw [move.gain_balance i p, move.error_zero_of_inactive i p physical, add_zero]
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
      min_add_nonnegative _ _ _ (mul_nonneg (by norm_num) (Nat.cast_nonneg _))]
    simp only [count, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

/-- Any sufficient number of actual complete available ERROR sections fills
the memory. This does not claim that arbitrary inputs produce those sections. -/
theorem CappedErrorSectionCover.saturated_of_dose {n θ ε route i p s u}
    {e : @Execution n θ route s u} (cover : CappedErrorSectionCover i p e)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p))
    (dose : Real.log ((θ i).cap p) - s.x i (.z p) ≤ (3 / 5 : ℝ) * cover.count) :
    u.x i (.z p) = Real.log ((θ i).cap p) := by
  rw [cover.gain_eq hb initial, min_eq_left (by linarith)]

/-- Required number of complete available ERROR sections for this initial
port memory, rounded upward. It is zero when the memory starts at its cap. -/
noncomputable def gainSaturationCount {n} (θ : Fin n → Parameters)
    (s : Snapshot n) (i : Fin n) (p : Port) : ℕ :=
  ⌈(Real.log ((θ i).cap p) - s.x i (.z p)) / (3 / 5 : ℝ)⌉₊

/-- The ceiling threshold is both sufficient and necessary for a trace with
this complete mechanically exposed section cover. No event timing occurs in
the threshold, and the final ERROR section is allowed to be clipped. -/
theorem CappedErrorSectionCover.saturated_iff_count {n θ ε route i p s u}
    {e : @Execution n θ route s u} (cover : CappedErrorSectionCover i p e)
    (hb : PhysicalBox θ ε) (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) = Real.log ((θ i).cap p) ↔
      gainSaturationCount θ s i p ≤ cover.count := by
  rw [cover.gain_eq hb initial, min_eq_left_iff, gainSaturationCount,
    Nat.ceil_le, div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 5)]
  constructor <;> intro h <;> linarith

#print axioms Execution.error_capped_transfer
#print axioms Execution.gain_stays_at_cap
#print axioms CappedErrorSectionCover.gain_eq
#print axioms CappedErrorSectionCover.saturated_of_dose
#print axioms CappedErrorSectionCover.saturated_iff_count

end KernelR.Hybrid
