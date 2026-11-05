import KernelR.HybridDoseCountingTools

/-! Zero physical dose implies structural inactivity when the energy and cap
gates are strictly open. The implication is proved from positive-duration
auxiliary decay. It does not add a zero-ledger alternative to cover constructors.
-/
namespace KernelR.Hybrid
open Set MeasureTheory

theorem Flow.section_error_nonnegative {n θ ε s u} (f : @Flow n θ s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port) : 0 ≤ f.ledger.error i p := by
  exact intervalIntegral.integral_nonneg f.positive.le
    (fun t ht => f.error_act_nonnegative box i p ht)

theorem Flow.section_mark_nonnegative {n θ ε s u} (f : @Flow n θ s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port) : 0 ≤ f.ledger.mark i p := by
  exact intervalIntegral.integral_nonneg f.positive.le
    (fun t ht => f.mark_act_nonnegative box i p ht)

theorem Execution.section_error_nonnegative {n θ ε route s u}
    (e : @Execution n θ route s u) (box : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    0 ≤ e.ledger.error i p := by
  have balance := e.gain_balance i p
  have monotone := e.gain_nondecreasing box i p
  linarith

theorem Execution.section_mark_nonnegative {n θ ε route s u}
    (e : @Execution n θ route s u) (box : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    0 ≤ e.ledger.mark i p := by
  induction e with
  | nil => exact le_rfl
  | cons move rest ih =>
    change 0 ≤ move.ledger.mark i p + rest.ledger.mark i p
    cases move with
    | flow f => exact add_nonneg (f.section_mark_nonnegative box i p) ih
    | jump j => simpa only [Move.ledger, j.no_mark_actuation, zero_add] using ih

/-- Any fully exposed positive-duration ERROR flow has strictly positive dose. -/
theorem Flow.section_error_positive {n θ ε s u} (f : @Flow n θ s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port) (exposed : ErrorOpen f i p) :
    0 < f.ledger.error i p := by
  have start_positive := f.protected_aux_positive i p
    (by rw [exposed.1]; decide) (show s.time ∈ Icc s.time u.time from ⟨le_rfl, f.positive.le⟩)
  rw [f.initial] at start_positive
  have decay := f.aux_decay_solution i p (by rw [exposed.1]; decide)
    u.time ⟨f.positive.le, le_rfl⟩
  simp only [f.final, exposed.1] at decay
  have exponent : -(θ i).le p * (u.time - s.time) < 0 := by
    nlinarith [mul_pos (box.rates_positive i p).2.2 (sub_pos.mpr f.positive)]
  have factor := Real.exp_lt_one_iff.mpr exponent
  have decrease : u.x i (.m p) < s.x i (.m p) := by
    rw [decay]
    exact (mul_lt_mul_of_pos_left factor start_positive).trans_eq (mul_one _)
  rw [f.error_charge_balance i p exposed]
  exact mul_pos (by norm_num) (sub_pos.mpr decrease)

theorem Flow.section_mark_positive {n θ ε s u} (f : @Flow n θ s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port) (exposed : MarkOpen f i p) :
    0 < f.ledger.mark i p := by
  have start_positive := f.protected_aux_positive i p
    (by rw [exposed.1]; decide) (show s.time ∈ Icc s.time u.time from ⟨le_rfl, f.positive.le⟩)
  rw [f.initial] at start_positive
  have decay := f.aux_decay_solution i p (by rw [exposed.1]; decide)
    u.time ⟨f.positive.le, le_rfl⟩
  simp only [f.final, exposed.1] at decay
  have exponent : -(θ i).lm p * (u.time - s.time) < 0 := by
    nlinarith [mul_pos (box.rates_positive i p).1 (sub_pos.mpr f.positive)]
  have factor := Real.exp_lt_one_iff.mpr exponent
  have decrease : u.x i (.m p) < s.x i (.m p) := by
    rw [decay]
    exact (mul_lt_mul_of_pos_left factor start_positive).trans_eq (mul_one _)
  change 0 < f.markIntegral i p
  rw [f.mark_charge_balance i p exposed]
  exact mul_pos (by norm_num) (sub_pos.mpr decrease)

/-- A zero ERROR ledger under open gates forces actual mode inactivity on
every flow; clipping and power loss cannot explain the zero. -/
theorem Execution.error_inactive_of_zero_open {n θ ε route s u}
    (e : @Execution n θ route s u) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen e) (i : Fin n) (p : Port)
    (zero_dose : e.ledger.error i p = 0) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .error ∨ v.main i ≠ .ready) := by
  induction e with
  | nil => trivial
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      change f.ledger.error i p + rest.ledger.error i p = 0 at zero_dose
      have nf := f.section_error_nonnegative box i p
      have nr := rest.section_error_nonnegative box i p
      have fzero : f.ledger.error i p = 0 := by linarith
      have rzero : rest.ledger.error i p = 0 := by linarith
      refine ⟨?_, ih gates.2 rzero⟩
      by_cases ha : s.aux i p = .error
      · by_cases hm : s.main i = .ready
        · have positive := f.section_error_positive box i p
            ⟨ha, hm, fun t ht => ⟨(gates.1 t ht i).1, (gates.1 t ht i).2.2 p⟩⟩
          exact False.elim (by linarith)
        · exact Or.inr hm
      · exact Or.inl ha
    | jump j =>
      apply ih gates
      simpa only [Execution.ledger, Move.ledger, Ledger.add, j.no_actuation.1, zero_add]
        using zero_dose

theorem Execution.mark_inactive_of_zero_open {n θ ε route s u}
    (e : @Execution n θ route s u) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen e) (i : Fin n) (p : Port)
    (zero_dose : e.ledger.mark i p = 0) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .mark ∨ v.main i = .ready) := by
  induction e with
  | nil => trivial
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      change f.ledger.mark i p + rest.ledger.mark i p = 0 at zero_dose
      have nf := f.section_mark_nonnegative box i p
      have nr := rest.section_mark_nonnegative box i p
      have fzero : f.ledger.mark i p = 0 := by linarith
      have rzero : rest.ledger.mark i p = 0 := by linarith
      refine ⟨?_, ih gates.2 rzero⟩
      by_cases ha : s.aux i p = .mark
      · by_cases hm : s.main i = .ready
        · exact Or.inr hm
        · have positive := f.section_mark_positive box i p
            ⟨ha, hm, fun t ht => ⟨(gates.1 t ht i).1, (gates.1 t ht i).2.1⟩⟩
          exact False.elim (by linarith)
      · exact Or.inl ha
    | jump j =>
      apply ih gates
      simpa only [Execution.ledger, Move.ledger, Ledger.add, j.no_mark_actuation, zero_add]
        using zero_dose

theorem Execution.error_cover_of_zero_open {n θ ε route s u}
    (e : @Execution n θ route s u) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen e) (i : Fin n) (p : Port)
    (zero_dose : e.ledger.error i p = 0) :
    ∃ cover : ErrorSectionCover i p e, cover.count = 0 := by
  let inactive := e.error_inactive_of_zero_open box gates i p zero_dose
  exact ⟨e.errorCover_of_inactive i p inactive, e.errorCover_of_inactive_count i p inactive⟩

theorem Execution.mark_cover_of_zero_open {n θ ε route s u}
    (e : @Execution n θ route s u) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen e) (i : Fin n) (p : Port)
    (zero_dose : e.ledger.mark i p = 0) :
    ∃ cover : MarkSectionCover i p e, cover.count = 0 := by
  let inactive := e.mark_inactive_of_zero_open box gates i p zero_dose
  exact ⟨e.markCover_of_inactive i p inactive, e.markCover_of_inactive_count i p inactive⟩

theorem Execution.error_cover_of_unchanged_gain {n θ ε route s u}
    (e : @Execution n θ route s u) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen e) (i : Fin n) (p : Port)
    (unchanged : u.x i (.z p) = s.x i (.z p)) :
    ∃ cover : ErrorSectionCover i p e, cover.count = 0 := by
  apply e.error_cover_of_zero_open box gates i p
  have balance := e.gain_balance i p
  linarith

/-- Recovery sums nonnegative port contributions. Preserved recovery therefore
forces every port's MARK actuation to be structurally inactive under open gates. -/
theorem Execution.mark_cover_of_unchanged_recovery {n θ ε route s u}
    (e : @Execution n θ route s u) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen e) (i : Fin n) (p : Port)
    (unchanged : u.x i .b = s.x i .b) :
    ∃ cover : MarkSectionCover i p e, cover.count = 0 := by
  apply e.mark_cover_of_zero_open box gates i p
  have sum_zero : (∑ q : Port, e.ledger.mark i q) = 0 := by
    rw [← e.recovery_sum_marks i]
    have balance := e.recovery_balance i
    linarith
  have upper : e.ledger.mark i p ≤ ∑ q : Port, e.ledger.mark i q :=
    Finset.single_le_sum (fun q _ => e.section_mark_nonnegative box i q) (Finset.mem_univ p)
  have lower := e.section_mark_nonnegative box i p
  linarith

#print axioms Execution.error_cover_of_zero_open
#print axioms Execution.mark_cover_of_zero_open

end KernelR.Hybrid
