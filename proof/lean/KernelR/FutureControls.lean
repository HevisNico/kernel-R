import KernelR.Indefinite
import KernelR.LearnedResponse

/-! Concrete controls and proved counterexamples for the future-operation
boundary. Negative controls prove the negation of an overclaim; they do not
merely fail to apply an existing theorem to a changed signature. -/
namespace KernelR.FutureControls
open KernelR.Hybrid

noncomputable def parameters : Fin 1 → Parameters := fun _ =>
  ⟨fun _ => 4, fun _ => Real.log (5/4) / (1/50),
   fun _ => Real.log 8 / (53/50), fun _ => a / (3/20),
   fun _ => (1-1/40) / response (1/50)⟩

theorem parameters_box : PhysicalBox parameters (1/10) := by
  have selfbox (x : ℝ) (hx : 0 ≤ x) : InRelativeBox (1/10) x x := by
    constructor <;> nlinarith
  have hr : 0 < response (1/50) := lt_of_lt_of_le (by norm_num) sensor_response_lower
  refine ⟨Or.inr rfl, fun _ _ => ⟨selfbox _ (by norm_num),
    selfbox _ (div_nonneg (Real.log_pos (by norm_num)).le (by norm_num)),
    selfbox _ (div_nonneg (Real.log_pos (by norm_num)).le (by norm_num)),
    selfbox _ (div_nonneg (by linarith [a_coarse_bounds.1]) (by norm_num)),
    selfbox _ (div_nonneg (by norm_num) hr.le)⟩⟩

noncomputable def learned : Snapshot 1 :=
  ⟨0, (fun _ c => match c with
    | .q => 1/10 | .m _ => 1/40 | .z _ => Real.log (37/20)
    | .b => 9/50 | .energy => 50),
   fun _ => .ready, fun _ _ => .ready, fun _ _ => none, []⟩

theorem learned_section : LearnedRest parameters (fun _ => 0) learned where
  main := by intro i; rfl
  aux := by intro i p; rfl
  raw := by intro i p; rfl
  pending := rfl
  charge := by intro i; rfl
  sensor := by intro i p; norm_num [learned]
  reserve := by intro i; norm_num [learned]
  gain := by intro i; norm_num [learned, Real.exp_log (by norm_num : (0:ℝ) < 37/20)]
  cap := by
    intro i p
    exact Real.log_le_log (by norm_num : (0:ℝ) < 37/20) (by norm_num : (37/20:ℝ) ≤ 4)
  recovery := by intro i; norm_num [learned]

theorem positive_learned_idle :
    ∃ e : Execution parameters (fun _ _ => []) learned (idleAt learned 1),
      CompleteThrough e 1 ∧ LearnedRest parameters (fun _ => 0) (idleAt learned 1) ∧
      e.ledger.emissions = [] :=
  learned_idle_complete learned_section (by norm_num [learned])

theorem stronger_reserve_floor_is_false :
    ¬ (∀ T, learned.time ≤ T → (51:ℝ) ≤ (idleAt learned T).x 0 .energy) := by
  intro h
  have hh := h 0 (by norm_num [learned])
  norm_num [idleAt, idleValues, learned] at hh

def zeroGapSchedule : FutureSchedule 0 := ⟨fun _ => 0, fun _ => by norm_num⟩

theorem nonpositive_gap_does_not_give_unbounded_dates :
    ¬ (∀ T : ℝ, ∃ k, T ≤ zeroGapSchedule.time k) := by
  intro h
  obtain ⟨k, hk⟩ := h 1
  norm_num [zeroGapSchedule] at hk

theorem weak_gain_is_not_a_learned_response :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → learnedHead (3/10) t < 1 := by
  intro t ht htime
  have hr := response_linear_upper ht
  have hat := mul_le_mul_of_nonneg_right a_coarse_bounds.2.le ht
  have hu : response t ≤ (7/5:ℝ) := by linarith
  dsimp [learnedHead]
  linarith

/-- Adding a token due exactly at the old endpoint preserves the old execution
but destroys its terminal saturation. The continuation must consume that token. -/
theorem due_now_requires_continuation :
    ∃ e : Execution parameters (fun _ _ => [])
      (withFuture learned [sourceToken 0 0 1])
      (withFuture (idleAt learned 1) [sourceToken 0 0 1]), ¬ CompleteThrough e 1 := by
  obtain ⟨wait, _, _, _⟩ := positive_learned_idle
  let e := wait.withFuture [sourceToken 0 0 1] (by
    intro d hd; have he := List.mem_singleton.mp hd; subst d; exact le_rfl)
  refine ⟨e, ?_⟩
  intro hc
  have h := hc.2.2 (sourceToken 0 0 1) (by simp [withFuture])
  norm_num [sourceToken] at h

end KernelR.FutureControls
