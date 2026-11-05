import KernelR.Family.Model

/-! Actual quiet witnesses for the parametric cell semantics. These witnesses
show non-vacuity of safe flows and complete executions for every admissible
constant family. They contain no learning, source pulses or FIRE events and
do not establish the nominal training protocol at nonnominal constants. -/
namespace KernelR.Family
open KernelR.Hybrid MeasureTheory

/-- A source-free READY state at the family member's own equilibria. Recovery
is zero, the log-gains are zero, and no cap or fabrication-rate premise is needed
because both learning actuators are structurally inactive. -/
noncomputable def quiet {n : ℕ} (c : Constants) (t : ℝ) : Snapshot n :=
  ⟨t, (fun _ k => match k with
    | .q => c.rest
    | .m _ => c.auxRest
    | .z _ => 0
    | .b => 0
    | .energy => c.energyTarget),
   fun _ => .ready, fun _ _ => .ready, fun _ _ => none, []⟩

theorem quiet_field {n} (c : Constants) (θ : Fin n → Parameters)
    (s t : ℝ) (i : Fin n) (k : Coord) :
    field c θ (quiet c s) (quiet c s).x t i k = 0 := by
  cases k <;> simp [field, quiet, drive, current, work, errorAct, markAct]

/-- A positive-duration integral ODE flow, with actual guards and queue rules.
This is an existence witness for the quiet regime only. -/
noncomputable def quietFlow {n} (c : Constants) (hc : Admissible c)
    (θ : Fin n → Parameters) {T : ℝ} (hT : 0 < T) :
    Flow c θ (quiet c 0) (quiet c T) where
  positive := hT
  path := fun _ => (quiet c 0).x
  initial := rfl
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun _ _ => continuousOn_const
  integrable := by
    intros
    simp only [quiet_field]
    exact intervalIntegrable_const
  mark_integrable := by intros; simp [markAct, quiet]
  integral_eq := by intros; simp [quiet_field]
  guards := by
    intro t ht
    change (∀ i : Fin n, c.rest < c.threshold) ∧
      ∀ (i : Fin n) (p : Port), c.auxRest < c.auxThreshold
    exact ⟨fun _ => hc.fastExit_gt_rest.trans hc.threshold_gt_fastExit,
      fun _ _ => hc.errorLevel_gt_rest.trans
        (hc.markExit_gt_error.trans hc.auxThreshold_gt_mark)⟩
  raw_support := by intros; simp_all [quiet]
  pending_urgent := by intros; simp_all [quiet]

theorem quietFlow_safe {n} (c : Constants) (hc : Admissible c)
    (θ : Fin n → Parameters) {T : ℝ} (hT : 0 < T) :
    (quietFlow c hc θ hT).Safe := by
  intro t ht i
  change 0 < c.energyTarget ∧ 0 ≤ (0 : ℝ) ∧ ∀ p : Port, 0 ≤ c.auxRest
  exact ⟨hc.energyTarget_pos, le_refl _, fun _ => hc.auxRest_pos.le⟩

theorem quiet_no_jump {n} (c : Constants) (hc : Admissible c)
    {route : Router n} {T : ℝ} {u : Snapshot n} :
    IsEmpty (Jump c route (quiet c T) u) := by
  have hq : c.rest ≠ c.threshold :=
    ne_of_lt (hc.fastExit_gt_rest.trans hc.threshold_gt_fastExit)
  have hm : c.auxRest ≠ c.auxThreshold :=
    ne_of_lt (hc.errorLevel_gt_rest.trans
      (hc.markExit_gt_error.trans hc.auxThreshold_gt_mark))
  constructor
  intro j
  cases j <;> simp_all [quiet]

/-- Every admissible member has an actual safe flow through every positive
horizon, for arbitrary fabrication parameters. This does not assert learning. -/
theorem safe_quiet_flow_exists {n} (c : Constants) (hc : Admissible c)
    (θ : Fin n → Parameters) {T : ℝ} (hT : 0 < T) :
    ∃ f : Flow c θ (quiet c 0) (quiet c T), f.Safe :=
  ⟨quietFlow c hc θ hT, quietFlow_safe c hc θ hT⟩

/-- A complete quiet execution exists with any supplied router. It issues no
tokens, so the router is never called. This is not a training witness. -/
theorem quiet_complete_exists {n} (c : Constants) (hc : Admissible c)
    (θ : Fin n → Parameters) (route : Router n) {T : ℝ} (hT : 0 < T) :
    ∃ e : Execution c θ route (quiet c 0) (quiet c T), CompleteThrough e T := by
  refine ⟨.cons (.flow (quietFlow c hc θ hT)) (.nil _), rfl, ?_, ?_⟩
  · intro u
    exact quiet_no_jump c hc
  · simp [quiet]

/-- The positive two-parameter learning-factor family also has safe actual
quiet flows. This non-vacuity statement does not claim active learning for all
those members or preservation of the nominal cadence protocol. -/
theorem learning_factor_family_quiet_flows {n} (θ : Fin n → Parameters)
    {T : ℝ} (hT : 0 < T) {gain recovery : ℝ}
    (hg : 0 < gain) (hr : 0 < recovery) :
    ∃ f : Flow (nominal.withLearningFactors gain recovery) θ
      (quiet (nominal.withLearningFactors gain recovery) 0)
      (quiet (nominal.withLearningFactors gain recovery) T), f.Safe :=
  safe_quiet_flow_exists _ (nominal_admissible.withLearningFactors hg hr) θ hT

#print axioms safe_quiet_flow_exists
#print axioms quiet_complete_exists
#print axioms learning_factor_family_quiet_flows

end KernelR.Family
