import KernelR.HybridMaximalProgress
import KernelR.HybridQuietFlowExistence

/-!
# A physical control against counting flow subdivisions as Zeno events

One actual R cell starts at an admissible READY birth with no incoming
currents or queued inputs. Its constant quiet trajectory is presented at
the increasing dates `1 - (1/2)^k`. The resulting infinite list of legal
moves stays below time one and contains no physical jumps. It therefore
refutes an unrestricted time-divergence claim about all move presentations,
without refuting physical-event non-Zeno or semantic maximal progress.
-/
namespace KernelR.Hybrid.Controls

noncomputable def restingValues : Values 1 := fun _ coordinate =>
  match coordinate with
  | .q => 1 / 10
  | .m _ => 1 / 40
  | .z port => Real.log (nominalGain port)
  | .b => 2 / 25
  | .energy => 100

noncomputable def restingState (time : ℝ) : Snapshot 1 where
  time := time
  x := restingValues
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := []

theorem resting_birth : BirthState (restingState 0) := by
  refine ⟨rfl, fun _ _ => rfl, ?_⟩
  intro cell
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · norm_num [restingState, restingValues]
  · norm_num [restingState, restingValues]
  · norm_num [restingState, restingValues]
  · intro port
    constructor
    · change Real.log (nominalGain port) - 1 / 100000 ≤ Real.log (nominalGain port) ∧
        Real.log (nominalGain port) ≤ Real.log (nominalGain port) + 1 / 100000
      constructor <;> linarith
    · left
      norm_num [restingState, restingValues]

theorem resting_quietAt (start finish : ℝ) :
    quietAt (restingState start) finish = restingState finish := by
  have values : quietValues (restingState start) finish = restingValues := by
    funext cell coordinate
    cases coordinate <;> simp [quietValues, restingState, restingValues, relax]
  change { restingState start with time := finish, x := quietValues (restingState start) finish } =
    restingState finish
  rw [values]
  rfl

/-- A positive quiet interval of this cell uses the actual R integral flow. -/
noncomputable def restingFlow (θ : Fin 1 → Parameters) (start finish : ℝ)
    (later : start < finish) : Flow θ (restingState start) (restingState finish) := by
  let flow : Flow θ (restingState start) (quietAt (restingState start) finish) :=
    quietFlow (restingState start) later
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (by intro cell; norm_num [restingState, restingValues])
      (by intro cell port; norm_num [restingState, restingValues])
      (by intro delivery member; simp [restingState] at member)
  simpa only [resting_quietAt] using flow

/-- No physical jump is being starved in this control: none is enabled.
Fairness for jumps alone therefore cannot force the presentation past time one.
-/
theorem resting_no_jump (time : ℝ) (next : Snapshot 1) :
    IsEmpty (Jump (fun _ _ => []) (restingState time) next) := by
  exact ready_no_jump (restingState time)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by intro cell; norm_num [restingState, restingValues])
    (by intro cell port; norm_num [restingState, restingValues])
    (by intro delivery member; simp [restingState] at member) next

noncomputable def subdivisionDate (index : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ index

theorem subdivisionDate_zero : subdivisionDate 0 = 0 := by
  norm_num [subdivisionDate]

theorem subdivisionDate_strict (index : ℕ) :
    subdivisionDate index < subdivisionDate (index + 1) := by
  have positive : (0 : ℝ) < (1 / 2 : ℝ) ^ index := pow_pos (by norm_num) _
  simp only [subdivisionDate, pow_succ]
  nlinarith

theorem subdivisionDate_bounded (index : ℕ) : subdivisionDate index < 1 := by
  have positive : (0 : ℝ) < (1 / 2 : ℝ) ^ index := pow_pos (by norm_num) _
  dsimp [subdivisionDate]
  linarith

/-- The same construction works for every supplied physical parameter family;
the quiet flow does not inspect the unused rates or gains of the parameters. -/
noncomputable def boundedFlowRun (θ : Fin 1 → Parameters) :
    InfiniteExecution θ (fun _ _ => []) where
  state := fun index => restingState (subdivisionDate index)
  move := fun index => .flow (restingFlow θ _ _ (subdivisionDate_strict index))

theorem boundedFlowRun_birth (θ : Fin 1 → Parameters) :
    BirthState ((boundedFlowRun θ).state 0) := by
  simpa only [boundedFlowRun, subdivisionDate_zero] using resting_birth

theorem boundedFlowRun_time_lt_one (θ : Fin 1 → Parameters) (index : ℕ) :
    ((boundedFlowRun θ).state index).time < 1 := subdivisionDate_bounded index

theorem boundedFlowRun_no_jumps (θ : Fin 1 → Parameters) (index : ℕ) :
    ((boundedFlowRun θ).finitePrefix index).jumpCount = 0 := by
  induction index with
  | zero => rfl
  | succ index ih =>
    rw [InfiniteExecution.prefix_jumpCount_succ, ih]
    rfl

/-- An infinite admissible move presentation may stay at bounded times even
from a genuine R birth. Hence physical jumps, not all moves, must be counted. -/
theorem bounded_infinite_flow_control (θ : Fin 1 → Parameters) :
    ∃ run : InfiniteExecution θ (fun _ _ => []),
      BirthState (run.state 0) ∧
      (∀ index, (run.state index).time < 1) ∧
      (∀ index, (run.finitePrefix index).jumpCount = 0) :=
  ⟨boundedFlowRun θ, boundedFlowRun_birth θ,
    boundedFlowRun_time_lt_one θ, boundedFlowRun_no_jumps θ⟩

theorem boundedFlowRun_not_infinitely_many_jumps (θ : Fin 1 → Parameters) :
    ¬ (boundedFlowRun θ).InfinitelyManyJumps := by
  intro events
  obtain ⟨index, positive⟩ := events 0
  rw [boundedFlowRun_no_jumps] at positive
  exact Nat.lt_irrefl 0 positive

/-- A claim about all infinite move presentations would already fail for
this one-cell, source-free router, even with a true birth-state premise. -/
theorem unrestricted_infinite_progress_false (θ : Fin 1 → Parameters) :
    ¬ (∀ run : InfiniteExecution θ (fun _ _ => []),
      BirthState (run.state 0) → ∀ horizon : ℝ, ∃ index,
        horizon < (run.state index).time) := by
  intro claim
  obtain ⟨index, later⟩ := claim (boundedFlowRun θ) (boundedFlowRun_birth θ) 1
  have earlier := boundedFlowRun_time_lt_one θ index
  linarith

/-- The underlying resting trajectory itself has a legal continuation past
the presentation's accumulation time. No new source or physical reset is used. -/
theorem resting_continues_past_one (θ : Fin 1 → Parameters) :
    Nonempty (Flow θ (restingState 1) (restingState 2)) :=
  ⟨restingFlow θ 1 2 (by norm_num)⟩

/-- The actual bounded subdivision control admits the new semantic extension. -/
theorem boundedFlowRun_has_limit_extension (θ : Fin 1 → Parameters) {ε}
    (box : PhysicalBox θ ε) : Nonempty (boundedFlowRun θ).FlowLimitExtension := by
  have starts : (boundedFlowRun θ).state 0 = restingState 0 := by
    simp only [boundedFlowRun, subdivisionDate_zero]
  have flow : Flow θ ((boundedFlowRun θ).state 0) (restingState 2) := by
    rw [starts]
    exact restingFlow θ 0 2 (by norm_num)
  let reference : Execution θ (fun _ _ => []) ((boundedFlowRun θ).state 0)
      (restingState 2) := .cons (.flow flow) (.nil _)
  have complete : CompleteThrough reference 2 :=
    ⟨rfl, resting_no_jump 2, by simp [restingState]⟩
  have fanout : FanoutBound (fun (_ : Fin 1) (_ : ℝ) => []) 0 := fun _ _ => le_rfl
  exact (boundedFlowRun θ).flow_limit_extension_exists (boundedFlowRun_birth θ)
    box fanout reference complete 1 (fun k => (boundedFlowRun_time_lt_one θ k).le)
    (by norm_num)

/-- A prefix already later than a reference horizon cannot be continued
backwards to it. This controls the endpoint guard of finite continuation. -/
theorem no_past_horizon_continuation (θ : Fin 1 → Parameters) :
    ¬ (∃ final, ∃ tail : Execution θ (fun _ _ => []) (restingState 2) final,
      CompleteThrough tail 1) := by
  rintro ⟨final, tail, complete⟩
  have forward := tail.time_monotone
  change (2 : ℝ) ≤ final.time at forward
  have date := complete.1
  linarith

#print axioms bounded_infinite_flow_control
#print axioms unrestricted_infinite_progress_false
#print axioms boundedFlowRun_has_limit_extension
#print axioms no_past_horizon_continuation

end KernelR.Hybrid.Controls
