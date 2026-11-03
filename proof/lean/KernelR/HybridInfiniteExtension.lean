import KernelR.HybridChainProgress

/-!
# Coherent infinite extension by actual finite segments

This module constructs continuations at successive unit-spaced model times.
Every step is an actual finite execution, and every accumulated execution
retains the supplied initial prefix by `Execution.append`. The unit spacing
is a choice of audit horizons, not an added physical clock or pulse source.

The conclusion is existence of a time-divergent extension. It does not assert
that every infinite move presentation is maximal or has divergent time.
-/
namespace KernelR.Hybrid

/-- A finite history from a fixed starting snapshot. -/
structure ReachableEndpoint {n} (θ : Fin n → Parameters) (route : Router n)
    (start : Snapshot n) where
  state : Snapshot n
  history : Execution θ route start state

/-- One actual unit-time continuation, including terminal saturation, after
an accumulated local history. The original global prefix is retained.
-/
structure UnitContinuation {n θ route born start}
    (initialRun : @Execution n θ route born start)
    (current : ReachableEndpoint θ route start) where
  final : Snapshot n
  tail : Execution θ route current.state final
  date : final.time = current.state.time + 1
  complete : CompleteThrough ((initialRun.append current.history).append tail)
    (current.state.time + 1)

def UnitContinuation.next {n θ route born start}
    {initialRun : @Execution n θ route born start}
    {current : ReachableEndpoint θ route start}
    (step : UnitContinuation initialRun current) : ReachableEndpoint θ route start :=
  ⟨step.final, current.history.append step.tail⟩

/-- A countable sequence of actual finite segments. Consecutive accumulated
histories are joined by append, rather than chosen independently at each date.
The first accumulated local history is empty, preserving the given prefix.
-/
structure CoherentInfiniteExtension {n θ route born start}
    (initialRun : @Execution n θ route born start) where
  endpoint : ℕ → ReachableEndpoint θ route start
  initial : endpoint 0 = ⟨start, .nil start⟩
  segment : ∀ k, Execution θ route (endpoint k).state (endpoint (k + 1)).state
  append_step : ∀ k,
    (endpoint (k + 1)).history = (endpoint k).history.append (segment k)
  unit_step : ∀ k, (endpoint (k + 1)).state.time = (endpoint k).state.time + 1
  complete_step : ∀ k,
    CompleteThrough (initialRun.append (endpoint (k + 1)).history)
      (endpoint (k + 1)).state.time

namespace CoherentInfiniteExtension

def fullPrefix {n θ route born start}
    {initialRun : @Execution n θ route born start}
    (extension : CoherentInfiniteExtension initialRun) (k : ℕ) :
    Execution θ route born (extension.endpoint k).state :=
  initialRun.append (extension.endpoint k).history

/-- Every accumulated global execution contains the original finite prefix.
No rebasing, replacement or independent horizon choice occurs in the history.
-/
theorem retains_prefix {n θ route born start}
    {initialRun : @Execution n θ route born start}
    (extension : CoherentInfiniteExtension initialRun) (k : ℕ) :
    (extension.fullPrefix k).IsPrefix initialRun :=
  Execution.IsPrefix.append_left initialRun (extension.endpoint k).history

/-- The actual finite segments link the accumulated global histories too. -/
theorem fullPrefix_append {n θ route born start}
    {initialRun : @Execution n θ route born start}
    (extension : CoherentInfiniteExtension initialRun) (k : ℕ) :
    extension.fullPrefix (k + 1) =
      (extension.fullPrefix k).append (extension.segment k) := by
  unfold fullPrefix
  rw [extension.append_step]
  exact (Execution.append_assoc initialRun (extension.endpoint k).history
    (extension.segment k)).symm

/-- Dates are derived from the constructed local steps and their initial date.
Time divergence is not assumed as a condition on an existing infinite run.
-/
theorem endpoint_date {n θ route born start}
    {initialRun : @Execution n θ route born start}
    (extension : CoherentInfiniteExtension initialRun) (k : ℕ) :
    (extension.endpoint k).state.time = start.time + (k : ℝ) := by
  induction k with
  | zero => simp only [extension.initial, Nat.cast_zero, add_zero]
  | succ k ih =>
    rw [extension.unit_step, ih]
    push_cast
    ring

/-- Each positive-index accumulated prefix is saturated at its scheduled date.
The caller's original prefix, at index zero, need not already be complete.
-/
theorem prefix_complete {n θ route born start}
    {initialRun : @Execution n θ route born start}
    (extension : CoherentInfiniteExtension initialRun) (k : ℕ) :
    CompleteThrough (extension.fullPrefix (k + 1))
      (start.time + ((k + 1 : ℕ) : ℝ)) := by
  have complete := extension.complete_step k
  rw [extension.endpoint_date] at complete
  exact complete

/-- After some index all subsequent actual endpoints lie beyond any chosen
finite physical horizon. This follows from the endpoint-date theorem.
-/
theorem time_diverges {n θ route born start}
    {initialRun : @Execution n θ route born start}
    (extension : CoherentInfiniteExtension initialRun) :
    ∀ horizon : ℝ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      horizon < (extension.endpoint k).state.time := by
  intro horizon
  obtain ⟨K, beyond⟩ := exists_nat_gt (horizon - start.time)
  refine ⟨K, fun k after => ?_⟩
  rw [extension.endpoint_date]
  have ordered : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast after
  linarith

end CoherentInfiniteExtension

private def continuationSequence {n θ route born start}
    (initialRun : @Execution n θ route born start)
    (select : ∀ current : ReachableEndpoint θ route start,
      UnitContinuation initialRun current) : ℕ → ReachableEndpoint θ route start
  | 0 => ⟨start, .nil start⟩
  | k + 1 => (select (continuationSequence initialRun select k)).next

/-- From the finite-chain witness, construct a coherent time-divergent
continuation of any given finite actual execution of that same protocol.
Only existence of finite physical continuations is used in the recursion.
-/
theorem ConstructedBirthCadenceChain.infinite_extension_exists
    {n θ bornCells K sigma centre delay T ε}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (box : PhysicalBox θ ε) {start}
    (initialRun : Execution θ chain.router (familyPreparationBornSource bornCells K) start) :
    Nonempty (CoherentInfiniteExtension initialRun) := by
  classical
  have available : ∀ current : ReachableEndpoint θ chain.router start,
      Nonempty (UnitContinuation initialRun current) := by
    intro current
    obtain ⟨final, tail, date, complete⟩ :=
      chain.progress_one_time_unit box (initialRun.append current.history)
    exact ⟨⟨final, tail, date, complete⟩⟩
  let select := fun current => Classical.choice (available current)
  let nodes := continuationSequence initialRun select
  refine ⟨{
    endpoint := nodes
    initial := rfl
    segment := fun k => (select (nodes k)).tail
    append_step := fun k => rfl
    unit_step := fun k => (select (nodes k)).date
    complete_step := ?_
  }⟩
  intro k
  change CompleteThrough (initialRun.append ((select (nodes k)).next).history)
    (select (nodes k)).final.time
  rw [(select (nodes k)).date]
  exact (select (nodes k)).complete

#print axioms ConstructedBirthCadenceChain.infinite_extension_exists
#print axioms CoherentInfiniteExtension.time_diverges

end KernelR.Hybrid
