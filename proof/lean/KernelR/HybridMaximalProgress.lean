import KernelR.HybridBoundedRun
import KernelR.HybridChainProgress

/-!
# Progress under extension at a flow limit

A bounded presentation can be continued when its final subdivisions fit one
actual flow to their limit and that state has a strictly later continuation.
The witness retains the original finite history up to the start of that flow
and matches the original flow paths on every remaining interval.
-/
namespace KernelR.Hybrid
open Set Filter
open scoped Topology

/-- Select a flow reaching a given date from the left. At a guard this
selects the incoming flow and retains its pre-jump endpoint. -/
private theorem Execution.left_flow_at {n θ route s u}
    (history : @Execution n θ route s u) (L : ℝ)
    (afterStart : s.time < L) (beforeEnd : L ≤ u.time) :
    ∃ a b, ∃ _prior : Execution θ route s a, ∃ _flow : Flow θ a b,
      a.time < L ∧ L ≤ b.time := by
  induction history with
  | nil => exact False.elim (not_lt_of_ge beforeEnd afterStart)
  | @cons s m u move rest ih =>
    by_cases reaches : L ≤ m.time
    · cases move with
      | jump jump =>
        exact False.elim (not_lt_of_ge (by simpa only [jump.time_unchanged] using reaches) afterStart)
      | flow flow => exact ⟨s, m, .nil s, flow, afterStart, reaches⟩
    · obtain ⟨a, b, prior, flow, ha, hb⟩ := ih (lt_of_not_ge reaches) beforeEnd
      exact ⟨a, b, .cons move prior, flow, ha, hb⟩

namespace InfiniteExecution

/-- A continuation through a finite accumulation date. The retained history
is the actual finite prefix at `anchor` followed by `incoming`. The path
agreement includes the full snapshots on the closed original intervals. -/
structure FlowLimitExtension {n θ route} (run : @InfiniteExecution n θ route) where
  anchor : ℕ
  limit : Snapshot n
  incoming : Flow θ (run.state anchor) limit
  dates : Tendsto (fun k => (run.state k).time) atTop (𝓝 limit.time)
  agrees : ∀ k, anchor ≤ k →
    ∃ flow : Flow θ (run.state k) (run.state (k + 1)),
      run.move k = .flow flow ∧
      Icc (run.state k).time (run.state (k + 1)).time ⊆
        Icc (run.state anchor).time limit.time ∧
      ∀ t ∈ Icc (run.state k).time (run.state (k + 1)).time,
        flow.at t = incoming.at t
  final : Snapshot n
  continuation : Execution θ route limit final
  progresses : limit.time < final.time

/-- The finite execution obtained by retaining the anchor history and
completing its final flow before taking the continuation. -/
def FlowLimitExtension.execution {n θ route} {run : @InfiniteExecution n θ route}
    (extension : run.FlowLimitExtension) :
    Execution θ route (run.state 0) extension.final :=
  (run.finitePrefix extension.anchor).append
    (.cons (.flow extension.incoming) extension.continuation)

/-- The incoming endpoint gives the coordinate limits of the presentation. -/
theorem FlowLimitExtension.coordinates_tendsto {n θ route}
    {run : @InfiniteExecution n θ route} (extension : run.FlowLimitExtension)
    (i : Fin n) (c : Coord) :
    Tendsto (fun k => (run.state k).x i c) atTop (𝓝 (extension.limit.x i c)) := by
  have inside : ∀ᶠ k in atTop, (run.state k).time ∈
      Icc (run.state extension.anchor).time extension.limit.time := by
    filter_upwards [eventually_ge_atTop extension.anchor] with k hk
    obtain ⟨_, _, sub, _⟩ := extension.agrees k hk
    exact sub ⟨le_rfl, run.time_monotone (Nat.le_succ k)⟩
  have atLimit : extension.limit.time ∈
      Icc (run.state extension.anchor).time extension.limit.time :=
    ⟨extension.incoming.positive.le, le_rfl⟩
  have along : Tendsto (fun k => extension.incoming.path (run.state k).time i c)
      atTop (𝓝 (extension.incoming.path extension.limit.time i c)) :=
    (extension.incoming.continuous i c extension.limit.time atLimit).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨extension.dates, inside⟩)
  rw [extension.incoming.final] at along
  apply along.congr'
  filter_upwards [eventually_ge_atTop extension.anchor] with k hk
  obtain ⟨flow, _, _, same⟩ := extension.agrees k hk
  have eq := congrArg (fun s : Snapshot n => s.x i c)
    (same (run.state k).time ⟨le_rfl, run.time_monotone (Nat.le_succ k)⟩)
  change flow.path (run.state k).time i c =
    extension.incoming.path (run.state k).time i c at eq
  rw [flow.initial] at eq
  exact eq.symm

/-- A flow starting at an actual late state determines all further flow
subdivisions up to its endpoint. This uses uniqueness on each interval. -/
private theorem follows_incoming {n θ ε route}
    (run : @InfiniteExecution n θ route)
    (box : PhysicalBox θ ε) (initial : PhysicalInvariant θ (run.state 0))
    (K : ℕ) {limit : Snapshot n} (incoming : Flow θ (run.state K) limit)
    (before : ∀ k, (run.state k).time < limit.time)
    (flows : ∀ k, K ≤ k → (run.move k).jumpCount = 0) :
    ∀ k, K ≤ k →
      ∃ f : Flow θ (run.state k) (run.state (k + 1)),
        run.move k = .flow f ∧
        Icc (run.state k).time (run.state (k + 1)).time ⊆
          Icc (run.state K).time limit.time ∧
        ∀ t ∈ Icc (run.state k).time (run.state (k + 1)).time,
          f.at t = incoming.at t := by
  have step_agrees (k : ℕ) (hk : K ≤ k)
      (atStart : incoming.at (run.state k).time = run.state k)
      (flow : Flow θ (run.state k) (run.state (k + 1))) :
      ∀ t ∈ Icc (run.state k).time (run.state (k + 1)).time,
        flow.at t = incoming.at t := by
    intro t ht
    let common := incoming.suffix (run.time_monotone hk) (before k)
    have rebasing : (incoming.at (run.state k).time).ObservationalEq (run.state k) := by
      rw [atStart]
      exact Snapshot.ObservationalEq.refl _
    let comparison := common.rebase_observational rebasing
    have values := flow.path_unique comparison box
      ((run.finitePrefix k).physical_invariant box initial) ht
      ⟨ht.1, ht.2.trans (before (k + 1)).le⟩
    change flow.path t = incoming.path t at values
    change { run.state k with time := t, x := flow.path t } =
      { run.state K with time := t, x := incoming.path t }
    rw [values, ← atStart]
    rfl
  have path_at : ∀ k, K ≤ k → incoming.at (run.state k).time = run.state k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      change { run.state K with x := incoming.path (run.state K).time } = run.state K
      rw [incoming.initial]
    | succ k hk ih =>
      have zero := flows k hk
      cases actual : run.move k with
      | jump jump => simp [actual, Move.jumpCount] at zero
      | flow flow =>
        have same := step_agrees k hk ih flow _ ⟨flow.positive.le, le_rfl⟩
        rw [flow.at_final] at same
        exact same.symm
  intro k hk
  have zero := flows k hk
  cases actual : run.move k with
  | jump jump => simp [actual, Move.jumpCount] at zero
  | flow flow =>
    exact ⟨flow, rfl,
      Icc_subset_Icc (run.time_monotone hk) (before (k + 1)).le,
      step_agrees k hk (path_at k hk) flow⟩

/-- Every bounded presentation with a sufficiently long complete reference
has a continuation through its physical limit. -/
theorem flow_limit_extension_exists {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) {u H}
    (reference : Execution θ route (run.state 0) u)
    (complete : CompleteThrough reference H)
    (B : ℝ) (bounded : ∀ k, (run.state k).time ≤ B) (later : B < H) :
    Nonempty run.FlowLimitExtension := by
  classical
  obtain ⟨K, zero⟩ := run.eventually_zero_jumpCount_of_time_bounded birth box fanout B bounded
  let L : ℝ := ⨆ k, (run.state k).time
  have bdd : BddAbove (range (fun k => (run.state k).time)) :=
    ⟨B, by rintro _ ⟨k, rfl⟩; exact bounded k⟩
  have leLimit (k : ℕ) : (run.state k).time ≤ L := le_ciSup bdd k
  have ltLimit (k : ℕ) : (run.state k).time < L := by
    let j := max k K
    have count := zero j (le_max_right _ _)
    cases actual : run.move j with
    | jump jump => simp [actual, Move.jumpCount] at count
    | flow flow =>
      exact (run.time_monotone (le_max_left k K)).trans_lt
        (flow.positive.trans_le (leLimit (j + 1)))
  have limitBound : L ≤ B := ciSup_le bounded
  have limitBefore : L < H := limitBound.trans_lt later
  obtain ⟨a, b, prior, flow, left, right⟩ :=
    reference.left_flow_at L (ltLimit 0) (by rw [complete.1]; exact limitBefore.le)
  have hasAnchor : ∃ k, a.time < (run.state k).time := by
    by_contra no
    push Not at no
    exact (not_lt_of_ge (ciSup_le no)) left
  obtain ⟨k, after⟩ := hasAnchor
  let A := max k K
  have inside : a.time < (run.state A).time :=
    after.trans_le (run.time_monotone (le_max_left _ _))
  have before : (run.state A).time < b.time := (ltLimit A).trans_le right
  let piece := flow.prefix inside before.le
  let cut := prior.append (Execution.cons (.flow piece) (.nil _))
  let remains := flow.suffix inside.le before
  have cutComplete : CompleteThrough cut (run.state A).time :=
    ⟨rfl, remains.no_initial_jump, remains.initial_pending_strict⟩
  have runComplete : CompleteThrough (run.finitePrefix A) (run.state A).time := by
    have count := zero A (le_max_right _ _)
    cases actual : run.move A with
    | jump jump => simp [actual, Move.jumpCount] at count
    | flow next => exact ⟨rfl, next.no_initial_jump, next.initial_pending_strict⟩
  have physical := birth.physical_invariant box
  have same : (flow.at (run.state A).time).ObservationalEq (run.state A) :=
    (cut.observational_unique (run.finitePrefix A) box physical cutComplete runComplete).1
  let leftPart := remains.prefix (ltLimit A) right
  let incoming := leftPart.rebase_observational same
  let limit := { leftPart.at L with pending := (run.state A).pending }
  have incomingFlow : Flow θ (run.state A) limit := incoming
  let joined := (run.finitePrefix A).append (Execution.cons (.flow incomingFlow) (.nil _))
  obtain ⟨final, continuation, terminal⟩ := joined.continue_to_complete reference
    box physical complete limitBefore.le
  exact ⟨⟨A, limit, incomingFlow, tendsto_atTop_ciSup run.time_monotone bdd,
    run.follows_incoming box physical A incomingFlow ltLimit
      (fun j hj => zero j ((le_max_right k K).trans hj)),
    final, continuation, by rw [terminal.1]; exact limitBefore⟩⟩

/-- Maximality with respect to extensions that complete a final flow at its
accumulation date and then continue the same physical history. -/
def SemanticallyMaximal {n θ route} (run : @InfiniteExecution n θ route) : Prop :=
  IsEmpty run.FlowLimitExtension

theorem semanticallyMaximal_of_unbounded {n θ route} (run : @InfiniteExecution n θ route)
    (unbounded : ∀ H : ℝ, ∃ k, H < (run.state k).time) : run.SemanticallyMaximal := by
  constructor
  intro ext
  obtain ⟨k, later⟩ := unbounded ext.limit.time
  let j := max k ext.anchor
  obtain ⟨_, _, sub, _⟩ := ext.agrees j (le_max_right _ _)
  have date := sub ⟨le_rfl, run.time_monotone (Nat.le_succ j)⟩
  exact (not_lt_of_ge date.2) (later.trans_le (run.time_monotone (le_max_left _ _)))

/-- With complete finite histories at every horizon, maximality forces every
time threshold to be crossed and all later dates to stay past it. -/
theorem time_diverges_of_semanticallyMaximal {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F)
    (completeAt : ∀ H, (run.state 0).time ≤ H →
      HasCompleteExecution θ route (run.state 0) H)
    (maximal : run.SemanticallyMaximal) :
    ∀ H : ℝ, ∃ K : ℕ, ∀ k, K ≤ k → H < (run.state k).time := by
  intro H
  by_cases crosses : ∃ K, H < (run.state K).time
  · obtain ⟨K, later⟩ := crosses
    exact ⟨K, fun k hk => later.trans_le (run.time_monotone hk)⟩
  · have bounded (k : ℕ) : (run.state k).time ≤ H :=
      le_of_not_gt (fun later => crosses ⟨k, later⟩)
    have later : H < H + 1 := lt_add_of_pos_right H zero_lt_one
    obtain ⟨_, reference, complete⟩ := completeAt (H + 1) ((bounded 0).trans later.le)
    obtain ⟨extension⟩ := run.flow_limit_extension_exists birth box fanout
      reference complete H bounded later
    exact (maximal.false extension).elim

end InfiniteExecution

private theorem FiniteCausalChainData.fanout_le_length (d : FiniteCausalChainData)
    (contacts : ∀ j i t, (d.contacts j i t).length ≤ 1) (n : ℕ) :
    FanoutBound (d.route n) n := by
  induction n with
  | zero => intro i t; exact Nat.le_refl 0
  | succ n ih =>
    intro i t
    cases i using Fin.cases with
    | zero => exact Nat.zero_le _
    | succ i =>
      change ((d.route n i t).map Delivery.succ ++
        (d.contacts n i t).map Delivery.head).length ≤ n + 1
      simpa only [List.length_append, List.length_map] using
        Nat.add_le_add (ih i t) (contacts n i t)

/-- Each routing layer in the constructed chain contributes at most one
delivery per emission, so bounded fanout is supplied by the construction. -/
theorem ConstructedBirthCadenceChain.fanout_bound
    {n θ bornCells K sigma centre delay T}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T) :
    FanoutBound chain.router n := by
  apply FiniteCausalChainData.fanout_le_length
  intro j i t
  change (finiteCadenceHeadContact 0 2 160 (T + 1)
    (finiteChainPreparedDelay n delay j) i t).length ≤ 1
  simp only [finiteCadenceHeadContact]
  split <;> simp

/-- Every semantically maximal infinite run of the constructed finite-source
chain from birth progresses beyond each finite physical horizon. -/
theorem ConstructedBirthCadenceChain.maximal_run_progress
    {n θ bornCells K sigma centre delay T ε}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (box : PhysicalBox θ ε) (run : InfiniteExecution θ chain.router)
    (initial : run.state 0 = familyPreparationBornSource bornCells K)
    (maximal : run.SemanticallyMaximal) :
    ∀ H : ℝ, ∃ K' : ℕ, ∀ k, K' ≤ k → H < (run.state k).time := by
  apply run.time_diverges_of_semanticallyMaximal _ box chain.fanout_bound _ maximal
  · rw [initial]
    exact chain.preparation.source_birth
  · intro H afterBirth
    rw [initial] at afterBirth ⊢
    exact chain.complete_horizon H afterBirth

#print axioms InfiniteExecution.flow_limit_extension_exists
#print axioms InfiniteExecution.time_diverges_of_semanticallyMaximal
#print axioms ConstructedBirthCadenceChain.maximal_run_progress

end KernelR.Hybrid
