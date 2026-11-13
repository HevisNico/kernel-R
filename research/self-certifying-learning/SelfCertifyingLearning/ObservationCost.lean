import SelfCertifyingLearning.EpochSafety
import SelfCertifyingLearning.Availability

/-! Explicit modeled sensing/write prices. This is not measured energy and
adds no observation latency. Optimization is over a supplied finite catalogue
of certified plans ending at the same deadline, not over all online policies. -/
namespace SelfCertifyingLearning.ObservationCost
open Epochs EpochSafety

structure Prices where
  observation : Nat
  write : Nat
  deriving DecidableEq, Repr

/-- Model: one sensing attempt at each processed phase request, including
an attempted request that blocks. Unprocessed future requests are not billed. -/
def attempts : Plan → Nat
  | .complete _ => 0
  | .blocked _ => 1
  | .phase _ _ tail => 1 + attempts tail

def completed : Plan → Bool
  | .complete _ => true
  | .blocked _ => false
  | .phase _ _ tail => completed tail

def cost (prices : Prices) (plan : Plan) : Nat :=
  prices.observation * attempts plan + prices.write * plan.writes

theorem attempts_accounting (plan : Plan) :
    attempts plan = plan.phases + (if completed plan then 0 else 1) := by
  induction plan with
  | complete => rfl
  | blocked => rfl
  | phase cursor offer tail ih =>
    cases flag : completed tail <;> simp_all [attempts, completed, Plan.phases, Nat.add_assoc]

theorem blocked_attempt_paid (prices : Prices) (cursor : Cursor) :
    cost prices (.blocked cursor) = prices.observation := by simp [cost, attempts, Plan.writes]

/-- A plan cannot become competitive simply by stopping before service is
required. Completion and the common calendar endpoint are hard constraints. -/
def comparable (deadline : Nat) (plan : Plan) : Bool :=
  completed plan && decide (plan.finish.now = deadline)

structure Candidate (policy : Policy) (cursor : Cursor) where
  plan : Plan
  certified : WellFormed policy cursor plan

def bestFrom {A : Type} (price : A → Nat) (best : A) : List A → A
  | [] => best
  | next :: rest => bestFrom price (if price next ≤ price best then next else best) rest

theorem bestFrom_spec {A : Type} (price : A → Nat) (best : A) (rest : List A) :
    bestFrom price best rest ∈ best :: rest ∧
    ∀ other ∈ best :: rest, price (bestFrom price best rest) ≤ price other := by
  induction rest generalizing best with
  | nil => simp [bestFrom]
  | cons next rest ih =>
    by_cases cheaper : price next ≤ price best
    · simp only [bestFrom, ite_eq_left cheaper]
      have winner := ih next
      refine ⟨List.mem_cons_of_mem _ winner.1, ?_⟩
      intro other member
      rcases List.mem_cons.mp member with same | later
      · subst other
        exact Nat.le_trans (winner.2 next (by simp)) cheaper
      · exact winner.2 other later
    · simp only [bestFrom, ite_eq_right cheaper]
      have winner := ih best
      refine ⟨?_, ?_⟩
      · rcases List.mem_cons.mp winner.1 with same | member
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr member)))
      intro other member
      rcases List.mem_cons.mp member with same | later
      · subst other; exact winner.2 best (by simp)
      · rcases List.mem_cons.mp later with same | later
        · subst other
          have bound := winner.2 best (by simp)
          omega
        · exact winner.2 other (by simp [later])

def select {policy cursor} (prices : Prices) (deadline : Nat)
    (candidates : List (Candidate policy cursor)) : Option (Candidate policy cursor) :=
  match candidates.filter (fun c => comparable deadline c.plan) with
  | [] => none
  | first :: rest => some (bestFrom (fun c => cost prices c.plan) first rest)

theorem select_spec {policy cursor prices deadline candidates chosen}
    (selected : @select policy cursor prices deadline candidates = some chosen) :
    chosen ∈ candidates ∧ comparable deadline chosen.plan = true ∧
    ∀ other ∈ candidates, comparable deadline other.plan = true →
      cost prices chosen.plan ≤ cost prices other.plan := by
  unfold select at selected
  cases filtered : candidates.filter (fun c => comparable deadline c.plan) with
  | nil => simp [filtered] at selected
  | cons first rest =>
    simp only [filtered, Option.some.injEq] at selected
    have winner := bestFrom_spec (fun c => cost prices c.plan) first rest
    rw [selected] at winner
    have member : chosen ∈ candidates.filter (fun c => comparable deadline c.plan) := by
      rw [filtered]; exact winner.1
    have input := List.mem_filter.mp member
    refine ⟨input.1, input.2, ?_⟩
    intro other original feasible
    apply winner.2 other
    rw [← filtered]
    exact List.mem_filter.mpr ⟨original, feasible⟩

/-- Safety is a constraint on candidates, never traded for fewer samples.
Physical realization is still required for the selected plan. -/
theorem selected_service {policy cursor prices deadline candidates chosen}
    (selected : @select policy cursor prices deadline candidates = some chosen)
    (state : Nat → Int) (initial : policy.service ≤ cursor.lower)
    (observed : (cursor.lower : Int) ≤ state cursor.now)
    (physics : EpochSafety.Realizes state chosen.plan) :
    SafeBetween state policy.service cursor.now deadline := by
  have specification := select_spec selected
  have endpoint := specification.2.1
  simp only [comparable, Bool.and_eq_true, decide_eq_true_eq] at endpoint
  have safe := composed_safe chosen.certified state initial observed physics
  rw [endpoint.2] at safe
  exact safe.1

theorem blocked_ineligible (deadline : Nat) (cursor : Cursor) :
    comparable deadline (.blocked cursor) = false := rfl

theorem premature_completion_ineligible (cursor : Cursor) (deadline : Nat)
    (later : cursor.now < deadline) : comparable deadline (.complete cursor) = false := by
  have different : cursor.now ≠ deadline := by omega
  simp [comparable, completed, Plan.finish, different]

/-- Same two writes and same deadline, packaged as one sensing phase or
as two renewed phases. The example isolates the modeled observation price. -/
def bundled : Candidate (Availability.policy Availability.exampleConfig) Availability.fundedExample :=
  ⟨Epochs.run (Availability.policy Availability.exampleConfig) Availability.fundedExample
    [[{ Availability.offer Availability.exampleConfig Availability.fundedExample with decisions := 2, expires := 6 }]],
   Epochs.run_wellFormed _ _ _⟩

def separated : Candidate (Availability.policy Availability.exampleConfig) Availability.fundedExample :=
  ⟨Availability.renew Availability.exampleConfig Availability.fundedExample 2,
   Availability.renew_wellFormed Availability.example_ready.1 Availability.example_ready.2 2⟩

theorem comparison_is_like_for_like : comparable 6 bundled.plan = true ∧
    comparable 6 separated.plan = true ∧ bundled.plan.writes = 2 ∧ separated.plan.writes = 2 := by decide

theorem observation_price_changes_cost : cost ⟨10, 1⟩ bundled.plan = 12 ∧
    cost ⟨10, 1⟩ separated.plan = 22 := by decide

theorem fewer_samples_selected :
    (select ⟨10, 1⟩ 6 [separated, bundled]).map (fun c => attempts c.plan) = some 1 := by decide

end SelfCertifyingLearning.ObservationCost
