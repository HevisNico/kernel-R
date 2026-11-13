import SelfCertifyingLearning.ClosedLoop

/-! Executable finite-lived contract selection. Reconfiguration pays for
any increase of the deficit potential; renewal never resets that debt. -/
namespace SelfCertifyingLearning.Epochs
open Repair ClosedLoop

structure Policy where
  service : Nat
  handoff : Nat
  deriving DecidableEq, Repr

structure Cursor where
  now : Nat
  lower : Nat
  debt : Nat
  credit : Nat
  deriving DecidableEq, Repr

structure Offer where
  config : Config
  decisions : Nat
  issued : Nat
  expires : Nat
  deriving DecidableEq, Repr

def entry (cursor : Cursor) (offer : Offer) : Nat := min cursor.lower offer.config.capacity

def span (cursor : Cursor) (offer : Offer) : Nat :=
  clock offer.config offer.decisions (entry cursor offer)

def endpoint (cursor : Cursor) (offer : Offer) : Nat :=
  final offer.config offer.decisions (entry cursor offer)

def charge (cursor : Cursor) (offer : Offer) : Nat :=
  deficit offer.config (entry cursor offer) - cursor.debt

def advance (cursor : Cursor) (offer : Offer) : Cursor :=
  ⟨cursor.now + span cursor offer, endpoint cursor offer,
    deficit offer.config (endpoint cursor offer), cursor.credit - charge cursor offer⟩

/-- All conditions are checked before dispatch. Expiry covers the whole
phase, the service requirement cannot be weakened, and switching debt is
paid from an explicit budget. Physical truth of an offered contract is
not inferred by these arithmetic checks. -/
structure Admissible (policy : Policy) (cursor : Cursor) (offer : Offer) : Prop where
  valid : offer.config.Valid
  sameService : offer.config.service = policy.service
  ready : offer.config.Ready (entry cursor offer)
  positive : 0 < offer.decisions
  issued : offer.issued ≤ cursor.now
  covers : cursor.now + span cursor offer ≤ offer.expires
  preserves : policy.handoff ≤ endpoint cursor offer
  affordable : charge cursor offer ≤ cursor.credit

def eligible (policy : Policy) (cursor : Cursor) (offer : Offer) : Bool :=
  decide (offer.config.Valid ∧ offer.config.service = policy.service ∧
    offer.config.Ready (entry cursor offer) ∧ 0 < offer.decisions ∧
    offer.issued ≤ cursor.now ∧ cursor.now + span cursor offer ≤ offer.expires ∧
    policy.handoff ≤ endpoint cursor offer ∧ charge cursor offer ≤ cursor.credit)

theorem eligible_iff (policy cursor offer) :
    eligible policy cursor offer = true ↔ Admissible policy cursor offer := by
  simp only [eligible, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, c, d, e, f, g, h⟩
    exact ⟨a, b, c, d, e, f, g, h⟩
  · intro h
    exact ⟨h.valid, h.sameService, h.ready, h.positive, h.issued, h.covers, h.preserves, h.affordable⟩

/-- Ordered candidates: put the preferred policy first and prudent
fallbacks afterwards. If no current contract passes, report refusal. -/
def select (policy : Policy) (cursor : Cursor) : List Offer → Option Offer
  | [] => none
  | offer :: rest => if eligible policy cursor offer then some offer else select policy cursor rest

theorem select_sound {policy cursor offers offer} (chosen : select policy cursor offers = some offer) :
    offer ∈ offers ∧ Admissible policy cursor offer := by
  induction offers with
  | nil => simp [select] at chosen
  | cons first rest ih =>
    simp only [select] at chosen
    split at chosen
    next good =>
      have equal := Option.some.inj chosen
      subst offer
      exact ⟨by simp, (eligible_iff _ _ _).mp good⟩
    next =>
      have tail := ih chosen
      exact ⟨by simp [tail.1], tail.2⟩

theorem select_exists {policy cursor offers} (available : ∃ offer ∈ offers, Admissible policy cursor offer) :
    ∃ chosen, select policy cursor offers = some chosen := by
  induction offers with
  | nil => simp at available
  | cons first rest ih =>
    by_cases good : eligible policy cursor first = true
    · exact ⟨first, by simp [select, good]⟩
    · obtain ⟨offer, member, valid⟩ := available
      have different : offer ≠ first := by
        intro same
        subst offer
        exact good ((eligible_iff _ _ _).mpr valid)
      have later : offer ∈ rest := by simpa [different] using member
      obtain ⟨chosen, choice⟩ := ih ⟨offer, later, valid⟩
      exact ⟨chosen, by simp [select, good, choice]⟩

theorem phase_progress {policy cursor offer} (admitted : Admissible policy cursor offer) :
    cursor.now < (advance cursor offer).now := by
  have progress := time_progress admitted.valid offer.decisions admitted.ready
  have positive := admitted.positive
  simp only [advance, span]
  omega

/-- The runtime budget covers a positive potential jump without inventing
physical disturbance. Equal or smaller deficits consume no credit. -/
theorem budget_bridge {policy cursor offer} (admitted : Admissible policy cursor offer) :
    deficit offer.config (entry cursor offer) + (advance cursor offer).credit ≤ cursor.debt + cursor.credit := by
  have paid := admitted.affordable
  simp only [advance, charge] at *
  omega

theorem credit_accounting {policy cursor offer} (admitted : Admissible policy cursor offer) :
    (advance cursor offer).credit + charge cursor offer = cursor.credit := by
  have paid := admitted.affordable
  simp only [advance]
  omega

/-- Renewing exactly the same configuration at its own endpoint incurs no
new deficit charge. Changing dates alone cannot reset the ledger. -/
theorem same_config_no_charge (previous : Cursor) (old fresh : Offer)
    (same : fresh.config = old.config)
    (bounded : endpoint previous old ≤ old.config.capacity) :
    charge (advance previous old) fresh = 0 := by
  unfold charge entry advance
  dsimp only
  rw [same]
  have cap : min (endpoint previous old) old.config.capacity = endpoint previous old := by omega
  rw [cap]
  omega

inductive Plan where
  | complete (cursor : Cursor)
  | blocked (cursor : Cursor)
  | phase (cursor : Cursor) (offer : Offer) (tail : Plan)
  deriving Repr

def run (policy : Policy) (cursor : Cursor) : List (List Offer) → Plan
  | [] => .complete cursor
  | candidates :: rest =>
    match select policy cursor candidates with
    | none => .blocked cursor
    | some offer => .phase cursor offer (run policy (advance cursor offer) rest)

inductive WellFormed (policy : Policy) : Cursor → Plan → Prop where
  | complete (cursor) : WellFormed policy cursor (.complete cursor)
  | blocked (cursor) : WellFormed policy cursor (.blocked cursor)
  | phase {cursor offer tail} (admitted : Admissible policy cursor offer)
      (rest : WellFormed policy (advance cursor offer) tail) :
      WellFormed policy cursor (.phase cursor offer tail)

theorem run_wellFormed (policy cursor requests) : WellFormed policy cursor (run policy cursor requests) := by
  induction requests generalizing cursor with
  | nil => exact .complete cursor
  | cons candidates rest ih =>
    simp only [run]
    split
    next => exact .blocked cursor
    next offer chosen => exact .phase (select_sound chosen).2 (ih _)

def Plan.finish : Plan → Cursor
  | .complete cursor | .blocked cursor => cursor
  | .phase _ _ tail => tail.finish

def Plan.phases : Plan → Nat
  | .complete _ | .blocked _ => 0
  | .phase _ _ tail => 1 + tail.phases

def Plan.switchCost : Plan → Nat
  | .complete _ | .blocked _ => 0
  | .phase cursor offer tail => charge cursor offer + tail.switchCost

def Plan.writes : Plan → Nat
  | .complete _ | .blocked _ => 0
  | .phase cursor offer tail =>
    ClosedLoop.writes (trace offer.config offer.decisions (entry cursor offer)) + tail.writes

def Plan.leakBudget : Plan → Nat
  | .complete _ | .blocked _ => 0
  | .phase cursor offer tail =>
    offer.config.bound * waitTime (trace offer.config offer.decisions (entry cursor offer)) + tail.leakBudget

def Plan.events : Plan → List Event
  | .complete _ | .blocked _ => []
  | .phase cursor offer tail =>
    .idle :: (ledger offer.config (trace offer.config offer.decisions (entry cursor offer)) ++ tail.events)

theorem switch_budget {policy cursor plan} (valid : WellFormed policy cursor plan) :
    plan.finish.credit + plan.switchCost = cursor.credit := by
  induction valid with
  | complete => simp [Plan.finish, Plan.switchCost]
  | blocked => simp [Plan.finish, Plan.switchCost]
  | phase admitted rest ih =>
    have paid := credit_accounting admitted
    simp only [Plan.finish, Plan.switchCost]
    omega

theorem no_zero_time_phases {policy cursor plan} (valid : WellFormed policy cursor plan) :
    cursor.now + plan.phases ≤ plan.finish.now := by
  induction valid with
  | complete => simp [Plan.finish, Plan.phases]
  | blocked => simp [Plan.finish, Plan.phases]
  | phase admitted rest ih =>
    have positive := phase_progress admitted
    simp only [Plan.finish, Plan.phases]
    omega

/-- Arithmetic selection refuses exactly when no supplied candidate is
admissible. It does not claim that the physical task remains safe afterwards. -/
theorem select_none_iff (policy cursor offers) :
    select policy cursor offers = none ↔ ¬ ∃ offer ∈ offers, Admissible policy cursor offer := by
  constructor
  · intro refused available
    obtain ⟨chosen, accepted⟩ := select_exists available
    rw [refused] at accepted
    contradiction
  · intro unavailable
    cases chosen : select policy cursor offers with
    | none => rfl
    | some offer =>
      have sound := select_sound chosen
      exact False.elim (unavailable ⟨offer, sound.1, sound.2⟩)

theorem add_reserve {eta initial events final} (run : Run eta initial events final) (reserve : Nat) :
    Run eta (initial + reserve) events (final + reserve) := by
  induction run with
  | nil => exact .nil _
  | correction decrease tail ih => exact .correction (by omega) ih
  | disturbance increase tail ih => exact .disturbance (by omega) ih
  | idle nonincrease tail ih => exact .idle (by omega) ih

theorem append_run {eta initial middle final first second}
    (left : Run eta initial first middle) (right : Run eta middle second final) :
    Run eta initial (first ++ second) final := by
  induction left with
  | nil => exact right
  | correction decrease tail ih => exact .correction decrease (ih right)
  | disturbance increase tail ih => exact .disturbance increase (ih right)
  | idle nonincrease tail ih => exact .idle nonincrease (ih right)

theorem corrections_append (first second : List Event) :
    corrections (first ++ second) = corrections first + corrections second := by
  induction first with
  | nil => simp [corrections]
  | cons event rest ih => cases event <;> simp [corrections, ih, Nat.add_assoc]

theorem injected_append (first second : List Event) :
    injected (first ++ second) = injected first + injected second := by
  induction first with
  | nil => simp [injected]
  | cons event rest ih => cases event <;> simp [injected, ih, Nat.add_assoc]

theorem events_counts (plan : Plan) :
    corrections plan.events = plan.writes ∧ injected plan.events = plan.leakBudget := by
  induction plan with
  | complete => simp [Plan.events, Plan.writes, Plan.leakBudget, corrections, injected]
  | blocked => simp [Plan.events, Plan.writes, Plan.leakBudget, corrections, injected]
  | phase cursor offer tail ih =>
    have counts := ledger_counts offer.config (trace offer.config offer.decisions (entry cursor offer))
    simp only [Plan.events, Plan.writes, Plan.leakBudget, corrections, injected,
      corrections_append, injected_append, counts.1, counts.2, ih.1, ih.2, and_self]

/-- Global potential is current deficit plus unspent switching credit.
The admission step pays any potential jump, then the old per-phase ledger
runs without resetting the terminal deficit. -/
theorem accounting {policy cursor plan} (valid : WellFormed policy cursor plan) :
    Run 1 (cursor.debt + cursor.credit) plan.events (plan.finish.debt + plan.finish.credit) := by
  induction valid with
  | complete => exact .nil _
  | blocked => exact .nil _
  | @phase cursor offer tail admitted rest ih =>
    have phaseRun := ledger_run admitted.valid offer.decisions admitted.ready
    have funded := add_reserve phaseRun (advance cursor offer).credit
    have combined := append_run funded ih
    exact .idle (budget_bridge admitted) combined

theorem global_write_bound {policy cursor plan} (valid : WellFormed policy cursor plan) :
    plan.writes ≤ cursor.debt + cursor.credit + plan.leakBudget := by
  have bound := (accounting valid).correction_bound
  have counts := events_counts plan
  rw [counts.1, counts.2] at bound
  simpa using bound

/-- Retaining terminal debt yields the tighter bound using credit actually
spent, rather than charging every renewal a fresh initial deficit. -/
theorem global_balance {policy cursor plan} (valid : WellFormed policy cursor plan) :
    plan.finish.debt + plan.writes ≤ cursor.debt + plan.switchCost + plan.leakBudget := by
  have balance := (accounting valid).balance
  have counts := events_counts plan
  rw [counts.1, counts.2] at balance
  simp only [Nat.one_mul] at balance
  have paid := switch_budget valid
  omega

def Plan.elapsed : Plan → Nat
  | .complete _ | .blocked _ => 0
  | .phase cursor offer tail => span cursor offer + tail.elapsed

def Plan.waitTicks : Plan → Nat
  | .complete _ | .blocked _ => 0
  | .phase cursor offer tail =>
    waitTime (trace offer.config offer.decisions (entry cursor offer)) + tail.waitTicks

def Plan.writeTicks : Plan → Nat
  | .complete _ | .blocked _ => 0
  | .phase cursor offer tail =>
    offer.config.latency * ClosedLoop.writes (trace offer.config offer.decisions (entry cursor offer)) + tail.writeTicks

theorem elapsed_accounting (plan : Plan) : plan.elapsed = plan.waitTicks + plan.writeTicks := by
  induction plan with
  | complete => rfl
  | blocked => rfl
  | phase cursor offer tail ih =>
    have clockLaw := clock_accounting offer.config offer.decisions (entry cursor offer)
    simp only [Plan.elapsed, Plan.waitTicks, Plan.writeTicks, span]
    omega

theorem contiguous_clock {policy cursor plan} (valid : WellFormed policy cursor plan) :
    cursor.now + plan.elapsed = plan.finish.now := by
  induction valid with
  | complete => simp [Plan.elapsed, Plan.finish]
  | blocked => simp [Plan.elapsed, Plan.finish]
  | phase admitted rest ih =>
    simp only [Plan.elapsed, Plan.finish]
    simp only [advance] at ih
    omega

theorem empty_candidates_block (policy cursor) :
    run policy cursor [[]] = .blocked cursor := rfl

end SelfCertifyingLearning.Epochs
