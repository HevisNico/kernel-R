import SelfCertifyingLearning.EpochSafety

/-! Sufficient conditions for a perpetually renewable *fixed fallback*.
Its ceiling is a known hard bound, not an extrapolated local measurement.
Physical all-time service additionally requires the plant laws forever. -/
namespace SelfCertifyingLearning.Availability
open Repair ClosedLoop Epochs EpochSafety

def policy (c : Config) : Policy := ⟨c.service, c.guard⟩

/-- Entry may come from another policy, but must fund any increase in the
fallback deficit. Readiness alone is insufficient with finite credit. -/
def Funded (c : Config) (cursor : Cursor) : Prop :=
  c.Ready cursor.lower ∧ deficit c cursor.lower ≤ cursor.debt + cursor.credit

instance (c : Config) (cursor : Cursor) : Decidable (Funded c cursor) :=
  inferInstanceAs (Decidable (_ ∧ _))

def offer (c : Config) (cursor : Cursor) : Offer :=
  ⟨c, 1, cursor.now, cursor.now + max c.maxWait c.latency⟩

theorem entry_equal {c cursor} (funded : Funded c cursor) :
    entry cursor (offer c cursor) = cursor.lower := by
  have bounded := funded.1.2
  simp only [entry, offer]
  omega

/-- Every funded fallback state has an admissible fresh one-decision offer.
The hard envelope must justify issuing it at the new calendar time. -/
theorem available {c : Config} (valid : c.Valid) {cursor : Cursor} (funded : Funded c cursor) :
    Admissible (policy c) cursor (offer c cursor) := by
  have same := entry_equal funded
  have ready : c.Ready (entry cursor (offer c cursor)) := by rw [same]; exact funded.1
  have endReady := final_ready valid 1 ready
  have timeBound := clock_upper valid 1 ready
  refine ⟨valid, rfl, ready, by change 0 < 1; decide, Nat.le_refl _, ?_, endReady.1, ?_⟩
  · simp only [offer, span, Nat.one_mul] at *
    omega
  · have paid := funded.2
    simp only [charge, offer]
    change deficit c (entry cursor (offer c cursor)) - cursor.debt ≤ cursor.credit
    rw [same]
    omega

theorem selected {c : Config} (valid : c.Valid) {cursor : Cursor} (funded : Funded c cursor) :
    select (policy c) cursor [offer c cursor] = some (offer c cursor) := by
  have eligible := (eligible_iff _ _ _).mpr (available valid funded)
  simp [select, eligible]

/-- After entry, the generated terminal debt is exactly the fallback's
own deficit. Reissuing the same configuration needs no fresh credit. -/
theorem funded_next {c : Config} (valid : c.Valid) {cursor : Cursor} (funded : Funded c cursor) :
    Funded c (advance cursor (offer c cursor)) := by
  have nextReady := endpoint_ready (available valid funded)
  refine ⟨nextReady, ?_⟩
  simp only [advance, offer]
  omega

def renew (c : Config) (cursor : Cursor) : Nat → Plan
  | 0 => .complete cursor
  | n + 1 =>
    match select (policy c) cursor [offer c cursor] with
    | none => .blocked cursor
    | some chosen => .phase cursor chosen (renew c (advance cursor chosen) n)

theorem renew_wellFormed {c : Config} (valid : c.Valid) {cursor : Cursor}
    (funded : Funded c cursor) (n : Nat) : WellFormed (policy c) cursor (renew c cursor n) := by
  induction n generalizing cursor with
  | zero => exact .complete cursor
  | succ n ih =>
    simp only [renew, selected valid funded]
    exact .phase (available valid funded) (ih (funded_next valid funded))

def Completed : Plan → Prop
  | .complete _ => True
  | .blocked _ => False
  | .phase _ _ tail => Completed tail

/-- Every finite requested number of fallback phases is executed. This is
not merely existence of a safe path or safety conditional on non-blocking. -/
theorem completes_every_prefix {c : Config} (valid : c.Valid) {cursor : Cursor}
    (funded : Funded c cursor) (n : Nat) : Completed (renew c cursor n) ∧ (renew c cursor n).phases = n := by
  induction n generalizing cursor with
  | zero => exact ⟨trivial, rfl⟩
  | succ n ih =>
    have tail := ih (funded_next valid funded)
    simp only [renew, selected valid funded, Completed, Plan.phases]
    exact ⟨tail.1, by omega⟩

theorem unbounded_time {c : Config} (valid : c.Valid) {cursor : Cursor}
    (funded : Funded c cursor) (n : Nat) : cursor.now + n ≤ (renew c cursor n).finish.now := by
  have time := no_zero_time_phases (renew_wellFormed valid funded n)
  rw [(completes_every_prefix valid funded n).2] at time
  exact time

/-- One state trajectory must realize every prefix: the loss ceiling and
commanded-dose laws remain true forever. With that explicit physical
assumption, the non-blocking policy preserves service at every future tick. -/
theorem perpetual_service {c : Config} (valid : c.Valid) {cursor : Cursor}
    (funded : Funded c cursor) (state : Nat → Int)
    (observed : (cursor.lower : Int) ≤ state cursor.now)
    (physics : ∀ n, EpochSafety.Realizes state (renew c cursor n)) :
    ∀ t, cursor.now ≤ t → (c.service : Int) ≤ state t := by
  intro t after
  have floor : (policy c).service ≤ cursor.lower := by
    have := funded.1.1
    unfold Config.guard at this
    simp only [policy]
    omega
  have safe := composed_safe (renew_wellFormed valid funded (t + 1)) state floor observed (physics (t + 1))
  have time := unbounded_time valid funded (t + 1)
  exact safe.1 t after (by omega)

/-- Spare repair power and reserve do not suffice when entry debt is not
funded. Once funded, the same configuration renews without further charge. -/
def exampleConfig : Config := ⟨10, 2, 3, 7, 20, 4⟩
def unfunded : Cursor := ⟨0, 16, 0, 0⟩
def fundedExample : Cursor := ⟨0, 16, 0, 2⟩

theorem missing_credit_refuses :
    select (policy exampleConfig) unfunded [offer exampleConfig unfunded] = none := by decide

theorem example_ready : exampleConfig.Valid ∧ Funded exampleConfig fundedExample := by decide

theorem example_never_blocks (n : Nat) : Completed (renew exampleConfig fundedExample n) :=
  (completes_every_prefix example_ready.1 example_ready.2 n).1

end SelfCertifyingLearning.Availability
