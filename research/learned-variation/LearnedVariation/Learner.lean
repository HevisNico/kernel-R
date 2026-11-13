import LearnedVariation.Envelope

namespace LearnedVariation

structure Policy where
  horizon : Nat
  cap : Nat
  window : Nat
  deriving DecidableEq, Repr

def Policy.Valid (p : Policy) : Prop := 0 < p.horizon ∧ p.horizon ≤ p.window
instance (p : Policy) : Decidable p.Valid := inferInstanceAs (Decidable (_ ∧ _))

inductive Mode where
  | validating
  | provisional
  | exhausted
  | fault
  deriving DecidableEq, Repr

def Mode.live : Mode → Bool
  | .validating | .provisional => true
  | _ => false

structure Annotation where
  through : Nat
  oldBound : Nat
  required : Nat
  demonstrated : Bool
  witnesses : List Sample
  trigger : Sample
  deriving DecidableEq, Repr

def annotation (p : Policy) (bound : Nat) (history : List Sample) (sample : Sample) : Annotation :=
  ⟨sample.time, bound, demand p.horizon history sample,
    refuted p.horizon bound history sample,
    history.filter (fun old => eligible p.horizon old sample && decide (bound < pairNeed old sample)),
    sample⟩

structure State where
  bound : Nat
  history : List Sample
  mode : Mode
  nextTime : Nat
  remaining : Nat
  windowStart : Nat
  refinements : Nat
  validationSteps : Nat
  credit : Nat
  attempts : Nat
  annotations : List Annotation
  deriving DecidableEq, Repr

def initial (p : Policy) (start budget : Nat) : State :=
  ⟨0, [], .validating, start, p.window, start, 0, 0, budget, 0, []⟩

def charge (s : State) : State := { s with credit := s.credit - 1, attempts := s.attempts + 1 }

def accept (p : Policy) (s : State) (sample : Sample) : State :=
  let required := demand p.horizon s.history sample
  let enlarged := widen s.bound required
  let record := annotation p s.bound s.history sample
  if p.cap < enlarged then
    { s with mode := .exhausted, annotations := record :: s.annotations }
  else if s.bound < required then
    { s with bound := enlarged, history := sample :: s.history, mode := .validating, nextTime := sample.time + 1, remaining := p.window, windowStart := sample.time, refinements := s.refinements + 1, annotations := record :: s.annotations }
  else if s.history.isEmpty then
    { s with history := [sample], nextTime := sample.time + 1, mode := .validating, remaining := p.window, windowStart := sample.time }
  else if s.mode = .validating then
    { s with history := sample :: s.history, nextTime := sample.time + 1, remaining := s.remaining - 1, validationSteps := s.validationSteps + 1, mode := if s.remaining ≤ 1 then .provisional else .validating }
  else
    { s with history := sample :: s.history, nextTime := sample.time + 1 }

def step (p : Policy) (s : State) (reading : Option Sample) : State :=
  if !s.mode.live then s else
  if s.credit = 0 then { s with mode := .exhausted } else
  let paid := charge s
  match reading with
  | none => { paid with mode := .fault }
  | some sample =>
    if p.Valid ∧ sample.time = s.nextTime then accept p paid sample
    else { paid with mode := .fault }

def run (p : Policy) : State → List (Option Sample) → State
  | s, [] => s
  | s, next :: rest => run p (step p s next) rest

def Fits (p : Policy) (bound : Nat) : List Sample → Prop
  | [] => True
  | sample :: history => demand p.horizon history sample ≤ bound ∧ Fits p bound history

theorem fits_monotone {p a b history} (fits : Fits p a history) (larger : a ≤ b) :
    Fits p b history := by
  induction history with
  | nil => trivial
  | cons sample history ih => exact ⟨by have := fits.1; omega, ih fits.2⟩

theorem accept_fits (p s sample) (old : Fits p s.bound s.history) :
    Fits p (accept p s sample).bound (accept p s sample).history := by
  simp only [accept]
  split
  · exact old
  · split
    · exact ⟨widen_covers _ _, fits_monotone old (widen_monotone _ _)⟩
    · split
      · simp [Fits, demand]
      · split <;> change demand p.horizon s.history sample ≤ s.bound ∧ Fits p s.bound s.history
        all_goals exact ⟨by omega, old⟩

theorem step_fits (p s reading) (old : Fits p s.bound s.history) :
    Fits p (step p s reading).bound (step p s reading).history := by
  simp only [step]
  split
  · exact old
  · split
    · exact old
    · cases reading with
      | none => exact old
      | some sample =>
        simp only
        split
        · exact accept_fits p (charge s) sample old
        · exact old

theorem prefix_fits (p start budget readings) :
    Fits p (run p (initial p start budget) readings).bound
      (run p (initial p start budget) readings).history := by
  have general : ∀ s, Fits p s.bound s.history → Fits p (run p s readings).bound (run p s readings).history := by
    induction readings with
    | nil => intro s old; exact old
    | cons next rest ih => intro s old; exact ih (step p s next) (step_fits p s next old)
  exact general _ trivial

theorem accept_accounting (p s sample) :
    (accept p s sample).credit = s.credit ∧ (accept p s sample).attempts = s.attempts := by
  simp only [accept]
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl⟩

theorem step_accounting (p s reading) :
    (step p s reading).attempts + (step p s reading).credit = s.attempts + s.credit := by
  simp only [step]
  split
  · rfl
  · split
    · rfl
    next positive =>
      have paid : (charge s).attempts + (charge s).credit = s.attempts + s.credit := by
        simp only [charge]; omega
      cases reading with
      | none => exact paid
      | some sample =>
        simp only
        split
        · have accounting := accept_accounting p (charge s) sample
          rw [accounting.1, accounting.2]; exact paid
        · exact paid

theorem attempts_bounded (p s readings) :
    (run p s readings).attempts + (run p s readings).credit = s.attempts + s.credit := by
  induction readings generalizing s with
  | nil => rfl
  | cons next rest ih => exact (ih (step p s next)).trans (step_accounting p s next)

theorem fixed_budget (p start budget readings) :
    (run p (initial p start budget) readings).attempts ≤ budget := by
  have accounting := attempts_bounded p (initial p start budget) readings
  change (run p (initial p start budget) readings).attempts +
    (run p (initial p start budget) readings).credit = 0 + budget at accounting
  omega

theorem cost_bound (p start budget readings price) :
    price * (run p (initial p start budget) readings).attempts ≤ price * budget :=
  Nat.mul_le_mul_left price (fixed_budget p start budget readings)

def Ranked (p : Policy) (s : State) : Prop :=
  s.refinements ≤ s.bound ∧ s.bound ≤ p.cap

theorem accept_ranked (p s sample) (ranked : Ranked p s) : Ranked p (accept p s sample) := by
  unfold Ranked at *
  simp only [accept]
  split
  · exact ranked
  · split
    · have strict : s.bound + 1 ≤ widen s.bound (demand p.horizon s.history sample) := by
        unfold widen; omega
      change s.refinements + 1 ≤ widen s.bound (demand p.horizon s.history sample) ∧
        widen s.bound (demand p.horizon s.history sample) ≤ p.cap
      constructor <;> omega
    · split
      · exact ranked
      · split <;> exact ranked

theorem step_ranked (p s reading) (ranked : Ranked p s) : Ranked p (step p s reading) := by
  simp only [step]
  split
  · exact ranked
  · split
    · exact ranked
    · cases reading with
      | none => exact ranked
      | some sample =>
        simp only
        split
        · exact accept_ranked p (charge s) sample ranked
        · exact ranked

theorem refinements_bounded (p start budget readings) :
    (run p (initial p start budget) readings).refinements ≤ p.cap := by
  have general : ∀ s, Ranked p s → Ranked p (run p s readings) := by
    induction readings with
    | nil => intro s old; exact old
    | cons next rest ih => intro s old; exact ih _ (step_ranked p s next old)
  have rank := general (initial p start budget) (by simp [Ranked, initial])
  unfold Ranked at rank
  omega

theorem accept_keeps_annotations (p s sample) :
    ∃ extra, (accept p s sample).annotations = extra ++ s.annotations := by
  simp only [accept]
  split
  · exact ⟨[_], rfl⟩
  · split
    · exact ⟨[_], rfl⟩
    · split
      · exact ⟨[], rfl⟩
      · split <;> exact ⟨[], rfl⟩

structure EmpiricalProposal where
  bound : Nat
  horizon : Nat
  fromTime : Nat
  throughTime : Nat
  deriving DecidableEq, Repr

def proposal (p : Policy) (s : State) : Option EmpiricalProposal :=
  if s.mode = .provisional ∧ s.remaining = 0 then
    some ⟨s.bound, p.horizon, s.windowStart, s.windowStart + p.window⟩
  else none

theorem proposal_requires_finished_window {p s result} (offered : proposal p s = some result) :
    s.mode = .provisional ∧ s.remaining = 0 := by
  simp only [proposal] at offered
  split at offered
  · assumption
  · contradiction

def futureGuarantee (_ : EmpiricalProposal) : Bool := false

theorem no_empirical_future_guarantee (result : EmpiricalProposal) : futureGuarantee result = false := rfl

end LearnedVariation
