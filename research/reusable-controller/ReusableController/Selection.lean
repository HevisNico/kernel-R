import ReusableController.Proofs

/-! Bounded policy selection on a fixed benchmark. The evaluator, error bound,
charges and adoption rule are external parameters, never mutable state fields.
Integer scores are resource ticks; no circuit error bound is inferred here. -/
namespace ReusableController.Adaptive

structure SelectState (P : Type) where
  incumbent : P
  score : Int
  pending : List P
  spent : Nat
  trials : Nat
  adoptions : Nat
  live : ReusableController.State

/-- The same fixed report function is accurate on every policy under review. -/
def CostAccurate {P : Type} (trueCost : P → Nat) (report : P → Int) (tau : Nat) : Prop :=
  ∀ p, (trueCost p : Int) - (tau : Int) ≤ report p ∧
    report p ≤ (trueCost p : Int) + (tau : Int)

/-- Weak real improvement needs the 2τ margin. The additional strict measured
comparison forbids zero-error ties and supplies a decreasing natural potential. -/
def selectionAccept (tau : Nat) (old new : Int) : Bool :=
  decide (new + 2 * (tau : Int) ≤ old ∧ new < old)

def SelectState.potential {P : Type} (s : SelectState P) (tau : Nat) : Nat :=
  (s.score + (tau : Int)).toNat

/-- The incumbent is validated and charged once before trying alternatives. -/
def selectInit {P : Type} (report : P → Int) (charge : P → Nat)
    (seed : P) (pending : List P) (live : ReusableController.State) : SelectState P :=
  ⟨seed, report seed, pending, charge seed, 1, 0, live⟩

def selectStep {P : Type} (tau : Nat) (report : P → Int) (charge : P → Nat)
    (s : SelectState P) : SelectState P :=
  match s.pending with
  | [] => s
  | p :: ps =>
      let paid := { s with pending := ps, spent := s.spent + charge p, trials := s.trials + 1 }
      if selectionAccept tau s.score (report p) then
        { paid with incumbent := p, score := report p, adoptions := s.adoptions + 1 }
      else paid

def selectRun {P : Type} (tau : Nat) (report : P → Int) (charge : P → Nat) :
    Nat → SelectState P → SelectState P
  | 0, s => s
  | n + 1, s => selectRun tau report charge n (selectStep tau report charge s)

def selectFinish {P : Type} (tau : Nat) (report : P → Int) (charge : P → Nat)
    (s : SelectState P) : SelectState P :=
  selectRun tau report charge s.pending.length s

/-- The real comparison follows from two bounded errors, including equality
at the 2τ threshold. Strict real decrease is deliberately not asserted. -/
theorem robust_cost_nondegradation {oldCost newCost : Nat} {old new : Int} {tau : Nat}
    (oldAccurate : (oldCost : Int) - (tau : Int) ≤ old ∧ old ≤ (oldCost : Int) + (tau : Int))
    (newAccurate : (newCost : Int) - (tau : Int) ≤ new ∧ new ≤ (newCost : Int) + (tau : Int))
    (accept : selectionAccept tau old new = true) : newCost ≤ oldCost := by
  have guard := of_decide_eq_true accept
  omega

theorem selectStep_live {P : Type} (tau report charge) (s : SelectState P) :
    (selectStep tau report charge s).live = s.live := by
  cases pending : s.pending with
  | nil => simp [selectStep, pending]
  | cons p ps => simp only [selectStep, pending]; split <;> rfl

theorem selectStep_pending {P : Type} (tau report charge) (s : SelectState P) :
    (selectStep tau report charge s).pending = s.pending.tail := by
  cases pending : s.pending with
  | nil => simp [selectStep, pending]
  | cons p ps => simp only [selectStep, pending]; split <;> rfl

theorem selectStep_cache {P : Type} (tau report charge) {s : SelectState P}
    (cache : s.score = report s.incumbent) :
    (selectStep tau report charge s).score = report (selectStep tau report charge s).incumbent := by
  cases pending : s.pending with
  | nil => simpa [selectStep, pending] using cache
  | cons p ps => simp only [selectStep, pending]; split <;> simp_all

theorem selectStep_score {P : Type} (tau report charge) (s : SelectState P) :
    (selectStep tau report charge s).score ≤ s.score := by
  cases pending : s.pending with
  | nil => simp [selectStep, pending]
  | cons p ps =>
      simp only [selectStep, pending]
      split
      · rename_i accepted
        have guard := of_decide_eq_true accepted
        simp only
        omega
      · exact Int.le_refl _

theorem selectStep_trueCost {P : Type} {tau report charge trueCost} {s : SelectState P}
    (accurate : CostAccurate trueCost report tau) (cache : s.score = report s.incumbent) :
    trueCost (selectStep tau report charge s).incumbent ≤ trueCost s.incumbent := by
  cases pending : s.pending with
  | nil => simp [selectStep, pending]
  | cons p ps =>
      simp only [selectStep, pending]
      split
      · rename_i accepted
        exact robust_cost_nondegradation (by simpa [cache] using accurate s.incumbent)
          (accurate p) accepted
      · exact Nat.le_refl _

theorem cached_score_lower_bound {P : Type} {tau report trueCost} {s : SelectState P}
    (accurate : CostAccurate trueCost report tau) (cache : s.score = report s.incumbent) :
    0 ≤ s.score + (tau : Int) := by
  have bounds := accurate s.incumbent
  rw [← cache] at bounds
  omega

/-- The cached measured score, shifted by τ, strictly decreases on every
adoption. The true cost may tie, so it is not used as this potential. -/
theorem selectStep_adoption_progress {P : Type} {tau report charge trueCost} {s : SelectState P}
    (accurate : CostAccurate trueCost report tau) (cache : s.score = report s.incumbent)
    (adopted : (selectStep tau report charge s).adoptions = s.adoptions + 1) :
    (selectStep tau report charge s).potential tau < s.potential tau := by
  cases pending : s.pending with
  | nil => simp [selectStep, pending] at adopted
  | cons p ps =>
      simp only [selectStep, pending] at adopted ⊢
      by_cases accepted : selectionAccept tau s.score (report p) = true
      · simp only [accepted, ↓reduceIte] at adopted ⊢
        have guard := of_decide_eq_true accepted
        have oldLower := cached_score_lower_bound accurate cache
        have newBounds := accurate p
        simp only [SelectState.potential]
        omega
      · simp [accepted] at adopted

/-- Exactly one validation is charged for a nonempty queue, whether adopted
or rejected; exhaustion leaves all counters untouched. -/
theorem selectStep_accounting {P : Type} (tau report charge) (s : SelectState P) :
    (selectStep tau report charge s).spent = s.spent +
      (match s.pending with | [] => 0 | p :: _ => charge p) ∧
    (selectStep tau report charge s).trials = s.trials + (if s.pending = [] then 0 else 1) ∧
    s.adoptions ≤ (selectStep tau report charge s).adoptions ∧
    (selectStep tau report charge s).adoptions ≤ s.adoptions + (if s.pending = [] then 0 else 1) := by
  cases pending : s.pending with
  | nil => simp [selectStep, pending]
  | cons p ps => simp only [selectStep, pending]; split <;> simp

theorem selectStep_budget {P : Type} {tau report charge B} (s : SelectState P)
    (bounded : ∀ p, charge p ≤ B) :
    (selectStep tau report charge s).spent ≤ s.spent + B := by
  rw [(selectStep_accounting tau report charge s).1]
  cases pending : s.pending with
  | nil => simp
  | cons p ps => exact Nat.add_le_add_left (bounded p) _

theorem selectRun_live {P : Type} (tau report charge) (n : Nat) (s : SelectState P) :
    (selectRun tau report charge n s).live = s.live := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih _).trans (selectStep_live tau report charge s)

theorem selectRun_cache {P : Type} (tau report charge) (n : Nat) {s : SelectState P}
    (cache : s.score = report s.incumbent) :
    (selectRun tau report charge n s).score = report (selectRun tau report charge n s).incumbent := by
  induction n generalizing s with
  | zero => exact cache
  | succ n ih => exact ih (selectStep_cache tau report charge cache)

theorem selectRun_score {P : Type} (tau report charge) (n : Nat) (s : SelectState P) :
    (selectRun tau report charge n s).score ≤ s.score := by
  induction n generalizing s with
  | zero => exact Int.le_refl _
  | succ n ih => exact Int.le_trans (ih _) (selectStep_score tau report charge s)

theorem selectRun_trueCost {P : Type} {tau report charge trueCost} (n : Nat) {s : SelectState P}
    (accurate : CostAccurate trueCost report tau) (cache : s.score = report s.incumbent) :
    trueCost (selectRun tau report charge n s).incumbent ≤ trueCost s.incumbent := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      exact Nat.le_trans (ih (selectStep_cache tau report charge cache))
        (selectStep_trueCost accurate cache)

theorem selectRun_pending {P : Type} (tau report charge) (n : Nat) (s : SelectState P) :
    (selectRun tau report charge n s).pending = s.pending.drop n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [selectRun, ih, selectStep_pending]
      cases pending : s.pending <;> simp [List.drop_succ_cons]

theorem selectRun_bounds {P : Type} {tau report charge B} (n : Nat) (s : SelectState P)
    (bounded : ∀ p, charge p ≤ B) :
    (selectRun tau report charge n s).spent ≤ s.spent + n * B ∧
    (selectRun tau report charge n s).trials ≤ s.trials + n ∧
    (selectRun tau report charge n s).adoptions ≤ s.adoptions + n ∧
    s.adoptions ≤ (selectRun tau report charge n s).adoptions := by
  induction n generalizing s with
  | zero => simp [selectRun]
  | succ n ih =>
      obtain ⟨spent, trials, adoptions, monotone⟩ := ih (selectStep tau report charge s)
      have stepSpent := selectStep_budget (tau := tau) (report := report) s bounded
      have stepCounts := selectStep_accounting tau report charge s
      simp only [selectRun, Nat.succ_mul]
      have one : (if s.pending = [] then 0 else 1) ≤ 1 := by split <;> decide
      omega


/-- Pending alternatives are consumed exactly once in list order; the
trial counter includes unsuccessful validation just as successful validation. -/
theorem selectStep_trial_balance {P : Type} (tau report charge) (s : SelectState P) :
    (selectStep tau report charge s).trials + (selectStep tau report charge s).pending.length =
      s.trials + s.pending.length := by
  cases pending : s.pending with
  | nil => simp [selectStep, pending]
  | cons p ps => simp only [selectStep, pending]; split <;> simp <;> omega

theorem selectRun_trial_balance {P : Type} (tau report charge) (n : Nat) (s : SelectState P) :
    (selectRun tau report charge n s).trials + (selectRun tau report charge n s).pending.length =
      s.trials + s.pending.length := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih _).trans (selectStep_trial_balance tau report charge s)

theorem selectRun_spent_monotone {P : Type} (tau report charge) (n : Nat) (s : SelectState P) :
    s.spent ≤ (selectRun tau report charge n s).spent := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      apply Nat.le_trans _ (ih _)
      rw [(selectStep_accounting tau report charge s).1]
      omega

theorem selectStep_potential_accounting {P : Type} {tau report charge trueCost} {s : SelectState P}
    (accurate : CostAccurate trueCost report tau) (cache : s.score = report s.incumbent) :
    (selectStep tau report charge s).potential tau + (selectStep tau report charge s).adoptions ≤
      s.potential tau + s.adoptions := by
  cases pending : s.pending with
  | nil => simp [selectStep, pending]
  | cons p ps =>
      by_cases accepted : selectionAccept tau s.score (report p) = true
      · have adopted : (selectStep tau report charge s).adoptions = s.adoptions + 1 := by
          simp [selectStep, pending, accepted]
        have lower := selectStep_adoption_progress accurate cache adopted
        omega
      · simp [selectStep, pending, accepted, SelectState.potential]

theorem selectRun_potential_accounting {P : Type} {tau report charge trueCost}
    (n : Nat) {s : SelectState P} (accurate : CostAccurate trueCost report tau)
    (cache : s.score = report s.incumbent) :
    (selectRun tau report charge n s).potential tau + (selectRun tau report charge n s).adoptions ≤
      s.potential tau + s.adoptions := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      exact Nat.le_trans (ih (selectStep_cache tau report charge cache))
        (selectStep_potential_accounting accurate cache)

theorem selectRun_adoption_bound {P : Type} {tau report charge trueCost}
    (n : Nat) {s : SelectState P} (accurate : CostAccurate trueCost report tau)
    (cache : s.score = report s.incumbent) :
    (selectRun tau report charge n s).adoptions ≤ s.adoptions + s.potential tau := by
  have bound := selectRun_potential_accounting (charge := charge) n accurate cache
  omega

/-- Selection cannot alter a live lesson or its permanent blocked bits. -/
theorem selectRun_live_invariants {P : Type} (tau report charge) (n : Nat) (s : SelectState P)
    {need : RecursiveLearning.Learner} (ready : ReusableController.Ready need s.live) :
    ReusableController.Ready need (selectRun tau report charge n s).live ∧
      (selectRun tau report charge n s).live.preparationBlocked = s.live.preparationBlocked ∧
      (selectRun tau report charge n s).live.practiceBlocked = s.live.practiceBlocked := by
  rw [selectRun_live]
  exact ⟨ready, rfl, rfl⟩

theorem selectFinish_exhausted {P : Type} (tau report charge) (s : SelectState P) :
    (selectFinish tau report charge s).pending = [] := by
  rw [selectFinish, selectRun_pending]
  simp


theorem selectFinish_trials {P : Type} (tau report charge) (s : SelectState P) :
    (selectFinish tau report charge s).trials = s.trials + s.pending.length := by
  have balance := selectRun_trial_balance tau report charge s.pending.length s
  change (selectFinish tau report charge s).trials +
    (selectFinish tau report charge s).pending.length = _ at balance
  rw [selectFinish_exhausted] at balance
  simpa using balance


theorem selectFinish_stable {P : Type} (tau report charge) (s : SelectState P) :
    selectStep tau report charge (selectFinish tau report charge s) = selectFinish tau report charge s := by
  simp [selectStep, selectFinish_exhausted]

/-- Baseline plus every queued alternative is paid, including rejected trials.
A duplicate-free menu identifies length+1 with the number of policies. -/
theorem selection_total_budget {P : Type} {tau report charge B} (seed : P)
    (pending : List P) (live : ReusableController.State) (bounded : ∀ p, charge p ≤ B) :
    (selectFinish tau report charge (selectInit report charge seed pending live)).spent ≤
      (pending.length + 1) * B := by
  have bound := (selectRun_bounds (tau := tau) (report := report) pending.length
    (selectInit report charge seed pending live) bounded).1
  change _ ≤ (pending.length + 1) * B
  simp only [selectInit] at bound
  simp only [Nat.add_mul, Nat.one_mul]
  have initial := bounded seed
  exact Nat.le_trans bound (by omega)

/-- Sufficient break-even condition; selection work is paid in addition to
repeat uses of the retained policy's true benchmark cost. -/
theorem selection_amortization {P : Type} (trueCost : P → Nat) (before after : SelectState P)
    (uses : Nat) (nonincrease : trueCost after.incumbent ≤ trueCost before.incumbent)
    (paid : after.spent ≤ uses * (trueCost before.incumbent - trueCost after.incumbent)) :
    after.spent + uses * trueCost after.incumbent ≤ uses * trueCost before.incumbent := by
  have splitCost : trueCost before.incumbent =
      trueCost before.incumbent - trueCost after.incumbent + trueCost after.incumbent := by omega
  rw [splitCost, Nat.mul_add]
  exact Nat.add_le_add_right paid _


/-- A finite duplicate-free policy family, with its baseline included once. -/
structure PolicyMenu (P : Type) where
  seed : P
  alternatives : List P
  distinct : (seed :: alternatives).Nodup

def PolicyMenu.count {P : Type} (menu : PolicyMenu P) : Nat := menu.alternatives.length + 1

def selectMenu {P : Type} (tau : Nat) (report : P → Int) (charge : P → Nat)
    (menu : PolicyMenu P) (live : ReusableController.State) : SelectState P :=
  selectFinish tau report charge (selectInit report charge menu.seed menu.alternatives live)

theorem selectMenu_trials {P : Type} (tau report charge) (menu : PolicyMenu P)
    (live : ReusableController.State) :
    (selectMenu tau report charge menu live).trials = menu.count := by
  rw [selectMenu, selectFinish_trials]
  simp [selectInit, PolicyMenu.count, Nat.add_comm]

theorem selectMenu_budget {P : Type} {tau report charge B} (menu : PolicyMenu P)
    (live : ReusableController.State) (bounded : ∀ p, charge p ≤ B) :
    (selectMenu tau report charge menu live).spent ≤ menu.count * B :=
  selection_total_budget menu.seed menu.alternatives live bounded

theorem selectMenu_trueCost {P : Type} {tau report charge trueCost} (menu : PolicyMenu P)
    (live : ReusableController.State) (accurate : CostAccurate trueCost report tau) :
    trueCost (selectMenu tau report charge menu live).incumbent ≤ trueCost menu.seed :=
  selectRun_trueCost menu.alternatives.length accurate rfl

theorem selectStep_family {P : Type} (tau report charge) (allowed : List P) {s : SelectState P}
    (current : s.incumbent ∈ allowed) (pending : ∀ p ∈ s.pending, p ∈ allowed) :
    (selectStep tau report charge s).incumbent ∈ allowed ∧
      ∀ p ∈ (selectStep tau report charge s).pending, p ∈ allowed := by
  cases rest : s.pending with
  | nil => simp [selectStep, rest, current]
  | cons p ps =>
      have head := pending p (by simp [rest])
      have tail : ∀ p ∈ ps, p ∈ allowed := fun p member => pending p (by simp [rest, member])
      simp only [selectStep, rest]
      split <;> simp_all

theorem selectRun_family {P : Type} (tau report charge) (allowed : List P) (n : Nat)
    {s : SelectState P} (current : s.incumbent ∈ allowed)
    (pending : ∀ p ∈ s.pending, p ∈ allowed) :
    (selectRun tau report charge n s).incumbent ∈ allowed ∧
      ∀ p ∈ (selectRun tau report charge n s).pending, p ∈ allowed := by
  induction n generalizing s with
  | zero => exact ⟨current, pending⟩
  | succ n ih =>
      have next := selectStep_family tau report charge allowed current pending
      exact ih next.1 next.2

theorem selectMenu_member {P : Type} (tau report charge) (menu : PolicyMenu P)
    (live : ReusableController.State) :
    (selectMenu tau report charge menu live).incumbent ∈ menu.seed :: menu.alternatives := by
  apply (selectRun_family tau report charge (menu.seed :: menu.alternatives)
    menu.alternatives.length (s := selectInit report charge menu.seed menu.alternatives live)
    (by simp [selectInit]) (by intro p member; exact List.mem_cons_of_mem _ member)).1

end ReusableController.Adaptive
