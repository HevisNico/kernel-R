import SelfCertifyingLearning.Renewal

namespace LearnedVariation
open SelfCertifyingLearning

structure Sample where
  time : Nat
  interval : Renewal.Interval
  deriving DecidableEq, Repr

def eligible (horizon : Nat) (old next : Sample) : Bool :=
  decide (old.time < next.time ∧ next.time ≤ old.time + horizon)

def pairNeed (old next : Sample) : Nat := next.interval.hi - old.interval.lo

def demand (horizon : Nat) : List Sample → Sample → Nat
  | [], _ => 0
  | old :: rest, next =>
    max (if eligible horizon old next then pairNeed old next else 0)
      (demand horizon rest next)

theorem pairNeed_iff (old next : Sample) (bound : Nat) :
    pairNeed old next ≤ bound ↔ next.interval.hi ≤ old.interval.lo + bound := by
  unfold pairNeed
  omega

theorem demand_spec (horizon : Nat) (history : List Sample) (next : Sample) (bound : Nat) :
    demand horizon history next ≤ bound ↔
      ∀ old ∈ history, eligible horizon old next = true →
        next.interval.hi ≤ old.interval.lo + bound := by
  induction history with
  | nil => simp [demand]
  | cons first rest ih =>
    constructor
    · intro covered old member within
      have firstBound : (if eligible horizon first next then pairNeed first next else 0) ≤ bound := by
        change max _ _ ≤ bound at covered
        omega
      have restBound : demand horizon rest next ≤ bound := by
        change max _ _ ≤ bound at covered
        omega
      rcases List.mem_cons.mp member with same | later
      · subst old
        simp only [within, ite_true] at firstBound
        exact (pairNeed_iff first next bound).mp firstBound
      · exact ih.mp restBound old later within
    · intro covered
      have firstBound : (if eligible horizon first next then pairNeed first next else 0) ≤ bound := by
        split
        next within => exact (pairNeed_iff first next bound).mpr (covered first (by simp) within)
        next => omega
      have restBound : demand horizon rest next ≤ bound :=
        ih.mpr (by intro old member within; exact covered old (by simp [member]) within)
      change max _ _ ≤ bound
      omega

theorem sampled_excursion {old next : Sample} {before after bound : Nat}
    (oldHonest : old.interval.Contains before) (nextHonest : next.interval.Contains after)
    (covered : pairNeed old next ≤ bound) : after ≤ before + bound := by
  have fit := (pairNeed_iff old next bound).mp covered
  unfold Renewal.Interval.Contains at oldHonest nextHonest
  omega

theorem demand_sampled_sound {horizon bound : Nat} {history : List Sample} {next old : Sample}
    {before after : Nat} (covered : demand horizon history next ≤ bound)
    (member : old ∈ history) (within : eligible horizon old next = true)
    (oldHonest : old.interval.Contains before) (nextHonest : next.interval.Contains after) :
    after ≤ before + bound := by
  apply sampled_excursion oldHonest nextHonest
  exact (pairNeed_iff old next bound).mpr ((demand_spec horizon history next bound).mp covered old member within)

def refuted (horizon bound : Nat) (history : List Sample) (next : Sample) : Bool :=
  history.any fun old => eligible horizon old next &&
    decide (old.interval.hi + bound < next.interval.lo)

theorem refuted_iff (horizon bound : Nat) (history : List Sample) (next : Sample) :
    refuted horizon bound history next = true ↔
      ∃ old ∈ history, eligible horizon old next = true ∧
        old.interval.hi + bound < next.interval.lo := by
  simp [refuted, List.any_eq_true]

theorem definite_refutation {old next : Sample} {before after bound : Nat}
    (oldHonest : old.interval.Contains before) (nextHonest : next.interval.Contains after)
    (refutation : old.interval.hi + bound < next.interval.lo) : before + bound < after := by
  unfold Renewal.Interval.Contains at oldHonest nextHonest
  omega

theorem refuted_sampled_sound {horizon bound : Nat} {history : List Sample} {next : Sample}
    (truth : Nat → Nat)
    (oldHonest : ∀ old ∈ history, old.interval.Contains (truth old.time))
    (nextHonest : next.interval.Contains (truth next.time))
    (refutation : refuted horizon bound history next = true) :
    ∃ old ∈ history, eligible horizon old next = true ∧
      truth old.time + bound < truth next.time := by
  obtain ⟨old, member, within, apart⟩ := (refuted_iff horizon bound history next).mp refutation
  exact ⟨old, member, within, definite_refutation (oldHonest old member) nextHonest apart⟩

theorem refutation_requires_widening {horizon bound : Nat} {history : List Sample} {next : Sample}
    (refutation : refuted horizon bound history next = true) :
    bound < demand horizon history next := by
  obtain ⟨old, member, within, apart⟩ := (refuted_iff horizon bound history next).mp refutation
  by_cases larger : bound < demand horizon history next
  · exact larger
  · have covered : demand horizon history next ≤ bound := by omega
    have fit := (demand_spec horizon history next bound).mp covered old member within
    have oldOrder := old.interval.ordered
    have nextOrder := next.interval.ordered
    omega

def ambiguous (horizon bound : Nat) (history : List Sample) (next : Sample) : Bool :=
  decide (bound < demand horizon history next) && !refuted horizon bound history next

theorem ambiguity_is_not_refutation {horizon bound history next}
    (uncertain : ambiguous horizon bound history next = true) :
    bound < demand horizon history next ∧ refuted horizon bound history next = false := by
  have parts := uncertain
  simp only [ambiguous, Bool.and_eq_true, decide_eq_true_eq] at parts
  refine ⟨parts.1, ?_⟩
  cases flag : refuted horizon bound history next with
  | false => rfl
  | true => simp [flag] at parts

def widen (bound needed : Nat) : Nat := max bound needed

theorem widen_monotone (bound needed : Nat) : bound ≤ widen bound needed := by
  unfold widen
  omega

theorem widen_covers (bound needed : Nat) : needed ≤ widen bound needed := by
  unfold widen
  omega

theorem widen_strict {bound needed : Nat} (exceeded : bound < needed) :
    bound + 1 ≤ widen bound needed := by
  unfold widen
  omega

def fit (cap bound needed : Nat) : Option Nat :=
  if widen bound needed ≤ cap then some (widen bound needed) else none

theorem fit_spec {cap bound needed chosen : Nat} (accepted : fit cap bound needed = some chosen) :
    chosen = widen bound needed ∧ bound ≤ chosen ∧ needed ≤ chosen ∧ chosen ≤ cap := by
  unfold fit at accepted
  split at accepted
  next enough =>
    have same := Option.some.inj accepted
    subst chosen
    exact ⟨rfl, widen_monotone _ _, widen_covers _ _, enough⟩
  next => contradiction

theorem cap_exhaustion (cap bound needed : Nat) (tooLarge : cap < needed) :
    fit cap bound needed = none := by
  have above : ¬ widen bound needed ≤ cap := by have := widen_covers bound needed; omega
  simp [fit, above]

theorem fit_cannot_clamp {cap bound needed chosen : Nat}
    (accepted : fit cap bound needed = some chosen) : needed ≤ chosen :=
  (fit_spec accepted).2.2.1

theorem old_sample_remains_irrelevant {horizon now later : Nat} {old next : Sample}
    (expired : old.time + horizon < now) (future : now ≤ later) (stamp : next.time = later) :
    eligible horizon old next = false := by
  simp only [eligible, decide_eq_false_iff_not]
  omega

theorem finite_prefix_no_future_bound (past : Nat → Nat) (endTime bound : Nat) :
    ∃ alternative : Nat → Nat,
      (∀ t, t ≤ endTime → alternative t = past t) ∧
      alternative endTime + bound < alternative (endTime + 1) := by
  refine ⟨fun t => if t ≤ endTime then past t else past endTime + bound + 1, ?_, ?_⟩
  · intro t within; simp [within]
  · have later : ¬ endTime + 1 ≤ endTime := by omega
    simp [later]

def constantOld : Sample := ⟨0, Renewal.measurement 9 1⟩
def constantNext : Sample := ⟨1, Renewal.measurement 11 1⟩

theorem constant_truth_ambiguous_example :
    constantOld.interval.Contains 10 ∧ constantNext.interval.Contains 10 ∧
    demand 41 [constantOld] constantNext = 4 ∧
    ambiguous 41 0 [constantOld] constantNext = true ∧
    refuted 41 0 [constantOld] constantNext = false := by
  unfold Renewal.Interval.Contains
  decide

end LearnedVariation
