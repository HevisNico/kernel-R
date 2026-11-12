import SelfCertifyingLearning.OfferFactory

/-! End-to-end finite witness: measurements generate both offers. Larger
measurement uncertainty raises the second certified ceiling although the
actual rate stays constant. The hardware and future-slew facts are explicit. -/
namespace SelfCertifyingLearning.FactoryExample
open Repair ClosedLoop Epochs OfferFactory

def policy : Policy := ⟨10, 19⟩
def hardware : Hardware := ⟨3, 10, 30, 4, 0⟩
def initial : Cursor := ⟨0, 20, 0, 2⟩
def firstReading : Reading := ⟨0, 2, 0⟩
def secondReading : Reading := ⟨5, 2, 1⟩
def firstOffer := make policy hardware firstReading 2
def secondCursor := advance initial firstOffer

def requests : List Request := [⟨firstReading, [2]⟩, ⟨secondReading, [2]⟩]
def program : Plan := OfferFactory.run policy hardware initial requests

def actualRate (_ : Nat) : Nat := 2

def world (t : Nat) : Int :=
  [20, 18, 16, 14, 12, 20, 18, 16, 24, 22, 20, 28, 26, 24].getD t
    ((28 : Int) - (2 * (t - 11) : Nat))

theorem first_evidence : Evidence policy hardware initial firstReading 2
    (fun t => actualRate (initial.now + t)) (fun t => world (initial.now + t)) := by
  constructor
  · decide
  · decide
  · intro k _; simp [actualRate, hardware]
  · have finite : ∀ k : Fin 8,
        world (initial.now + k.val) - (actualRate (initial.now + (k.val + 1)) : Int) ≤
          world (initial.now + (k.val + 1)) := by decide
    intro k hk
    exact finite ⟨k, hk⟩
  · simp only [Delivers]
    decide

theorem second_evidence : Evidence policy hardware secondCursor secondReading 2
    (fun t => actualRate (secondCursor.now + t)) (fun t => world (secondCursor.now + t)) := by
  constructor
  · decide
  · decide
  · intro k _; simp [actualRate, hardware]
  · have finite : ∀ k : Fin 8,
        world (secondCursor.now + k.val) - (actualRate (secondCursor.now + (k.val + 1)) : Int) ≤
          world (secondCursor.now + (k.val + 1)) := by decide
    intro k hk
    exact finite ⟨k, hk⟩
  · simp only [Delivers]
    decide

theorem supported : Supported policy hardware world actualRate initial requests := by
  change (∃ count ∈ [2], make policy hardware firstReading count = firstOffer ∧
    Evidence policy hardware initial firstReading count
      (fun t => actualRate (initial.now + t)) (fun t => world (initial.now + t))) ∧
    Supported policy hardware world actualRate secondCursor [⟨secondReading, [2]⟩]
  refine ⟨⟨2, by decide, rfl, first_evidence⟩, ?_⟩
  change (∃ count ∈ [2], make policy hardware secondReading count = make policy hardware secondReading 2 ∧
    Evidence policy hardware secondCursor secondReading count
      (fun t => actualRate (secondCursor.now + t)) (fun t => world (secondCursor.now + t))) ∧ True
  exact ⟨⟨2, by decide, rfl, second_evidence⟩, trivial⟩

theorem completed_summary : program.phases = 2 ∧ program.finish.now = 11 ∧
    program.finish.lower = 22 ∧ program.writes = 3 ∧ program.switchCost = 2 ∧
    program.finish.credit = 0 := by decide

theorem complete_service : EpochSafety.SafeBetween world 10 0 11 ∧ (22 : Int) ≤ world 11 :=
  system_safe (by decide) (by decide) supported

theorem complete_cost : program.writes ≤ initial.debt + initial.credit + program.leakBudget :=
  system_cost policy hardware initial requests

theorem stale_measurement_blocks :
    OfferFactory.run policy hardware secondCursor [⟨firstReading, [2]⟩] = .blocked secondCursor := rfl

theorem uncertainty_changes_ceiling : firstOffer.config.bound = 2 ∧
    (make policy hardware secondReading 2).config.bound = 3 := by decide

/-- The certified horizon includes writes even if the requested wait cap
is shorter than a write. The phase clock is bounded before deriving a rate. -/
theorem horizon_includes_writes : horizon { hardware with maxWait := 1 } 2 = 6 := by decide

end SelfCertifyingLearning.FactoryExample
