import LayeredMonotoneRecognition
import LayeredMonotoneCharacterization

/-! A complete three-layer trace for a saturated (A AND B) OR (C AND D).
All slots, routed pulses, and reference scores are specified here. -/
namespace LearnedCoincidence.Layered.Example

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF (ThresholdRead singleton)

private def mask₂ (a b : Bool) : Pattern 2 := fun i => if i = 0 then a else b

private def mask₄ (a b c d : Bool) : Pattern 4 :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

private theorem allMasks₂ (P : Pattern 2 → Prop) (h : ∀ a b, P (mask₂ a b)) : ∀ x, P x := by
  intro x
  have same : x = mask₂ (x 0) (x 1) := by
    funext i
    revert i
    simp [Fin.forall_fin_two, mask₂]
  rw [same]
  exact h _ _

private theorem allMasks₄ (P : Pattern 4 → Prop) (h : ∀ a b c d, P (mask₄ a b c d)) : ∀ x, P x := by
  intro x
  have same : x = mask₄ (x 0) (x 1) (x 2) (x 3) := by
    funext i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  rw [same]
  exact h _ _ _ _

def clock : SlotTiming := ⟨0, 1, 2⟩

private theorem clock_valid : clock.Valid := by
  unfold SlotTiming.Valid
  decide

private def term (i : Fin 2) : Pattern 4 :=
  if i = 0 then mask₄ true true false false else mask₄ false false true true

private def source (i a : Fin 2) : Fin 4 :=
  if i = 0 then (if a = 0 then 0 else 1) else (if a = 0 then 2 else 3)

private def firstNode (i : Fin 2) : Node 4 4 :=
  ⟨canonical .both, fun a => some (source i a), fun _ => 0, fun _ => term i⟩

private def copyNode (i : Fin 2) : Node 4 2 :=
  ⟨canonical .copy, fun a => if a = 0 then some i else none, fun _ => 0, fun _ => fun _ => true⟩

private def orNode : Node 4 2 :=
  ⟨canonical .either, some, fun _ => 0, term⟩

def firstLayer : Cascade 4 1 2 := .layer .input clock firstNode
def copyLayer : Cascade 4 2 2 := .layer firstLayer clock copyNode
def circuit : Cascade 4 3 1 := .layer copyLayer clock (fun _ => orNode)

private def arrivals (start : Rat) (x : Pattern M) : Fin M → Option Rat :=
  fun i => if x i then some start else none

def slot (start : Rat) (x : Pattern 2) (value : Int) (fires : Bool) : ReadObservation 2 :=
  ⟨start, arrivals start x, if fires then [start + 1] else [], value⟩

private theorem slot_timed (start : Rat) (x : Pattern 2) (value : Int) (fires : Bool) (level : Nat)
    (decoder : fires = decide ((level : Int) ≤ value)) :
    ThresholdRead level clock (slot start x value fires) := by
  have incoming (a : Fin 2) (t : Rat) (seen : arrivals start x a = some t) : t = start := by
    unfold arrivals at seen
    split at seen
    · exact (Option.some.inj seen).symm
    · contradiction
  have slack : start ≤ start + 1 := by
    simpa only [Rat.add_zero] using
      (Rat.add_le_add_left.mpr (show (0 : Rat) ≤ 1 by decide) : start + 0 ≤ start + 1)
  refine ⟨clock_valid, ?_, ?_, ?_⟩
  · intro a t seen
    have same := incoming a t seen
    subst t
    exact ⟨Rat.le_refl, by change start ≤ start + 0; rw [Rat.add_zero]; exact Rat.le_refl⟩
  · cases fires
    · trivial
    · change start ≤ start + 1 ∧ start + 1 ≤ start + 1 ∧ _
      exact ⟨slack, Rat.le_refl, fun a t seen => (incoming a t seen) ▸ slack⟩
  · cases fires <;> exact decoder

private def firstMask (x : Pattern 4) (i : Fin 2) : Pattern 2 := fun a => x (source i a)

private def termFires (x : Pattern 4) (i : Fin 2) : Bool :=
  firstMask x i 0 && firstMask x i 1

private def copyMask (x : Pattern 4) (i : Fin 2) : Pattern 2 :=
  mask₂ (termFires x i) false

private def andScore (y : Pattern 2) : Int :=
  (if y 0 then 4 else 0) + (if y 1 then 4 else 0)

private def copyScore (y : Pattern 2) : Int := if y 0 then 4 else 0

private def orScore (y : Pattern 2) : Int :=
  if y 0 then (if y 1 then 6 else 4) else (if y 1 then 4 else 0)

private def firstReplay (t : Rat) (x : Pattern 4) : ReadTrace firstLayer :=
  ⟨arrivals t x, fun i => slot t (firstMask x i) (andScore (firstMask x i)) (termFires x i),
    fun _ => andScore⟩

private def copyReplay (t : Rat) (x : Pattern 4) : ReadTrace copyLayer :=
  ⟨firstReplay t x,
    fun i => slot (t + 1) (copyMask x i) (copyScore (copyMask x i)) (termFires x i),
    fun _ => copyScore⟩

def replay (t : Rat) (x : Pattern 4) : ReadTrace circuit :=
  ⟨copyReplay t x,
    fun _ => slot (t + 2) (termFires x) (orScore (termFires x)) (termFires x 0 || termFires x 1),
    fun _ => orScore⟩

def test (x : Pattern 4) : ReadTrace circuit := replay 120 x

private def tFirst (i : Fin 2) (r : Nat) : Rat := (20 * i.val + 10 * r : Nat)
private def tCopy (i : Fin 2) (r : Nat) : Rat := (40 + 20 * i.val + 10 * r : Nat)
private def tOr (g : Fin 2) (r : Nat) : Rat := (80 + 20 * g.val + 10 * r : Nat)

private def firstTrain : TrainingTrace firstLayer :=
  ⟨(), fun i _ r => arrivals (tFirst i r) (term i),
    fun i _ r => slot (tFirst i r) fullMask (if r = 0 then 0 else 8) (decide (r ≠ 0))⟩

private def copyTrain : TrainingTrace copyLayer :=
  ⟨firstTrain, fun i _ r => firstReplay (tCopy i r) (fun _ => true),
    fun i _ r => slot (tCopy i r + 1) (singleton 0) (if r = 0 then 0 else 4) (decide (r ≠ 0))⟩

def train : TrainingTrace circuit :=
  ⟨copyTrain, fun _ g r => copyReplay (tOr g r) (term g),
    fun _ g r => slot (tOr g r + 2) (singleton g) (if r = 0 then 0 else 4) (decide (r ≠ 0))⟩

-- Each closed comparison is reduced by the kernel. Implications with an
-- unbounded round or input are first reduced to finite cases by ordinary proofs.
local macro "verifyNode" : tactic =>
  `(tactic| (
    refine ⟨canonical_valid _, ?_, ?_⟩
    · decide +kernel
    · rw [Fin.forall_fin_two]
      constructor <;> intro active <;> first | (apply funext; decide +kernel) | contradiction))

local macro "verifyAdditive" : tactic =>
  `(tactic| (
    refine ⟨?_, ?_⟩
    · apply slot_timed
      decide +kernel
    · unfold admissible
      decide +kernel))

local macro "verifyFiring" : tactic =>
  `(tactic| (
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply slot_timed
      decide +kernel
    · decide +kernel
    · apply allMasks₂
      intro a b
      cases a <;> cases b <;> decide +kernel
    · intro y anchor _
      first
      | (change y ∈ [fullMask] at anchor
         have same := List.mem_singleton.mp anchor
         subst y
         decide +kernel)
      | (change y ∈ [MonotoneDNF.singleton (0 : Fin 2)] at anchor
         have same := List.mem_singleton.mp anchor
         subst y
         decide +kernel)
      | (change y ∈ [MonotoneDNF.singleton (0 : Fin 2), MonotoneDNF.singleton 1] at anchor
         simp only [List.mem_cons, List.not_mem_nil, or_false] at anchor
         rcases anchor with same | same <;> rw [same] <;> decide +kernel)))

local macro "verifyRead" : tactic =>
  `(tactic| (
    refine ⟨?_, ?_⟩
    · unfold Routed
      decide +kernel
    · first | verifyAdditive | verifyFiring))

local macro "verifyFirstReplay" : tactic =>
  `(tactic| (
    refine ⟨?_, ?_⟩
    · apply funext
      decide +kernel
    · rw [Fin.forall_fin_two]
      constructor <;> verifyRead))

local macro "verifyCopyReplay" : tactic =>
  `(tactic| (
    refine ⟨?_, ?_⟩
    · verifyFirstReplay
    · rw [Fin.forall_fin_two]
      constructor <;> verifyRead))

local macro "verifyTrainTail" : tactic =>
  `(tactic| (
    refine ⟨?_, ?_⟩
    · unfold Routed
      decide +kernel
    · verifyAdditive))

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

private theorem first_valid : firstLayer.Valid := by
  refine ⟨trivial, clock_valid, ?_⟩
  rw [Fin.forall_fin_two]
  constructor <;> verifyNode

private theorem copy_valid : copyLayer.Valid := by
  refine ⟨first_valid, clock_valid, ?_⟩
  rw [Fin.forall_fin_two]
  constructor <;> verifyNode

private theorem valid : circuit.Valid := by
  refine ⟨copy_valid, clock_valid, ?_⟩
  intro i
  have only : i = 0 := by omega
  subst i
  verifyNode

private theorem rounds {r : Nat} (bound : r ≤ 1) : r = 0 ∨ r = 1 := by omega
private theorem ports (i : Fin 2) : i = 0 ∨ i = 1 := by omega

private theorem first_calibration : TrainingCalibration firstLayer firstTrain := by
  refine ⟨trivial, ?_⟩
  intro i g active r bound
  have g0 : g = 0 := by
    change g.val < 1 at active
    omega
  subst g
  rcases ports i with rfl | rfl <;> rcases rounds bound with rfl | rfl <;>
    (refine ⟨?_, ?_⟩
     · apply funext
       decide +kernel
     · verifyTrainTail)

private theorem copy_calibration : TrainingCalibration copyLayer copyTrain := by
  refine ⟨first_calibration, ?_⟩
  intro i g active r bound
  have g0 : g = 0 := by
    change g.val < 1 at active
    omega
  subst g
  rcases ports i with rfl | rfl <;> rcases rounds bound with rfl | rfl <;>
    (refine ⟨?_, ?_⟩
     · verifyFirstReplay
     · verifyTrainTail)

private theorem training_calibration : TrainingCalibration circuit train := by
  refine ⟨copy_calibration, ?_⟩
  intro i g _ r bound
  have only : i = 0 := by omega
  subst i
  rcases ports g with rfl | rfl <;> rcases rounds bound with rfl | rfl <;>
    (refine ⟨?_, ?_⟩
     · verifyCopyReplay
     · verifyTrainTail)

private theorem read_calibration : ∀ x, ReadCalibration circuit train x (test x) := by
  apply allMasks₄
  intro a b c d
  cases a <;> cases b <;> cases c <;> cases d <;>
    (refine ⟨?_, ?_⟩
     · verifyCopyReplay
     · intro i
       have only : i = 0 := by omega
       subst i
       verifyRead)

private instance (a b : List Window) : Decidable (BatchBefore a b) := by
  unfold BatchBefore
  infer_instance

private theorem training_separation : TrainingSeparation circuit train test := by
  refine ⟨by decide +kernel, ?_⟩
  apply allMasks₄
  intro a b c d
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem predicted_pair : ∀ x, circuit.predict x 0 = ((x 0 && x 1) || (x 2 && x 3)) := by
  apply allMasks₄
  intro a b c d
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

-- The final pair lands two units below the additive score, outside budget 1.
example : orNode.cell.score (orNode.cell.settledWrites (train.2.2 0)) fullMask = 8 ∧
    ((test (fun _ => true)).2.1 0).measuredScore = 6 := by decide +kernel

/-- In the example the observed training writes reach the guarded targets,
and the replay of every external mask computes the stated formula. -/
theorem three_layer_example :
    circuit.Trained train ∧
    ∀ x, observed circuit (test x) 0 = ((x 0 && x 1) || (x 2 && x 3)) := by
  obtain ⟨trained, decisions⟩ :=
    layered_monotone_recognition_one_sided 4 3 1 circuit valid train test
      training_separation training_calibration read_calibration
  exact ⟨trained, fun x => (congrFun (decisions x) 0).trans (predicted_pair x)⟩

end LearnedCoincidence.Layered.Example
