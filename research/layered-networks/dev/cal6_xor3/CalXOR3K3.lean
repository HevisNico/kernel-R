import LayeredWitnessSupport
import LayeredMonotoneCheckerProofs
import LayeredReadCheckAt
import LayeredInverters
import LayeredChainChecks
import LayeredIntrinsic

/-! Calibrated instance XOR3 (x0 xor x1), seed 9803, at K3: research/layered-networks/leancal.py. -/

namespace LearnedCoincidence.Layered.CalXOR3K3

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (patterns)
open MonotoneDNF (InverterTiming rails)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

def timing1 : SlotTiming := ⟨(1 / 5 : Rat), (7 / 5 : Rat), (12 / 5 : Rat)⟩
def cell1_0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 35463 else 35463, help := 0, threshold := 100000, trainError := 2687, testError := 2687, dose := 8067, maxWrites := 3, rail := 1000000 }
def node1_0 : Node 4 4 := ⟨cell1_0, fun a => if a.val = 0 then some 0 else some 3, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [0, 3] else pattern []⟩
def cell1_1 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 40332 else 40332, help := 0, threshold := 100000, trainError := 2483, testError := 2483, dose := 7458, maxWrites := 3, rail := 1000000 }
def node1_1 : Node 4 4 := ⟨cell1_1, fun a => if a.val = 0 then some 2 else some 1, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [1, 2] else pattern []⟩
def layer1 : Cascade 4 1 2 := .layer (Cascade.input : Cascade 4 0 4) timing1 fun i => if i.val = 0 then node1_0 else node1_1

def timing2 : SlotTiming := ⟨(7 / 5 : Rat), (13 / 5 : Rat), (18 / 5 : Rat)⟩
def cell2_0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 52571 else 47429, help := 0, threshold := 100000, trainError := 3277, testError := 6457, dose := 19587, maxWrites := 4, rail := 1000000 }
def node2_0 : Node 4 2 := ⟨cell2_0, fun a => if a.val = 0 then some 0 else some 1, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [0, 3] else pattern [1, 2]⟩
def layer2 : Cascade 4 2 1 := .layer layer1 timing2 fun i => node2_0

def timing3 : SlotTiming := ⟨(13 / 5 : Rat), (19 / 5 : Rat), (24 / 5 : Rat)⟩
def cell3_0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 79824 else 0, help := 0, threshold := 100000, trainError := 1444, testError := 1444, dose := 8772, maxWrites := 4, rail := 1000000 }
def node3_0 : Node 4 1 := ⟨cell3_0, fun a => if a.val = 0 then some 0 else none, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [0, 3] else pattern []⟩
def layer3 : Cascade 4 3 1 := .layer layer2 timing3 fun i => node3_0

def circuit := layer3

def blankRead : ReadObservation 2 := ⟨0, fun _ => none, [], 0⟩
def blankInv : ReadObservation 1 := ⟨0, fun _ => none, [], 0⟩
def arr2 (a b : Option Rat) : Fin 2 → Option Rat := fun j => if j.val = 0 then a else b
def maskIdx (y : Pattern 2) : Nat := (if y 0 then 1 else 0) + (if y 1 then 2 else 0)

/-- A trace constructor from data rows (top layer first; each read with its four reference scores) and the
line arrivals. No proof obligation. -/
def build : (c : Cascade M L N) → List (List (ReadObservation 2 × List Int)) → List (Option Rat) → ReadTrace c
  | .input, _, ext => fun j => ext.getD j.val none
  | .layer lower _ _, rows, ext => ⟨build lower rows.tail ext,
      fun i => ((rows.headD []).getD i.val (blankRead, [])).1,
      fun i y => (((rows.headD []).getD i.val (blankRead, [])).2).getD (maskIdx y) 0⟩

def testData : Nat → List (List (ReadObservation 2 × List Int)) × List (Option Rat)
  | 0 => ([[(⟨(102961 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 106139, 0, 0])], [(⟨(102937 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 111324, 106185, 217508])], [(⟨(102913 / 200 : Rat), arr2 (none) (some (102929 / 200 : Rat)), [], 51591⟩, [0, 51591, 51591, 103182]), (⟨(102913 / 200 : Rat), arr2 (some (102929 / 200 : Rat)) (none), [], 55243⟩, [0, 55243, 55243, 110486])]], [none, none, some (20581 / 40 : Rat), some (20581 / 40 : Rat)])
  | 1 => ([[(⟨(107361 / 200 : Rat), arr2 (some (107713 / 200 : Rat)) (none), [(107873 / 200 : Rat)], 106139⟩, [0, 106139, 0, 0])], [(⟨(107337 / 200 : Rat), arr2 (some (4301 / 8 : Rat)) (none), [(107689 / 200 : Rat)], 111323⟩, [0, 111323, 106184, 217507])], [(⟨(107313 / 200 : Rat), arr2 (some (107313 / 200 : Rat)) (some (107329 / 200 : Rat)), [(107501 / 200 : Rat)], 103181⟩, [0, 51591, 51590, 103181]), (⟨(107313 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55243, 55243, 110486])]], [some (107289 / 200 : Rat), none, none, some (21461 / 40 : Rat)])
  | 2 => ([[(⟨(111761 / 200 : Rat), arr2 (some (112101 / 200 : Rat)) (none), [(112261 / 200 : Rat)], 106138⟩, [0, 106138, 0, 0])], [(⟨(111737 / 200 : Rat), arr2 (none) (some (111901 / 200 : Rat)), [(112077 / 200 : Rat)], 106183⟩, [0, 111321, 106183, 217505])], [(⟨(111713 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 51590, 51590, 103181]), (⟨(111713 / 200 : Rat), arr2 (some (111729 / 200 : Rat)) (some (111713 / 200 : Rat)), [(111877 / 200 : Rat)], 110485⟩, [0, 55243, 55242, 110485])]], [none, some (111689 / 200 : Rat), some (22341 / 40 : Rat), none])
  | 3 => ([[(⟨(116161 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 106138, 0, 0])], [(⟨(116137 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 111321, 106182, 217502])], [(⟨(116113 / 200 : Rat), arr2 (some (116113 / 200 : Rat)) (none), [], 51590⟩, [0, 51590, 51590, 103180]), (⟨(116113 / 200 : Rat), arr2 (none) (some (116113 / 200 : Rat)), [], 55242⟩, [0, 55243, 55242, 110485])]], [some (116089 / 200 : Rat), some (116089 / 200 : Rat), none, none])
  | _ => ([], [])
def test (k : Nat) : ReadTrace circuit := build circuit (testData k).1 (testData k).2
def code (y : Pattern 2) : Nat := (List.finRange 2).foldl (fun acc j => acc + if y j then 2 ^ j.val else 0) 0
def expect : Nat → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false
  | _ => false
def lines (y : Pattern 2) : Pattern 4 := rails y

def lessonRow : Nat → Nat → Nat → Nat → List (List (ReadObservation 2 × List Int)) × List (Option Rat) × ReadObservation 2
  | 1, 0, 0, 0 => ([], [some (1689 / 200 : Rat), none, none, some (341 / 40 : Rat)], ⟨(1713 / 200 : Rat), arr2 (some (1713 / 200 : Rat)) (some (1729 / 200 : Rat)), [], 70926⟩)
  | 1, 0, 0, 1 => ([], [some (6089 / 200 : Rat), none, none, some (1221 / 40 : Rat)], ⟨(6113 / 200 : Rat), arr2 (some (6113 / 200 : Rat)) (some (6129 / 200 : Rat)), [], 87060⟩)
  | 1, 0, 0, 2 => ([], [some (10489 / 200 : Rat), none, none, some (2101 / 40 : Rat)], ⟨(10513 / 200 : Rat), arr2 (some (10513 / 200 : Rat)) (some (10529 / 200 : Rat)), [(10701 / 200 : Rat)], 103194⟩)
  | 1, 0, 0, 3 => ([], [some (14889 / 200 : Rat), none, none, some (2981 / 40 : Rat)], ⟨(14913 / 200 : Rat), arr2 (some (14913 / 200 : Rat)) (some (14929 / 200 : Rat)), [(15101 / 200 : Rat)], 103193⟩)
  | 1, 1, 0, 0 => ([], [none, some (19289 / 200 : Rat), some (3861 / 40 : Rat), none], ⟨(19313 / 200 : Rat), arr2 (some (19329 / 200 : Rat)) (some (19313 / 200 : Rat)), [], 80664⟩)
  | 1, 1, 0, 1 => ([], [none, some (23689 / 200 : Rat), some (4741 / 40 : Rat), none], ⟨(23713 / 200 : Rat), arr2 (some (23729 / 200 : Rat)) (some (23713 / 200 : Rat)), [], 95580⟩)
  | 1, 1, 0, 2 => ([], [none, some (28089 / 200 : Rat), some (5621 / 40 : Rat), none], ⟨(28113 / 200 : Rat), arr2 (some (28129 / 200 : Rat)) (some (28113 / 200 : Rat)), [(28277 / 200 : Rat)], 110496⟩)
  | 1, 1, 0, 3 => ([], [none, some (32489 / 200 : Rat), some (6501 / 40 : Rat), none], ⟨(32513 / 200 : Rat), arr2 (some (32529 / 200 : Rat)) (some (32513 / 200 : Rat)), [(32677 / 200 : Rat)], 110495⟩)
  | 2, 0, 0, 0 => ([[(⟨(36913 / 200 : Rat), arr2 (some (36913 / 200 : Rat)) (some (36929 / 200 : Rat)), [(37101 / 200 : Rat)], 103190⟩, [0, 51595, 51595, 103190]), (⟨(36913 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55247, 55247, 110495])]], [some (36889 / 200 : Rat), none, none, some (7381 / 40 : Rat)], ⟨(36937 / 200 : Rat), arr2 (some (1485 / 8 : Rat)) (none), [], 52571⟩)
  | 2, 0, 0, 1 => ([[(⟨(41313 / 200 : Rat), arr2 (some (41313 / 200 : Rat)) (some (41329 / 200 : Rat)), [(41501 / 200 : Rat)], 103190⟩, [0, 51595, 51595, 103190]), (⟨(41313 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55247, 55247, 110494])]], [some (41289 / 200 : Rat), none, none, some (8261 / 40 : Rat)], ⟨(41337 / 200 : Rat), arr2 (some (1661 / 8 : Rat)) (none), [], 72160⟩)
  | 2, 0, 0, 2 => ([[(⟨(45713 / 200 : Rat), arr2 (some (45713 / 200 : Rat)) (some (45729 / 200 : Rat)), [(45901 / 200 : Rat)], 103189⟩, [0, 51595, 51595, 103189]), (⟨(45713 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55247, 55247, 110494])]], [some (45689 / 200 : Rat), none, none, some (9141 / 40 : Rat)], ⟨(45737 / 200 : Rat), arr2 (some (1837 / 8 : Rat)) (none), [], 91748⟩)
  | 2, 0, 0, 3 => ([[(⟨(50113 / 200 : Rat), arr2 (some (50113 / 200 : Rat)) (some (50129 / 200 : Rat)), [(50301 / 200 : Rat)], 103189⟩, [0, 51594, 51594, 103189]), (⟨(50113 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55247, 55246, 110493])]], [some (50089 / 200 : Rat), none, none, some (10021 / 40 : Rat)], ⟨(50137 / 200 : Rat), arr2 (some (2013 / 8 : Rat)) (none), [(50489 / 200 : Rat)], 111335⟩)
  | 2, 0, 0, 4 => ([[(⟨(54513 / 200 : Rat), arr2 (some (54513 / 200 : Rat)) (some (54529 / 200 : Rat)), [(54701 / 200 : Rat)], 103188⟩, [0, 51594, 51594, 103188]), (⟨(54513 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55246, 55246, 110492])]], [some (54489 / 200 : Rat), none, none, some (10901 / 40 : Rat)], ⟨(54537 / 200 : Rat), arr2 (some (2189 / 8 : Rat)) (none), [(54889 / 200 : Rat)], 111335⟩)
  | 2, 0, 1, 0 => ([[(⟨(58913 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 51594, 51594, 103188]), (⟨(58913 / 200 : Rat), arr2 (some (58929 / 200 : Rat)) (some (58913 / 200 : Rat)), [(59077 / 200 : Rat)], 110492⟩, [0, 55246, 55246, 110492])]], [none, some (58889 / 200 : Rat), some (11781 / 40 : Rat), none], ⟨(58937 / 200 : Rat), arr2 (none) (some (59101 / 200 : Rat)), [], 47428⟩)
  | 2, 0, 1, 1 => ([[(⟨(63313 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 51594, 51593, 103187]), (⟨(63313 / 200 : Rat), arr2 (some (63329 / 200 : Rat)) (some (63313 / 200 : Rat)), [(63477 / 200 : Rat)], 110491⟩, [0, 55246, 55246, 110491])]], [none, some (63289 / 200 : Rat), some (12661 / 40 : Rat), none], ⟨(63337 / 200 : Rat), arr2 (none) (some (63501 / 200 : Rat)), [], 67017⟩)
  | 2, 0, 1, 2 => ([[(⟨(67713 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 51593, 51593, 103187]), (⟨(67713 / 200 : Rat), arr2 (some (67729 / 200 : Rat)) (some (67713 / 200 : Rat)), [(67877 / 200 : Rat)], 110491⟩, [0, 55246, 55245, 110491])]], [none, some (67689 / 200 : Rat), some (13541 / 40 : Rat), none], ⟨(67737 / 200 : Rat), arr2 (none) (some (67901 / 200 : Rat)), [], 86605⟩)
  | 2, 0, 1, 3 => ([[(⟨(72113 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 51593, 51593, 103186]), (⟨(72113 / 200 : Rat), arr2 (some (72129 / 200 : Rat)) (some (72113 / 200 : Rat)), [(72277 / 200 : Rat)], 110490⟩, [0, 55245, 55245, 110490])]], [none, some (72089 / 200 : Rat), some (14421 / 40 : Rat), none], ⟨(72137 / 200 : Rat), arr2 (none) (some (72301 / 200 : Rat)), [(72477 / 200 : Rat)], 106192⟩)
  | 2, 0, 1, 4 => ([[(⟨(76513 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 51593, 51593, 103185]), (⟨(76513 / 200 : Rat), arr2 (some (76529 / 200 : Rat)) (some (76513 / 200 : Rat)), [(76677 / 200 : Rat)], 110490⟩, [0, 55245, 55245, 110490])]], [none, some (76489 / 200 : Rat), some (15301 / 40 : Rat), none], ⟨(76537 / 200 : Rat), arr2 (none) (some (76701 / 200 : Rat)), [(76877 / 200 : Rat)], 106191⟩)
  | 3, 0, 0, 0 => ([[(⟨(80937 / 200 : Rat), arr2 (some (3245 / 8 : Rat)) (none), [(81289 / 200 : Rat)], 111329⟩, [0, 111329, 106190, 217518])], [(⟨(80913 / 200 : Rat), arr2 (some (80913 / 200 : Rat)) (some (80929 / 200 : Rat)), [(81101 / 200 : Rat)], 103185⟩, [0, 51593, 51592, 103185]), (⟨(80913 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55245, 55244, 110489])]], [some (80889 / 200 : Rat), none, none, some (16181 / 40 : Rat)], ⟨(80961 / 200 : Rat), arr2 (some (81313 / 200 : Rat)) (none), [], 79824⟩)
  | 3, 0, 0, 1 => ([[(⟨(85337 / 200 : Rat), arr2 (some (3421 / 8 : Rat)) (none), [(85689 / 200 : Rat)], 111327⟩, [0, 111327, 106189, 217516])], [(⟨(85313 / 200 : Rat), arr2 (some (85313 / 200 : Rat)) (some (85329 / 200 : Rat)), [(85501 / 200 : Rat)], 103184⟩, [0, 51592, 51592, 103184]), (⟨(85313 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55244, 55244, 110489])]], [some (85289 / 200 : Rat), none, none, some (17061 / 40 : Rat)], ⟨(85361 / 200 : Rat), arr2 (some (85713 / 200 : Rat)) (none), [], 88596⟩)
  | 3, 0, 0, 2 => ([[(⟨(89737 / 200 : Rat), arr2 (some (3597 / 8 : Rat)) (none), [(90089 / 200 : Rat)], 111327⟩, [0, 111327, 106187, 217514])], [(⟨(89713 / 200 : Rat), arr2 (some (89713 / 200 : Rat)) (some (89729 / 200 : Rat)), [(89901 / 200 : Rat)], 103184⟩, [0, 51592, 51592, 103184]), (⟨(89713 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55244, 55244, 110488])]], [some (89689 / 200 : Rat), none, none, some (17941 / 40 : Rat)], ⟨(89761 / 200 : Rat), arr2 (some (90113 / 200 : Rat)) (none), [], 97368⟩)
  | 3, 0, 0, 3 => ([[(⟨(94137 / 200 : Rat), arr2 (some (3773 / 8 : Rat)) (none), [(94489 / 200 : Rat)], 111326⟩, [0, 111326, 106187, 217513])], [(⟨(94113 / 200 : Rat), arr2 (some (94113 / 200 : Rat)) (some (94129 / 200 : Rat)), [(94301 / 200 : Rat)], 103183⟩, [0, 51592, 51591, 103183]), (⟨(94113 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55244, 55244, 110487])]], [some (94089 / 200 : Rat), none, none, some (18821 / 40 : Rat)], ⟨(94161 / 200 : Rat), arr2 (some (94513 / 200 : Rat)) (none), [(94673 / 200 : Rat)], 106140⟩)
  | 3, 0, 0, 4 => ([[(⟨(98537 / 200 : Rat), arr2 (some (3949 / 8 : Rat)) (none), [(98889 / 200 : Rat)], 111324⟩, [0, 111324, 106186, 217510])], [(⟨(98513 / 200 : Rat), arr2 (some (98513 / 200 : Rat)) (some (98529 / 200 : Rat)), [(98701 / 200 : Rat)], 103182⟩, [0, 51591, 51591, 103182]), (⟨(98513 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 55244, 55243, 110487])]], [some (98489 / 200 : Rat), none, none, some (19701 / 40 : Rat)], ⟨(98561 / 200 : Rat), arr2 (some (98913 / 200 : Rat)) (none), [(99073 / 200 : Rat)], 106140⟩)
  | _, _, _, _ => ([], [], blankRead)
def buildTrain : (c : Cascade M L N) → TrainingTrace c
  | .input => ()
  | .layer (L := L) lower _ _ => ⟨buildTrain lower,
      fun i g r => build lower (lessonRow (L + 1) i.val g.val r).1 (lessonRow (L + 1) i.val g.val r).2.1,
      fun i g r => (lessonRow (L + 1) i.val g.val r).2.2⟩
def train : TrainingTrace circuit := buildTrain circuit

theorem valid_check : checkLayeredValid circuit = false := by decide +kernel
theorem training_check : checkLayeredTrainingCalibration circuit train = true := by decide +kernel
theorem reads_check : ((patterns 2).all fun y => Checker.oneRead circuit train (lines y) (test (code y))) = true := by decide +kernel
theorem predicted_check : ((patterns 2).all fun y => circuit.predict (lines y) 0 == expect (code y)) = true := by decide +kernel

/-! The front end and the latency chain (measure.py's timing, config.json's design constants). -/

def sched (T : Rat) : Nat → Rat := fun k => T + (if k = 0 then (11 / 25 : Rat) else if k = 1 then (14 / 25 : Rat) else if k = 2 then (17 / 25 : Rat) else (4 / 5 : Rat))
def dmin : Nat → Rat := fun k => if k = 1 then (37 / 50 : Rat) else if k = 2 then (41 / 50 : Rat) else (4 / 5 : Rat)
def dmax : Nat → Rat := fun k => if k = 1 then (43 / 50 : Rat) else if k = 2 then (22 / 25 : Rat) else (4 / 5 : Rat)
def w : Rat := (1 / 5 : Rat)
def lhigh : Nat → Rat := fun k => layerSkew circuit k + dmax k
def front : InverterTiming := ⟨(0 : Rat), (11 / 25 : Rat), (16 / 25 : Rat)⟩
def testT : Nat → Rat
  | 0 => (102801 / 200 : Rat)
  | 1 => (107201 / 200 : Rat)
  | 2 => (111601 / 200 : Rat)
  | 3 => (116001 / 200 : Rat)
  | _ => 0
def testInv : Nat → List (ReadObservation 1)
  | 0 => [⟨(102801 / 200 : Rat), fun _ => none, [(20581 / 40 : Rat)], 0⟩, ⟨(102801 / 200 : Rat), fun _ => none, [(20581 / 40 : Rat)], 0⟩]
  | 1 => [⟨(107201 / 200 : Rat), fun _ => some (107201 / 200 : Rat), [], 0⟩, ⟨(107201 / 200 : Rat), fun _ => none, [(21461 / 40 : Rat)], 0⟩]
  | 2 => [⟨(111601 / 200 : Rat), fun _ => none, [(22341 / 40 : Rat)], 0⟩, ⟨(111601 / 200 : Rat), fun _ => some (111601 / 200 : Rat), [], 0⟩]
  | 3 => [⟨(116001 / 200 : Rat), fun _ => some (116001 / 200 : Rat), [], 0⟩, ⟨(116001 / 200 : Rat), fun _ => some (116001 / 200 : Rat), [], 0⟩]
  | _ => []
def testExt (k : Nat) (y : Pattern 2) : Fin 2 → Option Rat := fun j => if y j then some (testT k) else none
def testInvs (k : Nat) : Fin 2 → ReadObservation 1 := fun j => (testInv k).getD j.val blankInv

theorem front_check : ((patterns 2).all fun y => let k := code y; checkChainDates (sched (testT k)) (latencyLow dmin) (latencyHigh w lhigh) circuit && checkLayeredFront front (testT k) (testExt k y) (testInvs k) circuit (test k) && checkScheduled (sched (testT k)) circuit (test k) && checkLatencies dmin lhigh circuit (test k)) = true := by decide +kernel
theorem realised_check : ((patterns 2).all fun y => let k := code y; (List.finRange 2).all fun j => (testExt k y j).isSome == y j) = true := by decide +kernel
theorem front_fit : (∀ T, sched T 0 = T + front.emitEarly) ∧ front.window ≤ w ∧ front.emitLate - front.emitEarly ≤ w := by
  refine ⟨fun T => ?_, by decide +kernel, by decide +kernel⟩
  simp [sched, front]

end LearnedCoincidence.Layered.CalXOR3K3
