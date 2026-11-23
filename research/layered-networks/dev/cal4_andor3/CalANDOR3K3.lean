import LayeredWitnessSupport
import LayeredMonotoneCheckerProofs
import LayeredReadCheckAt

/-! Calibrated instance ANDOR3 ((x0 and x1) or x2), seed 9802, at K3: research/layered-networks/leancal.py. -/

namespace LearnedCoincidence.Layered.CalANDOR3K3

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (patterns)
open MonotoneDNF (InverterTiming rails)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

def timing1 : SlotTiming := ⟨(0 : Rat), (6 / 5 : Rat), (11 / 5 : Rat)⟩
def cell1_0 : Cell := { gate := .both, initialGain := fun a => if a.val = 0 then 223 else 223, help := 0, threshold := 100000, trainError := 8323, testError := 8323, dose := 12472, maxWrites := 5, rail := 1000000 }
def node1_0 : Node 3 3 := ⟨cell1_0, fun a => if a.val = 0 then some 0 else some 1, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [0, 1, 2] else pattern []⟩
def cell1_1 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 70623 else 0, help := 0, threshold := 100000, trainError := 3444, testError := 3444, dose := 9922, maxWrites := 4, rail := 1000000 }
def node1_1 : Node 3 3 := ⟨cell1_1, fun a => if a.val = 0 then some 2 else none, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [0, 1, 2] else pattern []⟩
def layer1 : Cascade 3 1 2 := .layer (Cascade.input : Cascade 3 0 3) timing1 fun i => if i.val = 0 then node1_0 else node1_1

def timing2 : SlotTiming := ⟨(6 / 5 : Rat), (12 / 5 : Rat), (17 / 5 : Rat)⟩
def cell2_0 : Cell := { gate := .either, initialGain := fun a => if a.val = 0 then 40697 else 59285, help := 0, threshold := 100000, trainError := 5129, testError := 9983, dose := 14969, maxWrites := 4, rail := 1000000 }
def node2_0 : Node 3 2 := ⟨cell2_0, fun a => if a.val = 0 then some 0 else some 1, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [0, 1] else pattern [2]⟩
def layer2 : Cascade 3 2 1 := .layer layer1 timing2 fun i => node2_0

def timing3 : SlotTiming := ⟨(12 / 5 : Rat), (18 / 5 : Rat), (23 / 5 : Rat)⟩
def cell3_0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 52891 else 0, help := 0, threshold := 100000, trainError := 4010, testError := 4010, dose := 12136, maxWrites := 5, rail := 1000000 }
def node3_0 : Node 3 1 := ⟨cell3_0, fun a => if a.val = 0 then some 0 else none, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [0, 1] else pattern []⟩
def layer3 : Cascade 3 3 1 := .layer layer2 timing3 fun i => node3_0

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
  | 0 => ([[(⟨(102873 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 101431, 0, 0])], [(⟨(102849 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 100546, 104174, 204720])], [(⟨(4113 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 50071, 50071, 100142]), (⟨(4113 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100358, 0, 0])]], [none, none, none])
  | 1 => ([[(⟨(107273 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 101429, 0, 0])], [(⟨(107249 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 100543, 104172, 204716])], [(⟨(4289 / 8 : Rat), arr2 (some (4289 / 8 : Rat)) (none), [], 50069⟩, [0, 50069, 50069, 100139]), (⟨(4289 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100356, 0, 0])]], [some (107201 / 200 : Rat), none, none])
  | 2 => ([[(⟨(111673 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 101428, 0, 0])], [(⟨(111649 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 100541, 104170, 204711])], [(⟨(4465 / 8 : Rat), arr2 (none) (some (4465 / 8 : Rat)), [], 50067⟩, [0, 50066, 50067, 100134]), (⟨(4465 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100355, 0, 0])]], [none, some (111601 / 200 : Rat), none])
  | 3 => ([[(⟨(116073 / 200 : Rat), arr2 (some (116473 / 200 : Rat)) (none), [(116669 / 200 : Rat)], 101425⟩, [0, 101425, 0, 0])], [(⟨(116049 / 200 : Rat), arr2 (some (116249 / 200 : Rat)) (none), [(116449 / 200 : Rat)], 100538⟩, [0, 100538, 104168, 204706])], [(⟨(4641 / 8 : Rat), arr2 (some (4641 / 8 : Rat)) (some (4641 / 8 : Rat)), [(4649 / 8 : Rat)], 100129⟩, [0, 50065, 50065, 100129]), (⟨(4641 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100353, 0, 0])]], [some (116001 / 200 : Rat), some (116001 / 200 : Rat), none])
  | 4 => ([[(⟨(120473 / 200 : Rat), arr2 (some (120861 / 200 : Rat)) (none), [(121057 / 200 : Rat)], 101423⟩, [0, 101423, 0, 0])], [(⟨(120449 / 200 : Rat), arr2 (none) (some (120649 / 200 : Rat)), [(120837 / 200 : Rat)], 104166⟩, [0, 100536, 104166, 204701])], [(⟨(4817 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 50063, 50063, 100126]), (⟨(4817 / 8 : Rat), arr2 (some (4817 / 8 : Rat)) (none), [(4825 / 8 : Rat)], 100352⟩, [0, 100352, 0, 0])]], [none, none, some (120401 / 200 : Rat)])
  | 5 => ([[(⟨(124873 / 200 : Rat), arr2 (some (125261 / 200 : Rat)) (none), [(125457 / 200 : Rat)], 101421⟩, [0, 101421, 0, 0])], [(⟨(124849 / 200 : Rat), arr2 (none) (some (125049 / 200 : Rat)), [(125237 / 200 : Rat)], 104163⟩, [0, 100533, 104163, 204697])], [(⟨(4993 / 8 : Rat), arr2 (some (4993 / 8 : Rat)) (none), [], 50061⟩, [0, 50061, 50061, 100122]), (⟨(4993 / 8 : Rat), arr2 (some (4993 / 8 : Rat)) (none), [(5001 / 8 : Rat)], 100351⟩, [0, 100351, 0, 0])]], [some (124801 / 200 : Rat), none, some (124801 / 200 : Rat)])
  | 6 => ([[(⟨(129273 / 200 : Rat), arr2 (some (129661 / 200 : Rat)) (none), [(129857 / 200 : Rat)], 101420⟩, [0, 101420, 0, 0])], [(⟨(129249 / 200 : Rat), arr2 (none) (some (129449 / 200 : Rat)), [(129637 / 200 : Rat)], 104161⟩, [0, 100530, 104161, 204691])], [(⟨(5169 / 8 : Rat), arr2 (none) (some (5169 / 8 : Rat)), [], 50059⟩, [0, 50058, 50059, 100117]), (⟨(5169 / 8 : Rat), arr2 (some (5169 / 8 : Rat)) (none), [(5177 / 8 : Rat)], 100349⟩, [0, 100349, 0, 0])]], [none, some (129201 / 200 : Rat), some (129201 / 200 : Rat)])
  | 7 => ([[(⟨(133673 / 200 : Rat), arr2 (some (133929 / 200 : Rat)) (none), [(5365 / 8 : Rat)], 101417⟩, [0, 101417, 0, 0])], [(⟨(133649 / 200 : Rat), arr2 (some (133849 / 200 : Rat)) (some (133849 / 200 : Rat)), [(26781 / 40 : Rat)], 204687⟩, [0, 100528, 104159, 204687])], [(⟨(5345 / 8 : Rat), arr2 (some (5345 / 8 : Rat)) (some (5345 / 8 : Rat)), [(5353 / 8 : Rat)], 100113⟩, [0, 50056, 50056, 100113]), (⟨(5345 / 8 : Rat), arr2 (some (5345 / 8 : Rat)) (none), [(5353 / 8 : Rat)], 100348⟩, [0, 100348, 0, 0])]], [some (133601 / 200 : Rat), some (133601 / 200 : Rat), some (133601 / 200 : Rat)])
  | _ => ([], [])
def test (k : Nat) : ReadTrace circuit := build circuit (testData k).1 (testData k).2
def code (y : Pattern 3) : Nat := (List.finRange 3).foldl (fun acc j => acc + if y j then 2 ^ j.val else 0) 0
def expect : Nat → Bool
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | _ => false
def lines (y : Pattern 3) : Pattern 3 := y

def lessonRow : Nat → Nat → Nat → Nat → List (List (ReadObservation 2 × List Int)) × List (Option Rat) × ReadObservation 2
  | 1, 0, 0, 0 => ([], [some (1601 / 200 : Rat), some (1601 / 200 : Rat), some (1601 / 200 : Rat)], ⟨(65 / 8 : Rat), arr2 (some (65 / 8 : Rat)) (some (65 / 8 : Rat)), [], 446⟩)
  | 1, 0, 0, 1 => ([], [some (6001 / 200 : Rat), some (6001 / 200 : Rat), some (6001 / 200 : Rat)], ⟨(241 / 8 : Rat), arr2 (some (241 / 8 : Rat)) (some (241 / 8 : Rat)), [], 25390⟩)
  | 1, 0, 0, 2 => ([], [some (10401 / 200 : Rat), some (10401 / 200 : Rat), some (10401 / 200 : Rat)], ⟨(417 / 8 : Rat), arr2 (some (417 / 8 : Rat)) (some (417 / 8 : Rat)), [], 50334⟩)
  | 1, 0, 0, 3 => ([], [some (14801 / 200 : Rat), some (14801 / 200 : Rat), some (14801 / 200 : Rat)], ⟨(593 / 8 : Rat), arr2 (some (593 / 8 : Rat)) (some (593 / 8 : Rat)), [], 75278⟩)
  | 1, 0, 0, 4 => ([], [some (19201 / 200 : Rat), some (19201 / 200 : Rat), some (19201 / 200 : Rat)], ⟨(769 / 8 : Rat), arr2 (some (769 / 8 : Rat)) (some (769 / 8 : Rat)), [(777 / 8 : Rat)], 100222⟩)
  | 1, 0, 0, 5 => ([], [some (23601 / 200 : Rat), some (23601 / 200 : Rat), some (23601 / 200 : Rat)], ⟨(945 / 8 : Rat), arr2 (some (945 / 8 : Rat)) (some (945 / 8 : Rat)), [(953 / 8 : Rat)], 100217⟩)
  | 1, 1, 0, 0 => ([], [some (1601 / 200 : Rat), some (1601 / 200 : Rat), some (1601 / 200 : Rat)], ⟨(65 / 8 : Rat), arr2 (some (65 / 8 : Rat)) (none), [], 70623⟩)
  | 1, 1, 0, 1 => ([], [some (6001 / 200 : Rat), some (6001 / 200 : Rat), some (6001 / 200 : Rat)], ⟨(241 / 8 : Rat), arr2 (some (241 / 8 : Rat)) (none), [], 80545⟩)
  | 1, 1, 0, 2 => ([], [some (10401 / 200 : Rat), some (10401 / 200 : Rat), some (10401 / 200 : Rat)], ⟨(417 / 8 : Rat), arr2 (some (417 / 8 : Rat)) (none), [], 90467⟩)
  | 1, 1, 0, 3 => ([], [some (14801 / 200 : Rat), some (14801 / 200 : Rat), some (14801 / 200 : Rat)], ⟨(593 / 8 : Rat), arr2 (some (593 / 8 : Rat)) (none), [(601 / 8 : Rat)], 100389⟩)
  | 1, 1, 0, 4 => ([], [some (19201 / 200 : Rat), some (19201 / 200 : Rat), some (19201 / 200 : Rat)], ⟨(769 / 8 : Rat), arr2 (some (769 / 8 : Rat)) (none), [(777 / 8 : Rat)], 100388⟩)
  | 2, 0, 0, 0 => ([[(⟨(1121 / 8 : Rat), arr2 (some (1121 / 8 : Rat)) (some (1121 / 8 : Rat)), [(1129 / 8 : Rat)], 100214⟩, [0, 50106, 50107, 100214]), (⟨(1121 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100385, 0, 0])]], [some (28001 / 200 : Rat), some (28001 / 200 : Rat), none], ⟨(28049 / 200 : Rat), arr2 (some (28249 / 200 : Rat)) (none), [], 40694⟩)
  | 2, 0, 0, 1 => ([[(⟨(1297 / 8 : Rat), arr2 (some (1297 / 8 : Rat)) (some (1297 / 8 : Rat)), [(1305 / 8 : Rat)], 100209⟩, [0, 50104, 50105, 100209]), (⟨(1297 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100382, 0, 0])]], [some (32401 / 200 : Rat), some (32401 / 200 : Rat), none], ⟨(32449 / 200 : Rat), arr2 (some (32649 / 200 : Rat)) (none), [], 55665⟩)
  | 2, 0, 0, 2 => ([[(⟨(1473 / 8 : Rat), arr2 (some (1473 / 8 : Rat)) (some (1473 / 8 : Rat)), [(1481 / 8 : Rat)], 100205⟩, [0, 50103, 50103, 100205]), (⟨(1473 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100381, 0, 0])]], [some (36801 / 200 : Rat), some (36801 / 200 : Rat), none], ⟨(36849 / 200 : Rat), arr2 (some (37049 / 200 : Rat)) (none), [], 70637⟩)
  | 2, 0, 0, 3 => ([[(⟨(1649 / 8 : Rat), arr2 (some (1649 / 8 : Rat)) (some (1649 / 8 : Rat)), [(1657 / 8 : Rat)], 100201⟩, [0, 50100, 50101, 100201]), (⟨(1649 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100379, 0, 0])]], [some (41201 / 200 : Rat), some (41201 / 200 : Rat), none], ⟨(41249 / 200 : Rat), arr2 (some (41449 / 200 : Rat)) (none), [], 85608⟩)
  | 2, 0, 0, 4 => ([[(⟨(1825 / 8 : Rat), arr2 (some (1825 / 8 : Rat)) (some (1825 / 8 : Rat)), [(1833 / 8 : Rat)], 100196⟩, [0, 50098, 50098, 100196]), (⟨(1825 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100378, 0, 0])]], [some (45601 / 200 : Rat), some (45601 / 200 : Rat), none], ⟨(45649 / 200 : Rat), arr2 (some (45849 / 200 : Rat)) (none), [(46049 / 200 : Rat)], 100578⟩)
  | 2, 0, 1, 0 => ([[(⟨(2177 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 50094, 50094, 100189]), (⟨(2177 / 8 : Rat), arr2 (some (2177 / 8 : Rat)) (none), [(2185 / 8 : Rat)], 100375⟩, [0, 100375, 0, 0])]], [none, none, some (54401 / 200 : Rat)], ⟨(54449 / 200 : Rat), arr2 (none) (some (54649 / 200 : Rat)), [], 59280⟩)
  | 2, 0, 1, 1 => ([[(⟨(2353 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 50091, 50092, 100184]), (⟨(2353 / 8 : Rat), arr2 (some (2353 / 8 : Rat)) (none), [(2361 / 8 : Rat)], 100373⟩, [0, 100373, 0, 0])]], [none, none, some (58801 / 200 : Rat)], ⟨(58849 / 200 : Rat), arr2 (none) (some (59049 / 200 : Rat)), [], 74251⟩)
  | 2, 0, 1, 2 => ([[(⟨(2529 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 50090, 50090, 100179]), (⟨(2529 / 8 : Rat), arr2 (some (2529 / 8 : Rat)) (none), [(2537 / 8 : Rat)], 100372⟩, [0, 100372, 0, 0])]], [none, none, some (63201 / 200 : Rat)], ⟨(63249 / 200 : Rat), arr2 (none) (some (63449 / 200 : Rat)), [], 89221⟩)
  | 2, 0, 1, 3 => ([[(⟨(2705 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 50088, 50088, 100176]), (⟨(2705 / 8 : Rat), arr2 (some (2705 / 8 : Rat)) (none), [(2713 / 8 : Rat)], 100371⟩, [0, 100371, 0, 0])]], [none, none, some (67601 / 200 : Rat)], ⟨(67649 / 200 : Rat), arr2 (none) (some (67849 / 200 : Rat)), [(68037 / 200 : Rat)], 104193⟩)
  | 2, 0, 1, 4 => ([[(⟨(2881 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 50086, 50086, 100172]), (⟨(2881 / 8 : Rat), arr2 (some (2881 / 8 : Rat)) (none), [(2889 / 8 : Rat)], 100369⟩, [0, 100369, 0, 0])]], [none, none, some (72001 / 200 : Rat)], ⟨(72049 / 200 : Rat), arr2 (none) (some (72249 / 200 : Rat)), [(72437 / 200 : Rat)], 104191⟩)
  | 3, 0, 0, 0 => ([[(⟨(76449 / 200 : Rat), arr2 (some (76649 / 200 : Rat)) (none), [(76849 / 200 : Rat)], 100561⟩, [0, 100561, 104188, 204749])], [(⟨(3057 / 8 : Rat), arr2 (some (3057 / 8 : Rat)) (some (3057 / 8 : Rat)), [(3065 / 8 : Rat)], 100167⟩, [0, 50083, 50084, 100167]), (⟨(3057 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100368, 0, 0])]], [some (76401 / 200 : Rat), some (76401 / 200 : Rat), none], ⟨(76473 / 200 : Rat), arr2 (some (76873 / 200 : Rat)) (none), [], 52892⟩)
  | 3, 0, 0, 1 => ([[(⟨(80849 / 200 : Rat), arr2 (some (81049 / 200 : Rat)) (none), [(81249 / 200 : Rat)], 100558⟩, [0, 100558, 104185, 204743])], [(⟨(3233 / 8 : Rat), arr2 (some (3233 / 8 : Rat)) (some (3233 / 8 : Rat)), [(3241 / 8 : Rat)], 100163⟩, [0, 50081, 50081, 100163]), (⟨(3233 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100366, 0, 0])]], [some (80801 / 200 : Rat), some (80801 / 200 : Rat), none], ⟨(80873 / 200 : Rat), arr2 (some (81273 / 200 : Rat)) (none), [], 65027⟩)
  | 3, 0, 0, 2 => ([[(⟨(85249 / 200 : Rat), arr2 (some (85449 / 200 : Rat)) (none), [(85649 / 200 : Rat)], 100556⟩, [0, 100556, 104183, 204739])], [(⟨(3409 / 8 : Rat), arr2 (some (3409 / 8 : Rat)) (some (3409 / 8 : Rat)), [(3417 / 8 : Rat)], 100159⟩, [0, 50079, 50080, 100159]), (⟨(3409 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100365, 0, 0])]], [some (85201 / 200 : Rat), some (85201 / 200 : Rat), none], ⟨(85273 / 200 : Rat), arr2 (some (85673 / 200 : Rat)) (none), [], 77163⟩)
  | 3, 0, 0, 3 => ([[(⟨(89649 / 200 : Rat), arr2 (some (89849 / 200 : Rat)) (none), [(90049 / 200 : Rat)], 100553⟩, [0, 100553, 104181, 204734])], [(⟨(3585 / 8 : Rat), arr2 (some (3585 / 8 : Rat)) (some (3585 / 8 : Rat)), [(3593 / 8 : Rat)], 100155⟩, [0, 50078, 50078, 100155]), (⟨(3585 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100363, 0, 0])]], [some (89601 / 200 : Rat), some (89601 / 200 : Rat), none], ⟨(89673 / 200 : Rat), arr2 (some (90073 / 200 : Rat)) (none), [], 89299⟩)
  | 3, 0, 0, 4 => ([[(⟨(94049 / 200 : Rat), arr2 (some (94249 / 200 : Rat)) (none), [(94449 / 200 : Rat)], 100551⟩, [0, 100551, 104179, 204730])], [(⟨(3761 / 8 : Rat), arr2 (some (3761 / 8 : Rat)) (some (3761 / 8 : Rat)), [(3769 / 8 : Rat)], 100151⟩, [0, 50075, 50076, 100151]), (⟨(3761 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100362, 0, 0])]], [some (94001 / 200 : Rat), some (94001 / 200 : Rat), none], ⟨(94073 / 200 : Rat), arr2 (some (94473 / 200 : Rat)) (none), [(94669 / 200 : Rat)], 101436⟩)
  | 3, 0, 0, 5 => ([[(⟨(98449 / 200 : Rat), arr2 (some (98649 / 200 : Rat)) (none), [(98849 / 200 : Rat)], 100548⟩, [0, 100548, 104177, 204724])], [(⟨(3937 / 8 : Rat), arr2 (some (3937 / 8 : Rat)) (some (3937 / 8 : Rat)), [(3945 / 8 : Rat)], 100146⟩, [0, 50073, 50073, 100146]), (⟨(3937 / 8 : Rat), arr2 (none) (none), [], 0⟩, [0, 100360, 0, 0])]], [some (98401 / 200 : Rat), some (98401 / 200 : Rat), none], ⟨(98473 / 200 : Rat), arr2 (some (98873 / 200 : Rat)) (none), [(99069 / 200 : Rat)], 101433⟩)
  | _, _, _, _ => ([], [], blankRead)
def buildTrain : (c : Cascade M L N) → TrainingTrace c
  | .input => ()
  | .layer (L := L) lower _ _ => ⟨buildTrain lower,
      fun i g r => build lower (lessonRow (L + 1) i.val g.val r).1 (lessonRow (L + 1) i.val g.val r).2.1,
      fun i g r => (lessonRow (L + 1) i.val g.val r).2.2⟩
def train : TrainingTrace circuit := buildTrain circuit

theorem valid_check : checkLayeredValid circuit = false := by decide +kernel
theorem training_check : checkLayeredTrainingCalibration circuit train = true := by decide +kernel
theorem reads_check : ((patterns 3).all fun y => Checker.oneRead circuit train (lines y) (test (code y))) = true := by decide +kernel
theorem predicted_check : ((patterns 3).all fun y => circuit.predict (lines y) 0 == expect (code y)) = true := by decide +kernel

end LearnedCoincidence.Layered.CalANDOR3K3
