import PhysicalEvaluator.Asymmetric

namespace ReusableController.PhysicalEvaluator.AsymmetricData

noncomputable def t6002p1 : AsymmetricEntry 2 where
  cellId := 6002
  port := 1
  level0 := (491306860829 / 500000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (593707149697 / 1000000000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (588765043351 / 100000000000000 : ℝ)
  epsilon := (520780950947 / 1000000000000000 : ℝ)
  ell := (38002653271 / 10000000000000 : ℝ)
  observed := fun k => [false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6003p1 : AsymmetricEntry 5 where
  cellId := 6003
  port := 1
  level0 := (104295908429 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (592994208913 / 100000000000000 : ℝ)
  baseBSilent := (97441689137 / 20000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (964576675959 / 1000000000000000 : ℝ)
  ell := (20070774429 / 5000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6004p1 : AsymmetricEntry 6 where
  cellId := 6004
  port := 1
  level0 := (101649007307 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (281419367837 / 50000000000000 : ℝ)
  baseBSilent := (394949179457 / 100000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (469671200673 / 500000000000000 : ℝ)
  ell := (263145366997 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6004p2 : AsymmetricEntry 4 where
  cellId := 6004
  port := 2
  level0 := (101649007307 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (350328876061 / 100000000000000 : ℝ)
  baseBSilent := (27506766937 / 20000000000000 : ℝ)
  baseBFire := (15831482053 / 5000000000000 : ℝ)
  epsilon := (378192763311 / 500000000000000 : ℝ)
  ell := (27326263123 / 5000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6005p1 : AsymmetricEntry 2 where
  cellId := 6005
  port := 1
  level0 := (997052042403 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (713714991111 / 100000000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (62140886731 / 50000000000000 : ℝ)
  epsilon := (511020932617 / 1000000000000000 : ℝ)
  ell := (468199710539 / 100000000000000 : ℝ)
  observed := fun k => [false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6008p1 : AsymmetricEntry 3 where
  cellId := 6008
  port := 1
  level0 := (496592287167 / 500000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (33293448539 / 6250000000000 : ℝ)
  baseBSilent := (539751980621 / 1000000000000000 : ℝ)
  baseBFire := (30999708717 / 12500000000000 : ℝ)
  epsilon := (608386021137 / 1000000000000000 : ℝ)
  ell := (64456004691 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6009p2 : AsymmetricEntry 3 where
  cellId := 6009
  port := 2
  level0 := (199039313773 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (256113724237 / 50000000000000 : ℝ)
  baseBSilent := (1102882077 / 1562500000000 : ℝ)
  baseBFire := (428979713591 / 500000000000000 : ℝ)
  epsilon := (316195576873 / 500000000000000 : ℝ)
  ell := (10600631737 / 2000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6010p1 : AsymmetricEntry 4 where
  cellId := 6010
  port := 1
  level0 := (101038209147 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (370699294979 / 50000000000000 : ℝ)
  baseBSilent := (855400243689 / 1000000000000000 : ℝ)
  baseBFire := (10614074071 / 3125000000000 : ℝ)
  epsilon := (160753007461 / 200000000000000 : ℝ)
  ell := (101882349009 / 20000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6011p2 : AsymmetricEntry 5 where
  cellId := 6011
  port := 2
  level0 := (100036553783 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (19140513101 / 6250000000000 : ℝ)
  baseBSilent := (645611040919 / 100000000000000 : ℝ)
  baseBFire := (32852277157 / 25000000000000 : ℝ)
  epsilon := (874112621161 / 1000000000000000 : ℝ)
  ell := (21558118663 / 5000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6012p1 : AsymmetricEntry 4 where
  cellId := 6012
  port := 1
  level0 := (61366029683 / 62500000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (221675833127 / 100000000000000 : ℝ)
  baseBSilent := (61739973303 / 20000000000000 : ℝ)
  baseBFire := (6329308057 / 5000000000000 : ℝ)
  epsilon := (727869338271 / 1000000000000000 : ℝ)
  ell := (93547558419 / 20000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6013p2 : AsymmetricEntry 3 where
  cellId := 6013
  port := 2
  level0 := (997781596883 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (520037102427 / 100000000000000 : ℝ)
  baseBSilent := (187629806169 / 100000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (131161982899 / 200000000000000 : ℝ)
  ell := (205794860991 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6015p1 : AsymmetricEntry 4 where
  cellId := 6015
  port := 1
  level0 := (2559470749 / 2500000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (230630426409 / 50000000000000 : ℝ)
  baseBSilent := (514013614927 / 1000000000000000 : ℝ)
  baseBFire := (360865319083 / 100000000000000 : ℝ)
  epsilon := (827315393429 / 1000000000000000 : ℝ)
  ell := (444956840723 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6016p1 : AsymmetricEntry 4 where
  cellId := 6016
  port := 1
  level0 := (247693710563 / 250000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (416477507449 / 50000000000000 : ℝ)
  baseBSilent := (96628176513 / 25000000000000 : ℝ)
  baseBFire := (504316394857 / 100000000000000 : ℝ)
  epsilon := (144903824999 / 200000000000000 : ℝ)
  ell := (43985788911 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6018p2 : AsymmetricEntry 3 where
  cellId := 6018
  port := 2
  level0 := (100496638391 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (91127336943 / 25000000000000 : ℝ)
  baseBSilent := (4751684001 / 3125000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (42352907969 / 62500000000000 : ℝ)
  ell := (499062359671 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6019p2 : AsymmetricEntry 4 where
  cellId := 6019
  port := 2
  level0 := (12516871121 / 12500000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (153020413097 / 20000000000000 : ℝ)
  baseBSilent := (97947626749 / 25000000000000 : ℝ)
  baseBFire := (189739447713 / 100000000000000 : ℝ)
  epsilon := (71984958711 / 100000000000000 : ℝ)
  ell := (62790895379 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6025p1 : AsymmetricEntry 4 where
  cellId := 6025
  port := 1
  level0 := (50336216699 / 50000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (863825998027 / 100000000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (103613102843 / 50000000000000 : ℝ)
  epsilon := (188777552921 / 250000000000000 : ℝ)
  ell := (458699443909 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6027p2 : AsymmetricEntry 3 where
  cellId := 6027
  port := 2
  level0 := (491646781317 / 500000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (427947079553 / 50000000000000 : ℝ)
  baseBSilent := (465314629879 / 500000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (599478540361 / 1000000000000000 : ℝ)
  ell := (507532090727 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6028p2 : AsymmetricEntry 4 where
  cellId := 6028
  port := 2
  level0 := (989852634407 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (511829546591 / 100000000000000 : ℝ)
  baseBSilent := (473022546897 / 500000000000000 : ℝ)
  baseBFire := (6448805597 / 1250000000000 : ℝ)
  epsilon := (362753861977 / 500000000000000 : ℝ)
  ell := (452383007527 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6030p1 : AsymmetricEntry 3 where
  cellId := 6030
  port := 1
  level0 := (10016016093 / 10000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (68975830857 / 12500000000000 : ℝ)
  baseBSilent := (554675372131 / 1000000000000000 : ℝ)
  baseBFire := (698464527621 / 100000000000000 : ℝ)
  epsilon := (316045035737 / 500000000000000 : ℝ)
  ell := (66121713523 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6031p1 : AsymmetricEntry 4 where
  cellId := 6031
  port := 1
  level0 := (970223031509 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (365829457391 / 50000000000000 : ℝ)
  baseBSilent := (3234423461 / 800000000000 : ℝ)
  baseBFire := (57452661121 / 20000000000000 : ℝ)
  epsilon := (701616561889 / 1000000000000000 : ℝ)
  ell := (213690221131 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6032p1 : AsymmetricEntry 3 where
  cellId := 6032
  port := 1
  level0 := (97395029201 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (51782725773 / 25000000000000 : ℝ)
  baseBSilent := (637176331587 / 100000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (148440171207 / 250000000000000 : ℝ)
  ell := (458673112593 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6032p2 : AsymmetricEntry 4 where
  cellId := 6032
  port := 2
  level0 := (97395029201 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (471751922731 / 100000000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (170890779421 / 50000000000000 : ℝ)
  epsilon := (139070231611 / 200000000000000 : ℝ)
  ell := (107073962397 / 20000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6037p1 : AsymmetricEntry 4 where
  cellId := 6037
  port := 1
  level0 := (197613333211 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (177866116403 / 25000000000000 : ℝ)
  baseBSilent := (62508536707 / 50000000000000 : ℝ)
  baseBFire := (24105544689 / 10000000000000 : ℝ)
  epsilon := (706450363667 / 1000000000000000 : ℝ)
  ell := (194009486263 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6037p2 : AsymmetricEntry 4 where
  cellId := 6037
  port := 2
  level0 := (197613333211 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (106458607533 / 10000000000000 : ℝ)
  baseBSilent := (244115283577 / 100000000000000 : ℝ)
  baseBFire := (190095891661 / 100000000000000 : ℝ)
  epsilon := (743034058747 / 1000000000000000 : ℝ)
  ell := (45175925057 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6040p2 : AsymmetricEntry 5 where
  cellId := 6040
  port := 2
  level0 := (998130957413 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (115294077429 / 25000000000000 : ℝ)
  baseBSilent := (283478555591 / 50000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (168326860387 / 200000000000000 : ℝ)
  ell := (566650781363 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6042p2 : AsymmetricEntry 5 where
  cellId := 6042
  port := 2
  level0 := (497818571609 / 500000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (337522158413 / 50000000000000 : ℝ)
  baseBSilent := (90438869907 / 50000000000000 : ℝ)
  baseBFire := (3013157601 / 2000000000000 : ℝ)
  epsilon := (880263292897 / 1000000000000000 : ℝ)
  ell := (53163608361 / 10000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6043p2 : AsymmetricEntry 5 where
  cellId := 6043
  port := 2
  level0 := (10138161991 / 10000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (41802049321 / 25000000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (799503540147 / 100000000000000 : ℝ)
  epsilon := (213980659741 / 250000000000000 : ℝ)
  ell := (514931251919 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6045p2 : AsymmetricEntry 4 where
  cellId := 6045
  port := 2
  level0 := (62084413703 / 62500000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (48069712117 / 6250000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (573951719739 / 100000000000000 : ℝ)
  epsilon := (750511959883 / 1000000000000000 : ℝ)
  ell := (192739955719 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6050p2 : AsymmetricEntry 4 where
  cellId := 6050
  port := 2
  level0 := (19535389203 / 20000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (24014890379 / 5000000000000 : ℝ)
  baseBSilent := (27719113573 / 5000000000000 : ℝ)
  baseBFire := (58638065319 / 20000000000000 : ℝ)
  epsilon := (683602683271 / 1000000000000000 : ℝ)
  ell := (46509573637 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6051p2 : AsymmetricEntry 3 where
  cellId := 6051
  port := 2
  level0 := (20035775199 / 20000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (65221711417 / 50000000000000 : ℝ)
  baseBSilent := (39833348737 / 25000000000000 : ℝ)
  baseBFire := (611761636791 / 100000000000000 : ℝ)
  epsilon := (313009297509 / 500000000000000 : ℝ)
  ell := (443974143399 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6052p1 : AsymmetricEntry 4 where
  cellId := 6052
  port := 1
  level0 := (492478557327 / 500000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (153591529957 / 20000000000000 : ℝ)
  baseBSilent := (38456777293 / 10000000000000 : ℝ)
  baseBFire := (34566372427 / 20000000000000 : ℝ)
  epsilon := (743140516879 / 1000000000000000 : ℝ)
  ell := (6986400583 / 1562500000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6055p1 : AsymmetricEntry 6 where
  cellId := 6055
  port := 1
  level0 := (123403901071 / 125000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (189595458631 / 20000000000000 : ℝ)
  baseBSilent := (189712598941 / 100000000000000 : ℝ)
  baseBFire := (221376112059 / 100000000000000 : ℝ)
  epsilon := (178545381031 / 200000000000000 : ℝ)
  ell := (492572836363 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6056p1 : AsymmetricEntry 5 where
  cellId := 6056
  port := 1
  level0 := (20234150859 / 20000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (109983439307 / 12500000000000 : ℝ)
  baseBSilent := (70814312491 / 20000000000000 : ℝ)
  baseBFire := (91582047077 / 50000000000000 : ℝ)
  epsilon := (912773522171 / 1000000000000000 : ℝ)
  ell := (16846590007 / 4000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6058p2 : AsymmetricEntry 4 where
  cellId := 6058
  port := 2
  level0 := (984513506533 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (75631509071 / 20000000000000 : ℝ)
  baseBSilent := (556805729403 / 100000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (695940240701 / 1000000000000000 : ℝ)
  ell := (364803571369 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6061p2 : AsymmetricEntry 3 where
  cellId := 6061
  port := 2
  level0 := (198124301459 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (183073322163 / 25000000000000 : ℝ)
  baseBSilent := (69609319767 / 20000000000000 : ℝ)
  baseBFire := (301774408391 / 500000000000000 : ℝ)
  epsilon := (31701948923 / 50000000000000 : ℝ)
  ell := (367928920077 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6063p1 : AsymmetricEntry 2 where
  cellId := 6063
  port := 1
  level0 := (983161897939 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (471501928873 / 100000000000000 : ℝ)
  baseBSilent := (232975027131 / 100000000000000 : ℝ)
  baseBFire := (73296631109 / 20000000000000 : ℝ)
  epsilon := (515253427591 / 1000000000000000 : ℝ)
  ell := (190721049139 / 50000000000000 : ℝ)
  observed := fun k => [false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6065p1 : AsymmetricEntry 4 where
  cellId := 6065
  port := 1
  level0 := (248769350279 / 250000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (225569272467 / 500000000000000 : ℝ)
  baseBSilent := (133270287619 / 200000000000000 : ℝ)
  baseBFire := (160585221477 / 100000000000000 : ℝ)
  epsilon := (744041707491 / 1000000000000000 : ℝ)
  ell := (96842002221 / 20000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6067p2 : AsymmetricEntry 3 where
  cellId := 6067
  port := 2
  level0 := (987918432557 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (216661279479 / 50000000000000 : ℝ)
  baseBSilent := (234965358763 / 50000000000000 : ℝ)
  baseBFire := (41578361199 / 12500000000000 : ℝ)
  epsilon := (77455842597 / 125000000000000 : ℝ)
  ell := (255537132991 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6068p2 : AsymmetricEntry 2 where
  cellId := 6068
  port := 2
  level0 := (992652268279 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (390055555947 / 50000000000000 : ℝ)
  baseBSilent := (4722753943 / 4000000000000 : ℝ)
  baseBFire := (198725065299 / 50000000000000 : ℝ)
  epsilon := (512342049297 / 1000000000000000 : ℝ)
  ell := (3160445227 / 781250000000 : ℝ)
  observed := fun k => [false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6074p1 : AsymmetricEntry 3 where
  cellId := 6074
  port := 1
  level0 := (1992418577 / 2000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (133533356797 / 50000000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (329318591639 / 100000000000000 : ℝ)
  epsilon := (20528528577 / 31250000000000 : ℝ)
  ell := (368999428613 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6075p1 : AsymmetricEntry 3 where
  cellId := 6075
  port := 1
  level0 := (199426086749 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (964380481389 / 100000000000000 : ℝ)
  baseBSilent := (193145854239 / 50000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (631922270089 / 1000000000000000 : ℝ)
  ell := (52218127747 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6075p2 : AsymmetricEntry 4 where
  cellId := 6075
  port := 2
  level0 := (199426086749 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (6520344039 / 2500000000000 : ℝ)
  baseBSilent := (224985219197 / 100000000000000 : ℝ)
  baseBFire := (266252676279 / 50000000000000 : ℝ)
  epsilon := (368269360609 / 500000000000000 : ℝ)
  ell := (30962565141 / 6250000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6076p1 : AsymmetricEntry 4 where
  cellId := 6076
  port := 1
  level0 := (100760212509 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (58075422149 / 12500000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (14293670183 / 3125000000000 : ℝ)
  epsilon := (190376366847 / 250000000000000 : ℝ)
  ell := (118353653053 / 25000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6077p1 : AsymmetricEntry 5 where
  cellId := 6077
  port := 1
  level0 := (100406760237 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (571170729331 / 100000000000000 : ℝ)
  baseBSilent := (358185314469 / 100000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (209395235343 / 250000000000000 : ℝ)
  ell := (1544505539 / 400000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6077p2 : AsymmetricEntry 5 where
  cellId := 6077
  port := 2
  level0 := (100406760237 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (312996555443 / 100000000000000 : ℝ)
  baseBSilent := (474316976383 / 100000000000000 : ℝ)
  baseBFire := (162190498471 / 500000000000000 : ℝ)
  epsilon := (6895245697 / 7812500000000 : ℝ)
  ell := (46491641389 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6079p1 : AsymmetricEntry 4 where
  cellId := 6079
  port := 1
  level0 := (100385428541 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (156876787 / 32000000000 : ℝ)
  baseBSilent := (57305700789 / 25000000000000 : ℝ)
  baseBFire := (317230554307 / 100000000000000 : ℝ)
  epsilon := (762030599603 / 1000000000000000 : ℝ)
  ell := (110958423391 / 25000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6080p2 : AsymmetricEntry 3 where
  cellId := 6080
  port := 2
  level0 := (249953056811 / 250000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (276967586211 / 50000000000000 : ℝ)
  baseBSilent := (511365327109 / 100000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (641099145411 / 1000000000000000 : ℝ)
  ell := (193662649187 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6081p1 : AsymmetricEntry 4 where
  cellId := 6081
  port := 1
  level0 := (977853550813 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (994316576193 / 100000000000000 : ℝ)
  baseBSilent := (24058076257 / 12500000000000 : ℝ)
  baseBFire := (374543303983 / 100000000000000 : ℝ)
  epsilon := (756068861691 / 1000000000000000 : ℝ)
  ell := (43312837641 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6082p2 : AsymmetricEntry 4 where
  cellId := 6082
  port := 2
  level0 := (50280500643 / 50000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (807206974821 / 100000000000000 : ℝ)
  baseBSilent := (22432072157 / 12500000000000 : ℝ)
  baseBFire := (59287485541 / 50000000000000 : ℝ)
  epsilon := (776835340601 / 1000000000000000 : ℝ)
  ell := (89303010611 / 25000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6085p2 : AsymmetricEntry 3 where
  cellId := 6085
  port := 2
  level0 := (24928022531 / 25000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (358218330029 / 50000000000000 : ℝ)
  baseBSilent := (611988140207 / 1000000000000000 : ℝ)
  baseBFire := (135554762599 / 20000000000000 : ℝ)
  epsilon := (32715577193 / 50000000000000 : ℝ)
  ell := (336595171431 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6088p2 : AsymmetricEntry 4 where
  cellId := 6088
  port := 2
  level0 := (101366041713 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (350946689403 / 100000000000000 : ℝ)
  baseBSilent := (4000001 / 10000000000 : ℝ)
  baseBFire := (738685158507 / 100000000000000 : ℝ)
  epsilon := (32386010889 / 40000000000000 : ℝ)
  ell := (123010515459 / 25000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6090p1 : AsymmetricEntry 4 where
  cellId := 6090
  port := 1
  level0 := (50073646041 / 50000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (31096360533 / 5000000000000 : ℝ)
  baseBSilent := (53610274731 / 10000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (753386217949 / 1000000000000000 : ℝ)
  ell := (425781203859 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6093p2 : AsymmetricEntry 4 where
  cellId := 6093
  port := 2
  level0 := (100412136401 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (842825521539 / 100000000000000 : ℝ)
  baseBSilent := (562675465549 / 1000000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (753764644333 / 1000000000000000 : ℝ)
  ell := (21085095297 / 5000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6095p2 : AsymmetricEntry 3 where
  cellId := 6095
  port := 2
  level0 := (995887535393 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (108856009913 / 12500000000000 : ℝ)
  baseBSilent := (979515740487 / 1000000000000000 : ℝ)
  baseBFire := (92006596607 / 500000000000000 : ℝ)
  epsilon := (16291915063 / 25000000000000 : ℝ)
  ell := (3214860941 / 781250000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6096p1 : AsymmetricEntry 3 where
  cellId := 6096
  port := 1
  level0 := (25138115681 / 25000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (177816937331 / 50000000000000 : ℝ)
  baseBSilent := (352417527347 / 100000000000000 : ℝ)
  baseBFire := (38286613973 / 20000000000000 : ℝ)
  epsilon := (76669785799 / 125000000000000 : ℝ)
  ell := (454390424847 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6098p2 : AsymmetricEntry 5 where
  cellId := 6098
  port := 2
  level0 := (122952284633 / 125000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (172469152669 / 50000000000000 : ℝ)
  baseBSilent := (279609003121 / 100000000000000 : ℝ)
  baseBFire := (133761584153 / 250000000000000 : ℝ)
  epsilon := (818149854787 / 1000000000000000 : ℝ)
  ell := (464155802783 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def t6099p1 : AsymmetricEntry 5 where
  cellId := 6099
  port := 1
  level0 := (25380841551 / 25000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (104834178719 / 12500000000000 : ℝ)
  baseBSilent := (407197444849 / 100000000000000 : ℝ)
  baseBFire := (1 / 10000000000 : ℝ)
  epsilon := (848569764253 / 1000000000000000 : ℝ)
  ell := (199196836001 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  doseNonnegative := by norm_num
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  silenceRoom := by norm_num
  fireRoom := by norm_num

noncomputable def entries : List (Sigma AsymmetricEntry) :=
  [⟨2, t6002p1⟩, ⟨5, t6003p1⟩, ⟨6, t6004p1⟩, ⟨4, t6004p2⟩, ⟨2, t6005p1⟩, ⟨3, t6008p1⟩, ⟨3, t6009p2⟩, ⟨4, t6010p1⟩, ⟨5, t6011p2⟩, ⟨4, t6012p1⟩, ⟨3, t6013p2⟩, ⟨4, t6015p1⟩, ⟨4, t6016p1⟩, ⟨3, t6018p2⟩, ⟨4, t6019p2⟩, ⟨4, t6025p1⟩, ⟨3, t6027p2⟩, ⟨4, t6028p2⟩, ⟨3, t6030p1⟩, ⟨4, t6031p1⟩, ⟨3, t6032p1⟩, ⟨4, t6032p2⟩, ⟨4, t6037p1⟩, ⟨4, t6037p2⟩, ⟨5, t6040p2⟩, ⟨5, t6042p2⟩, ⟨5, t6043p2⟩, ⟨4, t6045p2⟩, ⟨4, t6050p2⟩, ⟨3, t6051p2⟩, ⟨4, t6052p1⟩, ⟨6, t6055p1⟩, ⟨5, t6056p1⟩, ⟨4, t6058p2⟩, ⟨3, t6061p2⟩, ⟨2, t6063p1⟩, ⟨4, t6065p1⟩, ⟨3, t6067p2⟩, ⟨2, t6068p2⟩, ⟨3, t6074p1⟩, ⟨3, t6075p1⟩, ⟨4, t6075p2⟩, ⟨4, t6076p1⟩, ⟨5, t6077p1⟩, ⟨5, t6077p2⟩, ⟨4, t6079p1⟩, ⟨3, t6080p2⟩, ⟨4, t6081p1⟩, ⟨4, t6082p2⟩, ⟨3, t6085p2⟩, ⟨4, t6088p2⟩, ⟨4, t6090p1⟩, ⟨4, t6093p2⟩, ⟨3, t6095p2⟩, ⟨3, t6096p1⟩, ⟨5, t6098p2⟩, ⟨5, t6099p1⟩]
theorem entry_count : entries.length = 57 := by rfl

end ReusableController.PhysicalEvaluator.AsymmetricData
