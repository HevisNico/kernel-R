import PhysicalEvaluator.CampaignBridge

namespace ReusableController.PhysicalEvaluator.CampaignData

noncomputable def t6002p1 : CampaignEntry 2 where
  cellId := 6002
  port := 1
  level0 := (491306860829 / 500000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (593707149697 / 1000000000000000 : ℝ)
  baseB := (588765043351 / 100000000000000 : ℝ)
  epsilon := (520780950947 / 1000000000000000 : ℝ)
  ell := (38002653271 / 10000000000000 : ℝ)
  observed := fun k => [false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6003p1 : CampaignEntry 5 where
  cellId := 6003
  port := 1
  level0 := (104295908429 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (592994208913 / 100000000000000 : ℝ)
  baseB := (347082150901 / 50000000000000 : ℝ)
  epsilon := (964576675959 / 1000000000000000 : ℝ)
  ell := (20070774429 / 5000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6004p2 : CampaignEntry 4 where
  cellId := 6004
  port := 2
  level0 := (101649007307 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (350328876061 / 100000000000000 : ℝ)
  baseB := (352677304057 / 50000000000000 : ℝ)
  epsilon := (378192763311 / 500000000000000 : ℝ)
  ell := (27326263123 / 5000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6005p1 : CampaignEntry 2 where
  cellId := 6005
  port := 1
  level0 := (997052042403 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (713714991111 / 100000000000000 : ℝ)
  baseB := (405157027 / 97656250000 : ℝ)
  epsilon := (511020932617 / 1000000000000000 : ℝ)
  ell := (468199710539 / 100000000000000 : ℝ)
  observed := fun k => [false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6008p1 : CampaignEntry 3 where
  cellId := 6008
  port := 1
  level0 := (496592287167 / 500000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (33293448539 / 6250000000000 : ℝ)
  baseB := (54059573491 / 20000000000000 : ℝ)
  epsilon := (608386021137 / 1000000000000000 : ℝ)
  ell := (64456004691 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6009p2 : CampaignEntry 3 where
  cellId := 6009
  port := 2
  level0 := (199039313773 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (256113724237 / 50000000000000 : ℝ)
  baseB := (102028947379 / 25000000000000 : ℝ)
  epsilon := (316195576873 / 500000000000000 : ℝ)
  ell := (10600631737 / 2000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6010p1 : CampaignEntry 4 where
  cellId := 6010
  port := 1
  level0 := (101038209147 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (370699294979 / 50000000000000 : ℝ)
  baseB := (108140998863 / 25000000000000 : ℝ)
  epsilon := (160753007461 / 200000000000000 : ℝ)
  ell := (101882349009 / 20000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6011p2 : CampaignEntry 5 where
  cellId := 6011
  port := 2
  level0 := (100036553783 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (19140513101 / 6250000000000 : ℝ)
  baseB := (213141724259 / 25000000000000 : ℝ)
  epsilon := (874112621161 / 1000000000000000 : ℝ)
  ell := (21558118663 / 5000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6012p1 : CampaignEntry 4 where
  cellId := 6012
  port := 1
  level0 := (61366029683 / 62500000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (221675833127 / 100000000000000 : ℝ)
  baseB := (64456965329 / 12500000000000 : ℝ)
  epsilon := (727869338271 / 1000000000000000 : ℝ)
  ell := (93547558419 / 20000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6013p2 : CampaignEntry 3 where
  cellId := 6013
  port := 2
  level0 := (997781596883 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (520037102427 / 100000000000000 : ℝ)
  baseB := (133042838387 / 25000000000000 : ℝ)
  epsilon := (131161982899 / 200000000000000 : ℝ)
  ell := (205794860991 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6015p1 : CampaignEntry 4 where
  cellId := 6015
  port := 1
  level0 := (2559470749 / 2500000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (230630426409 / 50000000000000 : ℝ)
  baseB := (169020878923 / 25000000000000 : ℝ)
  epsilon := (827315393429 / 1000000000000000 : ℝ)
  ell := (444956840723 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6018p2 : CampaignEntry 3 where
  cellId := 6018
  port := 2
  level0 := (100496638391 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (91127336943 / 25000000000000 : ℝ)
  baseB := (650068906209 / 100000000000000 : ℝ)
  epsilon := (42352907969 / 62500000000000 : ℝ)
  ell := (499062359671 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6028p2 : CampaignEntry 4 where
  cellId := 6028
  port := 2
  level0 := (989852634407 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (511829546591 / 100000000000000 : ℝ)
  baseB := (6448805597 / 1250000000000 : ℝ)
  epsilon := (362753861977 / 500000000000000 : ℝ)
  ell := (452383007527 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6030p1 : CampaignEntry 3 where
  cellId := 6030
  port := 1
  level0 := (10016016093 / 10000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (68975830857 / 12500000000000 : ℝ)
  baseB := (698464527621 / 100000000000000 : ℝ)
  epsilon := (316045035737 / 500000000000000 : ℝ)
  ell := (66121713523 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6031p1 : CampaignEntry 4 where
  cellId := 6031
  port := 1
  level0 := (970223031509 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (365829457391 / 50000000000000 : ℝ)
  baseB := (305629394371 / 50000000000000 : ℝ)
  epsilon := (701616561889 / 1000000000000000 : ℝ)
  ell := (213690221131 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6032p1 : CampaignEntry 3 where
  cellId := 6032
  port := 1
  level0 := (97395029201 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (51782725773 / 25000000000000 : ℝ)
  baseB := (105516523463 / 12500000000000 : ℝ)
  epsilon := (148440171207 / 250000000000000 : ℝ)
  ell := (458673112593 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6032p2 : CampaignEntry 4 where
  cellId := 6032
  port := 2
  level0 := (97395029201 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (471751922731 / 100000000000000 : ℝ)
  baseB := (246599056263 / 50000000000000 : ℝ)
  epsilon := (139070231611 / 200000000000000 : ℝ)
  ell := (107073962397 / 20000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6043p2 : CampaignEntry 5 where
  cellId := 6043
  port := 2
  level0 := (10138161991 / 10000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (41802049321 / 25000000000000 : ℝ)
  baseB := (799503540147 / 100000000000000 : ℝ)
  epsilon := (213980659741 / 250000000000000 : ℝ)
  ell := (514931251919 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6050p2 : CampaignEntry 4 where
  cellId := 6050
  port := 2
  level0 := (19535389203 / 20000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (24014890379 / 5000000000000 : ℝ)
  baseB := (761338127577 / 100000000000000 : ℝ)
  epsilon := (683602683271 / 1000000000000000 : ℝ)
  ell := (46509573637 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6051p2 : CampaignEntry 3 where
  cellId := 6051
  port := 2
  level0 := (20035775199 / 20000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (65221711417 / 50000000000000 : ℝ)
  baseB := (611761636791 / 100000000000000 : ℝ)
  epsilon := (313009297509 / 500000000000000 : ℝ)
  ell := (443974143399 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6058p2 : CampaignEntry 4 where
  cellId := 6058
  port := 2
  level0 := (984513506533 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (75631509071 / 20000000000000 : ℝ)
  baseB := (881142812607 / 100000000000000 : ℝ)
  epsilon := (695940240701 / 1000000000000000 : ℝ)
  ell := (364803571369 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6061p2 : CampaignEntry 3 where
  cellId := 6061
  port := 2
  level0 := (198124301459 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (183073322163 / 25000000000000 : ℝ)
  baseB := (69375306869 / 12500000000000 : ℝ)
  epsilon := (31701948923 / 50000000000000 : ℝ)
  ell := (367928920077 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6063p1 : CampaignEntry 2 where
  cellId := 6063
  port := 1
  level0 := (983161897939 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (471501928873 / 100000000000000 : ℝ)
  baseB := (27495680203 / 6250000000000 : ℝ)
  epsilon := (515253427591 / 1000000000000000 : ℝ)
  ell := (190721049139 / 50000000000000 : ℝ)
  observed := fun k => [false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6065p1 : CampaignEntry 4 where
  cellId := 6065
  port := 1
  level0 := (248769350279 / 250000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (225569272467 / 500000000000000 : ℝ)
  baseB := (333326510757 / 100000000000000 : ℝ)
  epsilon := (744041707491 / 1000000000000000 : ℝ)
  ell := (96842002221 / 20000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6067p2 : CampaignEntry 3 where
  cellId := 6067
  port := 2
  level0 := (987918432557 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (216661279479 / 50000000000000 : ℝ)
  baseB := (676886573643 / 100000000000000 : ℝ)
  epsilon := (77455842597 / 125000000000000 : ℝ)
  ell := (255537132991 / 50000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6068p2 : CampaignEntry 2 where
  cellId := 6068
  port := 2
  level0 := (992652268279 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (390055555947 / 50000000000000 : ℝ)
  baseB := (198725065299 / 50000000000000 : ℝ)
  epsilon := (512342049297 / 1000000000000000 : ℝ)
  ell := (3160445227 / 781250000000 : ℝ)
  observed := fun k => [false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6074p1 : CampaignEntry 3 where
  cellId := 6074
  port := 1
  level0 := (1992418577 / 2000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (133533356797 / 50000000000000 : ℝ)
  baseB := (466611142997 / 100000000000000 : ℝ)
  epsilon := (20528528577 / 31250000000000 : ℝ)
  ell := (368999428613 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6075p2 : CampaignEntry 4 where
  cellId := 6075
  port := 2
  level0 := (199426086749 / 200000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (6520344039 / 2500000000000 : ℝ)
  baseB := (266252676279 / 50000000000000 : ℝ)
  epsilon := (368269360609 / 500000000000000 : ℝ)
  ell := (30962565141 / 6250000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6077p1 : CampaignEntry 5 where
  cellId := 6077
  port := 1
  level0 := (100406760237 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (571170729331 / 100000000000000 : ℝ)
  baseB := (611952004557 / 100000000000000 : ℝ)
  epsilon := (209395235343 / 250000000000000 : ℝ)
  ell := (1544505539 / 400000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6077p2 : CampaignEntry 5 where
  cellId := 6077
  port := 2
  level0 := (100406760237 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (312996555443 / 100000000000000 : ℝ)
  baseB := (90342279119 / 12500000000000 : ℝ)
  epsilon := (6895245697 / 7812500000000 : ℝ)
  ell := (46491641389 / 12500000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6079p1 : CampaignEntry 4 where
  cellId := 6079
  port := 1
  level0 := (100385428541 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (156876787 / 32000000000 : ℝ)
  baseB := (436178659273 / 100000000000000 : ℝ)
  epsilon := (762030599603 / 1000000000000000 : ℝ)
  ell := (110958423391 / 25000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6082p2 : CampaignEntry 4 where
  cellId := 6082
  port := 2
  level0 := (50280500643 / 50000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (807206974821 / 100000000000000 : ℝ)
  baseB := (291256636521 / 50000000000000 : ℝ)
  epsilon := (776835340601 / 1000000000000000 : ℝ)
  ell := (89303010611 / 25000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6085p2 : CampaignEntry 3 where
  cellId := 6085
  port := 2
  level0 := (24928022531 / 25000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (358218330029 / 50000000000000 : ℝ)
  baseB := (135554762599 / 20000000000000 : ℝ)
  epsilon := (32715577193 / 50000000000000 : ℝ)
  ell := (336595171431 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6088p2 : CampaignEntry 4 where
  cellId := 6088
  port := 2
  level0 := (101366041713 / 100000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (350946689403 / 100000000000000 : ℝ)
  baseB := (738685158507 / 100000000000000 : ℝ)
  epsilon := (32386010889 / 40000000000000 : ℝ)
  ell := (123010515459 / 25000000000000 : ℝ)
  observed := fun k => [false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6095p2 : CampaignEntry 3 where
  cellId := 6095
  port := 2
  level0 := (995887535393 / 1000000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (108856009913 / 12500000000000 : ℝ)
  baseB := (475510412913 / 100000000000000 : ℝ)
  epsilon := (16291915063 / 25000000000000 : ℝ)
  ell := (3214860941 / 781250000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6096p1 : CampaignEntry 3 where
  cellId := 6096
  port := 1
  level0 := (25138115681 / 25000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (177816937331 / 50000000000000 : ℝ)
  baseB := (69921672933 / 12500000000000 : ℝ)
  epsilon := (76669785799 / 125000000000000 : ℝ)
  ell := (454390424847 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def t6098p2 : CampaignEntry 5 where
  cellId := 6098
  port := 2
  level0 := (122952284633 / 125000000000 : ℝ)
  dose0 := (4209334265125419 / 100000000000000000 : ℝ)
  baseA := (172469152669 / 50000000000000 : ℝ)
  baseB := (517899041797 / 100000000000000 : ℝ)
  epsilon := (818149854787 / 1000000000000000 : ℝ)
  ell := (464155802783 / 100000000000000 : ℝ)
  observed := fun k => [false, false, false, false, false, true][k.val]!
  ellNonnegative := by norm_num
  levelFloor := by norm_num
  room := by norm_num

noncomputable def entries : List (Sigma CampaignEntry) :=
  [⟨2, t6002p1⟩, ⟨5, t6003p1⟩, ⟨4, t6004p2⟩, ⟨2, t6005p1⟩, ⟨3, t6008p1⟩, ⟨3, t6009p2⟩, ⟨4, t6010p1⟩, ⟨5, t6011p2⟩, ⟨4, t6012p1⟩, ⟨3, t6013p2⟩, ⟨4, t6015p1⟩, ⟨3, t6018p2⟩, ⟨4, t6028p2⟩, ⟨3, t6030p1⟩, ⟨4, t6031p1⟩, ⟨3, t6032p1⟩, ⟨4, t6032p2⟩, ⟨5, t6043p2⟩, ⟨4, t6050p2⟩, ⟨3, t6051p2⟩, ⟨4, t6058p2⟩, ⟨3, t6061p2⟩, ⟨2, t6063p1⟩, ⟨4, t6065p1⟩, ⟨3, t6067p2⟩, ⟨2, t6068p2⟩, ⟨3, t6074p1⟩, ⟨4, t6075p2⟩, ⟨5, t6077p1⟩, ⟨5, t6077p2⟩, ⟨4, t6079p1⟩, ⟨4, t6082p2⟩, ⟨3, t6085p2⟩, ⟨4, t6088p2⟩, ⟨3, t6095p2⟩, ⟨3, t6096p1⟩, ⟨5, t6098p2⟩]
theorem entry_count : entries.length = 37 := by rfl

theorem t6004_preparation_budget_rejected :
    ¬ ((281419367837 / 50000000000000 : ℝ) + (469671200673 / 500000000000000 : ℝ)) + ((178449720491 / 25000000000000 : ℝ) + 2*(469671200673 / 500000000000000 : ℝ)) +
      20/17*(263145366997 / 50000000000000 : ℝ) + 1/8000 < (4209334265125419 / 100000000000000000 : ℝ)/2 := by norm_num

end ReusableController.PhysicalEvaluator.CampaignData
