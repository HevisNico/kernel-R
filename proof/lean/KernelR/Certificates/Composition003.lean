import KernelR.Intervals

/-! Generated exact endpoint checks. Analytic enclosure soundness is NOT asserted. -/
namespace KernelR.Certificates.Composition003
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def aux_birth_below_threshold_left : RationalBox := ⟨(2499 / 100000 : ℚ), (2501 / 100000 : ℚ)⟩
theorem aux_birth_below_threshold_left_valid : aux_birth_below_threshold_left.Valid := by norm_num [RationalBox.Valid, aux_birth_below_threshold_left]

def aux_birth_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_birth_below_threshold_right_valid : aux_birth_below_threshold_right.Valid := by norm_num [RationalBox.Valid, aux_birth_below_threshold_right]

def aux_root_lower_left : RationalBox := ⟨(7574882850978467925186299383452110043197 / 10000000000000000000000000000000000000000 : ℚ), (7619163495629254921412199185543111152121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_lower_left_valid : aux_root_lower_left.Valid := by norm_num [RationalBox.Valid, aux_root_lower_left]

def aux_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_root_lower_right_valid : aux_root_lower_right.Valid := by norm_num [RationalBox.Valid, aux_root_lower_right]

def aux_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_root_upper_left_valid : aux_root_upper_left.Valid := by norm_num [RationalBox.Valid, aux_root_upper_left]

def aux_root_upper_right : RationalBox := ⟨(14694387879766713610083071880494126587067 / 10000000000000000000000000000000000000000 : ℚ), (369537815090118715231835911579788708021 / 250000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_upper_right_valid : aux_root_upper_right.Valid := by norm_num [RationalBox.Valid, aux_root_upper_right]

def aux_root_strict_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem aux_root_strict_left_valid : aux_root_strict_left.Valid := by norm_num [RationalBox.Valid, aux_root_strict_left]

def aux_root_strict_right : RationalBox := ⟨(463727986045511090000642156089472106413213 / 10000000000000000000000000000000000000000 : ℚ), (502451804730260617612837996162287249719871 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_strict_right_valid : aux_root_strict_right.Valid := by norm_num [RationalBox.Valid, aux_root_strict_right]

def aux_finish_after_raw_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_finish_after_raw_left_valid : aux_finish_after_raw_left.Valid := by norm_num [RationalBox.Valid, aux_finish_after_raw_left]

def aux_finish_after_raw_right : RationalBox := ⟨(12413210368893320039880358923230309072781 / 10000000000000000000000000000000000000000 : ℚ), (6206605184446660019940179461615154536391 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_after_raw_right_valid : aux_finish_after_raw_right.Valid := by norm_num [RationalBox.Valid, aux_finish_after_raw_right]

def aux_finish_before_fastest_next_input_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_before_fastest_next_input_left_valid : aux_finish_before_fastest_next_input_left.Valid := by norm_num [RationalBox.Valid, aux_finish_before_fastest_next_input_left]

def aux_finish_before_fastest_next_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem aux_finish_before_fastest_next_input_right_valid : aux_finish_before_fastest_next_input_right.Valid := by norm_num [RationalBox.Valid, aux_finish_before_fastest_next_input_right]

def energy_reserve_invariant_left : RationalBox := ⟨(2412569423394848013788616984038787968476533 / 10000000000000000000000000000000000000000 : ℚ), (1206284711697424006894308492019393984238267 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem energy_reserve_invariant_left_valid : energy_reserve_invariant_left.Valid := by norm_num [RationalBox.Valid, energy_reserve_invariant_left]

def energy_reserve_invariant_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem energy_reserve_invariant_right_valid : energy_reserve_invariant_right.Valid := by norm_num [RationalBox.Valid, energy_reserve_invariant_right]

def caps_final_gain_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem caps_final_gain_left_valid : caps_final_gain_left.Valid := by norm_num [RationalBox.Valid, caps_final_gain_left]

def caps_final_gain_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem caps_final_gain_right_valid : caps_final_gain_right.Valid := by norm_num [RationalBox.Valid, caps_final_gain_right]

def caps_final_recovery_left : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem caps_final_recovery_left_valid : caps_final_recovery_left.Valid := by norm_num [RationalBox.Valid, caps_final_recovery_left]

def caps_final_recovery_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem caps_final_recovery_right_valid : caps_final_recovery_right.Valid := by norm_num [RationalBox.Valid, caps_final_recovery_right]

def jitter_budget : RationalBox := ⟨(3 / 20 : ℚ), (3 / 20 : ℚ)⟩
theorem jitter_budget_valid : jitter_budget.Valid := by norm_num [RationalBox.Valid, jitter_budget]

def prepared_recovery : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem prepared_recovery_valid : prepared_recovery.Valid := by norm_num [RationalBox.Valid, prepared_recovery]

def final_recovery : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem final_recovery_valid : final_recovery.Valid := by norm_num [RationalBox.Valid, final_recovery]

def prepared_gain : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem prepared_gain_valid : prepared_gain.Valid := by norm_num [RationalBox.Valid, prepared_gain]

def final_gain : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem final_gain_valid : final_gain.Valid := by norm_num [RationalBox.Valid, final_gain]

def aux_mark_end : RationalBox := ⟨(349401794616151545363908275174476570289 / 10000000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem aux_mark_end_valid : aux_mark_end.Valid := by norm_num [RationalBox.Valid, aux_mark_end]

def aux_ERROR_start : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (111324974924774322968906720160481444333 / 100000000000000000000000000000000000000 : ℚ)⟩
theorem aux_ERROR_start_valid : aux_ERROR_start.Valid := by norm_num [RationalBox.Valid, aux_ERROR_start]

def aux_finish : RationalBox := ⟨(12413210368893320039880358923230309072781 / 10000000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_valid : aux_finish.Valid := by norm_num [RationalBox.Valid, aux_finish]

def MARK_integral_deficit : RationalBox := ⟨(153747522149121359283779567307875399 / 62500000000000000000000000000000000000 : ℚ), (4957171809740596256000619980136389673 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem MARK_integral_deficit_valid : MARK_integral_deficit.Valid := by norm_num [RationalBox.Valid, MARK_integral_deficit]

def relay_low_root_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_low_root_positive_coefficient_left_valid : relay_low_root_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_positive_coefficient_left]

def relay_low_root_positive_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_positive_coefficient_right_valid : relay_low_root_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_positive_coefficient_right]

def relay_low_root_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_low_root_increasing_left_valid : relay_low_root_increasing_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_increasing_left]

def relay_low_root_increasing_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_increasing_right_valid : relay_low_root_increasing_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_increasing_right]

def relay_low_root_lower_sign_left : RationalBox := ⟨(998178201240310947902485726302510005149 / 1000000000000000000000000000000000000000 : ℚ), (9981961649839725919464288313052310149421 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_lower_sign_left_valid : relay_low_root_lower_sign_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_lower_sign_left]

def relay_low_root_lower_sign_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_low_root_lower_sign_right_valid : relay_low_root_lower_sign_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_lower_sign_right]

def relay_low_root_upper_sign_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_low_root_upper_sign_left_valid : relay_low_root_upper_sign_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_upper_sign_left]

def relay_low_root_upper_sign_right : RationalBox := ⟨(1003820576896766608189493188295273519847 / 1000000000000000000000000000000000000000 : ℚ), (5019193267445349320005691617168449083861 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_upper_sign_right_valid : relay_low_root_upper_sign_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_upper_sign_right]

def relay_low_root_MARK_precedes_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_MARK_precedes_fire_left_valid : relay_low_root_MARK_precedes_fire_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_MARK_precedes_fire_left]

def relay_low_root_MARK_precedes_fire_right : RationalBox := ⟨(13 / 20 : ℚ), (13 / 20 : ℚ)⟩
theorem relay_low_root_MARK_precedes_fire_right_valid : relay_low_root_MARK_precedes_fire_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_MARK_precedes_fire_right]

def relay_low_root_fire_precedes_ERROR_left : RationalBox := ⟨(33 / 50 : ℚ), (33 / 50 : ℚ)⟩
theorem relay_low_root_fire_precedes_ERROR_left_valid : relay_low_root_fire_precedes_ERROR_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_fire_precedes_ERROR_left]

def relay_low_root_fire_precedes_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_fire_precedes_ERROR_right_valid : relay_low_root_fire_precedes_ERROR_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_fire_precedes_ERROR_right]

def relay_low_root_ERROR_entirely_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_ERROR_entirely_protected_left_valid : relay_low_root_ERROR_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_ERROR_entirely_protected_left]

def relay_low_root_ERROR_entirely_protected_right : RationalBox := ⟨(8425276594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67407868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_ERROR_entirely_protected_right_valid : relay_low_root_ERROR_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_ERROR_entirely_protected_right]

def relay_low_root_at_b2_ERROR_entirely_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_at_b2_ERROR_entirely_protected_left_valid : relay_low_root_at_b2_ERROR_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_at_b2_ERROR_entirely_protected_left]

def relay_low_root_at_b2_ERROR_entirely_protected_right : RationalBox := ⟨(24611750149533142837461648008428468116319 / 5000000000000000000000000000000000000000 : ℚ), (49225837775426088974017901059609667182761 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_at_b2_ERROR_entirely_protected_right_valid : relay_low_root_at_b2_ERROR_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_at_b2_ERROR_entirely_protected_right]

def relay_high_rest_root_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_high_rest_root_positive_coefficient_left_valid : relay_high_rest_root_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_positive_coefficient_left]

def relay_high_rest_root_positive_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_positive_coefficient_right_valid : relay_high_rest_root_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_positive_coefficient_right]

def relay_high_rest_root_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_high_rest_root_increasing_left_valid : relay_high_rest_root_increasing_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_increasing_left]

def relay_high_rest_root_increasing_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_increasing_right_valid : relay_high_rest_root_increasing_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_increasing_right]

def relay_high_rest_root_lower_sign_left : RationalBox := ⟨(9790304931478480597693570265572100652703 / 10000000000000000000000000000000000000000 : ℚ), (489524036966759143703319891422117957267 / 500000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_lower_sign_left_valid : relay_high_rest_root_lower_sign_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_lower_sign_left]

def relay_high_rest_root_lower_sign_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_high_rest_root_lower_sign_right_valid : relay_high_rest_root_lower_sign_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_lower_sign_right]

def relay_high_rest_root_upper_sign_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_high_rest_root_upper_sign_left_valid : relay_high_rest_root_upper_sign_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_upper_sign_left]

def relay_high_rest_root_upper_sign_right : RationalBox := ⟨(2014413477662782087737588494001580679009 / 2000000000000000000000000000000000000000 : ℚ), (2014449766295220458141966018597367959459 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_upper_sign_right_valid : relay_high_rest_root_upper_sign_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_upper_sign_right]

def relay_high_rest_root_MARK_precedes_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_MARK_precedes_fire_left_valid : relay_high_rest_root_MARK_precedes_fire_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_MARK_precedes_fire_left]

def relay_high_rest_root_MARK_precedes_fire_right : RationalBox := ⟨(6 / 25 : ℚ), (6 / 25 : ℚ)⟩
theorem relay_high_rest_root_MARK_precedes_fire_right_valid : relay_high_rest_root_MARK_precedes_fire_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_MARK_precedes_fire_right]

def relay_high_rest_root_fire_precedes_ERROR_left : RationalBox := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem relay_high_rest_root_fire_precedes_ERROR_left_valid : relay_high_rest_root_fire_precedes_ERROR_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_fire_precedes_ERROR_left]

def relay_high_rest_root_fire_precedes_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_fire_precedes_ERROR_right_valid : relay_high_rest_root_fire_precedes_ERROR_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_fire_precedes_ERROR_right]

def relay_high_rest_root_ERROR_entirely_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_ERROR_entirely_protected_left_valid : relay_high_rest_root_ERROR_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_ERROR_entirely_protected_left]

def relay_high_rest_root_ERROR_entirely_protected_right : RationalBox := ⟨(18256139731509105881207431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36513548563755758445841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_ERROR_entirely_protected_right_valid : relay_high_rest_root_ERROR_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_ERROR_entirely_protected_right]

def slow_prefix_ready_before_every_input_left : RationalBox := ⟨(8437776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67507868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem slow_prefix_ready_before_every_input_left_valid : slow_prefix_ready_before_every_input_left.Valid := by norm_num [RationalBox.Valid, slow_prefix_ready_before_every_input_left]

def slow_prefix_ready_before_every_input_right : RationalBox := ⟨(71 / 10 : ℚ), (71 / 10 : ℚ)⟩
theorem slow_prefix_ready_before_every_input_right_valid : slow_prefix_ready_before_every_input_right.Valid := by norm_num [RationalBox.Valid, slow_prefix_ready_before_every_input_right]

def steady_tail_ready_before_every_input_left : RationalBox := ⟨(18306139731509105881207431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36613548563755758445841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem steady_tail_ready_before_every_input_left_valid : steady_tail_ready_before_every_input_left.Valid := by norm_num [RationalBox.Valid, steady_tail_ready_before_every_input_left]

def steady_tail_ready_before_every_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem steady_tail_ready_before_every_input_right_valid : steady_tail_ready_before_every_input_right.Valid := by norm_num [RationalBox.Valid, steady_tail_ready_before_every_input_right]

def h_increasing_through_raw_end_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem h_increasing_through_raw_end_left_valid : h_increasing_through_raw_end_left.Valid := by norm_num [RationalBox.Valid, h_increasing_through_raw_end_left]

def h_increasing_through_raw_end_right : RationalBox := ⟨(433082604236559429067162932334980573167 / 10000000000000000000000000000000000000000 : ℚ), (27067662764784964316697683270936285823 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem h_increasing_through_raw_end_right_valid : h_increasing_through_raw_end_right.Valid := by norm_num [RationalBox.Valid, h_increasing_through_raw_end_right]

def relay_first_miss_past_FAST_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_first_miss_past_FAST_left_valid : relay_first_miss_past_FAST_left.Valid := by norm_num [RationalBox.Valid, relay_first_miss_past_FAST_left]

def relay_first_miss_past_FAST_right : RationalBox := ⟨(51 / 25 : ℚ), (11 / 4 : ℚ)⟩
theorem relay_first_miss_past_FAST_right_valid : relay_first_miss_past_FAST_right.Valid := by norm_num [RationalBox.Valid, relay_first_miss_past_FAST_right]

def relay_first_miss_still_in_SLOW_left : RationalBox := ⟨(917949 / 2500000 : ℚ), (198011 / 400000 : ℚ)⟩
theorem relay_first_miss_still_in_SLOW_left_valid : relay_first_miss_still_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, relay_first_miss_still_in_SLOW_left]

def relay_first_miss_still_in_SLOW_right : RationalBox := ⟨(9162907318741550651835272117680110714501 / 10000000000000000000000000000000000000000 : ℚ), (4581453659370775325917636058840055357251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_still_in_SLOW_right_valid : relay_first_miss_still_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, relay_first_miss_still_in_SLOW_right]

def relay_first_miss_return : RationalBox := ⟨(3783107676766374477090708232250072120943 / 2500000000000000000000000000000000000000 : ℚ), (4938362703328221920321508873103683910037 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_return_valid : relay_first_miss_return.Valid := by norm_num [RationalBox.Valid, relay_first_miss_return]

def relay_first_miss_entire_MARK_protected_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_entire_MARK_protected_left_valid : relay_first_miss_entire_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, relay_first_miss_entire_MARK_protected_left]

def relay_first_miss_entire_MARK_protected_right : RationalBox := ⟨(3783107676766374477090708232250072120943 / 2500000000000000000000000000000000000000 : ℚ), (15132430707065497908362832929000288483773 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_entire_MARK_protected_right_valid : relay_first_miss_entire_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, relay_first_miss_entire_MARK_protected_right]

def relay_first_miss_ready_before_following_input_left : RationalBox := ⟨(19753450813312887681286035492414735640147 / 10000000000000000000000000000000000000000 : ℚ), (4938362703328221920321508873103683910037 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_ready_before_following_input_left_valid : relay_first_miss_ready_before_following_input_left.Valid := by norm_num [RationalBox.Valid, relay_first_miss_ready_before_following_input_left]

def relay_first_miss_ready_before_following_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem relay_first_miss_ready_before_following_input_right_valid : relay_first_miss_ready_before_following_input_right.Valid := by norm_num [RationalBox.Valid, relay_first_miss_ready_before_following_input_right]

def relay_first_miss_entire_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_entire_ERROR_protected_left_valid : relay_first_miss_entire_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, relay_first_miss_entire_ERROR_protected_left]

def relay_first_miss_entire_ERROR_protected_right : RationalBox := ⟨(3783107676766374477090708232250072120943 / 2500000000000000000000000000000000000000 : ℚ), (15132430707065497908362832929000288483773 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_entire_ERROR_protected_right_valid : relay_first_miss_entire_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, relay_first_miss_entire_ERROR_protected_right]

def relay_second_miss_past_FAST_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_second_miss_past_FAST_left_valid : relay_second_miss_past_FAST_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_past_FAST_left]

def relay_second_miss_past_FAST_right : RationalBox := ⟨(51 / 25 : ℚ), (53 / 20 : ℚ)⟩
theorem relay_second_miss_past_FAST_right_valid : relay_second_miss_past_FAST_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_past_FAST_right]

def relay_second_miss_still_in_SLOW_left : RationalBox := ⟨(1427949 / 2500000 : ℚ), (1484053 / 2000000 : ℚ)⟩
theorem relay_second_miss_still_in_SLOW_left_valid : relay_second_miss_still_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_still_in_SLOW_left]

def relay_second_miss_still_in_SLOW_right : RationalBox := ⟨(9162907318741550651835272117680110714501 / 10000000000000000000000000000000000000000 : ℚ), (4581453659370775325917636058840055357251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_still_in_SLOW_right_valid : relay_second_miss_still_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_still_in_SLOW_right]

def relay_second_miss_return : RationalBox := ⟨(4650514255639088627458953312937477377809 / 10000000000000000000000000000000000000000 : ℚ), (1837295030511053144495000961878576716169 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_return_valid : relay_second_miss_return.Valid := by norm_num [RationalBox.Valid, relay_second_miss_return]

def relay_second_miss_entire_MARK_protected_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_entire_MARK_protected_left_valid : relay_second_miss_entire_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_entire_MARK_protected_left]

def relay_second_miss_entire_MARK_protected_right : RationalBox := ⟨(4650514255639088627458953312937477377809 / 10000000000000000000000000000000000000000 : ℚ), (465051425563908862745895331293747737781 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_entire_MARK_protected_right_valid : relay_second_miss_entire_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_entire_MARK_protected_right]

def relay_second_miss_ready_before_following_input_left : RationalBox := ⟨(2296618788138816430618751202348220895211 / 2500000000000000000000000000000000000000 : ℚ), (1837295030511053144495000961878576716169 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_ready_before_following_input_left_valid : relay_second_miss_ready_before_following_input_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_ready_before_following_input_left]

def relay_second_miss_ready_before_following_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem relay_second_miss_ready_before_following_input_right_valid : relay_second_miss_ready_before_following_input_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_ready_before_following_input_right]

def relay_second_miss_ready_before_ERROR_left : RationalBox := ⟨(2296618788138816430618751202348220895211 / 2500000000000000000000000000000000000000 : ℚ), (1837295030511053144495000961878576716169 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_ready_before_ERROR_left_valid : relay_second_miss_ready_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_ready_before_ERROR_left]

def relay_second_miss_ready_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_ready_before_ERROR_right_valid : relay_second_miss_ready_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_ready_before_ERROR_right]

def relay_second_miss_before_raw_end_left : RationalBox := ⟨(2296618788138816430618751202348220895211 / 2500000000000000000000000000000000000000 : ℚ), (1837295030511053144495000961878576716169 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_before_raw_end_left_valid : relay_second_miss_before_raw_end_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_before_raw_end_left]

def relay_second_miss_before_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_second_miss_before_raw_end_right_valid : relay_second_miss_before_raw_end_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_before_raw_end_right]

def relay_second_miss_no_refire_from_tail_left : RationalBox := ⟨(2652521902943613861841550154206868811971 / 5000000000000000000000000000000000000000 : ℚ), (5305043805887227723683100308413737623943 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_no_refire_from_tail_left_valid : relay_second_miss_no_refire_from_tail_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_no_refire_from_tail_left]

def relay_second_miss_no_refire_from_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_second_miss_no_refire_from_tail_right_valid : relay_second_miss_no_refire_from_tail_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_no_refire_from_tail_right]

def relay_transient_charge_excess : RationalBox := ⟨(0 / 1 : ℚ), (558020339165092839856833001214295689791 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_transient_charge_excess_valid : relay_transient_charge_excess.Valid := by norm_num [RationalBox.Valid, relay_transient_charge_excess]

def relay_high_transient_root_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_high_transient_root_positive_coefficient_left_valid : relay_high_transient_root_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_positive_coefficient_left]

def relay_high_transient_root_positive_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (26421075678771802141495330707572704201449 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_positive_coefficient_right_valid : relay_high_transient_root_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_positive_coefficient_right]

def relay_high_transient_root_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_high_transient_root_increasing_left_valid : relay_high_transient_root_increasing_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_increasing_left]

def relay_high_transient_root_increasing_right : RationalBox := ⟨(7605411572235699588882726720676407594767 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_increasing_right_valid : relay_high_transient_root_increasing_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_increasing_right]

def relay_high_transient_root_lower_sign_left : RationalBox := ⟨(4301253470772651664047614877313461764851 / 5000000000000000000000000000000000000000 : ℚ), (9612494359008031867516838954314778386853 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_lower_sign_left_valid : relay_high_transient_root_lower_sign_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_lower_sign_left]

def relay_high_transient_root_lower_sign_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_high_transient_root_lower_sign_right_valid : relay_high_transient_root_lower_sign_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_lower_sign_right]

def relay_high_transient_root_upper_sign_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_high_transient_root_upper_sign_left_valid : relay_high_transient_root_upper_sign_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_upper_sign_left]

def relay_high_transient_root_upper_sign_right : RationalBox := ⟨(2014413477662782087737588494001580679009 / 2000000000000000000000000000000000000000 : ℚ), (2764287818315225484025986746892861970181 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_upper_sign_right_valid : relay_high_transient_root_upper_sign_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_upper_sign_right]

def relay_high_transient_root_MARK_precedes_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_MARK_precedes_fire_left_valid : relay_high_transient_root_MARK_precedes_fire_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_MARK_precedes_fire_left]

def relay_high_transient_root_MARK_precedes_fire_right : RationalBox := ⟨(1 / 5 : ℚ), (1 / 5 : ℚ)⟩
theorem relay_high_transient_root_MARK_precedes_fire_right_valid : relay_high_transient_root_MARK_precedes_fire_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_MARK_precedes_fire_right]

def relay_high_transient_root_fire_precedes_ERROR_left : RationalBox := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem relay_high_transient_root_fire_precedes_ERROR_left_valid : relay_high_transient_root_fire_precedes_ERROR_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_fire_precedes_ERROR_left]

def relay_high_transient_root_fire_precedes_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_fire_precedes_ERROR_right_valid : relay_high_transient_root_fire_precedes_ERROR_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_fire_precedes_ERROR_right]

def relay_high_transient_root_ERROR_entirely_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_ERROR_entirely_protected_left_valid : relay_high_transient_root_ERROR_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_ERROR_entirely_protected_left]

def relay_high_transient_root_ERROR_entirely_protected_right : RationalBox := ⟨(18056139731509105881207431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36113548563755758445841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_ERROR_entirely_protected_right_valid : relay_high_transient_root_ERROR_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_ERROR_entirely_protected_right]

def relay_transient_return_before_next_input_left : RationalBox := ⟨(18306139731509105881207431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36613548563755758445841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_transient_return_before_next_input_left_valid : relay_transient_return_before_next_input_left.Valid := by norm_num [RationalBox.Valid, relay_transient_return_before_next_input_left]

def relay_transient_return_before_next_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem relay_transient_return_before_next_input_right_valid : relay_transient_return_before_next_input_right.Valid := by norm_num [RationalBox.Valid, relay_transient_return_before_next_input_right]

def output_first_new_slow_lower_left : RationalBox := ⟨(37 / 5 : ℚ), (37 / 5 : ℚ)⟩
theorem output_first_new_slow_lower_left_valid : output_first_new_slow_lower_left.Valid := by norm_num [RationalBox.Valid, output_first_new_slow_lower_left]

def output_first_new_slow_lower_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem output_first_new_slow_lower_right_valid : output_first_new_slow_lower_right.Valid := by norm_num [RationalBox.Valid, output_first_new_slow_lower_right]

def output_first_new_slow_upper_left : RationalBox := ⟨(81 / 10 : ℚ), (81 / 10 : ℚ)⟩
theorem output_first_new_slow_upper_left_valid : output_first_new_slow_upper_left.Valid := by norm_num [RationalBox.Valid, output_first_new_slow_upper_left]

def output_first_new_slow_upper_right : RationalBox := ⟨(83 / 10 : ℚ), (83 / 10 : ℚ)⟩
theorem output_first_new_slow_upper_right_valid : output_first_new_slow_upper_right.Valid := by norm_num [RationalBox.Valid, output_first_new_slow_upper_right]

def output_second_new_slow_lower_left : RationalBox := ⟨(37 / 5 : ℚ), (37 / 5 : ℚ)⟩
theorem output_second_new_slow_lower_left_valid : output_second_new_slow_lower_left.Valid := by norm_num [RationalBox.Valid, output_second_new_slow_lower_left]

def output_second_new_slow_lower_right : RationalBox := ⟨(377 / 50 : ℚ), (377 / 50 : ℚ)⟩
theorem output_second_new_slow_lower_right_valid : output_second_new_slow_lower_right.Valid := by norm_num [RationalBox.Valid, output_second_new_slow_lower_right]

def output_second_new_slow_upper_left : RationalBox := ⟨(38 / 5 : ℚ), (38 / 5 : ℚ)⟩
theorem output_second_new_slow_upper_left_valid : output_second_new_slow_upper_left.Valid := by norm_num [RationalBox.Valid, output_second_new_slow_upper_left]

def output_second_new_slow_upper_right : RationalBox := ⟨(83 / 10 : ℚ), (83 / 10 : ℚ)⟩
theorem output_second_new_slow_upper_right_valid : output_second_new_slow_upper_right.Valid := by norm_num [RationalBox.Valid, output_second_new_slow_upper_right]

def output_settling_upper_left : RationalBox := ⟨(81 / 20 : ℚ), (81 / 20 : ℚ)⟩
theorem output_settling_upper_left_valid : output_settling_upper_left.Valid := by norm_num [RationalBox.Valid, output_settling_upper_left]

def output_settling_upper_right : RationalBox := ⟨(41 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem output_settling_upper_right_valid : output_settling_upper_right.Valid := by norm_num [RationalBox.Valid, output_settling_upper_right]

def leaf_weak_0_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_weak_0_increasing_left_valid : leaf_weak_0_increasing_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_0_increasing_left]

def leaf_weak_0_increasing_right : RationalBox := ⟨(812763675428163105435705291892405716897 / 10000000000000000000000000000000000000000 : ℚ), (406503810918942910873231317319577075491 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_0_increasing_right_valid : leaf_weak_0_increasing_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_0_increasing_right]

def leaf_weak_0_no_fire_left : RationalBox := ⟨(668245496870030414562379084115601089407 / 2500000000000000000000000000000000000000 : ℚ), (2673015447454469888832508889797450392823 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_0_no_fire_left_valid : leaf_weak_0_no_fire_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_0_no_fire_left]

def leaf_weak_0_no_fire_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_weak_0_no_fire_right_valid : leaf_weak_0_no_fire_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_0_no_fire_right]

def leaf_weak_1_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_weak_1_increasing_left_valid : leaf_weak_1_increasing_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_1_increasing_left]

def leaf_weak_1_increasing_right : RationalBox := ⟨(128514491798898444042878025073666282201 / 1250000000000000000000000000000000000000 : ℚ), (370349118152897270256862943194939520681 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_1_increasing_right_valid : leaf_weak_1_increasing_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_1_increasing_right]

def leaf_weak_1_no_fire_left : RationalBox := ⟨(404837193210220878069943630299241842341 / 1000000000000000000000000000000000000000 : ℚ), (4274850919591008276434296393988955982977 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_1_no_fire_left_valid : leaf_weak_1_no_fire_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_1_no_fire_left]

def leaf_weak_1_no_fire_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_weak_1_no_fire_right_valid : leaf_weak_1_no_fire_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_1_no_fire_right]

def leaf_weak_2_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_weak_2_increasing_left_valid : leaf_weak_2_increasing_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_2_increasing_left]

def leaf_weak_2_increasing_right : RationalBox := ⟨(1812064679453537684486476566086021581849 / 10000000000000000000000000000000000000000 : ℚ), (674820090894440045079595129917914509719 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_2_increasing_right_valid : leaf_weak_2_increasing_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_2_increasing_right]

def leaf_weak_2_no_fire_left : RationalBox := ⟨(3277247904033087369540798740533573094581 / 5000000000000000000000000000000000000000 : ℚ), (6997809775853773271203600825208198725001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_2_no_fire_left_valid : leaf_weak_2_no_fire_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_2_no_fire_left]

def leaf_weak_2_no_fire_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_weak_2_no_fire_right_valid : leaf_weak_2_no_fire_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_2_no_fire_right]

def leaf_first_firing_excess : RationalBox := ⟨(0 / 1 : ℚ), (1338292255826070445611715695662391177491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_firing_excess_valid : leaf_first_firing_excess.Valid := by norm_num [RationalBox.Valid, leaf_first_firing_excess]

def leaf_first_root_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_first_root_positive_coefficient_left_valid : leaf_first_root_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_positive_coefficient_left]

def leaf_first_root_positive_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (1486309184323293978167013416858949662313 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_positive_coefficient_right_valid : leaf_first_root_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_positive_coefficient_right]

def leaf_first_root_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_first_root_increasing_left_valid : leaf_first_root_increasing_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_increasing_left]

def leaf_first_root_increasing_right : RationalBox := ⟨(1646751569295971922063103980599705619083 / 5000000000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_increasing_right_valid : leaf_first_root_increasing_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_increasing_right]

def leaf_first_root_lower_sign_left : RationalBox := ⟨(3968669443516656660866724072139110506223 / 5000000000000000000000000000000000000000 : ℚ), (1806635732329888165151520127597827788893 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_lower_sign_left_valid : leaf_first_root_lower_sign_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_lower_sign_left]

def leaf_first_root_lower_sign_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_first_root_lower_sign_right_valid : leaf_first_root_lower_sign_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_lower_sign_right]

def leaf_first_root_upper_sign_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_first_root_upper_sign_left_valid : leaf_first_root_upper_sign_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_upper_sign_left]

def leaf_first_root_upper_sign_right : RationalBox := ⟨(1003820576896766608189493188295273519847 / 1000000000000000000000000000000000000000 : ℚ), (220010331997444233025923322680313639341 / 200000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_upper_sign_right_valid : leaf_first_root_upper_sign_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_upper_sign_right]

def leaf_first_root_MARK_precedes_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_MARK_precedes_fire_left_valid : leaf_first_root_MARK_precedes_fire_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_MARK_precedes_fire_left]

def leaf_first_root_MARK_precedes_fire_right : RationalBox := ⟨(2 / 5 : ℚ), (2 / 5 : ℚ)⟩
theorem leaf_first_root_MARK_precedes_fire_right_valid : leaf_first_root_MARK_precedes_fire_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_MARK_precedes_fire_right]

def leaf_first_root_fire_precedes_ERROR_left : RationalBox := ⟨(33 / 50 : ℚ), (33 / 50 : ℚ)⟩
theorem leaf_first_root_fire_precedes_ERROR_left_valid : leaf_first_root_fire_precedes_ERROR_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_fire_precedes_ERROR_left]

def leaf_first_root_fire_precedes_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_fire_precedes_ERROR_right_valid : leaf_first_root_fire_precedes_ERROR_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_fire_precedes_ERROR_right]

def leaf_first_root_ERROR_entirely_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_ERROR_entirely_protected_left_valid : leaf_first_root_ERROR_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_ERROR_entirely_protected_left]

def leaf_first_root_ERROR_entirely_protected_right : RationalBox := ⟨(8112776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (64907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_ERROR_entirely_protected_right_valid : leaf_first_root_ERROR_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_ERROR_entirely_protected_right]

def leaf_first_miss_past_FAST_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_first_miss_past_FAST_left_valid : leaf_first_miss_past_FAST_left.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_past_FAST_left]

def leaf_first_miss_past_FAST_right : RationalBox := ⟨(117 / 50 : ℚ), (13 / 5 : ℚ)⟩
theorem leaf_first_miss_past_FAST_right_valid : leaf_first_miss_past_FAST_right.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_past_FAST_right]

def leaf_first_miss_still_in_SLOW_left : RationalBox := ⟨(2105883 / 5000000 : ℚ), (234013 / 500000 : ℚ)⟩
theorem leaf_first_miss_still_in_SLOW_left_valid : leaf_first_miss_still_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_still_in_SLOW_left]

def leaf_first_miss_still_in_SLOW_right : RationalBox := ⟨(9162907318741550651835272117680110714501 / 10000000000000000000000000000000000000000 : ℚ), (4581453659370775325917636058840055357251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_still_in_SLOW_right_valid : leaf_first_miss_still_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_still_in_SLOW_right]

def leaf_first_miss_return : RationalBox := ⟨(8048367776660494391844357073764099100641 / 5000000000000000000000000000000000000000 : ℚ), (17824917651414248444170424220583598813833 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_return_valid : leaf_first_miss_return.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_return]

def leaf_first_miss_entire_MARK_protected_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_entire_MARK_protected_left_valid : leaf_first_miss_entire_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_entire_MARK_protected_left]

def leaf_first_miss_entire_MARK_protected_right : RationalBox := ⟨(8048367776660494391844357073764099100641 / 5000000000000000000000000000000000000000 : ℚ), (16096735553320988783688714147528198201283 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_entire_MARK_protected_right_valid : leaf_first_miss_entire_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_entire_MARK_protected_right]

def leaf_first_miss_ready_before_following_input_left : RationalBox := ⟨(2228114706426781055521303027572949851729 / 1250000000000000000000000000000000000000 : ℚ), (17824917651414248444170424220583598813833 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_ready_before_following_input_left_valid : leaf_first_miss_ready_before_following_input_left.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_ready_before_following_input_left]

def leaf_first_miss_ready_before_following_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem leaf_first_miss_ready_before_following_input_right_valid : leaf_first_miss_ready_before_following_input_right.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_ready_before_following_input_right]

def leaf_first_miss_entire_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_entire_ERROR_protected_left_valid : leaf_first_miss_entire_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_entire_ERROR_protected_left]

def leaf_first_miss_entire_ERROR_protected_right : RationalBox := ⟨(8048367776660494391844357073764099100641 / 5000000000000000000000000000000000000000 : ℚ), (16096735553320988783688714147528198201283 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_entire_ERROR_protected_right_valid : leaf_first_miss_entire_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_entire_ERROR_protected_right]

def leaf_first_output_gap_lower_left : RationalBox := ⟨(37 / 5 : ℚ), (37 / 5 : ℚ)⟩
theorem leaf_first_output_gap_lower_left_valid : leaf_first_output_gap_lower_left.Valid := by norm_num [RationalBox.Valid, leaf_first_output_gap_lower_left]

def leaf_first_output_gap_lower_right : RationalBox := ⟨(799 / 100 : ℚ), (799 / 100 : ℚ)⟩
theorem leaf_first_output_gap_lower_right_valid : leaf_first_output_gap_lower_right.Valid := by norm_num [RationalBox.Valid, leaf_first_output_gap_lower_right]

def leaf_first_output_gap_upper_left : RationalBox := ⟨(413 / 50 : ℚ), (413 / 50 : ℚ)⟩
theorem leaf_first_output_gap_upper_left_valid : leaf_first_output_gap_upper_left.Valid := by norm_num [RationalBox.Valid, leaf_first_output_gap_upper_left]

def leaf_first_output_gap_upper_right : RationalBox := ⟨(83 / 10 : ℚ), (83 / 10 : ℚ)⟩
theorem leaf_first_output_gap_upper_right_valid : leaf_first_output_gap_upper_right.Valid := by norm_num [RationalBox.Valid, leaf_first_output_gap_upper_right]

def preparation_last_return_before_fast_start_left : RationalBox := ⟨(158737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem preparation_last_return_before_fast_start_left_valid : preparation_last_return_before_fast_start_left.Valid := by norm_num [RationalBox.Valid, preparation_last_return_before_fast_start_left]

def preparation_last_return_before_fast_start_right : RationalBox := ⟨(1599 / 10 : ℚ), (1599 / 10 : ℚ)⟩
theorem preparation_last_return_before_fast_start_right_valid : preparation_last_return_before_fast_start_right.Valid := by norm_num [RationalBox.Valid, preparation_last_return_before_fast_start_right]

def horizon_cell_latency_left : RationalBox := ⟨(33 / 50 : ℚ), (33 / 50 : ℚ)⟩
theorem horizon_cell_latency_left_valid : horizon_cell_latency_left.Valid := by norm_num [RationalBox.Valid, horizon_cell_latency_left]

def horizon_cell_latency_right : RationalBox := ⟨(7 / 10 : ℚ), (7 / 10 : ℚ)⟩
theorem horizon_cell_latency_right_valid : horizon_cell_latency_right.Valid := by norm_num [RationalBox.Valid, horizon_cell_latency_right]

def horizon_hop_budget_left : RationalBox := ⟨(53 / 50 : ℚ), (53 / 50 : ℚ)⟩
theorem horizon_hop_budget_left_valid : horizon_hop_budget_left.Valid := by norm_num [RationalBox.Valid, horizon_hop_budget_left]

def horizon_hop_budget_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem horizon_hop_budget_right_valid : horizon_hop_budget_right.Valid := by norm_num [RationalBox.Valid, horizon_hop_budget_right]

def horizon_last_return_budget_left : RationalBox := ⟨(8437776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67507868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem horizon_last_return_budget_left_valid : horizon_last_return_budget_left.Valid := by norm_num [RationalBox.Valid, horizon_last_return_budget_left]

def horizon_last_return_budget_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem horizon_last_return_budget_right_valid : horizon_last_return_budget_right.Valid := by norm_num [RationalBox.Valid, horizon_last_return_budget_right]

def probe_before_next_raw_entirely_protected_left : RationalBox := ⟨(5 / 1 : ℚ), (5 / 1 : ℚ)⟩
theorem probe_before_next_raw_entirely_protected_left_valid : probe_before_next_raw_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, probe_before_next_raw_entirely_protected_left]

def probe_before_next_raw_entirely_protected_right : RationalBox := ⟨(8425276594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67402212758966449929644309303261544994729 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_before_next_raw_entirely_protected_right_valid : probe_before_next_raw_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, probe_before_next_raw_entirely_protected_right]

def probe_before_ready_for_third_left : RationalBox := ⟨(33753934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (67507868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_before_ready_for_third_left_valid : probe_before_ready_for_third_left.Valid := by norm_num [RationalBox.Valid, probe_before_ready_for_third_left]

def probe_before_ready_for_third_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem probe_before_ready_for_third_right_valid : probe_before_ready_for_third_right.Valid := by norm_num [RationalBox.Valid, probe_before_ready_for_third_right]

def probe_after_ready_for_every_next_left : RationalBox := ⟨(457669357046946980573017451698732555939 / 125000000000000000000000000000000000000 : ℚ), (36613548563755758445841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_after_ready_for_every_next_left_valid : probe_after_ready_for_every_next_left.Valid := by norm_num [RationalBox.Valid, probe_after_ready_for_every_next_left]

def probe_after_ready_for_every_next_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem probe_after_ready_for_every_next_right_valid : probe_after_ready_for_every_next_right.Valid := by norm_num [RationalBox.Valid, probe_after_ready_for_every_next_right]

def probe_leaf_before_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem probe_leaf_before_flow_increases_left_valid : probe_leaf_before_flow_increases_left.Valid := by norm_num [RationalBox.Valid, probe_leaf_before_flow_increases_left]

def probe_leaf_before_flow_increases_right : RationalBox := ⟨(72262701797365403720056619589354882941 / 2500000000000000000000000000000000000000 : ℚ), (289305227751807229853387545682035567811 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_leaf_before_flow_increases_right_valid : probe_leaf_before_flow_increases_right.Valid := by norm_num [RationalBox.Valid, probe_leaf_before_flow_increases_right]

def probe_leaf_before_never_fires_left : RationalBox := ⟨(2934833184523160954196053880940963649213 / 10000000000000000000000000000000000000000 : ℚ), (293487188157382063411024829656494348539 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_leaf_before_never_fires_left_valid : probe_leaf_before_never_fires_left.Valid := by norm_num [RationalBox.Valid, probe_leaf_before_never_fires_left]

def probe_leaf_before_never_fires_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem probe_leaf_before_never_fires_right_valid : probe_leaf_before_never_fires_right.Valid := by norm_num [RationalBox.Valid, probe_leaf_before_never_fires_right]

theorem aux_birth_below_threshold_verified : RationalBox.StrictBefore aux_birth_below_threshold_left aux_birth_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, aux_birth_below_threshold_left, aux_birth_below_threshold_right]

theorem aux_root_lower_verified : RationalBox.StrictBefore aux_root_lower_left aux_root_lower_right := by
  norm_num [RationalBox.StrictBefore, aux_root_lower_left, aux_root_lower_right]

theorem aux_root_upper_verified : RationalBox.StrictBefore aux_root_upper_left aux_root_upper_right := by
  norm_num [RationalBox.StrictBefore, aux_root_upper_left, aux_root_upper_right]

theorem aux_root_strict_verified : RationalBox.StrictBefore aux_root_strict_left aux_root_strict_right := by
  norm_num [RationalBox.StrictBefore, aux_root_strict_left, aux_root_strict_right]

theorem aux_finish_after_raw_verified : RationalBox.StrictBefore aux_finish_after_raw_left aux_finish_after_raw_right := by
  norm_num [RationalBox.StrictBefore, aux_finish_after_raw_left, aux_finish_after_raw_right]

theorem aux_finish_before_fastest_next_input_verified : RationalBox.StrictBefore aux_finish_before_fastest_next_input_left aux_finish_before_fastest_next_input_right := by
  norm_num [RationalBox.StrictBefore, aux_finish_before_fastest_next_input_left, aux_finish_before_fastest_next_input_right]

theorem energy_reserve_invariant_verified : RationalBox.StrictBefore energy_reserve_invariant_left energy_reserve_invariant_right := by
  norm_num [RationalBox.StrictBefore, energy_reserve_invariant_left, energy_reserve_invariant_right]

theorem caps_final_gain_verified : RationalBox.StrictBefore caps_final_gain_left caps_final_gain_right := by
  norm_num [RationalBox.StrictBefore, caps_final_gain_left, caps_final_gain_right]

theorem caps_final_recovery_verified : RationalBox.StrictBefore caps_final_recovery_left caps_final_recovery_right := by
  norm_num [RationalBox.StrictBefore, caps_final_recovery_left, caps_final_recovery_right]

theorem relay_low_root_positive_coefficient_verified : RationalBox.StrictBefore relay_low_root_positive_coefficient_left relay_low_root_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, relay_low_root_positive_coefficient_left, relay_low_root_positive_coefficient_right]

theorem relay_low_root_increasing_verified : RationalBox.StrictBefore relay_low_root_increasing_left relay_low_root_increasing_right := by
  norm_num [RationalBox.StrictBefore, relay_low_root_increasing_left, relay_low_root_increasing_right]

theorem relay_low_root_lower_sign_verified : RationalBox.StrictBefore relay_low_root_lower_sign_left relay_low_root_lower_sign_right := by
  norm_num [RationalBox.StrictBefore, relay_low_root_lower_sign_left, relay_low_root_lower_sign_right]

theorem relay_low_root_upper_sign_verified : RationalBox.StrictBefore relay_low_root_upper_sign_left relay_low_root_upper_sign_right := by
  norm_num [RationalBox.StrictBefore, relay_low_root_upper_sign_left, relay_low_root_upper_sign_right]

theorem relay_low_root_MARK_precedes_fire_verified : RationalBox.StrictBefore relay_low_root_MARK_precedes_fire_left relay_low_root_MARK_precedes_fire_right := by
  norm_num [RationalBox.StrictBefore, relay_low_root_MARK_precedes_fire_left, relay_low_root_MARK_precedes_fire_right]

theorem relay_low_root_fire_precedes_ERROR_verified : RationalBox.StrictBefore relay_low_root_fire_precedes_ERROR_left relay_low_root_fire_precedes_ERROR_right := by
  norm_num [RationalBox.StrictBefore, relay_low_root_fire_precedes_ERROR_left, relay_low_root_fire_precedes_ERROR_right]

theorem relay_low_root_ERROR_entirely_protected_verified : RationalBox.StrictBefore relay_low_root_ERROR_entirely_protected_left relay_low_root_ERROR_entirely_protected_right := by
  norm_num [RationalBox.StrictBefore, relay_low_root_ERROR_entirely_protected_left, relay_low_root_ERROR_entirely_protected_right]

theorem relay_low_root_at_b2_ERROR_entirely_protected_verified : RationalBox.StrictBefore relay_low_root_at_b2_ERROR_entirely_protected_left relay_low_root_at_b2_ERROR_entirely_protected_right := by
  norm_num [RationalBox.StrictBefore, relay_low_root_at_b2_ERROR_entirely_protected_left, relay_low_root_at_b2_ERROR_entirely_protected_right]

theorem relay_high_rest_root_positive_coefficient_verified : RationalBox.StrictBefore relay_high_rest_root_positive_coefficient_left relay_high_rest_root_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, relay_high_rest_root_positive_coefficient_left, relay_high_rest_root_positive_coefficient_right]

theorem relay_high_rest_root_increasing_verified : RationalBox.StrictBefore relay_high_rest_root_increasing_left relay_high_rest_root_increasing_right := by
  norm_num [RationalBox.StrictBefore, relay_high_rest_root_increasing_left, relay_high_rest_root_increasing_right]

theorem relay_high_rest_root_lower_sign_verified : RationalBox.StrictBefore relay_high_rest_root_lower_sign_left relay_high_rest_root_lower_sign_right := by
  norm_num [RationalBox.StrictBefore, relay_high_rest_root_lower_sign_left, relay_high_rest_root_lower_sign_right]

theorem relay_high_rest_root_upper_sign_verified : RationalBox.StrictBefore relay_high_rest_root_upper_sign_left relay_high_rest_root_upper_sign_right := by
  norm_num [RationalBox.StrictBefore, relay_high_rest_root_upper_sign_left, relay_high_rest_root_upper_sign_right]

theorem relay_high_rest_root_MARK_precedes_fire_verified : RationalBox.StrictBefore relay_high_rest_root_MARK_precedes_fire_left relay_high_rest_root_MARK_precedes_fire_right := by
  norm_num [RationalBox.StrictBefore, relay_high_rest_root_MARK_precedes_fire_left, relay_high_rest_root_MARK_precedes_fire_right]

theorem relay_high_rest_root_fire_precedes_ERROR_verified : RationalBox.StrictBefore relay_high_rest_root_fire_precedes_ERROR_left relay_high_rest_root_fire_precedes_ERROR_right := by
  norm_num [RationalBox.StrictBefore, relay_high_rest_root_fire_precedes_ERROR_left, relay_high_rest_root_fire_precedes_ERROR_right]

theorem relay_high_rest_root_ERROR_entirely_protected_verified : RationalBox.StrictBefore relay_high_rest_root_ERROR_entirely_protected_left relay_high_rest_root_ERROR_entirely_protected_right := by
  norm_num [RationalBox.StrictBefore, relay_high_rest_root_ERROR_entirely_protected_left, relay_high_rest_root_ERROR_entirely_protected_right]

theorem slow_prefix_ready_before_every_input_verified : RationalBox.StrictBefore slow_prefix_ready_before_every_input_left slow_prefix_ready_before_every_input_right := by
  norm_num [RationalBox.StrictBefore, slow_prefix_ready_before_every_input_left, slow_prefix_ready_before_every_input_right]

theorem steady_tail_ready_before_every_input_verified : RationalBox.StrictBefore steady_tail_ready_before_every_input_left steady_tail_ready_before_every_input_right := by
  norm_num [RationalBox.StrictBefore, steady_tail_ready_before_every_input_left, steady_tail_ready_before_every_input_right]

theorem h_increasing_through_raw_end_verified : RationalBox.StrictBefore h_increasing_through_raw_end_left h_increasing_through_raw_end_right := by
  norm_num [RationalBox.StrictBefore, h_increasing_through_raw_end_left, h_increasing_through_raw_end_right]

theorem relay_first_miss_past_FAST_verified : RationalBox.StrictBefore relay_first_miss_past_FAST_left relay_first_miss_past_FAST_right := by
  norm_num [RationalBox.StrictBefore, relay_first_miss_past_FAST_left, relay_first_miss_past_FAST_right]

theorem relay_first_miss_still_in_SLOW_verified : RationalBox.StrictBefore relay_first_miss_still_in_SLOW_left relay_first_miss_still_in_SLOW_right := by
  norm_num [RationalBox.StrictBefore, relay_first_miss_still_in_SLOW_left, relay_first_miss_still_in_SLOW_right]

theorem relay_first_miss_entire_MARK_protected_verified : RationalBox.StrictBefore relay_first_miss_entire_MARK_protected_left relay_first_miss_entire_MARK_protected_right := by
  norm_num [RationalBox.StrictBefore, relay_first_miss_entire_MARK_protected_left, relay_first_miss_entire_MARK_protected_right]

theorem relay_first_miss_ready_before_following_input_verified : RationalBox.StrictBefore relay_first_miss_ready_before_following_input_left relay_first_miss_ready_before_following_input_right := by
  norm_num [RationalBox.StrictBefore, relay_first_miss_ready_before_following_input_left, relay_first_miss_ready_before_following_input_right]

theorem relay_first_miss_entire_ERROR_protected_verified : RationalBox.StrictBefore relay_first_miss_entire_ERROR_protected_left relay_first_miss_entire_ERROR_protected_right := by
  norm_num [RationalBox.StrictBefore, relay_first_miss_entire_ERROR_protected_left, relay_first_miss_entire_ERROR_protected_right]

theorem relay_second_miss_past_FAST_verified : RationalBox.StrictBefore relay_second_miss_past_FAST_left relay_second_miss_past_FAST_right := by
  norm_num [RationalBox.StrictBefore, relay_second_miss_past_FAST_left, relay_second_miss_past_FAST_right]

theorem relay_second_miss_still_in_SLOW_verified : RationalBox.StrictBefore relay_second_miss_still_in_SLOW_left relay_second_miss_still_in_SLOW_right := by
  norm_num [RationalBox.StrictBefore, relay_second_miss_still_in_SLOW_left, relay_second_miss_still_in_SLOW_right]

theorem relay_second_miss_entire_MARK_protected_verified : RationalBox.StrictBefore relay_second_miss_entire_MARK_protected_left relay_second_miss_entire_MARK_protected_right := by
  norm_num [RationalBox.StrictBefore, relay_second_miss_entire_MARK_protected_left, relay_second_miss_entire_MARK_protected_right]

theorem relay_second_miss_ready_before_following_input_verified : RationalBox.StrictBefore relay_second_miss_ready_before_following_input_left relay_second_miss_ready_before_following_input_right := by
  norm_num [RationalBox.StrictBefore, relay_second_miss_ready_before_following_input_left, relay_second_miss_ready_before_following_input_right]

theorem relay_second_miss_ready_before_ERROR_verified : RationalBox.StrictBefore relay_second_miss_ready_before_ERROR_left relay_second_miss_ready_before_ERROR_right := by
  norm_num [RationalBox.StrictBefore, relay_second_miss_ready_before_ERROR_left, relay_second_miss_ready_before_ERROR_right]

theorem relay_second_miss_before_raw_end_verified : RationalBox.StrictBefore relay_second_miss_before_raw_end_left relay_second_miss_before_raw_end_right := by
  norm_num [RationalBox.StrictBefore, relay_second_miss_before_raw_end_left, relay_second_miss_before_raw_end_right]

theorem relay_second_miss_no_refire_from_tail_verified : RationalBox.StrictBefore relay_second_miss_no_refire_from_tail_left relay_second_miss_no_refire_from_tail_right := by
  norm_num [RationalBox.StrictBefore, relay_second_miss_no_refire_from_tail_left, relay_second_miss_no_refire_from_tail_right]

theorem relay_high_transient_root_positive_coefficient_verified : RationalBox.StrictBefore relay_high_transient_root_positive_coefficient_left relay_high_transient_root_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, relay_high_transient_root_positive_coefficient_left, relay_high_transient_root_positive_coefficient_right]

theorem relay_high_transient_root_increasing_verified : RationalBox.StrictBefore relay_high_transient_root_increasing_left relay_high_transient_root_increasing_right := by
  norm_num [RationalBox.StrictBefore, relay_high_transient_root_increasing_left, relay_high_transient_root_increasing_right]

theorem relay_high_transient_root_lower_sign_verified : RationalBox.StrictBefore relay_high_transient_root_lower_sign_left relay_high_transient_root_lower_sign_right := by
  norm_num [RationalBox.StrictBefore, relay_high_transient_root_lower_sign_left, relay_high_transient_root_lower_sign_right]

theorem relay_high_transient_root_upper_sign_verified : RationalBox.StrictBefore relay_high_transient_root_upper_sign_left relay_high_transient_root_upper_sign_right := by
  norm_num [RationalBox.StrictBefore, relay_high_transient_root_upper_sign_left, relay_high_transient_root_upper_sign_right]

theorem relay_high_transient_root_MARK_precedes_fire_verified : RationalBox.StrictBefore relay_high_transient_root_MARK_precedes_fire_left relay_high_transient_root_MARK_precedes_fire_right := by
  norm_num [RationalBox.StrictBefore, relay_high_transient_root_MARK_precedes_fire_left, relay_high_transient_root_MARK_precedes_fire_right]

theorem relay_high_transient_root_fire_precedes_ERROR_verified : RationalBox.StrictBefore relay_high_transient_root_fire_precedes_ERROR_left relay_high_transient_root_fire_precedes_ERROR_right := by
  norm_num [RationalBox.StrictBefore, relay_high_transient_root_fire_precedes_ERROR_left, relay_high_transient_root_fire_precedes_ERROR_right]

theorem relay_high_transient_root_ERROR_entirely_protected_verified : RationalBox.StrictBefore relay_high_transient_root_ERROR_entirely_protected_left relay_high_transient_root_ERROR_entirely_protected_right := by
  norm_num [RationalBox.StrictBefore, relay_high_transient_root_ERROR_entirely_protected_left, relay_high_transient_root_ERROR_entirely_protected_right]

theorem relay_transient_return_before_next_input_verified : RationalBox.StrictBefore relay_transient_return_before_next_input_left relay_transient_return_before_next_input_right := by
  norm_num [RationalBox.StrictBefore, relay_transient_return_before_next_input_left, relay_transient_return_before_next_input_right]

theorem output_first_new_slow_lower_verified : RationalBox.StrictBefore output_first_new_slow_lower_left output_first_new_slow_lower_right := by
  norm_num [RationalBox.StrictBefore, output_first_new_slow_lower_left, output_first_new_slow_lower_right]

theorem output_first_new_slow_upper_verified : RationalBox.StrictBefore output_first_new_slow_upper_left output_first_new_slow_upper_right := by
  norm_num [RationalBox.StrictBefore, output_first_new_slow_upper_left, output_first_new_slow_upper_right]

theorem output_second_new_slow_lower_verified : RationalBox.StrictBefore output_second_new_slow_lower_left output_second_new_slow_lower_right := by
  norm_num [RationalBox.StrictBefore, output_second_new_slow_lower_left, output_second_new_slow_lower_right]

theorem output_second_new_slow_upper_verified : RationalBox.StrictBefore output_second_new_slow_upper_left output_second_new_slow_upper_right := by
  norm_num [RationalBox.StrictBefore, output_second_new_slow_upper_left, output_second_new_slow_upper_right]

theorem output_settling_upper_verified : RationalBox.StrictBefore output_settling_upper_left output_settling_upper_right := by
  norm_num [RationalBox.StrictBefore, output_settling_upper_left, output_settling_upper_right]

theorem leaf_weak_0_increasing_verified : RationalBox.StrictBefore leaf_weak_0_increasing_left leaf_weak_0_increasing_right := by
  norm_num [RationalBox.StrictBefore, leaf_weak_0_increasing_left, leaf_weak_0_increasing_right]

theorem leaf_weak_0_no_fire_verified : RationalBox.StrictBefore leaf_weak_0_no_fire_left leaf_weak_0_no_fire_right := by
  norm_num [RationalBox.StrictBefore, leaf_weak_0_no_fire_left, leaf_weak_0_no_fire_right]

theorem leaf_weak_1_increasing_verified : RationalBox.StrictBefore leaf_weak_1_increasing_left leaf_weak_1_increasing_right := by
  norm_num [RationalBox.StrictBefore, leaf_weak_1_increasing_left, leaf_weak_1_increasing_right]

theorem leaf_weak_1_no_fire_verified : RationalBox.StrictBefore leaf_weak_1_no_fire_left leaf_weak_1_no_fire_right := by
  norm_num [RationalBox.StrictBefore, leaf_weak_1_no_fire_left, leaf_weak_1_no_fire_right]

theorem leaf_weak_2_increasing_verified : RationalBox.StrictBefore leaf_weak_2_increasing_left leaf_weak_2_increasing_right := by
  norm_num [RationalBox.StrictBefore, leaf_weak_2_increasing_left, leaf_weak_2_increasing_right]

theorem leaf_weak_2_no_fire_verified : RationalBox.StrictBefore leaf_weak_2_no_fire_left leaf_weak_2_no_fire_right := by
  norm_num [RationalBox.StrictBefore, leaf_weak_2_no_fire_left, leaf_weak_2_no_fire_right]

theorem leaf_first_root_positive_coefficient_verified : RationalBox.StrictBefore leaf_first_root_positive_coefficient_left leaf_first_root_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_root_positive_coefficient_left, leaf_first_root_positive_coefficient_right]

theorem leaf_first_root_increasing_verified : RationalBox.StrictBefore leaf_first_root_increasing_left leaf_first_root_increasing_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_root_increasing_left, leaf_first_root_increasing_right]

theorem leaf_first_root_lower_sign_verified : RationalBox.StrictBefore leaf_first_root_lower_sign_left leaf_first_root_lower_sign_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_root_lower_sign_left, leaf_first_root_lower_sign_right]

theorem leaf_first_root_upper_sign_verified : RationalBox.StrictBefore leaf_first_root_upper_sign_left leaf_first_root_upper_sign_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_root_upper_sign_left, leaf_first_root_upper_sign_right]

theorem leaf_first_root_MARK_precedes_fire_verified : RationalBox.StrictBefore leaf_first_root_MARK_precedes_fire_left leaf_first_root_MARK_precedes_fire_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_root_MARK_precedes_fire_left, leaf_first_root_MARK_precedes_fire_right]

theorem leaf_first_root_fire_precedes_ERROR_verified : RationalBox.StrictBefore leaf_first_root_fire_precedes_ERROR_left leaf_first_root_fire_precedes_ERROR_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_root_fire_precedes_ERROR_left, leaf_first_root_fire_precedes_ERROR_right]

theorem leaf_first_root_ERROR_entirely_protected_verified : RationalBox.StrictBefore leaf_first_root_ERROR_entirely_protected_left leaf_first_root_ERROR_entirely_protected_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_root_ERROR_entirely_protected_left, leaf_first_root_ERROR_entirely_protected_right]

theorem leaf_first_miss_past_FAST_verified : RationalBox.StrictBefore leaf_first_miss_past_FAST_left leaf_first_miss_past_FAST_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_miss_past_FAST_left, leaf_first_miss_past_FAST_right]

theorem leaf_first_miss_still_in_SLOW_verified : RationalBox.StrictBefore leaf_first_miss_still_in_SLOW_left leaf_first_miss_still_in_SLOW_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_miss_still_in_SLOW_left, leaf_first_miss_still_in_SLOW_right]

theorem leaf_first_miss_entire_MARK_protected_verified : RationalBox.StrictBefore leaf_first_miss_entire_MARK_protected_left leaf_first_miss_entire_MARK_protected_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_miss_entire_MARK_protected_left, leaf_first_miss_entire_MARK_protected_right]

theorem leaf_first_miss_ready_before_following_input_verified : RationalBox.StrictBefore leaf_first_miss_ready_before_following_input_left leaf_first_miss_ready_before_following_input_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_miss_ready_before_following_input_left, leaf_first_miss_ready_before_following_input_right]

theorem leaf_first_miss_entire_ERROR_protected_verified : RationalBox.StrictBefore leaf_first_miss_entire_ERROR_protected_left leaf_first_miss_entire_ERROR_protected_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_miss_entire_ERROR_protected_left, leaf_first_miss_entire_ERROR_protected_right]

theorem leaf_first_output_gap_lower_verified : RationalBox.StrictBefore leaf_first_output_gap_lower_left leaf_first_output_gap_lower_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_output_gap_lower_left, leaf_first_output_gap_lower_right]

theorem leaf_first_output_gap_upper_verified : RationalBox.StrictBefore leaf_first_output_gap_upper_left leaf_first_output_gap_upper_right := by
  norm_num [RationalBox.StrictBefore, leaf_first_output_gap_upper_left, leaf_first_output_gap_upper_right]

theorem preparation_last_return_before_fast_start_verified : RationalBox.StrictBefore preparation_last_return_before_fast_start_left preparation_last_return_before_fast_start_right := by
  norm_num [RationalBox.StrictBefore, preparation_last_return_before_fast_start_left, preparation_last_return_before_fast_start_right]

theorem horizon_cell_latency_verified : RationalBox.StrictBefore horizon_cell_latency_left horizon_cell_latency_right := by
  norm_num [RationalBox.StrictBefore, horizon_cell_latency_left, horizon_cell_latency_right]

theorem horizon_hop_budget_verified : RationalBox.StrictBefore horizon_hop_budget_left horizon_hop_budget_right := by
  norm_num [RationalBox.StrictBefore, horizon_hop_budget_left, horizon_hop_budget_right]

theorem horizon_last_return_budget_verified : RationalBox.StrictBefore horizon_last_return_budget_left horizon_last_return_budget_right := by
  norm_num [RationalBox.StrictBefore, horizon_last_return_budget_left, horizon_last_return_budget_right]

theorem probe_before_next_raw_entirely_protected_verified : RationalBox.StrictBefore probe_before_next_raw_entirely_protected_left probe_before_next_raw_entirely_protected_right := by
  norm_num [RationalBox.StrictBefore, probe_before_next_raw_entirely_protected_left, probe_before_next_raw_entirely_protected_right]

theorem probe_before_ready_for_third_verified : RationalBox.StrictBefore probe_before_ready_for_third_left probe_before_ready_for_third_right := by
  norm_num [RationalBox.StrictBefore, probe_before_ready_for_third_left, probe_before_ready_for_third_right]

theorem probe_after_ready_for_every_next_verified : RationalBox.StrictBefore probe_after_ready_for_every_next_left probe_after_ready_for_every_next_right := by
  norm_num [RationalBox.StrictBefore, probe_after_ready_for_every_next_left, probe_after_ready_for_every_next_right]

theorem probe_leaf_before_flow_increases_verified : RationalBox.StrictBefore probe_leaf_before_flow_increases_left probe_leaf_before_flow_increases_right := by
  norm_num [RationalBox.StrictBefore, probe_leaf_before_flow_increases_left, probe_leaf_before_flow_increases_right]

theorem probe_leaf_before_never_fires_verified : RationalBox.StrictBefore probe_leaf_before_never_fires_left probe_leaf_before_never_fires_right := by
  norm_num [RationalBox.StrictBefore, probe_leaf_before_never_fires_left, probe_leaf_before_never_fires_right]

def Obligations : Prop :=
  RationalBox.StrictBefore aux_birth_below_threshold_left aux_birth_below_threshold_right ∧
  RationalBox.StrictBefore aux_root_lower_left aux_root_lower_right ∧
  RationalBox.StrictBefore aux_root_upper_left aux_root_upper_right ∧
  RationalBox.StrictBefore aux_root_strict_left aux_root_strict_right ∧
  RationalBox.StrictBefore aux_finish_after_raw_left aux_finish_after_raw_right ∧
  RationalBox.StrictBefore aux_finish_before_fastest_next_input_left aux_finish_before_fastest_next_input_right ∧
  RationalBox.StrictBefore energy_reserve_invariant_left energy_reserve_invariant_right ∧
  RationalBox.StrictBefore caps_final_gain_left caps_final_gain_right ∧
  RationalBox.StrictBefore caps_final_recovery_left caps_final_recovery_right ∧
  RationalBox.StrictBefore relay_low_root_positive_coefficient_left relay_low_root_positive_coefficient_right ∧
  RationalBox.StrictBefore relay_low_root_increasing_left relay_low_root_increasing_right ∧
  RationalBox.StrictBefore relay_low_root_lower_sign_left relay_low_root_lower_sign_right ∧
  RationalBox.StrictBefore relay_low_root_upper_sign_left relay_low_root_upper_sign_right ∧
  RationalBox.StrictBefore relay_low_root_MARK_precedes_fire_left relay_low_root_MARK_precedes_fire_right ∧
  RationalBox.StrictBefore relay_low_root_fire_precedes_ERROR_left relay_low_root_fire_precedes_ERROR_right ∧
  RationalBox.StrictBefore relay_low_root_ERROR_entirely_protected_left relay_low_root_ERROR_entirely_protected_right ∧
  RationalBox.StrictBefore relay_low_root_at_b2_ERROR_entirely_protected_left relay_low_root_at_b2_ERROR_entirely_protected_right ∧
  RationalBox.StrictBefore relay_high_rest_root_positive_coefficient_left relay_high_rest_root_positive_coefficient_right ∧
  RationalBox.StrictBefore relay_high_rest_root_increasing_left relay_high_rest_root_increasing_right ∧
  RationalBox.StrictBefore relay_high_rest_root_lower_sign_left relay_high_rest_root_lower_sign_right ∧
  RationalBox.StrictBefore relay_high_rest_root_upper_sign_left relay_high_rest_root_upper_sign_right ∧
  RationalBox.StrictBefore relay_high_rest_root_MARK_precedes_fire_left relay_high_rest_root_MARK_precedes_fire_right ∧
  RationalBox.StrictBefore relay_high_rest_root_fire_precedes_ERROR_left relay_high_rest_root_fire_precedes_ERROR_right ∧
  RationalBox.StrictBefore relay_high_rest_root_ERROR_entirely_protected_left relay_high_rest_root_ERROR_entirely_protected_right ∧
  RationalBox.StrictBefore slow_prefix_ready_before_every_input_left slow_prefix_ready_before_every_input_right ∧
  RationalBox.StrictBefore steady_tail_ready_before_every_input_left steady_tail_ready_before_every_input_right ∧
  RationalBox.StrictBefore h_increasing_through_raw_end_left h_increasing_through_raw_end_right ∧
  RationalBox.StrictBefore relay_first_miss_past_FAST_left relay_first_miss_past_FAST_right ∧
  RationalBox.StrictBefore relay_first_miss_still_in_SLOW_left relay_first_miss_still_in_SLOW_right ∧
  RationalBox.StrictBefore relay_first_miss_entire_MARK_protected_left relay_first_miss_entire_MARK_protected_right ∧
  RationalBox.StrictBefore relay_first_miss_ready_before_following_input_left relay_first_miss_ready_before_following_input_right ∧
  RationalBox.StrictBefore relay_first_miss_entire_ERROR_protected_left relay_first_miss_entire_ERROR_protected_right ∧
  RationalBox.StrictBefore relay_second_miss_past_FAST_left relay_second_miss_past_FAST_right ∧
  RationalBox.StrictBefore relay_second_miss_still_in_SLOW_left relay_second_miss_still_in_SLOW_right ∧
  RationalBox.StrictBefore relay_second_miss_entire_MARK_protected_left relay_second_miss_entire_MARK_protected_right ∧
  RationalBox.StrictBefore relay_second_miss_ready_before_following_input_left relay_second_miss_ready_before_following_input_right ∧
  RationalBox.StrictBefore relay_second_miss_ready_before_ERROR_left relay_second_miss_ready_before_ERROR_right ∧
  RationalBox.StrictBefore relay_second_miss_before_raw_end_left relay_second_miss_before_raw_end_right ∧
  RationalBox.StrictBefore relay_second_miss_no_refire_from_tail_left relay_second_miss_no_refire_from_tail_right ∧
  RationalBox.StrictBefore relay_high_transient_root_positive_coefficient_left relay_high_transient_root_positive_coefficient_right ∧
  RationalBox.StrictBefore relay_high_transient_root_increasing_left relay_high_transient_root_increasing_right ∧
  RationalBox.StrictBefore relay_high_transient_root_lower_sign_left relay_high_transient_root_lower_sign_right ∧
  RationalBox.StrictBefore relay_high_transient_root_upper_sign_left relay_high_transient_root_upper_sign_right ∧
  RationalBox.StrictBefore relay_high_transient_root_MARK_precedes_fire_left relay_high_transient_root_MARK_precedes_fire_right ∧
  RationalBox.StrictBefore relay_high_transient_root_fire_precedes_ERROR_left relay_high_transient_root_fire_precedes_ERROR_right ∧
  RationalBox.StrictBefore relay_high_transient_root_ERROR_entirely_protected_left relay_high_transient_root_ERROR_entirely_protected_right ∧
  RationalBox.StrictBefore relay_transient_return_before_next_input_left relay_transient_return_before_next_input_right ∧
  RationalBox.StrictBefore output_first_new_slow_lower_left output_first_new_slow_lower_right ∧
  RationalBox.StrictBefore output_first_new_slow_upper_left output_first_new_slow_upper_right ∧
  RationalBox.StrictBefore output_second_new_slow_lower_left output_second_new_slow_lower_right ∧
  RationalBox.StrictBefore output_second_new_slow_upper_left output_second_new_slow_upper_right ∧
  RationalBox.StrictBefore output_settling_upper_left output_settling_upper_right ∧
  RationalBox.StrictBefore leaf_weak_0_increasing_left leaf_weak_0_increasing_right ∧
  RationalBox.StrictBefore leaf_weak_0_no_fire_left leaf_weak_0_no_fire_right ∧
  RationalBox.StrictBefore leaf_weak_1_increasing_left leaf_weak_1_increasing_right ∧
  RationalBox.StrictBefore leaf_weak_1_no_fire_left leaf_weak_1_no_fire_right ∧
  RationalBox.StrictBefore leaf_weak_2_increasing_left leaf_weak_2_increasing_right ∧
  RationalBox.StrictBefore leaf_weak_2_no_fire_left leaf_weak_2_no_fire_right ∧
  RationalBox.StrictBefore leaf_first_root_positive_coefficient_left leaf_first_root_positive_coefficient_right ∧
  RationalBox.StrictBefore leaf_first_root_increasing_left leaf_first_root_increasing_right ∧
  RationalBox.StrictBefore leaf_first_root_lower_sign_left leaf_first_root_lower_sign_right ∧
  RationalBox.StrictBefore leaf_first_root_upper_sign_left leaf_first_root_upper_sign_right ∧
  RationalBox.StrictBefore leaf_first_root_MARK_precedes_fire_left leaf_first_root_MARK_precedes_fire_right ∧
  RationalBox.StrictBefore leaf_first_root_fire_precedes_ERROR_left leaf_first_root_fire_precedes_ERROR_right ∧
  RationalBox.StrictBefore leaf_first_root_ERROR_entirely_protected_left leaf_first_root_ERROR_entirely_protected_right ∧
  RationalBox.StrictBefore leaf_first_miss_past_FAST_left leaf_first_miss_past_FAST_right ∧
  RationalBox.StrictBefore leaf_first_miss_still_in_SLOW_left leaf_first_miss_still_in_SLOW_right ∧
  RationalBox.StrictBefore leaf_first_miss_entire_MARK_protected_left leaf_first_miss_entire_MARK_protected_right ∧
  RationalBox.StrictBefore leaf_first_miss_ready_before_following_input_left leaf_first_miss_ready_before_following_input_right ∧
  RationalBox.StrictBefore leaf_first_miss_entire_ERROR_protected_left leaf_first_miss_entire_ERROR_protected_right ∧
  RationalBox.StrictBefore leaf_first_output_gap_lower_left leaf_first_output_gap_lower_right ∧
  RationalBox.StrictBefore leaf_first_output_gap_upper_left leaf_first_output_gap_upper_right ∧
  RationalBox.StrictBefore preparation_last_return_before_fast_start_left preparation_last_return_before_fast_start_right ∧
  RationalBox.StrictBefore horizon_cell_latency_left horizon_cell_latency_right ∧
  RationalBox.StrictBefore horizon_hop_budget_left horizon_hop_budget_right ∧
  RationalBox.StrictBefore horizon_last_return_budget_left horizon_last_return_budget_right ∧
  RationalBox.StrictBefore probe_before_next_raw_entirely_protected_left probe_before_next_raw_entirely_protected_right ∧
  RationalBox.StrictBefore probe_before_ready_for_third_left probe_before_ready_for_third_right ∧
  RationalBox.StrictBefore probe_after_ready_for_every_next_left probe_after_ready_for_every_next_right ∧
  RationalBox.StrictBefore probe_leaf_before_flow_increases_left probe_leaf_before_flow_increases_right ∧
  RationalBox.StrictBefore probe_leaf_before_never_fires_left probe_leaf_before_never_fires_right
theorem obligations_verified : Obligations := by
  exact ⟨aux_birth_below_threshold_verified, aux_root_lower_verified, aux_root_upper_verified, aux_root_strict_verified, aux_finish_after_raw_verified, aux_finish_before_fastest_next_input_verified, energy_reserve_invariant_verified, caps_final_gain_verified, caps_final_recovery_verified, relay_low_root_positive_coefficient_verified, relay_low_root_increasing_verified, relay_low_root_lower_sign_verified, relay_low_root_upper_sign_verified, relay_low_root_MARK_precedes_fire_verified, relay_low_root_fire_precedes_ERROR_verified, relay_low_root_ERROR_entirely_protected_verified, relay_low_root_at_b2_ERROR_entirely_protected_verified, relay_high_rest_root_positive_coefficient_verified, relay_high_rest_root_increasing_verified, relay_high_rest_root_lower_sign_verified, relay_high_rest_root_upper_sign_verified, relay_high_rest_root_MARK_precedes_fire_verified, relay_high_rest_root_fire_precedes_ERROR_verified, relay_high_rest_root_ERROR_entirely_protected_verified, slow_prefix_ready_before_every_input_verified, steady_tail_ready_before_every_input_verified, h_increasing_through_raw_end_verified, relay_first_miss_past_FAST_verified, relay_first_miss_still_in_SLOW_verified, relay_first_miss_entire_MARK_protected_verified, relay_first_miss_ready_before_following_input_verified, relay_first_miss_entire_ERROR_protected_verified, relay_second_miss_past_FAST_verified, relay_second_miss_still_in_SLOW_verified, relay_second_miss_entire_MARK_protected_verified, relay_second_miss_ready_before_following_input_verified, relay_second_miss_ready_before_ERROR_verified, relay_second_miss_before_raw_end_verified, relay_second_miss_no_refire_from_tail_verified, relay_high_transient_root_positive_coefficient_verified, relay_high_transient_root_increasing_verified, relay_high_transient_root_lower_sign_verified, relay_high_transient_root_upper_sign_verified, relay_high_transient_root_MARK_precedes_fire_verified, relay_high_transient_root_fire_precedes_ERROR_verified, relay_high_transient_root_ERROR_entirely_protected_verified, relay_transient_return_before_next_input_verified, output_first_new_slow_lower_verified, output_first_new_slow_upper_verified, output_second_new_slow_lower_verified, output_second_new_slow_upper_verified, output_settling_upper_verified, leaf_weak_0_increasing_verified, leaf_weak_0_no_fire_verified, leaf_weak_1_increasing_verified, leaf_weak_1_no_fire_verified, leaf_weak_2_increasing_verified, leaf_weak_2_no_fire_verified, leaf_first_root_positive_coefficient_verified, leaf_first_root_increasing_verified, leaf_first_root_lower_sign_verified, leaf_first_root_upper_sign_verified, leaf_first_root_MARK_precedes_fire_verified, leaf_first_root_fire_precedes_ERROR_verified, leaf_first_root_ERROR_entirely_protected_verified, leaf_first_miss_past_FAST_verified, leaf_first_miss_still_in_SLOW_verified, leaf_first_miss_entire_MARK_protected_verified, leaf_first_miss_ready_before_following_input_verified, leaf_first_miss_entire_ERROR_protected_verified, leaf_first_output_gap_lower_verified, leaf_first_output_gap_upper_verified, preparation_last_return_before_fast_start_verified, horizon_cell_latency_verified, horizon_hop_budget_verified, horizon_last_return_budget_verified, probe_before_next_raw_entirely_protected_verified, probe_before_ready_for_third_verified, probe_after_ready_for_every_next_verified, probe_leaf_before_flow_increases_verified, probe_leaf_before_never_fires_verified⟩

def AllBoundsValid : Prop :=
  aux_birth_below_threshold_left.Valid ∧
  aux_birth_below_threshold_right.Valid ∧
  aux_root_lower_left.Valid ∧
  aux_root_lower_right.Valid ∧
  aux_root_upper_left.Valid ∧
  aux_root_upper_right.Valid ∧
  aux_root_strict_left.Valid ∧
  aux_root_strict_right.Valid ∧
  aux_finish_after_raw_left.Valid ∧
  aux_finish_after_raw_right.Valid ∧
  aux_finish_before_fastest_next_input_left.Valid ∧
  aux_finish_before_fastest_next_input_right.Valid ∧
  energy_reserve_invariant_left.Valid ∧
  energy_reserve_invariant_right.Valid ∧
  caps_final_gain_left.Valid ∧
  caps_final_gain_right.Valid ∧
  caps_final_recovery_left.Valid ∧
  caps_final_recovery_right.Valid ∧
  jitter_budget.Valid ∧
  prepared_recovery.Valid ∧
  final_recovery.Valid ∧
  prepared_gain.Valid ∧
  final_gain.Valid ∧
  aux_mark_end.Valid ∧
  aux_ERROR_start.Valid ∧
  aux_finish.Valid ∧
  MARK_integral_deficit.Valid ∧
  relay_low_root_positive_coefficient_left.Valid ∧
  relay_low_root_positive_coefficient_right.Valid ∧
  relay_low_root_increasing_left.Valid ∧
  relay_low_root_increasing_right.Valid ∧
  relay_low_root_lower_sign_left.Valid ∧
  relay_low_root_lower_sign_right.Valid ∧
  relay_low_root_upper_sign_left.Valid ∧
  relay_low_root_upper_sign_right.Valid ∧
  relay_low_root_MARK_precedes_fire_left.Valid ∧
  relay_low_root_MARK_precedes_fire_right.Valid ∧
  relay_low_root_fire_precedes_ERROR_left.Valid ∧
  relay_low_root_fire_precedes_ERROR_right.Valid ∧
  relay_low_root_ERROR_entirely_protected_left.Valid ∧
  relay_low_root_ERROR_entirely_protected_right.Valid ∧
  relay_low_root_at_b2_ERROR_entirely_protected_left.Valid ∧
  relay_low_root_at_b2_ERROR_entirely_protected_right.Valid ∧
  relay_high_rest_root_positive_coefficient_left.Valid ∧
  relay_high_rest_root_positive_coefficient_right.Valid ∧
  relay_high_rest_root_increasing_left.Valid ∧
  relay_high_rest_root_increasing_right.Valid ∧
  relay_high_rest_root_lower_sign_left.Valid ∧
  relay_high_rest_root_lower_sign_right.Valid ∧
  relay_high_rest_root_upper_sign_left.Valid ∧
  relay_high_rest_root_upper_sign_right.Valid ∧
  relay_high_rest_root_MARK_precedes_fire_left.Valid ∧
  relay_high_rest_root_MARK_precedes_fire_right.Valid ∧
  relay_high_rest_root_fire_precedes_ERROR_left.Valid ∧
  relay_high_rest_root_fire_precedes_ERROR_right.Valid ∧
  relay_high_rest_root_ERROR_entirely_protected_left.Valid ∧
  relay_high_rest_root_ERROR_entirely_protected_right.Valid ∧
  slow_prefix_ready_before_every_input_left.Valid ∧
  slow_prefix_ready_before_every_input_right.Valid ∧
  steady_tail_ready_before_every_input_left.Valid ∧
  steady_tail_ready_before_every_input_right.Valid ∧
  h_increasing_through_raw_end_left.Valid ∧
  h_increasing_through_raw_end_right.Valid ∧
  relay_first_miss_past_FAST_left.Valid ∧
  relay_first_miss_past_FAST_right.Valid ∧
  relay_first_miss_still_in_SLOW_left.Valid ∧
  relay_first_miss_still_in_SLOW_right.Valid ∧
  relay_first_miss_return.Valid ∧
  relay_first_miss_entire_MARK_protected_left.Valid ∧
  relay_first_miss_entire_MARK_protected_right.Valid ∧
  relay_first_miss_ready_before_following_input_left.Valid ∧
  relay_first_miss_ready_before_following_input_right.Valid ∧
  relay_first_miss_entire_ERROR_protected_left.Valid ∧
  relay_first_miss_entire_ERROR_protected_right.Valid ∧
  relay_second_miss_past_FAST_left.Valid ∧
  relay_second_miss_past_FAST_right.Valid ∧
  relay_second_miss_still_in_SLOW_left.Valid ∧
  relay_second_miss_still_in_SLOW_right.Valid ∧
  relay_second_miss_return.Valid ∧
  relay_second_miss_entire_MARK_protected_left.Valid ∧
  relay_second_miss_entire_MARK_protected_right.Valid ∧
  relay_second_miss_ready_before_following_input_left.Valid ∧
  relay_second_miss_ready_before_following_input_right.Valid ∧
  relay_second_miss_ready_before_ERROR_left.Valid ∧
  relay_second_miss_ready_before_ERROR_right.Valid ∧
  relay_second_miss_before_raw_end_left.Valid ∧
  relay_second_miss_before_raw_end_right.Valid ∧
  relay_second_miss_no_refire_from_tail_left.Valid ∧
  relay_second_miss_no_refire_from_tail_right.Valid ∧
  relay_transient_charge_excess.Valid ∧
  relay_high_transient_root_positive_coefficient_left.Valid ∧
  relay_high_transient_root_positive_coefficient_right.Valid ∧
  relay_high_transient_root_increasing_left.Valid ∧
  relay_high_transient_root_increasing_right.Valid ∧
  relay_high_transient_root_lower_sign_left.Valid ∧
  relay_high_transient_root_lower_sign_right.Valid ∧
  relay_high_transient_root_upper_sign_left.Valid ∧
  relay_high_transient_root_upper_sign_right.Valid ∧
  relay_high_transient_root_MARK_precedes_fire_left.Valid ∧
  relay_high_transient_root_MARK_precedes_fire_right.Valid ∧
  relay_high_transient_root_fire_precedes_ERROR_left.Valid ∧
  relay_high_transient_root_fire_precedes_ERROR_right.Valid ∧
  relay_high_transient_root_ERROR_entirely_protected_left.Valid ∧
  relay_high_transient_root_ERROR_entirely_protected_right.Valid ∧
  relay_transient_return_before_next_input_left.Valid ∧
  relay_transient_return_before_next_input_right.Valid ∧
  output_first_new_slow_lower_left.Valid ∧
  output_first_new_slow_lower_right.Valid ∧
  output_first_new_slow_upper_left.Valid ∧
  output_first_new_slow_upper_right.Valid ∧
  output_second_new_slow_lower_left.Valid ∧
  output_second_new_slow_lower_right.Valid ∧
  output_second_new_slow_upper_left.Valid ∧
  output_second_new_slow_upper_right.Valid ∧
  output_settling_upper_left.Valid ∧
  output_settling_upper_right.Valid ∧
  leaf_weak_0_increasing_left.Valid ∧
  leaf_weak_0_increasing_right.Valid ∧
  leaf_weak_0_no_fire_left.Valid ∧
  leaf_weak_0_no_fire_right.Valid ∧
  leaf_weak_1_increasing_left.Valid ∧
  leaf_weak_1_increasing_right.Valid ∧
  leaf_weak_1_no_fire_left.Valid ∧
  leaf_weak_1_no_fire_right.Valid ∧
  leaf_weak_2_increasing_left.Valid ∧
  leaf_weak_2_increasing_right.Valid ∧
  leaf_weak_2_no_fire_left.Valid ∧
  leaf_weak_2_no_fire_right.Valid ∧
  leaf_first_firing_excess.Valid ∧
  leaf_first_root_positive_coefficient_left.Valid ∧
  leaf_first_root_positive_coefficient_right.Valid ∧
  leaf_first_root_increasing_left.Valid ∧
  leaf_first_root_increasing_right.Valid ∧
  leaf_first_root_lower_sign_left.Valid ∧
  leaf_first_root_lower_sign_right.Valid ∧
  leaf_first_root_upper_sign_left.Valid ∧
  leaf_first_root_upper_sign_right.Valid ∧
  leaf_first_root_MARK_precedes_fire_left.Valid ∧
  leaf_first_root_MARK_precedes_fire_right.Valid ∧
  leaf_first_root_fire_precedes_ERROR_left.Valid ∧
  leaf_first_root_fire_precedes_ERROR_right.Valid ∧
  leaf_first_root_ERROR_entirely_protected_left.Valid ∧
  leaf_first_root_ERROR_entirely_protected_right.Valid ∧
  leaf_first_miss_past_FAST_left.Valid ∧
  leaf_first_miss_past_FAST_right.Valid ∧
  leaf_first_miss_still_in_SLOW_left.Valid ∧
  leaf_first_miss_still_in_SLOW_right.Valid ∧
  leaf_first_miss_return.Valid ∧
  leaf_first_miss_entire_MARK_protected_left.Valid ∧
  leaf_first_miss_entire_MARK_protected_right.Valid ∧
  leaf_first_miss_ready_before_following_input_left.Valid ∧
  leaf_first_miss_ready_before_following_input_right.Valid ∧
  leaf_first_miss_entire_ERROR_protected_left.Valid ∧
  leaf_first_miss_entire_ERROR_protected_right.Valid ∧
  leaf_first_output_gap_lower_left.Valid ∧
  leaf_first_output_gap_lower_right.Valid ∧
  leaf_first_output_gap_upper_left.Valid ∧
  leaf_first_output_gap_upper_right.Valid ∧
  preparation_last_return_before_fast_start_left.Valid ∧
  preparation_last_return_before_fast_start_right.Valid ∧
  horizon_cell_latency_left.Valid ∧
  horizon_cell_latency_right.Valid ∧
  horizon_hop_budget_left.Valid ∧
  horizon_hop_budget_right.Valid ∧
  horizon_last_return_budget_left.Valid ∧
  horizon_last_return_budget_right.Valid ∧
  probe_before_next_raw_entirely_protected_left.Valid ∧
  probe_before_next_raw_entirely_protected_right.Valid ∧
  probe_before_ready_for_third_left.Valid ∧
  probe_before_ready_for_third_right.Valid ∧
  probe_after_ready_for_every_next_left.Valid ∧
  probe_after_ready_for_every_next_right.Valid ∧
  probe_leaf_before_flow_increases_left.Valid ∧
  probe_leaf_before_flow_increases_right.Valid ∧
  probe_leaf_before_never_fires_left.Valid ∧
  probe_leaf_before_never_fires_right.Valid
theorem all_bounds_valid : AllBoundsValid := by
  exact ⟨aux_birth_below_threshold_left_valid, aux_birth_below_threshold_right_valid, aux_root_lower_left_valid, aux_root_lower_right_valid, aux_root_upper_left_valid, aux_root_upper_right_valid, aux_root_strict_left_valid, aux_root_strict_right_valid, aux_finish_after_raw_left_valid, aux_finish_after_raw_right_valid, aux_finish_before_fastest_next_input_left_valid, aux_finish_before_fastest_next_input_right_valid, energy_reserve_invariant_left_valid, energy_reserve_invariant_right_valid, caps_final_gain_left_valid, caps_final_gain_right_valid, caps_final_recovery_left_valid, caps_final_recovery_right_valid, jitter_budget_valid, prepared_recovery_valid, final_recovery_valid, prepared_gain_valid, final_gain_valid, aux_mark_end_valid, aux_ERROR_start_valid, aux_finish_valid, MARK_integral_deficit_valid, relay_low_root_positive_coefficient_left_valid, relay_low_root_positive_coefficient_right_valid, relay_low_root_increasing_left_valid, relay_low_root_increasing_right_valid, relay_low_root_lower_sign_left_valid, relay_low_root_lower_sign_right_valid, relay_low_root_upper_sign_left_valid, relay_low_root_upper_sign_right_valid, relay_low_root_MARK_precedes_fire_left_valid, relay_low_root_MARK_precedes_fire_right_valid, relay_low_root_fire_precedes_ERROR_left_valid, relay_low_root_fire_precedes_ERROR_right_valid, relay_low_root_ERROR_entirely_protected_left_valid, relay_low_root_ERROR_entirely_protected_right_valid, relay_low_root_at_b2_ERROR_entirely_protected_left_valid, relay_low_root_at_b2_ERROR_entirely_protected_right_valid, relay_high_rest_root_positive_coefficient_left_valid, relay_high_rest_root_positive_coefficient_right_valid, relay_high_rest_root_increasing_left_valid, relay_high_rest_root_increasing_right_valid, relay_high_rest_root_lower_sign_left_valid, relay_high_rest_root_lower_sign_right_valid, relay_high_rest_root_upper_sign_left_valid, relay_high_rest_root_upper_sign_right_valid, relay_high_rest_root_MARK_precedes_fire_left_valid, relay_high_rest_root_MARK_precedes_fire_right_valid, relay_high_rest_root_fire_precedes_ERROR_left_valid, relay_high_rest_root_fire_precedes_ERROR_right_valid, relay_high_rest_root_ERROR_entirely_protected_left_valid, relay_high_rest_root_ERROR_entirely_protected_right_valid, slow_prefix_ready_before_every_input_left_valid, slow_prefix_ready_before_every_input_right_valid, steady_tail_ready_before_every_input_left_valid, steady_tail_ready_before_every_input_right_valid, h_increasing_through_raw_end_left_valid, h_increasing_through_raw_end_right_valid, relay_first_miss_past_FAST_left_valid, relay_first_miss_past_FAST_right_valid, relay_first_miss_still_in_SLOW_left_valid, relay_first_miss_still_in_SLOW_right_valid, relay_first_miss_return_valid, relay_first_miss_entire_MARK_protected_left_valid, relay_first_miss_entire_MARK_protected_right_valid, relay_first_miss_ready_before_following_input_left_valid, relay_first_miss_ready_before_following_input_right_valid, relay_first_miss_entire_ERROR_protected_left_valid, relay_first_miss_entire_ERROR_protected_right_valid, relay_second_miss_past_FAST_left_valid, relay_second_miss_past_FAST_right_valid, relay_second_miss_still_in_SLOW_left_valid, relay_second_miss_still_in_SLOW_right_valid, relay_second_miss_return_valid, relay_second_miss_entire_MARK_protected_left_valid, relay_second_miss_entire_MARK_protected_right_valid, relay_second_miss_ready_before_following_input_left_valid, relay_second_miss_ready_before_following_input_right_valid, relay_second_miss_ready_before_ERROR_left_valid, relay_second_miss_ready_before_ERROR_right_valid, relay_second_miss_before_raw_end_left_valid, relay_second_miss_before_raw_end_right_valid, relay_second_miss_no_refire_from_tail_left_valid, relay_second_miss_no_refire_from_tail_right_valid, relay_transient_charge_excess_valid, relay_high_transient_root_positive_coefficient_left_valid, relay_high_transient_root_positive_coefficient_right_valid, relay_high_transient_root_increasing_left_valid, relay_high_transient_root_increasing_right_valid, relay_high_transient_root_lower_sign_left_valid, relay_high_transient_root_lower_sign_right_valid, relay_high_transient_root_upper_sign_left_valid, relay_high_transient_root_upper_sign_right_valid, relay_high_transient_root_MARK_precedes_fire_left_valid, relay_high_transient_root_MARK_precedes_fire_right_valid, relay_high_transient_root_fire_precedes_ERROR_left_valid, relay_high_transient_root_fire_precedes_ERROR_right_valid, relay_high_transient_root_ERROR_entirely_protected_left_valid, relay_high_transient_root_ERROR_entirely_protected_right_valid, relay_transient_return_before_next_input_left_valid, relay_transient_return_before_next_input_right_valid, output_first_new_slow_lower_left_valid, output_first_new_slow_lower_right_valid, output_first_new_slow_upper_left_valid, output_first_new_slow_upper_right_valid, output_second_new_slow_lower_left_valid, output_second_new_slow_lower_right_valid, output_second_new_slow_upper_left_valid, output_second_new_slow_upper_right_valid, output_settling_upper_left_valid, output_settling_upper_right_valid, leaf_weak_0_increasing_left_valid, leaf_weak_0_increasing_right_valid, leaf_weak_0_no_fire_left_valid, leaf_weak_0_no_fire_right_valid, leaf_weak_1_increasing_left_valid, leaf_weak_1_increasing_right_valid, leaf_weak_1_no_fire_left_valid, leaf_weak_1_no_fire_right_valid, leaf_weak_2_increasing_left_valid, leaf_weak_2_increasing_right_valid, leaf_weak_2_no_fire_left_valid, leaf_weak_2_no_fire_right_valid, leaf_first_firing_excess_valid, leaf_first_root_positive_coefficient_left_valid, leaf_first_root_positive_coefficient_right_valid, leaf_first_root_increasing_left_valid, leaf_first_root_increasing_right_valid, leaf_first_root_lower_sign_left_valid, leaf_first_root_lower_sign_right_valid, leaf_first_root_upper_sign_left_valid, leaf_first_root_upper_sign_right_valid, leaf_first_root_MARK_precedes_fire_left_valid, leaf_first_root_MARK_precedes_fire_right_valid, leaf_first_root_fire_precedes_ERROR_left_valid, leaf_first_root_fire_precedes_ERROR_right_valid, leaf_first_root_ERROR_entirely_protected_left_valid, leaf_first_root_ERROR_entirely_protected_right_valid, leaf_first_miss_past_FAST_left_valid, leaf_first_miss_past_FAST_right_valid, leaf_first_miss_still_in_SLOW_left_valid, leaf_first_miss_still_in_SLOW_right_valid, leaf_first_miss_return_valid, leaf_first_miss_entire_MARK_protected_left_valid, leaf_first_miss_entire_MARK_protected_right_valid, leaf_first_miss_ready_before_following_input_left_valid, leaf_first_miss_ready_before_following_input_right_valid, leaf_first_miss_entire_ERROR_protected_left_valid, leaf_first_miss_entire_ERROR_protected_right_valid, leaf_first_output_gap_lower_left_valid, leaf_first_output_gap_lower_right_valid, leaf_first_output_gap_upper_left_valid, leaf_first_output_gap_upper_right_valid, preparation_last_return_before_fast_start_left_valid, preparation_last_return_before_fast_start_right_valid, horizon_cell_latency_left_valid, horizon_cell_latency_right_valid, horizon_hop_budget_left_valid, horizon_hop_budget_right_valid, horizon_last_return_budget_left_valid, horizon_last_return_budget_right_valid, probe_before_next_raw_entirely_protected_left_valid, probe_before_next_raw_entirely_protected_right_valid, probe_before_ready_for_third_left_valid, probe_before_ready_for_third_right_valid, probe_after_ready_for_every_next_left_valid, probe_after_ready_for_every_next_right_valid, probe_leaf_before_flow_increases_left_valid, probe_leaf_before_flow_increases_right_valid, probe_leaf_before_never_fires_left_valid, probe_leaf_before_never_fires_right_valid⟩

end KernelR.Certificates.Composition003
#print axioms KernelR.Certificates.Composition003.obligations_verified
#print axioms KernelR.Certificates.Composition003.all_bounds_valid
