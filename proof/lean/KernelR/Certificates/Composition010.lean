import KernelR.Intervals

/-! Generated exact endpoint checks. Analytic enclosure soundness is NOT asserted. -/
namespace KernelR.Certificates.Composition010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def aux_birth_below_threshold_left : RationalBox := ⟨(2499 / 100000 : ℚ), (2501 / 100000 : ℚ)⟩
theorem aux_birth_below_threshold_left_valid : aux_birth_below_threshold_left.Valid := by norm_num [RationalBox.Valid, aux_birth_below_threshold_left]

def aux_birth_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_birth_below_threshold_right_valid : aux_birth_below_threshold_right.Valid := by norm_num [RationalBox.Valid, aux_birth_below_threshold_right]

def aux_root_lower_left : RationalBox := ⟨(857777700395999170890784025356980226903 / 1250000000000000000000000000000000000000 : ℚ), (4165912371719864739736113183069689690047 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_lower_left_valid : aux_root_lower_left.Valid := by norm_num [RationalBox.Valid, aux_root_lower_left]

def aux_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_root_lower_right_valid : aux_root_lower_right.Valid := by norm_num [RationalBox.Valid, aux_root_lower_right]

def aux_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_root_upper_left_valid : aux_root_upper_left.Valid := by norm_num [RationalBox.Valid, aux_root_upper_left]

def aux_root_upper_right : RationalBox := ⟨(13289056706323197692444281225825371354033 / 10000000000000000000000000000000000000000 : ℚ), (8093421888524132263456113558930151776937 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_upper_right_valid : aux_root_upper_right.Valid := by norm_num [RationalBox.Valid, aux_root_upper_right]

def aux_root_strict_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem aux_root_strict_left_valid : aux_root_strict_left.Valid := by norm_num [RationalBox.Valid, aux_root_strict_left]

def aux_root_strict_right : RationalBox := ⟨(104652753909468400451498982066330214586733 / 2500000000000000000000000000000000000000 : ℚ), (68880481100858260141341200869705380694399 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_strict_right_valid : aux_root_strict_right.Valid := by norm_num [RationalBox.Valid, aux_root_strict_right]

def aux_finish_after_raw_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_finish_after_raw_left_valid : aux_finish_after_raw_left.Valid := by norm_num [RationalBox.Valid, aux_finish_after_raw_left]

def aux_finish_after_raw_right : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (5665909090909090909090909090909090909091 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_after_raw_right_valid : aux_finish_after_raw_right.Valid := by norm_num [RationalBox.Valid, aux_finish_after_raw_right]

def aux_finish_before_fastest_next_input_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_before_fastest_next_input_left_valid : aux_finish_before_fastest_next_input_left.Valid := by norm_num [RationalBox.Valid, aux_finish_before_fastest_next_input_left]

def aux_finish_before_fastest_next_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem aux_finish_before_fastest_next_input_right_valid : aux_finish_before_fastest_next_input_right.Valid := by norm_num [RationalBox.Valid, aux_finish_before_fastest_next_input_right]

def energy_reserve_invariant_left : RationalBox := ⟨(10573936830325210453707713866907429323159 / 40000000000000000000000000000000000000 : ℚ), (2643484207581302613426928466726857330789751 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem energy_reserve_invariant_left_valid : energy_reserve_invariant_left.Valid := by norm_num [RationalBox.Valid, energy_reserve_invariant_left]

def energy_reserve_invariant_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem energy_reserve_invariant_right_valid : energy_reserve_invariant_right.Valid := by norm_num [RationalBox.Valid, energy_reserve_invariant_right]

def caps_final_gain_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem caps_final_gain_left_valid : caps_final_gain_left.Valid := by norm_num [RationalBox.Valid, caps_final_gain_left]

def caps_final_gain_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
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

def aux_mark_end : RationalBox := ⟨(331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_mark_end_valid : aux_mark_end.Valid := by norm_num [RationalBox.Valid, aux_mark_end]

def aux_ERROR_start : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (12300000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_ERROR_start_valid : aux_ERROR_start.Valid := by norm_num [RationalBox.Valid, aux_ERROR_start]

def aux_finish : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_valid : aux_finish.Valid := by norm_num [RationalBox.Valid, aux_finish]

def MARK_integral_deficit : RationalBox := ⟨(23753093049537268852600859055970767301 / 10000000000000000000000000000000000000000 : ℚ), (20349112419161664298811636089759913351 / 5000000000000000000000000000000000000000 : ℚ)⟩
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

def relay_low_root_MARK_precedes_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_MARK_precedes_fire_left_valid : relay_low_root_MARK_precedes_fire_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_MARK_precedes_fire_left]

def relay_low_root_MARK_precedes_fire_right : RationalBox := ⟨(13 / 20 : ℚ), (13 / 20 : ℚ)⟩
theorem relay_low_root_MARK_precedes_fire_right_valid : relay_low_root_MARK_precedes_fire_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_MARK_precedes_fire_right]

def relay_low_root_fire_precedes_ERROR_left : RationalBox := ⟨(33 / 50 : ℚ), (33 / 50 : ℚ)⟩
theorem relay_low_root_fire_precedes_ERROR_left_valid : relay_low_root_fire_precedes_ERROR_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_fire_precedes_ERROR_left]

def relay_low_root_fire_precedes_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_fire_precedes_ERROR_right_valid : relay_low_root_fire_precedes_ERROR_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_fire_precedes_ERROR_right]

def relay_low_root_ERROR_entirely_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_ERROR_entirely_protected_left_valid : relay_low_root_ERROR_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, relay_low_root_ERROR_entirely_protected_left]

def relay_low_root_ERROR_entirely_protected_right : RationalBox := ⟨(8425276594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67407868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_low_root_ERROR_entirely_protected_right_valid : relay_low_root_ERROR_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, relay_low_root_ERROR_entirely_protected_right]

def relay_low_root_at_b2_ERROR_entirely_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

def relay_high_rest_root_MARK_precedes_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_MARK_precedes_fire_left_valid : relay_high_rest_root_MARK_precedes_fire_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_MARK_precedes_fire_left]

def relay_high_rest_root_MARK_precedes_fire_right : RationalBox := ⟨(6 / 25 : ℚ), (6 / 25 : ℚ)⟩
theorem relay_high_rest_root_MARK_precedes_fire_right_valid : relay_high_rest_root_MARK_precedes_fire_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_MARK_precedes_fire_right]

def relay_high_rest_root_fire_precedes_ERROR_left : RationalBox := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem relay_high_rest_root_fire_precedes_ERROR_left_valid : relay_high_rest_root_fire_precedes_ERROR_left.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_fire_precedes_ERROR_left]

def relay_high_rest_root_fire_precedes_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_rest_root_fire_precedes_ERROR_right_valid : relay_high_rest_root_fire_precedes_ERROR_right.Valid := by norm_num [RationalBox.Valid, relay_high_rest_root_fire_precedes_ERROR_right]

def relay_high_rest_root_ERROR_entirely_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

def relay_first_miss_return : RationalBox := ⟨(15129407563269482949494207266655053325961 / 10000000000000000000000000000000000000000 : ℚ), (2469646033599358004050544389915546332549 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_return_valid : relay_first_miss_return.Valid := by norm_num [RationalBox.Valid, relay_first_miss_return]

def relay_first_miss_entire_MARK_protected_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_entire_MARK_protected_left_valid : relay_first_miss_entire_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, relay_first_miss_entire_MARK_protected_left]

def relay_first_miss_entire_MARK_protected_right : RationalBox := ⟨(15129407563269482949494207266655053325961 / 10000000000000000000000000000000000000000 : ℚ), (7564703781634741474747103633327526662981 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_entire_MARK_protected_right_valid : relay_first_miss_entire_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, relay_first_miss_entire_MARK_protected_right]

def relay_first_miss_ready_before_following_input_left : RationalBox := ⟨(19757168268794864032404355119324370660391 / 10000000000000000000000000000000000000000 : ℚ), (2469646033599358004050544389915546332549 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_ready_before_following_input_left_valid : relay_first_miss_ready_before_following_input_left.Valid := by norm_num [RationalBox.Valid, relay_first_miss_ready_before_following_input_left]

def relay_first_miss_ready_before_following_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem relay_first_miss_ready_before_following_input_right_valid : relay_first_miss_ready_before_following_input_right.Valid := by norm_num [RationalBox.Valid, relay_first_miss_ready_before_following_input_right]

def relay_first_miss_entire_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_entire_ERROR_protected_left_valid : relay_first_miss_entire_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, relay_first_miss_entire_ERROR_protected_left]

def relay_first_miss_entire_ERROR_protected_right : RationalBox := ⟨(15129407563269482949494207266655053325961 / 10000000000000000000000000000000000000000 : ℚ), (7564703781634741474747103633327526662981 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_first_miss_entire_ERROR_protected_right_valid : relay_first_miss_entire_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, relay_first_miss_entire_ERROR_protected_right]

def relay_second_miss_past_FAST_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_second_miss_past_FAST_left_valid : relay_second_miss_past_FAST_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_past_FAST_left]

def relay_second_miss_past_FAST_right : RationalBox := ⟨(51 / 25 : ℚ), (53 / 20 : ℚ)⟩
theorem relay_second_miss_past_FAST_right_valid : relay_second_miss_past_FAST_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_past_FAST_right]

def relay_second_miss_still_in_SLOW_left : RationalBox := ⟨(1427949 / 2500000 : ℚ), (1484053 / 2000000 : ℚ)⟩
theorem relay_second_miss_still_in_SLOW_left_valid : relay_second_miss_still_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_still_in_SLOW_left]

def relay_second_miss_still_in_SLOW_right : RationalBox := ⟨(9162907318741550651835272117680110714501 / 10000000000000000000000000000000000000000 : ℚ), (4581453659370775325917636058840055357251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_still_in_SLOW_right_valid : relay_second_miss_still_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_still_in_SLOW_right]

def relay_second_miss_return : RationalBox := ⟨(4648286655064571776237133172116737669541 / 10000000000000000000000000000000000000000 : ℚ), (9189214304533998211618451511512488594971 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_return_valid : relay_second_miss_return.Valid := by norm_num [RationalBox.Valid, relay_second_miss_return]

def relay_second_miss_entire_MARK_protected_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_entire_MARK_protected_left_valid : relay_second_miss_entire_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_entire_MARK_protected_left]

def relay_second_miss_entire_MARK_protected_right : RationalBox := ⟨(4648286655064571776237133172116737669541 / 10000000000000000000000000000000000000000 : ℚ), (2324143327532285888118566586058368834771 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_entire_MARK_protected_right_valid : relay_second_miss_entire_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_entire_MARK_protected_right]

def relay_second_miss_ready_before_following_input_left : RationalBox := ⟨(918921430453399821161845151151248859497 / 1000000000000000000000000000000000000000 : ℚ), (9189214304533998211618451511512488594971 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_ready_before_following_input_left_valid : relay_second_miss_ready_before_following_input_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_ready_before_following_input_left]

def relay_second_miss_ready_before_following_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem relay_second_miss_ready_before_following_input_right_valid : relay_second_miss_ready_before_following_input_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_ready_before_following_input_right]

def relay_second_miss_ready_before_ERROR_left : RationalBox := ⟨(918921430453399821161845151151248859497 / 1000000000000000000000000000000000000000 : ℚ), (9189214304533998211618451511512488594971 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_ready_before_ERROR_left_valid : relay_second_miss_ready_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_ready_before_ERROR_left]

def relay_second_miss_ready_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_ready_before_ERROR_right_valid : relay_second_miss_ready_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_ready_before_ERROR_right]

def relay_second_miss_before_raw_end_left : RationalBox := ⟨(918921430453399821161845151151248859497 / 1000000000000000000000000000000000000000 : ℚ), (9189214304533998211618451511512488594971 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_before_raw_end_left_valid : relay_second_miss_before_raw_end_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_before_raw_end_left]

def relay_second_miss_before_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_second_miss_before_raw_end_right_valid : relay_second_miss_before_raw_end_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_before_raw_end_right]

def relay_second_miss_no_refire_from_tail_left : RationalBox := ⟨(5323821882718414442980678837981667436613 / 10000000000000000000000000000000000000000 : ℚ), (2661910941359207221490339418990833718307 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_second_miss_no_refire_from_tail_left_valid : relay_second_miss_no_refire_from_tail_left.Valid := by norm_num [RationalBox.Valid, relay_second_miss_no_refire_from_tail_left]

def relay_second_miss_no_refire_from_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_second_miss_no_refire_from_tail_right_valid : relay_second_miss_no_refire_from_tail_right.Valid := by norm_num [RationalBox.Valid, relay_second_miss_no_refire_from_tail_right]

def relay_transient_charge_excess : RationalBox := ⟨(0 / 1 : ℚ), (1120908711862331101286710291420534555653 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_transient_charge_excess_valid : relay_transient_charge_excess.Valid := by norm_num [RationalBox.Valid, relay_transient_charge_excess]

def relay_high_transient_root_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_high_transient_root_positive_coefficient_left_valid : relay_high_transient_root_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_positive_coefficient_left]

def relay_high_transient_root_positive_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (5284701939107574970456370570413735157897 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_positive_coefficient_right_valid : relay_high_transient_root_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_positive_coefficient_right]

def relay_high_transient_root_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem relay_high_transient_root_increasing_left_valid : relay_high_transient_root_increasing_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_increasing_left]

def relay_high_transient_root_increasing_right : RationalBox := ⟨(1899876587264047205404300551203663290833 / 2500000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_increasing_right_valid : relay_high_transient_root_increasing_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_increasing_right]

def relay_high_transient_root_lower_sign_left : RationalBox := ⟨(4301253470772651664047614877313461764851 / 5000000000000000000000000000000000000000 : ℚ), (9616899137900170803181479048228574334221 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_lower_sign_left_valid : relay_high_transient_root_lower_sign_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_lower_sign_left]

def relay_high_transient_root_lower_sign_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_high_transient_root_lower_sign_right_valid : relay_high_transient_root_lower_sign_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_lower_sign_right]

def relay_high_transient_root_upper_sign_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem relay_high_transient_root_upper_sign_left_valid : relay_high_transient_root_upper_sign_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_upper_sign_left]

def relay_high_transient_root_upper_sign_right : RationalBox := ⟨(2014413477662782087737588494001580679009 / 2000000000000000000000000000000000000000 : ℚ), (1106144729777469821807952689591751187477 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_upper_sign_right_valid : relay_high_transient_root_upper_sign_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_upper_sign_right]

def relay_high_transient_root_MARK_precedes_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_MARK_precedes_fire_left_valid : relay_high_transient_root_MARK_precedes_fire_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_MARK_precedes_fire_left]

def relay_high_transient_root_MARK_precedes_fire_right : RationalBox := ⟨(1 / 5 : ℚ), (1 / 5 : ℚ)⟩
theorem relay_high_transient_root_MARK_precedes_fire_right_valid : relay_high_transient_root_MARK_precedes_fire_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_MARK_precedes_fire_right]

def relay_high_transient_root_fire_precedes_ERROR_left : RationalBox := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem relay_high_transient_root_fire_precedes_ERROR_left_valid : relay_high_transient_root_fire_precedes_ERROR_left.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_fire_precedes_ERROR_left]

def relay_high_transient_root_fire_precedes_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem relay_high_transient_root_fire_precedes_ERROR_right_valid : relay_high_transient_root_fire_precedes_ERROR_right.Valid := by norm_num [RationalBox.Valid, relay_high_transient_root_fire_precedes_ERROR_right]

def relay_high_transient_root_ERROR_entirely_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

def leaf_weak_0_no_fire_left : RationalBox := ⟨(668245496870030414562379084115601089407 / 2500000000000000000000000000000000000000 : ℚ), (668936808320405663643604042669827175303 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_0_no_fire_left_valid : leaf_weak_0_no_fire_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_0_no_fire_left]

def leaf_weak_0_no_fire_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_weak_0_no_fire_right_valid : leaf_weak_0_no_fire_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_0_no_fire_right]

def leaf_weak_1_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_weak_1_increasing_left_valid : leaf_weak_1_increasing_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_1_increasing_left]

def leaf_weak_1_increasing_right : RationalBox := ⟨(256844130093467146168678940778312744363 / 2500000000000000000000000000000000000000 : ℚ), (370349118152897270256862943194939520681 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_1_increasing_right_valid : leaf_weak_1_increasing_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_1_increasing_right]

def leaf_weak_1_no_fire_left : RationalBox := ⟨(404837193210220878069943630299241842341 / 1000000000000000000000000000000000000000 : ℚ), (1070049566228490788020429075489819966341 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_1_no_fire_left_valid : leaf_weak_1_no_fire_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_1_no_fire_left]

def leaf_weak_1_no_fire_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_weak_1_no_fire_right_valid : leaf_weak_1_no_fire_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_1_no_fire_right]

def leaf_weak_2_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_weak_2_increasing_left_valid : leaf_weak_2_increasing_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_2_increasing_left]

def leaf_weak_2_increasing_right : RationalBox := ⟨(1810617310465845535959827520722683051457 / 10000000000000000000000000000000000000000 : ℚ), (674820090894440045079595129917914509719 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_2_increasing_right_valid : leaf_weak_2_increasing_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_2_increasing_right]

def leaf_weak_2_no_fire_left : RationalBox := ⟨(3277247904033087369540798740533573094581 / 5000000000000000000000000000000000000000 : ℚ), (350380165435082055003932934813451997389 / 500000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_weak_2_no_fire_left_valid : leaf_weak_2_no_fire_left.Valid := by norm_num [RationalBox.Valid, leaf_weak_2_no_fire_left]

def leaf_weak_2_no_fire_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_weak_2_no_fire_right_valid : leaf_weak_2_no_fire_right.Valid := by norm_num [RationalBox.Valid, leaf_weak_2_no_fire_right]

def leaf_first_firing_excess : RationalBox := ⟨(0 / 1 : ℚ), (134047748837883410233272146339481523011 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_firing_excess_valid : leaf_first_firing_excess.Valid := by norm_num [RationalBox.Valid, leaf_first_firing_excess]

def leaf_first_root_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_first_root_positive_coefficient_left_valid : leaf_first_root_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_positive_coefficient_left]

def leaf_first_root_positive_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (92901152871933260062691481577848179059 / 62500000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_positive_coefficient_right_valid : leaf_first_root_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_positive_coefficient_right]

def leaf_first_root_increasing_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem leaf_first_root_increasing_left_valid : leaf_first_root_increasing_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_increasing_left]

def leaf_first_root_increasing_right : RationalBox := ⟨(822713079377059329662708068977931970193 / 2500000000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_increasing_right_valid : leaf_first_root_increasing_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_increasing_right]

def leaf_first_root_lower_sign_left : RationalBox := ⟨(3968669443516656660866724072139110506223 / 5000000000000000000000000000000000000000 : ℚ), (9034967778743015535151913758989714411249 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_lower_sign_left_valid : leaf_first_root_lower_sign_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_lower_sign_left]

def leaf_first_root_lower_sign_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_first_root_lower_sign_right_valid : leaf_first_root_lower_sign_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_lower_sign_right]

def leaf_first_root_upper_sign_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem leaf_first_root_upper_sign_left_valid : leaf_first_root_upper_sign_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_upper_sign_left]

def leaf_first_root_upper_sign_right : RationalBox := ⟨(1003820576896766608189493188295273519847 / 1000000000000000000000000000000000000000 : ℚ), (11002087615417461477978865155212745211639 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_upper_sign_right_valid : leaf_first_root_upper_sign_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_upper_sign_right]

def leaf_first_root_MARK_precedes_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_MARK_precedes_fire_left_valid : leaf_first_root_MARK_precedes_fire_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_MARK_precedes_fire_left]

def leaf_first_root_MARK_precedes_fire_right : RationalBox := ⟨(2 / 5 : ℚ), (2 / 5 : ℚ)⟩
theorem leaf_first_root_MARK_precedes_fire_right_valid : leaf_first_root_MARK_precedes_fire_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_MARK_precedes_fire_right]

def leaf_first_root_fire_precedes_ERROR_left : RationalBox := ⟨(33 / 50 : ℚ), (33 / 50 : ℚ)⟩
theorem leaf_first_root_fire_precedes_ERROR_left_valid : leaf_first_root_fire_precedes_ERROR_left.Valid := by norm_num [RationalBox.Valid, leaf_first_root_fire_precedes_ERROR_left]

def leaf_first_root_fire_precedes_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_root_fire_precedes_ERROR_right_valid : leaf_first_root_fire_precedes_ERROR_right.Valid := by norm_num [RationalBox.Valid, leaf_first_root_fire_precedes_ERROR_right]

def leaf_first_root_ERROR_entirely_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

def leaf_first_miss_return : RationalBox := ⟨(1005857025595310864051255530323935190217 / 625000000000000000000000000000000000000 : ℚ), (17828635106896224795288743847493233834077 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_return_valid : leaf_first_miss_return.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_return]

def leaf_first_miss_entire_MARK_protected_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_entire_MARK_protected_left_valid : leaf_first_miss_entire_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_entire_MARK_protected_left]

def leaf_first_miss_entire_MARK_protected_right : RationalBox := ⟨(1005857025595310864051255530323935190217 / 625000000000000000000000000000000000000 : ℚ), (16093712409524973824820088485182963043473 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_entire_MARK_protected_right_valid : leaf_first_miss_entire_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_entire_MARK_protected_right]

def leaf_first_miss_ready_before_following_input_left : RationalBox := ⟨(4457158776724056198822185961873308458519 / 2500000000000000000000000000000000000000 : ℚ), (17828635106896224795288743847493233834077 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_ready_before_following_input_left_valid : leaf_first_miss_ready_before_following_input_left.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_ready_before_following_input_left]

def leaf_first_miss_ready_before_following_input_right : RationalBox := ⟨(37 / 10 : ℚ), (37 / 10 : ℚ)⟩
theorem leaf_first_miss_ready_before_following_input_right_valid : leaf_first_miss_ready_before_following_input_right.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_ready_before_following_input_right]

def leaf_first_miss_entire_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem leaf_first_miss_entire_ERROR_protected_left_valid : leaf_first_miss_entire_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, leaf_first_miss_entire_ERROR_protected_left]

def leaf_first_miss_entire_ERROR_protected_right : RationalBox := ⟨(1005857025595310864051255530323935190217 / 625000000000000000000000000000000000000 : ℚ), (16093712409524973824820088485182963043473 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

end KernelR.Certificates.Composition010
#print axioms KernelR.Certificates.Composition010.obligations_verified
#print axioms KernelR.Certificates.Composition010.all_bounds_valid
