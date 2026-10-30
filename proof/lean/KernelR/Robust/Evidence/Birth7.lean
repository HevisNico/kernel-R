import KernelR.Intervals

/-! Generated rational endpoint checks; analytic enclosure membership is separate. -/
namespace KernelR.Robust.Evidence.Birth7
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def local_epsilon : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_epsilon_valid : local_epsilon.Valid := by norm_num [RationalBox.Valid, local_epsilon]

def local_nu : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem local_nu_valid : local_nu.Valid := by norm_num [RationalBox.Valid, local_nu]

def local_alpha : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem local_alpha_valid : local_alpha.Valid := by norm_num [RationalBox.Valid, local_alpha]

def local_section_excess : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_section_excess_valid : local_section_excess.Valid := by norm_num [RationalBox.Valid, local_section_excess]

def local_a : RationalBox := ⟨(1386294361119890618834464242916353136151 / 1000000000000000000000000000000000000000 : ℚ), (13862943611198906188344642429163531361511 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_a_valid : local_a.Valid := by norm_num [RationalBox.Valid, local_a]

def local_kappa : RationalBox := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem local_kappa_valid : local_kappa.Valid := by norm_num [RationalBox.Valid, local_kappa]

def local_cap : RationalBox := ⟨(18 / 5 : ℚ), (22 / 5 : ℚ)⟩
theorem local_cap_valid : local_cap.Valid := by norm_num [RationalBox.Valid, local_cap]

def local_Lm : RationalBox := ⟨(10041459809139439009483279063942552651857 / 1000000000000000000000000000000000000000 : ℚ), (122728953222815365671462299670408976856031 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_Lm_valid : local_Lm.Valid := by norm_num [RationalBox.Valid, local_Lm]

def local_Ls : RationalBox := ⟨(17655635731243889956854025735255440884941 / 10000000000000000000000000000000000000000 : ℚ), (5394777584546744153483174530216940270399 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_Ls_valid : local_Ls.Valid := by norm_num [RationalBox.Valid, local_Ls]

def local_Le : RationalBox := ⟨(4158883083359671856503392728749059408453 / 500000000000000000000000000000000000000 : ℚ), (101661586482125312047860711147199229984407 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_Le_valid : local_Le.Valid := by norm_num [RationalBox.Valid, local_Le]

def local_M : RationalBox := ⟨(12900544781726378166238323015172510050413 / 400000000000000000000000000000000000000 : ℚ), (394183312774972666190615425463604473762621 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_M_valid : local_M.Valid := by norm_num [RationalBox.Valid, local_M]

def local_b : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem local_b_valid : local_b.Valid := by norm_num [RationalBox.Valid, local_b]

def local_h_increases_through_raw_window_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_h_increases_through_raw_window_left_valid : local_h_increases_through_raw_window_left.Valid := by norm_num [RationalBox.Valid, local_h_increases_through_raw_window_left]

def local_h_increases_through_raw_window_right : RationalBox := ⟨(5753062894644089006539049196938423108761 / 5000000000000000000000000000000000000000 : ℚ), (11506125789288178013078098393876846217523 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_h_increases_through_raw_window_right_valid : local_h_increases_through_raw_window_right.Valid := by norm_num [RationalBox.Valid, local_h_increases_through_raw_window_right]

def local_aux_rest_deviation : RationalBox := ⟨(1 / 100000 : ℚ), (1 / 100000 : ℚ)⟩
theorem local_aux_rest_deviation_valid : local_aux_rest_deviation.Valid := by norm_num [RationalBox.Valid, local_aux_rest_deviation]

def local_aux_rest_below_threshold_left : RationalBox := ⟨(2501 / 100000 : ℚ), (2501 / 100000 : ℚ)⟩
theorem local_aux_rest_below_threshold_left_valid : local_aux_rest_below_threshold_left.Valid := by norm_num [RationalBox.Valid, local_aux_rest_below_threshold_left]

def local_aux_rest_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_rest_below_threshold_right_valid : local_aux_rest_below_threshold_right.Valid := by norm_num [RationalBox.Valid, local_aux_rest_below_threshold_right]

def local_aux_below_threshold_until_0_015_left : RationalBox := ⟨(333273019625369902625166968517894866297 / 400000000000000000000000000000000000000 : ℚ), (4165912745317123782814587106473685828713 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_below_threshold_until_0_015_left_valid : local_aux_below_threshold_until_0_015_left.Valid := by norm_num [RationalBox.Valid, local_aux_below_threshold_until_0_015_left]

def local_aux_below_threshold_until_0_015_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_below_threshold_until_0_015_right_valid : local_aux_below_threshold_until_0_015_right.Valid := by norm_num [RationalBox.Valid, local_aux_below_threshold_until_0_015_right]

def local_aux_above_threshold_by_0_03_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_above_threshold_by_0_03_left_valid : local_aux_above_threshold_by_0_03_left.Valid := by norm_num [RationalBox.Valid, local_aux_above_threshold_by_0_03_left]

def local_aux_above_threshold_by_0_03_right : RationalBox := ⟨(6644527608758578999355214377329276854279 / 5000000000000000000000000000000000000000 : ℚ), (13289055217517157998710428754658553708559 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_above_threshold_by_0_03_right_valid : local_aux_above_threshold_by_0_03_right.Valid := by norm_num [RationalBox.Valid, local_aux_above_threshold_by_0_03_right]

def local_decay_1_0_8_dominates_noise_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem local_decay_1_0_8_dominates_noise_left_valid : local_decay_1_0_8_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_8_dominates_noise_left]

def local_decay_1_0_8_dominates_noise_right : RationalBox := ⟨(4 / 5 : ℚ), (4 / 5 : ℚ)⟩
theorem local_decay_1_0_8_dominates_noise_right_valid : local_decay_1_0_8_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_8_dominates_noise_right]

def local_decay_0_8_0_1_dominates_noise_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem local_decay_0_8_0_1_dominates_noise_left_valid : local_decay_0_8_0_1_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_8_0_1_dominates_noise_left]

def local_decay_0_8_0_1_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_decay_0_8_0_1_dominates_noise_right_valid : local_decay_0_8_0_1_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_8_0_1_dominates_noise_right]

def local_decay_0_1_0_025_dominates_noise_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem local_decay_0_1_0_025_dominates_noise_left_valid : local_decay_0_1_0_025_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_1_0_025_dominates_noise_left]

def local_decay_0_1_0_025_dominates_noise_right : RationalBox := ⟨(1 / 40 : ℚ), (1 / 40 : ℚ)⟩
theorem local_decay_0_1_0_025_dominates_noise_right_valid : local_decay_0_1_0_025_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_1_0_025_dominates_noise_right]

def local_mark_duration : RationalBox := ⟨(181818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (222222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_duration_valid : local_mark_duration.Valid := by norm_num [RationalBox.Valid, local_mark_duration]

def local_silent_duration : RationalBox := ⟨(2409090909090909090909090909090909090909 / 2500000000000000000000000000000000000000 : ℚ), (5888888888888888888888888888888888888889 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_duration_valid : local_silent_duration.Valid := by norm_num [RationalBox.Valid, local_silent_duration]

def local_error_duration : RationalBox := ⟨(1363636363636363636363636363636363636363 / 10000000000000000000000000000000000000000 : ℚ), (1666666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_duration_valid : local_error_duration.Valid := by norm_num [RationalBox.Valid, local_error_duration]

def local_mark_end : RationalBox := ⟨(331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_end_valid : local_mark_end.Valid := by norm_num [RationalBox.Valid, local_mark_end]

def local_error_start : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (12300000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_start_valid : local_error_start.Valid := by norm_num [RationalBox.Valid, local_error_start]

def local_aux_finish : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_finish_valid : local_aux_finish.Valid := by norm_num [RationalBox.Valid, local_aux_finish]

def local_gain_log_dose : RationalBox := ⟨(3 / 5 : ℚ), (3 / 5 : ℚ)⟩
theorem local_gain_log_dose_valid : local_gain_log_dose.Valid := by norm_num [RationalBox.Valid, local_gain_log_dose]

def local_initial_gain : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_initial_gain_valid : local_initial_gain.Valid := by norm_num [RationalBox.Valid, local_initial_gain]

def local_learned_gain : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_gain_valid : local_learned_gain.Valid := by norm_num [RationalBox.Valid, local_learned_gain]

def local_decay_1_0_25_dominates_noise_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem local_decay_1_0_25_dominates_noise_left_valid : local_decay_1_0_25_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_25_dominates_noise_left]

def local_decay_1_0_25_dominates_noise_right : RationalBox := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem local_decay_1_0_25_dominates_noise_right_valid : local_decay_1_0_25_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_25_dominates_noise_right]

def local_decay_0_25_0_1_dominates_noise_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem local_decay_0_25_0_1_dominates_noise_left_valid : local_decay_0_25_0_1_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_25_0_1_dominates_noise_left]

def local_decay_0_25_0_1_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_decay_0_25_0_1_dominates_noise_right_valid : local_decay_0_25_0_1_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_25_0_1_dominates_noise_right]

def local_min_input_gap : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_min_input_gap_valid : local_min_input_gap.Valid := by norm_num [RationalBox.Valid, local_min_input_gap]

def local_fast_duration : RationalBox := ⟨(9999999999999999999999999999999999999999 / 10000000000000000000000000000000000000000 : ℚ), (10000000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_fast_duration_valid : local_fast_duration.Valid := by norm_num [RationalBox.Valid, local_fast_duration]

def local_slow_duration : RationalBox := ⟨(6362776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (50907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_slow_duration_valid : local_slow_duration.Valid := by norm_num [RationalBox.Valid, local_slow_duration]

def local_main_reopen_bound : RationalBox := ⟨(34953934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (69907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopen_bound_valid : local_main_reopen_bound.Valid := by norm_num [RationalBox.Valid, local_main_reopen_bound]

def local_aux_cycle_ends_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_cycle_ends_after_raw_pulse_left_valid : local_aux_cycle_ends_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_after_raw_pulse_left]

def local_aux_cycle_ends_after_raw_pulse_right : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (5665909090909090909090909090909090909091 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_cycle_ends_after_raw_pulse_right_valid : local_aux_cycle_ends_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_after_raw_pulse_right]

def local_aux_cycle_ends_before_next_input_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_cycle_ends_before_next_input_left_valid : local_aux_cycle_ends_before_next_input_left.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_before_next_input_left]

def local_aux_cycle_ends_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_aux_cycle_ends_before_next_input_right_valid : local_aux_cycle_ends_before_next_input_right.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_before_next_input_right]

def local_learned_gain_below_all_caps_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_gain_below_all_caps_left_valid : local_learned_gain_below_all_caps_left.Valid := by norm_num [RationalBox.Valid, local_learned_gain_below_all_caps_left]

def local_learned_gain_below_all_caps_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem local_learned_gain_below_all_caps_right_valid : local_learned_gain_below_all_caps_right.Valid := by norm_num [RationalBox.Valid, local_learned_gain_below_all_caps_right]

def local_mark_finishes_before_any_main_firing_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_finishes_before_any_main_firing_left_valid : local_mark_finishes_before_any_main_firing_left.Valid := by norm_num [RationalBox.Valid, local_mark_finishes_before_any_main_firing_left]

def local_mark_finishes_before_any_main_firing_right : RationalBox := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem local_mark_finishes_before_any_main_firing_right_valid : local_mark_finishes_before_any_main_firing_right.Valid := by norm_num [RationalBox.Valid, local_mark_finishes_before_any_main_firing_right]

def local_main_fires_before_error_begins_left : RationalBox := ⟨(9 / 10 : ℚ), (9 / 10 : ℚ)⟩
theorem local_main_fires_before_error_begins_left_valid : local_main_fires_before_error_begins_left.Valid := by norm_num [RationalBox.Valid, local_main_fires_before_error_begins_left]

def local_main_fires_before_error_begins_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_fires_before_error_begins_right_valid : local_main_fires_before_error_begins_right.Valid := by norm_num [RationalBox.Valid, local_main_fires_before_error_begins_right]

def local_error_finishes_during_main_fast_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_finishes_during_main_fast_left_valid : local_error_finishes_during_main_fast_left.Valid := by norm_num [RationalBox.Valid, local_error_finishes_during_main_fast_left]

def local_error_finishes_during_main_fast_right : RationalBox := ⟨(14999999999999999999999999999999999999999 / 10000000000000000000000000000000000000000 : ℚ), (3 / 2 : ℚ)⟩
theorem local_error_finishes_during_main_fast_right_valid : local_error_finishes_during_main_fast_right.Valid := by norm_num [RationalBox.Valid, local_error_finishes_during_main_fast_right]

def local_main_reopens_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_main_reopens_after_raw_pulse_left_valid : local_main_reopens_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, local_main_reopens_after_raw_pulse_left]

def local_main_reopens_after_raw_pulse_right : RationalBox := ⟨(8237776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (65902212758966449929644309303261544994729 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopens_after_raw_pulse_right_valid : local_main_reopens_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, local_main_reopens_after_raw_pulse_right]

def local_main_reopens_before_next_input_left : RationalBox := ⟨(34953934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (69907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopens_before_next_input_left_valid : local_main_reopens_before_next_input_left.Valid := by norm_num [RationalBox.Valid, local_main_reopens_before_next_input_left]

def local_main_reopens_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_main_reopens_before_next_input_right_valid : local_main_reopens_before_next_input_right.Valid := by norm_num [RationalBox.Valid, local_main_reopens_before_next_input_right]

def local_arbitrary_initial_silence_inside_section_left : RationalBox := ⟨(1 / 100000 : ℚ), (1 / 100000 : ℚ)⟩
theorem local_arbitrary_initial_silence_inside_section_left_valid : local_arbitrary_initial_silence_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_arbitrary_initial_silence_inside_section_left]

def local_arbitrary_initial_silence_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_arbitrary_initial_silence_inside_section_right_valid : local_arbitrary_initial_silence_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_arbitrary_initial_silence_inside_section_right]

def local_rest_noise_inside_section_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem local_rest_noise_inside_section_left_valid : local_rest_noise_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_rest_noise_inside_section_left]

def local_rest_noise_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_rest_noise_inside_section_right_valid : local_rest_noise_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_rest_noise_inside_section_right]

def local_gain_before_0 : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_0_valid : local_gain_before_0.Valid := by norm_num [RationalBox.Valid, local_gain_before_0]

def local_peak_bound_0 : RationalBox := ⟨(1486507723727234944416254444898725196411 / 5000000000000000000000000000000000000000 : ℚ), (743936808320405663643604042669827175303 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_0_valid : local_peak_bound_0.Valid := by norm_num [RationalBox.Valid, local_peak_bound_0]

def local_carry_bound_0 : RationalBox := ⟨(15300422202959522407918279063983865337 / 2000000000000000000000000000000000000000 : ℚ), (15321606769242277199566132455298656847 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_0_valid : local_carry_bound_0.Valid := by norm_num [RationalBox.Valid, local_carry_bound_0]

def local_silent_0_no_first_crossing_left : RationalBox := ⟨(1486507723727234944416254444898725196411 / 5000000000000000000000000000000000000000 : ℚ), (743936808320405663643604042669827175303 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_0_no_first_crossing_left_valid : local_silent_0_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_no_first_crossing_left]

def local_silent_0_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_0_no_first_crossing_right_valid : local_silent_0_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_no_first_crossing_right]

def local_silent_0_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_silent_0_stays_below_threshold_after_raw_end_left_valid : local_silent_0_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_stays_below_threshold_after_raw_end_left]

def local_silent_0_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_0_stays_below_threshold_after_raw_end_right_valid : local_silent_0_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_stays_below_threshold_after_raw_end_right]

def local_silent_0_excess_returns_inside_section_left : RationalBox := ⟨(15300422202959522407918279063983865337 / 2000000000000000000000000000000000000000 : ℚ), (15321606769242277199566132455298656847 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_0_excess_returns_inside_section_left_valid : local_silent_0_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_excess_returns_inside_section_left]

def local_silent_0_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_0_excess_returns_inside_section_right_valid : local_silent_0_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_excess_returns_inside_section_right]

def local_gain_before_1 : RationalBox := ⟨(1093260347576166423671662107676113018829 / 2000000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_1_valid : local_gain_before_1.Valid := by norm_num [RationalBox.Valid, local_gain_before_1]

def local_peak_bound_1 : RationalBox := ⟨(1087108225037632318952931019576902586681 / 2500000000000000000000000000000000000000 : ℚ), (2176705269232412333812494883769947294517 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_1_valid : local_peak_bound_1.Valid := by norm_num [RationalBox.Valid, local_peak_bound_1]

def local_carry_bound_1 : RationalBox := ⟨(32458208295253073746125770419682342337 / 2500000000000000000000000000000000000000 : ℚ), (65012918581760963454536277079180689749 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_1_valid : local_carry_bound_1.Valid := by norm_num [RationalBox.Valid, local_carry_bound_1]

def local_silent_1_no_first_crossing_left : RationalBox := ⟨(1087108225037632318952931019576902586681 / 2500000000000000000000000000000000000000 : ℚ), (2176705269232412333812494883769947294517 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_1_no_first_crossing_left_valid : local_silent_1_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_no_first_crossing_left]

def local_silent_1_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_1_no_first_crossing_right_valid : local_silent_1_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_no_first_crossing_right]

def local_silent_1_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_silent_1_stays_below_threshold_after_raw_end_left_valid : local_silent_1_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_stays_below_threshold_after_raw_end_left]

def local_silent_1_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_1_stays_below_threshold_after_raw_end_right_valid : local_silent_1_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_stays_below_threshold_after_raw_end_right]

def local_silent_1_excess_returns_inside_section_left : RationalBox := ⟨(32458208295253073746125770419682342337 / 2500000000000000000000000000000000000000 : ℚ), (65012918581760963454536277079180689749 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_1_excess_returns_inside_section_left_valid : local_silent_1_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_excess_returns_inside_section_left]

def local_silent_1_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_1_excess_returns_inside_section_right_valid : local_silent_1_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_excess_returns_inside_section_right]

def local_gain_before_2 : RationalBox := ⟨(9960251165199976250523787258791057471269 / 10000000000000000000000000000000000000000 : ℚ), (9960450372215343763490081857984907714419 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_2_valid : local_gain_before_2.Valid := by norm_num [RationalBox.Valid, local_gain_before_2]

def local_peak_bound_2 : RationalBox := ⟨(3427303449546621315110527467953447792413 / 5000000000000000000000000000000000000000 : ℚ), (686367674744726438483278828428606754241 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_2_valid : local_peak_bound_2.Valid := by norm_num [RationalBox.Valid, local_peak_bound_2]

def local_carry_bound_2 : RationalBox := ⟨(3546996010601170613389962077147724881 / 156250000000000000000000000000000000000 : ℚ), (45471884172711192111030498080554273607 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_2_valid : local_carry_bound_2.Valid := by norm_num [RationalBox.Valid, local_carry_bound_2]

def local_silent_2_no_first_crossing_left : RationalBox := ⟨(3427303449546621315110527467953447792413 / 5000000000000000000000000000000000000000 : ℚ), (686367674744726438483278828428606754241 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_2_no_first_crossing_left_valid : local_silent_2_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_no_first_crossing_left]

def local_silent_2_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_2_no_first_crossing_right_valid : local_silent_2_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_no_first_crossing_right]

def local_silent_2_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_silent_2_stays_below_threshold_after_raw_end_left_valid : local_silent_2_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_stays_below_threshold_after_raw_end_left]

def local_silent_2_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_2_stays_below_threshold_after_raw_end_right_valid : local_silent_2_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_stays_below_threshold_after_raw_end_right]

def local_silent_2_excess_returns_inside_section_left : RationalBox := ⟨(3546996010601170613389962077147724881 / 156250000000000000000000000000000000000 : ℚ), (45471884172711192111030498080554273607 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_2_excess_returns_inside_section_left_valid : local_silent_2_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_excess_returns_inside_section_left]

def local_silent_2_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_2_excess_returns_inside_section_right_valid : local_silent_2_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_excess_returns_inside_section_right]

def local_learned_start_excess : RationalBox := ⟨(3546996010601170613389962077147724881 / 156250000000000000000000000000000000000 : ℚ), (45471884172711192111030498080554273607 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_start_excess_valid : local_learned_start_excess.Valid := by norm_num [RationalBox.Valid, local_learned_start_excess]

def local_learned_upper_at_0_5 : RationalBox := ⟨(2285393526321719384903312719361786997313 / 2500000000000000000000000000000000000000 : ℚ), (4570962890735979290455722897456232482451 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_upper_at_0_5_valid : local_learned_upper_at_0_5.Valid := by norm_num [RationalBox.Valid, local_learned_upper_at_0_5]

def local_learned_lower_at_0_9 : RationalBox := ⟨(5474169361770836637826062236177405808209 / 5000000000000000000000000000000000000000 : ℚ), (10948338723541673275652124472354811616419 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_lower_at_0_9_valid : local_learned_lower_at_0_9.Valid := by norm_num [RationalBox.Valid, local_learned_lower_at_0_9]

def local_learned_below_threshold_until_0_5_left : RationalBox := ⟨(2285393526321719384903312719361786997313 / 2500000000000000000000000000000000000000 : ℚ), (4570962890735979290455722897456232482451 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_below_threshold_until_0_5_left_valid : local_learned_below_threshold_until_0_5_left.Valid := by norm_num [RationalBox.Valid, local_learned_below_threshold_until_0_5_left]

def local_learned_below_threshold_until_0_5_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_learned_below_threshold_until_0_5_right_valid : local_learned_below_threshold_until_0_5_right.Valid := by norm_num [RationalBox.Valid, local_learned_below_threshold_until_0_5_right]

def local_learned_above_threshold_by_0_9_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_learned_above_threshold_by_0_9_left_valid : local_learned_above_threshold_by_0_9_left.Valid := by norm_num [RationalBox.Valid, local_learned_above_threshold_by_0_9_left]

def local_learned_above_threshold_by_0_9_right : RationalBox := ⟨(5474169361770836637826062236177405808209 / 5000000000000000000000000000000000000000 : ℚ), (10948338723541673275652124472354811616419 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_above_threshold_by_0_9_right_valid : local_learned_above_threshold_by_0_9_right.Valid := by norm_num [RationalBox.Valid, local_learned_above_threshold_by_0_9_right]

def local_probe_gap_exceeds_cycle_left : RationalBox := ⟨(34953934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (69907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_probe_gap_exceeds_cycle_left_valid : local_probe_gap_exceeds_cycle_left.Valid := by norm_num [RationalBox.Valid, local_probe_gap_exceeds_cycle_left]

def local_probe_gap_exceeds_cycle_right : RationalBox := ⟨(20 / 1 : ℚ), (20 / 1 : ℚ)⟩
theorem local_probe_gap_exceeds_cycle_right_valid : local_probe_gap_exceeds_cycle_right.Valid := by norm_num [RationalBox.Valid, local_probe_gap_exceeds_cycle_right]

def local_probe_aux_cycle_ends_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_probe_aux_cycle_ends_left_valid : local_probe_aux_cycle_ends_left.Valid := by norm_num [RationalBox.Valid, local_probe_aux_cycle_ends_left]

def local_probe_aux_cycle_ends_right : RationalBox := ⟨(20 / 1 : ℚ), (20 / 1 : ℚ)⟩
theorem local_probe_aux_cycle_ends_right_valid : local_probe_aux_cycle_ends_right.Valid := by norm_num [RationalBox.Valid, local_probe_aux_cycle_ends_right]

def local_work_bound : RationalBox := ⟨(10573936830325210453707713866907429323159 / 40000000000000000000000000000000000000 : ℚ), (2643484207581302613426928466726857330789751 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_work_bound_valid : local_work_bound.Valid := by norm_num [RationalBox.Valid, local_work_bound]

def local_reserve_gate_stays_open_left : RationalBox := ⟨(10573936830325210453707713866907429323159 / 40000000000000000000000000000000000000 : ℚ), (2643484207581302613426928466726857330789751 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_reserve_gate_stays_open_left_valid : local_reserve_gate_stays_open_left.Valid := by norm_num [RationalBox.Valid, local_reserve_gate_stays_open_left]

def local_reserve_gate_stays_open_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem local_reserve_gate_stays_open_right_valid : local_reserve_gate_stays_open_right.Valid := by norm_num [RationalBox.Valid, local_reserve_gate_stays_open_right]

def local_A_gain_complete_by : RationalBox := ⟨(213483333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (426966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_gain_complete_by_valid : local_A_gain_complete_by.Valid := by norm_num [RationalBox.Valid, local_A_gain_complete_by]

def local_A_first_emission : RationalBox := ⟨(493 / 10 : ℚ), (251 / 5 : ℚ)⟩
theorem local_A_first_emission_valid : local_A_first_emission.Valid := by norm_num [RationalBox.Valid, local_A_first_emission]

def local_A_last_return_by : RationalBox := ⟨(641453934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (1282907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_last_return_by_valid : local_A_last_return_by.Valid := by norm_num [RationalBox.Valid, local_A_last_return_by]

def local_B_last_return_by : RationalBox := ⟨(634953934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_B_last_return_by_valid : local_B_last_return_by.Valid := by norm_num [RationalBox.Valid, local_B_last_return_by]

def local_A_learning_complete_before_first_response_left : RationalBox := ⟨(213483333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (426966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_learning_complete_before_first_response_left_valid : local_A_learning_complete_before_first_response_left.Valid := by norm_num [RationalBox.Valid, local_A_learning_complete_before_first_response_left]

def local_A_learning_complete_before_first_response_right : RationalBox := ⟨(493 / 10 : ℚ), (493 / 10 : ℚ)⟩
theorem local_A_learning_complete_before_first_response_right_valid : local_A_learning_complete_before_first_response_right.Valid := by norm_num [RationalBox.Valid, local_A_learning_complete_before_first_response_right]

def local_A_quiescent_before_measurement_left : RationalBox := ⟨(641453934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (1282907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_quiescent_before_measurement_left_valid : local_A_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, local_A_quiescent_before_measurement_left]

def local_A_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem local_A_quiescent_before_measurement_right_valid : local_A_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, local_A_quiescent_before_measurement_right]

def local_B_quiescent_before_measurement_left : RationalBox := ⟨(634953934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_B_quiescent_before_measurement_left_valid : local_B_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, local_B_quiescent_before_measurement_left]

def local_B_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem local_B_quiescent_before_measurement_right_valid : local_B_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, local_B_quiescent_before_measurement_right]

def birth_slow_decay_dominates_noise_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem birth_slow_decay_dominates_noise_left_valid : birth_slow_decay_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, birth_slow_decay_dominates_noise_left]

def birth_slow_decay_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem birth_slow_decay_dominates_noise_right_valid : birth_slow_decay_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, birth_slow_decay_dominates_noise_right]

def protected_arrival_after_FAST_left : RationalBox := ⟨(19 / 10 : ℚ), (19000000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_arrival_after_FAST_left_valid : protected_arrival_after_FAST_left.Valid := by norm_num [RationalBox.Valid, protected_arrival_after_FAST_left]

def protected_arrival_after_FAST_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem protected_arrival_after_FAST_right_valid : protected_arrival_after_FAST_right.Valid := by norm_num [RationalBox.Valid, protected_arrival_after_FAST_right]

def entire_protected_MARK_and_ERROR_before_reopen_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem entire_protected_MARK_and_ERROR_before_reopen_left_valid : entire_protected_MARK_and_ERROR_before_reopen_left.Valid := by norm_num [RationalBox.Valid, entire_protected_MARK_and_ERROR_before_reopen_left]

def entire_protected_MARK_and_ERROR_before_reopen_right : RationalBox := ⟨(1155821983878683912233952713126621492413 / 10000000000000000000000000000000000000000 : ℚ), (577910991939341956116976356563310746207 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem entire_protected_MARK_and_ERROR_before_reopen_right_valid : entire_protected_MARK_and_ERROR_before_reopen_right.Valid := by norm_num [RationalBox.Valid, entire_protected_MARK_and_ERROR_before_reopen_right]

def protected_input_reopens_by_deadline_left : RationalBox := ⟨(164338170600535429933483389700105808943 / 2000000000000000000000000000000000000000 : ℚ), (205422713250669287416854237125132261179 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem protected_input_reopens_by_deadline_left_valid : protected_input_reopens_by_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_by_deadline_left]

def protected_input_reopens_by_deadline_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem protected_input_reopens_by_deadline_right_valid : protected_input_reopens_by_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_by_deadline_right]

def protected_aux_cycle_before_deadline_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_aux_cycle_before_deadline_left_valid : protected_aux_cycle_before_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_aux_cycle_before_deadline_left]

def protected_aux_cycle_before_deadline_right : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_aux_cycle_before_deadline_right_valid : protected_aux_cycle_before_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_aux_cycle_before_deadline_right]

def protected_return_before_next_input_left : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_return_before_next_input_left_valid : protected_return_before_next_input_left.Valid := by norm_num [RationalBox.Valid, protected_return_before_next_input_left]

def protected_return_before_next_input_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem protected_return_before_next_input_right_valid : protected_return_before_next_input_right.Valid := by norm_num [RationalBox.Valid, protected_return_before_next_input_right]

def recovery_cap_not_reached_left : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem recovery_cap_not_reached_left_valid : recovery_cap_not_reached_left.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_left]

def recovery_cap_not_reached_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem recovery_cap_not_reached_right_valid : recovery_cap_not_reached_right.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_right]

def unused_port1_birth_gain_below_caps_left : RationalBox := ⟨(5999940000299999000002499995000008333321 / 5000000000000000000000000000000000000000 : ℚ), (12000120000600002000005000010000016666691 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem unused_port1_birth_gain_below_caps_left_valid : unused_port1_birth_gain_below_caps_left.Valid := by norm_num [RationalBox.Valid, unused_port1_birth_gain_below_caps_left]

def unused_port1_birth_gain_below_caps_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem unused_port1_birth_gain_below_caps_right_valid : unused_port1_birth_gain_below_caps_right.Valid := by norm_num [RationalBox.Valid, unused_port1_birth_gain_below_caps_right]

def warmup_returns_before_entry_cut_left : RationalBox := ⟨(634953934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem warmup_returns_before_entry_cut_left_valid : warmup_returns_before_entry_cut_left.Valid := by norm_num [RationalBox.Valid, warmup_returns_before_entry_cut_left]

def warmup_returns_before_entry_cut_right : RationalBox := ⟨(1599 / 10 : ℚ), (1599 / 10 : ℚ)⟩
theorem warmup_returns_before_entry_cut_right_valid : warmup_returns_before_entry_cut_right.Valid := by norm_num [RationalBox.Valid, warmup_returns_before_entry_cut_right]

def entry_charge_radius_inside_local_section_left : RationalBox := ⟨(1 / 100000 : ℚ), (1 / 100000 : ℚ)⟩
theorem entry_charge_radius_inside_local_section_left_valid : entry_charge_radius_inside_local_section_left.Valid := by norm_num [RationalBox.Valid, entry_charge_radius_inside_local_section_left]

def entry_charge_radius_inside_local_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem entry_charge_radius_inside_local_section_right_valid : entry_charge_radius_inside_local_section_right.Valid := by norm_num [RationalBox.Valid, entry_charge_radius_inside_local_section_right]

def entry_aux_band_below_threshold_left : RationalBox := ⟨(2501 / 100000 : ℚ), (2501 / 100000 : ℚ)⟩
theorem entry_aux_band_below_threshold_left_valid : entry_aux_band_below_threshold_left.Valid := by norm_num [RationalBox.Valid, entry_aux_band_below_threshold_left]

def entry_aux_band_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem entry_aux_band_below_threshold_right_valid : entry_aux_band_below_threshold_right.Valid := by norm_num [RationalBox.Valid, entry_aux_band_below_threshold_right]

def birth_recovery : RationalBox := ⟨(7999 / 100000 : ℚ), (8001 / 100000 : ℚ)⟩
theorem birth_recovery_valid : birth_recovery.Valid := by norm_num [RationalBox.Valid, birth_recovery]

def protected_MARK_dose : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem protected_MARK_dose_valid : protected_MARK_dose.Valid := by norm_num [RationalBox.Valid, protected_MARK_dose]

def entry_recovery : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem entry_recovery_valid : entry_recovery.Valid := by norm_num [RationalBox.Valid, entry_recovery]

def entry_charge_radius : RationalBox := ⟨(1 / 100000 : ℚ), (1 / 100000 : ℚ)⟩
theorem entry_charge_radius_valid : entry_charge_radius.Valid := by norm_num [RationalBox.Valid, entry_charge_radius]

def entry_q : RationalBox := ⟨(9999 / 100000 : ℚ), (10001 / 100000 : ℚ)⟩
theorem entry_q_valid : entry_q.Valid := by norm_num [RationalBox.Valid, entry_q]

def entry_m : RationalBox := ⟨(2499 / 100000 : ℚ), (2501 / 100000 : ℚ)⟩
theorem entry_m_valid : entry_m.Valid := by norm_num [RationalBox.Valid, entry_m]

def q_lower_at_protected_arrival : RationalBox := ⟨(297240952695236861337250883586105985229 / 2000000000000000000000000000000000000000 : ℚ), (743102381738092153343127208965264963073 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem q_lower_at_protected_arrival_valid : q_lower_at_protected_arrival.Valid := by norm_num [RationalBox.Valid, q_lower_at_protected_arrival]

def q_lower_through_protected_cycle : RationalBox := ⟨(1155821983878683912233952713126621492413 / 10000000000000000000000000000000000000000 : ℚ), (577910991939341956116976356563310746207 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem q_lower_through_protected_cycle_valid : q_lower_through_protected_cycle.Valid := by norm_num [RationalBox.Valid, q_lower_through_protected_cycle]

def q_upper_at_reopen_deadline : RationalBox := ⟨(164338170600535429933483389700105808943 / 2000000000000000000000000000000000000000 : ℚ), (205422713250669287416854237125132261179 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem q_upper_at_reopen_deadline_valid : q_upper_at_reopen_deadline.Valid := by norm_num [RationalBox.Valid, q_upper_at_reopen_deadline]

def protected_reopen_deadline : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_reopen_deadline_valid : protected_reopen_deadline.Valid := by norm_num [RationalBox.Valid, protected_reopen_deadline]

def last_warmup_return : RationalBox := ⟨(634953934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem last_warmup_return_valid : last_warmup_return.Valid := by norm_num [RationalBox.Valid, last_warmup_return]

def no_noise_positive_residual_left : RationalBox := ⟨(1 / 100000 : ℚ), (1 / 100000 : ℚ)⟩
theorem no_noise_positive_residual_left_valid : no_noise_positive_residual_left.Valid := by norm_num [RationalBox.Valid, no_noise_positive_residual_left]

def no_noise_positive_residual_right : RationalBox := ⟨(418245496870030414562379084115601089407 / 2500000000000000000000000000000000000000 : ℚ), (1672981987480121658249516336462404357629 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem no_noise_positive_residual_right_valid : no_noise_positive_residual_right.Valid := by norm_num [RationalBox.Valid, no_noise_positive_residual_right]

theorem local_h_increases_through_raw_window_verified : RationalBox.StrictBefore local_h_increases_through_raw_window_left local_h_increases_through_raw_window_right := by
  norm_num [RationalBox.StrictBefore, local_h_increases_through_raw_window_left, local_h_increases_through_raw_window_right]

theorem local_aux_rest_below_threshold_verified : RationalBox.StrictBefore local_aux_rest_below_threshold_left local_aux_rest_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, local_aux_rest_below_threshold_left, local_aux_rest_below_threshold_right]

theorem local_aux_below_threshold_until_0_015_verified : RationalBox.StrictBefore local_aux_below_threshold_until_0_015_left local_aux_below_threshold_until_0_015_right := by
  norm_num [RationalBox.StrictBefore, local_aux_below_threshold_until_0_015_left, local_aux_below_threshold_until_0_015_right]

theorem local_aux_above_threshold_by_0_03_verified : RationalBox.StrictBefore local_aux_above_threshold_by_0_03_left local_aux_above_threshold_by_0_03_right := by
  norm_num [RationalBox.StrictBefore, local_aux_above_threshold_by_0_03_left, local_aux_above_threshold_by_0_03_right]

theorem local_decay_1_0_8_dominates_noise_verified : RationalBox.StrictBefore local_decay_1_0_8_dominates_noise_left local_decay_1_0_8_dominates_noise_right := by
  norm_num [RationalBox.StrictBefore, local_decay_1_0_8_dominates_noise_left, local_decay_1_0_8_dominates_noise_right]

theorem local_decay_0_8_0_1_dominates_noise_verified : RationalBox.StrictBefore local_decay_0_8_0_1_dominates_noise_left local_decay_0_8_0_1_dominates_noise_right := by
  norm_num [RationalBox.StrictBefore, local_decay_0_8_0_1_dominates_noise_left, local_decay_0_8_0_1_dominates_noise_right]

theorem local_decay_0_1_0_025_dominates_noise_verified : RationalBox.StrictBefore local_decay_0_1_0_025_dominates_noise_left local_decay_0_1_0_025_dominates_noise_right := by
  norm_num [RationalBox.StrictBefore, local_decay_0_1_0_025_dominates_noise_left, local_decay_0_1_0_025_dominates_noise_right]

theorem local_decay_1_0_25_dominates_noise_verified : RationalBox.StrictBefore local_decay_1_0_25_dominates_noise_left local_decay_1_0_25_dominates_noise_right := by
  norm_num [RationalBox.StrictBefore, local_decay_1_0_25_dominates_noise_left, local_decay_1_0_25_dominates_noise_right]

theorem local_decay_0_25_0_1_dominates_noise_verified : RationalBox.StrictBefore local_decay_0_25_0_1_dominates_noise_left local_decay_0_25_0_1_dominates_noise_right := by
  norm_num [RationalBox.StrictBefore, local_decay_0_25_0_1_dominates_noise_left, local_decay_0_25_0_1_dominates_noise_right]

theorem local_aux_cycle_ends_after_raw_pulse_verified : RationalBox.StrictBefore local_aux_cycle_ends_after_raw_pulse_left local_aux_cycle_ends_after_raw_pulse_right := by
  norm_num [RationalBox.StrictBefore, local_aux_cycle_ends_after_raw_pulse_left, local_aux_cycle_ends_after_raw_pulse_right]

theorem local_aux_cycle_ends_before_next_input_verified : RationalBox.StrictBefore local_aux_cycle_ends_before_next_input_left local_aux_cycle_ends_before_next_input_right := by
  norm_num [RationalBox.StrictBefore, local_aux_cycle_ends_before_next_input_left, local_aux_cycle_ends_before_next_input_right]

theorem local_learned_gain_below_all_caps_verified : RationalBox.StrictBefore local_learned_gain_below_all_caps_left local_learned_gain_below_all_caps_right := by
  norm_num [RationalBox.StrictBefore, local_learned_gain_below_all_caps_left, local_learned_gain_below_all_caps_right]

theorem local_mark_finishes_before_any_main_firing_verified : RationalBox.StrictBefore local_mark_finishes_before_any_main_firing_left local_mark_finishes_before_any_main_firing_right := by
  norm_num [RationalBox.StrictBefore, local_mark_finishes_before_any_main_firing_left, local_mark_finishes_before_any_main_firing_right]

theorem local_main_fires_before_error_begins_verified : RationalBox.StrictBefore local_main_fires_before_error_begins_left local_main_fires_before_error_begins_right := by
  norm_num [RationalBox.StrictBefore, local_main_fires_before_error_begins_left, local_main_fires_before_error_begins_right]

theorem local_error_finishes_during_main_fast_verified : RationalBox.StrictBefore local_error_finishes_during_main_fast_left local_error_finishes_during_main_fast_right := by
  norm_num [RationalBox.StrictBefore, local_error_finishes_during_main_fast_left, local_error_finishes_during_main_fast_right]

theorem local_main_reopens_after_raw_pulse_verified : RationalBox.StrictBefore local_main_reopens_after_raw_pulse_left local_main_reopens_after_raw_pulse_right := by
  norm_num [RationalBox.StrictBefore, local_main_reopens_after_raw_pulse_left, local_main_reopens_after_raw_pulse_right]

theorem local_main_reopens_before_next_input_verified : RationalBox.StrictBefore local_main_reopens_before_next_input_left local_main_reopens_before_next_input_right := by
  norm_num [RationalBox.StrictBefore, local_main_reopens_before_next_input_left, local_main_reopens_before_next_input_right]

theorem local_arbitrary_initial_silence_inside_section_verified : RationalBox.StrictBefore local_arbitrary_initial_silence_inside_section_left local_arbitrary_initial_silence_inside_section_right := by
  norm_num [RationalBox.StrictBefore, local_arbitrary_initial_silence_inside_section_left, local_arbitrary_initial_silence_inside_section_right]

theorem local_rest_noise_inside_section_verified : RationalBox.StrictBefore local_rest_noise_inside_section_left local_rest_noise_inside_section_right := by
  norm_num [RationalBox.StrictBefore, local_rest_noise_inside_section_left, local_rest_noise_inside_section_right]

theorem local_silent_0_no_first_crossing_verified : RationalBox.StrictBefore local_silent_0_no_first_crossing_left local_silent_0_no_first_crossing_right := by
  norm_num [RationalBox.StrictBefore, local_silent_0_no_first_crossing_left, local_silent_0_no_first_crossing_right]

theorem local_silent_0_stays_below_threshold_after_raw_end_verified : RationalBox.StrictBefore local_silent_0_stays_below_threshold_after_raw_end_left local_silent_0_stays_below_threshold_after_raw_end_right := by
  norm_num [RationalBox.StrictBefore, local_silent_0_stays_below_threshold_after_raw_end_left, local_silent_0_stays_below_threshold_after_raw_end_right]

theorem local_silent_0_excess_returns_inside_section_verified : RationalBox.StrictBefore local_silent_0_excess_returns_inside_section_left local_silent_0_excess_returns_inside_section_right := by
  norm_num [RationalBox.StrictBefore, local_silent_0_excess_returns_inside_section_left, local_silent_0_excess_returns_inside_section_right]

theorem local_silent_1_no_first_crossing_verified : RationalBox.StrictBefore local_silent_1_no_first_crossing_left local_silent_1_no_first_crossing_right := by
  norm_num [RationalBox.StrictBefore, local_silent_1_no_first_crossing_left, local_silent_1_no_first_crossing_right]

theorem local_silent_1_stays_below_threshold_after_raw_end_verified : RationalBox.StrictBefore local_silent_1_stays_below_threshold_after_raw_end_left local_silent_1_stays_below_threshold_after_raw_end_right := by
  norm_num [RationalBox.StrictBefore, local_silent_1_stays_below_threshold_after_raw_end_left, local_silent_1_stays_below_threshold_after_raw_end_right]

theorem local_silent_1_excess_returns_inside_section_verified : RationalBox.StrictBefore local_silent_1_excess_returns_inside_section_left local_silent_1_excess_returns_inside_section_right := by
  norm_num [RationalBox.StrictBefore, local_silent_1_excess_returns_inside_section_left, local_silent_1_excess_returns_inside_section_right]

theorem local_silent_2_no_first_crossing_verified : RationalBox.StrictBefore local_silent_2_no_first_crossing_left local_silent_2_no_first_crossing_right := by
  norm_num [RationalBox.StrictBefore, local_silent_2_no_first_crossing_left, local_silent_2_no_first_crossing_right]

theorem local_silent_2_stays_below_threshold_after_raw_end_verified : RationalBox.StrictBefore local_silent_2_stays_below_threshold_after_raw_end_left local_silent_2_stays_below_threshold_after_raw_end_right := by
  norm_num [RationalBox.StrictBefore, local_silent_2_stays_below_threshold_after_raw_end_left, local_silent_2_stays_below_threshold_after_raw_end_right]

theorem local_silent_2_excess_returns_inside_section_verified : RationalBox.StrictBefore local_silent_2_excess_returns_inside_section_left local_silent_2_excess_returns_inside_section_right := by
  norm_num [RationalBox.StrictBefore, local_silent_2_excess_returns_inside_section_left, local_silent_2_excess_returns_inside_section_right]

theorem local_learned_below_threshold_until_0_5_verified : RationalBox.StrictBefore local_learned_below_threshold_until_0_5_left local_learned_below_threshold_until_0_5_right := by
  norm_num [RationalBox.StrictBefore, local_learned_below_threshold_until_0_5_left, local_learned_below_threshold_until_0_5_right]

theorem local_learned_above_threshold_by_0_9_verified : RationalBox.StrictBefore local_learned_above_threshold_by_0_9_left local_learned_above_threshold_by_0_9_right := by
  norm_num [RationalBox.StrictBefore, local_learned_above_threshold_by_0_9_left, local_learned_above_threshold_by_0_9_right]

theorem local_probe_gap_exceeds_cycle_verified : RationalBox.StrictBefore local_probe_gap_exceeds_cycle_left local_probe_gap_exceeds_cycle_right := by
  norm_num [RationalBox.StrictBefore, local_probe_gap_exceeds_cycle_left, local_probe_gap_exceeds_cycle_right]

theorem local_probe_aux_cycle_ends_verified : RationalBox.StrictBefore local_probe_aux_cycle_ends_left local_probe_aux_cycle_ends_right := by
  norm_num [RationalBox.StrictBefore, local_probe_aux_cycle_ends_left, local_probe_aux_cycle_ends_right]

theorem local_reserve_gate_stays_open_verified : RationalBox.StrictBefore local_reserve_gate_stays_open_left local_reserve_gate_stays_open_right := by
  norm_num [RationalBox.StrictBefore, local_reserve_gate_stays_open_left, local_reserve_gate_stays_open_right]

theorem local_A_learning_complete_before_first_response_verified : RationalBox.StrictBefore local_A_learning_complete_before_first_response_left local_A_learning_complete_before_first_response_right := by
  norm_num [RationalBox.StrictBefore, local_A_learning_complete_before_first_response_left, local_A_learning_complete_before_first_response_right]

theorem local_A_quiescent_before_measurement_verified : RationalBox.StrictBefore local_A_quiescent_before_measurement_left local_A_quiescent_before_measurement_right := by
  norm_num [RationalBox.StrictBefore, local_A_quiescent_before_measurement_left, local_A_quiescent_before_measurement_right]

theorem local_B_quiescent_before_measurement_verified : RationalBox.StrictBefore local_B_quiescent_before_measurement_left local_B_quiescent_before_measurement_right := by
  norm_num [RationalBox.StrictBefore, local_B_quiescent_before_measurement_left, local_B_quiescent_before_measurement_right]

theorem birth_slow_decay_dominates_noise_verified : RationalBox.StrictBefore birth_slow_decay_dominates_noise_left birth_slow_decay_dominates_noise_right := by
  norm_num [RationalBox.StrictBefore, birth_slow_decay_dominates_noise_left, birth_slow_decay_dominates_noise_right]

theorem protected_arrival_after_FAST_verified : RationalBox.StrictBefore protected_arrival_after_FAST_left protected_arrival_after_FAST_right := by
  norm_num [RationalBox.StrictBefore, protected_arrival_after_FAST_left, protected_arrival_after_FAST_right]

theorem entire_protected_MARK_and_ERROR_before_reopen_verified : RationalBox.StrictBefore entire_protected_MARK_and_ERROR_before_reopen_left entire_protected_MARK_and_ERROR_before_reopen_right := by
  norm_num [RationalBox.StrictBefore, entire_protected_MARK_and_ERROR_before_reopen_left, entire_protected_MARK_and_ERROR_before_reopen_right]

theorem protected_input_reopens_by_deadline_verified : RationalBox.StrictBefore protected_input_reopens_by_deadline_left protected_input_reopens_by_deadline_right := by
  norm_num [RationalBox.StrictBefore, protected_input_reopens_by_deadline_left, protected_input_reopens_by_deadline_right]

theorem protected_aux_cycle_before_deadline_verified : RationalBox.StrictBefore protected_aux_cycle_before_deadline_left protected_aux_cycle_before_deadline_right := by
  norm_num [RationalBox.StrictBefore, protected_aux_cycle_before_deadline_left, protected_aux_cycle_before_deadline_right]

theorem protected_return_before_next_input_verified : RationalBox.StrictBefore protected_return_before_next_input_left protected_return_before_next_input_right := by
  norm_num [RationalBox.StrictBefore, protected_return_before_next_input_left, protected_return_before_next_input_right]

theorem recovery_cap_not_reached_verified : RationalBox.StrictBefore recovery_cap_not_reached_left recovery_cap_not_reached_right := by
  norm_num [RationalBox.StrictBefore, recovery_cap_not_reached_left, recovery_cap_not_reached_right]

theorem unused_port1_birth_gain_below_caps_verified : RationalBox.StrictBefore unused_port1_birth_gain_below_caps_left unused_port1_birth_gain_below_caps_right := by
  norm_num [RationalBox.StrictBefore, unused_port1_birth_gain_below_caps_left, unused_port1_birth_gain_below_caps_right]

theorem warmup_returns_before_entry_cut_verified : RationalBox.StrictBefore warmup_returns_before_entry_cut_left warmup_returns_before_entry_cut_right := by
  norm_num [RationalBox.StrictBefore, warmup_returns_before_entry_cut_left, warmup_returns_before_entry_cut_right]

theorem entry_charge_radius_inside_local_section_verified : RationalBox.StrictBefore entry_charge_radius_inside_local_section_left entry_charge_radius_inside_local_section_right := by
  norm_num [RationalBox.StrictBefore, entry_charge_radius_inside_local_section_left, entry_charge_radius_inside_local_section_right]

theorem entry_aux_band_below_threshold_verified : RationalBox.StrictBefore entry_aux_band_below_threshold_left entry_aux_band_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, entry_aux_band_below_threshold_left, entry_aux_band_below_threshold_right]

theorem no_noise_positive_residual_verified : RationalBox.StrictBefore no_noise_positive_residual_left no_noise_positive_residual_right := by
  norm_num [RationalBox.StrictBefore, no_noise_positive_residual_left, no_noise_positive_residual_right]

def Obligations : Prop :=
  RationalBox.StrictBefore local_h_increases_through_raw_window_left local_h_increases_through_raw_window_right ∧
  RationalBox.StrictBefore local_aux_rest_below_threshold_left local_aux_rest_below_threshold_right ∧
  RationalBox.StrictBefore local_aux_below_threshold_until_0_015_left local_aux_below_threshold_until_0_015_right ∧
  RationalBox.StrictBefore local_aux_above_threshold_by_0_03_left local_aux_above_threshold_by_0_03_right ∧
  RationalBox.StrictBefore local_decay_1_0_8_dominates_noise_left local_decay_1_0_8_dominates_noise_right ∧
  RationalBox.StrictBefore local_decay_0_8_0_1_dominates_noise_left local_decay_0_8_0_1_dominates_noise_right ∧
  RationalBox.StrictBefore local_decay_0_1_0_025_dominates_noise_left local_decay_0_1_0_025_dominates_noise_right ∧
  RationalBox.StrictBefore local_decay_1_0_25_dominates_noise_left local_decay_1_0_25_dominates_noise_right ∧
  RationalBox.StrictBefore local_decay_0_25_0_1_dominates_noise_left local_decay_0_25_0_1_dominates_noise_right ∧
  RationalBox.StrictBefore local_aux_cycle_ends_after_raw_pulse_left local_aux_cycle_ends_after_raw_pulse_right ∧
  RationalBox.StrictBefore local_aux_cycle_ends_before_next_input_left local_aux_cycle_ends_before_next_input_right ∧
  RationalBox.StrictBefore local_learned_gain_below_all_caps_left local_learned_gain_below_all_caps_right ∧
  RationalBox.StrictBefore local_mark_finishes_before_any_main_firing_left local_mark_finishes_before_any_main_firing_right ∧
  RationalBox.StrictBefore local_main_fires_before_error_begins_left local_main_fires_before_error_begins_right ∧
  RationalBox.StrictBefore local_error_finishes_during_main_fast_left local_error_finishes_during_main_fast_right ∧
  RationalBox.StrictBefore local_main_reopens_after_raw_pulse_left local_main_reopens_after_raw_pulse_right ∧
  RationalBox.StrictBefore local_main_reopens_before_next_input_left local_main_reopens_before_next_input_right ∧
  RationalBox.StrictBefore local_arbitrary_initial_silence_inside_section_left local_arbitrary_initial_silence_inside_section_right ∧
  RationalBox.StrictBefore local_rest_noise_inside_section_left local_rest_noise_inside_section_right ∧
  RationalBox.StrictBefore local_silent_0_no_first_crossing_left local_silent_0_no_first_crossing_right ∧
  RationalBox.StrictBefore local_silent_0_stays_below_threshold_after_raw_end_left local_silent_0_stays_below_threshold_after_raw_end_right ∧
  RationalBox.StrictBefore local_silent_0_excess_returns_inside_section_left local_silent_0_excess_returns_inside_section_right ∧
  RationalBox.StrictBefore local_silent_1_no_first_crossing_left local_silent_1_no_first_crossing_right ∧
  RationalBox.StrictBefore local_silent_1_stays_below_threshold_after_raw_end_left local_silent_1_stays_below_threshold_after_raw_end_right ∧
  RationalBox.StrictBefore local_silent_1_excess_returns_inside_section_left local_silent_1_excess_returns_inside_section_right ∧
  RationalBox.StrictBefore local_silent_2_no_first_crossing_left local_silent_2_no_first_crossing_right ∧
  RationalBox.StrictBefore local_silent_2_stays_below_threshold_after_raw_end_left local_silent_2_stays_below_threshold_after_raw_end_right ∧
  RationalBox.StrictBefore local_silent_2_excess_returns_inside_section_left local_silent_2_excess_returns_inside_section_right ∧
  RationalBox.StrictBefore local_learned_below_threshold_until_0_5_left local_learned_below_threshold_until_0_5_right ∧
  RationalBox.StrictBefore local_learned_above_threshold_by_0_9_left local_learned_above_threshold_by_0_9_right ∧
  RationalBox.StrictBefore local_probe_gap_exceeds_cycle_left local_probe_gap_exceeds_cycle_right ∧
  RationalBox.StrictBefore local_probe_aux_cycle_ends_left local_probe_aux_cycle_ends_right ∧
  RationalBox.StrictBefore local_reserve_gate_stays_open_left local_reserve_gate_stays_open_right ∧
  RationalBox.StrictBefore local_A_learning_complete_before_first_response_left local_A_learning_complete_before_first_response_right ∧
  RationalBox.StrictBefore local_A_quiescent_before_measurement_left local_A_quiescent_before_measurement_right ∧
  RationalBox.StrictBefore local_B_quiescent_before_measurement_left local_B_quiescent_before_measurement_right ∧
  RationalBox.StrictBefore birth_slow_decay_dominates_noise_left birth_slow_decay_dominates_noise_right ∧
  RationalBox.StrictBefore protected_arrival_after_FAST_left protected_arrival_after_FAST_right ∧
  RationalBox.StrictBefore entire_protected_MARK_and_ERROR_before_reopen_left entire_protected_MARK_and_ERROR_before_reopen_right ∧
  RationalBox.StrictBefore protected_input_reopens_by_deadline_left protected_input_reopens_by_deadline_right ∧
  RationalBox.StrictBefore protected_aux_cycle_before_deadline_left protected_aux_cycle_before_deadline_right ∧
  RationalBox.StrictBefore protected_return_before_next_input_left protected_return_before_next_input_right ∧
  RationalBox.StrictBefore recovery_cap_not_reached_left recovery_cap_not_reached_right ∧
  RationalBox.StrictBefore unused_port1_birth_gain_below_caps_left unused_port1_birth_gain_below_caps_right ∧
  RationalBox.StrictBefore warmup_returns_before_entry_cut_left warmup_returns_before_entry_cut_right ∧
  RationalBox.StrictBefore entry_charge_radius_inside_local_section_left entry_charge_radius_inside_local_section_right ∧
  RationalBox.StrictBefore entry_aux_band_below_threshold_left entry_aux_band_below_threshold_right ∧
  RationalBox.StrictBefore no_noise_positive_residual_left no_noise_positive_residual_right
theorem obligations_verified : Obligations := by
  exact ⟨local_h_increases_through_raw_window_verified, local_aux_rest_below_threshold_verified, local_aux_below_threshold_until_0_015_verified, local_aux_above_threshold_by_0_03_verified, local_decay_1_0_8_dominates_noise_verified, local_decay_0_8_0_1_dominates_noise_verified, local_decay_0_1_0_025_dominates_noise_verified, local_decay_1_0_25_dominates_noise_verified, local_decay_0_25_0_1_dominates_noise_verified, local_aux_cycle_ends_after_raw_pulse_verified, local_aux_cycle_ends_before_next_input_verified, local_learned_gain_below_all_caps_verified, local_mark_finishes_before_any_main_firing_verified, local_main_fires_before_error_begins_verified, local_error_finishes_during_main_fast_verified, local_main_reopens_after_raw_pulse_verified, local_main_reopens_before_next_input_verified, local_arbitrary_initial_silence_inside_section_verified, local_rest_noise_inside_section_verified, local_silent_0_no_first_crossing_verified, local_silent_0_stays_below_threshold_after_raw_end_verified, local_silent_0_excess_returns_inside_section_verified, local_silent_1_no_first_crossing_verified, local_silent_1_stays_below_threshold_after_raw_end_verified, local_silent_1_excess_returns_inside_section_verified, local_silent_2_no_first_crossing_verified, local_silent_2_stays_below_threshold_after_raw_end_verified, local_silent_2_excess_returns_inside_section_verified, local_learned_below_threshold_until_0_5_verified, local_learned_above_threshold_by_0_9_verified, local_probe_gap_exceeds_cycle_verified, local_probe_aux_cycle_ends_verified, local_reserve_gate_stays_open_verified, local_A_learning_complete_before_first_response_verified, local_A_quiescent_before_measurement_verified, local_B_quiescent_before_measurement_verified, birth_slow_decay_dominates_noise_verified, protected_arrival_after_FAST_verified, entire_protected_MARK_and_ERROR_before_reopen_verified, protected_input_reopens_by_deadline_verified, protected_aux_cycle_before_deadline_verified, protected_return_before_next_input_verified, recovery_cap_not_reached_verified, unused_port1_birth_gain_below_caps_verified, warmup_returns_before_entry_cut_verified, entry_charge_radius_inside_local_section_verified, entry_aux_band_below_threshold_verified, no_noise_positive_residual_verified⟩

end KernelR.Robust.Evidence.Birth7
