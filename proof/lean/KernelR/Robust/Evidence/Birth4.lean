import KernelR.Intervals

/-! Generated rational endpoint checks; analytic enclosure membership is separate. -/
namespace KernelR.Robust.Evidence.Birth4
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def local_epsilon : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_epsilon_valid : local_epsilon.Valid := by norm_num [RationalBox.Valid, local_epsilon]

def local_nu : RationalBox := ⟨(3 / 2000 : ℚ), (3 / 2000 : ℚ)⟩
theorem local_nu_valid : local_nu.Valid := by norm_num [RationalBox.Valid, local_nu]

def local_alpha : RationalBox := ⟨(1 / 20 : ℚ), (1 / 20 : ℚ)⟩
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

def local_b : RationalBox := ⟨(112483331589713378828884611039670302591 / 625000000000000000000000000000000000000 : ℚ), (112516668410286621171115388960329697409 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem local_b_valid : local_b.Valid := by norm_num [RationalBox.Valid, local_b]

def local_h_increases_through_raw_window_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_h_increases_through_raw_window_left_valid : local_h_increases_through_raw_window_left.Valid := by norm_num [RationalBox.Valid, local_h_increases_through_raw_window_left]

def local_h_increases_through_raw_window_right : RationalBox := ⟨(5753062894644089006539049196938423108761 / 5000000000000000000000000000000000000000 : ℚ), (11506125789288178013078098393876846217523 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_h_increases_through_raw_window_right_valid : local_h_increases_through_raw_window_right.Valid := by norm_num [RationalBox.Valid, local_h_increases_through_raw_window_right]

def local_aux_rest_deviation : RationalBox := ⟨(301 / 100000 : ℚ), (301 / 100000 : ℚ)⟩
theorem local_aux_rest_deviation_valid : local_aux_rest_deviation.Valid := by norm_num [RationalBox.Valid, local_aux_rest_deviation]

def local_aux_rest_below_threshold_left : RationalBox := ⟨(2801 / 100000 : ℚ), (2801 / 100000 : ℚ)⟩
theorem local_aux_rest_below_threshold_left_valid : local_aux_rest_below_threshold_left.Valid := by norm_num [RationalBox.Valid, local_aux_rest_below_threshold_left]

def local_aux_rest_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_rest_below_threshold_right_valid : local_aux_rest_below_threshold_right.Valid := by norm_num [RationalBox.Valid, local_aux_rest_below_threshold_right]

def local_aux_below_threshold_until_0_015_left : RationalBox := ⟨(1095767095645744992988829115449342530037 / 1250000000000000000000000000000000000000 : ℚ), (8766136765165959943910632923594740240297 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_below_threshold_until_0_015_left_valid : local_aux_below_threshold_until_0_015_left.Valid := by norm_num [RationalBox.Valid, local_aux_below_threshold_until_0_015_left]

def local_aux_below_threshold_until_0_015_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_below_threshold_until_0_015_right_valid : local_aux_below_threshold_until_0_015_right.Valid := by norm_num [RationalBox.Valid, local_aux_below_threshold_until_0_015_right]

def local_aux_above_threshold_by_0_03_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_above_threshold_by_0_03_left_valid : local_aux_above_threshold_by_0_03_left.Valid := by norm_num [RationalBox.Valid, local_aux_above_threshold_by_0_03_left]

def local_aux_above_threshold_by_0_03_right : RationalBox := ⟨(1260664745664130009877490731692562602313 / 1000000000000000000000000000000000000000 : ℚ), (12606647456641300098774907316925626023131 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_above_threshold_by_0_03_right_valid : local_aux_above_threshold_by_0_03_right.Valid := by norm_num [RationalBox.Valid, local_aux_above_threshold_by_0_03_right]

def local_decay_1_0_8_dominates_noise_left : RationalBox := ⟨(1493806705908183262297682416026130733 / 10000000000000000000000000000000000000000 : ℚ), (746903352954091631148841208013065367 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_1_0_8_dominates_noise_left_valid : local_decay_1_0_8_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_8_dominates_noise_left]

def local_decay_1_0_8_dominates_noise_right : RationalBox := ⟨(4 / 5 : ℚ), (4 / 5 : ℚ)⟩
theorem local_decay_1_0_8_dominates_noise_right_valid : local_decay_1_0_8_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_8_dominates_noise_right]

def local_decay_0_8_0_1_dominates_noise_left : RationalBox := ⟨(8495870796346117843341778677011142587 / 10000000000000000000000000000000000000000 : ℚ), (2123967699086529460835444669252785647 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_8_0_1_dominates_noise_left_valid : local_decay_0_8_0_1_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_8_0_1_dominates_noise_left]

def local_decay_0_8_0_1_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_decay_0_8_0_1_dominates_noise_right_valid : local_decay_0_8_0_1_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_8_0_1_dominates_noise_right]

def local_decay_0_1_0_025_dominates_noise_left : RationalBox := ⟨(1803368801111204259199905851252365171 / 10000000000000000000000000000000000000000 : ℚ), (450842200277801064799976462813091293 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_1_0_025_dominates_noise_left_valid : local_decay_0_1_0_025_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_1_0_025_dominates_noise_left]

def local_decay_0_1_0_025_dominates_noise_right : RationalBox := ⟨(1 / 40 : ℚ), (1 / 40 : ℚ)⟩
theorem local_decay_0_1_0_025_dominates_noise_right_valid : local_decay_0_1_0_025_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_1_0_025_dominates_noise_right]

def local_mark_duration : RationalBox := ⟨(227241611004244796418099214407804049 / 12500000000000000000000000000000000000 : ℚ), (222259419447918317128297820366878057621 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_duration_valid : local_mark_duration.Valid := by norm_num [RationalBox.Valid, local_mark_duration]

def local_silent_duration : RationalBox := ⟨(4804143703704139847118956136489892049153 / 5000000000000000000000000000000000000000 : ℚ), (11820085052281713985146159771978124084819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_duration_valid : local_silent_duration.Valid := by norm_num [RationalBox.Valid, local_silent_duration]

def local_error_duration : RationalBox := ⟨(679649127550149386314502213829264410403 / 5000000000000000000000000000000000000000 : ℚ), (334640083529539614183248578253146540067 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_duration_valid : local_error_duration.Valid := by norm_num [RationalBox.Valid, local_error_duration]

def local_mark_end : RationalBox := ⟨(414741611004244796418099214407804049 / 12500000000000000000000000000000000000 : ℚ), (522259419447918317128297820366878057621 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_end_valid : local_mark_end.Valid := by norm_num [RationalBox.Valid, local_mark_end]

def local_error_start : RationalBox := ⟨(4970040348105837765686195822253013668753 / 5000000000000000000000000000000000000000 : ℚ), (12342344471729632302274457592345002142439 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_start_valid : local_error_start.Valid := by norm_num [RationalBox.Valid, local_error_start]

def local_aux_finish : RationalBox := ⟨(11299378951311974304001396072164556158313 / 10000000000000000000000000000000000000000 : ℚ), (7007772444688665186595350241805367421387 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_finish_valid : local_aux_finish.Valid := by norm_num [RationalBox.Valid, local_aux_finish]

def local_gain_log_dose : RationalBox := ⟨(1195984318997645524629801017060962241519 / 2000000000000000000000000000000000000000 : ℚ), (1204015681002354475370198982939037758481 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_log_dose_valid : local_gain_log_dose.Valid := by norm_num [RationalBox.Valid, local_gain_log_dose]

def local_initial_gain : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_initial_gain_valid : local_initial_gain.Valid := by norm_num [RationalBox.Valid, local_initial_gain]

def local_learned_gain : RationalBox := ⟨(1127485627319296029966383952190571845289 / 625000000000000000000000000000000000000 : ℚ), (9129387717125600929115173948984023290419 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_gain_valid : local_learned_gain.Valid := by norm_num [RationalBox.Valid, local_learned_gain]

def local_decay_1_0_25_dominates_noise_left : RationalBox := ⟨(1082021280666722555519943510751419103 / 1000000000000000000000000000000000000000 : ℚ), (10820212806667225555199435107514191031 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_1_0_25_dominates_noise_left_valid : local_decay_1_0_25_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_25_dominates_noise_left]

def local_decay_1_0_25_dominates_noise_right : RationalBox := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem local_decay_1_0_25_dominates_noise_right_valid : local_decay_1_0_25_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_25_dominates_noise_right]

def local_decay_0_25_0_1_dominates_noise_left : RationalBox := ⟨(83345682133559293138469990392704026923 / 10000000000000000000000000000000000000000 : ℚ), (20836420533389823284617497598176006731 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_25_0_1_dominates_noise_left_valid : local_decay_0_25_0_1_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_25_0_1_dominates_noise_left]

def local_decay_0_25_0_1_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_decay_0_25_0_1_dominates_noise_right_valid : local_decay_0_25_0_1_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_25_0_1_dominates_noise_right]

def local_min_input_gap : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_min_input_gap_valid : local_min_input_gap.Valid := by norm_num [RationalBox.Valid, local_min_input_gap]

def local_fast_duration : RationalBox := ⟨(9976647747599025414441940102112403596681 / 10000000000000000000000000000000000000000 : ℚ), (2004695786694546693075760792266279647467 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_fast_duration_valid : local_fast_duration.Valid := by norm_num [RationalBox.Valid, local_fast_duration]

def local_slow_duration : RationalBox := ⟨(6034136959066484600369135824059662855783 / 1250000000000000000000000000000000000000 : ℚ), (53864031737819950195316545296520257748269 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_slow_duration_valid : local_slow_duration.Valid := by norm_num [RationalBox.Valid, local_slow_duration]

def local_main_reopen_bound : RationalBox := ⟨(36443755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (72887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopen_bound_valid : local_main_reopen_bound.Valid := by norm_num [RationalBox.Valid, local_main_reopen_bound]

def local_aux_cycle_ends_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_cycle_ends_after_raw_pulse_left_valid : local_aux_cycle_ends_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_after_raw_pulse_left]

def local_aux_cycle_ends_after_raw_pulse_right : RationalBox := ⟨(11299378951311974304001396072164556158313 / 10000000000000000000000000000000000000000 : ℚ), (5649689475655987152000698036082278079157 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_cycle_ends_after_raw_pulse_right_valid : local_aux_cycle_ends_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_after_raw_pulse_right]

def local_aux_cycle_ends_before_next_input_left : RationalBox := ⟨(14015544889377330373190700483610734842773 / 10000000000000000000000000000000000000000 : ℚ), (7007772444688665186595350241805367421387 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_cycle_ends_before_next_input_left_valid : local_aux_cycle_ends_before_next_input_left.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_before_next_input_left]

def local_aux_cycle_ends_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_aux_cycle_ends_before_next_input_right_valid : local_aux_cycle_ends_before_next_input_right.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_before_next_input_right]

def local_learned_gain_below_all_caps_left : RationalBox := ⟨(1127485627319296029966383952190571845289 / 625000000000000000000000000000000000000 : ℚ), (9129387717125600929115173948984023290419 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_gain_below_all_caps_left_valid : local_learned_gain_below_all_caps_left.Valid := by norm_num [RationalBox.Valid, local_learned_gain_below_all_caps_left]

def local_learned_gain_below_all_caps_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem local_learned_gain_below_all_caps_right_valid : local_learned_gain_below_all_caps_right.Valid := by norm_num [RationalBox.Valid, local_learned_gain_below_all_caps_right]

def local_mark_finishes_before_any_main_firing_left : RationalBox := ⟨(26112970972395915856414891018343902881 / 500000000000000000000000000000000000000 : ℚ), (522259419447918317128297820366878057621 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_finishes_before_any_main_firing_left_valid : local_mark_finishes_before_any_main_firing_left.Valid := by norm_num [RationalBox.Valid, local_mark_finishes_before_any_main_firing_left]

def local_mark_finishes_before_any_main_firing_right : RationalBox := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem local_mark_finishes_before_any_main_firing_right_valid : local_mark_finishes_before_any_main_firing_right.Valid := by norm_num [RationalBox.Valid, local_mark_finishes_before_any_main_firing_right]

def local_main_fires_before_error_begins_left : RationalBox := ⟨(9 / 10 : ℚ), (9 / 10 : ℚ)⟩
theorem local_main_fires_before_error_begins_left_valid : local_main_fires_before_error_begins_left.Valid := by norm_num [RationalBox.Valid, local_main_fires_before_error_begins_left]

def local_main_fires_before_error_begins_right : RationalBox := ⟨(4970040348105837765686195822253013668753 / 5000000000000000000000000000000000000000 : ℚ), (9940080696211675531372391644506027337507 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_fires_before_error_begins_right_valid : local_main_fires_before_error_begins_right.Valid := by norm_num [RationalBox.Valid, local_main_fires_before_error_begins_right]

def local_error_finishes_during_main_fast_left : RationalBox := ⟨(14015544889377330373190700483610734842773 / 10000000000000000000000000000000000000000 : ℚ), (7007772444688665186595350241805367421387 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_finishes_during_main_fast_left_valid : local_error_finishes_during_main_fast_left.Valid := by norm_num [RationalBox.Valid, local_error_finishes_during_main_fast_left]

def local_error_finishes_during_main_fast_right : RationalBox := ⟨(14976647747599025414441940102112403596681 / 10000000000000000000000000000000000000000 : ℚ), (7488323873799512707220970051056201798341 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_finishes_during_main_fast_right_valid : local_error_finishes_during_main_fast_right.Valid := by norm_num [RationalBox.Valid, local_error_finishes_during_main_fast_right]

def local_main_reopens_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_main_reopens_after_raw_pulse_left_valid : local_main_reopens_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, local_main_reopens_after_raw_pulse_left]

def local_main_reopens_after_raw_pulse_right : RationalBox := ⟨(31624871710065451108697513347294853221473 / 5000000000000000000000000000000000000000 : ℚ), (63249743420130902217395026694589706442947 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopens_after_raw_pulse_right_valid : local_main_reopens_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, local_main_reopens_after_raw_pulse_right]

def local_main_reopens_before_next_input_left : RationalBox := ⟨(36443755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (72887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopens_before_next_input_left_valid : local_main_reopens_before_next_input_left.Valid := by norm_num [RationalBox.Valid, local_main_reopens_before_next_input_left]

def local_main_reopens_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_main_reopens_before_next_input_right_valid : local_main_reopens_before_next_input_right.Valid := by norm_num [RationalBox.Valid, local_main_reopens_before_next_input_right]

def local_arbitrary_initial_silence_inside_section_left : RationalBox := ⟨(301 / 100000 : ℚ), (301 / 100000 : ℚ)⟩
theorem local_arbitrary_initial_silence_inside_section_left_valid : local_arbitrary_initial_silence_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_arbitrary_initial_silence_inside_section_left]

def local_arbitrary_initial_silence_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_arbitrary_initial_silence_inside_section_right_valid : local_arbitrary_initial_silence_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_arbitrary_initial_silence_inside_section_right]

def local_rest_noise_inside_section_left : RationalBox := ⟨(3 / 1000 : ℚ), (3 / 1000 : ℚ)⟩
theorem local_rest_noise_inside_section_left_valid : local_rest_noise_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_rest_noise_inside_section_left]

def local_rest_noise_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_rest_noise_inside_section_right_valid : local_rest_noise_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_rest_noise_inside_section_right]

def local_gain_before_0 : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_0_valid : local_gain_before_0.Valid := by norm_num [RationalBox.Valid, local_gain_before_0]

def local_peak_bound_0 : RationalBox := ⟨(3071666219827193383274134334287322912463 / 10000000000000000000000000000000000000000 : ℚ), (3077113121158389794491152780152238039107 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_0_valid : local_peak_bound_0.Valid := by norm_num [RationalBox.Valid, local_peak_bound_0]

def local_carry_bound_0 : RationalBox := ⟨(5516360828276874632078548254295764651 / 500000000000000000000000000000000000000 : ℚ), (110538415849792185570595069633065470213 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_0_valid : local_carry_bound_0.Valid := by norm_num [RationalBox.Valid, local_carry_bound_0]

def local_silent_0_no_first_crossing_left : RationalBox := ⟨(3071666219827193383274134334287322912463 / 10000000000000000000000000000000000000000 : ℚ), (3077113121158389794491152780152238039107 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_0_no_first_crossing_left_valid : local_silent_0_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_no_first_crossing_left]

def local_silent_0_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_0_no_first_crossing_right_valid : local_silent_0_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_no_first_crossing_right]

def local_silent_0_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(103 / 1000 : ℚ), (103 / 1000 : ℚ)⟩
theorem local_silent_0_stays_below_threshold_after_raw_end_left_valid : local_silent_0_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_stays_below_threshold_after_raw_end_left]

def local_silent_0_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_0_stays_below_threshold_after_raw_end_right_valid : local_silent_0_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_stays_below_threshold_after_raw_end_right]

def local_silent_0_excess_returns_inside_section_left : RationalBox := ⟨(5516360828276874632078548254295764651 / 500000000000000000000000000000000000000 : ℚ), (110538415849792185570595069633065470213 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_0_excess_returns_inside_section_left_valid : local_silent_0_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_excess_returns_inside_section_left]

def local_silent_0_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_0_excess_returns_inside_section_right_valid : local_silent_0_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_excess_returns_inside_section_right]

def local_gain_before_1 : RationalBox := ⟨(1091067457395537240285213370475036123869 / 2000000000000000000000000000000000000000 : ℚ), (5477397772628526562519882170139110391963 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_1_valid : local_gain_before_1.Valid := by norm_num [RationalBox.Valid, local_gain_before_1]

def local_peak_bound_1 : RationalBox := ⟨(1130571951718161807425497192292295216749 / 2500000000000000000000000000000000000000 : ℚ), (4532232655830067937744416504369888341803 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_1_valid : local_peak_bound_1.Valid := by norm_num [RationalBox.Valid, local_peak_bound_1]

def local_carry_bound_1 : RationalBox := ⟨(166573919466820340454680097563876933953 / 10000000000000000000000000000000000000000 : ℚ), (83479761553575227468645673502219178251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_1_valid : local_carry_bound_1.Valid := by norm_num [RationalBox.Valid, local_carry_bound_1]

def local_silent_1_no_first_crossing_left : RationalBox := ⟨(1130571951718161807425497192292295216749 / 2500000000000000000000000000000000000000 : ℚ), (4532232655830067937744416504369888341803 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_1_no_first_crossing_left_valid : local_silent_1_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_no_first_crossing_left]

def local_silent_1_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_1_no_first_crossing_right_valid : local_silent_1_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_no_first_crossing_right]

def local_silent_1_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(103 / 1000 : ℚ), (103 / 1000 : ℚ)⟩
theorem local_silent_1_stays_below_threshold_after_raw_end_left_valid : local_silent_1_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_stays_below_threshold_after_raw_end_left]

def local_silent_1_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_1_stays_below_threshold_after_raw_end_right_valid : local_silent_1_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_stays_below_threshold_after_raw_end_right]

def local_silent_1_excess_returns_inside_section_left : RationalBox := ⟨(166573919466820340454680097563876933953 / 10000000000000000000000000000000000000000 : ℚ), (83479761553575227468645673502219178251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_1_excess_returns_inside_section_left_valid : local_silent_1_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_excess_returns_inside_section_left]

def local_silent_1_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_1_excess_returns_inside_section_right_valid : local_silent_1_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_excess_returns_inside_section_right]

def local_gain_before_2 : RationalBox := ⟨(4960167087204374811788768291109887302021 / 5000000000000000000000000000000000000000 : ℚ), (5000264390372072888168614201214199441399 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_2_valid : local_gain_before_2.Valid := by norm_num [RationalBox.Valid, local_gain_before_2]

def local_peak_bound_2 : RationalBox := ⟨(7170805138170117000610605821416795034569 / 10000000000000000000000000000000000000000 : ℚ), (7188962254440880871074917117483251119763 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_2_valid : local_peak_bound_2.Valid := by norm_num [RationalBox.Valid, local_peak_bound_2]

def local_carry_bound_2 : RationalBox := ⟨(269268080916466169935153112539439769999 / 10000000000000000000000000000000000000000 : ℚ), (53994421743274701907025472516445328859 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_2_valid : local_carry_bound_2.Valid := by norm_num [RationalBox.Valid, local_carry_bound_2]

def local_silent_2_no_first_crossing_left : RationalBox := ⟨(7170805138170117000610605821416795034569 / 10000000000000000000000000000000000000000 : ℚ), (7188962254440880871074917117483251119763 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_2_no_first_crossing_left_valid : local_silent_2_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_no_first_crossing_left]

def local_silent_2_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_2_no_first_crossing_right_valid : local_silent_2_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_no_first_crossing_right]

def local_silent_2_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(103 / 1000 : ℚ), (103 / 1000 : ℚ)⟩
theorem local_silent_2_stays_below_threshold_after_raw_end_left_valid : local_silent_2_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_stays_below_threshold_after_raw_end_left]

def local_silent_2_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_2_stays_below_threshold_after_raw_end_right_valid : local_silent_2_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_stays_below_threshold_after_raw_end_right]

def local_silent_2_excess_returns_inside_section_left : RationalBox := ⟨(269268080916466169935153112539439769999 / 10000000000000000000000000000000000000000 : ℚ), (53994421743274701907025472516445328859 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_2_excess_returns_inside_section_left_valid : local_silent_2_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_excess_returns_inside_section_left]

def local_silent_2_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_2_excess_returns_inside_section_right_valid : local_silent_2_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_excess_returns_inside_section_right]

def local_learned_start_excess : RationalBox := ⟨(269268080916466169935153112539439769999 / 10000000000000000000000000000000000000000 : ℚ), (53994421743274701907025472516445328859 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_start_excess_valid : local_learned_start_excess.Valid := by norm_num [RationalBox.Valid, local_learned_start_excess]

def local_learned_upper_at_0_5 : RationalBox := ⟨(9637271061838880887037583637596791278733 / 10000000000000000000000000000000000000000 : ℚ), (9637975089638788226637557887639578153029 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_upper_at_0_5_valid : local_learned_upper_at_0_5.Valid := by norm_num [RationalBox.Valid, local_learned_upper_at_0_5]

def local_learned_lower_at_0_9 : RationalBox := ⟨(10350659495509052259152913891764843939853 / 10000000000000000000000000000000000000000 : ℚ), (5175329747754526129576456945882421969927 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_lower_at_0_9_valid : local_learned_lower_at_0_9.Valid := by norm_num [RationalBox.Valid, local_learned_lower_at_0_9]

def local_learned_below_threshold_until_0_5_left : RationalBox := ⟨(9637271061838880887037583637596791278733 / 10000000000000000000000000000000000000000 : ℚ), (9637975089638788226637557887639578153029 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_below_threshold_until_0_5_left_valid : local_learned_below_threshold_until_0_5_left.Valid := by norm_num [RationalBox.Valid, local_learned_below_threshold_until_0_5_left]

def local_learned_below_threshold_until_0_5_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_learned_below_threshold_until_0_5_right_valid : local_learned_below_threshold_until_0_5_right.Valid := by norm_num [RationalBox.Valid, local_learned_below_threshold_until_0_5_right]

def local_learned_above_threshold_by_0_9_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_learned_above_threshold_by_0_9_left_valid : local_learned_above_threshold_by_0_9_left.Valid := by norm_num [RationalBox.Valid, local_learned_above_threshold_by_0_9_left]

def local_learned_above_threshold_by_0_9_right : RationalBox := ⟨(10350659495509052259152913891764843939853 / 10000000000000000000000000000000000000000 : ℚ), (5175329747754526129576456945882421969927 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_above_threshold_by_0_9_right_valid : local_learned_above_threshold_by_0_9_right.Valid := by norm_num [RationalBox.Valid, local_learned_above_threshold_by_0_9_right]

def local_probe_gap_exceeds_cycle_left : RationalBox := ⟨(36443755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (72887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_probe_gap_exceeds_cycle_left_valid : local_probe_gap_exceeds_cycle_left.Valid := by norm_num [RationalBox.Valid, local_probe_gap_exceeds_cycle_left]

def local_probe_gap_exceeds_cycle_right : RationalBox := ⟨(20 / 1 : ℚ), (20 / 1 : ℚ)⟩
theorem local_probe_gap_exceeds_cycle_right_valid : local_probe_gap_exceeds_cycle_right.Valid := by norm_num [RationalBox.Valid, local_probe_gap_exceeds_cycle_right]

def local_probe_aux_cycle_ends_left : RationalBox := ⟨(14015544889377330373190700483610734842773 / 10000000000000000000000000000000000000000 : ℚ), (7007772444688665186595350241805367421387 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_probe_aux_cycle_ends_left_valid : local_probe_aux_cycle_ends_left.Valid := by norm_num [RationalBox.Valid, local_probe_aux_cycle_ends_left]

def local_probe_aux_cycle_ends_right : RationalBox := ⟨(20 / 1 : ℚ), (20 / 1 : ℚ)⟩
theorem local_probe_aux_cycle_ends_right_valid : local_probe_aux_cycle_ends_right.Valid := by norm_num [RationalBox.Valid, local_probe_aux_cycle_ends_right]

def local_work_bound : RationalBox := ⟨(1367647506553689624688226293649847134969251 / 5000000000000000000000000000000000000000 : ℚ), (2735295013107379249376452587299694269938503 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_work_bound_valid : local_work_bound.Valid := by norm_num [RationalBox.Valid, local_work_bound]

def local_reserve_gate_stays_open_left : RationalBox := ⟨(1367647506553689624688226293649847134969251 / 5000000000000000000000000000000000000000 : ℚ), (2735295013107379249376452587299694269938503 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_reserve_gate_stays_open_left_valid : local_reserve_gate_stays_open_left.Valid := by norm_num [RationalBox.Valid, local_reserve_gate_stays_open_left]

def local_reserve_gate_stays_open_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem local_reserve_gate_stays_open_right_valid : local_reserve_gate_stays_open_right.Valid := by norm_num [RationalBox.Valid, local_reserve_gate_stays_open_right]

def local_A_gain_complete_by : RationalBox := ⟨(427015544889377330373190700483610734842773 / 10000000000000000000000000000000000000000 : ℚ), (213507772444688665186595350241805367421387 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_gain_complete_by_valid : local_A_gain_complete_by.Valid := by norm_num [RationalBox.Valid, local_A_gain_complete_by]

def local_A_first_emission : RationalBox := ⟨(493 / 10 : ℚ), (251 / 5 : ℚ)⟩
theorem local_A_first_emission_valid : local_A_first_emission.Valid := by norm_num [RationalBox.Valid, local_A_first_emission]

def local_A_last_return_by : RationalBox := ⟨(642943755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (1285887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_last_return_by_valid : local_A_last_return_by.Valid := by norm_num [RationalBox.Valid, local_A_last_return_by]

def local_B_last_return_by : RationalBox := ⟨(636443755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (1272887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_B_last_return_by_valid : local_B_last_return_by.Valid := by norm_num [RationalBox.Valid, local_B_last_return_by]

def local_A_learning_complete_before_first_response_left : RationalBox := ⟨(427015544889377330373190700483610734842773 / 10000000000000000000000000000000000000000 : ℚ), (213507772444688665186595350241805367421387 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_learning_complete_before_first_response_left_valid : local_A_learning_complete_before_first_response_left.Valid := by norm_num [RationalBox.Valid, local_A_learning_complete_before_first_response_left]

def local_A_learning_complete_before_first_response_right : RationalBox := ⟨(493 / 10 : ℚ), (493 / 10 : ℚ)⟩
theorem local_A_learning_complete_before_first_response_right_valid : local_A_learning_complete_before_first_response_right.Valid := by norm_num [RationalBox.Valid, local_A_learning_complete_before_first_response_right]

def local_A_quiescent_before_measurement_left : RationalBox := ⟨(642943755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (1285887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_quiescent_before_measurement_left_valid : local_A_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, local_A_quiescent_before_measurement_left]

def local_A_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem local_A_quiescent_before_measurement_right_valid : local_A_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, local_A_quiescent_before_measurement_right]

def local_B_quiescent_before_measurement_left : RationalBox := ⟨(636443755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (1272887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_B_quiescent_before_measurement_left_valid : local_B_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, local_B_quiescent_before_measurement_left]

def local_B_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem local_B_quiescent_before_measurement_right_valid : local_B_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, local_B_quiescent_before_measurement_right]

def birth_slow_decay_dominates_noise_left : RationalBox := ⟨(93761720215026878359794974371796474559 / 5000000000000000000000000000000000000000 : ℚ), (187523440430053756719589948743592949119 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem birth_slow_decay_dominates_noise_left_valid : birth_slow_decay_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, birth_slow_decay_dominates_noise_left]

def birth_slow_decay_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem birth_slow_decay_dominates_noise_right_valid : birth_slow_decay_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, birth_slow_decay_dominates_noise_right]

def protected_arrival_after_FAST_left : RationalBox := ⟨(9511739466736366732689401980665699118667 / 5000000000000000000000000000000000000000 : ℚ), (3804695786694546693075760792266279647467 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_arrival_after_FAST_left_valid : protected_arrival_after_FAST_left.Valid := by norm_num [RationalBox.Valid, protected_arrival_after_FAST_left]

def protected_arrival_after_FAST_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem protected_arrival_after_FAST_right_valid : protected_arrival_after_FAST_right.Valid := by norm_num [RationalBox.Valid, protected_arrival_after_FAST_right]

def entire_protected_MARK_and_ERROR_before_reopen_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem entire_protected_MARK_and_ERROR_before_reopen_left_valid : entire_protected_MARK_and_ERROR_before_reopen_left.Valid := by norm_num [RationalBox.Valid, entire_protected_MARK_and_ERROR_before_reopen_left]

def entire_protected_MARK_and_ERROR_before_reopen_right : RationalBox := ⟨(538447224125499643070135861270984929307 / 5000000000000000000000000000000000000000 : ℚ), (215378889650199857228054344508393971723 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem entire_protected_MARK_and_ERROR_before_reopen_right_valid : entire_protected_MARK_and_ERROR_before_reopen_right.Valid := by norm_num [RationalBox.Valid, entire_protected_MARK_and_ERROR_before_reopen_right]

def protected_input_reopens_by_deadline_left : RationalBox := ⟨(22490054194794873861220208950391797451 / 250000000000000000000000000000000000000 : ℚ), (899602167791794954448808358015671898041 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_input_reopens_by_deadline_left_valid : protected_input_reopens_by_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_by_deadline_left]

def protected_input_reopens_by_deadline_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem protected_input_reopens_by_deadline_right_valid : protected_input_reopens_by_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_by_deadline_right]

def protected_aux_cycle_before_deadline_left : RationalBox := ⟨(14015544889377330373190700483610734842773 / 10000000000000000000000000000000000000000 : ℚ), (7007772444688665186595350241805367421387 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_aux_cycle_before_deadline_left_valid : protected_aux_cycle_before_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_aux_cycle_before_deadline_left]

def protected_aux_cycle_before_deadline_right : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_aux_cycle_before_deadline_right_valid : protected_aux_cycle_before_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_aux_cycle_before_deadline_right]

def protected_return_before_next_input_left : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_return_before_next_input_left_valid : protected_return_before_next_input_left.Valid := by norm_num [RationalBox.Valid, protected_return_before_next_input_left]

def protected_return_before_next_input_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem protected_return_before_next_input_right_valid : protected_return_before_next_input_right.Valid := by norm_num [RationalBox.Valid, protected_return_before_next_input_right]

def recovery_cap_not_reached_left : RationalBox := ⟨(112483331589713378828884611039670302591 / 625000000000000000000000000000000000000 : ℚ), (112516668410286621171115388960329697409 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem recovery_cap_not_reached_left_valid : recovery_cap_not_reached_left.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_left]

def recovery_cap_not_reached_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem recovery_cap_not_reached_right_valid : recovery_cap_not_reached_right.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_right]

def unused_port1_birth_gain_below_caps_left : RationalBox := ⟨(5999940000299999000002499995000008333321 / 5000000000000000000000000000000000000000 : ℚ), (12000120000600002000005000010000016666691 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem unused_port1_birth_gain_below_caps_left_valid : unused_port1_birth_gain_below_caps_left.Valid := by norm_num [RationalBox.Valid, unused_port1_birth_gain_below_caps_left]

def unused_port1_birth_gain_below_caps_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem unused_port1_birth_gain_below_caps_right_valid : unused_port1_birth_gain_below_caps_right.Valid := by norm_num [RationalBox.Valid, unused_port1_birth_gain_below_caps_right]

def warmup_returns_before_entry_cut_left : RationalBox := ⟨(636443755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (1272887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem warmup_returns_before_entry_cut_left_valid : warmup_returns_before_entry_cut_left.Valid := by norm_num [RationalBox.Valid, warmup_returns_before_entry_cut_left]

def warmup_returns_before_entry_cut_right : RationalBox := ⟨(1599 / 10 : ℚ), (1599 / 10 : ℚ)⟩
theorem warmup_returns_before_entry_cut_right_valid : warmup_returns_before_entry_cut_right.Valid := by norm_num [RationalBox.Valid, warmup_returns_before_entry_cut_right]

def entry_charge_radius_inside_local_section_left : RationalBox := ⟨(301 / 100000 : ℚ), (301 / 100000 : ℚ)⟩
theorem entry_charge_radius_inside_local_section_left_valid : entry_charge_radius_inside_local_section_left.Valid := by norm_num [RationalBox.Valid, entry_charge_radius_inside_local_section_left]

def entry_charge_radius_inside_local_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem entry_charge_radius_inside_local_section_right_valid : entry_charge_radius_inside_local_section_right.Valid := by norm_num [RationalBox.Valid, entry_charge_radius_inside_local_section_right]

def entry_aux_band_below_threshold_left : RationalBox := ⟨(2801 / 100000 : ℚ), (2801 / 100000 : ℚ)⟩
theorem entry_aux_band_below_threshold_left_valid : entry_aux_band_below_threshold_left.Valid := by norm_num [RationalBox.Valid, entry_aux_band_below_threshold_left]

def entry_aux_band_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem entry_aux_band_below_threshold_right_valid : entry_aux_band_below_threshold_right.Valid := by norm_num [RationalBox.Valid, entry_aux_band_below_threshold_right]

def birth_recovery : RationalBox := ⟨(7999 / 100000 : ℚ), (8001 / 100000 : ℚ)⟩
theorem birth_recovery_valid : birth_recovery.Valid := by norm_num [RationalBox.Valid, birth_recovery]

def protected_MARK_dose : RationalBox := ⟨(62489581589713378828884611039670302591 / 625000000000000000000000000000000000000 : ℚ), (62510418410286621171115388960329697409 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem protected_MARK_dose_valid : protected_MARK_dose.Valid := by norm_num [RationalBox.Valid, protected_MARK_dose]

def entry_recovery : RationalBox := ⟨(112483331589713378828884611039670302591 / 625000000000000000000000000000000000000 : ℚ), (112516668410286621171115388960329697409 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem entry_recovery_valid : entry_recovery.Valid := by norm_num [RationalBox.Valid, entry_recovery]

def entry_charge_radius : RationalBox := ⟨(301 / 100000 : ℚ), (301 / 100000 : ℚ)⟩
theorem entry_charge_radius_valid : entry_charge_radius.Valid := by norm_num [RationalBox.Valid, entry_charge_radius]

def entry_q : RationalBox := ⟨(9699 / 100000 : ℚ), (10301 / 100000 : ℚ)⟩
theorem entry_q_valid : entry_q.Valid := by norm_num [RationalBox.Valid, entry_q]

def entry_m : RationalBox := ⟨(2199 / 100000 : ℚ), (2801 / 100000 : ℚ)⟩
theorem entry_m_valid : entry_m.Valid := by norm_num [RationalBox.Valid, entry_m]

def q_lower_at_protected_arrival : RationalBox := ⟨(281976228698185262870367781097844155831 / 2000000000000000000000000000000000000000 : ℚ), (352470285872731578587959726372305194789 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem q_lower_at_protected_arrival_valid : q_lower_at_protected_arrival.Valid := by norm_num [RationalBox.Valid, q_lower_at_protected_arrival]

def q_lower_through_protected_cycle : RationalBox := ⟨(538447224125499643070135861270984929307 / 5000000000000000000000000000000000000000 : ℚ), (215378889650199857228054344508393971723 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem q_lower_through_protected_cycle_valid : q_lower_through_protected_cycle.Valid := by norm_num [RationalBox.Valid, q_lower_through_protected_cycle]

def q_upper_at_reopen_deadline : RationalBox := ⟨(22490054194794873861220208950391797451 / 250000000000000000000000000000000000000 : ℚ), (899602167791794954448808358015671898041 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem q_upper_at_reopen_deadline_valid : q_upper_at_reopen_deadline.Valid := by norm_num [RationalBox.Valid, q_upper_at_reopen_deadline]

def protected_reopen_deadline : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_reopen_deadline_valid : protected_reopen_deadline.Valid := by norm_num [RationalBox.Valid, protected_reopen_deadline]

def last_warmup_return : RationalBox := ⟨(636443755335646341830347674628925827992801 / 5000000000000000000000000000000000000000 : ℚ), (1272887510671292683660695349257851655985603 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

end KernelR.Robust.Evidence.Birth4
