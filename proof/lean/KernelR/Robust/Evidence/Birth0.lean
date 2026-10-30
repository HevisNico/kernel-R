import KernelR.Intervals

/-! Generated rational endpoint checks; analytic enclosure membership is separate. -/
namespace KernelR.Robust.Evidence.Birth0
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def local_epsilon : RationalBox := ⟨(3 / 1000 : ℚ), (3 / 1000 : ℚ)⟩
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

def local_cap : RationalBox := ⟨(997 / 250 : ℚ), (1003 / 250 : ℚ)⟩
theorem local_cap_valid : local_cap.Valid := by norm_num [RationalBox.Valid, local_cap]

def local_Lm : RationalBox := ⟨(55618530165066781624749051259726249966119 / 5000000000000000000000000000000000000000 : ℚ), (111906490984076192516796987790382003442363 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_Lm_valid : local_Lm.Valid := by norm_num [RationalBox.Valid, local_Lm]

def local_Ls : RationalBox := ⟨(19558520915611286985537181842277416180319 / 10000000000000000000000000000000000000000 : ℚ), (19676225153819579585249542013845785786219 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_Ls_valid : local_Ls.Valid := by norm_num [RationalBox.Valid, local_Ls]

def local_Le : RationalBox := ⟨(92142365202435396465197390012506938449503 / 10000000000000000000000000000000000000000 : ℚ), (23174220736720838178182793927418369925991 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_Le_valid : local_Le.Valid := by norm_num [RationalBox.Valid, local_Le]

def local_M : RationalBox := ⟨(178636710380294430996383445085097118336969 / 5000000000000000000000000000000000000000 : ℚ), (22463969472346453647112913167045186771813 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem local_M_valid : local_M.Valid := by norm_num [RationalBox.Valid, local_M]

def local_b : RationalBox := ⟨(112484345369549905807531293390262105509 / 625000000000000000000000000000000000000 : ℚ), (112515654630450094192468706609737894491 / 625000000000000000000000000000000000000 : ℚ)⟩
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

def local_aux_below_threshold_until_0_015_left : RationalBox := ⟨(2004460613741240414486901095992164650231 / 2500000000000000000000000000000000000000 : ℚ), (320713698198598466317904175358746344037 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_below_threshold_until_0_015_left_valid : local_aux_below_threshold_until_0_015_left.Valid := by norm_num [RationalBox.Valid, local_aux_below_threshold_until_0_015_left]

def local_aux_below_threshold_until_0_015_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_below_threshold_until_0_015_right_valid : local_aux_below_threshold_until_0_015_right.Valid := by norm_num [RationalBox.Valid, local_aux_below_threshold_until_0_015_right]

def local_aux_above_threshold_by_0_03_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_above_threshold_by_0_03_left_valid : local_aux_above_threshold_by_0_03_left.Valid := by norm_num [RationalBox.Valid, local_aux_above_threshold_by_0_03_left]

def local_aux_above_threshold_by_0_03_right : RationalBox := ⟨(871357004463290013783234902428808968407 / 625000000000000000000000000000000000000 : ℚ), (13941712071412640220531758438860943494513 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_above_threshold_by_0_03_right_valid : local_aux_above_threshold_by_0_03_right.Valid := by norm_num [RationalBox.Valid, local_aux_above_threshold_by_0_03_right]

def local_decay_1_0_8_dominates_noise_left : RationalBox := ⟨(168558931208295503519046411036047851 / 1250000000000000000000000000000000000000 : ℚ), (1348471449666364028152371288288382809 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_1_0_8_dominates_noise_left_valid : local_decay_1_0_8_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_8_dominates_noise_left]

def local_decay_1_0_8_dominates_noise_right : RationalBox := ⟨(4 / 5 : ℚ), (4 / 5 : ℚ)⟩
theorem local_decay_1_0_8_dominates_noise_right_valid : local_decay_1_0_8_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_8_dominates_noise_right]

def local_decay_0_8_0_1_dominates_noise_left : RationalBox := ⟨(958661448935745493857522669171267343 / 1250000000000000000000000000000000000000 : ℚ), (1533858318297192790172036270674027749 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_8_0_1_dominates_noise_left_valid : local_decay_0_8_0_1_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_8_0_1_dominates_noise_left]

def local_decay_0_8_0_1_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_decay_0_8_0_1_dominates_noise_right_valid : local_decay_0_8_0_1_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_8_0_1_dominates_noise_right]

def local_decay_0_1_0_025_dominates_noise_left : RationalBox := ⟨(325583133600819224328969963114770041 / 2000000000000000000000000000000000000000 : ℚ), (813957834002048060822424907786925103 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_1_0_025_dominates_noise_left_valid : local_decay_0_1_0_025_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_1_0_025_dominates_noise_left]

def local_decay_0_1_0_025_dominates_noise_right : RationalBox := ⟨(1 / 40 : ℚ), (1 / 40 : ℚ)⟩
theorem local_decay_0_1_0_025_dominates_noise_right_valid : local_decay_0_1_0_025_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_1_0_025_dominates_noise_right]

def local_mark_duration : RationalBox := ⟨(199371854379606771968073315818486404827 / 10000000000000000000000000000000000000000 : ℚ), (20063211626867610599907434107508247413 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_duration_valid : local_mark_duration.Valid := by norm_num [RationalBox.Valid, local_mark_duration]

def local_silent_duration : RationalBox := ⟨(10534538491562378573921748510534737674337 / 10000000000000000000000000000000000000000 : ℚ), (2133270998625113532947200185944188355059 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_duration_valid : local_silent_duration.Valid := by norm_num [RationalBox.Valid, local_silent_duration]

def local_error_duration : RationalBox := ⟨(372574388486777254813685302784099215609 / 2500000000000000000000000000000000000000 : ℚ), (150983542905095667226823995737721471487 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_duration_valid : local_error_duration.Valid := by norm_num [RationalBox.Valid, local_error_duration]

def local_mark_end : RationalBox := ⟨(349371854379606771968073315818486404827 / 10000000000000000000000000000000000000000 : ℚ), (50063211626867610599907434107508247413 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_end_valid : local_mark_end.Valid := by norm_num [RationalBox.Valid, local_mark_end]

def local_error_start : RationalBox := ⟨(2720977586485496336472455456588306019791 / 2500000000000000000000000000000000000000 : ℚ), (446679484375769750829403010831840969977 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_start_valid : local_error_start.Valid := by norm_num [RationalBox.Valid, local_error_start]

def local_aux_finish : RationalBox := ⟨(15467759874861367956430703796862026177 / 12500000000000000000000000000000000000 : ℚ), (6338411269222600221501657614086619482147 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_finish_valid : local_aux_finish.Valid := by norm_num [RationalBox.Valid, local_aux_finish]

def local_gain_log_dose : RationalBox := ⟨(5981881974851388519932781120511473423421 / 10000000000000000000000000000000000000000 : ℚ), (6018118025148611480067218879488526576579 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_log_dose_valid : local_gain_log_dose.Valid := by norm_num [RationalBox.Valid, local_gain_log_dose]

def local_initial_gain : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_initial_gain_valid : local_initial_gain.Valid := by norm_num [RationalBox.Valid, local_initial_gain]

def local_learned_gain : RationalBox := ⟨(2256297824759438949817044510197386975093 / 1250000000000000000000000000000000000000 : ℚ), (9124020175290357329530678341409593691131 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_gain_valid : local_learned_gain.Valid := by norm_num [RationalBox.Valid, local_learned_gain]

def local_decay_1_0_25_dominates_noise_left : RationalBox := ⟨(1082021280666722555519943510751419103 / 1000000000000000000000000000000000000000 : ℚ), (10820212806667225555199435107514191031 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_1_0_25_dominates_noise_left_valid : local_decay_1_0_25_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_25_dominates_noise_left]

def local_decay_1_0_25_dominates_noise_right : RationalBox := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem local_decay_1_0_25_dominates_noise_right_valid : local_decay_1_0_25_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_25_dominates_noise_right]

def local_decay_0_25_0_1_dominates_noise_left : RationalBox := ⟨(83344930969726397131995676023836524887 / 10000000000000000000000000000000000000000 : ℚ), (10418116371215799641499459502979565611 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_25_0_1_dominates_noise_left_valid : local_decay_0_25_0_1_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_25_0_1_dominates_noise_left]

def local_decay_0_25_0_1_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_decay_0_25_0_1_dominates_noise_right_valid : local_decay_0_25_0_1_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_25_0_1_dominates_noise_right]

def local_min_input_gap : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_min_input_gap_valid : local_min_input_gap.Valid := by norm_num [RationalBox.Valid, local_min_input_gap]

def local_fast_duration : RationalBox := ⟨(9976647747599025414441940102112403596681 / 10000000000000000000000000000000000000000 : ℚ), (2004695786694546693075760792266279647467 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_fast_duration_valid : local_fast_duration.Valid := by norm_num [RationalBox.Valid, local_fast_duration]

def local_slow_duration : RationalBox := ⟨(48273508267487152661085507845684236606091 / 10000000000000000000000000000000000000000 : ℚ), (26931759009909394748023206734158563399291 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_slow_duration_valid : local_slow_duration.Valid := by norm_num [RationalBox.Valid, local_slow_duration]

def local_main_reopen_bound : RationalBox := ⟨(14577399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (18221749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopen_bound_valid : local_main_reopen_bound.Valid := by norm_num [RationalBox.Valid, local_main_reopen_bound]

def local_aux_cycle_ends_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_cycle_ends_after_raw_pulse_left_valid : local_aux_cycle_ends_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_after_raw_pulse_left]

def local_aux_cycle_ends_after_raw_pulse_right : RationalBox := ⟨(15467759874861367956430703796862026177 / 12500000000000000000000000000000000000 : ℚ), (12374207899889094365144563037489620941601 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_cycle_ends_after_raw_pulse_right_valid : local_aux_cycle_ends_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_after_raw_pulse_right]

def local_aux_cycle_ends_before_next_input_left : RationalBox := ⟨(12676822538445200443003315228173238964293 / 10000000000000000000000000000000000000000 : ℚ), (6338411269222600221501657614086619482147 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_cycle_ends_before_next_input_left_valid : local_aux_cycle_ends_before_next_input_left.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_before_next_input_left]

def local_aux_cycle_ends_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_aux_cycle_ends_before_next_input_right_valid : local_aux_cycle_ends_before_next_input_right.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_before_next_input_right]

def local_learned_gain_below_all_caps_left : RationalBox := ⟨(2256297824759438949817044510197386975093 / 1250000000000000000000000000000000000000 : ℚ), (9124020175290357329530678341409593691131 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_gain_below_all_caps_left_valid : local_learned_gain_below_all_caps_left.Valid := by norm_num [RationalBox.Valid, local_learned_gain_below_all_caps_left]

def local_learned_gain_below_all_caps_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem local_learned_gain_below_all_caps_right_valid : local_learned_gain_below_all_caps_right.Valid := by norm_num [RationalBox.Valid, local_learned_gain_below_all_caps_right]

def local_mark_finishes_before_any_main_firing_left : RationalBox := ⟨(500632116268676105999074341075082474129 / 10000000000000000000000000000000000000000 : ℚ), (50063211626867610599907434107508247413 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_finishes_before_any_main_firing_left_valid : local_mark_finishes_before_any_main_firing_left.Valid := by norm_num [RationalBox.Valid, local_mark_finishes_before_any_main_firing_left]

def local_mark_finishes_before_any_main_firing_right : RationalBox := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem local_mark_finishes_before_any_main_firing_right_valid : local_mark_finishes_before_any_main_firing_right.Valid := by norm_num [RationalBox.Valid, local_mark_finishes_before_any_main_firing_right]

def local_main_fires_before_error_begins_left : RationalBox := ⟨(9 / 10 : ℚ), (9 / 10 : ℚ)⟩
theorem local_main_fires_before_error_begins_left_valid : local_main_fires_before_error_begins_left.Valid := by norm_num [RationalBox.Valid, local_main_fires_before_error_begins_left]

def local_main_fires_before_error_begins_right : RationalBox := ⟨(2720977586485496336472455456588306019791 / 2500000000000000000000000000000000000000 : ℚ), (2176782069188397069177964365270644815833 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_fires_before_error_begins_right_valid : local_main_fires_before_error_begins_right.Valid := by norm_num [RationalBox.Valid, local_main_fires_before_error_begins_right]

def local_error_finishes_during_main_fast_left : RationalBox := ⟨(12676822538445200443003315228173238964293 / 10000000000000000000000000000000000000000 : ℚ), (6338411269222600221501657614086619482147 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_finishes_during_main_fast_left_valid : local_error_finishes_during_main_fast_left.Valid := by norm_num [RationalBox.Valid, local_error_finishes_during_main_fast_left]

def local_error_finishes_during_main_fast_right : RationalBox := ⟨(14976647747599025414441940102112403596681 / 10000000000000000000000000000000000000000 : ℚ), (7488323873799512707220970051056201798341 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_finishes_during_main_fast_right_valid : local_error_finishes_during_main_fast_right.Valid := by norm_num [RationalBox.Valid, local_error_finishes_during_main_fast_right]

def local_main_reopens_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_main_reopens_after_raw_pulse_left_valid : local_main_reopens_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, local_main_reopens_after_raw_pulse_left]

def local_main_reopens_after_raw_pulse_right : RationalBox := ⟨(63250156015086178075527447947796640202773 / 10000000000000000000000000000000000000000 : ℚ), (31625078007543089037763723973898320101387 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopens_after_raw_pulse_right_valid : local_main_reopens_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, local_main_reopens_after_raw_pulse_right]

def local_main_reopens_before_next_input_left : RationalBox := ⟨(14577399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (18221749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
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

def local_peak_bound_0 : RationalBox := ⟨(3071666219827193383274134334287322912463 / 10000000000000000000000000000000000000000 : ℚ), (191979138739199586454633395892957682029 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_0_valid : local_peak_bound_0.Valid := by norm_num [RationalBox.Valid, local_peak_bound_0]

def local_carry_bound_0 : RationalBox := ⟨(5516360828276874632078548254295764651 / 500000000000000000000000000000000000000 : ℚ), (110327216565537492641570965085915293021 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_0_valid : local_carry_bound_0.Valid := by norm_num [RationalBox.Valid, local_carry_bound_0]

def local_silent_0_no_first_crossing_left : RationalBox := ⟨(3071666219827193383274134334287322912463 / 10000000000000000000000000000000000000000 : ℚ), (191979138739199586454633395892957682029 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_0_no_first_crossing_left_valid : local_silent_0_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_no_first_crossing_left]

def local_silent_0_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_0_no_first_crossing_right_valid : local_silent_0_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_no_first_crossing_right]

def local_silent_0_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(103 / 1000 : ℚ), (103 / 1000 : ℚ)⟩
theorem local_silent_0_stays_below_threshold_after_raw_end_left_valid : local_silent_0_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_stays_below_threshold_after_raw_end_left]

def local_silent_0_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_0_stays_below_threshold_after_raw_end_right_valid : local_silent_0_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_stays_below_threshold_after_raw_end_right]

def local_silent_0_excess_returns_inside_section_left : RationalBox := ⟨(5516360828276874632078548254295764651 / 500000000000000000000000000000000000000 : ℚ), (110327216565537492641570965085915293021 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_0_excess_returns_inside_section_left_valid : local_silent_0_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_excess_returns_inside_section_left]

def local_silent_0_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_0_excess_returns_inside_section_right_valid : local_silent_0_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_excess_returns_inside_section_right]

def local_gain_before_1 : RationalBox := ⟨(5456406845147689995049126052665357533169 / 10000000000000000000000000000000000000000 : ℚ), (342270256240168262308431863837234449423 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_1_valid : local_gain_before_1.Valid := by norm_num [RationalBox.Valid, local_gain_before_1]

def local_peak_bound_1 : RationalBox := ⟨(2260829559127445256439636466373319934071 / 5000000000000000000000000000000000000000 : ℚ), (4521659118254890512879272932746639868143 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_1_valid : local_peak_bound_1.Valid := by norm_num [RationalBox.Valid, local_peak_bound_1]

def local_carry_bound_1 : RationalBox := ⟨(83274771281847001740101048999847416311 / 5000000000000000000000000000000000000000 : ℚ), (166549542563694003480202097999694832623 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_1_valid : local_carry_bound_1.Valid := by norm_num [RationalBox.Valid, local_carry_bound_1]

def local_silent_1_no_first_crossing_left : RationalBox := ⟨(2260829559127445256439636466373319934071 / 5000000000000000000000000000000000000000 : ℚ), (4521659118254890512879272932746639868143 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_1_no_first_crossing_left_valid : local_silent_1_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_no_first_crossing_left]

def local_silent_1_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_1_no_first_crossing_right_valid : local_silent_1_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_no_first_crossing_right]

def local_silent_1_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(103 / 1000 : ℚ), (103 / 1000 : ℚ)⟩
theorem local_silent_1_stays_below_threshold_after_raw_end_left_valid : local_silent_1_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_stays_below_threshold_after_raw_end_left]

def local_silent_1_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_1_stays_below_threshold_after_raw_end_right_valid : local_silent_1_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_stays_below_threshold_after_raw_end_right]

def local_silent_1_excess_returns_inside_section_left : RationalBox := ⟨(83274771281847001740101048999847416311 / 5000000000000000000000000000000000000000 : ℚ), (166549542563694003480202097999694832623 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_1_excess_returns_inside_section_left_valid : local_silent_1_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_excess_returns_inside_section_left]

def local_silent_1_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_1_excess_returns_inside_section_right_valid : local_silent_1_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_excess_returns_inside_section_right]

def local_gain_before_2 : RationalBox := ⟨(4962112230836631485934656593196649089149 / 5000000000000000000000000000000000000000 : ℚ), (399864343290145454389230760370802766529 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_2_valid : local_gain_before_2.Valid := by norm_num [RationalBox.Valid, local_gain_before_2]

def local_peak_bound_2 : RationalBox := ⟨(896063708462979744392267755232999354017 / 1250000000000000000000000000000000000000 : ℚ), (7168509667703837955138142041863994832137 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_2_valid : local_peak_bound_2.Valid := by norm_num [RationalBox.Valid, local_peak_bound_2]

def local_carry_bound_2 : RationalBox := ⟨(269179075867535086396391762317692681073 / 10000000000000000000000000000000000000000 : ℚ), (134589537933767543198195881158846340537 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_2_valid : local_carry_bound_2.Valid := by norm_num [RationalBox.Valid, local_carry_bound_2]

def local_silent_2_no_first_crossing_left : RationalBox := ⟨(896063708462979744392267755232999354017 / 1250000000000000000000000000000000000000 : ℚ), (7168509667703837955138142041863994832137 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_2_no_first_crossing_left_valid : local_silent_2_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_no_first_crossing_left]

def local_silent_2_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_2_no_first_crossing_right_valid : local_silent_2_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_no_first_crossing_right]

def local_silent_2_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(103 / 1000 : ℚ), (103 / 1000 : ℚ)⟩
theorem local_silent_2_stays_below_threshold_after_raw_end_left_valid : local_silent_2_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_stays_below_threshold_after_raw_end_left]

def local_silent_2_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_2_stays_below_threshold_after_raw_end_right_valid : local_silent_2_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_stays_below_threshold_after_raw_end_right]

def local_silent_2_excess_returns_inside_section_left : RationalBox := ⟨(269179075867535086396391762317692681073 / 10000000000000000000000000000000000000000 : ℚ), (134589537933767543198195881158846340537 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_2_excess_returns_inside_section_left_valid : local_silent_2_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_excess_returns_inside_section_left]

def local_silent_2_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_2_excess_returns_inside_section_right_valid : local_silent_2_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_excess_returns_inside_section_right]

def local_learned_start_excess : RationalBox := ⟨(269179075867535086396391762317692681073 / 10000000000000000000000000000000000000000 : ℚ), (134589537933767543198195881158846340537 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_start_excess_valid : local_learned_start_excess.Valid := by norm_num [RationalBox.Valid, local_learned_start_excess]

def local_learned_upper_at_0_5 : RationalBox := ⟨(1926453314771356899123283739114759197577 / 2000000000000000000000000000000000000000 : ℚ), (4816133286928392247808209347786897993943 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_upper_at_0_5_valid : local_learned_upper_at_0_5.Valid := by norm_num [RationalBox.Valid, local_learned_upper_at_0_5]

def local_learned_lower_at_0_9 : RationalBox := ⟨(517809300780242900506058193915408067873 / 500000000000000000000000000000000000000 : ℚ), (10356186015604858010121163878308161357461 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_lower_at_0_9_valid : local_learned_lower_at_0_9.Valid := by norm_num [RationalBox.Valid, local_learned_lower_at_0_9]

def local_learned_below_threshold_until_0_5_left : RationalBox := ⟨(1926453314771356899123283739114759197577 / 2000000000000000000000000000000000000000 : ℚ), (4816133286928392247808209347786897993943 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_below_threshold_until_0_5_left_valid : local_learned_below_threshold_until_0_5_left.Valid := by norm_num [RationalBox.Valid, local_learned_below_threshold_until_0_5_left]

def local_learned_below_threshold_until_0_5_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_learned_below_threshold_until_0_5_right_valid : local_learned_below_threshold_until_0_5_right.Valid := by norm_num [RationalBox.Valid, local_learned_below_threshold_until_0_5_right]

def local_learned_above_threshold_by_0_9_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_learned_above_threshold_by_0_9_left_valid : local_learned_above_threshold_by_0_9_left.Valid := by norm_num [RationalBox.Valid, local_learned_above_threshold_by_0_9_left]

def local_learned_above_threshold_by_0_9_right : RationalBox := ⟨(517809300780242900506058193915408067873 / 500000000000000000000000000000000000000 : ℚ), (10356186015604858010121163878308161357461 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_above_threshold_by_0_9_right_valid : local_learned_above_threshold_by_0_9_right.Valid := by norm_num [RationalBox.Valid, local_learned_above_threshold_by_0_9_right]

def local_probe_gap_exceeds_cycle_left : RationalBox := ⟨(14577399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (18221749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_probe_gap_exceeds_cycle_left_valid : local_probe_gap_exceeds_cycle_left.Valid := by norm_num [RationalBox.Valid, local_probe_gap_exceeds_cycle_left]

def local_probe_gap_exceeds_cycle_right : RationalBox := ⟨(20 / 1 : ℚ), (20 / 1 : ℚ)⟩
theorem local_probe_gap_exceeds_cycle_right_valid : local_probe_gap_exceeds_cycle_right.Valid := by norm_num [RationalBox.Valid, local_probe_gap_exceeds_cycle_right]

def local_probe_aux_cycle_ends_left : RationalBox := ⟨(12676822538445200443003315228173238964293 / 10000000000000000000000000000000000000000 : ℚ), (6338411269222600221501657614086619482147 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_probe_aux_cycle_ends_left_valid : local_probe_aux_cycle_ends_left.Valid := by norm_num [RationalBox.Valid, local_probe_aux_cycle_ends_left]

def local_probe_aux_cycle_ends_right : RationalBox := ⟨(20 / 1 : ℚ), (20 / 1 : ℚ)⟩
theorem local_probe_aux_cycle_ends_right_valid : local_probe_aux_cycle_ends_right.Valid := by norm_num [RationalBox.Valid, local_probe_aux_cycle_ends_right]

def local_work_bound : RationalBox := ⟨(312043163517443408604530096237841324820169 / 1250000000000000000000000000000000000000 : ℚ), (2496345308139547268836240769902730598561353 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_work_bound_valid : local_work_bound.Valid := by norm_num [RationalBox.Valid, local_work_bound]

def local_reserve_gate_stays_open_left : RationalBox := ⟨(312043163517443408604530096237841324820169 / 1250000000000000000000000000000000000000 : ℚ), (2496345308139547268836240769902730598561353 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_reserve_gate_stays_open_left_valid : local_reserve_gate_stays_open_left.Valid := by norm_num [RationalBox.Valid, local_reserve_gate_stays_open_left]

def local_reserve_gate_stays_open_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem local_reserve_gate_stays_open_right_valid : local_reserve_gate_stays_open_right.Valid := by norm_num [RationalBox.Valid, local_reserve_gate_stays_open_right]

def local_A_gain_complete_by : RationalBox := ⟨(425676822538445200443003315228173238964293 / 10000000000000000000000000000000000000000 : ℚ), (212838411269222600221501657614086619482147 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_gain_complete_by_valid : local_A_gain_complete_by.Valid := by norm_num [RationalBox.Valid, local_A_gain_complete_by]

def local_A_first_emission : RationalBox := ⟨(493 / 10 : ℚ), (251 / 5 : ℚ)⟩
theorem local_A_first_emission_valid : local_A_first_emission.Valid := by norm_num [RationalBox.Valid, local_A_first_emission]

def local_A_last_return_by : RationalBox := ⟨(257177399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (321471749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_last_return_by_valid : local_A_last_return_by.Valid := by norm_num [RationalBox.Valid, local_A_last_return_by]

def local_B_last_return_by : RationalBox := ⟨(254577399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (318221749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_B_last_return_by_valid : local_B_last_return_by.Valid := by norm_num [RationalBox.Valid, local_B_last_return_by]

def local_A_learning_complete_before_first_response_left : RationalBox := ⟨(425676822538445200443003315228173238964293 / 10000000000000000000000000000000000000000 : ℚ), (212838411269222600221501657614086619482147 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_learning_complete_before_first_response_left_valid : local_A_learning_complete_before_first_response_left.Valid := by norm_num [RationalBox.Valid, local_A_learning_complete_before_first_response_left]

def local_A_learning_complete_before_first_response_right : RationalBox := ⟨(493 / 10 : ℚ), (493 / 10 : ℚ)⟩
theorem local_A_learning_complete_before_first_response_right_valid : local_A_learning_complete_before_first_response_right.Valid := by norm_num [RationalBox.Valid, local_A_learning_complete_before_first_response_right]

def local_A_quiescent_before_measurement_left : RationalBox := ⟨(257177399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (321471749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_quiescent_before_measurement_left_valid : local_A_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, local_A_quiescent_before_measurement_left]

def local_A_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem local_A_quiescent_before_measurement_right_valid : local_A_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, local_A_quiescent_before_measurement_right]

def local_B_quiescent_before_measurement_left : RationalBox := ⟨(254577399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (318221749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
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

def entire_protected_MARK_and_ERROR_before_reopen_right : RationalBox := ⟨(1105198266969719750601104555432650634647 / 10000000000000000000000000000000000000000 : ℚ), (138149783371214968825138069429081329331 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem entire_protected_MARK_and_ERROR_before_reopen_right_valid : entire_protected_MARK_and_ERROR_before_reopen_right.Valid := by norm_num [RationalBox.Valid, entire_protected_MARK_and_ERROR_before_reopen_right]

def protected_input_reopens_by_deadline_left : RationalBox := ⟨(449705540348856647582467719601386950133 / 5000000000000000000000000000000000000000 : ℚ), (899411080697713295164935439202773900267 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_input_reopens_by_deadline_left_valid : protected_input_reopens_by_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_by_deadline_left]

def protected_input_reopens_by_deadline_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem protected_input_reopens_by_deadline_right_valid : protected_input_reopens_by_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_by_deadline_right]

def protected_aux_cycle_before_deadline_left : RationalBox := ⟨(12676822538445200443003315228173238964293 / 10000000000000000000000000000000000000000 : ℚ), (6338411269222600221501657614086619482147 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_aux_cycle_before_deadline_left_valid : protected_aux_cycle_before_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_aux_cycle_before_deadline_left]

def protected_aux_cycle_before_deadline_right : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_aux_cycle_before_deadline_right_valid : protected_aux_cycle_before_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_aux_cycle_before_deadline_right]

def protected_return_before_next_input_left : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_return_before_next_input_left_valid : protected_return_before_next_input_left.Valid := by norm_num [RationalBox.Valid, protected_return_before_next_input_left]

def protected_return_before_next_input_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem protected_return_before_next_input_right_valid : protected_return_before_next_input_right.Valid := by norm_num [RationalBox.Valid, protected_return_before_next_input_right]

def recovery_cap_not_reached_left : RationalBox := ⟨(112484345369549905807531293390262105509 / 625000000000000000000000000000000000000 : ℚ), (112515654630450094192468706609737894491 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem recovery_cap_not_reached_left_valid : recovery_cap_not_reached_left.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_left]

def recovery_cap_not_reached_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem recovery_cap_not_reached_right_valid : recovery_cap_not_reached_right.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_right]

def unused_port1_birth_gain_below_caps_left : RationalBox := ⟨(5999940000299999000002499995000008333321 / 5000000000000000000000000000000000000000 : ℚ), (12000120000600002000005000010000016666691 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem unused_port1_birth_gain_below_caps_left_valid : unused_port1_birth_gain_below_caps_left.Valid := by norm_num [RationalBox.Valid, unused_port1_birth_gain_below_caps_left]

def unused_port1_birth_gain_below_caps_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem unused_port1_birth_gain_below_caps_right_valid : unused_port1_birth_gain_below_caps_right.Valid := by norm_num [RationalBox.Valid, unused_port1_birth_gain_below_caps_right]

def warmup_returns_before_entry_cut_left : RationalBox := ⟨(254577399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (318221749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
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

def protected_MARK_dose : RationalBox := ⟨(62490595369549905807531293390262105509 / 625000000000000000000000000000000000000 : ℚ), (62509404630450094192468706609737894491 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem protected_MARK_dose_valid : protected_MARK_dose.Valid := by norm_num [RationalBox.Valid, protected_MARK_dose]

def entry_recovery : RationalBox := ⟨(112484345369549905807531293390262105509 / 625000000000000000000000000000000000000 : ℚ), (112515654630450094192468706609737894491 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem entry_recovery_valid : entry_recovery.Valid := by norm_num [RationalBox.Valid, entry_recovery]

def entry_charge_radius : RationalBox := ⟨(301 / 100000 : ℚ), (301 / 100000 : ℚ)⟩
theorem entry_charge_radius_valid : entry_charge_radius.Valid := by norm_num [RationalBox.Valid, entry_charge_radius]

def entry_q : RationalBox := ⟨(9699 / 100000 : ℚ), (10301 / 100000 : ℚ)⟩
theorem entry_q_valid : entry_q.Valid := by norm_num [RationalBox.Valid, entry_q]

def entry_m : RationalBox := ⟨(2199 / 100000 : ℚ), (2801 / 100000 : ℚ)⟩
theorem entry_m_valid : entry_m.Valid := by norm_num [RationalBox.Valid, entry_m]

def q_lower_at_protected_arrival : RationalBox := ⟨(281976228698185262870367781097844155831 / 2000000000000000000000000000000000000000 : ℚ), (352470285872731578587959726372305194789 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem q_lower_at_protected_arrival_valid : q_lower_at_protected_arrival.Valid := by norm_num [RationalBox.Valid, q_lower_at_protected_arrival]

def q_lower_through_protected_cycle : RationalBox := ⟨(1105198266969719750601104555432650634647 / 10000000000000000000000000000000000000000 : ℚ), (138149783371214968825138069429081329331 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem q_lower_through_protected_cycle_valid : q_lower_through_protected_cycle.Valid := by norm_num [RationalBox.Valid, q_lower_through_protected_cycle]

def q_upper_at_reopen_deadline : RationalBox := ⟨(449705540348856647582467719601386950133 / 5000000000000000000000000000000000000000 : ℚ), (899411080697713295164935439202773900267 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem q_upper_at_reopen_deadline_valid : q_upper_at_reopen_deadline.Valid := by norm_num [RationalBox.Valid, q_upper_at_reopen_deadline]

def protected_reopen_deadline : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_reopen_deadline_valid : protected_reopen_deadline.Valid := by norm_num [RationalBox.Valid, protected_reopen_deadline]

def last_warmup_return : RationalBox := ⟨(254577399390658304592285043485929705007183 / 2000000000000000000000000000000000000000 : ℚ), (318221749238322880740356304357412131258979 / 2500000000000000000000000000000000000000 : ℚ)⟩
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

end KernelR.Robust.Evidence.Birth0
