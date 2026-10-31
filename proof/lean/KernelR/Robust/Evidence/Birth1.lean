import KernelR.Intervals

/-! Generated rational endpoint checks; analytic enclosure membership is separate. -/
namespace KernelR.Robust.Evidence.Birth1
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def local_epsilon : RationalBox := ⟨(3 / 1000 : ℚ), (3 / 1000 : ℚ)⟩
theorem local_epsilon_valid : local_epsilon.Valid := by norm_num [RationalBox.Valid, local_epsilon]

def local_nu : RationalBox := ⟨(1 / 500 : ℚ), (1 / 500 : ℚ)⟩
theorem local_nu_valid : local_nu.Valid := by norm_num [RationalBox.Valid, local_nu]

def local_alpha : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
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

def local_b : RationalBox := ⟨(1799699357778069765715623190334479789427 / 10000000000000000000000000000000000000000 : ℚ), (1800300642221930234284376809665520210573 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_b_valid : local_b.Valid := by norm_num [RationalBox.Valid, local_b]

def local_h_increases_through_raw_window_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_h_increases_through_raw_window_left_valid : local_h_increases_through_raw_window_left.Valid := by norm_num [RationalBox.Valid, local_h_increases_through_raw_window_left]

def local_h_increases_through_raw_window_right : RationalBox := ⟨(5753062894644089006539049196938423108761 / 5000000000000000000000000000000000000000 : ℚ), (11506125789288178013078098393876846217523 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_h_increases_through_raw_window_right_valid : local_h_increases_through_raw_window_right.Valid := by norm_num [RationalBox.Valid, local_h_increases_through_raw_window_right]

def local_aux_rest_deviation : RationalBox := ⟨(401 / 100000 : ℚ), (401 / 100000 : ℚ)⟩
theorem local_aux_rest_deviation_valid : local_aux_rest_deviation.Valid := by norm_num [RationalBox.Valid, local_aux_rest_deviation]

def local_aux_rest_below_threshold_left : RationalBox := ⟨(2901 / 100000 : ℚ), (2901 / 100000 : ℚ)⟩
theorem local_aux_rest_below_threshold_left_valid : local_aux_rest_below_threshold_left.Valid := by norm_num [RationalBox.Valid, local_aux_rest_below_threshold_left]

def local_aux_rest_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_rest_below_threshold_right_valid : local_aux_rest_below_threshold_right.Valid := by norm_num [RationalBox.Valid, local_aux_rest_below_threshold_right]

def local_aux_below_threshold_until_0_015_left : RationalBox := ⟨(1914866060705943251892286758087775857363 / 2500000000000000000000000000000000000000 : ℚ), (7659464242823773007569147032351103429453 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_below_threshold_until_0_015_left_valid : local_aux_below_threshold_until_0_015_left.Valid := by norm_num [RationalBox.Valid, local_aux_below_threshold_until_0_015_left]

def local_aux_below_threshold_until_0_015_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_below_threshold_until_0_015_right_valid : local_aux_below_threshold_until_0_015_right.Valid := by norm_num [RationalBox.Valid, local_aux_below_threshold_until_0_015_right]

def local_aux_above_threshold_by_0_03_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_above_threshold_by_0_03_left_valid : local_aux_above_threshold_by_0_03_left.Valid := by norm_num [RationalBox.Valid, local_aux_above_threshold_by_0_03_left]

def local_aux_above_threshold_by_0_03_right : RationalBox := ⟨(14653786390960673916349219409327308941591 / 10000000000000000000000000000000000000000 : ℚ), (1831723298870084239543652426165913617699 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_above_threshold_by_0_03_right_valid : local_aux_above_threshold_by_0_03_right.Valid := by norm_num [RationalBox.Valid, local_aux_above_threshold_by_0_03_right]

def local_decay_1_0_8_dominates_noise_left : RationalBox := ⟨(1797961932888485370869828384384510411 / 10000000000000000000000000000000000000000 : ℚ), (449490483222121342717457096096127603 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_1_0_8_dominates_noise_left_valid : local_decay_1_0_8_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_8_dominates_noise_left]

def local_decay_1_0_8_dominates_noise_right : RationalBox := ⟨(4 / 5 : ℚ), (4 / 5 : ℚ)⟩
theorem local_decay_1_0_8_dominates_noise_right_valid : local_decay_1_0_8_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_8_dominates_noise_right]

def local_decay_0_8_0_1_dominates_noise_left : RationalBox := ⟨(10225722121981285267813575137826851659 / 10000000000000000000000000000000000000000 : ℚ), (511286106099064263390678756891342583 / 500000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_8_0_1_dominates_noise_left_valid : local_decay_0_8_0_1_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_8_0_1_dominates_noise_left]

def local_decay_0_8_0_1_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_decay_0_8_0_1_dominates_noise_right_valid : local_decay_0_8_0_1_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_8_0_1_dominates_noise_right]

def local_decay_0_1_0_025_dominates_noise_left : RationalBox := ⟨(1085277112002730747763233210382566803 / 5000000000000000000000000000000000000000 : ℚ), (2170554224005461495526466420765133607 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_1_0_025_dominates_noise_left_valid : local_decay_0_1_0_025_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_1_0_025_dominates_noise_left]

def local_decay_0_1_0_025_dominates_noise_right : RationalBox := ⟨(1 / 40 : ℚ), (1 / 40 : ℚ)⟩
theorem local_decay_0_1_0_025_dominates_noise_right_valid : local_decay_0_1_0_025_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_1_0_025_dominates_noise_right]

def local_mark_duration : RationalBox := ⟨(39872375261390822549770961516805357017 / 2000000000000000000000000000000000000000 : ℚ), (200642221930234284376809665520210572511 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_duration_valid : local_mark_duration.Valid := by norm_num [RationalBox.Valid, local_mark_duration]

def local_silent_duration : RationalBox := ⟨(5261675062803583734483728006185528575603 / 5000000000000000000000000000000000000000 : ℚ), (10677908016689829192296164219727712756819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_duration_valid : local_silent_duration.Valid := by norm_num [RationalBox.Valid, local_silent_duration]

def local_error_duration : RationalBox := ⟨(372142059004446547176160534762983065963 / 2500000000000000000000000000000000000000 : ℚ), (755809540865448422354677106586852869623 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_duration_valid : local_error_duration.Valid := by norm_num [RationalBox.Valid, local_error_duration]

def local_mark_end : RationalBox := ⟨(69872375261390822549770961516805357017 / 2000000000000000000000000000000000000000 : ℚ), (500642221930234284376809665520210572511 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_end_valid : local_mark_end.Valid := by norm_num [RationalBox.Valid, local_mark_end]

def local_error_start : RationalBox := ⟨(10872712001914121581716310819955083936291 / 10000000000000000000000000000000000000000 : ℚ), (11178550238620063476672973885247923329329 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_start_valid : local_error_start.Valid := by norm_num [RationalBox.Valid, local_error_start]

def local_aux_finish : RationalBox := ⟨(12361280237931907770420952959007016200143 / 10000000000000000000000000000000000000000 : ℚ), (6345084660175480160691164049210814534287 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_finish_valid : local_aux_finish.Valid := by norm_num [RationalBox.Valid, local_aux_finish]

def local_gain_log_dose : RationalBox := ⟨(1493953523673076412621162583147305177043 / 2500000000000000000000000000000000000000 : ℚ), (1506046476326923587378837416852694822957 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_log_dose_valid : local_gain_log_dose.Valid := by norm_num [RationalBox.Valid, local_gain_log_dose]

def local_initial_gain : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_initial_gain_valid : local_initial_gain.Valid := by norm_num [RationalBox.Valid, local_initial_gain]

def local_learned_gain : RationalBox := ⟨(18017554219411780565711921791465088961099 / 10000000000000000000000000000000000000000 : ℚ), (18281288680026811045099511396562788906733 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_gain_valid : local_learned_gain.Valid := by norm_num [RationalBox.Valid, local_learned_gain]

def local_decay_1_0_25_dominates_noise_left : RationalBox := ⟨(7213475204444817036799623405009460687 / 5000000000000000000000000000000000000000 : ℚ), (115415603271117072588793974480151371 / 80000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_1_0_25_dominates_noise_left_valid : local_decay_1_0_25_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_25_dominates_noise_left]

def local_decay_1_0_25_dominates_noise_right : RationalBox := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem local_decay_1_0_25_dominates_noise_right_valid : local_decay_1_0_25_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_1_0_25_dominates_noise_right]

def local_decay_0_25_0_1_dominates_noise_left : RationalBox := ⟨(111129672373124797339464085797264351849 / 10000000000000000000000000000000000000000 : ℚ), (2222593447462495946789281715945287037 / 200000000000000000000000000000000000000 : ℚ)⟩
theorem local_decay_0_25_0_1_dominates_noise_left_valid : local_decay_0_25_0_1_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, local_decay_0_25_0_1_dominates_noise_left]

def local_decay_0_25_0_1_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem local_decay_0_25_0_1_dominates_noise_right_valid : local_decay_0_25_0_1_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, local_decay_0_25_0_1_dominates_noise_right]

def local_min_input_gap : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_min_input_gap_valid : local_min_input_gap.Valid := by norm_num [RationalBox.Valid, local_min_input_gap]

def local_fast_duration : RationalBox := ⟨(498444580833712029458393018090524001329 / 500000000000000000000000000000000000000 : ℚ), (2507833398965798195878523017893343664721 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_fast_duration_valid : local_fast_duration.Valid := by norm_num [RationalBox.Valid, local_fast_duration]

def local_slow_duration : RationalBox := ⟨(23730062123900037650474023549641202575383 / 5000000000000000000000000000000000000000 : ℚ), (27466379341584540175121917028356467074443 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_slow_duration_valid : local_slow_duration.Valid := by norm_num [RationalBox.Valid, local_slow_duration]

def local_main_reopen_bound : RationalBox := ⟨(9245511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (73964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopen_bound_valid : local_main_reopen_bound.Valid := by norm_num [RationalBox.Valid, local_main_reopen_bound]

def local_aux_cycle_ends_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_aux_cycle_ends_after_raw_pulse_left_valid : local_aux_cycle_ends_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_after_raw_pulse_left]

def local_aux_cycle_ends_after_raw_pulse_right : RationalBox := ⟨(12361280237931907770420952959007016200143 / 10000000000000000000000000000000000000000 : ℚ), (772580014870744235651309559937938512509 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_cycle_ends_after_raw_pulse_right_valid : local_aux_cycle_ends_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_after_raw_pulse_right]

def local_aux_cycle_ends_before_next_input_left : RationalBox := ⟨(12690169320350960321382328098421629068573 / 10000000000000000000000000000000000000000 : ℚ), (6345084660175480160691164049210814534287 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_aux_cycle_ends_before_next_input_left_valid : local_aux_cycle_ends_before_next_input_left.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_before_next_input_left]

def local_aux_cycle_ends_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_aux_cycle_ends_before_next_input_right_valid : local_aux_cycle_ends_before_next_input_right.Valid := by norm_num [RationalBox.Valid, local_aux_cycle_ends_before_next_input_right]

def local_learned_gain_below_all_caps_left : RationalBox := ⟨(18017554219411780565711921791465088961099 / 10000000000000000000000000000000000000000 : ℚ), (18281288680026811045099511396562788906733 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_gain_below_all_caps_left_valid : local_learned_gain_below_all_caps_left.Valid := by norm_num [RationalBox.Valid, local_learned_gain_below_all_caps_left]

def local_learned_gain_below_all_caps_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem local_learned_gain_below_all_caps_right_valid : local_learned_gain_below_all_caps_right.Valid := by norm_num [RationalBox.Valid, local_learned_gain_below_all_caps_right]

def local_mark_finishes_before_any_main_firing_left : RationalBox := ⟨(50064222193023428437680966552021057251 / 1000000000000000000000000000000000000000 : ℚ), (500642221930234284376809665520210572511 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_mark_finishes_before_any_main_firing_left_valid : local_mark_finishes_before_any_main_firing_left.Valid := by norm_num [RationalBox.Valid, local_mark_finishes_before_any_main_firing_left]

def local_mark_finishes_before_any_main_firing_right : RationalBox := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem local_mark_finishes_before_any_main_firing_right_valid : local_mark_finishes_before_any_main_firing_right.Valid := by norm_num [RationalBox.Valid, local_mark_finishes_before_any_main_firing_right]

def local_main_fires_before_error_begins_left : RationalBox := ⟨(9 / 10 : ℚ), (9 / 10 : ℚ)⟩
theorem local_main_fires_before_error_begins_left_valid : local_main_fires_before_error_begins_left.Valid := by norm_num [RationalBox.Valid, local_main_fires_before_error_begins_left]

def local_main_fires_before_error_begins_right : RationalBox := ⟨(10872712001914121581716310819955083936291 / 10000000000000000000000000000000000000000 : ℚ), (2718178000478530395429077704988770984073 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_fires_before_error_begins_right_valid : local_main_fires_before_error_begins_right.Valid := by norm_num [RationalBox.Valid, local_main_fires_before_error_begins_right]

def local_error_finishes_during_main_fast_left : RationalBox := ⟨(12690169320350960321382328098421629068573 / 10000000000000000000000000000000000000000 : ℚ), (6345084660175480160691164049210814534287 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_finishes_during_main_fast_left_valid : local_error_finishes_during_main_fast_left.Valid := by norm_num [RationalBox.Valid, local_error_finishes_during_main_fast_left]

def local_error_finishes_during_main_fast_right : RationalBox := ⟨(748444580833712029458393018090524001329 / 500000000000000000000000000000000000000 : ℚ), (14968891616674240589167860361810480026581 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_error_finishes_during_main_fast_right_valid : local_error_finishes_during_main_fast_right.Valid := by norm_num [RationalBox.Valid, local_error_finishes_during_main_fast_right]

def local_main_reopens_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_main_reopens_after_raw_pulse_left_valid : local_main_reopens_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, local_main_reopens_after_raw_pulse_left]

def local_main_reopens_after_raw_pulse_right : RationalBox := ⟨(31214507932237157945057953730546442588673 / 5000000000000000000000000000000000000000 : ℚ), (62429015864474315890115907461092885177347 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopens_after_raw_pulse_right_valid : local_main_reopens_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, local_main_reopens_after_raw_pulse_right]

def local_main_reopens_before_next_input_left : RationalBox := ⟨(9245511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (73964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_main_reopens_before_next_input_left_valid : local_main_reopens_before_next_input_left.Valid := by norm_num [RationalBox.Valid, local_main_reopens_before_next_input_left]

def local_main_reopens_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem local_main_reopens_before_next_input_right_valid : local_main_reopens_before_next_input_right.Valid := by norm_num [RationalBox.Valid, local_main_reopens_before_next_input_right]

def local_arbitrary_initial_silence_inside_section_left : RationalBox := ⟨(401 / 100000 : ℚ), (401 / 100000 : ℚ)⟩
theorem local_arbitrary_initial_silence_inside_section_left_valid : local_arbitrary_initial_silence_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_arbitrary_initial_silence_inside_section_left]

def local_arbitrary_initial_silence_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_arbitrary_initial_silence_inside_section_right_valid : local_arbitrary_initial_silence_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_arbitrary_initial_silence_inside_section_right]

def local_rest_noise_inside_section_left : RationalBox := ⟨(1 / 250 : ℚ), (1 / 250 : ℚ)⟩
theorem local_rest_noise_inside_section_left_valid : local_rest_noise_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_rest_noise_inside_section_left]

def local_rest_noise_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_rest_noise_inside_section_right_valid : local_rest_noise_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_rest_noise_inside_section_right]

def local_gain_before_0 : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_0_valid : local_gain_before_0.Valid := by norm_num [RationalBox.Valid, local_gain_before_0]

def local_peak_bound_0 : RationalBox := ⟨(1496507723727234944416254444898725196411 / 5000000000000000000000000000000000000000 : ℚ), (2993015447454469888832508889797450392823 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_0_valid : local_peak_bound_0.Valid := by norm_num [RationalBox.Valid, local_peak_bound_0]

def local_carry_bound_0 : RationalBox := ⟨(2345551903428641044746587840505424991 / 200000000000000000000000000000000000000 : ℚ), (117277595171432052237329392025271249551 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_0_valid : local_carry_bound_0.Valid := by norm_num [RationalBox.Valid, local_carry_bound_0]

def local_silent_0_no_first_crossing_left : RationalBox := ⟨(1496507723727234944416254444898725196411 / 5000000000000000000000000000000000000000 : ℚ), (2993015447454469888832508889797450392823 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_0_no_first_crossing_left_valid : local_silent_0_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_no_first_crossing_left]

def local_silent_0_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_0_no_first_crossing_right_valid : local_silent_0_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_no_first_crossing_right]

def local_silent_0_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(13 / 125 : ℚ), (13 / 125 : ℚ)⟩
theorem local_silent_0_stays_below_threshold_after_raw_end_left_valid : local_silent_0_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_stays_below_threshold_after_raw_end_left]

def local_silent_0_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_0_stays_below_threshold_after_raw_end_right_valid : local_silent_0_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_stays_below_threshold_after_raw_end_right]

def local_silent_0_excess_returns_inside_section_left : RationalBox := ⟨(2345551903428641044746587840505424991 / 200000000000000000000000000000000000000 : ℚ), (117277595171432052237329392025271249551 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_0_excess_returns_inside_section_left_valid : local_silent_0_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_0_excess_returns_inside_section_left]

def local_silent_0_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_0_excess_returns_inside_section_right_valid : local_silent_0_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_0_excess_returns_inside_section_right]

def local_gain_before_1 : RationalBox := ⟨(272654848358141894736334845672383897973 / 500000000000000000000000000000000000000 : ℚ), (5479648076050182044971088451992663667563 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_1_valid : local_gain_before_1.Valid := by norm_num [RationalBox.Valid, local_gain_before_1]

def local_peak_bound_1 : RationalBox := ⟨(1093953683578809763761029415479540959863 / 2500000000000000000000000000000000000000 : ℚ), (4375814734315239055044117661918163839453 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_1_valid : local_peak_bound_1.Valid := by norm_num [RationalBox.Valid, local_peak_bound_1]

def local_carry_bound_1 : RationalBox := ⟨(170894542109728498205246410290235386341 / 10000000000000000000000000000000000000000 : ℚ), (85447271054864249102623205145117693171 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_1_valid : local_carry_bound_1.Valid := by norm_num [RationalBox.Valid, local_carry_bound_1]

def local_silent_1_no_first_crossing_left : RationalBox := ⟨(1093953683578809763761029415479540959863 / 2500000000000000000000000000000000000000 : ℚ), (4375814734315239055044117661918163839453 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_1_no_first_crossing_left_valid : local_silent_1_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_no_first_crossing_left]

def local_silent_1_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_1_no_first_crossing_right_valid : local_silent_1_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_no_first_crossing_right]

def local_silent_1_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(13 / 125 : ℚ), (13 / 125 : ℚ)⟩
theorem local_silent_1_stays_below_threshold_after_raw_end_left_valid : local_silent_1_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_stays_below_threshold_after_raw_end_left]

def local_silent_1_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_1_stays_below_threshold_after_raw_end_right_valid : local_silent_1_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_stays_below_threshold_after_raw_end_right]

def local_silent_1_excess_returns_inside_section_left : RationalBox := ⟨(170894542109728498205246410290235386341 / 10000000000000000000000000000000000000000 : ℚ), (85447271054864249102623205145117693171 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_1_excess_returns_inside_section_left_valid : local_silent_1_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_1_excess_returns_inside_section_left]

def local_silent_1_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_1_excess_returns_inside_section_right_valid : local_silent_1_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_1_excess_returns_inside_section_right]

def local_gain_before_2 : RationalBox := ⟨(9912187965810897278949491744480108774281 / 10000000000000000000000000000000000000000 : ℚ), (2502186897785950850932805823511772400021 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem local_gain_before_2_valid : local_gain_before_2.Valid := by norm_num [RationalBox.Valid, local_gain_before_2]

def local_peak_bound_2 : RationalBox := ⟨(3450770313766706335097645168602791530189 / 5000000000000000000000000000000000000000 : ℚ), (6901540627533412670195290337205583060379 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_peak_bound_2_valid : local_peak_bound_2.Valid := by norm_num [RationalBox.Valid, local_peak_bound_2]

def local_carry_bound_2 : RationalBox := ⟨(268827562819331674451861029025200046141 / 10000000000000000000000000000000000000000 : ℚ), (134413781409665837225930514512600023071 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_carry_bound_2_valid : local_carry_bound_2.Valid := by norm_num [RationalBox.Valid, local_carry_bound_2]

def local_silent_2_no_first_crossing_left : RationalBox := ⟨(3450770313766706335097645168602791530189 / 5000000000000000000000000000000000000000 : ℚ), (6901540627533412670195290337205583060379 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_2_no_first_crossing_left_valid : local_silent_2_no_first_crossing_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_no_first_crossing_left]

def local_silent_2_no_first_crossing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_2_no_first_crossing_right_valid : local_silent_2_no_first_crossing_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_no_first_crossing_right]

def local_silent_2_stays_below_threshold_after_raw_end_left : RationalBox := ⟨(13 / 125 : ℚ), (13 / 125 : ℚ)⟩
theorem local_silent_2_stays_below_threshold_after_raw_end_left_valid : local_silent_2_stays_below_threshold_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_stays_below_threshold_after_raw_end_left]

def local_silent_2_stays_below_threshold_after_raw_end_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_silent_2_stays_below_threshold_after_raw_end_right_valid : local_silent_2_stays_below_threshold_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_stays_below_threshold_after_raw_end_right]

def local_silent_2_excess_returns_inside_section_left : RationalBox := ⟨(268827562819331674451861029025200046141 / 10000000000000000000000000000000000000000 : ℚ), (134413781409665837225930514512600023071 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_silent_2_excess_returns_inside_section_left_valid : local_silent_2_excess_returns_inside_section_left.Valid := by norm_num [RationalBox.Valid, local_silent_2_excess_returns_inside_section_left]

def local_silent_2_excess_returns_inside_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem local_silent_2_excess_returns_inside_section_right_valid : local_silent_2_excess_returns_inside_section_right.Valid := by norm_num [RationalBox.Valid, local_silent_2_excess_returns_inside_section_right]

def local_learned_start_excess : RationalBox := ⟨(268827562819331674451861029025200046141 / 10000000000000000000000000000000000000000 : ℚ), (134413781409665837225930514512600023071 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_start_excess_valid : local_learned_start_excess.Valid := by norm_num [RationalBox.Valid, local_learned_start_excess]

def local_learned_upper_at_0_5 : RationalBox := ⟨(462551452499687824341908010760212138917 / 500000000000000000000000000000000000000 : ℚ), (9251029049993756486838160215204242778341 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_upper_at_0_5_valid : local_learned_upper_at_0_5.Valid := by norm_num [RationalBox.Valid, local_learned_upper_at_0_5]

def local_learned_lower_at_0_9 : RationalBox := ⟨(10818416366098991200679503507256191374749 / 10000000000000000000000000000000000000000 : ℚ), (43273665464395964802718014029024765499 / 40000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_lower_at_0_9_valid : local_learned_lower_at_0_9.Valid := by norm_num [RationalBox.Valid, local_learned_lower_at_0_9]

def local_learned_below_threshold_until_0_5_left : RationalBox := ⟨(462551452499687824341908010760212138917 / 500000000000000000000000000000000000000 : ℚ), (9251029049993756486838160215204242778341 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_below_threshold_until_0_5_left_valid : local_learned_below_threshold_until_0_5_left.Valid := by norm_num [RationalBox.Valid, local_learned_below_threshold_until_0_5_left]

def local_learned_below_threshold_until_0_5_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_learned_below_threshold_until_0_5_right_valid : local_learned_below_threshold_until_0_5_right.Valid := by norm_num [RationalBox.Valid, local_learned_below_threshold_until_0_5_right]

def local_learned_above_threshold_by_0_9_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem local_learned_above_threshold_by_0_9_left_valid : local_learned_above_threshold_by_0_9_left.Valid := by norm_num [RationalBox.Valid, local_learned_above_threshold_by_0_9_left]

def local_learned_above_threshold_by_0_9_right : RationalBox := ⟨(10818416366098991200679503507256191374749 / 10000000000000000000000000000000000000000 : ℚ), (43273665464395964802718014029024765499 / 40000000000000000000000000000000000000 : ℚ)⟩
theorem local_learned_above_threshold_by_0_9_right_valid : local_learned_above_threshold_by_0_9_right.Valid := by norm_num [RationalBox.Valid, local_learned_above_threshold_by_0_9_right]

def local_probe_gap_exceeds_cycle_left : RationalBox := ⟨(9245511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (73964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_probe_gap_exceeds_cycle_left_valid : local_probe_gap_exceeds_cycle_left.Valid := by norm_num [RationalBox.Valid, local_probe_gap_exceeds_cycle_left]

def local_probe_gap_exceeds_cycle_right : RationalBox := ⟨(20 / 1 : ℚ), (20 / 1 : ℚ)⟩
theorem local_probe_gap_exceeds_cycle_right_valid : local_probe_gap_exceeds_cycle_right.Valid := by norm_num [RationalBox.Valid, local_probe_gap_exceeds_cycle_right]

def local_probe_aux_cycle_ends_left : RationalBox := ⟨(12690169320350960321382328098421629068573 / 10000000000000000000000000000000000000000 : ℚ), (6345084660175480160691164049210814534287 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_probe_aux_cycle_ends_left_valid : local_probe_aux_cycle_ends_left.Valid := by norm_num [RationalBox.Valid, local_probe_aux_cycle_ends_left]

def local_probe_aux_cycle_ends_right : RationalBox := ⟨(20 / 1 : ℚ), (20 / 1 : ℚ)⟩
theorem local_probe_aux_cycle_ends_right_valid : local_probe_aux_cycle_ends_right.Valid := by norm_num [RationalBox.Valid, local_probe_aux_cycle_ends_right]

def local_work_bound : RationalBox := ⟨(2412569423394848013788616984038787968476533 / 10000000000000000000000000000000000000000 : ℚ), (1206284711697424006894308492019393984238267 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_work_bound_valid : local_work_bound.Valid := by norm_num [RationalBox.Valid, local_work_bound]

def local_reserve_gate_stays_open_left : RationalBox := ⟨(2412569423394848013788616984038787968476533 / 10000000000000000000000000000000000000000 : ℚ), (1206284711697424006894308492019393984238267 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_reserve_gate_stays_open_left_valid : local_reserve_gate_stays_open_left.Valid := by norm_num [RationalBox.Valid, local_reserve_gate_stays_open_left]

def local_reserve_gate_stays_open_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem local_reserve_gate_stays_open_right_valid : local_reserve_gate_stays_open_right.Valid := by norm_num [RationalBox.Valid, local_reserve_gate_stays_open_right]

def local_A_gain_complete_by : RationalBox := ⟨(425690169320350960321382328098421629068573 / 10000000000000000000000000000000000000000 : ℚ), (212845084660175480160691164049210814534287 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_gain_complete_by_valid : local_A_gain_complete_by.Valid := by norm_num [RationalBox.Valid, local_A_gain_complete_by]

def local_A_first_emission : RationalBox := ⟨(493 / 10 : ℚ), (251 / 5 : ℚ)⟩
theorem local_A_first_emission_valid : local_A_first_emission.Valid := by norm_num [RationalBox.Valid, local_A_first_emission]

def local_A_last_return_by : RationalBox := ⟨(160870511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (1286964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_last_return_by_valid : local_A_last_return_by.Valid := by norm_num [RationalBox.Valid, local_A_last_return_by]

def local_B_last_return_by : RationalBox := ⟨(159245511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (1273964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_B_last_return_by_valid : local_B_last_return_by.Valid := by norm_num [RationalBox.Valid, local_B_last_return_by]

def local_A_learning_complete_before_first_response_left : RationalBox := ⟨(425690169320350960321382328098421629068573 / 10000000000000000000000000000000000000000 : ℚ), (212845084660175480160691164049210814534287 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_learning_complete_before_first_response_left_valid : local_A_learning_complete_before_first_response_left.Valid := by norm_num [RationalBox.Valid, local_A_learning_complete_before_first_response_left]

def local_A_learning_complete_before_first_response_right : RationalBox := ⟨(493 / 10 : ℚ), (493 / 10 : ℚ)⟩
theorem local_A_learning_complete_before_first_response_right_valid : local_A_learning_complete_before_first_response_right.Valid := by norm_num [RationalBox.Valid, local_A_learning_complete_before_first_response_right]

def local_A_quiescent_before_measurement_left : RationalBox := ⟨(160870511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (1286964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_A_quiescent_before_measurement_left_valid : local_A_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, local_A_quiescent_before_measurement_left]

def local_A_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem local_A_quiescent_before_measurement_right_valid : local_A_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, local_A_quiescent_before_measurement_right]

def local_B_quiescent_before_measurement_left : RationalBox := ⟨(159245511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (1273964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem local_B_quiescent_before_measurement_left_valid : local_B_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, local_B_quiescent_before_measurement_left]

def local_B_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem local_B_quiescent_before_measurement_right_valid : local_B_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, local_B_quiescent_before_measurement_right]

def birth_slow_decay_dominates_noise_left : RationalBox := ⟨(31253906738342292786598324790598824853 / 1250000000000000000000000000000000000000 : ℚ), (10001250156269533691711463932991623953 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem birth_slow_decay_dominates_noise_left_valid : birth_slow_decay_dominates_noise_left.Valid := by norm_num [RationalBox.Valid, birth_slow_decay_dominates_noise_left]

def birth_slow_decay_dominates_noise_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem birth_slow_decay_dominates_noise_right_valid : birth_slow_decay_dominates_noise_right.Valid := by norm_num [RationalBox.Valid, birth_slow_decay_dominates_noise_right]

def protected_arrival_after_FAST_left : RationalBox := ⟨(19031333595863192783514092071573374658883 / 10000000000000000000000000000000000000000 : ℚ), (4757833398965798195878523017893343664721 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem protected_arrival_after_FAST_left_valid : protected_arrival_after_FAST_left.Valid := by norm_num [RationalBox.Valid, protected_arrival_after_FAST_left]

def protected_arrival_after_FAST_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem protected_arrival_after_FAST_right_valid : protected_arrival_after_FAST_right.Valid := by norm_num [RationalBox.Valid, protected_arrival_after_FAST_right]

def entire_protected_MARK_and_ERROR_before_reopen_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem entire_protected_MARK_and_ERROR_before_reopen_left_valid : entire_protected_MARK_and_ERROR_before_reopen_left.Valid := by norm_num [RationalBox.Valid, entire_protected_MARK_and_ERROR_before_reopen_left]

def entire_protected_MARK_and_ERROR_before_reopen_right : RationalBox := ⟨(1078981088294538415704241953178151566703 / 10000000000000000000000000000000000000000 : ℚ), (67436318018408650981515122073634472919 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem entire_protected_MARK_and_ERROR_before_reopen_right_valid : entire_protected_MARK_and_ERROR_before_reopen_right.Valid := by norm_num [RationalBox.Valid, entire_protected_MARK_and_ERROR_before_reopen_right]

def protected_input_reopens_by_deadline_left : RationalBox := ⟨(92537337843952838540812779588880404579 / 1000000000000000000000000000000000000000 : ℚ), (925373378439528385408127795888804045791 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_input_reopens_by_deadline_left_valid : protected_input_reopens_by_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_by_deadline_left]

def protected_input_reopens_by_deadline_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem protected_input_reopens_by_deadline_right_valid : protected_input_reopens_by_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_by_deadline_right]

def protected_aux_cycle_before_deadline_left : RationalBox := ⟨(12690169320350960321382328098421629068573 / 10000000000000000000000000000000000000000 : ℚ), (6345084660175480160691164049210814534287 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_aux_cycle_before_deadline_left_valid : protected_aux_cycle_before_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_aux_cycle_before_deadline_left]

def protected_aux_cycle_before_deadline_right : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_aux_cycle_before_deadline_right_valid : protected_aux_cycle_before_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_aux_cycle_before_deadline_right]

def protected_return_before_next_input_left : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_return_before_next_input_left_valid : protected_return_before_next_input_left.Valid := by norm_num [RationalBox.Valid, protected_return_before_next_input_left]

def protected_return_before_next_input_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem protected_return_before_next_input_right_valid : protected_return_before_next_input_right.Valid := by norm_num [RationalBox.Valid, protected_return_before_next_input_right]

def recovery_cap_not_reached_left : RationalBox := ⟨(1799699357778069765715623190334479789427 / 10000000000000000000000000000000000000000 : ℚ), (1800300642221930234284376809665520210573 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem recovery_cap_not_reached_left_valid : recovery_cap_not_reached_left.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_left]

def recovery_cap_not_reached_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem recovery_cap_not_reached_right_valid : recovery_cap_not_reached_right.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_right]

def unused_port1_birth_gain_below_caps_left : RationalBox := ⟨(5999940000299999000002499995000008333321 / 5000000000000000000000000000000000000000 : ℚ), (12000120000600002000005000010000016666691 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem unused_port1_birth_gain_below_caps_left_valid : unused_port1_birth_gain_below_caps_left.Valid := by norm_num [RationalBox.Valid, unused_port1_birth_gain_below_caps_left]

def unused_port1_birth_gain_below_caps_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem unused_port1_birth_gain_below_caps_right_valid : unused_port1_birth_gain_below_caps_right.Valid := by norm_num [RationalBox.Valid, unused_port1_birth_gain_below_caps_right]

def warmup_returns_before_entry_cut_left : RationalBox := ⟨(159245511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (1273964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem warmup_returns_before_entry_cut_left_valid : warmup_returns_before_entry_cut_left.Valid := by norm_num [RationalBox.Valid, warmup_returns_before_entry_cut_left]

def warmup_returns_before_entry_cut_right : RationalBox := ⟨(1599 / 10 : ℚ), (1599 / 10 : ℚ)⟩
theorem warmup_returns_before_entry_cut_right_valid : warmup_returns_before_entry_cut_right.Valid := by norm_num [RationalBox.Valid, warmup_returns_before_entry_cut_right]

def entry_charge_radius_inside_local_section_left : RationalBox := ⟨(401 / 100000 : ℚ), (401 / 100000 : ℚ)⟩
theorem entry_charge_radius_inside_local_section_left_valid : entry_charge_radius_inside_local_section_left.Valid := by norm_num [RationalBox.Valid, entry_charge_radius_inside_local_section_left]

def entry_charge_radius_inside_local_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem entry_charge_radius_inside_local_section_right_valid : entry_charge_radius_inside_local_section_right.Valid := by norm_num [RationalBox.Valid, entry_charge_radius_inside_local_section_right]

def entry_aux_band_below_threshold_left : RationalBox := ⟨(2901 / 100000 : ℚ), (2901 / 100000 : ℚ)⟩
theorem entry_aux_band_below_threshold_left_valid : entry_aux_band_below_threshold_left.Valid := by norm_num [RationalBox.Valid, entry_aux_band_below_threshold_left]

def entry_aux_band_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem entry_aux_band_below_threshold_right_valid : entry_aux_band_below_threshold_right.Valid := by norm_num [RationalBox.Valid, entry_aux_band_below_threshold_right]

def birth_recovery : RationalBox := ⟨(7999 / 100000 : ℚ), (8001 / 100000 : ℚ)⟩
theorem birth_recovery_valid : birth_recovery.Valid := by norm_num [RationalBox.Valid, birth_recovery]

def protected_MARK_dose : RationalBox := ⟨(999799357778069765715623190334479789427 / 10000000000000000000000000000000000000000 : ℚ), (1000200642221930234284376809665520210573 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_MARK_dose_valid : protected_MARK_dose.Valid := by norm_num [RationalBox.Valid, protected_MARK_dose]

def entry_recovery : RationalBox := ⟨(1799699357778069765715623190334479789427 / 10000000000000000000000000000000000000000 : ℚ), (1800300642221930234284376809665520210573 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem entry_recovery_valid : entry_recovery.Valid := by norm_num [RationalBox.Valid, entry_recovery]

def entry_charge_radius : RationalBox := ⟨(401 / 100000 : ℚ), (401 / 100000 : ℚ)⟩
theorem entry_charge_radius_valid : entry_charge_radius.Valid := by norm_num [RationalBox.Valid, entry_charge_radius]

def entry_q : RationalBox := ⟨(9599 / 100000 : ℚ), (10401 / 100000 : ℚ)⟩
theorem entry_q_valid : entry_q.Valid := by norm_num [RationalBox.Valid, entry_q]

def entry_m : RationalBox := ⟨(2099 / 100000 : ℚ), (2901 / 100000 : ℚ)⟩
theorem entry_m_valid : entry_m.Valid := by norm_num [RationalBox.Valid, entry_m]

def q_lower_at_protected_arrival : RationalBox := ⟨(692215530459654045861054417513765973057 / 5000000000000000000000000000000000000000 : ℚ), (276886212183861618344421767005506389223 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem q_lower_at_protected_arrival_valid : q_lower_at_protected_arrival.Valid := by norm_num [RationalBox.Valid, q_lower_at_protected_arrival]

def q_lower_through_protected_cycle : RationalBox := ⟨(1078981088294538415704241953178151566703 / 10000000000000000000000000000000000000000 : ℚ), (67436318018408650981515122073634472919 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem q_lower_through_protected_cycle_valid : q_lower_through_protected_cycle.Valid := by norm_num [RationalBox.Valid, q_lower_through_protected_cycle]

def q_upper_at_reopen_deadline : RationalBox := ⟨(92537337843952838540812779588880404579 / 1000000000000000000000000000000000000000 : ℚ), (925373378439528385408127795888804045791 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem q_upper_at_reopen_deadline_valid : q_upper_at_reopen_deadline.Valid := by norm_num [RationalBox.Valid, q_upper_at_reopen_deadline]

def protected_reopen_deadline : RationalBox := ⟨(7 / 2 : ℚ), (7 / 2 : ℚ)⟩
theorem protected_reopen_deadline_valid : protected_reopen_deadline.Valid := by norm_num [RationalBox.Valid, protected_reopen_deadline]

def last_warmup_return : RationalBox := ⟨(159245511534879034141719740766035788600971 / 1250000000000000000000000000000000000000 : ℚ), (1273964092279032273133757926128286308807769 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

end KernelR.Robust.Evidence.Birth1
