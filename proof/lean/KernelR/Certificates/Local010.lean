import KernelR.Intervals

/-! Generated exact endpoint checks. Analytic enclosure soundness is NOT asserted. -/
namespace KernelR.Certificates.Local010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def epsilon : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem epsilon_valid : epsilon.Valid := by norm_num [RationalBox.Valid, epsilon]

def a : RationalBox := ⟨(1386294361119890618834464242916353136151 / 1000000000000000000000000000000000000000 : ℚ), (13862943611198906188344642429163531361511 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem a_valid : a.Valid := by norm_num [RationalBox.Valid, a]

def kappa : RationalBox := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem kappa_valid : kappa.Valid := by norm_num [RationalBox.Valid, kappa]

def delta : RationalBox := ⟨(1 / 100000 : ℚ), (1 / 100000 : ℚ)⟩
theorem delta_valid : delta.Valid := by norm_num [RationalBox.Valid, delta]

def cap : RationalBox := ⟨(18 / 5 : ℚ), (22 / 5 : ℚ)⟩
theorem cap_valid : cap.Valid := by norm_num [RationalBox.Valid, cap]

def Lm : RationalBox := ⟨(10041459809139439009483279063942552651857 / 1000000000000000000000000000000000000000 : ℚ), (122728953222815365671462299670408976856031 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Lm_valid : Lm.Valid := by norm_num [RationalBox.Valid, Lm]

def Ls : RationalBox := ⟨(17655635731243889956854025735255440884941 / 10000000000000000000000000000000000000000 : ℚ), (5394777584546744153483174530216940270399 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem Ls_valid : Ls.Valid := by norm_num [RationalBox.Valid, Ls]

def Le : RationalBox := ⟨(4158883083359671856503392728749059408453 / 500000000000000000000000000000000000000 : ℚ), (101661586482125312047860711147199229984407 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Le_valid : Le.Valid := by norm_num [RationalBox.Valid, Le]

def M : RationalBox := ⟨(12900544781726378166238323015172510050413 / 400000000000000000000000000000000000000 : ℚ), (394183312774972666190615425463604473762621 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem M_valid : M.Valid := by norm_num [RationalBox.Valid, M]

def initial_gain : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem initial_gain_valid : initial_gain.Valid := by norm_num [RationalBox.Valid, initial_gain]

def learned_gain : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem learned_gain_valid : learned_gain.Valid := by norm_num [RationalBox.Valid, learned_gain]

def gain_log_dose : RationalBox := ⟨(3 / 5 : ℚ), (3 / 5 : ℚ)⟩
theorem gain_log_dose_valid : gain_log_dose.Valid := by norm_num [RationalBox.Valid, gain_log_dose]

def aux_at_early : RationalBox := ⟨(857777700395999170890784025356980226903 / 1250000000000000000000000000000000000000 : ℚ), (4165912371719864739736113183069689690047 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_at_early_valid : aux_at_early.Valid := by norm_num [RationalBox.Valid, aux_at_early]

def aux_at_late : RationalBox := ⟨(13289056706323197692444281225825371354033 / 10000000000000000000000000000000000000000 : ℚ), (8093421888524132263456113558930151776937 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_at_late_valid : aux_at_late.Valid := by norm_num [RationalBox.Valid, aux_at_late]

def aux_derivative : RationalBox := ⟨(104652753909468400451498982066330214586733 / 2500000000000000000000000000000000000000 : ℚ), (68880481100858260141341200869705380694399 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem aux_derivative_valid : aux_derivative.Valid := by norm_num [RationalBox.Valid, aux_derivative]

def mark_end : RationalBox := ⟨(331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem mark_end_valid : mark_end.Valid := by norm_num [RationalBox.Valid, mark_end]

def error_start : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (12300000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem error_start_valid : error_start.Valid := by norm_num [RationalBox.Valid, error_start]

def aux_finish : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_valid : aux_finish.Valid := by norm_num [RationalBox.Valid, aux_finish]

def raw_error_overlap_length : RationalBox := ⟨(0 / 1 : ℚ), (15909090909090909090909090909090909091 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem raw_error_overlap_length_valid : raw_error_overlap_length.Valid := by norm_num [RationalBox.Valid, raw_error_overlap_length]

def overlap_density_bound : RationalBox := ⟨(3481056809084084213160803442899595862423 / 10000000000000000000000000000000000000000 : ℚ), (435132101135510526645100430362449482803 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem overlap_density_bound_valid : overlap_density_bound.Valid := by norm_num [RationalBox.Valid, overlap_density_bound]

def min_input_gap : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem min_input_gap_valid : min_input_gap.Valid := by norm_num [RationalBox.Valid, min_input_gap]

def main_reopen_bound : RationalBox := ⟨(8737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (69907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem main_reopen_bound_valid : main_reopen_bound.Valid := by norm_num [RationalBox.Valid, main_reopen_bound]

def initial_aux_below_threshold_left : RationalBox := ⟨(2499 / 100000 : ℚ), (2501 / 100000 : ℚ)⟩
theorem initial_aux_below_threshold_left_valid : initial_aux_below_threshold_left.Valid := by norm_num [RationalBox.Valid, initial_aux_below_threshold_left]

def initial_aux_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem initial_aux_below_threshold_right_valid : initial_aux_below_threshold_right.Valid := by norm_num [RationalBox.Valid, initial_aux_below_threshold_right]

def aux_early_below_threshold_left : RationalBox := ⟨(857777700395999170890784025356980226903 / 1250000000000000000000000000000000000000 : ℚ), (4165912371719864739736113183069689690047 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_early_below_threshold_left_valid : aux_early_below_threshold_left.Valid := by norm_num [RationalBox.Valid, aux_early_below_threshold_left]

def aux_early_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_early_below_threshold_right_valid : aux_early_below_threshold_right.Valid := by norm_num [RationalBox.Valid, aux_early_below_threshold_right]

def aux_late_above_threshold_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_late_above_threshold_left_valid : aux_late_above_threshold_left.Valid := by norm_num [RationalBox.Valid, aux_late_above_threshold_left]

def aux_late_above_threshold_right : RationalBox := ⟨(13289056706323197692444281225825371354033 / 10000000000000000000000000000000000000000 : ℚ), (8093421888524132263456113558930151776937 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_late_above_threshold_right_valid : aux_late_above_threshold_right.Valid := by norm_num [RationalBox.Valid, aux_late_above_threshold_right]

def aux_first_root_is_strict_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem aux_first_root_is_strict_left_valid : aux_first_root_is_strict_left.Valid := by norm_num [RationalBox.Valid, aux_first_root_is_strict_left]

def aux_first_root_is_strict_right : RationalBox := ⟨(104652753909468400451498982066330214586733 / 2500000000000000000000000000000000000000 : ℚ), (68880481100858260141341200869705380694399 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem aux_first_root_is_strict_right_valid : aux_first_root_is_strict_right.Valid := by norm_num [RationalBox.Valid, aux_first_root_is_strict_right]

def aux_cycle_ends_after_raw_pulse_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_cycle_ends_after_raw_pulse_left_valid : aux_cycle_ends_after_raw_pulse_left.Valid := by norm_num [RationalBox.Valid, aux_cycle_ends_after_raw_pulse_left]

def aux_cycle_ends_after_raw_pulse_right : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (5665909090909090909090909090909090909091 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_cycle_ends_after_raw_pulse_right_valid : aux_cycle_ends_after_raw_pulse_right.Valid := by norm_num [RationalBox.Valid, aux_cycle_ends_after_raw_pulse_right]

def aux_cycle_ends_before_next_input_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_cycle_ends_before_next_input_left_valid : aux_cycle_ends_before_next_input_left.Valid := by norm_num [RationalBox.Valid, aux_cycle_ends_before_next_input_left]

def aux_cycle_ends_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem aux_cycle_ends_before_next_input_right_valid : aux_cycle_ends_before_next_input_right.Valid := by norm_num [RationalBox.Valid, aux_cycle_ends_before_next_input_right]

def learned_gain_below_all_caps_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem learned_gain_below_all_caps_left_valid : learned_gain_below_all_caps_left.Valid := by norm_num [RationalBox.Valid, learned_gain_below_all_caps_left]

def learned_gain_below_all_caps_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem learned_gain_below_all_caps_right_valid : learned_gain_below_all_caps_right.Valid := by norm_num [RationalBox.Valid, learned_gain_below_all_caps_right]

def mark_finishes_before_any_main_firing_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem mark_finishes_before_any_main_firing_left_valid : mark_finishes_before_any_main_firing_left.Valid := by norm_num [RationalBox.Valid, mark_finishes_before_any_main_firing_left]

def mark_finishes_before_any_main_firing_right : RationalBox := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem mark_finishes_before_any_main_firing_right_valid : mark_finishes_before_any_main_firing_right.Valid := by norm_num [RationalBox.Valid, mark_finishes_before_any_main_firing_right]

def main_fires_before_error_begins_left : RationalBox := ⟨(9 / 10 : ℚ), (9 / 10 : ℚ)⟩
theorem main_fires_before_error_begins_left_valid : main_fires_before_error_begins_left.Valid := by norm_num [RationalBox.Valid, main_fires_before_error_begins_left]

def main_fires_before_error_begins_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem main_fires_before_error_begins_right_valid : main_fires_before_error_begins_right.Valid := by norm_num [RationalBox.Valid, main_fires_before_error_begins_right]

def error_finishes_during_main_fast_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem error_finishes_during_main_fast_left_valid : error_finishes_during_main_fast_left.Valid := by norm_num [RationalBox.Valid, error_finishes_during_main_fast_left]

def error_finishes_during_main_fast_right : RationalBox := ⟨(3 / 2 : ℚ), (3 / 2 : ℚ)⟩
theorem error_finishes_during_main_fast_right_valid : error_finishes_during_main_fast_right.Valid := by norm_num [RationalBox.Valid, error_finishes_during_main_fast_right]

def main_reopens_before_next_input_left : RationalBox := ⟨(8737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (69907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem main_reopens_before_next_input_left_valid : main_reopens_before_next_input_left.Valid := by norm_num [RationalBox.Valid, main_reopens_before_next_input_left]

def main_reopens_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem main_reopens_before_next_input_right_valid : main_reopens_before_next_input_right.Valid := by norm_num [RationalBox.Valid, main_reopens_before_next_input_right]

def gain_before_0 : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem gain_before_0_valid : gain_before_0.Valid := by norm_num [RationalBox.Valid, gain_before_0]

def peak_bound_0 : RationalBox := ⟨(1336460667207075197453577978254452619791 / 5000000000000000000000000000000000000000 : ℚ), (571541286239082536331111206235332567449 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem peak_bound_0_valid : peak_bound_0.Valid := by norm_num [RationalBox.Valid, peak_bound_0]

def carry_bound_0 : RationalBox := ⟨(32433099753347992891436735613419756851 / 5000000000000000000000000000000000000000 : ℚ), (36015547626748757751303033613172161549 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem carry_bound_0_valid : carry_bound_0.Valid := by norm_num [RationalBox.Valid, carry_bound_0]

def silent_0_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem silent_0_positive_derivative_coefficient_left_valid : silent_0_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, silent_0_positive_derivative_coefficient_left]

def silent_0_positive_derivative_coefficient_right : RationalBox := ⟨(234614652182025324597025620160078202879 / 1000000000000000000000000000000000000000 : ℚ), (624060861554983020919224180575194350001 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem silent_0_positive_derivative_coefficient_right_valid : silent_0_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, silent_0_positive_derivative_coefficient_right]

def silent_0_frozen_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem silent_0_frozen_flow_increases_left_valid : silent_0_frozen_flow_increases_left.Valid := by norm_num [RationalBox.Valid, silent_0_frozen_flow_increases_left]

def silent_0_frozen_flow_increases_right : RationalBox := ⟨(14026414987518220352294549090553045151 / 312500000000000000000000000000000000000 : ℚ), (813128927969828348431183394546152387073 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_0_frozen_flow_increases_right_valid : silent_0_frozen_flow_increases_right.Valid := by norm_num [RationalBox.Valid, silent_0_frozen_flow_increases_right]

def silent_0_no_first_crossing_even_with_overlap_left : RationalBox := ⟨(1336460667207075197453577978254452619791 / 5000000000000000000000000000000000000000 : ℚ), (571541286239082536331111206235332567449 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_0_no_first_crossing_even_with_overlap_left_valid : silent_0_no_first_crossing_even_with_overlap_left.Valid := by norm_num [RationalBox.Valid, silent_0_no_first_crossing_even_with_overlap_left]

def silent_0_no_first_crossing_even_with_overlap_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem silent_0_no_first_crossing_even_with_overlap_right_valid : silent_0_no_first_crossing_even_with_overlap_right.Valid := by norm_num [RationalBox.Valid, silent_0_no_first_crossing_even_with_overlap_right]

def silent_0_charge_returns_to_section_left : RationalBox := ⟨(32433099753347992891436735613419756851 / 5000000000000000000000000000000000000000 : ℚ), (36015547626748757751303033613172161549 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_0_charge_returns_to_section_left_valid : silent_0_charge_returns_to_section_left.Valid := by norm_num [RationalBox.Valid, silent_0_charge_returns_to_section_left]

def silent_0_charge_returns_to_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem silent_0_charge_returns_to_section_right_valid : silent_0_charge_returns_to_section_right.Valid := by norm_num [RationalBox.Valid, silent_0_charge_returns_to_section_right]

def gain_before_1 : RationalBox := ⟨(1093260347576166423671662107676113018829 / 2000000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem gain_before_1_valid : gain_before_1.Valid := by norm_num [RationalBox.Valid, gain_before_1]

def peak_bound_1 : RationalBox := ⟨(809662255807247503471415184607783861073 / 2000000000000000000000000000000000000000 : ℚ), (4235369736378614694706129628037248725067 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem peak_bound_1_valid : peak_bound_1.Valid := by norm_num [RationalBox.Valid, peak_bound_1]

def carry_bound_1 : RationalBox := ⟨(118195855069133417760095177713621038169 / 10000000000000000000000000000000000000000 : ℚ), (125448898570808056413847959108212418361 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem carry_bound_1_valid : carry_bound_1.Valid := by norm_num [RationalBox.Valid, carry_bound_1]

def silent_1_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem silent_1_positive_derivative_coefficient_left_valid : silent_1_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, silent_1_positive_derivative_coefficient_left]

def silent_1_positive_derivative_coefficient_right : RationalBox := ⟨(1068749697954876114708902087903751941771 / 2500000000000000000000000000000000000000 : ℚ), (4425134293650356307382242154168918002043 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_1_positive_derivative_coefficient_right_valid : silent_1_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, silent_1_positive_derivative_coefficient_right]

def silent_1_frozen_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem silent_1_frozen_flow_increases_left_valid : silent_1_frozen_flow_increases_left.Valid := by norm_num [RationalBox.Valid, silent_1_frozen_flow_increases_left]

def silent_1_frozen_flow_increases_right : RationalBox := ⟨(558516788722282749712944555478656629023 / 5000000000000000000000000000000000000000 : ℚ), (740758889371765803856086266343378159407 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_1_frozen_flow_increases_right_valid : silent_1_frozen_flow_increases_right.Valid := by norm_num [RationalBox.Valid, silent_1_frozen_flow_increases_right]

def silent_1_no_first_crossing_even_with_overlap_left : RationalBox := ⟨(809662255807247503471415184607783861073 / 2000000000000000000000000000000000000000 : ℚ), (4235369736378614694706129628037248725067 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_1_no_first_crossing_even_with_overlap_left_valid : silent_1_no_first_crossing_even_with_overlap_left.Valid := by norm_num [RationalBox.Valid, silent_1_no_first_crossing_even_with_overlap_left]

def silent_1_no_first_crossing_even_with_overlap_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem silent_1_no_first_crossing_even_with_overlap_right_valid : silent_1_no_first_crossing_even_with_overlap_right.Valid := by norm_num [RationalBox.Valid, silent_1_no_first_crossing_even_with_overlap_right]

def silent_1_charge_returns_to_section_left : RationalBox := ⟨(118195855069133417760095177713621038169 / 10000000000000000000000000000000000000000 : ℚ), (125448898570808056413847959108212418361 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_1_charge_returns_to_section_left_valid : silent_1_charge_returns_to_section_left.Valid := by norm_num [RationalBox.Valid, silent_1_charge_returns_to_section_left]

def silent_1_charge_returns_to_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem silent_1_charge_returns_to_section_right_valid : silent_1_charge_returns_to_section_right.Valid := by norm_num [RationalBox.Valid, silent_1_charge_returns_to_section_right]

def gain_before_2 : RationalBox := ⟨(9960251165199976250523787258791057471269 / 10000000000000000000000000000000000000000 : ℚ), (9960450372215343763490081857984907714419 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem gain_before_2_valid : gain_before_2.Valid := by norm_num [RationalBox.Valid, gain_before_2]

def peak_bound_2 : RationalBox := ⟨(6554435155000203475739237101113647071117 / 10000000000000000000000000000000000000000 : ℚ), (6745635945361054411913928144783421678443 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem peak_bound_2_valid : peak_bound_2.Valid := by norm_num [RationalBox.Valid, peak_bound_2]

def carry_bound_2 : RationalBox := ⟨(420642232593361221706359202354505541 / 19531250000000000000000000000000000000 : ℚ), (111391241135421045029963947676311203449 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem carry_bound_2_valid : carry_bound_2.Valid := by norm_num [RationalBox.Valid, carry_bound_2]

def silent_2_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem silent_2_positive_derivative_coefficient_left_valid : silent_2_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, silent_2_positive_derivative_coefficient_left]

def silent_2_positive_derivative_coefficient_right : RationalBox := ⟨(7789596776161050202363801858500545502817 / 10000000000000000000000000000000000000000 : ℚ), (3969901285327256582423845954654879575583 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_2_positive_derivative_coefficient_right_valid : silent_2_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, silent_2_positive_derivative_coefficient_right]

def silent_2_frozen_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem silent_2_frozen_flow_increases_left_valid : silent_2_frozen_flow_increases_left.Valid := by norm_num [RationalBox.Valid, silent_2_frozen_flow_increases_left]

def silent_2_frozen_flow_increases_right : RationalBox := ⟨(2334552037147018912289288623693919590131 / 10000000000000000000000000000000000000000 : ℚ), (2699401669709702707003101279578656274967 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_2_frozen_flow_increases_right_valid : silent_2_frozen_flow_increases_right.Valid := by norm_num [RationalBox.Valid, silent_2_frozen_flow_increases_right]

def silent_2_no_first_crossing_even_with_overlap_left : RationalBox := ⟨(6554435155000203475739237101113647071117 / 10000000000000000000000000000000000000000 : ℚ), (6745635945361054411913928144783421678443 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_2_no_first_crossing_even_with_overlap_left_valid : silent_2_no_first_crossing_even_with_overlap_left.Valid := by norm_num [RationalBox.Valid, silent_2_no_first_crossing_even_with_overlap_left]

def silent_2_no_first_crossing_even_with_overlap_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem silent_2_no_first_crossing_even_with_overlap_right_valid : silent_2_no_first_crossing_even_with_overlap_right.Valid := by norm_num [RationalBox.Valid, silent_2_no_first_crossing_even_with_overlap_right]

def silent_2_charge_returns_to_section_left : RationalBox := ⟨(420642232593361221706359202354505541 / 19531250000000000000000000000000000000 : ℚ), (111391241135421045029963947676311203449 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem silent_2_charge_returns_to_section_left_valid : silent_2_charge_returns_to_section_left.Valid := by norm_num [RationalBox.Valid, silent_2_charge_returns_to_section_left]

def silent_2_charge_returns_to_section_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem silent_2_charge_returns_to_section_right_valid : silent_2_charge_returns_to_section_right.Valid := by norm_num [RationalBox.Valid, silent_2_charge_returns_to_section_right]

def learned_ready_early : RationalBox := ⟨(8914330190785786031236358272500993673019 / 10000000000000000000000000000000000000000 : ℚ), (9148206595529824080829844384603189791057 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem learned_ready_early_valid : learned_ready_early.Valid := by norm_num [RationalBox.Valid, learned_ready_early]

def learned_ready_late : RationalBox := ⟨(10948374960726511098322810098010980394129 / 10000000000000000000000000000000000000000 : ℚ), (11139926139792377106420383113815579433053 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem learned_ready_late_valid : learned_ready_late.Valid := by norm_num [RationalBox.Valid, learned_ready_late]

def learned_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem learned_positive_derivative_coefficient_left_valid : learned_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, learned_positive_derivative_coefficient_left]

def learned_positive_derivative_coefficient_right : RationalBox := ⟨(7096805919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2868789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem learned_positive_derivative_coefficient_right_valid : learned_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, learned_positive_derivative_coefficient_right]

def learned_flow_strictly_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem learned_flow_strictly_increases_left_valid : learned_flow_strictly_increases_left.Valid := by norm_num [RationalBox.Valid, learned_flow_strictly_increases_left]

def learned_flow_strictly_increases_right : RationalBox := ⟨(4553015312393353567582092430317193151263 / 10000000000000000000000000000000000000000 : ℚ), (2459265402065953910408096372585777497291 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem learned_flow_strictly_increases_right_valid : learned_flow_strictly_increases_right.Valid := by norm_num [RationalBox.Valid, learned_flow_strictly_increases_right]

def learned_early_below_threshold_left : RationalBox := ⟨(8914330190785786031236358272500993673019 / 10000000000000000000000000000000000000000 : ℚ), (9148206595529824080829844384603189791057 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem learned_early_below_threshold_left_valid : learned_early_below_threshold_left.Valid := by norm_num [RationalBox.Valid, learned_early_below_threshold_left]

def learned_early_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem learned_early_below_threshold_right_valid : learned_early_below_threshold_right.Valid := by norm_num [RationalBox.Valid, learned_early_below_threshold_right]

def learned_late_above_threshold_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem learned_late_above_threshold_left_valid : learned_late_above_threshold_left.Valid := by norm_num [RationalBox.Valid, learned_late_above_threshold_left]

def learned_late_above_threshold_right : RationalBox := ⟨(10948374960726511098322810098010980394129 / 10000000000000000000000000000000000000000 : ℚ), (11139926139792377106420383113815579433053 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem learned_late_above_threshold_right_valid : learned_late_above_threshold_right.Valid := by norm_num [RationalBox.Valid, learned_late_above_threshold_right]

def work_bound : RationalBox := ⟨(10573936830325210453707713866907429323159 / 40000000000000000000000000000000000000 : ℚ), (2643484207581302613426928466726857330789751 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem work_bound_valid : work_bound.Valid := by norm_num [RationalBox.Valid, work_bound]

def reserve_gate_stays_open_left : RationalBox := ⟨(10573936830325210453707713866907429323159 / 40000000000000000000000000000000000000 : ℚ), (2643484207581302613426928466726857330789751 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem reserve_gate_stays_open_left_valid : reserve_gate_stays_open_left.Valid := by norm_num [RationalBox.Valid, reserve_gate_stays_open_left]

def reserve_gate_stays_open_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem reserve_gate_stays_open_right_valid : reserve_gate_stays_open_right.Valid := by norm_num [RationalBox.Valid, reserve_gate_stays_open_right]

def B_first_emission : RationalBox := ⟨(49 / 2 : ℚ), (249 / 10 : ℚ)⟩
theorem B_first_emission_valid : B_first_emission.Valid := by norm_num [RationalBox.Valid, B_first_emission]

def A_first_arrival : RationalBox := ⟨(124 / 5 : ℚ), (253 / 10 : ℚ)⟩
theorem A_first_arrival_valid : A_first_arrival.Valid := by norm_num [RationalBox.Valid, A_first_arrival]

def A_gain_complete_by : RationalBox := ⟨(213483333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (426966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_gain_complete_by_valid : A_gain_complete_by.Valid := by norm_num [RationalBox.Valid, A_gain_complete_by]

def A_first_emission : RationalBox := ⟨(493 / 10 : ℚ), (251 / 5 : ℚ)⟩
theorem A_first_emission_valid : A_first_emission.Valid := by norm_num [RationalBox.Valid, A_first_emission]

def A_last_emission : RationalBox := ⟨(1213 / 10 : ℚ), (611 / 5 : ℚ)⟩
theorem A_last_emission_valid : A_last_emission.Valid := by norm_num [RationalBox.Valid, A_last_emission]

def A_last_return_by : RationalBox := ⟨(160362776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (1282907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_last_return_by_valid : A_last_return_by.Valid := by norm_num [RationalBox.Valid, A_last_return_by]

def B_last_return_by : RationalBox := ⟨(158737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_last_return_by_valid : B_last_return_by.Valid := by norm_num [RationalBox.Valid, B_last_return_by]

def A_learning_complete_before_first_response_left : RationalBox := ⟨(213483333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (426966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_learning_complete_before_first_response_left_valid : A_learning_complete_before_first_response_left.Valid := by norm_num [RationalBox.Valid, A_learning_complete_before_first_response_left]

def A_learning_complete_before_first_response_right : RationalBox := ⟨(493 / 10 : ℚ), (493 / 10 : ℚ)⟩
theorem A_learning_complete_before_first_response_right_valid : A_learning_complete_before_first_response_right.Valid := by norm_num [RationalBox.Valid, A_learning_complete_before_first_response_right]

def A_quiescent_before_measurement_left : RationalBox := ⟨(160362776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (1282907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_quiescent_before_measurement_left_valid : A_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, A_quiescent_before_measurement_left]

def A_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem A_quiescent_before_measurement_right_valid : A_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, A_quiescent_before_measurement_right]

def B_quiescent_before_measurement_left : RationalBox := ⟨(158737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_quiescent_before_measurement_left_valid : B_quiescent_before_measurement_left.Valid := by norm_num [RationalBox.Valid, B_quiescent_before_measurement_left]

def B_quiescent_before_measurement_right : RationalBox := ⟨(1399 / 10 : ℚ), (1399 / 10 : ℚ)⟩
theorem B_quiescent_before_measurement_right_valid : B_quiescent_before_measurement_right.Valid := by norm_num [RationalBox.Valid, B_quiescent_before_measurement_right]

theorem initial_aux_below_threshold_verified : RationalBox.StrictBefore initial_aux_below_threshold_left initial_aux_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, initial_aux_below_threshold_left, initial_aux_below_threshold_right]

theorem aux_early_below_threshold_verified : RationalBox.StrictBefore aux_early_below_threshold_left aux_early_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, aux_early_below_threshold_left, aux_early_below_threshold_right]

theorem aux_late_above_threshold_verified : RationalBox.StrictBefore aux_late_above_threshold_left aux_late_above_threshold_right := by
  norm_num [RationalBox.StrictBefore, aux_late_above_threshold_left, aux_late_above_threshold_right]

theorem aux_first_root_is_strict_verified : RationalBox.StrictBefore aux_first_root_is_strict_left aux_first_root_is_strict_right := by
  norm_num [RationalBox.StrictBefore, aux_first_root_is_strict_left, aux_first_root_is_strict_right]

theorem aux_cycle_ends_after_raw_pulse_verified : RationalBox.StrictBefore aux_cycle_ends_after_raw_pulse_left aux_cycle_ends_after_raw_pulse_right := by
  norm_num [RationalBox.StrictBefore, aux_cycle_ends_after_raw_pulse_left, aux_cycle_ends_after_raw_pulse_right]

theorem aux_cycle_ends_before_next_input_verified : RationalBox.StrictBefore aux_cycle_ends_before_next_input_left aux_cycle_ends_before_next_input_right := by
  norm_num [RationalBox.StrictBefore, aux_cycle_ends_before_next_input_left, aux_cycle_ends_before_next_input_right]

theorem learned_gain_below_all_caps_verified : RationalBox.StrictBefore learned_gain_below_all_caps_left learned_gain_below_all_caps_right := by
  norm_num [RationalBox.StrictBefore, learned_gain_below_all_caps_left, learned_gain_below_all_caps_right]

theorem mark_finishes_before_any_main_firing_verified : RationalBox.StrictBefore mark_finishes_before_any_main_firing_left mark_finishes_before_any_main_firing_right := by
  norm_num [RationalBox.StrictBefore, mark_finishes_before_any_main_firing_left, mark_finishes_before_any_main_firing_right]

theorem main_fires_before_error_begins_verified : RationalBox.StrictBefore main_fires_before_error_begins_left main_fires_before_error_begins_right := by
  norm_num [RationalBox.StrictBefore, main_fires_before_error_begins_left, main_fires_before_error_begins_right]

theorem error_finishes_during_main_fast_verified : RationalBox.StrictBefore error_finishes_during_main_fast_left error_finishes_during_main_fast_right := by
  norm_num [RationalBox.StrictBefore, error_finishes_during_main_fast_left, error_finishes_during_main_fast_right]

theorem main_reopens_before_next_input_verified : RationalBox.StrictBefore main_reopens_before_next_input_left main_reopens_before_next_input_right := by
  norm_num [RationalBox.StrictBefore, main_reopens_before_next_input_left, main_reopens_before_next_input_right]

theorem silent_0_positive_derivative_coefficient_verified : RationalBox.StrictBefore silent_0_positive_derivative_coefficient_left silent_0_positive_derivative_coefficient_right := by
  norm_num [RationalBox.StrictBefore, silent_0_positive_derivative_coefficient_left, silent_0_positive_derivative_coefficient_right]

theorem silent_0_frozen_flow_increases_verified : RationalBox.StrictBefore silent_0_frozen_flow_increases_left silent_0_frozen_flow_increases_right := by
  norm_num [RationalBox.StrictBefore, silent_0_frozen_flow_increases_left, silent_0_frozen_flow_increases_right]

theorem silent_0_no_first_crossing_even_with_overlap_verified : RationalBox.StrictBefore silent_0_no_first_crossing_even_with_overlap_left silent_0_no_first_crossing_even_with_overlap_right := by
  norm_num [RationalBox.StrictBefore, silent_0_no_first_crossing_even_with_overlap_left, silent_0_no_first_crossing_even_with_overlap_right]

theorem silent_0_charge_returns_to_section_verified : RationalBox.StrictBefore silent_0_charge_returns_to_section_left silent_0_charge_returns_to_section_right := by
  norm_num [RationalBox.StrictBefore, silent_0_charge_returns_to_section_left, silent_0_charge_returns_to_section_right]

theorem silent_1_positive_derivative_coefficient_verified : RationalBox.StrictBefore silent_1_positive_derivative_coefficient_left silent_1_positive_derivative_coefficient_right := by
  norm_num [RationalBox.StrictBefore, silent_1_positive_derivative_coefficient_left, silent_1_positive_derivative_coefficient_right]

theorem silent_1_frozen_flow_increases_verified : RationalBox.StrictBefore silent_1_frozen_flow_increases_left silent_1_frozen_flow_increases_right := by
  norm_num [RationalBox.StrictBefore, silent_1_frozen_flow_increases_left, silent_1_frozen_flow_increases_right]

theorem silent_1_no_first_crossing_even_with_overlap_verified : RationalBox.StrictBefore silent_1_no_first_crossing_even_with_overlap_left silent_1_no_first_crossing_even_with_overlap_right := by
  norm_num [RationalBox.StrictBefore, silent_1_no_first_crossing_even_with_overlap_left, silent_1_no_first_crossing_even_with_overlap_right]

theorem silent_1_charge_returns_to_section_verified : RationalBox.StrictBefore silent_1_charge_returns_to_section_left silent_1_charge_returns_to_section_right := by
  norm_num [RationalBox.StrictBefore, silent_1_charge_returns_to_section_left, silent_1_charge_returns_to_section_right]

theorem silent_2_positive_derivative_coefficient_verified : RationalBox.StrictBefore silent_2_positive_derivative_coefficient_left silent_2_positive_derivative_coefficient_right := by
  norm_num [RationalBox.StrictBefore, silent_2_positive_derivative_coefficient_left, silent_2_positive_derivative_coefficient_right]

theorem silent_2_frozen_flow_increases_verified : RationalBox.StrictBefore silent_2_frozen_flow_increases_left silent_2_frozen_flow_increases_right := by
  norm_num [RationalBox.StrictBefore, silent_2_frozen_flow_increases_left, silent_2_frozen_flow_increases_right]

theorem silent_2_no_first_crossing_even_with_overlap_verified : RationalBox.StrictBefore silent_2_no_first_crossing_even_with_overlap_left silent_2_no_first_crossing_even_with_overlap_right := by
  norm_num [RationalBox.StrictBefore, silent_2_no_first_crossing_even_with_overlap_left, silent_2_no_first_crossing_even_with_overlap_right]

theorem silent_2_charge_returns_to_section_verified : RationalBox.StrictBefore silent_2_charge_returns_to_section_left silent_2_charge_returns_to_section_right := by
  norm_num [RationalBox.StrictBefore, silent_2_charge_returns_to_section_left, silent_2_charge_returns_to_section_right]

theorem learned_positive_derivative_coefficient_verified : RationalBox.StrictBefore learned_positive_derivative_coefficient_left learned_positive_derivative_coefficient_right := by
  norm_num [RationalBox.StrictBefore, learned_positive_derivative_coefficient_left, learned_positive_derivative_coefficient_right]

theorem learned_flow_strictly_increases_verified : RationalBox.StrictBefore learned_flow_strictly_increases_left learned_flow_strictly_increases_right := by
  norm_num [RationalBox.StrictBefore, learned_flow_strictly_increases_left, learned_flow_strictly_increases_right]

theorem learned_early_below_threshold_verified : RationalBox.StrictBefore learned_early_below_threshold_left learned_early_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, learned_early_below_threshold_left, learned_early_below_threshold_right]

theorem learned_late_above_threshold_verified : RationalBox.StrictBefore learned_late_above_threshold_left learned_late_above_threshold_right := by
  norm_num [RationalBox.StrictBefore, learned_late_above_threshold_left, learned_late_above_threshold_right]

theorem reserve_gate_stays_open_verified : RationalBox.StrictBefore reserve_gate_stays_open_left reserve_gate_stays_open_right := by
  norm_num [RationalBox.StrictBefore, reserve_gate_stays_open_left, reserve_gate_stays_open_right]

theorem A_learning_complete_before_first_response_verified : RationalBox.StrictBefore A_learning_complete_before_first_response_left A_learning_complete_before_first_response_right := by
  norm_num [RationalBox.StrictBefore, A_learning_complete_before_first_response_left, A_learning_complete_before_first_response_right]

theorem A_quiescent_before_measurement_verified : RationalBox.StrictBefore A_quiescent_before_measurement_left A_quiescent_before_measurement_right := by
  norm_num [RationalBox.StrictBefore, A_quiescent_before_measurement_left, A_quiescent_before_measurement_right]

theorem B_quiescent_before_measurement_verified : RationalBox.StrictBefore B_quiescent_before_measurement_left B_quiescent_before_measurement_right := by
  norm_num [RationalBox.StrictBefore, B_quiescent_before_measurement_left, B_quiescent_before_measurement_right]

def Obligations : Prop :=
  RationalBox.StrictBefore initial_aux_below_threshold_left initial_aux_below_threshold_right ∧
  RationalBox.StrictBefore aux_early_below_threshold_left aux_early_below_threshold_right ∧
  RationalBox.StrictBefore aux_late_above_threshold_left aux_late_above_threshold_right ∧
  RationalBox.StrictBefore aux_first_root_is_strict_left aux_first_root_is_strict_right ∧
  RationalBox.StrictBefore aux_cycle_ends_after_raw_pulse_left aux_cycle_ends_after_raw_pulse_right ∧
  RationalBox.StrictBefore aux_cycle_ends_before_next_input_left aux_cycle_ends_before_next_input_right ∧
  RationalBox.StrictBefore learned_gain_below_all_caps_left learned_gain_below_all_caps_right ∧
  RationalBox.StrictBefore mark_finishes_before_any_main_firing_left mark_finishes_before_any_main_firing_right ∧
  RationalBox.StrictBefore main_fires_before_error_begins_left main_fires_before_error_begins_right ∧
  RationalBox.StrictBefore error_finishes_during_main_fast_left error_finishes_during_main_fast_right ∧
  RationalBox.StrictBefore main_reopens_before_next_input_left main_reopens_before_next_input_right ∧
  RationalBox.StrictBefore silent_0_positive_derivative_coefficient_left silent_0_positive_derivative_coefficient_right ∧
  RationalBox.StrictBefore silent_0_frozen_flow_increases_left silent_0_frozen_flow_increases_right ∧
  RationalBox.StrictBefore silent_0_no_first_crossing_even_with_overlap_left silent_0_no_first_crossing_even_with_overlap_right ∧
  RationalBox.StrictBefore silent_0_charge_returns_to_section_left silent_0_charge_returns_to_section_right ∧
  RationalBox.StrictBefore silent_1_positive_derivative_coefficient_left silent_1_positive_derivative_coefficient_right ∧
  RationalBox.StrictBefore silent_1_frozen_flow_increases_left silent_1_frozen_flow_increases_right ∧
  RationalBox.StrictBefore silent_1_no_first_crossing_even_with_overlap_left silent_1_no_first_crossing_even_with_overlap_right ∧
  RationalBox.StrictBefore silent_1_charge_returns_to_section_left silent_1_charge_returns_to_section_right ∧
  RationalBox.StrictBefore silent_2_positive_derivative_coefficient_left silent_2_positive_derivative_coefficient_right ∧
  RationalBox.StrictBefore silent_2_frozen_flow_increases_left silent_2_frozen_flow_increases_right ∧
  RationalBox.StrictBefore silent_2_no_first_crossing_even_with_overlap_left silent_2_no_first_crossing_even_with_overlap_right ∧
  RationalBox.StrictBefore silent_2_charge_returns_to_section_left silent_2_charge_returns_to_section_right ∧
  RationalBox.StrictBefore learned_positive_derivative_coefficient_left learned_positive_derivative_coefficient_right ∧
  RationalBox.StrictBefore learned_flow_strictly_increases_left learned_flow_strictly_increases_right ∧
  RationalBox.StrictBefore learned_early_below_threshold_left learned_early_below_threshold_right ∧
  RationalBox.StrictBefore learned_late_above_threshold_left learned_late_above_threshold_right ∧
  RationalBox.StrictBefore reserve_gate_stays_open_left reserve_gate_stays_open_right ∧
  RationalBox.StrictBefore A_learning_complete_before_first_response_left A_learning_complete_before_first_response_right ∧
  RationalBox.StrictBefore A_quiescent_before_measurement_left A_quiescent_before_measurement_right ∧
  RationalBox.StrictBefore B_quiescent_before_measurement_left B_quiescent_before_measurement_right
theorem obligations_verified : Obligations := by
  exact ⟨initial_aux_below_threshold_verified, aux_early_below_threshold_verified, aux_late_above_threshold_verified, aux_first_root_is_strict_verified, aux_cycle_ends_after_raw_pulse_verified, aux_cycle_ends_before_next_input_verified, learned_gain_below_all_caps_verified, mark_finishes_before_any_main_firing_verified, main_fires_before_error_begins_verified, error_finishes_during_main_fast_verified, main_reopens_before_next_input_verified, silent_0_positive_derivative_coefficient_verified, silent_0_frozen_flow_increases_verified, silent_0_no_first_crossing_even_with_overlap_verified, silent_0_charge_returns_to_section_verified, silent_1_positive_derivative_coefficient_verified, silent_1_frozen_flow_increases_verified, silent_1_no_first_crossing_even_with_overlap_verified, silent_1_charge_returns_to_section_verified, silent_2_positive_derivative_coefficient_verified, silent_2_frozen_flow_increases_verified, silent_2_no_first_crossing_even_with_overlap_verified, silent_2_charge_returns_to_section_verified, learned_positive_derivative_coefficient_verified, learned_flow_strictly_increases_verified, learned_early_below_threshold_verified, learned_late_above_threshold_verified, reserve_gate_stays_open_verified, A_learning_complete_before_first_response_verified, A_quiescent_before_measurement_verified, B_quiescent_before_measurement_verified⟩

def AllBoundsValid : Prop :=
  epsilon.Valid ∧
  a.Valid ∧
  kappa.Valid ∧
  delta.Valid ∧
  cap.Valid ∧
  Lm.Valid ∧
  Ls.Valid ∧
  Le.Valid ∧
  M.Valid ∧
  initial_gain.Valid ∧
  learned_gain.Valid ∧
  gain_log_dose.Valid ∧
  aux_at_early.Valid ∧
  aux_at_late.Valid ∧
  aux_derivative.Valid ∧
  mark_end.Valid ∧
  error_start.Valid ∧
  aux_finish.Valid ∧
  raw_error_overlap_length.Valid ∧
  overlap_density_bound.Valid ∧
  min_input_gap.Valid ∧
  main_reopen_bound.Valid ∧
  initial_aux_below_threshold_left.Valid ∧
  initial_aux_below_threshold_right.Valid ∧
  aux_early_below_threshold_left.Valid ∧
  aux_early_below_threshold_right.Valid ∧
  aux_late_above_threshold_left.Valid ∧
  aux_late_above_threshold_right.Valid ∧
  aux_first_root_is_strict_left.Valid ∧
  aux_first_root_is_strict_right.Valid ∧
  aux_cycle_ends_after_raw_pulse_left.Valid ∧
  aux_cycle_ends_after_raw_pulse_right.Valid ∧
  aux_cycle_ends_before_next_input_left.Valid ∧
  aux_cycle_ends_before_next_input_right.Valid ∧
  learned_gain_below_all_caps_left.Valid ∧
  learned_gain_below_all_caps_right.Valid ∧
  mark_finishes_before_any_main_firing_left.Valid ∧
  mark_finishes_before_any_main_firing_right.Valid ∧
  main_fires_before_error_begins_left.Valid ∧
  main_fires_before_error_begins_right.Valid ∧
  error_finishes_during_main_fast_left.Valid ∧
  error_finishes_during_main_fast_right.Valid ∧
  main_reopens_before_next_input_left.Valid ∧
  main_reopens_before_next_input_right.Valid ∧
  gain_before_0.Valid ∧
  peak_bound_0.Valid ∧
  carry_bound_0.Valid ∧
  silent_0_positive_derivative_coefficient_left.Valid ∧
  silent_0_positive_derivative_coefficient_right.Valid ∧
  silent_0_frozen_flow_increases_left.Valid ∧
  silent_0_frozen_flow_increases_right.Valid ∧
  silent_0_no_first_crossing_even_with_overlap_left.Valid ∧
  silent_0_no_first_crossing_even_with_overlap_right.Valid ∧
  silent_0_charge_returns_to_section_left.Valid ∧
  silent_0_charge_returns_to_section_right.Valid ∧
  gain_before_1.Valid ∧
  peak_bound_1.Valid ∧
  carry_bound_1.Valid ∧
  silent_1_positive_derivative_coefficient_left.Valid ∧
  silent_1_positive_derivative_coefficient_right.Valid ∧
  silent_1_frozen_flow_increases_left.Valid ∧
  silent_1_frozen_flow_increases_right.Valid ∧
  silent_1_no_first_crossing_even_with_overlap_left.Valid ∧
  silent_1_no_first_crossing_even_with_overlap_right.Valid ∧
  silent_1_charge_returns_to_section_left.Valid ∧
  silent_1_charge_returns_to_section_right.Valid ∧
  gain_before_2.Valid ∧
  peak_bound_2.Valid ∧
  carry_bound_2.Valid ∧
  silent_2_positive_derivative_coefficient_left.Valid ∧
  silent_2_positive_derivative_coefficient_right.Valid ∧
  silent_2_frozen_flow_increases_left.Valid ∧
  silent_2_frozen_flow_increases_right.Valid ∧
  silent_2_no_first_crossing_even_with_overlap_left.Valid ∧
  silent_2_no_first_crossing_even_with_overlap_right.Valid ∧
  silent_2_charge_returns_to_section_left.Valid ∧
  silent_2_charge_returns_to_section_right.Valid ∧
  learned_ready_early.Valid ∧
  learned_ready_late.Valid ∧
  learned_positive_derivative_coefficient_left.Valid ∧
  learned_positive_derivative_coefficient_right.Valid ∧
  learned_flow_strictly_increases_left.Valid ∧
  learned_flow_strictly_increases_right.Valid ∧
  learned_early_below_threshold_left.Valid ∧
  learned_early_below_threshold_right.Valid ∧
  learned_late_above_threshold_left.Valid ∧
  learned_late_above_threshold_right.Valid ∧
  work_bound.Valid ∧
  reserve_gate_stays_open_left.Valid ∧
  reserve_gate_stays_open_right.Valid ∧
  B_first_emission.Valid ∧
  A_first_arrival.Valid ∧
  A_gain_complete_by.Valid ∧
  A_first_emission.Valid ∧
  A_last_emission.Valid ∧
  A_last_return_by.Valid ∧
  B_last_return_by.Valid ∧
  A_learning_complete_before_first_response_left.Valid ∧
  A_learning_complete_before_first_response_right.Valid ∧
  A_quiescent_before_measurement_left.Valid ∧
  A_quiescent_before_measurement_right.Valid ∧
  B_quiescent_before_measurement_left.Valid ∧
  B_quiescent_before_measurement_right.Valid
theorem all_bounds_valid : AllBoundsValid := by
  exact ⟨epsilon_valid, a_valid, kappa_valid, delta_valid, cap_valid, Lm_valid, Ls_valid, Le_valid, M_valid, initial_gain_valid, learned_gain_valid, gain_log_dose_valid, aux_at_early_valid, aux_at_late_valid, aux_derivative_valid, mark_end_valid, error_start_valid, aux_finish_valid, raw_error_overlap_length_valid, overlap_density_bound_valid, min_input_gap_valid, main_reopen_bound_valid, initial_aux_below_threshold_left_valid, initial_aux_below_threshold_right_valid, aux_early_below_threshold_left_valid, aux_early_below_threshold_right_valid, aux_late_above_threshold_left_valid, aux_late_above_threshold_right_valid, aux_first_root_is_strict_left_valid, aux_first_root_is_strict_right_valid, aux_cycle_ends_after_raw_pulse_left_valid, aux_cycle_ends_after_raw_pulse_right_valid, aux_cycle_ends_before_next_input_left_valid, aux_cycle_ends_before_next_input_right_valid, learned_gain_below_all_caps_left_valid, learned_gain_below_all_caps_right_valid, mark_finishes_before_any_main_firing_left_valid, mark_finishes_before_any_main_firing_right_valid, main_fires_before_error_begins_left_valid, main_fires_before_error_begins_right_valid, error_finishes_during_main_fast_left_valid, error_finishes_during_main_fast_right_valid, main_reopens_before_next_input_left_valid, main_reopens_before_next_input_right_valid, gain_before_0_valid, peak_bound_0_valid, carry_bound_0_valid, silent_0_positive_derivative_coefficient_left_valid, silent_0_positive_derivative_coefficient_right_valid, silent_0_frozen_flow_increases_left_valid, silent_0_frozen_flow_increases_right_valid, silent_0_no_first_crossing_even_with_overlap_left_valid, silent_0_no_first_crossing_even_with_overlap_right_valid, silent_0_charge_returns_to_section_left_valid, silent_0_charge_returns_to_section_right_valid, gain_before_1_valid, peak_bound_1_valid, carry_bound_1_valid, silent_1_positive_derivative_coefficient_left_valid, silent_1_positive_derivative_coefficient_right_valid, silent_1_frozen_flow_increases_left_valid, silent_1_frozen_flow_increases_right_valid, silent_1_no_first_crossing_even_with_overlap_left_valid, silent_1_no_first_crossing_even_with_overlap_right_valid, silent_1_charge_returns_to_section_left_valid, silent_1_charge_returns_to_section_right_valid, gain_before_2_valid, peak_bound_2_valid, carry_bound_2_valid, silent_2_positive_derivative_coefficient_left_valid, silent_2_positive_derivative_coefficient_right_valid, silent_2_frozen_flow_increases_left_valid, silent_2_frozen_flow_increases_right_valid, silent_2_no_first_crossing_even_with_overlap_left_valid, silent_2_no_first_crossing_even_with_overlap_right_valid, silent_2_charge_returns_to_section_left_valid, silent_2_charge_returns_to_section_right_valid, learned_ready_early_valid, learned_ready_late_valid, learned_positive_derivative_coefficient_left_valid, learned_positive_derivative_coefficient_right_valid, learned_flow_strictly_increases_left_valid, learned_flow_strictly_increases_right_valid, learned_early_below_threshold_left_valid, learned_early_below_threshold_right_valid, learned_late_above_threshold_left_valid, learned_late_above_threshold_right_valid, work_bound_valid, reserve_gate_stays_open_left_valid, reserve_gate_stays_open_right_valid, B_first_emission_valid, A_first_arrival_valid, A_gain_complete_by_valid, A_first_emission_valid, A_last_emission_valid, A_last_return_by_valid, B_last_return_by_valid, A_learning_complete_before_first_response_left_valid, A_learning_complete_before_first_response_right_valid, A_quiescent_before_measurement_left_valid, A_quiescent_before_measurement_right_valid, B_quiescent_before_measurement_left_valid, B_quiescent_before_measurement_right_valid⟩

end KernelR.Certificates.Local010
#print axioms KernelR.Certificates.Local010.obligations_verified
#print axioms KernelR.Certificates.Local010.all_bounds_valid
