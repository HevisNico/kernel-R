import KernelR.Intervals

/-! Generated exact endpoint checks. Analytic enclosure soundness is NOT asserted. -/
namespace KernelR.Certificates.Entry010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def epsilon : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem epsilon_valid : epsilon.Valid := by norm_num [RationalBox.Valid, epsilon]

def a : RationalBox := ⟨(1386294361119890618834464242916353136151 / 1000000000000000000000000000000000000000 : ℚ), (13862943611198906188344642429163531361511 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem a_valid : a.Valid := by norm_num [RationalBox.Valid, a]

def kappa : RationalBox := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem kappa_valid : kappa.Valid := by norm_num [RationalBox.Valid, kappa]

def C : RationalBox := ⟨(18 / 5 : ℚ), (22 / 5 : ℚ)⟩
theorem C_valid : C.Valid := by norm_num [RationalBox.Valid, C]

def Lm : RationalBox := ⟨(10041459809139439009483279063942552651857 / 1000000000000000000000000000000000000000 : ℚ), (122728953222815365671462299670408976856031 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Lm_valid : Lm.Valid := by norm_num [RationalBox.Valid, Lm]

def Ls : RationalBox := ⟨(17655635731243889956854025735255440884941 / 10000000000000000000000000000000000000000 : ℚ), (5394777584546744153483174530216940270399 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem Ls_valid : Ls.Valid := by norm_num [RationalBox.Valid, Ls]

def Le : RationalBox := ⟨(4158883083359671856503392728749059408453 / 500000000000000000000000000000000000000 : ℚ), (101661586482125312047860711147199229984407 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Le_valid : Le.Valid := by norm_num [RationalBox.Valid, Le]

def M : RationalBox := ⟨(12900544781726378166238323015172510050413 / 400000000000000000000000000000000000000 : ℚ), (394183312774972666190615425463604473762621 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem M_valid : M.Valid := by norm_num [RationalBox.Valid, M]

def birth_b : RationalBox := ⟨(7999 / 100000 : ℚ), (8001 / 100000 : ℚ)⟩
theorem birth_b_valid : birth_b.Valid := by norm_num [RationalBox.Valid, birth_b]

def mark_dose : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem mark_dose_valid : mark_dose.Valid := by norm_num [RationalBox.Valid, mark_dose]

def entry_b : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem entry_b_valid : entry_b.Valid := by norm_num [RationalBox.Valid, entry_b]

def gain_dose : RationalBox := ⟨(3 / 5 : ℚ), (3 / 5 : ℚ)⟩
theorem gain_dose_valid : gain_dose.Valid := by norm_num [RationalBox.Valid, gain_dose]

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

def overlap : RationalBox := ⟨(0 / 1 : ℚ), (15909090909090909090909090909090909091 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem overlap_valid : overlap.Valid := by norm_num [RationalBox.Valid, overlap]

def density : RationalBox := ⟨(3481056809084084213160803442899595862423 / 10000000000000000000000000000000000000000 : ℚ), (435132101135510526645100430362449482803 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem density_valid : density.Valid := by norm_num [RationalBox.Valid, density]

def A_trained_gain : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_trained_gain_valid : A_trained_gain.Valid := by norm_num [RationalBox.Valid, A_trained_gain]

def B_trained_port1_gain : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_trained_port1_gain_valid : B_trained_port1_gain.Valid := by norm_num [RationalBox.Valid, B_trained_port1_gain]

def min_input_gap : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem min_input_gap_valid : min_input_gap.Valid := by norm_num [RationalBox.Valid, min_input_gap]

def max_input_gap : RationalBox := ⟨(17 / 2 : ℚ), (17 / 2 : ℚ)⟩
theorem max_input_gap_valid : max_input_gap.Valid := by norm_num [RationalBox.Valid, max_input_gap]

def stable_return_bound : RationalBox := ⟨(8737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (69907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem stable_return_bound_valid : stable_return_bound.Valid := by norm_num [RationalBox.Valid, stable_return_bound]

def low_earliest_return : RationalBox := ⟨(127522026230990509334274117206350590107499 / 10000000000000000000000000000000000000000 : ℚ), (127550660316808984270974773317666092192787 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem low_earliest_return_valid : low_earliest_return.Valid := by norm_num [RationalBox.Valid, low_earliest_return]

def stable_earliest_return : RationalBox := ⟨(7987776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (63907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem stable_earliest_return_valid : stable_earliest_return.Valid := by norm_num [RationalBox.Valid, stable_earliest_return]

def slow_before_protected_input_upper : RationalBox := ⟨(72009 / 125000 : ℚ), (72009 / 125000 : ℚ)⟩
theorem slow_before_protected_input_upper_valid : slow_before_protected_input_upper.Valid := by norm_num [RationalBox.Valid, slow_before_protected_input_upper]

def slow_through_error_upper : RationalBox := ⟨(4137429833333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (8274859666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem slow_through_error_upper_valid : slow_through_error_upper.Valid := by norm_num [RationalBox.Valid, slow_through_error_upper]

def slow_at_return_lower : RationalBox := ⟨(4892572611111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (9785145222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem slow_at_return_lower_valid : slow_at_return_lower.Valid := by norm_num [RationalBox.Valid, slow_at_return_lower]

def protected_pulse_reopen_by : RationalBox := ⟨(3 / 1 : ℚ), (3 / 1 : ℚ)⟩
theorem protected_pulse_reopen_by_valid : protected_pulse_reopen_by.Valid := by norm_num [RationalBox.Valid, protected_pulse_reopen_by]

def slow_return_target : RationalBox := ⟨(9162907318741550651835272117680110714501 / 10000000000000000000000000000000000000000 : ℚ), (4581453659370775325917636058840055357251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem slow_return_target_valid : slow_return_target.Valid := by norm_num [RationalBox.Valid, slow_return_target]

def birth_aux_below_threshold_left : RationalBox := ⟨(2499 / 100000 : ℚ), (2501 / 100000 : ℚ)⟩
theorem birth_aux_below_threshold_left_valid : birth_aux_below_threshold_left.Valid := by norm_num [RationalBox.Valid, birth_aux_below_threshold_left]

def birth_aux_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem birth_aux_below_threshold_right_valid : birth_aux_below_threshold_right.Valid := by norm_num [RationalBox.Valid, birth_aux_below_threshold_right]

def aux_root_early_left : RationalBox := ⟨(857777700395999170890784025356980226903 / 1250000000000000000000000000000000000000 : ℚ), (4165912371719864739736113183069689690047 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_early_left_valid : aux_root_early_left.Valid := by norm_num [RationalBox.Valid, aux_root_early_left]

def aux_root_early_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_root_early_right_valid : aux_root_early_right.Valid := by norm_num [RationalBox.Valid, aux_root_early_right]

def aux_root_late_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_root_late_left_valid : aux_root_late_left.Valid := by norm_num [RationalBox.Valid, aux_root_late_left]

def aux_root_late_right : RationalBox := ⟨(13289056706323197692444281225825371354033 / 10000000000000000000000000000000000000000 : ℚ), (8093421888524132263456113558930151776937 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_late_right_valid : aux_root_late_right.Valid := by norm_num [RationalBox.Valid, aux_root_late_right]

def aux_first_crossing_strict_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem aux_first_crossing_strict_left_valid : aux_first_crossing_strict_left.Valid := by norm_num [RationalBox.Valid, aux_first_crossing_strict_left]

def aux_first_crossing_strict_right : RationalBox := ⟨(104652753909468400451498982066330214586733 / 2500000000000000000000000000000000000000 : ℚ), (68880481100858260141341200869705380694399 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem aux_first_crossing_strict_right_valid : aux_first_crossing_strict_right.Valid := by norm_num [RationalBox.Valid, aux_first_crossing_strict_right]

def aux_finish_after_raw_end_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_finish_after_raw_end_left_valid : aux_finish_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, aux_finish_after_raw_end_left]

def aux_finish_after_raw_end_right : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (5665909090909090909090909090909090909091 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_after_raw_end_right_valid : aux_finish_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, aux_finish_after_raw_end_right]

def aux_finish_before_next_input_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_before_next_input_left_valid : aux_finish_before_next_input_left.Valid := by norm_num [RationalBox.Valid, aux_finish_before_next_input_left]

def aux_finish_before_next_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem aux_finish_before_next_input_right_valid : aux_finish_before_next_input_right.Valid := by norm_num [RationalBox.Valid, aux_finish_before_next_input_right]

def raw_pulses_do_not_overlap_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem raw_pulses_do_not_overlap_left_valid : raw_pulses_do_not_overlap_left.Valid := by norm_num [RationalBox.Valid, raw_pulses_do_not_overlap_left]

def raw_pulses_do_not_overlap_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem raw_pulses_do_not_overlap_right_valid : raw_pulses_do_not_overlap_right.Valid := by norm_num [RationalBox.Valid, raw_pulses_do_not_overlap_right]

def A_weak_gain_0 : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_gain_0_valid : A_weak_gain_0.Valid := by norm_num [RationalBox.Valid, A_weak_gain_0]

def A_weak_peak_0 : RationalBox := ⟨(1336460667207075197453577978254452619791 / 5000000000000000000000000000000000000000 : ℚ), (571541286239082536331111206235332567449 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_peak_0_valid : A_weak_peak_0.Valid := by norm_num [RationalBox.Valid, A_weak_peak_0]

def A_weak_carry_0 : RationalBox := ⟨(32433099753347992891436735613419756851 / 5000000000000000000000000000000000000000 : ℚ), (36015547626748757751303033613172161549 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_carry_0_valid : A_weak_carry_0.Valid := by norm_num [RationalBox.Valid, A_weak_carry_0]

def A_weak_0_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_weak_0_positive_coefficient_left_valid : A_weak_0_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_weak_0_positive_coefficient_left]

def A_weak_0_positive_coefficient_right : RationalBox := ⟨(234614652182025324597025620160078202879 / 1000000000000000000000000000000000000000 : ℚ), (624060861554983020919224180575194350001 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_0_positive_coefficient_right_valid : A_weak_0_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_weak_0_positive_coefficient_right]

def A_weak_0_increasing_fixed_flow_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_weak_0_increasing_fixed_flow_left_valid : A_weak_0_increasing_fixed_flow_left.Valid := by norm_num [RationalBox.Valid, A_weak_0_increasing_fixed_flow_left]

def A_weak_0_increasing_fixed_flow_right : RationalBox := ⟨(14026414987518220352294549090553045151 / 312500000000000000000000000000000000000 : ℚ), (813128927969828348431183394546152387073 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_0_increasing_fixed_flow_right_valid : A_weak_0_increasing_fixed_flow_right.Valid := by norm_num [RationalBox.Valid, A_weak_0_increasing_fixed_flow_right]

def A_weak_0_never_fires_left : RationalBox := ⟨(1336460667207075197453577978254452619791 / 5000000000000000000000000000000000000000 : ℚ), (571541286239082536331111206235332567449 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_0_never_fires_left_valid : A_weak_0_never_fires_left.Valid := by norm_num [RationalBox.Valid, A_weak_0_never_fires_left]

def A_weak_0_never_fires_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_weak_0_never_fires_right_valid : A_weak_0_never_fires_right.Valid := by norm_num [RationalBox.Valid, A_weak_0_never_fires_right]

def A_weak_0_charge_section_invariant_left : RationalBox := ⟨(32433099753347992891436735613419756851 / 5000000000000000000000000000000000000000 : ℚ), (36015547626748757751303033613172161549 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_0_charge_section_invariant_left_valid : A_weak_0_charge_section_invariant_left.Valid := by norm_num [RationalBox.Valid, A_weak_0_charge_section_invariant_left]

def A_weak_0_charge_section_invariant_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem A_weak_0_charge_section_invariant_right_valid : A_weak_0_charge_section_invariant_right.Valid := by norm_num [RationalBox.Valid, A_weak_0_charge_section_invariant_right]

def A_weak_gain_1 : RationalBox := ⟨(1093260347576166423671662107676113018829 / 2000000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_gain_1_valid : A_weak_gain_1.Valid := by norm_num [RationalBox.Valid, A_weak_gain_1]

def A_weak_peak_1 : RationalBox := ⟨(809662255807247503471415184607783861073 / 2000000000000000000000000000000000000000 : ℚ), (4235369736378614694706129628037248725067 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_peak_1_valid : A_weak_peak_1.Valid := by norm_num [RationalBox.Valid, A_weak_peak_1]

def A_weak_carry_1 : RationalBox := ⟨(118195855069133417760095177713621038169 / 10000000000000000000000000000000000000000 : ℚ), (125448898570808056413847959108212418361 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_carry_1_valid : A_weak_carry_1.Valid := by norm_num [RationalBox.Valid, A_weak_carry_1]

def A_weak_1_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_weak_1_positive_coefficient_left_valid : A_weak_1_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_weak_1_positive_coefficient_left]

def A_weak_1_positive_coefficient_right : RationalBox := ⟨(1068749697954876114708902087903751941771 / 2500000000000000000000000000000000000000 : ℚ), (4425134293650356307382242154168918002043 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_1_positive_coefficient_right_valid : A_weak_1_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_weak_1_positive_coefficient_right]

def A_weak_1_increasing_fixed_flow_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_weak_1_increasing_fixed_flow_left_valid : A_weak_1_increasing_fixed_flow_left.Valid := by norm_num [RationalBox.Valid, A_weak_1_increasing_fixed_flow_left]

def A_weak_1_increasing_fixed_flow_right : RationalBox := ⟨(558516788722282749712944555478656629023 / 5000000000000000000000000000000000000000 : ℚ), (740758889371765803856086266343378159407 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_1_increasing_fixed_flow_right_valid : A_weak_1_increasing_fixed_flow_right.Valid := by norm_num [RationalBox.Valid, A_weak_1_increasing_fixed_flow_right]

def A_weak_1_never_fires_left : RationalBox := ⟨(809662255807247503471415184607783861073 / 2000000000000000000000000000000000000000 : ℚ), (4235369736378614694706129628037248725067 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_1_never_fires_left_valid : A_weak_1_never_fires_left.Valid := by norm_num [RationalBox.Valid, A_weak_1_never_fires_left]

def A_weak_1_never_fires_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_weak_1_never_fires_right_valid : A_weak_1_never_fires_right.Valid := by norm_num [RationalBox.Valid, A_weak_1_never_fires_right]

def A_weak_1_charge_section_invariant_left : RationalBox := ⟨(118195855069133417760095177713621038169 / 10000000000000000000000000000000000000000 : ℚ), (125448898570808056413847959108212418361 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_1_charge_section_invariant_left_valid : A_weak_1_charge_section_invariant_left.Valid := by norm_num [RationalBox.Valid, A_weak_1_charge_section_invariant_left]

def A_weak_1_charge_section_invariant_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem A_weak_1_charge_section_invariant_right_valid : A_weak_1_charge_section_invariant_right.Valid := by norm_num [RationalBox.Valid, A_weak_1_charge_section_invariant_right]

def A_weak_gain_2 : RationalBox := ⟨(9960251165199976250523787258791057471269 / 10000000000000000000000000000000000000000 : ℚ), (9960450372215343763490081857984907714419 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_gain_2_valid : A_weak_gain_2.Valid := by norm_num [RationalBox.Valid, A_weak_gain_2]

def A_weak_peak_2 : RationalBox := ⟨(6554435155000203475739237101113647071117 / 10000000000000000000000000000000000000000 : ℚ), (6745635945361054411913928144783421678443 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_peak_2_valid : A_weak_peak_2.Valid := by norm_num [RationalBox.Valid, A_weak_peak_2]

def A_weak_carry_2 : RationalBox := ⟨(420642232593361221706359202354505541 / 19531250000000000000000000000000000000 : ℚ), (111391241135421045029963947676311203449 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_carry_2_valid : A_weak_carry_2.Valid := by norm_num [RationalBox.Valid, A_weak_carry_2]

def A_weak_2_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_weak_2_positive_coefficient_left_valid : A_weak_2_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_weak_2_positive_coefficient_left]

def A_weak_2_positive_coefficient_right : RationalBox := ⟨(7789596776161050202363801858500545502817 / 10000000000000000000000000000000000000000 : ℚ), (3969901285327256582423845954654879575583 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_2_positive_coefficient_right_valid : A_weak_2_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_weak_2_positive_coefficient_right]

def A_weak_2_increasing_fixed_flow_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_weak_2_increasing_fixed_flow_left_valid : A_weak_2_increasing_fixed_flow_left.Valid := by norm_num [RationalBox.Valid, A_weak_2_increasing_fixed_flow_left]

def A_weak_2_increasing_fixed_flow_right : RationalBox := ⟨(2334552037147018912289288623693919590131 / 10000000000000000000000000000000000000000 : ℚ), (2699401669709702707003101279578656274967 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_2_increasing_fixed_flow_right_valid : A_weak_2_increasing_fixed_flow_right.Valid := by norm_num [RationalBox.Valid, A_weak_2_increasing_fixed_flow_right]

def A_weak_2_never_fires_left : RationalBox := ⟨(6554435155000203475739237101113647071117 / 10000000000000000000000000000000000000000 : ℚ), (6745635945361054411913928144783421678443 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_2_never_fires_left_valid : A_weak_2_never_fires_left.Valid := by norm_num [RationalBox.Valid, A_weak_2_never_fires_left]

def A_weak_2_never_fires_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_weak_2_never_fires_right_valid : A_weak_2_never_fires_right.Valid := by norm_num [RationalBox.Valid, A_weak_2_never_fires_right]

def A_weak_2_charge_section_invariant_left : RationalBox := ⟨(420642232593361221706359202354505541 / 19531250000000000000000000000000000000 : ℚ), (111391241135421045029963947676311203449 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_weak_2_charge_section_invariant_left_valid : A_weak_2_charge_section_invariant_left.Valid := by norm_num [RationalBox.Valid, A_weak_2_charge_section_invariant_left]

def A_weak_2_charge_section_invariant_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem A_weak_2_charge_section_invariant_right_valid : A_weak_2_charge_section_invariant_right.Valid := by norm_num [RationalBox.Valid, A_weak_2_charge_section_invariant_right]

def A_gain_cap_not_reached_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_gain_cap_not_reached_left_valid : A_gain_cap_not_reached_left.Valid := by norm_num [RationalBox.Valid, A_gain_cap_not_reached_left]

def A_gain_cap_not_reached_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem A_gain_cap_not_reached_right_valid : A_gain_cap_not_reached_right.Valid := by norm_num [RationalBox.Valid, A_gain_cap_not_reached_right]

def A_strong_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_strong_positive_coefficient_left_valid : A_strong_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_strong_positive_coefficient_left]

def A_strong_positive_coefficient_right : RationalBox := ⟨(7096805919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2868789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_strong_positive_coefficient_right_valid : A_strong_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_strong_positive_coefficient_right]

def A_strong_increasing_flow_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_strong_increasing_flow_left_valid : A_strong_increasing_flow_left.Valid := by norm_num [RationalBox.Valid, A_strong_increasing_flow_left]

def A_strong_increasing_flow_right : RationalBox := ⟨(4553015312393353567582092430317193151263 / 10000000000000000000000000000000000000000 : ℚ), (2459265402065953910408096372585777497291 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_strong_increasing_flow_right_valid : A_strong_increasing_flow_right.Valid := by norm_num [RationalBox.Valid, A_strong_increasing_flow_right]

def A_strong_early_below_threshold_left : RationalBox := ⟨(1340892153783846829929798808811137650807 / 2000000000000000000000000000000000000000 : ℚ), (6962873324722105309175394422442102909289 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_strong_early_below_threshold_left_valid : A_strong_early_below_threshold_left.Valid := by norm_num [RationalBox.Valid, A_strong_early_below_threshold_left]

def A_strong_early_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_strong_early_below_threshold_right_valid : A_strong_early_below_threshold_right.Valid := by norm_num [RationalBox.Valid, A_strong_early_below_threshold_right]

def A_strong_late_above_threshold_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_strong_late_above_threshold_left_valid : A_strong_late_above_threshold_left.Valid := by norm_num [RationalBox.Valid, A_strong_late_above_threshold_left]

def A_strong_late_above_threshold_right : RationalBox := ⟨(10948374960726511098322810098010980394129 / 10000000000000000000000000000000000000000 : ℚ), (11139926139792377106420383113815579433053 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_strong_late_above_threshold_right_valid : A_strong_late_above_threshold_right.Valid := by norm_num [RationalBox.Valid, A_strong_late_above_threshold_right]

def B_weak_gain_0 : RationalBox := ⟨(5999940000299999000002499995000008333321 / 5000000000000000000000000000000000000000 : ℚ), (12000120000600002000005000010000016666691 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_weak_gain_0_valid : B_weak_gain_0.Valid := by norm_num [RationalBox.Valid, B_weak_gain_0]

def B_weak_peak_0 : RationalBox := ⟨(7691867296854515369655704965896118312467 / 10000000000000000000000000000000000000000 : ℚ), (98561851638003508067235056790182361761 / 125000000000000000000000000000000000000 : ℚ)⟩
theorem B_weak_peak_0_valid : B_weak_peak_0.Valid := by norm_num [RationalBox.Valid, B_weak_peak_0]

def B_weak_carry_0 : RationalBox := ⟨(25947185335054074586396473026288818469 / 1000000000000000000000000000000000000000 : ℚ), (66739602435895466149472050578746911717 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem B_weak_carry_0_valid : B_weak_carry_0.Valid := by norm_num [RationalBox.Valid, B_weak_carry_0]

def B_weak_0_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_weak_0_positive_coefficient_left_valid : B_weak_0_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_weak_0_positive_coefficient_left]

def B_weak_0_positive_coefficient_right : RationalBox := ⟨(234618402182025324597025620160078202879 / 250000000000000000000000000000000000000 : ℚ), (4767486892439864167353793444601554800007 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_weak_0_positive_coefficient_right_valid : B_weak_0_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_weak_0_positive_coefficient_right]

def B_weak_0_increasing_fixed_flow_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_weak_0_increasing_fixed_flow_left_valid : B_weak_0_increasing_fixed_flow_left.Valid := by norm_num [RationalBox.Valid, B_weak_0_increasing_fixed_flow_left]

def B_weak_0_increasing_fixed_flow_right : RationalBox := ⟨(721784076471268091895135361643728648881 / 2500000000000000000000000000000000000000 : ℚ), (1626075896741742906835285649231807420009 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_weak_0_increasing_fixed_flow_right_valid : B_weak_0_increasing_fixed_flow_right.Valid := by norm_num [RationalBox.Valid, B_weak_0_increasing_fixed_flow_right]

def B_weak_0_never_fires_left : RationalBox := ⟨(7691867296854515369655704965896118312467 / 10000000000000000000000000000000000000000 : ℚ), (98561851638003508067235056790182361761 / 125000000000000000000000000000000000000 : ℚ)⟩
theorem B_weak_0_never_fires_left_valid : B_weak_0_never_fires_left.Valid := by norm_num [RationalBox.Valid, B_weak_0_never_fires_left]

def B_weak_0_never_fires_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_weak_0_never_fires_right_valid : B_weak_0_never_fires_right.Valid := by norm_num [RationalBox.Valid, B_weak_0_never_fires_right]

def B_weak_0_charge_section_invariant_left : RationalBox := ⟨(25947185335054074586396473026288818469 / 1000000000000000000000000000000000000000 : ℚ), (66739602435895466149472050578746911717 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem B_weak_0_charge_section_invariant_left_valid : B_weak_0_charge_section_invariant_left.Valid := by norm_num [RationalBox.Valid, B_weak_0_charge_section_invariant_left]

def B_weak_0_charge_section_invariant_right : RationalBox := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem B_weak_0_charge_section_invariant_right_valid : B_weak_0_charge_section_invariant_right.Valid := by norm_num [RationalBox.Valid, B_weak_0_charge_section_invariant_right]

def B_gain_cap_not_reached_left : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_gain_cap_not_reached_left_valid : B_gain_cap_not_reached_left.Valid := by norm_num [RationalBox.Valid, B_gain_cap_not_reached_left]

def B_gain_cap_not_reached_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_gain_cap_not_reached_right_valid : B_gain_cap_not_reached_right.Valid := by norm_num [RationalBox.Valid, B_gain_cap_not_reached_right]

def B_strong_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_strong_positive_coefficient_left_valid : B_strong_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_strong_positive_coefficient_left]

def B_strong_positive_coefficient_right : RationalBox := ⟨(17100145167278017835342433406460031068337 / 10000000000000000000000000000000000000000 : ℚ), (1725053717460142522952896861667567200817 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem B_strong_positive_coefficient_right_valid : B_strong_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_strong_positive_coefficient_right]

def B_strong_increasing_flow_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_strong_increasing_flow_left_valid : B_strong_increasing_flow_left.Valid := by norm_num [RationalBox.Valid, B_strong_increasing_flow_left]

def B_strong_increasing_flow_right : RationalBox := ⟨(2779944748630501080095197803406688924191 / 5000000000000000000000000000000000000000 : ℚ), (740713399572287356349315981378253820873 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_strong_increasing_flow_right_valid : B_strong_increasing_flow_right.Valid := by norm_num [RationalBox.Valid, B_strong_increasing_flow_right]

def B_strong_early_below_threshold_left : RationalBox := ⟨(314904795520857134203281222067559478891 / 400000000000000000000000000000000000000 : ℚ), (8131055807240314939866258326762797146503 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_strong_early_below_threshold_left_valid : B_strong_early_below_threshold_left.Valid := by norm_num [RationalBox.Valid, B_strong_early_below_threshold_left]

def B_strong_early_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_strong_early_below_threshold_right_valid : B_strong_early_below_threshold_right.Valid := by norm_num [RationalBox.Valid, B_strong_early_below_threshold_right]

def B_strong_late_above_threshold_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_strong_late_above_threshold_left_valid : B_strong_late_above_threshold_left.Valid := by norm_num [RationalBox.Valid, B_strong_late_above_threshold_left]

def B_strong_late_above_threshold_right : RationalBox := ⟨(6492792440780355051012595309719542478751 / 5000000000000000000000000000000000000000 : ℚ), (1317717680523243749456315338299126723409 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem B_strong_late_above_threshold_right_valid : B_strong_late_above_threshold_right.Valid := by norm_num [RationalBox.Valid, B_strong_late_above_threshold_right]

def A_output_lower_latency_for_delivery_hulls_left : RationalBox := ⟨(8914330190785786031236358272500993673019 / 10000000000000000000000000000000000000000 : ℚ), (9148206595529824080829844384603189791057 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_output_lower_latency_for_delivery_hulls_left_valid : A_output_lower_latency_for_delivery_hulls_left.Valid := by norm_num [RationalBox.Valid, A_output_lower_latency_for_delivery_hulls_left]

def A_output_lower_latency_for_delivery_hulls_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_output_lower_latency_for_delivery_hulls_right_valid : A_output_lower_latency_for_delivery_hulls_right.Valid := by norm_num [RationalBox.Valid, A_output_lower_latency_for_delivery_hulls_right]

def mark_complete_before_first_main_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem mark_complete_before_first_main_fire_left_valid : mark_complete_before_first_main_fire_left.Valid := by norm_num [RationalBox.Valid, mark_complete_before_first_main_fire_left]

def mark_complete_before_first_main_fire_right : RationalBox := ⟨(3 / 10 : ℚ), (3 / 10 : ℚ)⟩
theorem mark_complete_before_first_main_fire_right_valid : mark_complete_before_first_main_fire_right.Valid := by norm_num [RationalBox.Valid, mark_complete_before_first_main_fire_right]

def main_fire_before_error_start_left : RationalBox := ⟨(9 / 10 : ℚ), (9 / 10 : ℚ)⟩
theorem main_fire_before_error_start_left_valid : main_fire_before_error_start_left.Valid := by norm_num [RationalBox.Valid, main_fire_before_error_start_left]

def main_fire_before_error_start_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem main_fire_before_error_start_right_valid : main_fire_before_error_start_right.Valid := by norm_num [RationalBox.Valid, main_fire_before_error_start_right]

def initial_error_entirely_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem initial_error_entirely_protected_left_valid : initial_error_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, initial_error_entirely_protected_left]

def initial_error_entirely_protected_right : RationalBox := ⟨(127522026230990509334274117206350590107499 / 10000000000000000000000000000000000000000 : ℚ), (51008810492396203733709646882540236043 / 4000000000000000000000000000000000000 : ℚ)⟩
theorem initial_error_entirely_protected_right_valid : initial_error_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, initial_error_entirely_protected_right]

def stable_error_entirely_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem stable_error_entirely_protected_left_valid : stable_error_entirely_protected_left.Valid := by norm_num [RationalBox.Valid, stable_error_entirely_protected_left]

def stable_error_entirely_protected_right : RationalBox := ⟨(7987776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (63902212758966449929644309303261544994729 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem stable_error_entirely_protected_right_valid : stable_error_entirely_protected_right.Valid := by norm_num [RationalBox.Valid, stable_error_entirely_protected_right]

def next_input_is_after_fast_left : RationalBox := ⟨(19 / 10 : ℚ), (19 / 10 : ℚ)⟩
theorem next_input_is_after_fast_left_valid : next_input_is_after_fast_left.Valid := by norm_num [RationalBox.Valid, next_input_is_after_fast_left]

def next_input_is_after_fast_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem next_input_is_after_fast_right_valid : next_input_is_after_fast_right.Valid := by norm_num [RationalBox.Valid, next_input_is_after_fast_right]

def low_b_has_not_reopened_at_next_input_left : RationalBox := ⟨(72009 / 125000 : ℚ), (72009 / 125000 : ℚ)⟩
theorem low_b_has_not_reopened_at_next_input_left_valid : low_b_has_not_reopened_at_next_input_left.Valid := by norm_num [RationalBox.Valid, low_b_has_not_reopened_at_next_input_left]

def low_b_has_not_reopened_at_next_input_right : RationalBox := ⟨(9162907318741550651835272117680110714501 / 10000000000000000000000000000000000000000 : ℚ), (4581453659370775325917636058840055357251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem low_b_has_not_reopened_at_next_input_right_valid : low_b_has_not_reopened_at_next_input_right.Valid := by norm_num [RationalBox.Valid, low_b_has_not_reopened_at_next_input_right]

def whole_mark_and_error_of_protected_input_stay_protected_left : RationalBox := ⟨(4137429833333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (8274859666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem whole_mark_and_error_of_protected_input_stay_protected_left_valid : whole_mark_and_error_of_protected_input_stay_protected_left.Valid := by norm_num [RationalBox.Valid, whole_mark_and_error_of_protected_input_stay_protected_left]

def whole_mark_and_error_of_protected_input_stay_protected_right : RationalBox := ⟨(9162907318741550651835272117680110714501 / 10000000000000000000000000000000000000000 : ℚ), (4581453659370775325917636058840055357251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem whole_mark_and_error_of_protected_input_stay_protected_right_valid : whole_mark_and_error_of_protected_input_stay_protected_right.Valid := by norm_num [RationalBox.Valid, whole_mark_and_error_of_protected_input_stay_protected_right]

def protected_input_reopens_before_three_time_units_left : RationalBox := ⟨(9162907318741550651835272117680110714501 / 10000000000000000000000000000000000000000 : ℚ), (4581453659370775325917636058840055357251 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_input_reopens_before_three_time_units_left_valid : protected_input_reopens_before_three_time_units_left.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_before_three_time_units_left]

def protected_input_reopens_before_three_time_units_right : RationalBox := ⟨(4892572611111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (9785145222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_input_reopens_before_three_time_units_right_valid : protected_input_reopens_before_three_time_units_right.Valid := by norm_num [RationalBox.Valid, protected_input_reopens_before_three_time_units_right]

def protected_input_cycle_ends_before_reopening_deadline_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem protected_input_cycle_ends_before_reopening_deadline_left_valid : protected_input_cycle_ends_before_reopening_deadline_left.Valid := by norm_num [RationalBox.Valid, protected_input_cycle_ends_before_reopening_deadline_left]

def protected_input_cycle_ends_before_reopening_deadline_right : RationalBox := ⟨(3 / 1 : ℚ), (3 / 1 : ℚ)⟩
theorem protected_input_cycle_ends_before_reopening_deadline_right_valid : protected_input_cycle_ends_before_reopening_deadline_right.Valid := by norm_num [RationalBox.Valid, protected_input_cycle_ends_before_reopening_deadline_right]

def protected_input_return_before_following_input_left : RationalBox := ⟨(3 / 1 : ℚ), (3 / 1 : ℚ)⟩
theorem protected_input_return_before_following_input_left_valid : protected_input_return_before_following_input_left.Valid := by norm_num [RationalBox.Valid, protected_input_return_before_following_input_left]

def protected_input_return_before_following_input_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem protected_input_return_before_following_input_right_valid : protected_input_return_before_following_input_right.Valid := by norm_num [RationalBox.Valid, protected_input_return_before_following_input_right]

def all_later_inputs_follow_stable_return_left : RationalBox := ⟨(8737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (69907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem all_later_inputs_follow_stable_return_left_valid : all_later_inputs_follow_stable_return_left.Valid := by norm_num [RationalBox.Valid, all_later_inputs_follow_stable_return_left]

def all_later_inputs_follow_stable_return_right : RationalBox := ⟨(15 / 2 : ℚ), (15 / 2 : ℚ)⟩
theorem all_later_inputs_follow_stable_return_right_valid : all_later_inputs_follow_stable_return_right.Valid := by norm_num [RationalBox.Valid, all_later_inputs_follow_stable_return_right]

def recovery_cap_not_reached_left : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem recovery_cap_not_reached_left_valid : recovery_cap_not_reached_left.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_left]

def recovery_cap_not_reached_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem recovery_cap_not_reached_right_valid : recovery_cap_not_reached_right.Valid := by norm_num [RationalBox.Valid, recovery_cap_not_reached_right]

def work_bound : RationalBox := ⟨(10573936830325210453707713866907429323159 / 40000000000000000000000000000000000000 : ℚ), (2643484207581302613426928466726857330789751 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem work_bound_valid : work_bound.Valid := by norm_num [RationalBox.Valid, work_bound]

def energy_reserve_gate_open_left : RationalBox := ⟨(10573936830325210453707713866907429323159 / 40000000000000000000000000000000000000 : ℚ), (2643484207581302613426928466726857330789751 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem energy_reserve_gate_open_left_valid : energy_reserve_gate_open_left.Valid := by norm_num [RationalBox.Valid, energy_reserve_gate_open_left]

def energy_reserve_gate_open_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem energy_reserve_gate_open_right_valid : energy_reserve_gate_open_right.Valid := by norm_num [RationalBox.Valid, energy_reserve_gate_open_right]

def A_first_block_last_return : RationalBox := ⟨(158737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_first_block_last_return_valid : A_first_block_last_return.Valid := by norm_num [RationalBox.Valid, A_first_block_last_return]

def A_second_block_last_emission : RationalBox := ⟨(2809 / 10 : ℚ), (2809 / 10 : ℚ)⟩
theorem A_second_block_last_emission_valid : A_second_block_last_emission.Valid := by norm_num [RationalBox.Valid, A_second_block_last_emission]

def A_second_block_last_return : RationalBox := ⟨(358737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (2869907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_second_block_last_return_valid : A_second_block_last_return.Valid := by norm_num [RationalBox.Valid, A_second_block_last_return]

def B_first_possible_arrival : RationalBox := ⟨(804 / 5 : ℚ), (804 / 5 : ℚ)⟩
theorem B_first_possible_arrival_valid : B_first_possible_arrival.Valid := by norm_num [RationalBox.Valid, B_first_possible_arrival]

def B_last_possible_arrival : RationalBox := ⟨(2813 / 10 : ℚ), (2813 / 10 : ℚ)⟩
theorem B_last_possible_arrival_valid : B_last_possible_arrival.Valid := by norm_num [RationalBox.Valid, B_last_possible_arrival]

def B_last_possible_emission : RationalBox := ⟨(1411 / 5 : ℚ), (1411 / 5 : ℚ)⟩
theorem B_last_possible_emission_valid : B_last_possible_emission.Valid := by norm_num [RationalBox.Valid, B_last_possible_emission]

def B_last_return : RationalBox := ⟨(360362776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (2882907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_last_return_valid : B_last_return.Valid := by norm_num [RationalBox.Valid, B_last_return]

def A_quiescent_before_second_block_left : RationalBox := ⟨(158737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (1269907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_quiescent_before_second_block_left_valid : A_quiescent_before_second_block_left.Valid := by norm_num [RationalBox.Valid, A_quiescent_before_second_block_left]

def A_quiescent_before_second_block_right : RationalBox := ⟨(1599 / 10 : ℚ), (1599 / 10 : ℚ)⟩
theorem A_quiescent_before_second_block_right_valid : A_quiescent_before_second_block_right.Valid := by norm_num [RationalBox.Valid, A_quiescent_before_second_block_right]

def A_first_block_emissions_precede_B_birth_left : RationalBox := ⟨(1209 / 10 : ℚ), (1209 / 10 : ℚ)⟩
theorem A_first_block_emissions_precede_B_birth_left_valid : A_first_block_emissions_precede_B_birth_left.Valid := by norm_num [RationalBox.Valid, A_first_block_emissions_precede_B_birth_left]

def A_first_block_emissions_precede_B_birth_right : RationalBox := ⟨(160 / 1 : ℚ), (160 / 1 : ℚ)⟩
theorem A_first_block_emissions_precede_B_birth_right_valid : A_first_block_emissions_precede_B_birth_right.Valid := by norm_num [RationalBox.Valid, A_first_block_emissions_precede_B_birth_right]

def first_B_input_strictly_after_birth_left : RationalBox := ⟨(160 / 1 : ℚ), (160 / 1 : ℚ)⟩
theorem first_B_input_strictly_after_birth_left_valid : first_B_input_strictly_after_birth_left.Valid := by norm_num [RationalBox.Valid, first_B_input_strictly_after_birth_left]

def first_B_input_strictly_after_birth_right : RationalBox := ⟨(804 / 5 : ℚ), (804 / 5 : ℚ)⟩
theorem first_B_input_strictly_after_birth_right_valid : first_B_input_strictly_after_birth_right.Valid := by norm_num [RationalBox.Valid, first_B_input_strictly_after_birth_right]

def all_A_teaching_emissions_inside_gate_left : RationalBox := ⟨(2809 / 10 : ℚ), (2809 / 10 : ℚ)⟩
theorem all_A_teaching_emissions_inside_gate_left_valid : all_A_teaching_emissions_inside_gate_left.Valid := by norm_num [RationalBox.Valid, all_A_teaching_emissions_inside_gate_left]

def all_A_teaching_emissions_inside_gate_right : RationalBox := ⟨(310 / 1 : ℚ), (310 / 1 : ℚ)⟩
theorem all_A_teaching_emissions_inside_gate_right_valid : all_A_teaching_emissions_inside_gate_right.Valid := by norm_num [RationalBox.Valid, all_A_teaching_emissions_inside_gate_right]

def all_A_teaching_deliveries_before_gate_end_left : RationalBox := ⟨(2813 / 10 : ℚ), (2813 / 10 : ℚ)⟩
theorem all_A_teaching_deliveries_before_gate_end_left_valid : all_A_teaching_deliveries_before_gate_end_left.Valid := by norm_num [RationalBox.Valid, all_A_teaching_deliveries_before_gate_end_left]

def all_A_teaching_deliveries_before_gate_end_right : RationalBox := ⟨(310 / 1 : ℚ), (310 / 1 : ℚ)⟩
theorem all_A_teaching_deliveries_before_gate_end_right_valid : all_A_teaching_deliveries_before_gate_end_right.Valid := by norm_num [RationalBox.Valid, all_A_teaching_deliveries_before_gate_end_right]

def B_teaching_phase_emissions_precede_reverse_gate_left : RationalBox := ⟨(1411 / 5 : ℚ), (1411 / 5 : ℚ)⟩
theorem B_teaching_phase_emissions_precede_reverse_gate_left_valid : B_teaching_phase_emissions_precede_reverse_gate_left.Valid := by norm_num [RationalBox.Valid, B_teaching_phase_emissions_precede_reverse_gate_left]

def B_teaching_phase_emissions_precede_reverse_gate_right : RationalBox := ⟨(320 / 1 : ℚ), (320 / 1 : ℚ)⟩
theorem B_teaching_phase_emissions_precede_reverse_gate_right_valid : B_teaching_phase_emissions_precede_reverse_gate_right.Valid := by norm_num [RationalBox.Valid, B_teaching_phase_emissions_precede_reverse_gate_right]

def A_quiescent_at_prepared_cut_left : RationalBox := ⟨(358737776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (2869907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_quiescent_at_prepared_cut_left_valid : A_quiescent_at_prepared_cut_left.Valid := by norm_num [RationalBox.Valid, A_quiescent_at_prepared_cut_left]

def A_quiescent_at_prepared_cut_right : RationalBox := ⟨(3199 / 10 : ℚ), (3199 / 10 : ℚ)⟩
theorem A_quiescent_at_prepared_cut_right_valid : A_quiescent_at_prepared_cut_right.Valid := by norm_num [RationalBox.Valid, A_quiescent_at_prepared_cut_right]

def B_quiescent_at_prepared_cut_left : RationalBox := ⟨(360362776594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (2882907868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_quiescent_at_prepared_cut_left_valid : B_quiescent_at_prepared_cut_left.Valid := by norm_num [RationalBox.Valid, B_quiescent_at_prepared_cut_left]

def B_quiescent_at_prepared_cut_right : RationalBox := ⟨(3199 / 10 : ℚ), (3199 / 10 : ℚ)⟩
theorem B_quiescent_at_prepared_cut_right_valid : B_quiescent_at_prepared_cut_right.Valid := by norm_num [RationalBox.Valid, B_quiescent_at_prepared_cut_right]

def entry_b_contains_lower_endpoint_left : RationalBox := ⟨(17999 / 100000 : ℚ), (17999 / 100000 : ℚ)⟩
theorem entry_b_contains_lower_endpoint_left_valid : entry_b_contains_lower_endpoint_left.Valid := by norm_num [RationalBox.Valid, entry_b_contains_lower_endpoint_left]

def entry_b_contains_lower_endpoint_right : RationalBox := ⟨(17999 / 100000 : ℚ), (17999 / 100000 : ℚ)⟩
theorem entry_b_contains_lower_endpoint_right_valid : entry_b_contains_lower_endpoint_right.Valid := by norm_num [RationalBox.Valid, entry_b_contains_lower_endpoint_right]

def entry_b_contains_upper_endpoint_left : RationalBox := ⟨(18001 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem entry_b_contains_upper_endpoint_left_valid : entry_b_contains_upper_endpoint_left.Valid := by norm_num [RationalBox.Valid, entry_b_contains_upper_endpoint_left]

def entry_b_contains_upper_endpoint_right : RationalBox := ⟨(18001 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem entry_b_contains_upper_endpoint_right_valid : entry_b_contains_upper_endpoint_right.Valid := by norm_num [RationalBox.Valid, entry_b_contains_upper_endpoint_right]

def entry_rest_charge_above_section_lower_left : RationalBox := ⟨(9999 / 100000 : ℚ), (9999 / 100000 : ℚ)⟩
theorem entry_rest_charge_above_section_lower_left_valid : entry_rest_charge_above_section_lower_left.Valid := by norm_num [RationalBox.Valid, entry_rest_charge_above_section_lower_left]

def entry_rest_charge_above_section_lower_right : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem entry_rest_charge_above_section_lower_right_valid : entry_rest_charge_above_section_lower_right.Valid := by norm_num [RationalBox.Valid, entry_rest_charge_above_section_lower_right]

def entry_rest_charge_below_section_upper_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem entry_rest_charge_below_section_upper_left_valid : entry_rest_charge_below_section_upper_left.Valid := by norm_num [RationalBox.Valid, entry_rest_charge_below_section_upper_left]

def entry_rest_charge_below_section_upper_right : RationalBox := ⟨(10001 / 100000 : ℚ), (10001 / 100000 : ℚ)⟩
theorem entry_rest_charge_below_section_upper_right_valid : entry_rest_charge_below_section_upper_right.Valid := by norm_num [RationalBox.Valid, entry_rest_charge_below_section_upper_right]

theorem birth_aux_below_threshold_verified : RationalBox.StrictBefore birth_aux_below_threshold_left birth_aux_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, birth_aux_below_threshold_left, birth_aux_below_threshold_right]

theorem aux_root_early_verified : RationalBox.StrictBefore aux_root_early_left aux_root_early_right := by
  norm_num [RationalBox.StrictBefore, aux_root_early_left, aux_root_early_right]

theorem aux_root_late_verified : RationalBox.StrictBefore aux_root_late_left aux_root_late_right := by
  norm_num [RationalBox.StrictBefore, aux_root_late_left, aux_root_late_right]

theorem aux_first_crossing_strict_verified : RationalBox.StrictBefore aux_first_crossing_strict_left aux_first_crossing_strict_right := by
  norm_num [RationalBox.StrictBefore, aux_first_crossing_strict_left, aux_first_crossing_strict_right]

theorem aux_finish_after_raw_end_verified : RationalBox.StrictBefore aux_finish_after_raw_end_left aux_finish_after_raw_end_right := by
  norm_num [RationalBox.StrictBefore, aux_finish_after_raw_end_left, aux_finish_after_raw_end_right]

theorem aux_finish_before_next_input_verified : RationalBox.StrictBefore aux_finish_before_next_input_left aux_finish_before_next_input_right := by
  norm_num [RationalBox.StrictBefore, aux_finish_before_next_input_left, aux_finish_before_next_input_right]

theorem raw_pulses_do_not_overlap_verified : RationalBox.StrictBefore raw_pulses_do_not_overlap_left raw_pulses_do_not_overlap_right := by
  norm_num [RationalBox.StrictBefore, raw_pulses_do_not_overlap_left, raw_pulses_do_not_overlap_right]

theorem A_weak_0_positive_coefficient_verified : RationalBox.StrictBefore A_weak_0_positive_coefficient_left A_weak_0_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, A_weak_0_positive_coefficient_left, A_weak_0_positive_coefficient_right]

theorem A_weak_0_increasing_fixed_flow_verified : RationalBox.StrictBefore A_weak_0_increasing_fixed_flow_left A_weak_0_increasing_fixed_flow_right := by
  norm_num [RationalBox.StrictBefore, A_weak_0_increasing_fixed_flow_left, A_weak_0_increasing_fixed_flow_right]

theorem A_weak_0_never_fires_verified : RationalBox.StrictBefore A_weak_0_never_fires_left A_weak_0_never_fires_right := by
  norm_num [RationalBox.StrictBefore, A_weak_0_never_fires_left, A_weak_0_never_fires_right]

theorem A_weak_0_charge_section_invariant_verified : RationalBox.StrictBefore A_weak_0_charge_section_invariant_left A_weak_0_charge_section_invariant_right := by
  norm_num [RationalBox.StrictBefore, A_weak_0_charge_section_invariant_left, A_weak_0_charge_section_invariant_right]

theorem A_weak_1_positive_coefficient_verified : RationalBox.StrictBefore A_weak_1_positive_coefficient_left A_weak_1_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, A_weak_1_positive_coefficient_left, A_weak_1_positive_coefficient_right]

theorem A_weak_1_increasing_fixed_flow_verified : RationalBox.StrictBefore A_weak_1_increasing_fixed_flow_left A_weak_1_increasing_fixed_flow_right := by
  norm_num [RationalBox.StrictBefore, A_weak_1_increasing_fixed_flow_left, A_weak_1_increasing_fixed_flow_right]

theorem A_weak_1_never_fires_verified : RationalBox.StrictBefore A_weak_1_never_fires_left A_weak_1_never_fires_right := by
  norm_num [RationalBox.StrictBefore, A_weak_1_never_fires_left, A_weak_1_never_fires_right]

theorem A_weak_1_charge_section_invariant_verified : RationalBox.StrictBefore A_weak_1_charge_section_invariant_left A_weak_1_charge_section_invariant_right := by
  norm_num [RationalBox.StrictBefore, A_weak_1_charge_section_invariant_left, A_weak_1_charge_section_invariant_right]

theorem A_weak_2_positive_coefficient_verified : RationalBox.StrictBefore A_weak_2_positive_coefficient_left A_weak_2_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, A_weak_2_positive_coefficient_left, A_weak_2_positive_coefficient_right]

theorem A_weak_2_increasing_fixed_flow_verified : RationalBox.StrictBefore A_weak_2_increasing_fixed_flow_left A_weak_2_increasing_fixed_flow_right := by
  norm_num [RationalBox.StrictBefore, A_weak_2_increasing_fixed_flow_left, A_weak_2_increasing_fixed_flow_right]

theorem A_weak_2_never_fires_verified : RationalBox.StrictBefore A_weak_2_never_fires_left A_weak_2_never_fires_right := by
  norm_num [RationalBox.StrictBefore, A_weak_2_never_fires_left, A_weak_2_never_fires_right]

theorem A_weak_2_charge_section_invariant_verified : RationalBox.StrictBefore A_weak_2_charge_section_invariant_left A_weak_2_charge_section_invariant_right := by
  norm_num [RationalBox.StrictBefore, A_weak_2_charge_section_invariant_left, A_weak_2_charge_section_invariant_right]

theorem A_gain_cap_not_reached_verified : RationalBox.StrictBefore A_gain_cap_not_reached_left A_gain_cap_not_reached_right := by
  norm_num [RationalBox.StrictBefore, A_gain_cap_not_reached_left, A_gain_cap_not_reached_right]

theorem A_strong_positive_coefficient_verified : RationalBox.StrictBefore A_strong_positive_coefficient_left A_strong_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, A_strong_positive_coefficient_left, A_strong_positive_coefficient_right]

theorem A_strong_increasing_flow_verified : RationalBox.StrictBefore A_strong_increasing_flow_left A_strong_increasing_flow_right := by
  norm_num [RationalBox.StrictBefore, A_strong_increasing_flow_left, A_strong_increasing_flow_right]

theorem A_strong_early_below_threshold_verified : RationalBox.StrictBefore A_strong_early_below_threshold_left A_strong_early_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, A_strong_early_below_threshold_left, A_strong_early_below_threshold_right]

theorem A_strong_late_above_threshold_verified : RationalBox.StrictBefore A_strong_late_above_threshold_left A_strong_late_above_threshold_right := by
  norm_num [RationalBox.StrictBefore, A_strong_late_above_threshold_left, A_strong_late_above_threshold_right]

theorem B_weak_0_positive_coefficient_verified : RationalBox.StrictBefore B_weak_0_positive_coefficient_left B_weak_0_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, B_weak_0_positive_coefficient_left, B_weak_0_positive_coefficient_right]

theorem B_weak_0_increasing_fixed_flow_verified : RationalBox.StrictBefore B_weak_0_increasing_fixed_flow_left B_weak_0_increasing_fixed_flow_right := by
  norm_num [RationalBox.StrictBefore, B_weak_0_increasing_fixed_flow_left, B_weak_0_increasing_fixed_flow_right]

theorem B_weak_0_never_fires_verified : RationalBox.StrictBefore B_weak_0_never_fires_left B_weak_0_never_fires_right := by
  norm_num [RationalBox.StrictBefore, B_weak_0_never_fires_left, B_weak_0_never_fires_right]

theorem B_weak_0_charge_section_invariant_verified : RationalBox.StrictBefore B_weak_0_charge_section_invariant_left B_weak_0_charge_section_invariant_right := by
  norm_num [RationalBox.StrictBefore, B_weak_0_charge_section_invariant_left, B_weak_0_charge_section_invariant_right]

theorem B_gain_cap_not_reached_verified : RationalBox.StrictBefore B_gain_cap_not_reached_left B_gain_cap_not_reached_right := by
  norm_num [RationalBox.StrictBefore, B_gain_cap_not_reached_left, B_gain_cap_not_reached_right]

theorem B_strong_positive_coefficient_verified : RationalBox.StrictBefore B_strong_positive_coefficient_left B_strong_positive_coefficient_right := by
  norm_num [RationalBox.StrictBefore, B_strong_positive_coefficient_left, B_strong_positive_coefficient_right]

theorem B_strong_increasing_flow_verified : RationalBox.StrictBefore B_strong_increasing_flow_left B_strong_increasing_flow_right := by
  norm_num [RationalBox.StrictBefore, B_strong_increasing_flow_left, B_strong_increasing_flow_right]

theorem B_strong_early_below_threshold_verified : RationalBox.StrictBefore B_strong_early_below_threshold_left B_strong_early_below_threshold_right := by
  norm_num [RationalBox.StrictBefore, B_strong_early_below_threshold_left, B_strong_early_below_threshold_right]

theorem B_strong_late_above_threshold_verified : RationalBox.StrictBefore B_strong_late_above_threshold_left B_strong_late_above_threshold_right := by
  norm_num [RationalBox.StrictBefore, B_strong_late_above_threshold_left, B_strong_late_above_threshold_right]

theorem A_output_lower_latency_for_delivery_hulls_verified : RationalBox.StrictBefore A_output_lower_latency_for_delivery_hulls_left A_output_lower_latency_for_delivery_hulls_right := by
  norm_num [RationalBox.StrictBefore, A_output_lower_latency_for_delivery_hulls_left, A_output_lower_latency_for_delivery_hulls_right]

theorem mark_complete_before_first_main_fire_verified : RationalBox.StrictBefore mark_complete_before_first_main_fire_left mark_complete_before_first_main_fire_right := by
  norm_num [RationalBox.StrictBefore, mark_complete_before_first_main_fire_left, mark_complete_before_first_main_fire_right]

theorem main_fire_before_error_start_verified : RationalBox.StrictBefore main_fire_before_error_start_left main_fire_before_error_start_right := by
  norm_num [RationalBox.StrictBefore, main_fire_before_error_start_left, main_fire_before_error_start_right]

theorem initial_error_entirely_protected_verified : RationalBox.StrictBefore initial_error_entirely_protected_left initial_error_entirely_protected_right := by
  norm_num [RationalBox.StrictBefore, initial_error_entirely_protected_left, initial_error_entirely_protected_right]

theorem stable_error_entirely_protected_verified : RationalBox.StrictBefore stable_error_entirely_protected_left stable_error_entirely_protected_right := by
  norm_num [RationalBox.StrictBefore, stable_error_entirely_protected_left, stable_error_entirely_protected_right]

theorem next_input_is_after_fast_verified : RationalBox.StrictBefore next_input_is_after_fast_left next_input_is_after_fast_right := by
  norm_num [RationalBox.StrictBefore, next_input_is_after_fast_left, next_input_is_after_fast_right]

theorem low_b_has_not_reopened_at_next_input_verified : RationalBox.StrictBefore low_b_has_not_reopened_at_next_input_left low_b_has_not_reopened_at_next_input_right := by
  norm_num [RationalBox.StrictBefore, low_b_has_not_reopened_at_next_input_left, low_b_has_not_reopened_at_next_input_right]

theorem whole_mark_and_error_of_protected_input_stay_protected_verified : RationalBox.StrictBefore whole_mark_and_error_of_protected_input_stay_protected_left whole_mark_and_error_of_protected_input_stay_protected_right := by
  norm_num [RationalBox.StrictBefore, whole_mark_and_error_of_protected_input_stay_protected_left, whole_mark_and_error_of_protected_input_stay_protected_right]

theorem protected_input_reopens_before_three_time_units_verified : RationalBox.StrictBefore protected_input_reopens_before_three_time_units_left protected_input_reopens_before_three_time_units_right := by
  norm_num [RationalBox.StrictBefore, protected_input_reopens_before_three_time_units_left, protected_input_reopens_before_three_time_units_right]

theorem protected_input_cycle_ends_before_reopening_deadline_verified : RationalBox.StrictBefore protected_input_cycle_ends_before_reopening_deadline_left protected_input_cycle_ends_before_reopening_deadline_right := by
  norm_num [RationalBox.StrictBefore, protected_input_cycle_ends_before_reopening_deadline_left, protected_input_cycle_ends_before_reopening_deadline_right]

theorem protected_input_return_before_following_input_verified : RationalBox.StrictBefore protected_input_return_before_following_input_left protected_input_return_before_following_input_right := by
  norm_num [RationalBox.StrictBefore, protected_input_return_before_following_input_left, protected_input_return_before_following_input_right]

theorem all_later_inputs_follow_stable_return_verified : RationalBox.StrictBefore all_later_inputs_follow_stable_return_left all_later_inputs_follow_stable_return_right := by
  norm_num [RationalBox.StrictBefore, all_later_inputs_follow_stable_return_left, all_later_inputs_follow_stable_return_right]

theorem recovery_cap_not_reached_verified : RationalBox.StrictBefore recovery_cap_not_reached_left recovery_cap_not_reached_right := by
  norm_num [RationalBox.StrictBefore, recovery_cap_not_reached_left, recovery_cap_not_reached_right]

theorem energy_reserve_gate_open_verified : RationalBox.StrictBefore energy_reserve_gate_open_left energy_reserve_gate_open_right := by
  norm_num [RationalBox.StrictBefore, energy_reserve_gate_open_left, energy_reserve_gate_open_right]

theorem A_quiescent_before_second_block_verified : RationalBox.StrictBefore A_quiescent_before_second_block_left A_quiescent_before_second_block_right := by
  norm_num [RationalBox.StrictBefore, A_quiescent_before_second_block_left, A_quiescent_before_second_block_right]

theorem A_first_block_emissions_precede_B_birth_verified : RationalBox.StrictBefore A_first_block_emissions_precede_B_birth_left A_first_block_emissions_precede_B_birth_right := by
  norm_num [RationalBox.StrictBefore, A_first_block_emissions_precede_B_birth_left, A_first_block_emissions_precede_B_birth_right]

theorem first_B_input_strictly_after_birth_verified : RationalBox.StrictBefore first_B_input_strictly_after_birth_left first_B_input_strictly_after_birth_right := by
  norm_num [RationalBox.StrictBefore, first_B_input_strictly_after_birth_left, first_B_input_strictly_after_birth_right]

theorem all_A_teaching_emissions_inside_gate_verified : RationalBox.StrictBefore all_A_teaching_emissions_inside_gate_left all_A_teaching_emissions_inside_gate_right := by
  norm_num [RationalBox.StrictBefore, all_A_teaching_emissions_inside_gate_left, all_A_teaching_emissions_inside_gate_right]

theorem all_A_teaching_deliveries_before_gate_end_verified : RationalBox.StrictBefore all_A_teaching_deliveries_before_gate_end_left all_A_teaching_deliveries_before_gate_end_right := by
  norm_num [RationalBox.StrictBefore, all_A_teaching_deliveries_before_gate_end_left, all_A_teaching_deliveries_before_gate_end_right]

theorem B_teaching_phase_emissions_precede_reverse_gate_verified : RationalBox.StrictBefore B_teaching_phase_emissions_precede_reverse_gate_left B_teaching_phase_emissions_precede_reverse_gate_right := by
  norm_num [RationalBox.StrictBefore, B_teaching_phase_emissions_precede_reverse_gate_left, B_teaching_phase_emissions_precede_reverse_gate_right]

theorem A_quiescent_at_prepared_cut_verified : RationalBox.StrictBefore A_quiescent_at_prepared_cut_left A_quiescent_at_prepared_cut_right := by
  norm_num [RationalBox.StrictBefore, A_quiescent_at_prepared_cut_left, A_quiescent_at_prepared_cut_right]

theorem B_quiescent_at_prepared_cut_verified : RationalBox.StrictBefore B_quiescent_at_prepared_cut_left B_quiescent_at_prepared_cut_right := by
  norm_num [RationalBox.StrictBefore, B_quiescent_at_prepared_cut_left, B_quiescent_at_prepared_cut_right]

theorem entry_b_contains_lower_endpoint_verified : RationalBox.Before entry_b_contains_lower_endpoint_left entry_b_contains_lower_endpoint_right := by
  norm_num [RationalBox.Before, entry_b_contains_lower_endpoint_left, entry_b_contains_lower_endpoint_right]

theorem entry_b_contains_upper_endpoint_verified : RationalBox.Before entry_b_contains_upper_endpoint_left entry_b_contains_upper_endpoint_right := by
  norm_num [RationalBox.Before, entry_b_contains_upper_endpoint_left, entry_b_contains_upper_endpoint_right]

theorem entry_rest_charge_above_section_lower_verified : RationalBox.Before entry_rest_charge_above_section_lower_left entry_rest_charge_above_section_lower_right := by
  norm_num [RationalBox.Before, entry_rest_charge_above_section_lower_left, entry_rest_charge_above_section_lower_right]

theorem entry_rest_charge_below_section_upper_verified : RationalBox.Before entry_rest_charge_below_section_upper_left entry_rest_charge_below_section_upper_right := by
  norm_num [RationalBox.Before, entry_rest_charge_below_section_upper_left, entry_rest_charge_below_section_upper_right]

def Obligations : Prop :=
  RationalBox.StrictBefore birth_aux_below_threshold_left birth_aux_below_threshold_right ∧
  RationalBox.StrictBefore aux_root_early_left aux_root_early_right ∧
  RationalBox.StrictBefore aux_root_late_left aux_root_late_right ∧
  RationalBox.StrictBefore aux_first_crossing_strict_left aux_first_crossing_strict_right ∧
  RationalBox.StrictBefore aux_finish_after_raw_end_left aux_finish_after_raw_end_right ∧
  RationalBox.StrictBefore aux_finish_before_next_input_left aux_finish_before_next_input_right ∧
  RationalBox.StrictBefore raw_pulses_do_not_overlap_left raw_pulses_do_not_overlap_right ∧
  RationalBox.StrictBefore A_weak_0_positive_coefficient_left A_weak_0_positive_coefficient_right ∧
  RationalBox.StrictBefore A_weak_0_increasing_fixed_flow_left A_weak_0_increasing_fixed_flow_right ∧
  RationalBox.StrictBefore A_weak_0_never_fires_left A_weak_0_never_fires_right ∧
  RationalBox.StrictBefore A_weak_0_charge_section_invariant_left A_weak_0_charge_section_invariant_right ∧
  RationalBox.StrictBefore A_weak_1_positive_coefficient_left A_weak_1_positive_coefficient_right ∧
  RationalBox.StrictBefore A_weak_1_increasing_fixed_flow_left A_weak_1_increasing_fixed_flow_right ∧
  RationalBox.StrictBefore A_weak_1_never_fires_left A_weak_1_never_fires_right ∧
  RationalBox.StrictBefore A_weak_1_charge_section_invariant_left A_weak_1_charge_section_invariant_right ∧
  RationalBox.StrictBefore A_weak_2_positive_coefficient_left A_weak_2_positive_coefficient_right ∧
  RationalBox.StrictBefore A_weak_2_increasing_fixed_flow_left A_weak_2_increasing_fixed_flow_right ∧
  RationalBox.StrictBefore A_weak_2_never_fires_left A_weak_2_never_fires_right ∧
  RationalBox.StrictBefore A_weak_2_charge_section_invariant_left A_weak_2_charge_section_invariant_right ∧
  RationalBox.StrictBefore A_gain_cap_not_reached_left A_gain_cap_not_reached_right ∧
  RationalBox.StrictBefore A_strong_positive_coefficient_left A_strong_positive_coefficient_right ∧
  RationalBox.StrictBefore A_strong_increasing_flow_left A_strong_increasing_flow_right ∧
  RationalBox.StrictBefore A_strong_early_below_threshold_left A_strong_early_below_threshold_right ∧
  RationalBox.StrictBefore A_strong_late_above_threshold_left A_strong_late_above_threshold_right ∧
  RationalBox.StrictBefore B_weak_0_positive_coefficient_left B_weak_0_positive_coefficient_right ∧
  RationalBox.StrictBefore B_weak_0_increasing_fixed_flow_left B_weak_0_increasing_fixed_flow_right ∧
  RationalBox.StrictBefore B_weak_0_never_fires_left B_weak_0_never_fires_right ∧
  RationalBox.StrictBefore B_weak_0_charge_section_invariant_left B_weak_0_charge_section_invariant_right ∧
  RationalBox.StrictBefore B_gain_cap_not_reached_left B_gain_cap_not_reached_right ∧
  RationalBox.StrictBefore B_strong_positive_coefficient_left B_strong_positive_coefficient_right ∧
  RationalBox.StrictBefore B_strong_increasing_flow_left B_strong_increasing_flow_right ∧
  RationalBox.StrictBefore B_strong_early_below_threshold_left B_strong_early_below_threshold_right ∧
  RationalBox.StrictBefore B_strong_late_above_threshold_left B_strong_late_above_threshold_right ∧
  RationalBox.StrictBefore A_output_lower_latency_for_delivery_hulls_left A_output_lower_latency_for_delivery_hulls_right ∧
  RationalBox.StrictBefore mark_complete_before_first_main_fire_left mark_complete_before_first_main_fire_right ∧
  RationalBox.StrictBefore main_fire_before_error_start_left main_fire_before_error_start_right ∧
  RationalBox.StrictBefore initial_error_entirely_protected_left initial_error_entirely_protected_right ∧
  RationalBox.StrictBefore stable_error_entirely_protected_left stable_error_entirely_protected_right ∧
  RationalBox.StrictBefore next_input_is_after_fast_left next_input_is_after_fast_right ∧
  RationalBox.StrictBefore low_b_has_not_reopened_at_next_input_left low_b_has_not_reopened_at_next_input_right ∧
  RationalBox.StrictBefore whole_mark_and_error_of_protected_input_stay_protected_left whole_mark_and_error_of_protected_input_stay_protected_right ∧
  RationalBox.StrictBefore protected_input_reopens_before_three_time_units_left protected_input_reopens_before_three_time_units_right ∧
  RationalBox.StrictBefore protected_input_cycle_ends_before_reopening_deadline_left protected_input_cycle_ends_before_reopening_deadline_right ∧
  RationalBox.StrictBefore protected_input_return_before_following_input_left protected_input_return_before_following_input_right ∧
  RationalBox.StrictBefore all_later_inputs_follow_stable_return_left all_later_inputs_follow_stable_return_right ∧
  RationalBox.StrictBefore recovery_cap_not_reached_left recovery_cap_not_reached_right ∧
  RationalBox.StrictBefore energy_reserve_gate_open_left energy_reserve_gate_open_right ∧
  RationalBox.StrictBefore A_quiescent_before_second_block_left A_quiescent_before_second_block_right ∧
  RationalBox.StrictBefore A_first_block_emissions_precede_B_birth_left A_first_block_emissions_precede_B_birth_right ∧
  RationalBox.StrictBefore first_B_input_strictly_after_birth_left first_B_input_strictly_after_birth_right ∧
  RationalBox.StrictBefore all_A_teaching_emissions_inside_gate_left all_A_teaching_emissions_inside_gate_right ∧
  RationalBox.StrictBefore all_A_teaching_deliveries_before_gate_end_left all_A_teaching_deliveries_before_gate_end_right ∧
  RationalBox.StrictBefore B_teaching_phase_emissions_precede_reverse_gate_left B_teaching_phase_emissions_precede_reverse_gate_right ∧
  RationalBox.StrictBefore A_quiescent_at_prepared_cut_left A_quiescent_at_prepared_cut_right ∧
  RationalBox.StrictBefore B_quiescent_at_prepared_cut_left B_quiescent_at_prepared_cut_right ∧
  RationalBox.Before entry_b_contains_lower_endpoint_left entry_b_contains_lower_endpoint_right ∧
  RationalBox.Before entry_b_contains_upper_endpoint_left entry_b_contains_upper_endpoint_right ∧
  RationalBox.Before entry_rest_charge_above_section_lower_left entry_rest_charge_above_section_lower_right ∧
  RationalBox.Before entry_rest_charge_below_section_upper_left entry_rest_charge_below_section_upper_right
theorem obligations_verified : Obligations := by
  exact ⟨birth_aux_below_threshold_verified, aux_root_early_verified, aux_root_late_verified, aux_first_crossing_strict_verified, aux_finish_after_raw_end_verified, aux_finish_before_next_input_verified, raw_pulses_do_not_overlap_verified, A_weak_0_positive_coefficient_verified, A_weak_0_increasing_fixed_flow_verified, A_weak_0_never_fires_verified, A_weak_0_charge_section_invariant_verified, A_weak_1_positive_coefficient_verified, A_weak_1_increasing_fixed_flow_verified, A_weak_1_never_fires_verified, A_weak_1_charge_section_invariant_verified, A_weak_2_positive_coefficient_verified, A_weak_2_increasing_fixed_flow_verified, A_weak_2_never_fires_verified, A_weak_2_charge_section_invariant_verified, A_gain_cap_not_reached_verified, A_strong_positive_coefficient_verified, A_strong_increasing_flow_verified, A_strong_early_below_threshold_verified, A_strong_late_above_threshold_verified, B_weak_0_positive_coefficient_verified, B_weak_0_increasing_fixed_flow_verified, B_weak_0_never_fires_verified, B_weak_0_charge_section_invariant_verified, B_gain_cap_not_reached_verified, B_strong_positive_coefficient_verified, B_strong_increasing_flow_verified, B_strong_early_below_threshold_verified, B_strong_late_above_threshold_verified, A_output_lower_latency_for_delivery_hulls_verified, mark_complete_before_first_main_fire_verified, main_fire_before_error_start_verified, initial_error_entirely_protected_verified, stable_error_entirely_protected_verified, next_input_is_after_fast_verified, low_b_has_not_reopened_at_next_input_verified, whole_mark_and_error_of_protected_input_stay_protected_verified, protected_input_reopens_before_three_time_units_verified, protected_input_cycle_ends_before_reopening_deadline_verified, protected_input_return_before_following_input_verified, all_later_inputs_follow_stable_return_verified, recovery_cap_not_reached_verified, energy_reserve_gate_open_verified, A_quiescent_before_second_block_verified, A_first_block_emissions_precede_B_birth_verified, first_B_input_strictly_after_birth_verified, all_A_teaching_emissions_inside_gate_verified, all_A_teaching_deliveries_before_gate_end_verified, B_teaching_phase_emissions_precede_reverse_gate_verified, A_quiescent_at_prepared_cut_verified, B_quiescent_at_prepared_cut_verified, entry_b_contains_lower_endpoint_verified, entry_b_contains_upper_endpoint_verified, entry_rest_charge_above_section_lower_verified, entry_rest_charge_below_section_upper_verified⟩

def AllBoundsValid : Prop :=
  epsilon.Valid ∧
  a.Valid ∧
  kappa.Valid ∧
  C.Valid ∧
  Lm.Valid ∧
  Ls.Valid ∧
  Le.Valid ∧
  M.Valid ∧
  birth_b.Valid ∧
  mark_dose.Valid ∧
  entry_b.Valid ∧
  gain_dose.Valid ∧
  aux_at_early.Valid ∧
  aux_at_late.Valid ∧
  aux_derivative.Valid ∧
  mark_end.Valid ∧
  error_start.Valid ∧
  aux_finish.Valid ∧
  overlap.Valid ∧
  density.Valid ∧
  A_trained_gain.Valid ∧
  B_trained_port1_gain.Valid ∧
  min_input_gap.Valid ∧
  max_input_gap.Valid ∧
  stable_return_bound.Valid ∧
  low_earliest_return.Valid ∧
  stable_earliest_return.Valid ∧
  slow_before_protected_input_upper.Valid ∧
  slow_through_error_upper.Valid ∧
  slow_at_return_lower.Valid ∧
  protected_pulse_reopen_by.Valid ∧
  slow_return_target.Valid ∧
  birth_aux_below_threshold_left.Valid ∧
  birth_aux_below_threshold_right.Valid ∧
  aux_root_early_left.Valid ∧
  aux_root_early_right.Valid ∧
  aux_root_late_left.Valid ∧
  aux_root_late_right.Valid ∧
  aux_first_crossing_strict_left.Valid ∧
  aux_first_crossing_strict_right.Valid ∧
  aux_finish_after_raw_end_left.Valid ∧
  aux_finish_after_raw_end_right.Valid ∧
  aux_finish_before_next_input_left.Valid ∧
  aux_finish_before_next_input_right.Valid ∧
  raw_pulses_do_not_overlap_left.Valid ∧
  raw_pulses_do_not_overlap_right.Valid ∧
  A_weak_gain_0.Valid ∧
  A_weak_peak_0.Valid ∧
  A_weak_carry_0.Valid ∧
  A_weak_0_positive_coefficient_left.Valid ∧
  A_weak_0_positive_coefficient_right.Valid ∧
  A_weak_0_increasing_fixed_flow_left.Valid ∧
  A_weak_0_increasing_fixed_flow_right.Valid ∧
  A_weak_0_never_fires_left.Valid ∧
  A_weak_0_never_fires_right.Valid ∧
  A_weak_0_charge_section_invariant_left.Valid ∧
  A_weak_0_charge_section_invariant_right.Valid ∧
  A_weak_gain_1.Valid ∧
  A_weak_peak_1.Valid ∧
  A_weak_carry_1.Valid ∧
  A_weak_1_positive_coefficient_left.Valid ∧
  A_weak_1_positive_coefficient_right.Valid ∧
  A_weak_1_increasing_fixed_flow_left.Valid ∧
  A_weak_1_increasing_fixed_flow_right.Valid ∧
  A_weak_1_never_fires_left.Valid ∧
  A_weak_1_never_fires_right.Valid ∧
  A_weak_1_charge_section_invariant_left.Valid ∧
  A_weak_1_charge_section_invariant_right.Valid ∧
  A_weak_gain_2.Valid ∧
  A_weak_peak_2.Valid ∧
  A_weak_carry_2.Valid ∧
  A_weak_2_positive_coefficient_left.Valid ∧
  A_weak_2_positive_coefficient_right.Valid ∧
  A_weak_2_increasing_fixed_flow_left.Valid ∧
  A_weak_2_increasing_fixed_flow_right.Valid ∧
  A_weak_2_never_fires_left.Valid ∧
  A_weak_2_never_fires_right.Valid ∧
  A_weak_2_charge_section_invariant_left.Valid ∧
  A_weak_2_charge_section_invariant_right.Valid ∧
  A_gain_cap_not_reached_left.Valid ∧
  A_gain_cap_not_reached_right.Valid ∧
  A_strong_positive_coefficient_left.Valid ∧
  A_strong_positive_coefficient_right.Valid ∧
  A_strong_increasing_flow_left.Valid ∧
  A_strong_increasing_flow_right.Valid ∧
  A_strong_early_below_threshold_left.Valid ∧
  A_strong_early_below_threshold_right.Valid ∧
  A_strong_late_above_threshold_left.Valid ∧
  A_strong_late_above_threshold_right.Valid ∧
  B_weak_gain_0.Valid ∧
  B_weak_peak_0.Valid ∧
  B_weak_carry_0.Valid ∧
  B_weak_0_positive_coefficient_left.Valid ∧
  B_weak_0_positive_coefficient_right.Valid ∧
  B_weak_0_increasing_fixed_flow_left.Valid ∧
  B_weak_0_increasing_fixed_flow_right.Valid ∧
  B_weak_0_never_fires_left.Valid ∧
  B_weak_0_never_fires_right.Valid ∧
  B_weak_0_charge_section_invariant_left.Valid ∧
  B_weak_0_charge_section_invariant_right.Valid ∧
  B_gain_cap_not_reached_left.Valid ∧
  B_gain_cap_not_reached_right.Valid ∧
  B_strong_positive_coefficient_left.Valid ∧
  B_strong_positive_coefficient_right.Valid ∧
  B_strong_increasing_flow_left.Valid ∧
  B_strong_increasing_flow_right.Valid ∧
  B_strong_early_below_threshold_left.Valid ∧
  B_strong_early_below_threshold_right.Valid ∧
  B_strong_late_above_threshold_left.Valid ∧
  B_strong_late_above_threshold_right.Valid ∧
  A_output_lower_latency_for_delivery_hulls_left.Valid ∧
  A_output_lower_latency_for_delivery_hulls_right.Valid ∧
  mark_complete_before_first_main_fire_left.Valid ∧
  mark_complete_before_first_main_fire_right.Valid ∧
  main_fire_before_error_start_left.Valid ∧
  main_fire_before_error_start_right.Valid ∧
  initial_error_entirely_protected_left.Valid ∧
  initial_error_entirely_protected_right.Valid ∧
  stable_error_entirely_protected_left.Valid ∧
  stable_error_entirely_protected_right.Valid ∧
  next_input_is_after_fast_left.Valid ∧
  next_input_is_after_fast_right.Valid ∧
  low_b_has_not_reopened_at_next_input_left.Valid ∧
  low_b_has_not_reopened_at_next_input_right.Valid ∧
  whole_mark_and_error_of_protected_input_stay_protected_left.Valid ∧
  whole_mark_and_error_of_protected_input_stay_protected_right.Valid ∧
  protected_input_reopens_before_three_time_units_left.Valid ∧
  protected_input_reopens_before_three_time_units_right.Valid ∧
  protected_input_cycle_ends_before_reopening_deadline_left.Valid ∧
  protected_input_cycle_ends_before_reopening_deadline_right.Valid ∧
  protected_input_return_before_following_input_left.Valid ∧
  protected_input_return_before_following_input_right.Valid ∧
  all_later_inputs_follow_stable_return_left.Valid ∧
  all_later_inputs_follow_stable_return_right.Valid ∧
  recovery_cap_not_reached_left.Valid ∧
  recovery_cap_not_reached_right.Valid ∧
  work_bound.Valid ∧
  energy_reserve_gate_open_left.Valid ∧
  energy_reserve_gate_open_right.Valid ∧
  A_first_block_last_return.Valid ∧
  A_second_block_last_emission.Valid ∧
  A_second_block_last_return.Valid ∧
  B_first_possible_arrival.Valid ∧
  B_last_possible_arrival.Valid ∧
  B_last_possible_emission.Valid ∧
  B_last_return.Valid ∧
  A_quiescent_before_second_block_left.Valid ∧
  A_quiescent_before_second_block_right.Valid ∧
  A_first_block_emissions_precede_B_birth_left.Valid ∧
  A_first_block_emissions_precede_B_birth_right.Valid ∧
  first_B_input_strictly_after_birth_left.Valid ∧
  first_B_input_strictly_after_birth_right.Valid ∧
  all_A_teaching_emissions_inside_gate_left.Valid ∧
  all_A_teaching_emissions_inside_gate_right.Valid ∧
  all_A_teaching_deliveries_before_gate_end_left.Valid ∧
  all_A_teaching_deliveries_before_gate_end_right.Valid ∧
  B_teaching_phase_emissions_precede_reverse_gate_left.Valid ∧
  B_teaching_phase_emissions_precede_reverse_gate_right.Valid ∧
  A_quiescent_at_prepared_cut_left.Valid ∧
  A_quiescent_at_prepared_cut_right.Valid ∧
  B_quiescent_at_prepared_cut_left.Valid ∧
  B_quiescent_at_prepared_cut_right.Valid ∧
  entry_b_contains_lower_endpoint_left.Valid ∧
  entry_b_contains_lower_endpoint_right.Valid ∧
  entry_b_contains_upper_endpoint_left.Valid ∧
  entry_b_contains_upper_endpoint_right.Valid ∧
  entry_rest_charge_above_section_lower_left.Valid ∧
  entry_rest_charge_above_section_lower_right.Valid ∧
  entry_rest_charge_below_section_upper_left.Valid ∧
  entry_rest_charge_below_section_upper_right.Valid
theorem all_bounds_valid : AllBoundsValid := by
  exact ⟨epsilon_valid, a_valid, kappa_valid, C_valid, Lm_valid, Ls_valid, Le_valid, M_valid, birth_b_valid, mark_dose_valid, entry_b_valid, gain_dose_valid, aux_at_early_valid, aux_at_late_valid, aux_derivative_valid, mark_end_valid, error_start_valid, aux_finish_valid, overlap_valid, density_valid, A_trained_gain_valid, B_trained_port1_gain_valid, min_input_gap_valid, max_input_gap_valid, stable_return_bound_valid, low_earliest_return_valid, stable_earliest_return_valid, slow_before_protected_input_upper_valid, slow_through_error_upper_valid, slow_at_return_lower_valid, protected_pulse_reopen_by_valid, slow_return_target_valid, birth_aux_below_threshold_left_valid, birth_aux_below_threshold_right_valid, aux_root_early_left_valid, aux_root_early_right_valid, aux_root_late_left_valid, aux_root_late_right_valid, aux_first_crossing_strict_left_valid, aux_first_crossing_strict_right_valid, aux_finish_after_raw_end_left_valid, aux_finish_after_raw_end_right_valid, aux_finish_before_next_input_left_valid, aux_finish_before_next_input_right_valid, raw_pulses_do_not_overlap_left_valid, raw_pulses_do_not_overlap_right_valid, A_weak_gain_0_valid, A_weak_peak_0_valid, A_weak_carry_0_valid, A_weak_0_positive_coefficient_left_valid, A_weak_0_positive_coefficient_right_valid, A_weak_0_increasing_fixed_flow_left_valid, A_weak_0_increasing_fixed_flow_right_valid, A_weak_0_never_fires_left_valid, A_weak_0_never_fires_right_valid, A_weak_0_charge_section_invariant_left_valid, A_weak_0_charge_section_invariant_right_valid, A_weak_gain_1_valid, A_weak_peak_1_valid, A_weak_carry_1_valid, A_weak_1_positive_coefficient_left_valid, A_weak_1_positive_coefficient_right_valid, A_weak_1_increasing_fixed_flow_left_valid, A_weak_1_increasing_fixed_flow_right_valid, A_weak_1_never_fires_left_valid, A_weak_1_never_fires_right_valid, A_weak_1_charge_section_invariant_left_valid, A_weak_1_charge_section_invariant_right_valid, A_weak_gain_2_valid, A_weak_peak_2_valid, A_weak_carry_2_valid, A_weak_2_positive_coefficient_left_valid, A_weak_2_positive_coefficient_right_valid, A_weak_2_increasing_fixed_flow_left_valid, A_weak_2_increasing_fixed_flow_right_valid, A_weak_2_never_fires_left_valid, A_weak_2_never_fires_right_valid, A_weak_2_charge_section_invariant_left_valid, A_weak_2_charge_section_invariant_right_valid, A_gain_cap_not_reached_left_valid, A_gain_cap_not_reached_right_valid, A_strong_positive_coefficient_left_valid, A_strong_positive_coefficient_right_valid, A_strong_increasing_flow_left_valid, A_strong_increasing_flow_right_valid, A_strong_early_below_threshold_left_valid, A_strong_early_below_threshold_right_valid, A_strong_late_above_threshold_left_valid, A_strong_late_above_threshold_right_valid, B_weak_gain_0_valid, B_weak_peak_0_valid, B_weak_carry_0_valid, B_weak_0_positive_coefficient_left_valid, B_weak_0_positive_coefficient_right_valid, B_weak_0_increasing_fixed_flow_left_valid, B_weak_0_increasing_fixed_flow_right_valid, B_weak_0_never_fires_left_valid, B_weak_0_never_fires_right_valid, B_weak_0_charge_section_invariant_left_valid, B_weak_0_charge_section_invariant_right_valid, B_gain_cap_not_reached_left_valid, B_gain_cap_not_reached_right_valid, B_strong_positive_coefficient_left_valid, B_strong_positive_coefficient_right_valid, B_strong_increasing_flow_left_valid, B_strong_increasing_flow_right_valid, B_strong_early_below_threshold_left_valid, B_strong_early_below_threshold_right_valid, B_strong_late_above_threshold_left_valid, B_strong_late_above_threshold_right_valid, A_output_lower_latency_for_delivery_hulls_left_valid, A_output_lower_latency_for_delivery_hulls_right_valid, mark_complete_before_first_main_fire_left_valid, mark_complete_before_first_main_fire_right_valid, main_fire_before_error_start_left_valid, main_fire_before_error_start_right_valid, initial_error_entirely_protected_left_valid, initial_error_entirely_protected_right_valid, stable_error_entirely_protected_left_valid, stable_error_entirely_protected_right_valid, next_input_is_after_fast_left_valid, next_input_is_after_fast_right_valid, low_b_has_not_reopened_at_next_input_left_valid, low_b_has_not_reopened_at_next_input_right_valid, whole_mark_and_error_of_protected_input_stay_protected_left_valid, whole_mark_and_error_of_protected_input_stay_protected_right_valid, protected_input_reopens_before_three_time_units_left_valid, protected_input_reopens_before_three_time_units_right_valid, protected_input_cycle_ends_before_reopening_deadline_left_valid, protected_input_cycle_ends_before_reopening_deadline_right_valid, protected_input_return_before_following_input_left_valid, protected_input_return_before_following_input_right_valid, all_later_inputs_follow_stable_return_left_valid, all_later_inputs_follow_stable_return_right_valid, recovery_cap_not_reached_left_valid, recovery_cap_not_reached_right_valid, work_bound_valid, energy_reserve_gate_open_left_valid, energy_reserve_gate_open_right_valid, A_first_block_last_return_valid, A_second_block_last_emission_valid, A_second_block_last_return_valid, B_first_possible_arrival_valid, B_last_possible_arrival_valid, B_last_possible_emission_valid, B_last_return_valid, A_quiescent_before_second_block_left_valid, A_quiescent_before_second_block_right_valid, A_first_block_emissions_precede_B_birth_left_valid, A_first_block_emissions_precede_B_birth_right_valid, first_B_input_strictly_after_birth_left_valid, first_B_input_strictly_after_birth_right_valid, all_A_teaching_emissions_inside_gate_left_valid, all_A_teaching_emissions_inside_gate_right_valid, all_A_teaching_deliveries_before_gate_end_left_valid, all_A_teaching_deliveries_before_gate_end_right_valid, B_teaching_phase_emissions_precede_reverse_gate_left_valid, B_teaching_phase_emissions_precede_reverse_gate_right_valid, A_quiescent_at_prepared_cut_left_valid, A_quiescent_at_prepared_cut_right_valid, B_quiescent_at_prepared_cut_left_valid, B_quiescent_at_prepared_cut_right_valid, entry_b_contains_lower_endpoint_left_valid, entry_b_contains_lower_endpoint_right_valid, entry_b_contains_upper_endpoint_left_valid, entry_b_contains_upper_endpoint_right_valid, entry_rest_charge_above_section_lower_left_valid, entry_rest_charge_above_section_lower_right_valid, entry_rest_charge_below_section_upper_left_valid, entry_rest_charge_below_section_upper_right_valid⟩

end KernelR.Certificates.Entry010
#print axioms KernelR.Certificates.Entry010.obligations_verified
#print axioms KernelR.Certificates.Entry010.all_bounds_valid
