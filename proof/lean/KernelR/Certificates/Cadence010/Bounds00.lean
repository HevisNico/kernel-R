import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def aux_initial_below_threshold_left : RationalBox := ⟨(2499 / 100000 : ℚ), (2501 / 100000 : ℚ)⟩
theorem aux_initial_below_threshold_left_valid : aux_initial_below_threshold_left.Valid := by norm_num [RationalBox.Valid, aux_initial_below_threshold_left]

def aux_initial_below_threshold_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_initial_below_threshold_right_valid : aux_initial_below_threshold_right.Valid := by norm_num [RationalBox.Valid, aux_initial_below_threshold_right]

def aux_root_early_left : RationalBox := ⟨(857777700395999170890784025356980226903 / 1250000000000000000000000000000000000000 : ℚ), (4165912371719864739736113183069689690047 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_early_left_valid : aux_root_early_left.Valid := by norm_num [RationalBox.Valid, aux_root_early_left]

def aux_root_early_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_root_early_right_valid : aux_root_early_right.Valid := by norm_num [RationalBox.Valid, aux_root_early_right]

def aux_root_late_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_root_late_left_valid : aux_root_late_left.Valid := by norm_num [RationalBox.Valid, aux_root_late_left]

def aux_root_late_right : RationalBox := ⟨(13289056706323197692444281225825371354033 / 10000000000000000000000000000000000000000 : ℚ), (8093421888524132263456113558930151776937 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_late_right_valid : aux_root_late_right.Valid := by norm_num [RationalBox.Valid, aux_root_late_right]

def aux_root_strict_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem aux_root_strict_left_valid : aux_root_strict_left.Valid := by norm_num [RationalBox.Valid, aux_root_strict_left]

def aux_root_strict_right : RationalBox := ⟨(104652753909468400451498982066330214586733 / 2500000000000000000000000000000000000000 : ℚ), (68880481100858260141341200869705380694399 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem aux_root_strict_right_valid : aux_root_strict_right.Valid := by norm_num [RationalBox.Valid, aux_root_strict_right]

def aux_cycle_after_raw_end_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem aux_cycle_after_raw_end_left_valid : aux_cycle_after_raw_end_left.Valid := by norm_num [RationalBox.Valid, aux_cycle_after_raw_end_left]

def aux_cycle_after_raw_end_right : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (5665909090909090909090909090909090909091 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_cycle_after_raw_end_right_valid : aux_cycle_after_raw_end_right.Valid := by norm_num [RationalBox.Valid, aux_cycle_after_raw_end_right]

def reserve_invariant_left : RationalBox := ⟨(10573936830325210453707713866907429323159 / 40000000000000000000000000000000000000 : ℚ), (2643484207581302613426928466726857330789751 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem reserve_invariant_left_valid : reserve_invariant_left.Valid := by norm_num [RationalBox.Valid, reserve_invariant_left]

def reserve_invariant_right : RationalBox := ⟨(500 / 1 : ℚ), (500 / 1 : ℚ)⟩
theorem reserve_invariant_right_valid : reserve_invariant_right.Valid := by norm_num [RationalBox.Valid, reserve_invariant_right]

def aux_mark_end : RationalBox := ⟨(331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_mark_end_valid : aux_mark_end.Valid := by norm_num [RationalBox.Valid, aux_mark_end]

def aux_error_start : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (12300000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_error_start_valid : aux_error_start.Valid := by norm_num [RationalBox.Valid, aux_error_start]

def aux_finish : RationalBox := ⟨(11331818181818181818181818181818181818181 / 10000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem aux_finish_valid : aux_finish.Valid := by norm_num [RationalBox.Valid, aux_finish]

def gain_after_four_doses : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem gain_after_four_doses_valid : gain_after_four_doses.Valid := by norm_num [RationalBox.Valid, gain_after_four_doses]

def mark_integral_deficit : RationalBox := ⟨(23753093049537268852600859055970767301 / 10000000000000000000000000000000000000000 : ℚ), (20349112419161664298811636089759913351 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem mark_integral_deficit_valid : mark_integral_deficit.Valid := by norm_num [RationalBox.Valid, mark_integral_deficit]

def B_teach_0_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_gain_below_cap_left_valid : B_teach_0_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_gain_below_cap_left]

def B_teach_0_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_teach_0_gain_below_cap_right_valid : B_teach_0_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_gain_below_cap_right]

def B_teach_0_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_0_positive_derivative_coefficient_left_valid : B_teach_0_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_positive_derivative_coefficient_left]

def B_teach_0_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_positive_derivative_coefficient_right_valid : B_teach_0_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_positive_derivative_coefficient_right]

def B_teach_0_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_0_fixed_flow_increases_left_valid : B_teach_0_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_fixed_flow_increases_left]

def B_teach_0_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_fixed_flow_increases_right_valid : B_teach_0_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_fixed_flow_increases_right]

def B_teach_0_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_0_strong_crosses_by_one_left_valid : B_teach_0_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_strong_crosses_by_one_left]

def B_teach_0_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_strong_crosses_by_one_right_valid : B_teach_0_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_strong_crosses_by_one_right]

def B_teach_0_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_0_root_latency_valid : B_teach_0_root_latency.Valid := by norm_num [RationalBox.Valid, B_teach_0_root_latency]

def B_teach_0_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_root_lower_left_valid : B_teach_0_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_root_lower_left]

def B_teach_0_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_0_root_lower_right_valid : B_teach_0_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_root_lower_right]

def B_teach_0_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_0_root_upper_left_valid : B_teach_0_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_root_upper_left]

def B_teach_0_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_root_upper_right_valid : B_teach_0_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_root_upper_right]

def B_teach_0_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_MARK_before_fire_left_valid : B_teach_0_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_MARK_before_fire_left]

def B_teach_0_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_teach_0_MARK_before_fire_right_valid : B_teach_0_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_MARK_before_fire_right]

def B_teach_0_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_0_fire_before_ERROR_left_valid : B_teach_0_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_fire_before_ERROR_left]

def B_teach_0_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_fire_before_ERROR_right_valid : B_teach_0_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_fire_before_ERROR_right]

def B_teach_0_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_ERROR_protected_left_valid : B_teach_0_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_teach_0_ERROR_protected_left]

def B_teach_0_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_ERROR_protected_right_valid : B_teach_0_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_teach_0_ERROR_protected_right]

def B_teach_0_arrival : RationalBox := ⟨(480 / 1 : ℚ), (480 / 1 : ℚ)⟩
theorem B_teach_0_arrival_valid : B_teach_0_arrival.Valid := by norm_num [RationalBox.Valid, B_teach_0_arrival]

def B_teach_0_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_teach_0_b_after_valid : B_teach_0_b_after.Valid := by norm_num [RationalBox.Valid, B_teach_0_b_after]

def B_teach_0_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_0_gain_after_valid : B_teach_0_gain_after.Valid := by norm_num [RationalBox.Valid, B_teach_0_gain_after]

def B_teach_0_emission : RationalBox := ⟨(1008002745 / 2097152 : ℚ), (252000703 / 524288 : ℚ)⟩
theorem B_teach_0_emission_valid : B_teach_0_emission.Valid := by norm_num [RationalBox.Valid, B_teach_0_emission]

def Cteach_teach_0_gain_below_cap_left : RationalBox := ⟨(5999940000299999000002499995000008333321 / 5000000000000000000000000000000000000000 : ℚ), (12000120000600002000005000010000016666691 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_0_gain_below_cap_left_valid : Cteach_teach_0_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_gain_below_cap_left]

def Cteach_teach_0_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem Cteach_teach_0_gain_below_cap_right_valid : Cteach_teach_0_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_gain_below_cap_right]

def Cteach_teach_0_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_0_positive_derivative_coefficient_left_valid : Cteach_teach_0_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_positive_derivative_coefficient_left]

def Cteach_teach_0_positive_derivative_coefficient_right : RationalBox := ⟨(4692377521093205688877066849325191738589 / 5000000000000000000000000000000000000000 : ℚ), (2346251207493582485208619499238963559499 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_0_positive_derivative_coefficient_right_valid : Cteach_teach_0_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_positive_derivative_coefficient_right]

def Cteach_teach_0_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_0_fixed_flow_increases_left_valid : Cteach_teach_0_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_fixed_flow_increases_left]

def Cteach_teach_0_fixed_flow_increases_right : RationalBox := ⟨(1625489691252907104314103088553410226223 / 5000000000000000000000000000000000000000 : ℚ), (3252105806558381500100465529019419019071 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_0_fixed_flow_increases_right_valid : Cteach_teach_0_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_fixed_flow_increases_right]

def Cteach_teach_0_weak_no_firing_left : RationalBox := ⟨(7691890290317067526440757850618216222941 / 10000000000000000000000000000000000000000 : ℚ), (385151329636495486242748608897431800621 / 500000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_0_weak_no_firing_left_valid : Cteach_teach_0_weak_no_firing_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_weak_no_firing_left]

def Cteach_teach_0_weak_no_firing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_0_weak_no_firing_right_valid : Cteach_teach_0_weak_no_firing_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_weak_no_firing_right]

def Cteach_teach_0_weak_end_above_rest_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem Cteach_teach_0_weak_end_above_rest_left_valid : Cteach_teach_0_weak_end_above_rest_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_weak_end_above_rest_left]

def Cteach_teach_0_weak_end_above_rest_right : RationalBox := ⟨(7691890290317067526440757850618216222941 / 10000000000000000000000000000000000000000 : ℚ), (7692099449421298661887343054421202778863 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_0_weak_end_above_rest_right_valid : Cteach_teach_0_weak_end_above_rest_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_weak_end_above_rest_right]

def Cteach_teach_0_arrival : RationalBox := ⟨(5043159453 / 10485760 : ℚ), (1261052091 / 2621440 : ℚ)⟩
theorem Cteach_teach_0_arrival_valid : Cteach_teach_0_arrival.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_arrival]

def Cteach_teach_0_b_after : RationalBox := ⟨(7999 / 100000 : ℚ), (8001 / 100000 : ℚ)⟩
theorem Cteach_teach_0_b_after_valid : Cteach_teach_0_b_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_b_after]

def Cteach_teach_0_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_0_gain_after_valid : Cteach_teach_0_gain_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_0_gain_after]

def B_teach_1_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_aux_separation_left_valid : B_teach_1_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_aux_separation_left]

def B_teach_1_aux_separation_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem B_teach_1_aux_separation_right_valid : B_teach_1_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_aux_separation_right]

def B_teach_1_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_gain_below_cap_left_valid : B_teach_1_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_gain_below_cap_left]

def B_teach_1_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_teach_1_gain_below_cap_right_valid : B_teach_1_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_gain_below_cap_right]

def B_teach_1_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_1_ready_at_input_left_valid : B_teach_1_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_ready_at_input_left]

def B_teach_1_ready_at_input_right : RationalBox := ⟨(12560167776998568239254835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1570767921692609286138211337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_ready_at_input_right_valid : B_teach_1_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_ready_at_input_right]

def B_teach_1_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_1_positive_derivative_coefficient_left_valid : B_teach_1_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_positive_derivative_coefficient_left]

def B_teach_1_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_positive_derivative_coefficient_right_valid : B_teach_1_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_positive_derivative_coefficient_right]

def B_teach_1_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_1_fixed_flow_increases_left_valid : B_teach_1_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_fixed_flow_increases_left]

def B_teach_1_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_fixed_flow_increases_right_valid : B_teach_1_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_fixed_flow_increases_right]

def B_teach_1_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_1_strong_crosses_by_one_left_valid : B_teach_1_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_strong_crosses_by_one_left]

def B_teach_1_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_strong_crosses_by_one_right_valid : B_teach_1_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_strong_crosses_by_one_right]

def B_teach_1_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_1_root_latency_valid : B_teach_1_root_latency.Valid := by norm_num [RationalBox.Valid, B_teach_1_root_latency]

def B_teach_1_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_root_lower_left_valid : B_teach_1_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_root_lower_left]

def B_teach_1_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_1_root_lower_right_valid : B_teach_1_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_root_lower_right]

def B_teach_1_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_1_root_upper_left_valid : B_teach_1_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_root_upper_left]

def B_teach_1_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_root_upper_right_valid : B_teach_1_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_root_upper_right]

def B_teach_1_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_MARK_before_fire_left_valid : B_teach_1_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_MARK_before_fire_left]

def B_teach_1_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_teach_1_MARK_before_fire_right_valid : B_teach_1_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_MARK_before_fire_right]

def B_teach_1_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_1_fire_before_ERROR_left_valid : B_teach_1_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_fire_before_ERROR_left]

def B_teach_1_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_fire_before_ERROR_right_valid : B_teach_1_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_fire_before_ERROR_right]

def B_teach_1_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_ERROR_protected_left_valid : B_teach_1_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_teach_1_ERROR_protected_left]

def B_teach_1_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_ERROR_protected_right_valid : B_teach_1_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_teach_1_ERROR_protected_right]

def B_teach_1_arrival : RationalBox := ⟨(488 / 1 : ℚ), (488 / 1 : ℚ)⟩
theorem B_teach_1_arrival_valid : B_teach_1_arrival.Valid := by norm_num [RationalBox.Valid, B_teach_1_arrival]

def B_teach_1_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_teach_1_b_after_valid : B_teach_1_b_after.Valid := by norm_num [RationalBox.Valid, B_teach_1_b_after]

def B_teach_1_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_1_gain_after_valid : B_teach_1_gain_after.Valid := by norm_num [RationalBox.Valid, B_teach_1_gain_after]

def B_teach_1_emission : RationalBox := ⟨(1024779961 / 2097152 : ℚ), (256195007 / 524288 : ℚ)⟩
theorem B_teach_1_emission_valid : B_teach_1_emission.Valid := by norm_num [RationalBox.Valid, B_teach_1_emission]

def Cteach_teach_1_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_aux_separation_left_valid : Cteach_teach_1_aux_separation_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_aux_separation_left]

def Cteach_teach_1_aux_separation_right : RationalBox := ⟨(79 / 10 : ℚ), (81 / 10 : ℚ)⟩
theorem Cteach_teach_1_aux_separation_right_valid : Cteach_teach_1_aux_separation_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_aux_separation_right]

def Cteach_teach_1_gain_below_cap_left : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_gain_below_cap_left_valid : Cteach_teach_1_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_gain_below_cap_left]

def Cteach_teach_1_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem Cteach_teach_1_gain_below_cap_right_valid : Cteach_teach_1_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_gain_below_cap_right]

def Cteach_teach_1_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_1_ready_at_input_left_valid : Cteach_teach_1_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_ready_at_input_left]

def Cteach_teach_1_ready_at_input_right : RationalBox := ⟨(69 / 10 : ℚ), (71 / 10 : ℚ)⟩
theorem Cteach_teach_1_ready_at_input_right_valid : Cteach_teach_1_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_ready_at_input_right]

def Cteach_teach_1_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_1_positive_derivative_coefficient_left_valid : Cteach_teach_1_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_positive_derivative_coefficient_left]

def Cteach_teach_1_positive_derivative_coefficient_right : RationalBox := ⟨(17100195167278017835342433406460031068337 / 10000000000000000000000000000000000000000 : ℚ), (17206933097024086948434659941878384530891 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_positive_derivative_coefficient_right_valid : Cteach_teach_1_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_positive_derivative_coefficient_right]

def Cteach_teach_1_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_1_fixed_flow_increases_left_valid : Cteach_teach_1_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_fixed_flow_increases_left]

def Cteach_teach_1_fixed_flow_increases_right : RationalBox := ⟨(2832839168508788748465362863255299032623 / 5000000000000000000000000000000000000000 : ℚ), (5925585890446356324109807091119032330893 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_fixed_flow_increases_right_valid : Cteach_teach_1_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_fixed_flow_increases_right]

def Cteach_teach_1_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_1_strong_crosses_by_one_left_valid : Cteach_teach_1_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_strong_crosses_by_one_left]

def Cteach_teach_1_strong_crosses_by_one_right : RationalBox := ⟨(13193487728408835122797745211969673693643 / 10000000000000000000000000000000000000000 : ℚ), (13322796378637619461957871113879185414499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_strong_crosses_by_one_right_valid : Cteach_teach_1_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_strong_crosses_by_one_right]

def Cteach_teach_1_root_latency : RationalBox := ⟨(1833595 / 4194304 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_1_root_latency_valid : Cteach_teach_1_root_latency.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_root_latency]

def Cteach_teach_1_root_lower_left : RationalBox := ⟨(2457202228100321524861171618797134272473 / 2500000000000000000000000000000000000000 : ℚ), (9999997344452453160350598075616649051077 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_root_lower_left_valid : Cteach_teach_1_root_lower_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_root_lower_left]

def Cteach_teach_1_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_1_root_lower_right_valid : Cteach_teach_1_root_lower_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_root_lower_right]

def Cteach_teach_1_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_1_root_upper_left_valid : Cteach_teach_1_root_upper_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_root_upper_left]

def Cteach_teach_1_root_upper_right : RationalBox := ⟨(400000052593892859040323911217376832147 / 400000000000000000000000000000000000000 : ℚ), (10169968958439804745769943463249373783977 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_root_upper_right_valid : Cteach_teach_1_root_upper_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_root_upper_right]

def Cteach_teach_1_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_MARK_before_fire_left_valid : Cteach_teach_1_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_MARK_before_fire_left]

def Cteach_teach_1_MARK_before_fire_right : RationalBox := ⟨(1833595 / 4194304 : ℚ), (1833595 / 4194304 : ℚ)⟩
theorem Cteach_teach_1_MARK_before_fire_right_valid : Cteach_teach_1_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_MARK_before_fire_right]

def Cteach_teach_1_fire_before_ERROR_left : RationalBox := ⟨(946931 / 2097152 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_1_fire_before_ERROR_left_valid : Cteach_teach_1_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_fire_before_ERROR_left]

def Cteach_teach_1_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_fire_before_ERROR_right_valid : Cteach_teach_1_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_fire_before_ERROR_right]

def Cteach_teach_1_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_ERROR_protected_left_valid : Cteach_teach_1_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_ERROR_protected_left]

def Cteach_teach_1_ERROR_protected_right : RationalBox := ⟨(128893657376467804256149117206350590107499 / 10000000000000000000000000000000000000000 : ℚ), (128922291462286279192849773317666092192787 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_ERROR_protected_right_valid : Cteach_teach_1_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_ERROR_protected_right]

def Cteach_teach_1_arrival : RationalBox := ⟨(5127045533 / 10485760 : ℚ), (1282023611 / 2621440 : ℚ)⟩
theorem Cteach_teach_1_arrival_valid : Cteach_teach_1_arrival.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_arrival]

def Cteach_teach_1_b_after : RationalBox := ⟨(7999 / 100000 : ℚ), (8001 / 100000 : ℚ)⟩
theorem Cteach_teach_1_b_after_valid : Cteach_teach_1_b_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_b_after]

def Cteach_teach_1_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_1_gain_after_valid : Cteach_teach_1_gain_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_gain_after]

def Cteach_teach_1_emission : RationalBox := ⟨(10263259041 / 20971520 : ℚ), (5132829099 / 10485760 : ℚ)⟩
theorem Cteach_teach_1_emission_valid : Cteach_teach_1_emission.Valid := by norm_num [RationalBox.Valid, Cteach_teach_1_emission]

def B_teach_2_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_aux_separation_left_valid : B_teach_2_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_aux_separation_left]

def B_teach_2_aux_separation_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem B_teach_2_aux_separation_right_valid : B_teach_2_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_aux_separation_right]

def B_teach_2_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_gain_below_cap_left_valid : B_teach_2_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_gain_below_cap_left]

def B_teach_2_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_teach_2_gain_below_cap_right_valid : B_teach_2_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_gain_below_cap_right]

def B_teach_2_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_2_ready_at_input_left_valid : B_teach_2_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_ready_at_input_left]

def B_teach_2_ready_at_input_right : RationalBox := ⟨(12560167776998568239254835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1570767921692609286138211337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_ready_at_input_right_valid : B_teach_2_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_ready_at_input_right]

def B_teach_2_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_2_positive_derivative_coefficient_left_valid : B_teach_2_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_positive_derivative_coefficient_left]

def B_teach_2_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_positive_derivative_coefficient_right_valid : B_teach_2_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_positive_derivative_coefficient_right]

def B_teach_2_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_2_fixed_flow_increases_left_valid : B_teach_2_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_fixed_flow_increases_left]

def B_teach_2_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_fixed_flow_increases_right_valid : B_teach_2_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_fixed_flow_increases_right]

def B_teach_2_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_2_strong_crosses_by_one_left_valid : B_teach_2_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_strong_crosses_by_one_left]

def B_teach_2_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_strong_crosses_by_one_right_valid : B_teach_2_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_strong_crosses_by_one_right]

def B_teach_2_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_2_root_latency_valid : B_teach_2_root_latency.Valid := by norm_num [RationalBox.Valid, B_teach_2_root_latency]

def B_teach_2_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_root_lower_left_valid : B_teach_2_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_root_lower_left]

def B_teach_2_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_2_root_lower_right_valid : B_teach_2_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_root_lower_right]

def B_teach_2_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_2_root_upper_left_valid : B_teach_2_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_root_upper_left]

def B_teach_2_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_root_upper_right_valid : B_teach_2_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_root_upper_right]

def B_teach_2_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_MARK_before_fire_left_valid : B_teach_2_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_MARK_before_fire_left]

def B_teach_2_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_teach_2_MARK_before_fire_right_valid : B_teach_2_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_MARK_before_fire_right]

def B_teach_2_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_2_fire_before_ERROR_left_valid : B_teach_2_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_fire_before_ERROR_left]

def B_teach_2_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_fire_before_ERROR_right_valid : B_teach_2_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_fire_before_ERROR_right]

def B_teach_2_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_ERROR_protected_left_valid : B_teach_2_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_teach_2_ERROR_protected_left]

def B_teach_2_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_ERROR_protected_right_valid : B_teach_2_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_teach_2_ERROR_protected_right]

def B_teach_2_arrival : RationalBox := ⟨(496 / 1 : ℚ), (496 / 1 : ℚ)⟩
theorem B_teach_2_arrival_valid : B_teach_2_arrival.Valid := by norm_num [RationalBox.Valid, B_teach_2_arrival]

def B_teach_2_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_teach_2_b_after_valid : B_teach_2_b_after.Valid := by norm_num [RationalBox.Valid, B_teach_2_b_after]

def B_teach_2_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_2_gain_after_valid : B_teach_2_gain_after.Valid := by norm_num [RationalBox.Valid, B_teach_2_gain_after]

def B_teach_2_emission : RationalBox := ⟨(1041557177 / 2097152 : ℚ), (260389311 / 524288 : ℚ)⟩
theorem B_teach_2_emission_valid : B_teach_2_emission.Valid := by norm_num [RationalBox.Valid, B_teach_2_emission]

def Cteach_teach_2_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_aux_separation_left_valid : Cteach_teach_2_aux_separation_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_aux_separation_left]

def Cteach_teach_2_aux_separation_right : RationalBox := ⟨(79 / 10 : ℚ), (81 / 10 : ℚ)⟩
theorem Cteach_teach_2_aux_separation_right_valid : Cteach_teach_2_aux_separation_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_aux_separation_right]

def Cteach_teach_2_gain_below_cap_left : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_gain_below_cap_left_valid : Cteach_teach_2_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_gain_below_cap_left]

def Cteach_teach_2_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem Cteach_teach_2_gain_below_cap_right_valid : Cteach_teach_2_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_gain_below_cap_right]

def Cteach_teach_2_input_in_SLOW_left : RationalBox := ⟨(10284230561 / 20971520 : ℚ), (5143314859 / 10485760 : ℚ)⟩
theorem Cteach_teach_2_input_in_SLOW_left_valid : Cteach_teach_2_input_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_input_in_SLOW_left]

def Cteach_teach_2_input_in_SLOW_right : RationalBox := ⟨(5210931613 / 10485760 : ℚ), (1302995131 / 2621440 : ℚ)⟩
theorem Cteach_teach_2_input_in_SLOW_right_valid : Cteach_teach_2_input_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_input_in_SLOW_right]

def Cteach_teach_2_input_before_return_left : RationalBox := ⟨(5210931613 / 10485760 : ℚ), (1302995131 / 2621440 : ℚ)⟩
theorem Cteach_teach_2_input_before_return_left_valid : Cteach_teach_2_input_before_return_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_input_before_return_left]

def Cteach_teach_2_input_before_return_right : RationalBox := ⟨(5018425301243960480037399117206350590107499 / 10000000000000000000000000000000000000000 : ℚ), (5019597942535742089739724773317666092192787 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_input_before_return_right_valid : Cteach_teach_2_input_before_return_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_input_before_return_right]

def Cteach_teach_2_whole_MARK_protected_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_whole_MARK_protected_left_valid : Cteach_teach_2_whole_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_whole_MARK_protected_left]

def Cteach_teach_2_whole_MARK_protected_right : RationalBox := ⟨(21419502359539616062369266855930678750083 / 10000000000000000000000000000000000000000 : ℚ), (5354875589884904015592316713982669687521 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_whole_MARK_protected_right_valid : Cteach_teach_2_whole_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_whole_MARK_protected_right]

def Cteach_teach_2_b_below_cap_left : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem Cteach_teach_2_b_below_cap_left_valid : Cteach_teach_2_b_below_cap_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_b_below_cap_left]

def Cteach_teach_2_b_below_cap_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem Cteach_teach_2_b_below_cap_right_valid : Cteach_teach_2_b_below_cap_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_b_below_cap_right]

def Cteach_teach_2_whole_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_whole_ERROR_protected_left_valid : Cteach_teach_2_whole_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_whole_ERROR_protected_left]

def Cteach_teach_2_whole_ERROR_protected_right : RationalBox := ⟨(21419502359539616062369266855930678750083 / 10000000000000000000000000000000000000000 : ℚ), (5354875589884904015592316713982669687521 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_whole_ERROR_protected_right_valid : Cteach_teach_2_whole_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_whole_ERROR_protected_right]

def Cteach_teach_2_no_firing_from_raw_tail_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem Cteach_teach_2_no_firing_from_raw_tail_left_valid : Cteach_teach_2_no_firing_from_raw_tail_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_no_firing_from_raw_tail_left]

def Cteach_teach_2_no_firing_from_raw_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_2_no_firing_from_raw_tail_right_valid : Cteach_teach_2_no_firing_from_raw_tail_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_no_firing_from_raw_tail_right]

def Cteach_teach_2_reopen : RationalBox := ⟨(21419502359539616062369266855930678750083 / 10000000000000000000000000000000000000000 : ℚ), (1123805739217379638756863684054567070727 / 500000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_reopen_valid : Cteach_teach_2_reopen.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_reopen]

def Cteach_teach_2_arrival : RationalBox := ⟨(5210931613 / 10485760 : ℚ), (1302995131 / 2621440 : ℚ)⟩
theorem Cteach_teach_2_arrival_valid : Cteach_teach_2_arrival.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_arrival]

def Cteach_teach_2_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem Cteach_teach_2_b_after_valid : Cteach_teach_2_b_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_b_after]

def Cteach_teach_2_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_2_gain_after_valid : Cteach_teach_2_gain_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_2_gain_after]

def B_teach_3_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_aux_separation_left_valid : B_teach_3_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_aux_separation_left]

def B_teach_3_aux_separation_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem B_teach_3_aux_separation_right_valid : B_teach_3_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_aux_separation_right]

def B_teach_3_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_gain_below_cap_left_valid : B_teach_3_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_gain_below_cap_left]

def B_teach_3_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_teach_3_gain_below_cap_right_valid : B_teach_3_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_gain_below_cap_right]

def B_teach_3_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_3_ready_at_input_left_valid : B_teach_3_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_ready_at_input_left]

def B_teach_3_ready_at_input_right : RationalBox := ⟨(12560167776998568239254835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1570767921692609286138211337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_ready_at_input_right_valid : B_teach_3_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_ready_at_input_right]

def Bounds00Valid : Prop :=
  aux_initial_below_threshold_left.Valid ∧
  aux_initial_below_threshold_right.Valid ∧
  aux_root_early_left.Valid ∧
  aux_root_early_right.Valid ∧
  aux_root_late_left.Valid ∧
  aux_root_late_right.Valid ∧
  aux_root_strict_left.Valid ∧
  aux_root_strict_right.Valid ∧
  aux_cycle_after_raw_end_left.Valid ∧
  aux_cycle_after_raw_end_right.Valid ∧
  reserve_invariant_left.Valid ∧
  reserve_invariant_right.Valid ∧
  aux_mark_end.Valid ∧
  aux_error_start.Valid ∧
  aux_finish.Valid ∧
  gain_after_four_doses.Valid ∧
  mark_integral_deficit.Valid ∧
  B_teach_0_gain_below_cap_left.Valid ∧
  B_teach_0_gain_below_cap_right.Valid ∧
  B_teach_0_positive_derivative_coefficient_left.Valid ∧
  B_teach_0_positive_derivative_coefficient_right.Valid ∧
  B_teach_0_fixed_flow_increases_left.Valid ∧
  B_teach_0_fixed_flow_increases_right.Valid ∧
  B_teach_0_strong_crosses_by_one_left.Valid ∧
  B_teach_0_strong_crosses_by_one_right.Valid ∧
  B_teach_0_root_latency.Valid ∧
  B_teach_0_root_lower_left.Valid ∧
  B_teach_0_root_lower_right.Valid ∧
  B_teach_0_root_upper_left.Valid ∧
  B_teach_0_root_upper_right.Valid ∧
  B_teach_0_MARK_before_fire_left.Valid ∧
  B_teach_0_MARK_before_fire_right.Valid ∧
  B_teach_0_fire_before_ERROR_left.Valid ∧
  B_teach_0_fire_before_ERROR_right.Valid ∧
  B_teach_0_ERROR_protected_left.Valid ∧
  B_teach_0_ERROR_protected_right.Valid ∧
  B_teach_0_arrival.Valid ∧
  B_teach_0_b_after.Valid ∧
  B_teach_0_gain_after.Valid ∧
  B_teach_0_emission.Valid ∧
  Cteach_teach_0_gain_below_cap_left.Valid ∧
  Cteach_teach_0_gain_below_cap_right.Valid ∧
  Cteach_teach_0_positive_derivative_coefficient_left.Valid ∧
  Cteach_teach_0_positive_derivative_coefficient_right.Valid ∧
  Cteach_teach_0_fixed_flow_increases_left.Valid ∧
  Cteach_teach_0_fixed_flow_increases_right.Valid ∧
  Cteach_teach_0_weak_no_firing_left.Valid ∧
  Cteach_teach_0_weak_no_firing_right.Valid ∧
  Cteach_teach_0_weak_end_above_rest_left.Valid ∧
  Cteach_teach_0_weak_end_above_rest_right.Valid ∧
  Cteach_teach_0_arrival.Valid ∧
  Cteach_teach_0_b_after.Valid ∧
  Cteach_teach_0_gain_after.Valid ∧
  B_teach_1_aux_separation_left.Valid ∧
  B_teach_1_aux_separation_right.Valid ∧
  B_teach_1_gain_below_cap_left.Valid ∧
  B_teach_1_gain_below_cap_right.Valid ∧
  B_teach_1_ready_at_input_left.Valid ∧
  B_teach_1_ready_at_input_right.Valid ∧
  B_teach_1_positive_derivative_coefficient_left.Valid ∧
  B_teach_1_positive_derivative_coefficient_right.Valid ∧
  B_teach_1_fixed_flow_increases_left.Valid ∧
  B_teach_1_fixed_flow_increases_right.Valid ∧
  B_teach_1_strong_crosses_by_one_left.Valid ∧
  B_teach_1_strong_crosses_by_one_right.Valid ∧
  B_teach_1_root_latency.Valid ∧
  B_teach_1_root_lower_left.Valid ∧
  B_teach_1_root_lower_right.Valid ∧
  B_teach_1_root_upper_left.Valid ∧
  B_teach_1_root_upper_right.Valid ∧
  B_teach_1_MARK_before_fire_left.Valid ∧
  B_teach_1_MARK_before_fire_right.Valid ∧
  B_teach_1_fire_before_ERROR_left.Valid ∧
  B_teach_1_fire_before_ERROR_right.Valid ∧
  B_teach_1_ERROR_protected_left.Valid ∧
  B_teach_1_ERROR_protected_right.Valid ∧
  B_teach_1_arrival.Valid ∧
  B_teach_1_b_after.Valid ∧
  B_teach_1_gain_after.Valid ∧
  B_teach_1_emission.Valid ∧
  Cteach_teach_1_aux_separation_left.Valid ∧
  Cteach_teach_1_aux_separation_right.Valid ∧
  Cteach_teach_1_gain_below_cap_left.Valid ∧
  Cteach_teach_1_gain_below_cap_right.Valid ∧
  Cteach_teach_1_ready_at_input_left.Valid ∧
  Cteach_teach_1_ready_at_input_right.Valid ∧
  Cteach_teach_1_positive_derivative_coefficient_left.Valid ∧
  Cteach_teach_1_positive_derivative_coefficient_right.Valid ∧
  Cteach_teach_1_fixed_flow_increases_left.Valid ∧
  Cteach_teach_1_fixed_flow_increases_right.Valid ∧
  Cteach_teach_1_strong_crosses_by_one_left.Valid ∧
  Cteach_teach_1_strong_crosses_by_one_right.Valid ∧
  Cteach_teach_1_root_latency.Valid ∧
  Cteach_teach_1_root_lower_left.Valid ∧
  Cteach_teach_1_root_lower_right.Valid ∧
  Cteach_teach_1_root_upper_left.Valid ∧
  Cteach_teach_1_root_upper_right.Valid ∧
  Cteach_teach_1_MARK_before_fire_left.Valid ∧
  Cteach_teach_1_MARK_before_fire_right.Valid ∧
  Cteach_teach_1_fire_before_ERROR_left.Valid ∧
  Cteach_teach_1_fire_before_ERROR_right.Valid ∧
  Cteach_teach_1_ERROR_protected_left.Valid ∧
  Cteach_teach_1_ERROR_protected_right.Valid ∧
  Cteach_teach_1_arrival.Valid ∧
  Cteach_teach_1_b_after.Valid ∧
  Cteach_teach_1_gain_after.Valid ∧
  Cteach_teach_1_emission.Valid ∧
  B_teach_2_aux_separation_left.Valid ∧
  B_teach_2_aux_separation_right.Valid ∧
  B_teach_2_gain_below_cap_left.Valid ∧
  B_teach_2_gain_below_cap_right.Valid ∧
  B_teach_2_ready_at_input_left.Valid ∧
  B_teach_2_ready_at_input_right.Valid ∧
  B_teach_2_positive_derivative_coefficient_left.Valid ∧
  B_teach_2_positive_derivative_coefficient_right.Valid ∧
  B_teach_2_fixed_flow_increases_left.Valid ∧
  B_teach_2_fixed_flow_increases_right.Valid ∧
  B_teach_2_strong_crosses_by_one_left.Valid ∧
  B_teach_2_strong_crosses_by_one_right.Valid ∧
  B_teach_2_root_latency.Valid ∧
  B_teach_2_root_lower_left.Valid ∧
  B_teach_2_root_lower_right.Valid ∧
  B_teach_2_root_upper_left.Valid ∧
  B_teach_2_root_upper_right.Valid ∧
  B_teach_2_MARK_before_fire_left.Valid ∧
  B_teach_2_MARK_before_fire_right.Valid ∧
  B_teach_2_fire_before_ERROR_left.Valid ∧
  B_teach_2_fire_before_ERROR_right.Valid ∧
  B_teach_2_ERROR_protected_left.Valid ∧
  B_teach_2_ERROR_protected_right.Valid ∧
  B_teach_2_arrival.Valid ∧
  B_teach_2_b_after.Valid ∧
  B_teach_2_gain_after.Valid ∧
  B_teach_2_emission.Valid ∧
  Cteach_teach_2_aux_separation_left.Valid ∧
  Cteach_teach_2_aux_separation_right.Valid ∧
  Cteach_teach_2_gain_below_cap_left.Valid ∧
  Cteach_teach_2_gain_below_cap_right.Valid ∧
  Cteach_teach_2_input_in_SLOW_left.Valid ∧
  Cteach_teach_2_input_in_SLOW_right.Valid ∧
  Cteach_teach_2_input_before_return_left.Valid ∧
  Cteach_teach_2_input_before_return_right.Valid ∧
  Cteach_teach_2_whole_MARK_protected_left.Valid ∧
  Cteach_teach_2_whole_MARK_protected_right.Valid ∧
  Cteach_teach_2_b_below_cap_left.Valid ∧
  Cteach_teach_2_b_below_cap_right.Valid ∧
  Cteach_teach_2_whole_ERROR_protected_left.Valid ∧
  Cteach_teach_2_whole_ERROR_protected_right.Valid ∧
  Cteach_teach_2_no_firing_from_raw_tail_left.Valid ∧
  Cteach_teach_2_no_firing_from_raw_tail_right.Valid ∧
  Cteach_teach_2_reopen.Valid ∧
  Cteach_teach_2_arrival.Valid ∧
  Cteach_teach_2_b_after.Valid ∧
  Cteach_teach_2_gain_after.Valid ∧
  B_teach_3_aux_separation_left.Valid ∧
  B_teach_3_aux_separation_right.Valid ∧
  B_teach_3_gain_below_cap_left.Valid ∧
  B_teach_3_gain_below_cap_right.Valid ∧
  B_teach_3_ready_at_input_left.Valid ∧
  B_teach_3_ready_at_input_right.Valid
theorem Bounds00Valid_verified : Bounds00Valid := by
  exact ⟨aux_initial_below_threshold_left_valid, aux_initial_below_threshold_right_valid, aux_root_early_left_valid, aux_root_early_right_valid, aux_root_late_left_valid, aux_root_late_right_valid, aux_root_strict_left_valid, aux_root_strict_right_valid, aux_cycle_after_raw_end_left_valid, aux_cycle_after_raw_end_right_valid, reserve_invariant_left_valid, reserve_invariant_right_valid, aux_mark_end_valid, aux_error_start_valid, aux_finish_valid, gain_after_four_doses_valid, mark_integral_deficit_valid, B_teach_0_gain_below_cap_left_valid, B_teach_0_gain_below_cap_right_valid, B_teach_0_positive_derivative_coefficient_left_valid, B_teach_0_positive_derivative_coefficient_right_valid, B_teach_0_fixed_flow_increases_left_valid, B_teach_0_fixed_flow_increases_right_valid, B_teach_0_strong_crosses_by_one_left_valid, B_teach_0_strong_crosses_by_one_right_valid, B_teach_0_root_latency_valid, B_teach_0_root_lower_left_valid, B_teach_0_root_lower_right_valid, B_teach_0_root_upper_left_valid, B_teach_0_root_upper_right_valid, B_teach_0_MARK_before_fire_left_valid, B_teach_0_MARK_before_fire_right_valid, B_teach_0_fire_before_ERROR_left_valid, B_teach_0_fire_before_ERROR_right_valid, B_teach_0_ERROR_protected_left_valid, B_teach_0_ERROR_protected_right_valid, B_teach_0_arrival_valid, B_teach_0_b_after_valid, B_teach_0_gain_after_valid, B_teach_0_emission_valid, Cteach_teach_0_gain_below_cap_left_valid, Cteach_teach_0_gain_below_cap_right_valid, Cteach_teach_0_positive_derivative_coefficient_left_valid, Cteach_teach_0_positive_derivative_coefficient_right_valid, Cteach_teach_0_fixed_flow_increases_left_valid, Cteach_teach_0_fixed_flow_increases_right_valid, Cteach_teach_0_weak_no_firing_left_valid, Cteach_teach_0_weak_no_firing_right_valid, Cteach_teach_0_weak_end_above_rest_left_valid, Cteach_teach_0_weak_end_above_rest_right_valid, Cteach_teach_0_arrival_valid, Cteach_teach_0_b_after_valid, Cteach_teach_0_gain_after_valid, B_teach_1_aux_separation_left_valid, B_teach_1_aux_separation_right_valid, B_teach_1_gain_below_cap_left_valid, B_teach_1_gain_below_cap_right_valid, B_teach_1_ready_at_input_left_valid, B_teach_1_ready_at_input_right_valid, B_teach_1_positive_derivative_coefficient_left_valid, B_teach_1_positive_derivative_coefficient_right_valid, B_teach_1_fixed_flow_increases_left_valid, B_teach_1_fixed_flow_increases_right_valid, B_teach_1_strong_crosses_by_one_left_valid, B_teach_1_strong_crosses_by_one_right_valid, B_teach_1_root_latency_valid, B_teach_1_root_lower_left_valid, B_teach_1_root_lower_right_valid, B_teach_1_root_upper_left_valid, B_teach_1_root_upper_right_valid, B_teach_1_MARK_before_fire_left_valid, B_teach_1_MARK_before_fire_right_valid, B_teach_1_fire_before_ERROR_left_valid, B_teach_1_fire_before_ERROR_right_valid, B_teach_1_ERROR_protected_left_valid, B_teach_1_ERROR_protected_right_valid, B_teach_1_arrival_valid, B_teach_1_b_after_valid, B_teach_1_gain_after_valid, B_teach_1_emission_valid, Cteach_teach_1_aux_separation_left_valid, Cteach_teach_1_aux_separation_right_valid, Cteach_teach_1_gain_below_cap_left_valid, Cteach_teach_1_gain_below_cap_right_valid, Cteach_teach_1_ready_at_input_left_valid, Cteach_teach_1_ready_at_input_right_valid, Cteach_teach_1_positive_derivative_coefficient_left_valid, Cteach_teach_1_positive_derivative_coefficient_right_valid, Cteach_teach_1_fixed_flow_increases_left_valid, Cteach_teach_1_fixed_flow_increases_right_valid, Cteach_teach_1_strong_crosses_by_one_left_valid, Cteach_teach_1_strong_crosses_by_one_right_valid, Cteach_teach_1_root_latency_valid, Cteach_teach_1_root_lower_left_valid, Cteach_teach_1_root_lower_right_valid, Cteach_teach_1_root_upper_left_valid, Cteach_teach_1_root_upper_right_valid, Cteach_teach_1_MARK_before_fire_left_valid, Cteach_teach_1_MARK_before_fire_right_valid, Cteach_teach_1_fire_before_ERROR_left_valid, Cteach_teach_1_fire_before_ERROR_right_valid, Cteach_teach_1_ERROR_protected_left_valid, Cteach_teach_1_ERROR_protected_right_valid, Cteach_teach_1_arrival_valid, Cteach_teach_1_b_after_valid, Cteach_teach_1_gain_after_valid, Cteach_teach_1_emission_valid, B_teach_2_aux_separation_left_valid, B_teach_2_aux_separation_right_valid, B_teach_2_gain_below_cap_left_valid, B_teach_2_gain_below_cap_right_valid, B_teach_2_ready_at_input_left_valid, B_teach_2_ready_at_input_right_valid, B_teach_2_positive_derivative_coefficient_left_valid, B_teach_2_positive_derivative_coefficient_right_valid, B_teach_2_fixed_flow_increases_left_valid, B_teach_2_fixed_flow_increases_right_valid, B_teach_2_strong_crosses_by_one_left_valid, B_teach_2_strong_crosses_by_one_right_valid, B_teach_2_root_latency_valid, B_teach_2_root_lower_left_valid, B_teach_2_root_lower_right_valid, B_teach_2_root_upper_left_valid, B_teach_2_root_upper_right_valid, B_teach_2_MARK_before_fire_left_valid, B_teach_2_MARK_before_fire_right_valid, B_teach_2_fire_before_ERROR_left_valid, B_teach_2_fire_before_ERROR_right_valid, B_teach_2_ERROR_protected_left_valid, B_teach_2_ERROR_protected_right_valid, B_teach_2_arrival_valid, B_teach_2_b_after_valid, B_teach_2_gain_after_valid, B_teach_2_emission_valid, Cteach_teach_2_aux_separation_left_valid, Cteach_teach_2_aux_separation_right_valid, Cteach_teach_2_gain_below_cap_left_valid, Cteach_teach_2_gain_below_cap_right_valid, Cteach_teach_2_input_in_SLOW_left_valid, Cteach_teach_2_input_in_SLOW_right_valid, Cteach_teach_2_input_before_return_left_valid, Cteach_teach_2_input_before_return_right_valid, Cteach_teach_2_whole_MARK_protected_left_valid, Cteach_teach_2_whole_MARK_protected_right_valid, Cteach_teach_2_b_below_cap_left_valid, Cteach_teach_2_b_below_cap_right_valid, Cteach_teach_2_whole_ERROR_protected_left_valid, Cteach_teach_2_whole_ERROR_protected_right_valid, Cteach_teach_2_no_firing_from_raw_tail_left_valid, Cteach_teach_2_no_firing_from_raw_tail_right_valid, Cteach_teach_2_reopen_valid, Cteach_teach_2_arrival_valid, Cteach_teach_2_b_after_valid, Cteach_teach_2_gain_after_valid, B_teach_3_aux_separation_left_valid, B_teach_3_aux_separation_right_valid, B_teach_3_gain_below_cap_left_valid, B_teach_3_gain_below_cap_right_valid, B_teach_3_ready_at_input_left_valid, B_teach_3_ready_at_input_right_valid⟩

end KernelR.Certificates.Cadence010
