import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def B_teach_3_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_3_positive_derivative_coefficient_left_valid : B_teach_3_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_positive_derivative_coefficient_left]

def B_teach_3_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_positive_derivative_coefficient_right_valid : B_teach_3_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_positive_derivative_coefficient_right]

def B_teach_3_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_3_fixed_flow_increases_left_valid : B_teach_3_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_fixed_flow_increases_left]

def B_teach_3_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_fixed_flow_increases_right_valid : B_teach_3_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_fixed_flow_increases_right]

def B_teach_3_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_3_strong_crosses_by_one_left_valid : B_teach_3_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_strong_crosses_by_one_left]

def B_teach_3_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_strong_crosses_by_one_right_valid : B_teach_3_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_strong_crosses_by_one_right]

def B_teach_3_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_3_root_latency_valid : B_teach_3_root_latency.Valid := by norm_num [RationalBox.Valid, B_teach_3_root_latency]

def B_teach_3_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_root_lower_left_valid : B_teach_3_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_root_lower_left]

def B_teach_3_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_3_root_lower_right_valid : B_teach_3_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_root_lower_right]

def B_teach_3_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_3_root_upper_left_valid : B_teach_3_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_root_upper_left]

def B_teach_3_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_root_upper_right_valid : B_teach_3_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_root_upper_right]

def B_teach_3_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_MARK_before_fire_left_valid : B_teach_3_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_MARK_before_fire_left]

def B_teach_3_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_teach_3_MARK_before_fire_right_valid : B_teach_3_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_MARK_before_fire_right]

def B_teach_3_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_3_fire_before_ERROR_left_valid : B_teach_3_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_fire_before_ERROR_left]

def B_teach_3_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_fire_before_ERROR_right_valid : B_teach_3_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_fire_before_ERROR_right]

def B_teach_3_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_ERROR_protected_left_valid : B_teach_3_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_teach_3_ERROR_protected_left]

def B_teach_3_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_ERROR_protected_right_valid : B_teach_3_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_teach_3_ERROR_protected_right]

def B_teach_3_arrival : RationalBox := ⟨(504 / 1 : ℚ), (504 / 1 : ℚ)⟩
theorem B_teach_3_arrival_valid : B_teach_3_arrival.Valid := by norm_num [RationalBox.Valid, B_teach_3_arrival]

def B_teach_3_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_teach_3_b_after_valid : B_teach_3_b_after.Valid := by norm_num [RationalBox.Valid, B_teach_3_b_after]

def B_teach_3_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_3_gain_after_valid : B_teach_3_gain_after.Valid := by norm_num [RationalBox.Valid, B_teach_3_gain_after]

def B_teach_3_emission : RationalBox := ⟨(1058334393 / 2097152 : ℚ), (264583615 / 524288 : ℚ)⟩
theorem B_teach_3_emission_valid : B_teach_3_emission.Valid := by norm_num [RationalBox.Valid, B_teach_3_emission]

def Cteach_teach_3_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_aux_separation_left_valid : Cteach_teach_3_aux_separation_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_aux_separation_left]

def Cteach_teach_3_aux_separation_right : RationalBox := ⟨(79 / 10 : ℚ), (81 / 10 : ℚ)⟩
theorem Cteach_teach_3_aux_separation_right_valid : Cteach_teach_3_aux_separation_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_aux_separation_right]

def Cteach_teach_3_gain_below_cap_left : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_gain_below_cap_left_valid : Cteach_teach_3_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_gain_below_cap_left]

def Cteach_teach_3_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem Cteach_teach_3_gain_below_cap_right_valid : Cteach_teach_3_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_gain_below_cap_right]

def Cteach_teach_3_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_3_ready_at_input_left_valid : Cteach_teach_3_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_ready_at_input_left]

def Cteach_teach_3_ready_at_input_right : RationalBox := ⟨(2826194260782620361243136315945432929273 / 500000000000000000000000000000000000000 : ℚ), (59580497640460383937630733144069321249917 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_ready_at_input_right_valid : Cteach_teach_3_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_ready_at_input_right]

def Cteach_teach_3_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_3_positive_derivative_coefficient_left_valid : Cteach_teach_3_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_positive_derivative_coefficient_left]

def Cteach_teach_3_positive_derivative_coefficient_right : RationalBox := ⟨(17100195167278017835342433406460031068337 / 10000000000000000000000000000000000000000 : ℚ), (1710053717460142522952896861667567200817 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_positive_derivative_coefficient_right_valid : Cteach_teach_3_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_positive_derivative_coefficient_right]

def Cteach_teach_3_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_3_fixed_flow_increases_left_valid : Cteach_teach_3_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_fixed_flow_increases_left]

def Cteach_teach_3_fixed_flow_increases_right : RationalBox := ⟨(2892484322797159284351892249906292051 / 4882812500000000000000000000000000000 : ℚ), (5925585890446356324109807091119032330893 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_fixed_flow_increases_right_valid : Cteach_teach_3_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_fixed_flow_increases_right]

def Cteach_teach_3_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_3_strong_crosses_by_one_left_valid : Cteach_teach_3_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_strong_crosses_by_one_left]

def Cteach_teach_3_strong_crosses_by_one_right : RationalBox := ⟨(13193487728408835122797745211969673693643 / 10000000000000000000000000000000000000000 : ℚ), (13193731600602117103246896313230441386899 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_strong_crosses_by_one_right_valid : Cteach_teach_3_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_strong_crosses_by_one_right]

def Cteach_teach_3_root_latency : RationalBox := ⟨(1893797 / 4194304 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_3_root_latency_valid : Cteach_teach_3_root_latency.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_root_latency]

def Cteach_teach_3_root_lower_left : RationalBox := ⟨(1249977481575347633857846140220403846377 / 1250000000000000000000000000000000000000 : ℚ), (999999985079980909682454510070632893983 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_root_lower_left_valid : Cteach_teach_3_root_lower_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_root_lower_left]

def Cteach_teach_3_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_3_root_lower_right_valid : Cteach_teach_3_root_lower_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_root_lower_right]

def Cteach_teach_3_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_3_root_upper_left_valid : Cteach_teach_3_root_upper_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_root_upper_left]

def Cteach_teach_3_root_upper_right : RationalBox := ⟨(400000052593892859040323911217376832147 / 400000000000000000000000000000000000000 : ℚ), (5000090658336815342734417808060050466907 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_root_upper_right_valid : Cteach_teach_3_root_upper_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_root_upper_right]

def Cteach_teach_3_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_MARK_before_fire_left_valid : Cteach_teach_3_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_MARK_before_fire_left]

def Cteach_teach_3_MARK_before_fire_right : RationalBox := ⟨(1893797 / 4194304 : ℚ), (1893797 / 4194304 : ℚ)⟩
theorem Cteach_teach_3_MARK_before_fire_right_valid : Cteach_teach_3_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_MARK_before_fire_right]

def Cteach_teach_3_fire_before_ERROR_left : RationalBox := ⟨(946931 / 2097152 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_3_fire_before_ERROR_left_valid : Cteach_teach_3_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_fire_before_ERROR_left]

def Cteach_teach_3_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_fire_before_ERROR_right_valid : Cteach_teach_3_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_fire_before_ERROR_right]

def Cteach_teach_3_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_ERROR_protected_left_valid : Cteach_teach_3_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_ERROR_protected_left]

def Cteach_teach_3_ERROR_protected_right : RationalBox := ⟨(8177172082179308438471163662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (65423032773080777463870164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_ERROR_protected_right_valid : Cteach_teach_3_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_ERROR_protected_right]

def Cteach_teach_3_arrival : RationalBox := ⟨(5294817693 / 10485760 : ℚ), (1323966651 / 2621440 : ℚ)⟩
theorem Cteach_teach_3_arrival_valid : Cteach_teach_3_arrival.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_arrival]

def Cteach_teach_3_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem Cteach_teach_3_b_after_valid : Cteach_teach_3_b_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_b_after]

def Cteach_teach_3_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_3_gain_after_valid : Cteach_teach_3_gain_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_gain_after]

def Cteach_teach_3_emission : RationalBox := ⟨(10599104371 / 20971520 : ℚ), (5300601259 / 10485760 : ℚ)⟩
theorem Cteach_teach_3_emission_valid : Cteach_teach_3_emission.Valid := by norm_num [RationalBox.Valid, Cteach_teach_3_emission]

def B_teach_4_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_aux_separation_left_valid : B_teach_4_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_aux_separation_left]

def B_teach_4_aux_separation_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem B_teach_4_aux_separation_right_valid : B_teach_4_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_aux_separation_right]

def B_teach_4_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_gain_below_cap_left_valid : B_teach_4_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_gain_below_cap_left]

def B_teach_4_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_teach_4_gain_below_cap_right_valid : B_teach_4_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_gain_below_cap_right]

def B_teach_4_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_4_ready_at_input_left_valid : B_teach_4_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_ready_at_input_left]

def B_teach_4_ready_at_input_right : RationalBox := ⟨(12560167776998568239254835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1570767921692609286138211337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_ready_at_input_right_valid : B_teach_4_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_ready_at_input_right]

def B_teach_4_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_4_positive_derivative_coefficient_left_valid : B_teach_4_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_positive_derivative_coefficient_left]

def B_teach_4_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_positive_derivative_coefficient_right_valid : B_teach_4_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_positive_derivative_coefficient_right]

def B_teach_4_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_4_fixed_flow_increases_left_valid : B_teach_4_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_fixed_flow_increases_left]

def B_teach_4_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_fixed_flow_increases_right_valid : B_teach_4_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_fixed_flow_increases_right]

def B_teach_4_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_4_strong_crosses_by_one_left_valid : B_teach_4_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_strong_crosses_by_one_left]

def B_teach_4_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_strong_crosses_by_one_right_valid : B_teach_4_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_strong_crosses_by_one_right]

def B_teach_4_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_4_root_latency_valid : B_teach_4_root_latency.Valid := by norm_num [RationalBox.Valid, B_teach_4_root_latency]

def B_teach_4_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_root_lower_left_valid : B_teach_4_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_root_lower_left]

def B_teach_4_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_4_root_lower_right_valid : B_teach_4_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_root_lower_right]

def B_teach_4_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_4_root_upper_left_valid : B_teach_4_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_root_upper_left]

def B_teach_4_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_root_upper_right_valid : B_teach_4_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_root_upper_right]

def B_teach_4_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_MARK_before_fire_left_valid : B_teach_4_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_MARK_before_fire_left]

def B_teach_4_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_teach_4_MARK_before_fire_right_valid : B_teach_4_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_MARK_before_fire_right]

def B_teach_4_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_4_fire_before_ERROR_left_valid : B_teach_4_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_fire_before_ERROR_left]

def B_teach_4_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_fire_before_ERROR_right_valid : B_teach_4_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_fire_before_ERROR_right]

def B_teach_4_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_ERROR_protected_left_valid : B_teach_4_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_teach_4_ERROR_protected_left]

def B_teach_4_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_ERROR_protected_right_valid : B_teach_4_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_teach_4_ERROR_protected_right]

def B_teach_4_arrival : RationalBox := ⟨(512 / 1 : ℚ), (512 / 1 : ℚ)⟩
theorem B_teach_4_arrival_valid : B_teach_4_arrival.Valid := by norm_num [RationalBox.Valid, B_teach_4_arrival]

def B_teach_4_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_teach_4_b_after_valid : B_teach_4_b_after.Valid := by norm_num [RationalBox.Valid, B_teach_4_b_after]

def B_teach_4_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_4_gain_after_valid : B_teach_4_gain_after.Valid := by norm_num [RationalBox.Valid, B_teach_4_gain_after]

def B_teach_4_emission : RationalBox := ⟨(1075111609 / 2097152 : ℚ), (268777919 / 524288 : ℚ)⟩
theorem B_teach_4_emission_valid : B_teach_4_emission.Valid := by norm_num [RationalBox.Valid, B_teach_4_emission]

def Cteach_teach_4_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_aux_separation_left_valid : Cteach_teach_4_aux_separation_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_aux_separation_left]

def Cteach_teach_4_aux_separation_right : RationalBox := ⟨(79 / 10 : ℚ), (81 / 10 : ℚ)⟩
theorem Cteach_teach_4_aux_separation_right_valid : Cteach_teach_4_aux_separation_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_aux_separation_right]

def Cteach_teach_4_gain_below_cap_left : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_gain_below_cap_left_valid : Cteach_teach_4_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_gain_below_cap_left]

def Cteach_teach_4_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem Cteach_teach_4_gain_below_cap_right_valid : Cteach_teach_4_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_gain_below_cap_right]

def Cteach_teach_4_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_4_ready_at_input_left_valid : Cteach_teach_4_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_ready_at_input_left]

def Cteach_teach_4_ready_at_input_right : RationalBox := ⟨(13576812254842806520504835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1947827917820691561528836337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_ready_at_input_right_valid : Cteach_teach_4_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_ready_at_input_right]

def Cteach_teach_4_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_4_positive_derivative_coefficient_left_valid : Cteach_teach_4_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_positive_derivative_coefficient_left]

def Cteach_teach_4_positive_derivative_coefficient_right : RationalBox := ⟨(17100195167278017835342433406460031068337 / 10000000000000000000000000000000000000000 : ℚ), (1710053717460142522952896861667567200817 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_positive_derivative_coefficient_right_valid : Cteach_teach_4_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_positive_derivative_coefficient_right]

def Cteach_teach_4_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_4_fixed_flow_increases_left_valid : Cteach_teach_4_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_fixed_flow_increases_left]

def Cteach_teach_4_fixed_flow_increases_right : RationalBox := ⟨(2892484322797159284351892249906292051 / 4882812500000000000000000000000000000 : ℚ), (5925585890446356324109807091119032330893 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_fixed_flow_increases_right_valid : Cteach_teach_4_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_fixed_flow_increases_right]

def Cteach_teach_4_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_4_strong_crosses_by_one_left_valid : Cteach_teach_4_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_strong_crosses_by_one_left]

def Cteach_teach_4_strong_crosses_by_one_right : RationalBox := ⟨(13193487728408835122797745211969673693643 / 10000000000000000000000000000000000000000 : ℚ), (13193731600602117103246896313230441386899 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_strong_crosses_by_one_right_valid : Cteach_teach_4_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_strong_crosses_by_one_right]

def Cteach_teach_4_root_latency : RationalBox := ⟨(1893797 / 4194304 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_4_root_latency_valid : Cteach_teach_4_root_latency.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_root_latency]

def Cteach_teach_4_root_lower_left : RationalBox := ⟨(1249977481575347633857846140220403846377 / 1250000000000000000000000000000000000000 : ℚ), (999999985079980909682454510070632893983 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_root_lower_left_valid : Cteach_teach_4_root_lower_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_root_lower_left]

def Cteach_teach_4_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_4_root_lower_right_valid : Cteach_teach_4_root_lower_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_root_lower_right]

def Cteach_teach_4_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_4_root_upper_left_valid : Cteach_teach_4_root_upper_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_root_upper_left]

def Cteach_teach_4_root_upper_right : RationalBox := ⟨(400000052593892859040323911217376832147 / 400000000000000000000000000000000000000 : ℚ), (5000090658336815342734417808060050466907 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_root_upper_right_valid : Cteach_teach_4_root_upper_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_root_upper_right]

def Cteach_teach_4_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_MARK_before_fire_left_valid : Cteach_teach_4_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_MARK_before_fire_left]

def Cteach_teach_4_MARK_before_fire_right : RationalBox := ⟨(1893797 / 4194304 : ℚ), (1893797 / 4194304 : ℚ)⟩
theorem Cteach_teach_4_MARK_before_fire_right_valid : Cteach_teach_4_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_MARK_before_fire_right]

def Cteach_teach_4_fire_before_ERROR_left : RationalBox := ⟨(946931 / 2097152 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_4_fire_before_ERROR_left_valid : Cteach_teach_4_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_fire_before_ERROR_left]

def Cteach_teach_4_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_fire_before_ERROR_right_valid : Cteach_teach_4_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_fire_before_ERROR_right]

def Cteach_teach_4_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_ERROR_protected_left_valid : Cteach_teach_4_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_ERROR_protected_left]

def Cteach_teach_4_ERROR_protected_right : RationalBox := ⟨(8177172082179308438471163662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (65423032773080777463870164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_ERROR_protected_right_valid : Cteach_teach_4_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_ERROR_protected_right]

def Cteach_teach_4_arrival : RationalBox := ⟨(5378703773 / 10485760 : ℚ), (1344938171 / 2621440 : ℚ)⟩
theorem Cteach_teach_4_arrival_valid : Cteach_teach_4_arrival.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_arrival]

def Cteach_teach_4_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem Cteach_teach_4_b_after_valid : Cteach_teach_4_b_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_b_after]

def Cteach_teach_4_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_4_gain_after_valid : Cteach_teach_4_gain_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_gain_after]

def Cteach_teach_4_emission : RationalBox := ⟨(10766876531 / 20971520 : ℚ), (5384487339 / 10485760 : ℚ)⟩
theorem Cteach_teach_4_emission_valid : Cteach_teach_4_emission.Valid := by norm_num [RationalBox.Valid, Cteach_teach_4_emission]

def B_teach_5_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_aux_separation_left_valid : B_teach_5_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_aux_separation_left]

def B_teach_5_aux_separation_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem B_teach_5_aux_separation_right_valid : B_teach_5_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_aux_separation_right]

def B_teach_5_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_gain_below_cap_left_valid : B_teach_5_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_gain_below_cap_left]

def B_teach_5_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_teach_5_gain_below_cap_right_valid : B_teach_5_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_gain_below_cap_right]

def B_teach_5_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_5_ready_at_input_left_valid : B_teach_5_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_ready_at_input_left]

def B_teach_5_ready_at_input_right : RationalBox := ⟨(12560167776998568239254835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1570767921692609286138211337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_ready_at_input_right_valid : B_teach_5_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_ready_at_input_right]

def B_teach_5_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_5_positive_derivative_coefficient_left_valid : B_teach_5_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_positive_derivative_coefficient_left]

def B_teach_5_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_positive_derivative_coefficient_right_valid : B_teach_5_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_positive_derivative_coefficient_right]

def B_teach_5_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_5_fixed_flow_increases_left_valid : B_teach_5_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_fixed_flow_increases_left]

def B_teach_5_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_fixed_flow_increases_right_valid : B_teach_5_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_fixed_flow_increases_right]

def B_teach_5_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_5_strong_crosses_by_one_left_valid : B_teach_5_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_strong_crosses_by_one_left]

def B_teach_5_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_strong_crosses_by_one_right_valid : B_teach_5_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_strong_crosses_by_one_right]

def B_teach_5_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_5_root_latency_valid : B_teach_5_root_latency.Valid := by norm_num [RationalBox.Valid, B_teach_5_root_latency]

def B_teach_5_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_root_lower_left_valid : B_teach_5_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_root_lower_left]

def B_teach_5_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_5_root_lower_right_valid : B_teach_5_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_root_lower_right]

def B_teach_5_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_5_root_upper_left_valid : B_teach_5_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_root_upper_left]

def B_teach_5_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_root_upper_right_valid : B_teach_5_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_root_upper_right]

def B_teach_5_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_MARK_before_fire_left_valid : B_teach_5_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_MARK_before_fire_left]

def B_teach_5_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_teach_5_MARK_before_fire_right_valid : B_teach_5_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_MARK_before_fire_right]

def B_teach_5_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_5_fire_before_ERROR_left_valid : B_teach_5_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_fire_before_ERROR_left]

def B_teach_5_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_fire_before_ERROR_right_valid : B_teach_5_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_fire_before_ERROR_right]

def B_teach_5_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_ERROR_protected_left_valid : B_teach_5_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_teach_5_ERROR_protected_left]

def B_teach_5_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_ERROR_protected_right_valid : B_teach_5_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_teach_5_ERROR_protected_right]

def B_teach_5_arrival : RationalBox := ⟨(520 / 1 : ℚ), (520 / 1 : ℚ)⟩
theorem B_teach_5_arrival_valid : B_teach_5_arrival.Valid := by norm_num [RationalBox.Valid, B_teach_5_arrival]

def B_teach_5_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_teach_5_b_after_valid : B_teach_5_b_after.Valid := by norm_num [RationalBox.Valid, B_teach_5_b_after]

def B_teach_5_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_5_gain_after_valid : B_teach_5_gain_after.Valid := by norm_num [RationalBox.Valid, B_teach_5_gain_after]

def B_teach_5_emission : RationalBox := ⟨(1091888825 / 2097152 : ℚ), (272972223 / 524288 : ℚ)⟩
theorem B_teach_5_emission_valid : B_teach_5_emission.Valid := by norm_num [RationalBox.Valid, B_teach_5_emission]

def Cteach_teach_5_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_aux_separation_left_valid : Cteach_teach_5_aux_separation_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_aux_separation_left]

def Cteach_teach_5_aux_separation_right : RationalBox := ⟨(79 / 10 : ℚ), (81 / 10 : ℚ)⟩
theorem Cteach_teach_5_aux_separation_right_valid : Cteach_teach_5_aux_separation_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_aux_separation_right]

def Cteach_teach_5_gain_below_cap_left : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_gain_below_cap_left_valid : Cteach_teach_5_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_gain_below_cap_left]

def Cteach_teach_5_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem Cteach_teach_5_gain_below_cap_right_valid : Cteach_teach_5_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_gain_below_cap_right]

def Cteach_teach_5_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_5_ready_at_input_left_valid : Cteach_teach_5_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_ready_at_input_left]

def Cteach_teach_5_ready_at_input_right : RationalBox := ⟨(13576812254842806520504835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1947827917820691561528836337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_ready_at_input_right_valid : Cteach_teach_5_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_ready_at_input_right]

def Cteach_teach_5_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_5_positive_derivative_coefficient_left_valid : Cteach_teach_5_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_positive_derivative_coefficient_left]

def Cteach_teach_5_positive_derivative_coefficient_right : RationalBox := ⟨(17100195167278017835342433406460031068337 / 10000000000000000000000000000000000000000 : ℚ), (1710053717460142522952896861667567200817 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_positive_derivative_coefficient_right_valid : Cteach_teach_5_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_positive_derivative_coefficient_right]

def Cteach_teach_5_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_5_fixed_flow_increases_left_valid : Cteach_teach_5_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_fixed_flow_increases_left]

def Cteach_teach_5_fixed_flow_increases_right : RationalBox := ⟨(2892484322797159284351892249906292051 / 4882812500000000000000000000000000000 : ℚ), (5925585890446356324109807091119032330893 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_fixed_flow_increases_right_valid : Cteach_teach_5_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_fixed_flow_increases_right]

def Cteach_teach_5_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_5_strong_crosses_by_one_left_valid : Cteach_teach_5_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_strong_crosses_by_one_left]

def Cteach_teach_5_strong_crosses_by_one_right : RationalBox := ⟨(13193487728408835122797745211969673693643 / 10000000000000000000000000000000000000000 : ℚ), (13193731600602117103246896313230441386899 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_strong_crosses_by_one_right_valid : Cteach_teach_5_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_strong_crosses_by_one_right]

def Cteach_teach_5_root_latency : RationalBox := ⟨(1893797 / 4194304 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_5_root_latency_valid : Cteach_teach_5_root_latency.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_root_latency]

def Cteach_teach_5_root_lower_left : RationalBox := ⟨(1249977481575347633857846140220403846377 / 1250000000000000000000000000000000000000 : ℚ), (999999985079980909682454510070632893983 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_root_lower_left_valid : Cteach_teach_5_root_lower_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_root_lower_left]

def Cteach_teach_5_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_5_root_lower_right_valid : Cteach_teach_5_root_lower_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_root_lower_right]

def Cteach_teach_5_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_5_root_upper_left_valid : Cteach_teach_5_root_upper_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_root_upper_left]

def Cteach_teach_5_root_upper_right : RationalBox := ⟨(400000052593892859040323911217376832147 / 400000000000000000000000000000000000000 : ℚ), (5000090658336815342734417808060050466907 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_root_upper_right_valid : Cteach_teach_5_root_upper_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_root_upper_right]

def Cteach_teach_5_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_MARK_before_fire_left_valid : Cteach_teach_5_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_MARK_before_fire_left]

def Cteach_teach_5_MARK_before_fire_right : RationalBox := ⟨(1893797 / 4194304 : ℚ), (1893797 / 4194304 : ℚ)⟩
theorem Cteach_teach_5_MARK_before_fire_right_valid : Cteach_teach_5_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_MARK_before_fire_right]

def Cteach_teach_5_fire_before_ERROR_left : RationalBox := ⟨(946931 / 2097152 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_5_fire_before_ERROR_left_valid : Cteach_teach_5_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_fire_before_ERROR_left]

def Cteach_teach_5_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_fire_before_ERROR_right_valid : Cteach_teach_5_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_fire_before_ERROR_right]

def Cteach_teach_5_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_ERROR_protected_left_valid : Cteach_teach_5_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_ERROR_protected_left]

def Cteach_teach_5_ERROR_protected_right : RationalBox := ⟨(8177172082179308438471163662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (65423032773080777463870164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_ERROR_protected_right_valid : Cteach_teach_5_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_ERROR_protected_right]

def Cteach_teach_5_arrival : RationalBox := ⟨(5462589853 / 10485760 : ℚ), (1365909691 / 2621440 : ℚ)⟩
theorem Cteach_teach_5_arrival_valid : Cteach_teach_5_arrival.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_arrival]

def Cteach_teach_5_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem Cteach_teach_5_b_after_valid : Cteach_teach_5_b_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_b_after]

def Cteach_teach_5_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_5_gain_after_valid : Cteach_teach_5_gain_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_gain_after]

def Cteach_teach_5_emission : RationalBox := ⟨(10934648691 / 20971520 : ℚ), (5468373419 / 10485760 : ℚ)⟩
theorem Cteach_teach_5_emission_valid : Cteach_teach_5_emission.Valid := by norm_num [RationalBox.Valid, Cteach_teach_5_emission]

def B_teach_6_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_6_aux_separation_left_valid : B_teach_6_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_teach_6_aux_separation_left]

def B_teach_6_aux_separation_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem B_teach_6_aux_separation_right_valid : B_teach_6_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_teach_6_aux_separation_right]

def B_teach_6_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_6_gain_below_cap_left_valid : B_teach_6_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_teach_6_gain_below_cap_left]

def B_teach_6_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_teach_6_gain_below_cap_right_valid : B_teach_6_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_teach_6_gain_below_cap_right]

def Bounds01Valid : Prop :=
  B_teach_3_positive_derivative_coefficient_left.Valid ∧
  B_teach_3_positive_derivative_coefficient_right.Valid ∧
  B_teach_3_fixed_flow_increases_left.Valid ∧
  B_teach_3_fixed_flow_increases_right.Valid ∧
  B_teach_3_strong_crosses_by_one_left.Valid ∧
  B_teach_3_strong_crosses_by_one_right.Valid ∧
  B_teach_3_root_latency.Valid ∧
  B_teach_3_root_lower_left.Valid ∧
  B_teach_3_root_lower_right.Valid ∧
  B_teach_3_root_upper_left.Valid ∧
  B_teach_3_root_upper_right.Valid ∧
  B_teach_3_MARK_before_fire_left.Valid ∧
  B_teach_3_MARK_before_fire_right.Valid ∧
  B_teach_3_fire_before_ERROR_left.Valid ∧
  B_teach_3_fire_before_ERROR_right.Valid ∧
  B_teach_3_ERROR_protected_left.Valid ∧
  B_teach_3_ERROR_protected_right.Valid ∧
  B_teach_3_arrival.Valid ∧
  B_teach_3_b_after.Valid ∧
  B_teach_3_gain_after.Valid ∧
  B_teach_3_emission.Valid ∧
  Cteach_teach_3_aux_separation_left.Valid ∧
  Cteach_teach_3_aux_separation_right.Valid ∧
  Cteach_teach_3_gain_below_cap_left.Valid ∧
  Cteach_teach_3_gain_below_cap_right.Valid ∧
  Cteach_teach_3_ready_at_input_left.Valid ∧
  Cteach_teach_3_ready_at_input_right.Valid ∧
  Cteach_teach_3_positive_derivative_coefficient_left.Valid ∧
  Cteach_teach_3_positive_derivative_coefficient_right.Valid ∧
  Cteach_teach_3_fixed_flow_increases_left.Valid ∧
  Cteach_teach_3_fixed_flow_increases_right.Valid ∧
  Cteach_teach_3_strong_crosses_by_one_left.Valid ∧
  Cteach_teach_3_strong_crosses_by_one_right.Valid ∧
  Cteach_teach_3_root_latency.Valid ∧
  Cteach_teach_3_root_lower_left.Valid ∧
  Cteach_teach_3_root_lower_right.Valid ∧
  Cteach_teach_3_root_upper_left.Valid ∧
  Cteach_teach_3_root_upper_right.Valid ∧
  Cteach_teach_3_MARK_before_fire_left.Valid ∧
  Cteach_teach_3_MARK_before_fire_right.Valid ∧
  Cteach_teach_3_fire_before_ERROR_left.Valid ∧
  Cteach_teach_3_fire_before_ERROR_right.Valid ∧
  Cteach_teach_3_ERROR_protected_left.Valid ∧
  Cteach_teach_3_ERROR_protected_right.Valid ∧
  Cteach_teach_3_arrival.Valid ∧
  Cteach_teach_3_b_after.Valid ∧
  Cteach_teach_3_gain_after.Valid ∧
  Cteach_teach_3_emission.Valid ∧
  B_teach_4_aux_separation_left.Valid ∧
  B_teach_4_aux_separation_right.Valid ∧
  B_teach_4_gain_below_cap_left.Valid ∧
  B_teach_4_gain_below_cap_right.Valid ∧
  B_teach_4_ready_at_input_left.Valid ∧
  B_teach_4_ready_at_input_right.Valid ∧
  B_teach_4_positive_derivative_coefficient_left.Valid ∧
  B_teach_4_positive_derivative_coefficient_right.Valid ∧
  B_teach_4_fixed_flow_increases_left.Valid ∧
  B_teach_4_fixed_flow_increases_right.Valid ∧
  B_teach_4_strong_crosses_by_one_left.Valid ∧
  B_teach_4_strong_crosses_by_one_right.Valid ∧
  B_teach_4_root_latency.Valid ∧
  B_teach_4_root_lower_left.Valid ∧
  B_teach_4_root_lower_right.Valid ∧
  B_teach_4_root_upper_left.Valid ∧
  B_teach_4_root_upper_right.Valid ∧
  B_teach_4_MARK_before_fire_left.Valid ∧
  B_teach_4_MARK_before_fire_right.Valid ∧
  B_teach_4_fire_before_ERROR_left.Valid ∧
  B_teach_4_fire_before_ERROR_right.Valid ∧
  B_teach_4_ERROR_protected_left.Valid ∧
  B_teach_4_ERROR_protected_right.Valid ∧
  B_teach_4_arrival.Valid ∧
  B_teach_4_b_after.Valid ∧
  B_teach_4_gain_after.Valid ∧
  B_teach_4_emission.Valid ∧
  Cteach_teach_4_aux_separation_left.Valid ∧
  Cteach_teach_4_aux_separation_right.Valid ∧
  Cteach_teach_4_gain_below_cap_left.Valid ∧
  Cteach_teach_4_gain_below_cap_right.Valid ∧
  Cteach_teach_4_ready_at_input_left.Valid ∧
  Cteach_teach_4_ready_at_input_right.Valid ∧
  Cteach_teach_4_positive_derivative_coefficient_left.Valid ∧
  Cteach_teach_4_positive_derivative_coefficient_right.Valid ∧
  Cteach_teach_4_fixed_flow_increases_left.Valid ∧
  Cteach_teach_4_fixed_flow_increases_right.Valid ∧
  Cteach_teach_4_strong_crosses_by_one_left.Valid ∧
  Cteach_teach_4_strong_crosses_by_one_right.Valid ∧
  Cteach_teach_4_root_latency.Valid ∧
  Cteach_teach_4_root_lower_left.Valid ∧
  Cteach_teach_4_root_lower_right.Valid ∧
  Cteach_teach_4_root_upper_left.Valid ∧
  Cteach_teach_4_root_upper_right.Valid ∧
  Cteach_teach_4_MARK_before_fire_left.Valid ∧
  Cteach_teach_4_MARK_before_fire_right.Valid ∧
  Cteach_teach_4_fire_before_ERROR_left.Valid ∧
  Cteach_teach_4_fire_before_ERROR_right.Valid ∧
  Cteach_teach_4_ERROR_protected_left.Valid ∧
  Cteach_teach_4_ERROR_protected_right.Valid ∧
  Cteach_teach_4_arrival.Valid ∧
  Cteach_teach_4_b_after.Valid ∧
  Cteach_teach_4_gain_after.Valid ∧
  Cteach_teach_4_emission.Valid ∧
  B_teach_5_aux_separation_left.Valid ∧
  B_teach_5_aux_separation_right.Valid ∧
  B_teach_5_gain_below_cap_left.Valid ∧
  B_teach_5_gain_below_cap_right.Valid ∧
  B_teach_5_ready_at_input_left.Valid ∧
  B_teach_5_ready_at_input_right.Valid ∧
  B_teach_5_positive_derivative_coefficient_left.Valid ∧
  B_teach_5_positive_derivative_coefficient_right.Valid ∧
  B_teach_5_fixed_flow_increases_left.Valid ∧
  B_teach_5_fixed_flow_increases_right.Valid ∧
  B_teach_5_strong_crosses_by_one_left.Valid ∧
  B_teach_5_strong_crosses_by_one_right.Valid ∧
  B_teach_5_root_latency.Valid ∧
  B_teach_5_root_lower_left.Valid ∧
  B_teach_5_root_lower_right.Valid ∧
  B_teach_5_root_upper_left.Valid ∧
  B_teach_5_root_upper_right.Valid ∧
  B_teach_5_MARK_before_fire_left.Valid ∧
  B_teach_5_MARK_before_fire_right.Valid ∧
  B_teach_5_fire_before_ERROR_left.Valid ∧
  B_teach_5_fire_before_ERROR_right.Valid ∧
  B_teach_5_ERROR_protected_left.Valid ∧
  B_teach_5_ERROR_protected_right.Valid ∧
  B_teach_5_arrival.Valid ∧
  B_teach_5_b_after.Valid ∧
  B_teach_5_gain_after.Valid ∧
  B_teach_5_emission.Valid ∧
  Cteach_teach_5_aux_separation_left.Valid ∧
  Cteach_teach_5_aux_separation_right.Valid ∧
  Cteach_teach_5_gain_below_cap_left.Valid ∧
  Cteach_teach_5_gain_below_cap_right.Valid ∧
  Cteach_teach_5_ready_at_input_left.Valid ∧
  Cteach_teach_5_ready_at_input_right.Valid ∧
  Cteach_teach_5_positive_derivative_coefficient_left.Valid ∧
  Cteach_teach_5_positive_derivative_coefficient_right.Valid ∧
  Cteach_teach_5_fixed_flow_increases_left.Valid ∧
  Cteach_teach_5_fixed_flow_increases_right.Valid ∧
  Cteach_teach_5_strong_crosses_by_one_left.Valid ∧
  Cteach_teach_5_strong_crosses_by_one_right.Valid ∧
  Cteach_teach_5_root_latency.Valid ∧
  Cteach_teach_5_root_lower_left.Valid ∧
  Cteach_teach_5_root_lower_right.Valid ∧
  Cteach_teach_5_root_upper_left.Valid ∧
  Cteach_teach_5_root_upper_right.Valid ∧
  Cteach_teach_5_MARK_before_fire_left.Valid ∧
  Cteach_teach_5_MARK_before_fire_right.Valid ∧
  Cteach_teach_5_fire_before_ERROR_left.Valid ∧
  Cteach_teach_5_fire_before_ERROR_right.Valid ∧
  Cteach_teach_5_ERROR_protected_left.Valid ∧
  Cteach_teach_5_ERROR_protected_right.Valid ∧
  Cteach_teach_5_arrival.Valid ∧
  Cteach_teach_5_b_after.Valid ∧
  Cteach_teach_5_gain_after.Valid ∧
  Cteach_teach_5_emission.Valid ∧
  B_teach_6_aux_separation_left.Valid ∧
  B_teach_6_aux_separation_right.Valid ∧
  B_teach_6_gain_below_cap_left.Valid ∧
  B_teach_6_gain_below_cap_right.Valid
theorem Bounds01Valid_verified : Bounds01Valid := by
  exact ⟨B_teach_3_positive_derivative_coefficient_left_valid, B_teach_3_positive_derivative_coefficient_right_valid, B_teach_3_fixed_flow_increases_left_valid, B_teach_3_fixed_flow_increases_right_valid, B_teach_3_strong_crosses_by_one_left_valid, B_teach_3_strong_crosses_by_one_right_valid, B_teach_3_root_latency_valid, B_teach_3_root_lower_left_valid, B_teach_3_root_lower_right_valid, B_teach_3_root_upper_left_valid, B_teach_3_root_upper_right_valid, B_teach_3_MARK_before_fire_left_valid, B_teach_3_MARK_before_fire_right_valid, B_teach_3_fire_before_ERROR_left_valid, B_teach_3_fire_before_ERROR_right_valid, B_teach_3_ERROR_protected_left_valid, B_teach_3_ERROR_protected_right_valid, B_teach_3_arrival_valid, B_teach_3_b_after_valid, B_teach_3_gain_after_valid, B_teach_3_emission_valid, Cteach_teach_3_aux_separation_left_valid, Cteach_teach_3_aux_separation_right_valid, Cteach_teach_3_gain_below_cap_left_valid, Cteach_teach_3_gain_below_cap_right_valid, Cteach_teach_3_ready_at_input_left_valid, Cteach_teach_3_ready_at_input_right_valid, Cteach_teach_3_positive_derivative_coefficient_left_valid, Cteach_teach_3_positive_derivative_coefficient_right_valid, Cteach_teach_3_fixed_flow_increases_left_valid, Cteach_teach_3_fixed_flow_increases_right_valid, Cteach_teach_3_strong_crosses_by_one_left_valid, Cteach_teach_3_strong_crosses_by_one_right_valid, Cteach_teach_3_root_latency_valid, Cteach_teach_3_root_lower_left_valid, Cteach_teach_3_root_lower_right_valid, Cteach_teach_3_root_upper_left_valid, Cteach_teach_3_root_upper_right_valid, Cteach_teach_3_MARK_before_fire_left_valid, Cteach_teach_3_MARK_before_fire_right_valid, Cteach_teach_3_fire_before_ERROR_left_valid, Cteach_teach_3_fire_before_ERROR_right_valid, Cteach_teach_3_ERROR_protected_left_valid, Cteach_teach_3_ERROR_protected_right_valid, Cteach_teach_3_arrival_valid, Cteach_teach_3_b_after_valid, Cteach_teach_3_gain_after_valid, Cteach_teach_3_emission_valid, B_teach_4_aux_separation_left_valid, B_teach_4_aux_separation_right_valid, B_teach_4_gain_below_cap_left_valid, B_teach_4_gain_below_cap_right_valid, B_teach_4_ready_at_input_left_valid, B_teach_4_ready_at_input_right_valid, B_teach_4_positive_derivative_coefficient_left_valid, B_teach_4_positive_derivative_coefficient_right_valid, B_teach_4_fixed_flow_increases_left_valid, B_teach_4_fixed_flow_increases_right_valid, B_teach_4_strong_crosses_by_one_left_valid, B_teach_4_strong_crosses_by_one_right_valid, B_teach_4_root_latency_valid, B_teach_4_root_lower_left_valid, B_teach_4_root_lower_right_valid, B_teach_4_root_upper_left_valid, B_teach_4_root_upper_right_valid, B_teach_4_MARK_before_fire_left_valid, B_teach_4_MARK_before_fire_right_valid, B_teach_4_fire_before_ERROR_left_valid, B_teach_4_fire_before_ERROR_right_valid, B_teach_4_ERROR_protected_left_valid, B_teach_4_ERROR_protected_right_valid, B_teach_4_arrival_valid, B_teach_4_b_after_valid, B_teach_4_gain_after_valid, B_teach_4_emission_valid, Cteach_teach_4_aux_separation_left_valid, Cteach_teach_4_aux_separation_right_valid, Cteach_teach_4_gain_below_cap_left_valid, Cteach_teach_4_gain_below_cap_right_valid, Cteach_teach_4_ready_at_input_left_valid, Cteach_teach_4_ready_at_input_right_valid, Cteach_teach_4_positive_derivative_coefficient_left_valid, Cteach_teach_4_positive_derivative_coefficient_right_valid, Cteach_teach_4_fixed_flow_increases_left_valid, Cteach_teach_4_fixed_flow_increases_right_valid, Cteach_teach_4_strong_crosses_by_one_left_valid, Cteach_teach_4_strong_crosses_by_one_right_valid, Cteach_teach_4_root_latency_valid, Cteach_teach_4_root_lower_left_valid, Cteach_teach_4_root_lower_right_valid, Cteach_teach_4_root_upper_left_valid, Cteach_teach_4_root_upper_right_valid, Cteach_teach_4_MARK_before_fire_left_valid, Cteach_teach_4_MARK_before_fire_right_valid, Cteach_teach_4_fire_before_ERROR_left_valid, Cteach_teach_4_fire_before_ERROR_right_valid, Cteach_teach_4_ERROR_protected_left_valid, Cteach_teach_4_ERROR_protected_right_valid, Cteach_teach_4_arrival_valid, Cteach_teach_4_b_after_valid, Cteach_teach_4_gain_after_valid, Cteach_teach_4_emission_valid, B_teach_5_aux_separation_left_valid, B_teach_5_aux_separation_right_valid, B_teach_5_gain_below_cap_left_valid, B_teach_5_gain_below_cap_right_valid, B_teach_5_ready_at_input_left_valid, B_teach_5_ready_at_input_right_valid, B_teach_5_positive_derivative_coefficient_left_valid, B_teach_5_positive_derivative_coefficient_right_valid, B_teach_5_fixed_flow_increases_left_valid, B_teach_5_fixed_flow_increases_right_valid, B_teach_5_strong_crosses_by_one_left_valid, B_teach_5_strong_crosses_by_one_right_valid, B_teach_5_root_latency_valid, B_teach_5_root_lower_left_valid, B_teach_5_root_lower_right_valid, B_teach_5_root_upper_left_valid, B_teach_5_root_upper_right_valid, B_teach_5_MARK_before_fire_left_valid, B_teach_5_MARK_before_fire_right_valid, B_teach_5_fire_before_ERROR_left_valid, B_teach_5_fire_before_ERROR_right_valid, B_teach_5_ERROR_protected_left_valid, B_teach_5_ERROR_protected_right_valid, B_teach_5_arrival_valid, B_teach_5_b_after_valid, B_teach_5_gain_after_valid, B_teach_5_emission_valid, Cteach_teach_5_aux_separation_left_valid, Cteach_teach_5_aux_separation_right_valid, Cteach_teach_5_gain_below_cap_left_valid, Cteach_teach_5_gain_below_cap_right_valid, Cteach_teach_5_ready_at_input_left_valid, Cteach_teach_5_ready_at_input_right_valid, Cteach_teach_5_positive_derivative_coefficient_left_valid, Cteach_teach_5_positive_derivative_coefficient_right_valid, Cteach_teach_5_fixed_flow_increases_left_valid, Cteach_teach_5_fixed_flow_increases_right_valid, Cteach_teach_5_strong_crosses_by_one_left_valid, Cteach_teach_5_strong_crosses_by_one_right_valid, Cteach_teach_5_root_latency_valid, Cteach_teach_5_root_lower_left_valid, Cteach_teach_5_root_lower_right_valid, Cteach_teach_5_root_upper_left_valid, Cteach_teach_5_root_upper_right_valid, Cteach_teach_5_MARK_before_fire_left_valid, Cteach_teach_5_MARK_before_fire_right_valid, Cteach_teach_5_fire_before_ERROR_left_valid, Cteach_teach_5_fire_before_ERROR_right_valid, Cteach_teach_5_ERROR_protected_left_valid, Cteach_teach_5_ERROR_protected_right_valid, Cteach_teach_5_arrival_valid, Cteach_teach_5_b_after_valid, Cteach_teach_5_gain_after_valid, Cteach_teach_5_emission_valid, B_teach_6_aux_separation_left_valid, B_teach_6_aux_separation_right_valid, B_teach_6_gain_below_cap_left_valid, B_teach_6_gain_below_cap_right_valid⟩

end KernelR.Certificates.Cadence010
