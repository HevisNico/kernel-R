import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence003
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def Cteach_teach_14_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_14_gain_after_valid : Cteach_teach_14_gain_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_14_gain_after]

def Cteach_teach_14_emission : RationalBox := ⟨(12444598131 / 20971520 : ℚ), (6223348139 / 10485760 : ℚ)⟩
theorem Cteach_teach_14_emission_valid : Cteach_teach_14_emission.Valid := by norm_num [RationalBox.Valid, Cteach_teach_14_emission]

def B_teach_15_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_aux_separation_left_valid : B_teach_15_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_aux_separation_left]

def B_teach_15_aux_separation_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem B_teach_15_aux_separation_right_valid : B_teach_15_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_aux_separation_right]

def B_teach_15_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_gain_below_cap_left_valid : B_teach_15_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_gain_below_cap_left]

def B_teach_15_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_teach_15_gain_below_cap_right_valid : B_teach_15_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_gain_below_cap_right]

def B_teach_15_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_15_ready_at_input_left_valid : B_teach_15_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_ready_at_input_left]

def B_teach_15_ready_at_input_right : RationalBox := ⟨(12560167776998568239254835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1570767921692609286138211337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_ready_at_input_right_valid : B_teach_15_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_ready_at_input_right]

def B_teach_15_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_15_positive_derivative_coefficient_left_valid : B_teach_15_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_positive_derivative_coefficient_left]

def B_teach_15_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_positive_derivative_coefficient_right_valid : B_teach_15_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_positive_derivative_coefficient_right]

def B_teach_15_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_teach_15_fixed_flow_increases_left_valid : B_teach_15_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_fixed_flow_increases_left]

def B_teach_15_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_fixed_flow_increases_right_valid : B_teach_15_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_fixed_flow_increases_right]

def B_teach_15_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_15_strong_crosses_by_one_left_valid : B_teach_15_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_strong_crosses_by_one_left]

def B_teach_15_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_strong_crosses_by_one_right_valid : B_teach_15_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_strong_crosses_by_one_right]

def B_teach_15_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_15_root_latency_valid : B_teach_15_root_latency.Valid := by norm_num [RationalBox.Valid, B_teach_15_root_latency]

def B_teach_15_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_root_lower_left_valid : B_teach_15_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_root_lower_left]

def B_teach_15_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_15_root_lower_right_valid : B_teach_15_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_root_lower_right]

def B_teach_15_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_teach_15_root_upper_left_valid : B_teach_15_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_root_upper_left]

def B_teach_15_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_root_upper_right_valid : B_teach_15_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_root_upper_right]

def B_teach_15_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_MARK_before_fire_left_valid : B_teach_15_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_MARK_before_fire_left]

def B_teach_15_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_teach_15_MARK_before_fire_right_valid : B_teach_15_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_MARK_before_fire_right]

def B_teach_15_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_teach_15_fire_before_ERROR_left_valid : B_teach_15_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_fire_before_ERROR_left]

def B_teach_15_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_fire_before_ERROR_right_valid : B_teach_15_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_fire_before_ERROR_right]

def B_teach_15_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_ERROR_protected_left_valid : B_teach_15_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_teach_15_ERROR_protected_left]

def B_teach_15_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_ERROR_protected_right_valid : B_teach_15_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_teach_15_ERROR_protected_right]

def B_teach_15_arrival : RationalBox := ⟨(600 / 1 : ℚ), (600 / 1 : ℚ)⟩
theorem B_teach_15_arrival_valid : B_teach_15_arrival.Valid := by norm_num [RationalBox.Valid, B_teach_15_arrival]

def B_teach_15_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_teach_15_b_after_valid : B_teach_15_b_after.Valid := by norm_num [RationalBox.Valid, B_teach_15_b_after]

def B_teach_15_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_teach_15_gain_after_valid : B_teach_15_gain_after.Valid := by norm_num [RationalBox.Valid, B_teach_15_gain_after]

def B_teach_15_emission : RationalBox := ⟨(1259660985 / 2097152 : ℚ), (314915263 / 524288 : ℚ)⟩
theorem B_teach_15_emission_valid : B_teach_15_emission.Valid := by norm_num [RationalBox.Valid, B_teach_15_emission]

def Cteach_teach_15_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_aux_separation_left_valid : Cteach_teach_15_aux_separation_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_aux_separation_left]

def Cteach_teach_15_aux_separation_right : RationalBox := ⟨(79 / 10 : ℚ), (81 / 10 : ℚ)⟩
theorem Cteach_teach_15_aux_separation_right_valid : Cteach_teach_15_aux_separation_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_aux_separation_right]

def Cteach_teach_15_gain_below_cap_left : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_gain_below_cap_left_valid : Cteach_teach_15_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_gain_below_cap_left]

def Cteach_teach_15_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem Cteach_teach_15_gain_below_cap_right_valid : Cteach_teach_15_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_gain_below_cap_right]

def Cteach_teach_15_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_15_ready_at_input_left_valid : Cteach_teach_15_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_ready_at_input_left]

def Cteach_teach_15_ready_at_input_right : RationalBox := ⟨(13576812254842806520504835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1947827917820691561528836337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_ready_at_input_right_valid : Cteach_teach_15_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_ready_at_input_right]

def Cteach_teach_15_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_15_positive_derivative_coefficient_left_valid : Cteach_teach_15_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_positive_derivative_coefficient_left]

def Cteach_teach_15_positive_derivative_coefficient_right : RationalBox := ⟨(17100195167278017835342433406460031068337 / 10000000000000000000000000000000000000000 : ℚ), (1710053717460142522952896861667567200817 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_positive_derivative_coefficient_right_valid : Cteach_teach_15_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_positive_derivative_coefficient_right]

def Cteach_teach_15_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem Cteach_teach_15_fixed_flow_increases_left_valid : Cteach_teach_15_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_fixed_flow_increases_left]

def Cteach_teach_15_fixed_flow_increases_right : RationalBox := ⟨(2892484322797159284351892249906292051 / 4882812500000000000000000000000000000 : ℚ), (5925585890446356324109807091119032330893 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_fixed_flow_increases_right_valid : Cteach_teach_15_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_fixed_flow_increases_right]

def Cteach_teach_15_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_15_strong_crosses_by_one_left_valid : Cteach_teach_15_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_strong_crosses_by_one_left]

def Cteach_teach_15_strong_crosses_by_one_right : RationalBox := ⟨(13193487728408835122797745211969673693643 / 10000000000000000000000000000000000000000 : ℚ), (13193731600602117103246896313230441386899 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_strong_crosses_by_one_right_valid : Cteach_teach_15_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_strong_crosses_by_one_right]

def Cteach_teach_15_root_latency : RationalBox := ⟨(1893797 / 4194304 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_15_root_latency_valid : Cteach_teach_15_root_latency.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_root_latency]

def Cteach_teach_15_root_lower_left : RationalBox := ⟨(1249977481575347633857846140220403846377 / 1250000000000000000000000000000000000000 : ℚ), (999999985079980909682454510070632893983 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_root_lower_left_valid : Cteach_teach_15_root_lower_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_root_lower_left]

def Cteach_teach_15_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_15_root_lower_right_valid : Cteach_teach_15_root_lower_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_root_lower_right]

def Cteach_teach_15_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem Cteach_teach_15_root_upper_left_valid : Cteach_teach_15_root_upper_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_root_upper_left]

def Cteach_teach_15_root_upper_right : RationalBox := ⟨(400000052593892859040323911217376832147 / 400000000000000000000000000000000000000 : ℚ), (5000090658336815342734417808060050466907 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_root_upper_right_valid : Cteach_teach_15_root_upper_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_root_upper_right]

def Cteach_teach_15_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_MARK_before_fire_left_valid : Cteach_teach_15_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_MARK_before_fire_left]

def Cteach_teach_15_MARK_before_fire_right : RationalBox := ⟨(1893797 / 4194304 : ℚ), (1893797 / 4194304 : ℚ)⟩
theorem Cteach_teach_15_MARK_before_fire_right_valid : Cteach_teach_15_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_MARK_before_fire_right]

def Cteach_teach_15_fire_before_ERROR_left : RationalBox := ⟨(946931 / 2097152 : ℚ), (946931 / 2097152 : ℚ)⟩
theorem Cteach_teach_15_fire_before_ERROR_left_valid : Cteach_teach_15_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_fire_before_ERROR_left]

def Cteach_teach_15_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_fire_before_ERROR_right_valid : Cteach_teach_15_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_fire_before_ERROR_right]

def Cteach_teach_15_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_ERROR_protected_left_valid : Cteach_teach_15_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_ERROR_protected_left]

def Cteach_teach_15_ERROR_protected_right : RationalBox := ⟨(8177172082179308438471163662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (65423032773080777463870164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_ERROR_protected_right_valid : Cteach_teach_15_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_ERROR_protected_right]

def Cteach_teach_15_arrival : RationalBox := ⟨(6301450653 / 10485760 : ℚ), (1575624891 / 2621440 : ℚ)⟩
theorem Cteach_teach_15_arrival_valid : Cteach_teach_15_arrival.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_arrival]

def Cteach_teach_15_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem Cteach_teach_15_b_after_valid : Cteach_teach_15_b_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_b_after]

def Cteach_teach_15_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 500000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_teach_15_gain_after_valid : Cteach_teach_15_gain_after.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_gain_after]

def Cteach_teach_15_emission : RationalBox := ⟨(12612370291 / 20971520 : ℚ), (6307234219 / 10485760 : ℚ)⟩
theorem Cteach_teach_15_emission_valid : Cteach_teach_15_emission.Valid := by norm_num [RationalBox.Valid, Cteach_teach_15_emission]

def B_quiescent_before_fast_cut_left : RationalBox := ⟨(758429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (6067439832223001431760745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_quiescent_before_fast_cut_left_valid : B_quiescent_before_fast_cut_left.Valid := by norm_num [RationalBox.Valid, B_quiescent_before_fast_cut_left]

def B_quiescent_before_fast_cut_right : RationalBox := ⟨(6399 / 10 : ℚ), (6399 / 10 : ℚ)⟩
theorem B_quiescent_before_fast_cut_right_valid : B_quiescent_before_fast_cut_right.Valid := by norm_num [RationalBox.Valid, B_quiescent_before_fast_cut_right]

def Cteach_quiescent_before_fast_cut_left : RationalBox := ⟨(759368627565615892911127413662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (6075955151093545865354495164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem Cteach_quiescent_before_fast_cut_left_valid : Cteach_quiescent_before_fast_cut_left.Valid := by norm_num [RationalBox.Valid, Cteach_quiescent_before_fast_cut_left]

def Cteach_quiescent_before_fast_cut_right : RationalBox := ⟨(6399 / 10 : ℚ), (6399 / 10 : ℚ)⟩
theorem Cteach_quiescent_before_fast_cut_right_valid : Cteach_quiescent_before_fast_cut_right.Valid := by norm_num [RationalBox.Valid, Cteach_quiescent_before_fast_cut_right]

def all_B_teaching_emissions_in_gate_left : RationalBox := ⟨(1259660985 / 2097152 : ℚ), (314915263 / 524288 : ℚ)⟩
theorem all_B_teaching_emissions_in_gate_left_valid : all_B_teaching_emissions_in_gate_left.Valid := by norm_num [RationalBox.Valid, all_B_teaching_emissions_in_gate_left]

def all_B_teaching_emissions_in_gate_right : RationalBox := ⟨(630 / 1 : ℚ), (630 / 1 : ℚ)⟩
theorem all_B_teaching_emissions_in_gate_right_valid : all_B_teaching_emissions_in_gate_right.Valid := by norm_num [RationalBox.Valid, all_B_teaching_emissions_in_gate_right]

def C_fast_0_gain_below_cap_left : RationalBox := ⟨(149998500007499975000062499875000208333 / 500000000000000000000000000000000000000 : ℚ), (3000030000150000500001250002500004166673 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_0_gain_below_cap_left_valid : C_fast_0_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_0_gain_below_cap_left]

def C_fast_0_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_0_gain_below_cap_right_valid : C_fast_0_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_0_gain_below_cap_right]

def C_fast_0_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_0_positive_derivative_coefficient_left_valid : C_fast_0_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_0_positive_derivative_coefficient_left]

def C_fast_0_positive_derivative_coefficient_right : RationalBox := ⟨(234619652182025324597025620160078202879 / 1000000000000000000000000000000000000000 : ℚ), (586560861554983020919224180575194350001 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_0_positive_derivative_coefficient_right_valid : C_fast_0_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_0_positive_derivative_coefficient_right]

def C_fast_0_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_0_fixed_flow_increases_left_valid : C_fast_0_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_0_fixed_flow_increases_left]

def C_fast_0_fixed_flow_increases_right : RationalBox := ⟨(812763675428163105435705291892405716897 / 10000000000000000000000000000000000000000 : ℚ), (406503810918942910873231317319577075491 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_0_fixed_flow_increases_right_valid : C_fast_0_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_0_fixed_flow_increases_right]

def C_fast_0_weak_no_firing_left : RationalBox := ⟨(668245496870030414562379084115601089407 / 2500000000000000000000000000000000000000 : ℚ), (2673015447454469888832508889797450392823 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_0_weak_no_firing_left_valid : C_fast_0_weak_no_firing_left.Valid := by norm_num [RationalBox.Valid, C_fast_0_weak_no_firing_left]

def C_fast_0_weak_no_firing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_0_weak_no_firing_right_valid : C_fast_0_weak_no_firing_right.Valid := by norm_num [RationalBox.Valid, C_fast_0_weak_no_firing_right]

def C_fast_0_weak_end_above_rest_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem C_fast_0_weak_end_above_rest_left_valid : C_fast_0_weak_end_above_rest_left.Valid := by norm_num [RationalBox.Valid, C_fast_0_weak_end_above_rest_left]

def C_fast_0_weak_end_above_rest_right : RationalBox := ⟨(668245496870030414562379084115601089407 / 2500000000000000000000000000000000000000 : ℚ), (2673015447454469888832508889797450392823 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_0_weak_end_above_rest_right_valid : C_fast_0_weak_end_above_rest_right.Valid := by norm_num [RationalBox.Valid, C_fast_0_weak_end_above_rest_right]

def C_fast_0_arrival : RationalBox := ⟨(640 / 1 : ℚ), (640 / 1 : ℚ)⟩
theorem C_fast_0_arrival_valid : C_fast_0_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_0_arrival]

def C_fast_0_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem C_fast_0_b_after_valid : C_fast_0_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_0_b_after]

def C_fast_0_gain_after : RationalBox := ⟨(1093260347576166423671662107676113018829 / 2000000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_0_gain_after_valid : C_fast_0_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_0_gain_after]

def C_fast_1_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_1_aux_separation_left_valid : C_fast_1_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_1_aux_separation_left]

def C_fast_1_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_1_aux_separation_right_valid : C_fast_1_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_1_aux_separation_right]

def C_fast_1_gain_below_cap_left : RationalBox := ⟨(1093260347576166423671662107676113018829 / 2000000000000000000000000000000000000000 : ℚ), (2733205532504428685507801730030111871679 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_1_gain_below_cap_left_valid : C_fast_1_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_1_gain_below_cap_left]

def C_fast_1_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_1_gain_below_cap_right_valid : C_fast_1_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_1_gain_below_cap_right]

def C_fast_1_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_1_ready_at_input_left_valid : C_fast_1_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_1_ready_at_input_left]

def C_fast_1_ready_at_input_right : RationalBox := ⟨(3 / 1 : ℚ), (3 / 1 : ℚ)⟩
theorem C_fast_1_ready_at_input_right_valid : C_fast_1_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_1_ready_at_input_right]

def C_fast_1_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_1_positive_derivative_coefficient_left_valid : C_fast_1_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_1_positive_derivative_coefficient_left]

def C_fast_1_positive_derivative_coefficient_right : RationalBox := ⟨(1068762197954876114708902087903751941771 / 2500000000000000000000000000000000000000 : ℚ), (4461784396011012735221633438973062302427 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_1_positive_derivative_coefficient_right_valid : C_fast_1_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_1_positive_derivative_coefficient_right]

def C_fast_1_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_1_fixed_flow_increases_left_valid : C_fast_1_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_1_fixed_flow_increases_left]

def C_fast_1_fixed_flow_increases_right : RationalBox := ⟨(128514491798898444042878025073666282201 / 1250000000000000000000000000000000000000 : ℚ), (370349118152897270256862943194939520681 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_1_fixed_flow_increases_right_valid : C_fast_1_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_1_fixed_flow_increases_right]

def C_fast_1_weak_no_firing_left : RationalBox := ⟨(404837193210220878069943630299241842341 / 1000000000000000000000000000000000000000 : ℚ), (4274850919591008276434296393988955982977 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_1_weak_no_firing_left_valid : C_fast_1_weak_no_firing_left.Valid := by norm_num [RationalBox.Valid, C_fast_1_weak_no_firing_left]

def C_fast_1_weak_no_firing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_1_weak_no_firing_right_valid : C_fast_1_weak_no_firing_right.Valid := by norm_num [RationalBox.Valid, C_fast_1_weak_no_firing_right]

def C_fast_1_weak_end_above_rest_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem C_fast_1_weak_end_above_rest_left_valid : C_fast_1_weak_end_above_rest_left.Valid := by norm_num [RationalBox.Valid, C_fast_1_weak_end_above_rest_left]

def C_fast_1_weak_end_above_rest_right : RationalBox := ⟨(404837193210220878069943630299241842341 / 1000000000000000000000000000000000000000 : ℚ), (4274850919591008276434296393988955982977 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_1_weak_end_above_rest_right_valid : C_fast_1_weak_end_above_rest_right.Valid := by norm_num [RationalBox.Valid, C_fast_1_weak_end_above_rest_right]

def C_fast_1_arrival : RationalBox := ⟨(644 / 1 : ℚ), (644 / 1 : ℚ)⟩
theorem C_fast_1_arrival_valid : C_fast_1_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_1_arrival]

def C_fast_1_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem C_fast_1_b_after_valid : C_fast_1_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_1_b_after]

def C_fast_1_gain_after : RationalBox := ⟨(9960251165199976250523787258791057471269 / 10000000000000000000000000000000000000000 : ℚ), (9960450372215343763490081857984907714419 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_1_gain_after_valid : C_fast_1_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_1_gain_after]

def C_fast_2_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_2_aux_separation_left_valid : C_fast_2_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_2_aux_separation_left]

def C_fast_2_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_2_aux_separation_right_valid : C_fast_2_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_2_aux_separation_right]

def C_fast_2_gain_below_cap_left : RationalBox := ⟨(9960251165199976250523787258791057471269 / 10000000000000000000000000000000000000000 : ℚ), (9960450372215343763490081857984907714419 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_2_gain_below_cap_left_valid : C_fast_2_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_2_gain_below_cap_left]

def C_fast_2_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_2_gain_below_cap_right_valid : C_fast_2_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_2_gain_below_cap_right]

def C_fast_2_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_2_ready_at_input_left_valid : C_fast_2_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_2_ready_at_input_left]

def C_fast_2_ready_at_input_right : RationalBox := ⟨(3 / 1 : ℚ), (3 / 1 : ℚ)⟩
theorem C_fast_2_ready_at_input_right_valid : C_fast_2_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_2_ready_at_input_right]

def C_fast_2_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_2_positive_derivative_coefficient_left_valid : C_fast_2_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_2_positive_derivative_coefficient_left]

def C_fast_2_positive_derivative_coefficient_right : RationalBox := ⟨(7789646776161050202363801858500545502817 / 10000000000000000000000000000000000000000 : ℚ), (1019395196966225043922148887452079479763 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_2_positive_derivative_coefficient_right_valid : C_fast_2_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_2_positive_derivative_coefficient_right]

def C_fast_2_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_2_fixed_flow_increases_left_valid : C_fast_2_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_2_fixed_flow_increases_left]

def C_fast_2_fixed_flow_increases_right : RationalBox := ⟨(1812064679453537684486476566086021581849 / 10000000000000000000000000000000000000000 : ℚ), (674820090894440045079595129917914509719 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_2_fixed_flow_increases_right_valid : C_fast_2_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_2_fixed_flow_increases_right]

def C_fast_2_weak_no_firing_left : RationalBox := ⟨(3277247904033087369540798740533573094581 / 5000000000000000000000000000000000000000 : ℚ), (6997809775853773271203600825208198725001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_2_weak_no_firing_left_valid : C_fast_2_weak_no_firing_left.Valid := by norm_num [RationalBox.Valid, C_fast_2_weak_no_firing_left]

def C_fast_2_weak_no_firing_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_2_weak_no_firing_right_valid : C_fast_2_weak_no_firing_right.Valid := by norm_num [RationalBox.Valid, C_fast_2_weak_no_firing_right]

def C_fast_2_weak_end_above_rest_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem C_fast_2_weak_end_above_rest_left_valid : C_fast_2_weak_end_above_rest_left.Valid := by norm_num [RationalBox.Valid, C_fast_2_weak_end_above_rest_left]

def C_fast_2_weak_end_above_rest_right : RationalBox := ⟨(3277247904033087369540798740533573094581 / 5000000000000000000000000000000000000000 : ℚ), (6997809775853773271203600825208198725001 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_2_weak_end_above_rest_right_valid : C_fast_2_weak_end_above_rest_right.Valid := by norm_num [RationalBox.Valid, C_fast_2_weak_end_above_rest_right]

def C_fast_2_arrival : RationalBox := ⟨(648 / 1 : ℚ), (648 / 1 : ℚ)⟩
theorem C_fast_2_arrival_valid : C_fast_2_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_2_arrival]

def C_fast_2_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem C_fast_2_b_after_valid : C_fast_2_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_2_b_after]

def C_fast_2_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_2_gain_after_valid : C_fast_2_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_2_gain_after]

def C_fast_3_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_aux_separation_left_valid : C_fast_3_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_aux_separation_left]

def C_fast_3_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_3_aux_separation_right_valid : C_fast_3_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_aux_separation_right]

def C_fast_3_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_gain_below_cap_left_valid : C_fast_3_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_gain_below_cap_left]

def C_fast_3_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_3_gain_below_cap_right_valid : C_fast_3_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_gain_below_cap_right]

def C_fast_3_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_3_ready_at_input_left_valid : C_fast_3_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_ready_at_input_left]

def C_fast_3_ready_at_input_right : RationalBox := ⟨(3 / 1 : ℚ), (3 / 1 : ℚ)⟩
theorem C_fast_3_ready_at_input_right_valid : C_fast_3_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_ready_at_input_right]

def C_fast_3_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_3_positive_derivative_coefficient_left_valid : C_fast_3_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_positive_derivative_coefficient_left]

def C_fast_3_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (1486309184323293978167013416858949662313 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_positive_derivative_coefficient_right_valid : C_fast_3_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_positive_derivative_coefficient_right]

def C_fast_3_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_3_fixed_flow_increases_left_valid : C_fast_3_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_fixed_flow_increases_left]

def C_fast_3_fixed_flow_increases_right : RationalBox := ⟨(1646751569295971922063103980599705619083 / 5000000000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_fixed_flow_increases_right_valid : C_fast_3_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_fixed_flow_increases_right]

def C_fast_3_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_3_strong_crosses_by_one_left_valid : C_fast_3_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_strong_crosses_by_one_left]

def C_fast_3_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (477314757777244763371874457931451664359 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_strong_crosses_by_one_right_valid : C_fast_3_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_strong_crosses_by_one_right]

def C_fast_3_root_latency : RationalBox := ⟨(2119661 / 4194304 : ℚ), (342463 / 524288 : ℚ)⟩
theorem C_fast_3_root_latency_valid : C_fast_3_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_3_root_latency]

def C_fast_3_root_lower_left : RationalBox := ⟨(8960369274088747692178313348688637867007 / 10000000000000000000000000000000000000000 : ℚ), (9999998603082368475192107400356916080207 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_root_lower_left_valid : C_fast_3_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_root_lower_left]

def C_fast_3_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_3_root_lower_right_valid : C_fast_3_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_root_lower_right]

def C_fast_3_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_3_root_upper_left_valid : C_fast_3_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_root_upper_left]

def C_fast_3_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (5482794698738435473159699436752746778651 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_root_upper_right_valid : C_fast_3_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_root_upper_right]

def C_fast_3_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_MARK_before_fire_left_valid : C_fast_3_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_MARK_before_fire_left]

def C_fast_3_MARK_before_fire_right : RationalBox := ⟨(2119661 / 4194304 : ℚ), (2119661 / 4194304 : ℚ)⟩
theorem C_fast_3_MARK_before_fire_right_valid : C_fast_3_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_MARK_before_fire_right]

def C_fast_3_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem C_fast_3_fire_before_ERROR_left_valid : C_fast_3_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_fire_before_ERROR_left]

def C_fast_3_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_fire_before_ERROR_right_valid : C_fast_3_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_fire_before_ERROR_right]

def C_fast_3_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_ERROR_protected_left_valid : C_fast_3_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_3_ERROR_protected_left]

def C_fast_3_ERROR_protected_right : RationalBox := ⟨(8244484799617052579096163662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (65961534512582730588870164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_ERROR_protected_right_valid : C_fast_3_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_3_ERROR_protected_right]

def C_fast_3_arrival : RationalBox := ⟨(652 / 1 : ℚ), (652 / 1 : ℚ)⟩
theorem C_fast_3_arrival_valid : C_fast_3_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_3_arrival]

def C_fast_3_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem C_fast_3_b_after_valid : C_fast_3_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_3_b_after]

def C_fast_3_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_3_gain_after_valid : C_fast_3_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_3_gain_after]

def C_fast_3_emission : RationalBox := ⟨(2736805869 / 4194304 : ℚ), (342178239 / 524288 : ℚ)⟩
theorem C_fast_3_emission_valid : C_fast_3_emission.Valid := by norm_num [RationalBox.Valid, C_fast_3_emission]

def B_fast_3_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_aux_separation_left_valid : B_fast_3_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_aux_separation_left]

def B_fast_3_aux_separation_right : RationalBox := ⟨(1107408801 / 20971520 : ℚ), (139075771 / 2621440 : ℚ)⟩
theorem B_fast_3_aux_separation_right_valid : B_fast_3_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_aux_separation_right]

def B_fast_3_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_gain_below_cap_left_valid : B_fast_3_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_gain_below_cap_left]

def B_fast_3_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_fast_3_gain_below_cap_right_valid : B_fast_3_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_gain_below_cap_right]

def B_fast_3_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_3_ready_at_input_left_valid : B_fast_3_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_ready_at_input_left]

def B_fast_3_ready_at_input_right : RationalBox := ⟨(460613833414968538942379835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (57887263340241193270513211337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_ready_at_input_right_valid : B_fast_3_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_ready_at_input_right]

def B_fast_3_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_3_positive_derivative_coefficient_left_valid : B_fast_3_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_positive_derivative_coefficient_left]

def B_fast_3_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_positive_derivative_coefficient_right_valid : B_fast_3_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_positive_derivative_coefficient_right]

def B_fast_3_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_3_fixed_flow_increases_left_valid : B_fast_3_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_fixed_flow_increases_left]

def B_fast_3_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_fixed_flow_increases_right_valid : B_fast_3_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_fixed_flow_increases_right]

def B_fast_3_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_3_strong_crosses_by_one_left_valid : B_fast_3_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_strong_crosses_by_one_left]

def B_fast_3_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_strong_crosses_by_one_right_valid : B_fast_3_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_strong_crosses_by_one_right]

def B_fast_3_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_fast_3_root_latency_valid : B_fast_3_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_3_root_latency]

def B_fast_3_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_root_lower_left_valid : B_fast_3_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_root_lower_left]

def B_fast_3_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_3_root_lower_right_valid : B_fast_3_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_root_lower_right]

def B_fast_3_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_3_root_upper_left_valid : B_fast_3_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_root_upper_left]

def B_fast_3_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_root_upper_right_valid : B_fast_3_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_root_upper_right]

def B_fast_3_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_MARK_before_fire_left_valid : B_fast_3_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_MARK_before_fire_left]

def B_fast_3_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_fast_3_MARK_before_fire_right_valid : B_fast_3_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_MARK_before_fire_right]

def B_fast_3_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_fast_3_fire_before_ERROR_left_valid : B_fast_3_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_fire_before_ERROR_left]

def B_fast_3_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_fire_before_ERROR_right_valid : B_fast_3_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_fire_before_ERROR_right]

def B_fast_3_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_ERROR_protected_left_valid : B_fast_3_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_3_ERROR_protected_left]

def B_fast_3_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_ERROR_protected_right_valid : B_fast_3_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_3_ERROR_protected_right]

def B_fast_3_arrival : RationalBox := ⟨(13690320801 / 20971520 : ℚ), (1711939771 / 2621440 : ℚ)⟩
theorem B_fast_3_arrival_valid : B_fast_3_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_3_arrival]

def Bounds05Valid : Prop :=
  Cteach_teach_14_gain_after.Valid ∧
  Cteach_teach_14_emission.Valid ∧
  B_teach_15_aux_separation_left.Valid ∧
  B_teach_15_aux_separation_right.Valid ∧
  B_teach_15_gain_below_cap_left.Valid ∧
  B_teach_15_gain_below_cap_right.Valid ∧
  B_teach_15_ready_at_input_left.Valid ∧
  B_teach_15_ready_at_input_right.Valid ∧
  B_teach_15_positive_derivative_coefficient_left.Valid ∧
  B_teach_15_positive_derivative_coefficient_right.Valid ∧
  B_teach_15_fixed_flow_increases_left.Valid ∧
  B_teach_15_fixed_flow_increases_right.Valid ∧
  B_teach_15_strong_crosses_by_one_left.Valid ∧
  B_teach_15_strong_crosses_by_one_right.Valid ∧
  B_teach_15_root_latency.Valid ∧
  B_teach_15_root_lower_left.Valid ∧
  B_teach_15_root_lower_right.Valid ∧
  B_teach_15_root_upper_left.Valid ∧
  B_teach_15_root_upper_right.Valid ∧
  B_teach_15_MARK_before_fire_left.Valid ∧
  B_teach_15_MARK_before_fire_right.Valid ∧
  B_teach_15_fire_before_ERROR_left.Valid ∧
  B_teach_15_fire_before_ERROR_right.Valid ∧
  B_teach_15_ERROR_protected_left.Valid ∧
  B_teach_15_ERROR_protected_right.Valid ∧
  B_teach_15_arrival.Valid ∧
  B_teach_15_b_after.Valid ∧
  B_teach_15_gain_after.Valid ∧
  B_teach_15_emission.Valid ∧
  Cteach_teach_15_aux_separation_left.Valid ∧
  Cteach_teach_15_aux_separation_right.Valid ∧
  Cteach_teach_15_gain_below_cap_left.Valid ∧
  Cteach_teach_15_gain_below_cap_right.Valid ∧
  Cteach_teach_15_ready_at_input_left.Valid ∧
  Cteach_teach_15_ready_at_input_right.Valid ∧
  Cteach_teach_15_positive_derivative_coefficient_left.Valid ∧
  Cteach_teach_15_positive_derivative_coefficient_right.Valid ∧
  Cteach_teach_15_fixed_flow_increases_left.Valid ∧
  Cteach_teach_15_fixed_flow_increases_right.Valid ∧
  Cteach_teach_15_strong_crosses_by_one_left.Valid ∧
  Cteach_teach_15_strong_crosses_by_one_right.Valid ∧
  Cteach_teach_15_root_latency.Valid ∧
  Cteach_teach_15_root_lower_left.Valid ∧
  Cteach_teach_15_root_lower_right.Valid ∧
  Cteach_teach_15_root_upper_left.Valid ∧
  Cteach_teach_15_root_upper_right.Valid ∧
  Cteach_teach_15_MARK_before_fire_left.Valid ∧
  Cteach_teach_15_MARK_before_fire_right.Valid ∧
  Cteach_teach_15_fire_before_ERROR_left.Valid ∧
  Cteach_teach_15_fire_before_ERROR_right.Valid ∧
  Cteach_teach_15_ERROR_protected_left.Valid ∧
  Cteach_teach_15_ERROR_protected_right.Valid ∧
  Cteach_teach_15_arrival.Valid ∧
  Cteach_teach_15_b_after.Valid ∧
  Cteach_teach_15_gain_after.Valid ∧
  Cteach_teach_15_emission.Valid ∧
  B_quiescent_before_fast_cut_left.Valid ∧
  B_quiescent_before_fast_cut_right.Valid ∧
  Cteach_quiescent_before_fast_cut_left.Valid ∧
  Cteach_quiescent_before_fast_cut_right.Valid ∧
  all_B_teaching_emissions_in_gate_left.Valid ∧
  all_B_teaching_emissions_in_gate_right.Valid ∧
  C_fast_0_gain_below_cap_left.Valid ∧
  C_fast_0_gain_below_cap_right.Valid ∧
  C_fast_0_positive_derivative_coefficient_left.Valid ∧
  C_fast_0_positive_derivative_coefficient_right.Valid ∧
  C_fast_0_fixed_flow_increases_left.Valid ∧
  C_fast_0_fixed_flow_increases_right.Valid ∧
  C_fast_0_weak_no_firing_left.Valid ∧
  C_fast_0_weak_no_firing_right.Valid ∧
  C_fast_0_weak_end_above_rest_left.Valid ∧
  C_fast_0_weak_end_above_rest_right.Valid ∧
  C_fast_0_arrival.Valid ∧
  C_fast_0_b_after.Valid ∧
  C_fast_0_gain_after.Valid ∧
  C_fast_1_aux_separation_left.Valid ∧
  C_fast_1_aux_separation_right.Valid ∧
  C_fast_1_gain_below_cap_left.Valid ∧
  C_fast_1_gain_below_cap_right.Valid ∧
  C_fast_1_ready_at_input_left.Valid ∧
  C_fast_1_ready_at_input_right.Valid ∧
  C_fast_1_positive_derivative_coefficient_left.Valid ∧
  C_fast_1_positive_derivative_coefficient_right.Valid ∧
  C_fast_1_fixed_flow_increases_left.Valid ∧
  C_fast_1_fixed_flow_increases_right.Valid ∧
  C_fast_1_weak_no_firing_left.Valid ∧
  C_fast_1_weak_no_firing_right.Valid ∧
  C_fast_1_weak_end_above_rest_left.Valid ∧
  C_fast_1_weak_end_above_rest_right.Valid ∧
  C_fast_1_arrival.Valid ∧
  C_fast_1_b_after.Valid ∧
  C_fast_1_gain_after.Valid ∧
  C_fast_2_aux_separation_left.Valid ∧
  C_fast_2_aux_separation_right.Valid ∧
  C_fast_2_gain_below_cap_left.Valid ∧
  C_fast_2_gain_below_cap_right.Valid ∧
  C_fast_2_ready_at_input_left.Valid ∧
  C_fast_2_ready_at_input_right.Valid ∧
  C_fast_2_positive_derivative_coefficient_left.Valid ∧
  C_fast_2_positive_derivative_coefficient_right.Valid ∧
  C_fast_2_fixed_flow_increases_left.Valid ∧
  C_fast_2_fixed_flow_increases_right.Valid ∧
  C_fast_2_weak_no_firing_left.Valid ∧
  C_fast_2_weak_no_firing_right.Valid ∧
  C_fast_2_weak_end_above_rest_left.Valid ∧
  C_fast_2_weak_end_above_rest_right.Valid ∧
  C_fast_2_arrival.Valid ∧
  C_fast_2_b_after.Valid ∧
  C_fast_2_gain_after.Valid ∧
  C_fast_3_aux_separation_left.Valid ∧
  C_fast_3_aux_separation_right.Valid ∧
  C_fast_3_gain_below_cap_left.Valid ∧
  C_fast_3_gain_below_cap_right.Valid ∧
  C_fast_3_ready_at_input_left.Valid ∧
  C_fast_3_ready_at_input_right.Valid ∧
  C_fast_3_positive_derivative_coefficient_left.Valid ∧
  C_fast_3_positive_derivative_coefficient_right.Valid ∧
  C_fast_3_fixed_flow_increases_left.Valid ∧
  C_fast_3_fixed_flow_increases_right.Valid ∧
  C_fast_3_strong_crosses_by_one_left.Valid ∧
  C_fast_3_strong_crosses_by_one_right.Valid ∧
  C_fast_3_root_latency.Valid ∧
  C_fast_3_root_lower_left.Valid ∧
  C_fast_3_root_lower_right.Valid ∧
  C_fast_3_root_upper_left.Valid ∧
  C_fast_3_root_upper_right.Valid ∧
  C_fast_3_MARK_before_fire_left.Valid ∧
  C_fast_3_MARK_before_fire_right.Valid ∧
  C_fast_3_fire_before_ERROR_left.Valid ∧
  C_fast_3_fire_before_ERROR_right.Valid ∧
  C_fast_3_ERROR_protected_left.Valid ∧
  C_fast_3_ERROR_protected_right.Valid ∧
  C_fast_3_arrival.Valid ∧
  C_fast_3_b_after.Valid ∧
  C_fast_3_gain_after.Valid ∧
  C_fast_3_emission.Valid ∧
  B_fast_3_aux_separation_left.Valid ∧
  B_fast_3_aux_separation_right.Valid ∧
  B_fast_3_gain_below_cap_left.Valid ∧
  B_fast_3_gain_below_cap_right.Valid ∧
  B_fast_3_ready_at_input_left.Valid ∧
  B_fast_3_ready_at_input_right.Valid ∧
  B_fast_3_positive_derivative_coefficient_left.Valid ∧
  B_fast_3_positive_derivative_coefficient_right.Valid ∧
  B_fast_3_fixed_flow_increases_left.Valid ∧
  B_fast_3_fixed_flow_increases_right.Valid ∧
  B_fast_3_strong_crosses_by_one_left.Valid ∧
  B_fast_3_strong_crosses_by_one_right.Valid ∧
  B_fast_3_root_latency.Valid ∧
  B_fast_3_root_lower_left.Valid ∧
  B_fast_3_root_lower_right.Valid ∧
  B_fast_3_root_upper_left.Valid ∧
  B_fast_3_root_upper_right.Valid ∧
  B_fast_3_MARK_before_fire_left.Valid ∧
  B_fast_3_MARK_before_fire_right.Valid ∧
  B_fast_3_fire_before_ERROR_left.Valid ∧
  B_fast_3_fire_before_ERROR_right.Valid ∧
  B_fast_3_ERROR_protected_left.Valid ∧
  B_fast_3_ERROR_protected_right.Valid ∧
  B_fast_3_arrival.Valid
theorem Bounds05Valid_verified : Bounds05Valid := by
  exact ⟨Cteach_teach_14_gain_after_valid, Cteach_teach_14_emission_valid, B_teach_15_aux_separation_left_valid, B_teach_15_aux_separation_right_valid, B_teach_15_gain_below_cap_left_valid, B_teach_15_gain_below_cap_right_valid, B_teach_15_ready_at_input_left_valid, B_teach_15_ready_at_input_right_valid, B_teach_15_positive_derivative_coefficient_left_valid, B_teach_15_positive_derivative_coefficient_right_valid, B_teach_15_fixed_flow_increases_left_valid, B_teach_15_fixed_flow_increases_right_valid, B_teach_15_strong_crosses_by_one_left_valid, B_teach_15_strong_crosses_by_one_right_valid, B_teach_15_root_latency_valid, B_teach_15_root_lower_left_valid, B_teach_15_root_lower_right_valid, B_teach_15_root_upper_left_valid, B_teach_15_root_upper_right_valid, B_teach_15_MARK_before_fire_left_valid, B_teach_15_MARK_before_fire_right_valid, B_teach_15_fire_before_ERROR_left_valid, B_teach_15_fire_before_ERROR_right_valid, B_teach_15_ERROR_protected_left_valid, B_teach_15_ERROR_protected_right_valid, B_teach_15_arrival_valid, B_teach_15_b_after_valid, B_teach_15_gain_after_valid, B_teach_15_emission_valid, Cteach_teach_15_aux_separation_left_valid, Cteach_teach_15_aux_separation_right_valid, Cteach_teach_15_gain_below_cap_left_valid, Cteach_teach_15_gain_below_cap_right_valid, Cteach_teach_15_ready_at_input_left_valid, Cteach_teach_15_ready_at_input_right_valid, Cteach_teach_15_positive_derivative_coefficient_left_valid, Cteach_teach_15_positive_derivative_coefficient_right_valid, Cteach_teach_15_fixed_flow_increases_left_valid, Cteach_teach_15_fixed_flow_increases_right_valid, Cteach_teach_15_strong_crosses_by_one_left_valid, Cteach_teach_15_strong_crosses_by_one_right_valid, Cteach_teach_15_root_latency_valid, Cteach_teach_15_root_lower_left_valid, Cteach_teach_15_root_lower_right_valid, Cteach_teach_15_root_upper_left_valid, Cteach_teach_15_root_upper_right_valid, Cteach_teach_15_MARK_before_fire_left_valid, Cteach_teach_15_MARK_before_fire_right_valid, Cteach_teach_15_fire_before_ERROR_left_valid, Cteach_teach_15_fire_before_ERROR_right_valid, Cteach_teach_15_ERROR_protected_left_valid, Cteach_teach_15_ERROR_protected_right_valid, Cteach_teach_15_arrival_valid, Cteach_teach_15_b_after_valid, Cteach_teach_15_gain_after_valid, Cteach_teach_15_emission_valid, B_quiescent_before_fast_cut_left_valid, B_quiescent_before_fast_cut_right_valid, Cteach_quiescent_before_fast_cut_left_valid, Cteach_quiescent_before_fast_cut_right_valid, all_B_teaching_emissions_in_gate_left_valid, all_B_teaching_emissions_in_gate_right_valid, C_fast_0_gain_below_cap_left_valid, C_fast_0_gain_below_cap_right_valid, C_fast_0_positive_derivative_coefficient_left_valid, C_fast_0_positive_derivative_coefficient_right_valid, C_fast_0_fixed_flow_increases_left_valid, C_fast_0_fixed_flow_increases_right_valid, C_fast_0_weak_no_firing_left_valid, C_fast_0_weak_no_firing_right_valid, C_fast_0_weak_end_above_rest_left_valid, C_fast_0_weak_end_above_rest_right_valid, C_fast_0_arrival_valid, C_fast_0_b_after_valid, C_fast_0_gain_after_valid, C_fast_1_aux_separation_left_valid, C_fast_1_aux_separation_right_valid, C_fast_1_gain_below_cap_left_valid, C_fast_1_gain_below_cap_right_valid, C_fast_1_ready_at_input_left_valid, C_fast_1_ready_at_input_right_valid, C_fast_1_positive_derivative_coefficient_left_valid, C_fast_1_positive_derivative_coefficient_right_valid, C_fast_1_fixed_flow_increases_left_valid, C_fast_1_fixed_flow_increases_right_valid, C_fast_1_weak_no_firing_left_valid, C_fast_1_weak_no_firing_right_valid, C_fast_1_weak_end_above_rest_left_valid, C_fast_1_weak_end_above_rest_right_valid, C_fast_1_arrival_valid, C_fast_1_b_after_valid, C_fast_1_gain_after_valid, C_fast_2_aux_separation_left_valid, C_fast_2_aux_separation_right_valid, C_fast_2_gain_below_cap_left_valid, C_fast_2_gain_below_cap_right_valid, C_fast_2_ready_at_input_left_valid, C_fast_2_ready_at_input_right_valid, C_fast_2_positive_derivative_coefficient_left_valid, C_fast_2_positive_derivative_coefficient_right_valid, C_fast_2_fixed_flow_increases_left_valid, C_fast_2_fixed_flow_increases_right_valid, C_fast_2_weak_no_firing_left_valid, C_fast_2_weak_no_firing_right_valid, C_fast_2_weak_end_above_rest_left_valid, C_fast_2_weak_end_above_rest_right_valid, C_fast_2_arrival_valid, C_fast_2_b_after_valid, C_fast_2_gain_after_valid, C_fast_3_aux_separation_left_valid, C_fast_3_aux_separation_right_valid, C_fast_3_gain_below_cap_left_valid, C_fast_3_gain_below_cap_right_valid, C_fast_3_ready_at_input_left_valid, C_fast_3_ready_at_input_right_valid, C_fast_3_positive_derivative_coefficient_left_valid, C_fast_3_positive_derivative_coefficient_right_valid, C_fast_3_fixed_flow_increases_left_valid, C_fast_3_fixed_flow_increases_right_valid, C_fast_3_strong_crosses_by_one_left_valid, C_fast_3_strong_crosses_by_one_right_valid, C_fast_3_root_latency_valid, C_fast_3_root_lower_left_valid, C_fast_3_root_lower_right_valid, C_fast_3_root_upper_left_valid, C_fast_3_root_upper_right_valid, C_fast_3_MARK_before_fire_left_valid, C_fast_3_MARK_before_fire_right_valid, C_fast_3_fire_before_ERROR_left_valid, C_fast_3_fire_before_ERROR_right_valid, C_fast_3_ERROR_protected_left_valid, C_fast_3_ERROR_protected_right_valid, C_fast_3_arrival_valid, C_fast_3_b_after_valid, C_fast_3_gain_after_valid, C_fast_3_emission_valid, B_fast_3_aux_separation_left_valid, B_fast_3_aux_separation_right_valid, B_fast_3_gain_below_cap_left_valid, B_fast_3_gain_below_cap_right_valid, B_fast_3_ready_at_input_left_valid, B_fast_3_ready_at_input_right_valid, B_fast_3_positive_derivative_coefficient_left_valid, B_fast_3_positive_derivative_coefficient_right_valid, B_fast_3_fixed_flow_increases_left_valid, B_fast_3_fixed_flow_increases_right_valid, B_fast_3_strong_crosses_by_one_left_valid, B_fast_3_strong_crosses_by_one_right_valid, B_fast_3_root_latency_valid, B_fast_3_root_lower_left_valid, B_fast_3_root_lower_right_valid, B_fast_3_root_upper_left_valid, B_fast_3_root_upper_right_valid, B_fast_3_MARK_before_fire_left_valid, B_fast_3_MARK_before_fire_right_valid, B_fast_3_fire_before_ERROR_left_valid, B_fast_3_fire_before_ERROR_right_valid, B_fast_3_ERROR_protected_left_valid, B_fast_3_ERROR_protected_right_valid, B_fast_3_arrival_valid⟩

end KernelR.Certificates.Cadence003
