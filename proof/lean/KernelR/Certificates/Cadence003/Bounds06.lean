import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence003
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def B_fast_3_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_fast_3_b_after_valid : B_fast_3_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_3_b_after]

def B_fast_3_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_3_gain_after_valid : B_fast_3_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_3_gain_after]

def B_fast_3_emission : RationalBox := ⟨(13704018651 / 20971520 : ℚ), (856826043 / 1310720 : ℚ)⟩
theorem B_fast_3_emission_valid : B_fast_3_emission.Valid := by norm_num [RationalBox.Valid, B_fast_3_emission]

def A_fast_3_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_gain_below_cap_left_valid : A_fast_3_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_gain_below_cap_left]

def A_fast_3_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_3_gain_below_cap_right_valid : A_fast_3_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_gain_below_cap_right]

def A_fast_3_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_3_positive_derivative_coefficient_left_valid : A_fast_3_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_positive_derivative_coefficient_left]

def A_fast_3_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_positive_derivative_coefficient_right_valid : A_fast_3_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_positive_derivative_coefficient_right]

def A_fast_3_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_3_fixed_flow_increases_left_valid : A_fast_3_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_fixed_flow_increases_left]

def A_fast_3_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_fixed_flow_increases_right_valid : A_fast_3_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_fixed_flow_increases_right]

def A_fast_3_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_3_strong_crosses_by_one_left_valid : A_fast_3_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_strong_crosses_by_one_left]

def A_fast_3_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_strong_crosses_by_one_right_valid : A_fast_3_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_strong_crosses_by_one_right]

def A_fast_3_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_3_root_latency_valid : A_fast_3_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_3_root_latency]

def A_fast_3_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_root_lower_left_valid : A_fast_3_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_root_lower_left]

def A_fast_3_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_3_root_lower_right_valid : A_fast_3_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_root_lower_right]

def A_fast_3_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_3_root_upper_left_valid : A_fast_3_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_root_upper_left]

def A_fast_3_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_root_upper_right_valid : A_fast_3_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_root_upper_right]

def A_fast_3_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_MARK_before_fire_left_valid : A_fast_3_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_MARK_before_fire_left]

def A_fast_3_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem A_fast_3_MARK_before_fire_right_valid : A_fast_3_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_MARK_before_fire_right]

def A_fast_3_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_3_fire_before_ERROR_left_valid : A_fast_3_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_fire_before_ERROR_left]

def A_fast_3_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_fire_before_ERROR_right_valid : A_fast_3_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_fire_before_ERROR_right]

def A_fast_3_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_ERROR_protected_left_valid : A_fast_3_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_3_ERROR_protected_left]

def A_fast_3_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_ERROR_protected_right_valid : A_fast_3_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_3_ERROR_protected_right]

def A_fast_3_arrival : RationalBox := ⟨(13710310107 / 20971520 : ℚ), (857350331 / 1310720 : ℚ)⟩
theorem A_fast_3_arrival_valid : A_fast_3_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_3_arrival]

def A_fast_3_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem A_fast_3_b_after_valid : A_fast_3_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_3_b_after]

def A_fast_3_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_3_gain_after_valid : A_fast_3_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_3_gain_after]

def A_fast_3_emission : RationalBox := ⟨(13724007957 / 20971520 : ℚ), (1716412977 / 2621440 : ℚ)⟩
theorem A_fast_3_emission_valid : A_fast_3_emission.Valid := by norm_num [RationalBox.Valid, A_fast_3_emission]

def C_fast_4_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_aux_separation_left_valid : C_fast_4_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_4_aux_separation_left]

def C_fast_4_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_4_aux_separation_right_valid : C_fast_4_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_4_aux_separation_right]

def C_fast_4_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_gain_below_cap_left_valid : C_fast_4_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_4_gain_below_cap_left]

def C_fast_4_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_4_gain_below_cap_right_valid : C_fast_4_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_4_gain_below_cap_right]

def C_fast_4_input_in_SLOW_left : RationalBox := ⟨(2741000173 / 4194304 : ℚ), (342702527 / 524288 : ℚ)⟩
theorem C_fast_4_input_in_SLOW_left_valid : C_fast_4_input_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, C_fast_4_input_in_SLOW_left]

def C_fast_4_input_in_SLOW_right : RationalBox := ⟨(656 / 1 : ℚ), (656 / 1 : ℚ)⟩
theorem C_fast_4_input_in_SLOW_right_valid : C_fast_4_input_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, C_fast_4_input_in_SLOW_right]

def C_fast_4_input_before_return_left : RationalBox := ⟨(656 / 1 : ℚ), (656 / 1 : ℚ)⟩
theorem C_fast_4_input_before_return_left_valid : C_fast_4_input_before_return_left.Valid := by norm_num [RationalBox.Valid, C_fast_4_input_before_return_left]

def C_fast_4_input_before_return_right : RationalBox := ⟨(823244484799617052579096163662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (6587439832223001431760745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_input_before_return_right_valid : C_fast_4_input_before_return_right.Valid := by norm_num [RationalBox.Valid, C_fast_4_input_before_return_right]

def C_fast_4_whole_MARK_protected_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_whole_MARK_protected_left_valid : C_fast_4_whole_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_4_whole_MARK_protected_left]

def C_fast_4_whole_MARK_protected_right : RationalBox := ⟨(3354821094801174597757371592764094695433 / 2000000000000000000000000000000000000000 : ℚ), (8387052737002936494393428981910236738583 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_whole_MARK_protected_right_valid : C_fast_4_whole_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_4_whole_MARK_protected_right]

def C_fast_4_b_below_cap_left : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem C_fast_4_b_below_cap_left_valid : C_fast_4_b_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_4_b_below_cap_left]

def C_fast_4_b_below_cap_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem C_fast_4_b_below_cap_right_valid : C_fast_4_b_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_4_b_below_cap_right]

def C_fast_4_whole_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_whole_ERROR_protected_left_valid : C_fast_4_whole_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_4_whole_ERROR_protected_left]

def C_fast_4_whole_ERROR_protected_right : RationalBox := ⟨(3354821094801174597757371592764094695433 / 2000000000000000000000000000000000000000 : ℚ), (8387052737002936494393428981910236738583 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_whole_ERROR_protected_right_valid : C_fast_4_whole_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_4_whole_ERROR_protected_right]

def C_fast_4_no_firing_from_raw_tail_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem C_fast_4_no_firing_from_raw_tail_left_valid : C_fast_4_no_firing_from_raw_tail_left.Valid := by norm_num [RationalBox.Valid, C_fast_4_no_firing_from_raw_tail_left]

def C_fast_4_no_firing_from_raw_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_4_no_firing_from_raw_tail_right_valid : C_fast_4_no_firing_from_raw_tail_right.Valid := by norm_num [RationalBox.Valid, C_fast_4_no_firing_from_raw_tail_right]

def C_fast_4_reopen : RationalBox := ⟨(3354821094801174597757371592764094695433 / 2000000000000000000000000000000000000000 : ℚ), (4445295167948812879624742917176686517273 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_reopen_valid : C_fast_4_reopen.Valid := by norm_num [RationalBox.Valid, C_fast_4_reopen]

def C_fast_4_arrival : RationalBox := ⟨(656 / 1 : ℚ), (656 / 1 : ℚ)⟩
theorem C_fast_4_arrival_valid : C_fast_4_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_4_arrival]

def C_fast_4_b_after : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem C_fast_4_b_after_valid : C_fast_4_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_4_b_after]

def C_fast_4_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_4_gain_after_valid : C_fast_4_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_4_gain_after]

def C_fast_5_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_aux_separation_left_valid : C_fast_5_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_aux_separation_left]

def C_fast_5_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_5_aux_separation_right_valid : C_fast_5_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_aux_separation_right]

def C_fast_5_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_gain_below_cap_left_valid : C_fast_5_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_gain_below_cap_left]

def C_fast_5_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_5_gain_below_cap_right_valid : C_fast_5_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_gain_below_cap_right]

def C_fast_5_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_5_ready_at_input_left_valid : C_fast_5_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_ready_at_input_left]

def C_fast_5_ready_at_input_right : RationalBox := ⟨(5554704832051187120375257082823313482727 / 2500000000000000000000000000000000000000 : ℚ), (4645178905198825402242628407235905304567 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_ready_at_input_right_valid : C_fast_5_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_ready_at_input_right]

def C_fast_5_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_5_positive_derivative_coefficient_left_valid : C_fast_5_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_positive_derivative_coefficient_left]

def C_fast_5_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_positive_derivative_coefficient_right_valid : C_fast_5_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_positive_derivative_coefficient_right]

def C_fast_5_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_5_fixed_flow_increases_left_valid : C_fast_5_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_fixed_flow_increases_left]

def C_fast_5_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_fixed_flow_increases_right_valid : C_fast_5_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_fixed_flow_increases_right]

def C_fast_5_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_5_strong_crosses_by_one_left_valid : C_fast_5_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_strong_crosses_by_one_left]

def C_fast_5_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_strong_crosses_by_one_right_valid : C_fast_5_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_strong_crosses_by_one_right]

def C_fast_5_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem C_fast_5_root_latency_valid : C_fast_5_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_5_root_latency]

def C_fast_5_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_root_lower_left_valid : C_fast_5_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_root_lower_left]

def C_fast_5_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_5_root_lower_right_valid : C_fast_5_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_root_lower_right]

def C_fast_5_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_5_root_upper_left_valid : C_fast_5_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_root_upper_left]

def C_fast_5_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_root_upper_right_valid : C_fast_5_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_root_upper_right]

def C_fast_5_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_MARK_before_fire_left_valid : C_fast_5_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_MARK_before_fire_left]

def C_fast_5_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem C_fast_5_MARK_before_fire_right_valid : C_fast_5_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_MARK_before_fire_right]

def C_fast_5_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem C_fast_5_fire_before_ERROR_left_valid : C_fast_5_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_fire_before_ERROR_left]

def C_fast_5_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_fire_before_ERROR_right_valid : C_fast_5_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_fire_before_ERROR_right]

def C_fast_5_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_ERROR_protected_left_valid : C_fast_5_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_5_ERROR_protected_left]

def C_fast_5_ERROR_protected_right : RationalBox := ⟨(24627572083279480728086648008428468116319 / 5000000000000000000000000000000000000000 : ℚ), (49257481642918764755267901059609667182761 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_ERROR_protected_right_valid : C_fast_5_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_5_ERROR_protected_right]

def C_fast_5_arrival : RationalBox := ⟨(660 / 1 : ℚ), (660 / 1 : ℚ)⟩
theorem C_fast_5_arrival_valid : C_fast_5_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_5_arrival]

def C_fast_5_b_after : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem C_fast_5_b_after_valid : C_fast_5_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_5_b_after]

def C_fast_5_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_5_gain_after_valid : C_fast_5_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_5_gain_after]

def C_fast_5_emission : RationalBox := ⟨(1385490105 / 2097152 : ℚ), (346372543 / 524288 : ℚ)⟩
theorem C_fast_5_emission_valid : C_fast_5_emission.Valid := by norm_num [RationalBox.Valid, C_fast_5_emission]

def B_fast_5_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_aux_separation_left_valid : B_fast_5_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_aux_separation_left]

def B_fast_5_aux_separation_right : RationalBox := ⟨(82837169 / 10485760 : ℚ), (172969527 / 20971520 : ℚ)⟩
theorem B_fast_5_aux_separation_right_valid : B_fast_5_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_aux_separation_right]

def B_fast_5_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_gain_below_cap_left_valid : B_fast_5_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_gain_below_cap_left]

def B_fast_5_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_fast_5_gain_below_cap_right_valid : B_fast_5_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_gain_below_cap_right]

def B_fast_5_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_5_ready_at_input_left_valid : B_fast_5_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_ready_at_input_left]

def B_fast_5_ready_at_input_right : RationalBox := ⟨(11559848296102572145504835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1880555135494946932622586337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_ready_at_input_right_valid : B_fast_5_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_ready_at_input_right]

def B_fast_5_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_5_positive_derivative_coefficient_left_valid : B_fast_5_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_positive_derivative_coefficient_left]

def B_fast_5_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_positive_derivative_coefficient_right_valid : B_fast_5_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_positive_derivative_coefficient_right]

def B_fast_5_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_5_fixed_flow_increases_left_valid : B_fast_5_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_fixed_flow_increases_left]

def B_fast_5_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_fixed_flow_increases_right_valid : B_fast_5_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_fixed_flow_increases_right]

def B_fast_5_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_5_strong_crosses_by_one_left_valid : B_fast_5_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_strong_crosses_by_one_left]

def B_fast_5_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_strong_crosses_by_one_right_valid : B_fast_5_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_strong_crosses_by_one_right]

def B_fast_5_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_fast_5_root_latency_valid : B_fast_5_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_5_root_latency]

def B_fast_5_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_root_lower_left_valid : B_fast_5_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_root_lower_left]

def B_fast_5_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_5_root_lower_right_valid : B_fast_5_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_root_lower_right]

def B_fast_5_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_5_root_upper_left_valid : B_fast_5_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_root_upper_left]

def B_fast_5_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_root_upper_right_valid : B_fast_5_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_root_upper_right]

def B_fast_5_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_MARK_before_fire_left_valid : B_fast_5_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_MARK_before_fire_left]

def B_fast_5_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_fast_5_MARK_before_fire_right_valid : B_fast_5_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_MARK_before_fire_right]

def B_fast_5_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_fast_5_fire_before_ERROR_left_valid : B_fast_5_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_fire_before_ERROR_left]

def B_fast_5_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_fire_before_ERROR_right_valid : B_fast_5_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_fire_before_ERROR_right]

def B_fast_5_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_ERROR_protected_left_valid : B_fast_5_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_5_ERROR_protected_left]

def B_fast_5_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_ERROR_protected_right_valid : B_fast_5_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_5_ERROR_protected_right]

def B_fast_5_arrival : RationalBox := ⟨(6930596253 / 10485760 : ℚ), (1732911291 / 2621440 : ℚ)⟩
theorem B_fast_5_arrival_valid : B_fast_5_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_5_arrival]

def B_fast_5_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_fast_5_b_after_valid : B_fast_5_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_5_b_after]

def B_fast_5_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_5_gain_after_valid : B_fast_5_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_5_gain_after]

def B_fast_5_emission : RationalBox := ⟨(3468722589 / 5242880 : ℚ), (867311803 / 1310720 : ℚ)⟩
theorem B_fast_5_emission_valid : B_fast_5_emission.Valid := by norm_num [RationalBox.Valid, B_fast_5_emission]

def A_fast_5_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_aux_separation_left_valid : A_fast_5_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_aux_separation_left]

def A_fast_5_aux_separation_right : RationalBox := ⟨(81788593 / 10485760 : ℚ), (175066679 / 20971520 : ℚ)⟩
theorem A_fast_5_aux_separation_right_valid : A_fast_5_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_aux_separation_right]

def A_fast_5_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_gain_below_cap_left_valid : A_fast_5_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_gain_below_cap_left]

def A_fast_5_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_5_gain_below_cap_right_valid : A_fast_5_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_gain_below_cap_right]

def A_fast_5_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_5_ready_at_input_left_valid : A_fast_5_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_ready_at_input_left]

def A_fast_5_ready_at_input_right : RationalBox := ⟨(10559848296102572145504835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (2005555135494946932622586337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_ready_at_input_right_valid : A_fast_5_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_ready_at_input_right]

def A_fast_5_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_5_positive_derivative_coefficient_left_valid : A_fast_5_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_positive_derivative_coefficient_left]

def A_fast_5_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_positive_derivative_coefficient_right_valid : A_fast_5_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_positive_derivative_coefficient_right]

def A_fast_5_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_5_fixed_flow_increases_left_valid : A_fast_5_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_fixed_flow_increases_left]

def A_fast_5_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_fixed_flow_increases_right_valid : A_fast_5_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_fixed_flow_increases_right]

def A_fast_5_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_5_strong_crosses_by_one_left_valid : A_fast_5_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_strong_crosses_by_one_left]

def A_fast_5_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_strong_crosses_by_one_right_valid : A_fast_5_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_strong_crosses_by_one_right]

def A_fast_5_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_5_root_latency_valid : A_fast_5_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_5_root_latency]

def A_fast_5_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_root_lower_left_valid : A_fast_5_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_root_lower_left]

def A_fast_5_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_5_root_lower_right_valid : A_fast_5_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_root_lower_right]

def A_fast_5_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_5_root_upper_left_valid : A_fast_5_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_root_upper_left]

def A_fast_5_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_root_upper_right_valid : A_fast_5_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_root_upper_right]

def A_fast_5_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_MARK_before_fire_left_valid : A_fast_5_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_MARK_before_fire_left]

def A_fast_5_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem A_fast_5_MARK_before_fire_right_valid : A_fast_5_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_MARK_before_fire_right]

def A_fast_5_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_5_fire_before_ERROR_left_valid : A_fast_5_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_fire_before_ERROR_left]

def A_fast_5_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_fire_before_ERROR_right_valid : A_fast_5_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_fire_before_ERROR_right]

def A_fast_5_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_ERROR_protected_left_valid : A_fast_5_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_5_ERROR_protected_left]

def A_fast_5_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_ERROR_protected_right_valid : A_fast_5_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_5_ERROR_protected_right]

def A_fast_5_arrival : RationalBox := ⟨(3470295453 / 5242880 : ℚ), (867836091 / 1310720 : ℚ)⟩
theorem A_fast_5_arrival_valid : A_fast_5_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_5_arrival]

def A_fast_5_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem A_fast_5_b_after_valid : A_fast_5_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_5_b_after]

def A_fast_5_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_5_gain_after_valid : A_fast_5_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_5_gain_after]

def A_fast_5_emission : RationalBox := ⟨(6947439831 / 10485760 : ℚ), (1737384497 / 2621440 : ℚ)⟩
theorem A_fast_5_emission_valid : A_fast_5_emission.Valid := by norm_num [RationalBox.Valid, A_fast_5_emission]

def C_fast_6_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_aux_separation_left_valid : C_fast_6_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_6_aux_separation_left]

def C_fast_6_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_6_aux_separation_right_valid : C_fast_6_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_6_aux_separation_right]

def C_fast_6_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_gain_below_cap_left_valid : C_fast_6_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_6_gain_below_cap_left]

def C_fast_6_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_6_gain_below_cap_right_valid : C_fast_6_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_6_gain_below_cap_right]

def C_fast_6_input_in_SLOW_left : RationalBox := ⟨(1387587257 / 2097152 : ℚ), (346896831 / 524288 : ℚ)⟩
theorem C_fast_6_input_in_SLOW_left_valid : C_fast_6_input_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, C_fast_6_input_in_SLOW_left]

def C_fast_6_input_in_SLOW_right : RationalBox := ⟨(664 / 1 : ℚ), (664 / 1 : ℚ)⟩
theorem C_fast_6_input_in_SLOW_right_valid : C_fast_6_input_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, C_fast_6_input_in_SLOW_right]

def C_fast_6_input_before_return_left : RationalBox := ⟨(664 / 1 : ℚ), (664 / 1 : ℚ)⟩
theorem C_fast_6_input_before_return_left_valid : C_fast_6_input_before_return_left.Valid := by norm_num [RationalBox.Valid, C_fast_6_input_before_return_left]

def C_fast_6_input_before_return_right : RationalBox := ⟨(3324627572083279480728086648008428468116319 / 5000000000000000000000000000000000000000 : ℚ), (6649257801123814760849017901059609667182761 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_input_before_return_right_valid : C_fast_6_input_before_return_right.Valid := by norm_num [RationalBox.Valid, C_fast_6_input_before_return_right]

def C_fast_6_whole_MARK_protected_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_whole_MARK_protected_left_valid : C_fast_6_whole_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_6_whole_MARK_protected_left]

def C_fast_6_whole_MARK_protected_right : RationalBox := ⟨(3442189049790839997405975301241244675589 / 5000000000000000000000000000000000000000 : ℚ), (6884378099581679994811950602482489351179 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_whole_MARK_protected_right_valid : C_fast_6_whole_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_6_whole_MARK_protected_right]

def C_fast_6_b_below_cap_left : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_6_b_below_cap_left_valid : C_fast_6_b_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_6_b_below_cap_left]

def C_fast_6_b_below_cap_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem C_fast_6_b_below_cap_right_valid : C_fast_6_b_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_6_b_below_cap_right]

def C_fast_6_return_before_ERROR_left : RationalBox := ⟨(3462918907253900971294674961868998962979 / 5000000000000000000000000000000000000000 : ℚ), (6925837814507801942589349923737997925959 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_return_before_ERROR_left_valid : C_fast_6_return_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_6_return_before_ERROR_left]

def C_fast_6_return_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_return_before_ERROR_right_valid : C_fast_6_return_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_6_return_before_ERROR_right]

def C_fast_6_no_firing_from_raw_tail_left : RationalBox := ⟨(3257027964774671783814873434551130106927 / 10000000000000000000000000000000000000000 : ℚ), (203564247798416986488429589659445631683 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_no_firing_from_raw_tail_left_valid : C_fast_6_no_firing_from_raw_tail_left.Valid := by norm_num [RationalBox.Valid, C_fast_6_no_firing_from_raw_tail_left]

def C_fast_6_no_firing_from_raw_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_6_no_firing_from_raw_tail_right_valid : C_fast_6_no_firing_from_raw_tail_right.Valid := by norm_num [RationalBox.Valid, C_fast_6_no_firing_from_raw_tail_right]

def C_fast_6_reopen : RationalBox := ⟨(3442189049790839997405975301241244675589 / 5000000000000000000000000000000000000000 : ℚ), (6925837814507801942589349923737997925959 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_reopen_valid : C_fast_6_reopen.Valid := by norm_num [RationalBox.Valid, C_fast_6_reopen]

def C_fast_6_arrival : RationalBox := ⟨(664 / 1 : ℚ), (664 / 1 : ℚ)⟩
theorem C_fast_6_arrival_valid : C_fast_6_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_6_arrival]

def C_fast_6_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_6_b_after_valid : C_fast_6_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_6_b_after]

def C_fast_6_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_6_gain_after_valid : C_fast_6_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_6_gain_after]

def C_fast_7_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_aux_separation_left_valid : C_fast_7_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_aux_separation_left]

def C_fast_7_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_7_aux_separation_right_valid : C_fast_7_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_aux_separation_right]

def C_fast_7_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_gain_below_cap_left_valid : C_fast_7_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_gain_below_cap_left]

def C_fast_7_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_7_gain_below_cap_right_valid : C_fast_7_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_gain_below_cap_right]

def C_fast_7_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_7_ready_at_input_left_valid : C_fast_7_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_ready_at_input_left]

def C_fast_7_ready_at_input_right : RationalBox := ⟨(33074162185492198057410650076262002074041 / 10000000000000000000000000000000000000000 : ℚ), (16557810950209160002594024698758755324411 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_ready_at_input_right_valid : C_fast_7_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_ready_at_input_right]

def C_fast_7_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_7_positive_derivative_coefficient_left_valid : C_fast_7_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_positive_derivative_coefficient_left]

def C_fast_7_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (3264357605653317234816014265354281363287 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_positive_derivative_coefficient_right_valid : C_fast_7_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_positive_derivative_coefficient_right]

def C_fast_7_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_7_fixed_flow_increases_left_valid : C_fast_7_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_fixed_flow_increases_left]

def C_fast_7_fixed_flow_increases_right : RationalBox := ⟨(8348326312251713048619864487864709189829 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_fixed_flow_increases_right_valid : C_fast_7_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_fixed_flow_increases_right]

def C_fast_7_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_7_strong_crosses_by_one_left_valid : C_fast_7_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_strong_crosses_by_one_left]

def C_fast_7_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (394947997674287775576523852635283220031 / 200000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_strong_crosses_by_one_right_valid : C_fast_7_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_strong_crosses_by_one_right]

def C_fast_7_root_latency : RationalBox := ⟨(971733 / 4194304 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_7_root_latency_valid : C_fast_7_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_7_root_latency]

def Bounds06Valid : Prop :=
  B_fast_3_b_after.Valid ∧
  B_fast_3_gain_after.Valid ∧
  B_fast_3_emission.Valid ∧
  A_fast_3_gain_below_cap_left.Valid ∧
  A_fast_3_gain_below_cap_right.Valid ∧
  A_fast_3_positive_derivative_coefficient_left.Valid ∧
  A_fast_3_positive_derivative_coefficient_right.Valid ∧
  A_fast_3_fixed_flow_increases_left.Valid ∧
  A_fast_3_fixed_flow_increases_right.Valid ∧
  A_fast_3_strong_crosses_by_one_left.Valid ∧
  A_fast_3_strong_crosses_by_one_right.Valid ∧
  A_fast_3_root_latency.Valid ∧
  A_fast_3_root_lower_left.Valid ∧
  A_fast_3_root_lower_right.Valid ∧
  A_fast_3_root_upper_left.Valid ∧
  A_fast_3_root_upper_right.Valid ∧
  A_fast_3_MARK_before_fire_left.Valid ∧
  A_fast_3_MARK_before_fire_right.Valid ∧
  A_fast_3_fire_before_ERROR_left.Valid ∧
  A_fast_3_fire_before_ERROR_right.Valid ∧
  A_fast_3_ERROR_protected_left.Valid ∧
  A_fast_3_ERROR_protected_right.Valid ∧
  A_fast_3_arrival.Valid ∧
  A_fast_3_b_after.Valid ∧
  A_fast_3_gain_after.Valid ∧
  A_fast_3_emission.Valid ∧
  C_fast_4_aux_separation_left.Valid ∧
  C_fast_4_aux_separation_right.Valid ∧
  C_fast_4_gain_below_cap_left.Valid ∧
  C_fast_4_gain_below_cap_right.Valid ∧
  C_fast_4_input_in_SLOW_left.Valid ∧
  C_fast_4_input_in_SLOW_right.Valid ∧
  C_fast_4_input_before_return_left.Valid ∧
  C_fast_4_input_before_return_right.Valid ∧
  C_fast_4_whole_MARK_protected_left.Valid ∧
  C_fast_4_whole_MARK_protected_right.Valid ∧
  C_fast_4_b_below_cap_left.Valid ∧
  C_fast_4_b_below_cap_right.Valid ∧
  C_fast_4_whole_ERROR_protected_left.Valid ∧
  C_fast_4_whole_ERROR_protected_right.Valid ∧
  C_fast_4_no_firing_from_raw_tail_left.Valid ∧
  C_fast_4_no_firing_from_raw_tail_right.Valid ∧
  C_fast_4_reopen.Valid ∧
  C_fast_4_arrival.Valid ∧
  C_fast_4_b_after.Valid ∧
  C_fast_4_gain_after.Valid ∧
  C_fast_5_aux_separation_left.Valid ∧
  C_fast_5_aux_separation_right.Valid ∧
  C_fast_5_gain_below_cap_left.Valid ∧
  C_fast_5_gain_below_cap_right.Valid ∧
  C_fast_5_ready_at_input_left.Valid ∧
  C_fast_5_ready_at_input_right.Valid ∧
  C_fast_5_positive_derivative_coefficient_left.Valid ∧
  C_fast_5_positive_derivative_coefficient_right.Valid ∧
  C_fast_5_fixed_flow_increases_left.Valid ∧
  C_fast_5_fixed_flow_increases_right.Valid ∧
  C_fast_5_strong_crosses_by_one_left.Valid ∧
  C_fast_5_strong_crosses_by_one_right.Valid ∧
  C_fast_5_root_latency.Valid ∧
  C_fast_5_root_lower_left.Valid ∧
  C_fast_5_root_lower_right.Valid ∧
  C_fast_5_root_upper_left.Valid ∧
  C_fast_5_root_upper_right.Valid ∧
  C_fast_5_MARK_before_fire_left.Valid ∧
  C_fast_5_MARK_before_fire_right.Valid ∧
  C_fast_5_fire_before_ERROR_left.Valid ∧
  C_fast_5_fire_before_ERROR_right.Valid ∧
  C_fast_5_ERROR_protected_left.Valid ∧
  C_fast_5_ERROR_protected_right.Valid ∧
  C_fast_5_arrival.Valid ∧
  C_fast_5_b_after.Valid ∧
  C_fast_5_gain_after.Valid ∧
  C_fast_5_emission.Valid ∧
  B_fast_5_aux_separation_left.Valid ∧
  B_fast_5_aux_separation_right.Valid ∧
  B_fast_5_gain_below_cap_left.Valid ∧
  B_fast_5_gain_below_cap_right.Valid ∧
  B_fast_5_ready_at_input_left.Valid ∧
  B_fast_5_ready_at_input_right.Valid ∧
  B_fast_5_positive_derivative_coefficient_left.Valid ∧
  B_fast_5_positive_derivative_coefficient_right.Valid ∧
  B_fast_5_fixed_flow_increases_left.Valid ∧
  B_fast_5_fixed_flow_increases_right.Valid ∧
  B_fast_5_strong_crosses_by_one_left.Valid ∧
  B_fast_5_strong_crosses_by_one_right.Valid ∧
  B_fast_5_root_latency.Valid ∧
  B_fast_5_root_lower_left.Valid ∧
  B_fast_5_root_lower_right.Valid ∧
  B_fast_5_root_upper_left.Valid ∧
  B_fast_5_root_upper_right.Valid ∧
  B_fast_5_MARK_before_fire_left.Valid ∧
  B_fast_5_MARK_before_fire_right.Valid ∧
  B_fast_5_fire_before_ERROR_left.Valid ∧
  B_fast_5_fire_before_ERROR_right.Valid ∧
  B_fast_5_ERROR_protected_left.Valid ∧
  B_fast_5_ERROR_protected_right.Valid ∧
  B_fast_5_arrival.Valid ∧
  B_fast_5_b_after.Valid ∧
  B_fast_5_gain_after.Valid ∧
  B_fast_5_emission.Valid ∧
  A_fast_5_aux_separation_left.Valid ∧
  A_fast_5_aux_separation_right.Valid ∧
  A_fast_5_gain_below_cap_left.Valid ∧
  A_fast_5_gain_below_cap_right.Valid ∧
  A_fast_5_ready_at_input_left.Valid ∧
  A_fast_5_ready_at_input_right.Valid ∧
  A_fast_5_positive_derivative_coefficient_left.Valid ∧
  A_fast_5_positive_derivative_coefficient_right.Valid ∧
  A_fast_5_fixed_flow_increases_left.Valid ∧
  A_fast_5_fixed_flow_increases_right.Valid ∧
  A_fast_5_strong_crosses_by_one_left.Valid ∧
  A_fast_5_strong_crosses_by_one_right.Valid ∧
  A_fast_5_root_latency.Valid ∧
  A_fast_5_root_lower_left.Valid ∧
  A_fast_5_root_lower_right.Valid ∧
  A_fast_5_root_upper_left.Valid ∧
  A_fast_5_root_upper_right.Valid ∧
  A_fast_5_MARK_before_fire_left.Valid ∧
  A_fast_5_MARK_before_fire_right.Valid ∧
  A_fast_5_fire_before_ERROR_left.Valid ∧
  A_fast_5_fire_before_ERROR_right.Valid ∧
  A_fast_5_ERROR_protected_left.Valid ∧
  A_fast_5_ERROR_protected_right.Valid ∧
  A_fast_5_arrival.Valid ∧
  A_fast_5_b_after.Valid ∧
  A_fast_5_gain_after.Valid ∧
  A_fast_5_emission.Valid ∧
  C_fast_6_aux_separation_left.Valid ∧
  C_fast_6_aux_separation_right.Valid ∧
  C_fast_6_gain_below_cap_left.Valid ∧
  C_fast_6_gain_below_cap_right.Valid ∧
  C_fast_6_input_in_SLOW_left.Valid ∧
  C_fast_6_input_in_SLOW_right.Valid ∧
  C_fast_6_input_before_return_left.Valid ∧
  C_fast_6_input_before_return_right.Valid ∧
  C_fast_6_whole_MARK_protected_left.Valid ∧
  C_fast_6_whole_MARK_protected_right.Valid ∧
  C_fast_6_b_below_cap_left.Valid ∧
  C_fast_6_b_below_cap_right.Valid ∧
  C_fast_6_return_before_ERROR_left.Valid ∧
  C_fast_6_return_before_ERROR_right.Valid ∧
  C_fast_6_no_firing_from_raw_tail_left.Valid ∧
  C_fast_6_no_firing_from_raw_tail_right.Valid ∧
  C_fast_6_reopen.Valid ∧
  C_fast_6_arrival.Valid ∧
  C_fast_6_b_after.Valid ∧
  C_fast_6_gain_after.Valid ∧
  C_fast_7_aux_separation_left.Valid ∧
  C_fast_7_aux_separation_right.Valid ∧
  C_fast_7_gain_below_cap_left.Valid ∧
  C_fast_7_gain_below_cap_right.Valid ∧
  C_fast_7_ready_at_input_left.Valid ∧
  C_fast_7_ready_at_input_right.Valid ∧
  C_fast_7_positive_derivative_coefficient_left.Valid ∧
  C_fast_7_positive_derivative_coefficient_right.Valid ∧
  C_fast_7_fixed_flow_increases_left.Valid ∧
  C_fast_7_fixed_flow_increases_right.Valid ∧
  C_fast_7_strong_crosses_by_one_left.Valid ∧
  C_fast_7_strong_crosses_by_one_right.Valid ∧
  C_fast_7_root_latency.Valid
theorem Bounds06Valid_verified : Bounds06Valid := by
  exact ⟨B_fast_3_b_after_valid, B_fast_3_gain_after_valid, B_fast_3_emission_valid, A_fast_3_gain_below_cap_left_valid, A_fast_3_gain_below_cap_right_valid, A_fast_3_positive_derivative_coefficient_left_valid, A_fast_3_positive_derivative_coefficient_right_valid, A_fast_3_fixed_flow_increases_left_valid, A_fast_3_fixed_flow_increases_right_valid, A_fast_3_strong_crosses_by_one_left_valid, A_fast_3_strong_crosses_by_one_right_valid, A_fast_3_root_latency_valid, A_fast_3_root_lower_left_valid, A_fast_3_root_lower_right_valid, A_fast_3_root_upper_left_valid, A_fast_3_root_upper_right_valid, A_fast_3_MARK_before_fire_left_valid, A_fast_3_MARK_before_fire_right_valid, A_fast_3_fire_before_ERROR_left_valid, A_fast_3_fire_before_ERROR_right_valid, A_fast_3_ERROR_protected_left_valid, A_fast_3_ERROR_protected_right_valid, A_fast_3_arrival_valid, A_fast_3_b_after_valid, A_fast_3_gain_after_valid, A_fast_3_emission_valid, C_fast_4_aux_separation_left_valid, C_fast_4_aux_separation_right_valid, C_fast_4_gain_below_cap_left_valid, C_fast_4_gain_below_cap_right_valid, C_fast_4_input_in_SLOW_left_valid, C_fast_4_input_in_SLOW_right_valid, C_fast_4_input_before_return_left_valid, C_fast_4_input_before_return_right_valid, C_fast_4_whole_MARK_protected_left_valid, C_fast_4_whole_MARK_protected_right_valid, C_fast_4_b_below_cap_left_valid, C_fast_4_b_below_cap_right_valid, C_fast_4_whole_ERROR_protected_left_valid, C_fast_4_whole_ERROR_protected_right_valid, C_fast_4_no_firing_from_raw_tail_left_valid, C_fast_4_no_firing_from_raw_tail_right_valid, C_fast_4_reopen_valid, C_fast_4_arrival_valid, C_fast_4_b_after_valid, C_fast_4_gain_after_valid, C_fast_5_aux_separation_left_valid, C_fast_5_aux_separation_right_valid, C_fast_5_gain_below_cap_left_valid, C_fast_5_gain_below_cap_right_valid, C_fast_5_ready_at_input_left_valid, C_fast_5_ready_at_input_right_valid, C_fast_5_positive_derivative_coefficient_left_valid, C_fast_5_positive_derivative_coefficient_right_valid, C_fast_5_fixed_flow_increases_left_valid, C_fast_5_fixed_flow_increases_right_valid, C_fast_5_strong_crosses_by_one_left_valid, C_fast_5_strong_crosses_by_one_right_valid, C_fast_5_root_latency_valid, C_fast_5_root_lower_left_valid, C_fast_5_root_lower_right_valid, C_fast_5_root_upper_left_valid, C_fast_5_root_upper_right_valid, C_fast_5_MARK_before_fire_left_valid, C_fast_5_MARK_before_fire_right_valid, C_fast_5_fire_before_ERROR_left_valid, C_fast_5_fire_before_ERROR_right_valid, C_fast_5_ERROR_protected_left_valid, C_fast_5_ERROR_protected_right_valid, C_fast_5_arrival_valid, C_fast_5_b_after_valid, C_fast_5_gain_after_valid, C_fast_5_emission_valid, B_fast_5_aux_separation_left_valid, B_fast_5_aux_separation_right_valid, B_fast_5_gain_below_cap_left_valid, B_fast_5_gain_below_cap_right_valid, B_fast_5_ready_at_input_left_valid, B_fast_5_ready_at_input_right_valid, B_fast_5_positive_derivative_coefficient_left_valid, B_fast_5_positive_derivative_coefficient_right_valid, B_fast_5_fixed_flow_increases_left_valid, B_fast_5_fixed_flow_increases_right_valid, B_fast_5_strong_crosses_by_one_left_valid, B_fast_5_strong_crosses_by_one_right_valid, B_fast_5_root_latency_valid, B_fast_5_root_lower_left_valid, B_fast_5_root_lower_right_valid, B_fast_5_root_upper_left_valid, B_fast_5_root_upper_right_valid, B_fast_5_MARK_before_fire_left_valid, B_fast_5_MARK_before_fire_right_valid, B_fast_5_fire_before_ERROR_left_valid, B_fast_5_fire_before_ERROR_right_valid, B_fast_5_ERROR_protected_left_valid, B_fast_5_ERROR_protected_right_valid, B_fast_5_arrival_valid, B_fast_5_b_after_valid, B_fast_5_gain_after_valid, B_fast_5_emission_valid, A_fast_5_aux_separation_left_valid, A_fast_5_aux_separation_right_valid, A_fast_5_gain_below_cap_left_valid, A_fast_5_gain_below_cap_right_valid, A_fast_5_ready_at_input_left_valid, A_fast_5_ready_at_input_right_valid, A_fast_5_positive_derivative_coefficient_left_valid, A_fast_5_positive_derivative_coefficient_right_valid, A_fast_5_fixed_flow_increases_left_valid, A_fast_5_fixed_flow_increases_right_valid, A_fast_5_strong_crosses_by_one_left_valid, A_fast_5_strong_crosses_by_one_right_valid, A_fast_5_root_latency_valid, A_fast_5_root_lower_left_valid, A_fast_5_root_lower_right_valid, A_fast_5_root_upper_left_valid, A_fast_5_root_upper_right_valid, A_fast_5_MARK_before_fire_left_valid, A_fast_5_MARK_before_fire_right_valid, A_fast_5_fire_before_ERROR_left_valid, A_fast_5_fire_before_ERROR_right_valid, A_fast_5_ERROR_protected_left_valid, A_fast_5_ERROR_protected_right_valid, A_fast_5_arrival_valid, A_fast_5_b_after_valid, A_fast_5_gain_after_valid, A_fast_5_emission_valid, C_fast_6_aux_separation_left_valid, C_fast_6_aux_separation_right_valid, C_fast_6_gain_below_cap_left_valid, C_fast_6_gain_below_cap_right_valid, C_fast_6_input_in_SLOW_left_valid, C_fast_6_input_in_SLOW_right_valid, C_fast_6_input_before_return_left_valid, C_fast_6_input_before_return_right_valid, C_fast_6_whole_MARK_protected_left_valid, C_fast_6_whole_MARK_protected_right_valid, C_fast_6_b_below_cap_left_valid, C_fast_6_b_below_cap_right_valid, C_fast_6_return_before_ERROR_left_valid, C_fast_6_return_before_ERROR_right_valid, C_fast_6_no_firing_from_raw_tail_left_valid, C_fast_6_no_firing_from_raw_tail_right_valid, C_fast_6_reopen_valid, C_fast_6_arrival_valid, C_fast_6_b_after_valid, C_fast_6_gain_after_valid, C_fast_7_aux_separation_left_valid, C_fast_7_aux_separation_right_valid, C_fast_7_gain_below_cap_left_valid, C_fast_7_gain_below_cap_right_valid, C_fast_7_ready_at_input_left_valid, C_fast_7_ready_at_input_right_valid, C_fast_7_positive_derivative_coefficient_left_valid, C_fast_7_positive_derivative_coefficient_right_valid, C_fast_7_fixed_flow_increases_left_valid, C_fast_7_fixed_flow_increases_right_valid, C_fast_7_strong_crosses_by_one_left_valid, C_fast_7_strong_crosses_by_one_right_valid, C_fast_7_root_latency_valid⟩

end KernelR.Certificates.Cadence003
