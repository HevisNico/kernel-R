import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence003
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def C_fast_20_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_gain_below_cap_left_valid : C_fast_20_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_gain_below_cap_left]

def C_fast_20_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_20_gain_below_cap_right_valid : C_fast_20_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_gain_below_cap_right]

def C_fast_20_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_20_ready_at_input_left_valid : C_fast_20_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_ready_at_input_left]

def C_fast_20_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_ready_at_input_right_valid : C_fast_20_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_ready_at_input_right]

def C_fast_20_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_20_positive_derivative_coefficient_left_valid : C_fast_20_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_positive_derivative_coefficient_left]

def C_fast_20_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_positive_derivative_coefficient_right_valid : C_fast_20_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_positive_derivative_coefficient_right]

def C_fast_20_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_20_fixed_flow_increases_left_valid : C_fast_20_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_fixed_flow_increases_left]

def C_fast_20_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_fixed_flow_increases_right_valid : C_fast_20_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_fixed_flow_increases_right]

def C_fast_20_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_20_strong_crosses_by_one_left_valid : C_fast_20_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_strong_crosses_by_one_left]

def C_fast_20_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_strong_crosses_by_one_right_valid : C_fast_20_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_strong_crosses_by_one_right]

def C_fast_20_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_20_root_latency_valid : C_fast_20_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_20_root_latency]

def C_fast_20_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_root_lower_left_valid : C_fast_20_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_root_lower_left]

def C_fast_20_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_20_root_lower_right_valid : C_fast_20_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_root_lower_right]

def C_fast_20_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_20_root_upper_left_valid : C_fast_20_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_root_upper_left]

def C_fast_20_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_root_upper_right_valid : C_fast_20_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_root_upper_right]

def C_fast_20_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_MARK_before_fire_left_valid : C_fast_20_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_MARK_before_fire_left]

def C_fast_20_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_20_MARK_before_fire_right_valid : C_fast_20_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_MARK_before_fire_right]

def C_fast_20_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_20_fire_before_ERROR_left_valid : C_fast_20_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_fire_before_ERROR_left]

def C_fast_20_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_fire_before_ERROR_right_valid : C_fast_20_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_fire_before_ERROR_right]

def C_fast_20_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_ERROR_protected_left_valid : C_fast_20_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_20_ERROR_protected_left]

def C_fast_20_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_ERROR_protected_right_valid : C_fast_20_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_20_ERROR_protected_right]

def C_fast_20_arrival : RationalBox := ⟨(720 / 1 : ℚ), (720 / 1 : ℚ)⟩
theorem C_fast_20_arrival_valid : C_fast_20_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_20_arrival]

def C_fast_20_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_20_b_after_valid : C_fast_20_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_20_b_after]

def C_fast_20_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_20_gain_after_valid : C_fast_20_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_20_gain_after]

def C_fast_20_emission : RationalBox := ⟨(377617077 / 524288 : ℚ), (755234161 / 1048576 : ℚ)⟩
theorem C_fast_20_emission_valid : C_fast_20_emission.Valid := by norm_num [RationalBox.Valid, C_fast_20_emission]

def B_fast_20_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_aux_separation_left_valid : B_fast_20_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_aux_separation_left]

def B_fast_20_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_20_aux_separation_right_valid : B_fast_20_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_aux_separation_right]

def B_fast_20_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_gain_below_cap_left_valid : B_fast_20_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_gain_below_cap_left]

def B_fast_20_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_fast_20_gain_below_cap_right_valid : B_fast_20_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_gain_below_cap_right]

def B_fast_20_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_20_ready_at_input_left_valid : B_fast_20_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_ready_at_input_left]

def B_fast_20_ready_at_input_right : RationalBox := ⟨(2412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2206782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_ready_at_input_right_valid : B_fast_20_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_ready_at_input_right]

def B_fast_20_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_20_positive_derivative_coefficient_left_valid : B_fast_20_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_positive_derivative_coefficient_left]

def B_fast_20_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_positive_derivative_coefficient_right_valid : B_fast_20_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_positive_derivative_coefficient_right]

def B_fast_20_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_20_fixed_flow_increases_left_valid : B_fast_20_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_fixed_flow_increases_left]

def B_fast_20_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_fixed_flow_increases_right_valid : B_fast_20_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_fixed_flow_increases_right]

def B_fast_20_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_20_strong_crosses_by_one_left_valid : B_fast_20_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_strong_crosses_by_one_left]

def B_fast_20_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_strong_crosses_by_one_right_valid : B_fast_20_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_strong_crosses_by_one_right]

def B_fast_20_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_20_root_latency_valid : B_fast_20_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_20_root_latency]

def B_fast_20_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_root_lower_left_valid : B_fast_20_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_root_lower_left]

def B_fast_20_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_20_root_lower_right_valid : B_fast_20_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_root_lower_right]

def B_fast_20_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_20_root_upper_left_valid : B_fast_20_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_root_upper_left]

def B_fast_20_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_root_upper_right_valid : B_fast_20_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_root_upper_right]

def B_fast_20_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_MARK_before_fire_left_valid : B_fast_20_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_MARK_before_fire_left]

def B_fast_20_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_20_MARK_before_fire_right_valid : B_fast_20_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_MARK_before_fire_right]

def B_fast_20_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_20_fire_before_ERROR_left_valid : B_fast_20_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_fire_before_ERROR_left]

def B_fast_20_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_fire_before_ERROR_right_valid : B_fast_20_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_fire_before_ERROR_right]

def B_fast_20_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_ERROR_protected_left_valid : B_fast_20_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_20_ERROR_protected_left]

def B_fast_20_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_ERROR_protected_right_valid : B_fast_20_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_20_ERROR_protected_right]

def B_fast_20_arrival : RationalBox := ⟨(1888871817 / 2621440 : ℚ), (3778267957 / 5242880 : ℚ)⟩
theorem B_fast_20_arrival_valid : B_fast_20_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_20_arrival]

def B_fast_20_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_20_b_after_valid : B_fast_20_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_20_b_after]

def B_fast_20_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_20_gain_after_valid : B_fast_20_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_20_gain_after]

def B_fast_20_emission : RationalBox := ⟨(944760201 / 1310720 : ℚ), (1889782581 / 2621440 : ℚ)⟩
theorem B_fast_20_emission_valid : B_fast_20_emission.Valid := by norm_num [RationalBox.Valid, B_fast_20_emission]

def A_fast_20_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_aux_separation_left_valid : A_fast_20_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_aux_separation_left]

def A_fast_20_aux_separation_right : RationalBox := ⟨(19 / 5 : ℚ), (21 / 5 : ℚ)⟩
theorem A_fast_20_aux_separation_right_valid : A_fast_20_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_aux_separation_right]

def A_fast_20_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_gain_below_cap_left_valid : A_fast_20_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_gain_below_cap_left]

def A_fast_20_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_20_gain_below_cap_right_valid : A_fast_20_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_gain_below_cap_right]

def A_fast_20_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_20_ready_at_input_left_valid : A_fast_20_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_ready_at_input_left]

def A_fast_20_ready_at_input_right : RationalBox := ⟨(1412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_ready_at_input_right_valid : A_fast_20_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_ready_at_input_right]

def A_fast_20_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_20_positive_derivative_coefficient_left_valid : A_fast_20_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_positive_derivative_coefficient_left]

def A_fast_20_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_positive_derivative_coefficient_right_valid : A_fast_20_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_positive_derivative_coefficient_right]

def A_fast_20_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_20_fixed_flow_increases_left_valid : A_fast_20_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_fixed_flow_increases_left]

def A_fast_20_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_fixed_flow_increases_right_valid : A_fast_20_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_fixed_flow_increases_right]

def A_fast_20_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_20_strong_crosses_by_one_left_valid : A_fast_20_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_strong_crosses_by_one_left]

def A_fast_20_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_strong_crosses_by_one_right_valid : A_fast_20_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_strong_crosses_by_one_right]

def A_fast_20_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_20_root_latency_valid : A_fast_20_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_20_root_latency]

def A_fast_20_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_root_lower_left_valid : A_fast_20_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_root_lower_left]

def A_fast_20_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_20_root_lower_right_valid : A_fast_20_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_root_lower_right]

def A_fast_20_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_20_root_upper_left_valid : A_fast_20_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_root_upper_left]

def A_fast_20_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_root_upper_right_valid : A_fast_20_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_root_upper_right]

def A_fast_20_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_MARK_before_fire_left_valid : A_fast_20_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_MARK_before_fire_left]

def A_fast_20_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem A_fast_20_MARK_before_fire_right_valid : A_fast_20_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_MARK_before_fire_right]

def A_fast_20_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_20_fire_before_ERROR_left_valid : A_fast_20_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_fire_before_ERROR_left]

def A_fast_20_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_fire_before_ERROR_right_valid : A_fast_20_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_fire_before_ERROR_right]

def A_fast_20_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_ERROR_protected_left_valid : A_fast_20_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_20_ERROR_protected_left]

def A_fast_20_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_ERROR_protected_right_valid : A_fast_20_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_20_ERROR_protected_right]

def A_fast_20_arrival : RationalBox := ⟨(945153417 / 1310720 : ℚ), (1890831157 / 2621440 : ℚ)⟩
theorem A_fast_20_arrival_valid : A_fast_20_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_20_arrival]

def A_fast_20_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_20_b_after_valid : A_fast_20_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_20_b_after]

def A_fast_20_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_20_gain_after_valid : A_fast_20_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_20_gain_after]

def A_fast_20_emission : RationalBox := ⟨(1890955419 / 2621440 : ℚ), (3782959519 / 5242880 : ℚ)⟩
theorem A_fast_20_emission_valid : A_fast_20_emission.Valid := by norm_num [RationalBox.Valid, A_fast_20_emission]

def C_fast_21_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_aux_separation_left_valid : C_fast_21_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_aux_separation_left]

def C_fast_21_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_21_aux_separation_right_valid : C_fast_21_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_aux_separation_right]

def C_fast_21_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_gain_below_cap_left_valid : C_fast_21_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_gain_below_cap_left]

def C_fast_21_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_21_gain_below_cap_right_valid : C_fast_21_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_gain_below_cap_right]

def C_fast_21_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_21_ready_at_input_left_valid : C_fast_21_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_ready_at_input_left]

def C_fast_21_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_ready_at_input_right_valid : C_fast_21_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_ready_at_input_right]

def C_fast_21_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_21_positive_derivative_coefficient_left_valid : C_fast_21_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_positive_derivative_coefficient_left]

def C_fast_21_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_positive_derivative_coefficient_right_valid : C_fast_21_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_positive_derivative_coefficient_right]

def C_fast_21_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_21_fixed_flow_increases_left_valid : C_fast_21_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_fixed_flow_increases_left]

def C_fast_21_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_fixed_flow_increases_right_valid : C_fast_21_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_fixed_flow_increases_right]

def C_fast_21_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_21_strong_crosses_by_one_left_valid : C_fast_21_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_strong_crosses_by_one_left]

def C_fast_21_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_strong_crosses_by_one_right_valid : C_fast_21_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_strong_crosses_by_one_right]

def C_fast_21_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_21_root_latency_valid : C_fast_21_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_21_root_latency]

def C_fast_21_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_root_lower_left_valid : C_fast_21_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_root_lower_left]

def C_fast_21_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_21_root_lower_right_valid : C_fast_21_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_root_lower_right]

def C_fast_21_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_21_root_upper_left_valid : C_fast_21_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_root_upper_left]

def C_fast_21_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_root_upper_right_valid : C_fast_21_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_root_upper_right]

def C_fast_21_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_MARK_before_fire_left_valid : C_fast_21_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_MARK_before_fire_left]

def C_fast_21_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_21_MARK_before_fire_right_valid : C_fast_21_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_MARK_before_fire_right]

def C_fast_21_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_21_fire_before_ERROR_left_valid : C_fast_21_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_fire_before_ERROR_left]

def C_fast_21_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_fire_before_ERROR_right_valid : C_fast_21_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_fire_before_ERROR_right]

def C_fast_21_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_ERROR_protected_left_valid : C_fast_21_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_21_ERROR_protected_left]

def C_fast_21_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_ERROR_protected_right_valid : C_fast_21_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_21_ERROR_protected_right]

def C_fast_21_arrival : RationalBox := ⟨(724 / 1 : ℚ), (724 / 1 : ℚ)⟩
theorem C_fast_21_arrival_valid : C_fast_21_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_21_arrival]

def C_fast_21_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_21_b_after_valid : C_fast_21_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_21_b_after]

def C_fast_21_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_21_gain_after_valid : C_fast_21_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_21_gain_after]

def C_fast_21_emission : RationalBox := ⟨(379714229 / 524288 : ℚ), (759428465 / 1048576 : ℚ)⟩
theorem C_fast_21_emission_valid : C_fast_21_emission.Valid := by norm_num [RationalBox.Valid, C_fast_21_emission]

def B_fast_21_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_aux_separation_left_valid : B_fast_21_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_aux_separation_left]

def B_fast_21_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_21_aux_separation_right_valid : B_fast_21_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_aux_separation_right]

def B_fast_21_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_gain_below_cap_left_valid : B_fast_21_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_gain_below_cap_left]

def B_fast_21_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_fast_21_gain_below_cap_right_valid : B_fast_21_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_gain_below_cap_right]

def B_fast_21_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_21_ready_at_input_left_valid : B_fast_21_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_ready_at_input_left]

def B_fast_21_ready_at_input_right : RationalBox := ⟨(2412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2206782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_ready_at_input_right_valid : B_fast_21_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_ready_at_input_right]

def B_fast_21_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_21_positive_derivative_coefficient_left_valid : B_fast_21_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_positive_derivative_coefficient_left]

def B_fast_21_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_positive_derivative_coefficient_right_valid : B_fast_21_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_positive_derivative_coefficient_right]

def B_fast_21_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_21_fixed_flow_increases_left_valid : B_fast_21_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_fixed_flow_increases_left]

def B_fast_21_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_fixed_flow_increases_right_valid : B_fast_21_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_fixed_flow_increases_right]

def B_fast_21_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_21_strong_crosses_by_one_left_valid : B_fast_21_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_strong_crosses_by_one_left]

def B_fast_21_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_strong_crosses_by_one_right_valid : B_fast_21_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_strong_crosses_by_one_right]

def B_fast_21_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_21_root_latency_valid : B_fast_21_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_21_root_latency]

def B_fast_21_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_root_lower_left_valid : B_fast_21_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_root_lower_left]

def B_fast_21_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_21_root_lower_right_valid : B_fast_21_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_root_lower_right]

def B_fast_21_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_21_root_upper_left_valid : B_fast_21_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_root_upper_left]

def B_fast_21_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_root_upper_right_valid : B_fast_21_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_root_upper_right]

def B_fast_21_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_MARK_before_fire_left_valid : B_fast_21_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_MARK_before_fire_left]

def B_fast_21_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_21_MARK_before_fire_right_valid : B_fast_21_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_MARK_before_fire_right]

def B_fast_21_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_21_fire_before_ERROR_left_valid : B_fast_21_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_fire_before_ERROR_left]

def B_fast_21_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_fire_before_ERROR_right_valid : B_fast_21_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_fire_before_ERROR_right]

def B_fast_21_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_ERROR_protected_left_valid : B_fast_21_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_21_ERROR_protected_left]

def B_fast_21_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_ERROR_protected_right_valid : B_fast_21_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_21_ERROR_protected_right]

def B_fast_21_arrival : RationalBox := ⟨(1899357577 / 2621440 : ℚ), (3799239477 / 5242880 : ℚ)⟩
theorem B_fast_21_arrival_valid : B_fast_21_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_21_arrival]

def B_fast_21_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_21_b_after_valid : B_fast_21_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_21_b_after]

def B_fast_21_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_21_gain_after_valid : B_fast_21_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_21_gain_after]

def B_fast_21_emission : RationalBox := ⟨(950003081 / 1310720 : ℚ), (1900268341 / 2621440 : ℚ)⟩
theorem B_fast_21_emission_valid : B_fast_21_emission.Valid := by norm_num [RationalBox.Valid, B_fast_21_emission]

def A_fast_21_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_aux_separation_left_valid : A_fast_21_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_aux_separation_left]

def A_fast_21_aux_separation_right : RationalBox := ⟨(19 / 5 : ℚ), (21 / 5 : ℚ)⟩
theorem A_fast_21_aux_separation_right_valid : A_fast_21_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_aux_separation_right]

def A_fast_21_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_gain_below_cap_left_valid : A_fast_21_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_gain_below_cap_left]

def A_fast_21_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_21_gain_below_cap_right_valid : A_fast_21_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_gain_below_cap_right]

def A_fast_21_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_21_ready_at_input_left_valid : A_fast_21_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_ready_at_input_left]

def A_fast_21_ready_at_input_right : RationalBox := ⟨(1412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_ready_at_input_right_valid : A_fast_21_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_ready_at_input_right]

def A_fast_21_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_21_positive_derivative_coefficient_left_valid : A_fast_21_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_positive_derivative_coefficient_left]

def A_fast_21_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_positive_derivative_coefficient_right_valid : A_fast_21_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_positive_derivative_coefficient_right]

def A_fast_21_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_21_fixed_flow_increases_left_valid : A_fast_21_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_fixed_flow_increases_left]

def A_fast_21_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_fixed_flow_increases_right_valid : A_fast_21_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_fixed_flow_increases_right]

def A_fast_21_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_21_strong_crosses_by_one_left_valid : A_fast_21_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_strong_crosses_by_one_left]

def A_fast_21_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_strong_crosses_by_one_right_valid : A_fast_21_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_strong_crosses_by_one_right]

def A_fast_21_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_21_root_latency_valid : A_fast_21_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_21_root_latency]

def A_fast_21_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_root_lower_left_valid : A_fast_21_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_root_lower_left]

def A_fast_21_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_21_root_lower_right_valid : A_fast_21_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_root_lower_right]

def A_fast_21_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_21_root_upper_left_valid : A_fast_21_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_root_upper_left]

def A_fast_21_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_root_upper_right_valid : A_fast_21_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_root_upper_right]

def A_fast_21_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_MARK_before_fire_left_valid : A_fast_21_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_MARK_before_fire_left]

def A_fast_21_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem A_fast_21_MARK_before_fire_right_valid : A_fast_21_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_MARK_before_fire_right]

def A_fast_21_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_21_fire_before_ERROR_left_valid : A_fast_21_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_fire_before_ERROR_left]

def A_fast_21_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_fire_before_ERROR_right_valid : A_fast_21_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_fire_before_ERROR_right]

def A_fast_21_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_ERROR_protected_left_valid : A_fast_21_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_21_ERROR_protected_left]

def A_fast_21_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_ERROR_protected_right_valid : A_fast_21_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_21_ERROR_protected_right]

def A_fast_21_arrival : RationalBox := ⟨(950396297 / 1310720 : ℚ), (1901316917 / 2621440 : ℚ)⟩
theorem A_fast_21_arrival_valid : A_fast_21_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_21_arrival]

def A_fast_21_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_21_b_after_valid : A_fast_21_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_21_b_after]

def A_fast_21_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_21_gain_after_valid : A_fast_21_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_21_gain_after]

def A_fast_21_emission : RationalBox := ⟨(1901441179 / 2621440 : ℚ), (3803931039 / 5242880 : ℚ)⟩
theorem A_fast_21_emission_valid : A_fast_21_emission.Valid := by norm_num [RationalBox.Valid, A_fast_21_emission]

def Bounds13Valid : Prop :=
  C_fast_20_gain_below_cap_left.Valid ∧
  C_fast_20_gain_below_cap_right.Valid ∧
  C_fast_20_ready_at_input_left.Valid ∧
  C_fast_20_ready_at_input_right.Valid ∧
  C_fast_20_positive_derivative_coefficient_left.Valid ∧
  C_fast_20_positive_derivative_coefficient_right.Valid ∧
  C_fast_20_fixed_flow_increases_left.Valid ∧
  C_fast_20_fixed_flow_increases_right.Valid ∧
  C_fast_20_strong_crosses_by_one_left.Valid ∧
  C_fast_20_strong_crosses_by_one_right.Valid ∧
  C_fast_20_root_latency.Valid ∧
  C_fast_20_root_lower_left.Valid ∧
  C_fast_20_root_lower_right.Valid ∧
  C_fast_20_root_upper_left.Valid ∧
  C_fast_20_root_upper_right.Valid ∧
  C_fast_20_MARK_before_fire_left.Valid ∧
  C_fast_20_MARK_before_fire_right.Valid ∧
  C_fast_20_fire_before_ERROR_left.Valid ∧
  C_fast_20_fire_before_ERROR_right.Valid ∧
  C_fast_20_ERROR_protected_left.Valid ∧
  C_fast_20_ERROR_protected_right.Valid ∧
  C_fast_20_arrival.Valid ∧
  C_fast_20_b_after.Valid ∧
  C_fast_20_gain_after.Valid ∧
  C_fast_20_emission.Valid ∧
  B_fast_20_aux_separation_left.Valid ∧
  B_fast_20_aux_separation_right.Valid ∧
  B_fast_20_gain_below_cap_left.Valid ∧
  B_fast_20_gain_below_cap_right.Valid ∧
  B_fast_20_ready_at_input_left.Valid ∧
  B_fast_20_ready_at_input_right.Valid ∧
  B_fast_20_positive_derivative_coefficient_left.Valid ∧
  B_fast_20_positive_derivative_coefficient_right.Valid ∧
  B_fast_20_fixed_flow_increases_left.Valid ∧
  B_fast_20_fixed_flow_increases_right.Valid ∧
  B_fast_20_strong_crosses_by_one_left.Valid ∧
  B_fast_20_strong_crosses_by_one_right.Valid ∧
  B_fast_20_root_latency.Valid ∧
  B_fast_20_root_lower_left.Valid ∧
  B_fast_20_root_lower_right.Valid ∧
  B_fast_20_root_upper_left.Valid ∧
  B_fast_20_root_upper_right.Valid ∧
  B_fast_20_MARK_before_fire_left.Valid ∧
  B_fast_20_MARK_before_fire_right.Valid ∧
  B_fast_20_fire_before_ERROR_left.Valid ∧
  B_fast_20_fire_before_ERROR_right.Valid ∧
  B_fast_20_ERROR_protected_left.Valid ∧
  B_fast_20_ERROR_protected_right.Valid ∧
  B_fast_20_arrival.Valid ∧
  B_fast_20_b_after.Valid ∧
  B_fast_20_gain_after.Valid ∧
  B_fast_20_emission.Valid ∧
  A_fast_20_aux_separation_left.Valid ∧
  A_fast_20_aux_separation_right.Valid ∧
  A_fast_20_gain_below_cap_left.Valid ∧
  A_fast_20_gain_below_cap_right.Valid ∧
  A_fast_20_ready_at_input_left.Valid ∧
  A_fast_20_ready_at_input_right.Valid ∧
  A_fast_20_positive_derivative_coefficient_left.Valid ∧
  A_fast_20_positive_derivative_coefficient_right.Valid ∧
  A_fast_20_fixed_flow_increases_left.Valid ∧
  A_fast_20_fixed_flow_increases_right.Valid ∧
  A_fast_20_strong_crosses_by_one_left.Valid ∧
  A_fast_20_strong_crosses_by_one_right.Valid ∧
  A_fast_20_root_latency.Valid ∧
  A_fast_20_root_lower_left.Valid ∧
  A_fast_20_root_lower_right.Valid ∧
  A_fast_20_root_upper_left.Valid ∧
  A_fast_20_root_upper_right.Valid ∧
  A_fast_20_MARK_before_fire_left.Valid ∧
  A_fast_20_MARK_before_fire_right.Valid ∧
  A_fast_20_fire_before_ERROR_left.Valid ∧
  A_fast_20_fire_before_ERROR_right.Valid ∧
  A_fast_20_ERROR_protected_left.Valid ∧
  A_fast_20_ERROR_protected_right.Valid ∧
  A_fast_20_arrival.Valid ∧
  A_fast_20_b_after.Valid ∧
  A_fast_20_gain_after.Valid ∧
  A_fast_20_emission.Valid ∧
  C_fast_21_aux_separation_left.Valid ∧
  C_fast_21_aux_separation_right.Valid ∧
  C_fast_21_gain_below_cap_left.Valid ∧
  C_fast_21_gain_below_cap_right.Valid ∧
  C_fast_21_ready_at_input_left.Valid ∧
  C_fast_21_ready_at_input_right.Valid ∧
  C_fast_21_positive_derivative_coefficient_left.Valid ∧
  C_fast_21_positive_derivative_coefficient_right.Valid ∧
  C_fast_21_fixed_flow_increases_left.Valid ∧
  C_fast_21_fixed_flow_increases_right.Valid ∧
  C_fast_21_strong_crosses_by_one_left.Valid ∧
  C_fast_21_strong_crosses_by_one_right.Valid ∧
  C_fast_21_root_latency.Valid ∧
  C_fast_21_root_lower_left.Valid ∧
  C_fast_21_root_lower_right.Valid ∧
  C_fast_21_root_upper_left.Valid ∧
  C_fast_21_root_upper_right.Valid ∧
  C_fast_21_MARK_before_fire_left.Valid ∧
  C_fast_21_MARK_before_fire_right.Valid ∧
  C_fast_21_fire_before_ERROR_left.Valid ∧
  C_fast_21_fire_before_ERROR_right.Valid ∧
  C_fast_21_ERROR_protected_left.Valid ∧
  C_fast_21_ERROR_protected_right.Valid ∧
  C_fast_21_arrival.Valid ∧
  C_fast_21_b_after.Valid ∧
  C_fast_21_gain_after.Valid ∧
  C_fast_21_emission.Valid ∧
  B_fast_21_aux_separation_left.Valid ∧
  B_fast_21_aux_separation_right.Valid ∧
  B_fast_21_gain_below_cap_left.Valid ∧
  B_fast_21_gain_below_cap_right.Valid ∧
  B_fast_21_ready_at_input_left.Valid ∧
  B_fast_21_ready_at_input_right.Valid ∧
  B_fast_21_positive_derivative_coefficient_left.Valid ∧
  B_fast_21_positive_derivative_coefficient_right.Valid ∧
  B_fast_21_fixed_flow_increases_left.Valid ∧
  B_fast_21_fixed_flow_increases_right.Valid ∧
  B_fast_21_strong_crosses_by_one_left.Valid ∧
  B_fast_21_strong_crosses_by_one_right.Valid ∧
  B_fast_21_root_latency.Valid ∧
  B_fast_21_root_lower_left.Valid ∧
  B_fast_21_root_lower_right.Valid ∧
  B_fast_21_root_upper_left.Valid ∧
  B_fast_21_root_upper_right.Valid ∧
  B_fast_21_MARK_before_fire_left.Valid ∧
  B_fast_21_MARK_before_fire_right.Valid ∧
  B_fast_21_fire_before_ERROR_left.Valid ∧
  B_fast_21_fire_before_ERROR_right.Valid ∧
  B_fast_21_ERROR_protected_left.Valid ∧
  B_fast_21_ERROR_protected_right.Valid ∧
  B_fast_21_arrival.Valid ∧
  B_fast_21_b_after.Valid ∧
  B_fast_21_gain_after.Valid ∧
  B_fast_21_emission.Valid ∧
  A_fast_21_aux_separation_left.Valid ∧
  A_fast_21_aux_separation_right.Valid ∧
  A_fast_21_gain_below_cap_left.Valid ∧
  A_fast_21_gain_below_cap_right.Valid ∧
  A_fast_21_ready_at_input_left.Valid ∧
  A_fast_21_ready_at_input_right.Valid ∧
  A_fast_21_positive_derivative_coefficient_left.Valid ∧
  A_fast_21_positive_derivative_coefficient_right.Valid ∧
  A_fast_21_fixed_flow_increases_left.Valid ∧
  A_fast_21_fixed_flow_increases_right.Valid ∧
  A_fast_21_strong_crosses_by_one_left.Valid ∧
  A_fast_21_strong_crosses_by_one_right.Valid ∧
  A_fast_21_root_latency.Valid ∧
  A_fast_21_root_lower_left.Valid ∧
  A_fast_21_root_lower_right.Valid ∧
  A_fast_21_root_upper_left.Valid ∧
  A_fast_21_root_upper_right.Valid ∧
  A_fast_21_MARK_before_fire_left.Valid ∧
  A_fast_21_MARK_before_fire_right.Valid ∧
  A_fast_21_fire_before_ERROR_left.Valid ∧
  A_fast_21_fire_before_ERROR_right.Valid ∧
  A_fast_21_ERROR_protected_left.Valid ∧
  A_fast_21_ERROR_protected_right.Valid ∧
  A_fast_21_arrival.Valid ∧
  A_fast_21_b_after.Valid ∧
  A_fast_21_gain_after.Valid ∧
  A_fast_21_emission.Valid
theorem Bounds13Valid_verified : Bounds13Valid := by
  exact ⟨C_fast_20_gain_below_cap_left_valid, C_fast_20_gain_below_cap_right_valid, C_fast_20_ready_at_input_left_valid, C_fast_20_ready_at_input_right_valid, C_fast_20_positive_derivative_coefficient_left_valid, C_fast_20_positive_derivative_coefficient_right_valid, C_fast_20_fixed_flow_increases_left_valid, C_fast_20_fixed_flow_increases_right_valid, C_fast_20_strong_crosses_by_one_left_valid, C_fast_20_strong_crosses_by_one_right_valid, C_fast_20_root_latency_valid, C_fast_20_root_lower_left_valid, C_fast_20_root_lower_right_valid, C_fast_20_root_upper_left_valid, C_fast_20_root_upper_right_valid, C_fast_20_MARK_before_fire_left_valid, C_fast_20_MARK_before_fire_right_valid, C_fast_20_fire_before_ERROR_left_valid, C_fast_20_fire_before_ERROR_right_valid, C_fast_20_ERROR_protected_left_valid, C_fast_20_ERROR_protected_right_valid, C_fast_20_arrival_valid, C_fast_20_b_after_valid, C_fast_20_gain_after_valid, C_fast_20_emission_valid, B_fast_20_aux_separation_left_valid, B_fast_20_aux_separation_right_valid, B_fast_20_gain_below_cap_left_valid, B_fast_20_gain_below_cap_right_valid, B_fast_20_ready_at_input_left_valid, B_fast_20_ready_at_input_right_valid, B_fast_20_positive_derivative_coefficient_left_valid, B_fast_20_positive_derivative_coefficient_right_valid, B_fast_20_fixed_flow_increases_left_valid, B_fast_20_fixed_flow_increases_right_valid, B_fast_20_strong_crosses_by_one_left_valid, B_fast_20_strong_crosses_by_one_right_valid, B_fast_20_root_latency_valid, B_fast_20_root_lower_left_valid, B_fast_20_root_lower_right_valid, B_fast_20_root_upper_left_valid, B_fast_20_root_upper_right_valid, B_fast_20_MARK_before_fire_left_valid, B_fast_20_MARK_before_fire_right_valid, B_fast_20_fire_before_ERROR_left_valid, B_fast_20_fire_before_ERROR_right_valid, B_fast_20_ERROR_protected_left_valid, B_fast_20_ERROR_protected_right_valid, B_fast_20_arrival_valid, B_fast_20_b_after_valid, B_fast_20_gain_after_valid, B_fast_20_emission_valid, A_fast_20_aux_separation_left_valid, A_fast_20_aux_separation_right_valid, A_fast_20_gain_below_cap_left_valid, A_fast_20_gain_below_cap_right_valid, A_fast_20_ready_at_input_left_valid, A_fast_20_ready_at_input_right_valid, A_fast_20_positive_derivative_coefficient_left_valid, A_fast_20_positive_derivative_coefficient_right_valid, A_fast_20_fixed_flow_increases_left_valid, A_fast_20_fixed_flow_increases_right_valid, A_fast_20_strong_crosses_by_one_left_valid, A_fast_20_strong_crosses_by_one_right_valid, A_fast_20_root_latency_valid, A_fast_20_root_lower_left_valid, A_fast_20_root_lower_right_valid, A_fast_20_root_upper_left_valid, A_fast_20_root_upper_right_valid, A_fast_20_MARK_before_fire_left_valid, A_fast_20_MARK_before_fire_right_valid, A_fast_20_fire_before_ERROR_left_valid, A_fast_20_fire_before_ERROR_right_valid, A_fast_20_ERROR_protected_left_valid, A_fast_20_ERROR_protected_right_valid, A_fast_20_arrival_valid, A_fast_20_b_after_valid, A_fast_20_gain_after_valid, A_fast_20_emission_valid, C_fast_21_aux_separation_left_valid, C_fast_21_aux_separation_right_valid, C_fast_21_gain_below_cap_left_valid, C_fast_21_gain_below_cap_right_valid, C_fast_21_ready_at_input_left_valid, C_fast_21_ready_at_input_right_valid, C_fast_21_positive_derivative_coefficient_left_valid, C_fast_21_positive_derivative_coefficient_right_valid, C_fast_21_fixed_flow_increases_left_valid, C_fast_21_fixed_flow_increases_right_valid, C_fast_21_strong_crosses_by_one_left_valid, C_fast_21_strong_crosses_by_one_right_valid, C_fast_21_root_latency_valid, C_fast_21_root_lower_left_valid, C_fast_21_root_lower_right_valid, C_fast_21_root_upper_left_valid, C_fast_21_root_upper_right_valid, C_fast_21_MARK_before_fire_left_valid, C_fast_21_MARK_before_fire_right_valid, C_fast_21_fire_before_ERROR_left_valid, C_fast_21_fire_before_ERROR_right_valid, C_fast_21_ERROR_protected_left_valid, C_fast_21_ERROR_protected_right_valid, C_fast_21_arrival_valid, C_fast_21_b_after_valid, C_fast_21_gain_after_valid, C_fast_21_emission_valid, B_fast_21_aux_separation_left_valid, B_fast_21_aux_separation_right_valid, B_fast_21_gain_below_cap_left_valid, B_fast_21_gain_below_cap_right_valid, B_fast_21_ready_at_input_left_valid, B_fast_21_ready_at_input_right_valid, B_fast_21_positive_derivative_coefficient_left_valid, B_fast_21_positive_derivative_coefficient_right_valid, B_fast_21_fixed_flow_increases_left_valid, B_fast_21_fixed_flow_increases_right_valid, B_fast_21_strong_crosses_by_one_left_valid, B_fast_21_strong_crosses_by_one_right_valid, B_fast_21_root_latency_valid, B_fast_21_root_lower_left_valid, B_fast_21_root_lower_right_valid, B_fast_21_root_upper_left_valid, B_fast_21_root_upper_right_valid, B_fast_21_MARK_before_fire_left_valid, B_fast_21_MARK_before_fire_right_valid, B_fast_21_fire_before_ERROR_left_valid, B_fast_21_fire_before_ERROR_right_valid, B_fast_21_ERROR_protected_left_valid, B_fast_21_ERROR_protected_right_valid, B_fast_21_arrival_valid, B_fast_21_b_after_valid, B_fast_21_gain_after_valid, B_fast_21_emission_valid, A_fast_21_aux_separation_left_valid, A_fast_21_aux_separation_right_valid, A_fast_21_gain_below_cap_left_valid, A_fast_21_gain_below_cap_right_valid, A_fast_21_ready_at_input_left_valid, A_fast_21_ready_at_input_right_valid, A_fast_21_positive_derivative_coefficient_left_valid, A_fast_21_positive_derivative_coefficient_right_valid, A_fast_21_fixed_flow_increases_left_valid, A_fast_21_fixed_flow_increases_right_valid, A_fast_21_strong_crosses_by_one_left_valid, A_fast_21_strong_crosses_by_one_right_valid, A_fast_21_root_latency_valid, A_fast_21_root_lower_left_valid, A_fast_21_root_lower_right_valid, A_fast_21_root_upper_left_valid, A_fast_21_root_upper_right_valid, A_fast_21_MARK_before_fire_left_valid, A_fast_21_MARK_before_fire_right_valid, A_fast_21_fire_before_ERROR_left_valid, A_fast_21_fire_before_ERROR_right_valid, A_fast_21_ERROR_protected_left_valid, A_fast_21_ERROR_protected_right_valid, A_fast_21_arrival_valid, A_fast_21_b_after_valid, A_fast_21_gain_after_valid, A_fast_21_emission_valid⟩

end KernelR.Certificates.Cadence003
