import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def A_fast_23_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_23_gain_after_valid : A_fast_23_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_23_gain_after]

def A_fast_23_emission : RationalBox := ⟨(1922412699 / 2621440 : ℚ), (3845874079 / 5242880 : ℚ)⟩
theorem A_fast_23_emission_valid : A_fast_23_emission.Valid := by norm_num [RationalBox.Valid, A_fast_23_emission]

def C_fast_24_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_aux_separation_left_valid : C_fast_24_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_aux_separation_left]

def C_fast_24_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_24_aux_separation_right_valid : C_fast_24_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_aux_separation_right]

def C_fast_24_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_gain_below_cap_left_valid : C_fast_24_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_gain_below_cap_left]

def C_fast_24_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem C_fast_24_gain_below_cap_right_valid : C_fast_24_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_gain_below_cap_right]

def C_fast_24_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_24_ready_at_input_left_valid : C_fast_24_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_ready_at_input_left]

def C_fast_24_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_ready_at_input_right_valid : C_fast_24_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_ready_at_input_right]

def C_fast_24_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_24_positive_derivative_coefficient_left_valid : C_fast_24_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_positive_derivative_coefficient_left]

def C_fast_24_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_positive_derivative_coefficient_right_valid : C_fast_24_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_positive_derivative_coefficient_right]

def C_fast_24_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_24_fixed_flow_increases_left_valid : C_fast_24_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_fixed_flow_increases_left]

def C_fast_24_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_fixed_flow_increases_right_valid : C_fast_24_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_fixed_flow_increases_right]

def C_fast_24_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_24_strong_crosses_by_one_left_valid : C_fast_24_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_strong_crosses_by_one_left]

def C_fast_24_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_strong_crosses_by_one_right_valid : C_fast_24_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_strong_crosses_by_one_right]

def C_fast_24_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_24_root_latency_valid : C_fast_24_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_24_root_latency]

def C_fast_24_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_root_lower_left_valid : C_fast_24_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_root_lower_left]

def C_fast_24_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_24_root_lower_right_valid : C_fast_24_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_root_lower_right]

def C_fast_24_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_24_root_upper_left_valid : C_fast_24_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_root_upper_left]

def C_fast_24_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_root_upper_right_valid : C_fast_24_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_root_upper_right]

def C_fast_24_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_MARK_before_fire_left_valid : C_fast_24_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_MARK_before_fire_left]

def C_fast_24_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_24_MARK_before_fire_right_valid : C_fast_24_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_MARK_before_fire_right]

def C_fast_24_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_24_fire_before_ERROR_left_valid : C_fast_24_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_fire_before_ERROR_left]

def C_fast_24_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_fire_before_ERROR_right_valid : C_fast_24_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_fire_before_ERROR_right]

def C_fast_24_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_ERROR_protected_left_valid : C_fast_24_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_24_ERROR_protected_left]

def C_fast_24_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_ERROR_protected_right_valid : C_fast_24_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_24_ERROR_protected_right]

def C_fast_24_arrival : RationalBox := ⟨(736 / 1 : ℚ), (736 / 1 : ℚ)⟩
theorem C_fast_24_arrival_valid : C_fast_24_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_24_arrival]

def C_fast_24_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_24_b_after_valid : C_fast_24_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_24_b_after]

def C_fast_24_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_24_gain_after_valid : C_fast_24_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_24_gain_after]

def C_fast_24_emission : RationalBox := ⟨(386005685 / 524288 : ℚ), (772011377 / 1048576 : ℚ)⟩
theorem C_fast_24_emission_valid : C_fast_24_emission.Valid := by norm_num [RationalBox.Valid, C_fast_24_emission]

def B_fast_24_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_aux_separation_left_valid : B_fast_24_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_aux_separation_left]

def B_fast_24_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_24_aux_separation_right_valid : B_fast_24_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_aux_separation_right]

def B_fast_24_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_gain_below_cap_left_valid : B_fast_24_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_gain_below_cap_left]

def B_fast_24_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_fast_24_gain_below_cap_right_valid : B_fast_24_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_gain_below_cap_right]

def B_fast_24_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_24_ready_at_input_left_valid : B_fast_24_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_ready_at_input_left]

def B_fast_24_ready_at_input_right : RationalBox := ⟨(2412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2206782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_ready_at_input_right_valid : B_fast_24_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_ready_at_input_right]

def B_fast_24_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_24_positive_derivative_coefficient_left_valid : B_fast_24_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_positive_derivative_coefficient_left]

def B_fast_24_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_positive_derivative_coefficient_right_valid : B_fast_24_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_positive_derivative_coefficient_right]

def B_fast_24_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_24_fixed_flow_increases_left_valid : B_fast_24_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_fixed_flow_increases_left]

def B_fast_24_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_fixed_flow_increases_right_valid : B_fast_24_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_fixed_flow_increases_right]

def B_fast_24_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_24_strong_crosses_by_one_left_valid : B_fast_24_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_strong_crosses_by_one_left]

def B_fast_24_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_strong_crosses_by_one_right_valid : B_fast_24_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_strong_crosses_by_one_right]

def B_fast_24_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_24_root_latency_valid : B_fast_24_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_24_root_latency]

def B_fast_24_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_root_lower_left_valid : B_fast_24_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_root_lower_left]

def B_fast_24_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_24_root_lower_right_valid : B_fast_24_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_root_lower_right]

def B_fast_24_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_24_root_upper_left_valid : B_fast_24_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_root_upper_left]

def B_fast_24_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_root_upper_right_valid : B_fast_24_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_root_upper_right]

def B_fast_24_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_MARK_before_fire_left_valid : B_fast_24_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_MARK_before_fire_left]

def B_fast_24_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_24_MARK_before_fire_right_valid : B_fast_24_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_MARK_before_fire_right]

def B_fast_24_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_24_fire_before_ERROR_left_valid : B_fast_24_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_fire_before_ERROR_left]

def B_fast_24_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_fire_before_ERROR_right_valid : B_fast_24_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_fire_before_ERROR_right]

def B_fast_24_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_ERROR_protected_left_valid : B_fast_24_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_24_ERROR_protected_left]

def B_fast_24_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_ERROR_protected_right_valid : B_fast_24_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_24_ERROR_protected_right]

def B_fast_24_arrival : RationalBox := ⟨(1930814857 / 2621440 : ℚ), (3862154037 / 5242880 : ℚ)⟩
theorem B_fast_24_arrival_valid : B_fast_24_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_24_arrival]

def B_fast_24_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_24_b_after_valid : B_fast_24_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_24_b_after]

def B_fast_24_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_24_gain_after_valid : B_fast_24_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_24_gain_after]

def B_fast_24_emission : RationalBox := ⟨(965731721 / 1310720 : ℚ), (1931725621 / 2621440 : ℚ)⟩
theorem B_fast_24_emission_valid : B_fast_24_emission.Valid := by norm_num [RationalBox.Valid, B_fast_24_emission]

def A_fast_24_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_aux_separation_left_valid : A_fast_24_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_aux_separation_left]

def A_fast_24_aux_separation_right : RationalBox := ⟨(19 / 5 : ℚ), (21 / 5 : ℚ)⟩
theorem A_fast_24_aux_separation_right_valid : A_fast_24_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_aux_separation_right]

def A_fast_24_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_gain_below_cap_left_valid : A_fast_24_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_gain_below_cap_left]

def A_fast_24_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem A_fast_24_gain_below_cap_right_valid : A_fast_24_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_gain_below_cap_right]

def A_fast_24_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_24_ready_at_input_left_valid : A_fast_24_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_ready_at_input_left]

def A_fast_24_ready_at_input_right : RationalBox := ⟨(1412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_ready_at_input_right_valid : A_fast_24_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_ready_at_input_right]

def A_fast_24_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_24_positive_derivative_coefficient_left_valid : A_fast_24_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_positive_derivative_coefficient_left]

def A_fast_24_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_positive_derivative_coefficient_right_valid : A_fast_24_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_positive_derivative_coefficient_right]

def A_fast_24_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_24_fixed_flow_increases_left_valid : A_fast_24_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_fixed_flow_increases_left]

def A_fast_24_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_fixed_flow_increases_right_valid : A_fast_24_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_fixed_flow_increases_right]

def A_fast_24_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_24_strong_crosses_by_one_left_valid : A_fast_24_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_strong_crosses_by_one_left]

def A_fast_24_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_strong_crosses_by_one_right_valid : A_fast_24_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_strong_crosses_by_one_right]

def A_fast_24_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_24_root_latency_valid : A_fast_24_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_24_root_latency]

def A_fast_24_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_root_lower_left_valid : A_fast_24_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_root_lower_left]

def A_fast_24_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_24_root_lower_right_valid : A_fast_24_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_root_lower_right]

def A_fast_24_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_24_root_upper_left_valid : A_fast_24_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_root_upper_left]

def A_fast_24_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_root_upper_right_valid : A_fast_24_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_root_upper_right]

def A_fast_24_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_MARK_before_fire_left_valid : A_fast_24_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_MARK_before_fire_left]

def A_fast_24_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem A_fast_24_MARK_before_fire_right_valid : A_fast_24_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_MARK_before_fire_right]

def A_fast_24_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_24_fire_before_ERROR_left_valid : A_fast_24_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_fire_before_ERROR_left]

def A_fast_24_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_fire_before_ERROR_right_valid : A_fast_24_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_fire_before_ERROR_right]

def A_fast_24_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_ERROR_protected_left_valid : A_fast_24_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_24_ERROR_protected_left]

def A_fast_24_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_ERROR_protected_right_valid : A_fast_24_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_24_ERROR_protected_right]

def A_fast_24_arrival : RationalBox := ⟨(966124937 / 1310720 : ℚ), (1932774197 / 2621440 : ℚ)⟩
theorem A_fast_24_arrival_valid : A_fast_24_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_24_arrival]

def A_fast_24_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_24_b_after_valid : A_fast_24_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_24_b_after]

def A_fast_24_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_24_gain_after_valid : A_fast_24_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_24_gain_after]

def A_fast_24_emission : RationalBox := ⟨(1932898459 / 2621440 : ℚ), (3866845599 / 5242880 : ℚ)⟩
theorem A_fast_24_emission_valid : A_fast_24_emission.Valid := by norm_num [RationalBox.Valid, A_fast_24_emission]

def A_quiescent_at_measurement_left : RationalBox := ⟨(3703767372870547191818707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (7409536215113438375633341396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_quiescent_at_measurement_left_valid : A_quiescent_at_measurement_left.Valid := by norm_num [RationalBox.Valid, A_quiescent_at_measurement_left]

def A_quiescent_at_measurement_right : RationalBox := ⟨(7899 / 10 : ℚ), (7899 / 10 : ℚ)⟩
theorem A_quiescent_at_measurement_right_valid : A_quiescent_at_measurement_right.Valid := by norm_num [RationalBox.Valid, A_quiescent_at_measurement_right]

def A_last_emission_inside_fast_gate_left : RationalBox := ⟨(1932898459 / 2621440 : ℚ), (3866845599 / 5242880 : ℚ)⟩
theorem A_last_emission_inside_fast_gate_left_valid : A_last_emission_inside_fast_gate_left.Valid := by norm_num [RationalBox.Valid, A_last_emission_inside_fast_gate_left]

def A_last_emission_inside_fast_gate_right : RationalBox := ⟨(780 / 1 : ℚ), (780 / 1 : ℚ)⟩
theorem A_last_emission_inside_fast_gate_right_valid : A_last_emission_inside_fast_gate_right.Valid := by norm_num [RationalBox.Valid, A_last_emission_inside_fast_gate_right]

def A_final_b : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_final_b_valid : A_final_b.Valid := by norm_num [RationalBox.Valid, A_final_b]

def A_final_gain : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_final_gain_valid : A_final_gain.Valid := by norm_num [RationalBox.Valid, A_final_gain]

def A_final_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_final_gain_below_cap_left_valid : A_final_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_final_gain_below_cap_left]

def A_final_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem A_final_gain_below_cap_right_valid : A_final_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_final_gain_below_cap_right]

def B_quiescent_at_measurement_left : RationalBox := ⟨(3701030295157534496506207431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (7403061992930210836570841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_quiescent_at_measurement_left_valid : B_quiescent_at_measurement_left.Valid := by norm_num [RationalBox.Valid, B_quiescent_at_measurement_left]

def B_quiescent_at_measurement_right : RationalBox := ⟨(7899 / 10 : ℚ), (7899 / 10 : ℚ)⟩
theorem B_quiescent_at_measurement_right_valid : B_quiescent_at_measurement_right.Valid := by norm_num [RationalBox.Valid, B_quiescent_at_measurement_right]

def B_last_emission_inside_fast_gate_left : RationalBox := ⟨(965731721 / 1310720 : ℚ), (1931725621 / 2621440 : ℚ)⟩
theorem B_last_emission_inside_fast_gate_left_valid : B_last_emission_inside_fast_gate_left.Valid := by norm_num [RationalBox.Valid, B_last_emission_inside_fast_gate_left]

def B_last_emission_inside_fast_gate_right : RationalBox := ⟨(780 / 1 : ℚ), (780 / 1 : ℚ)⟩
theorem B_last_emission_inside_fast_gate_right_valid : B_last_emission_inside_fast_gate_right.Valid := by norm_num [RationalBox.Valid, B_last_emission_inside_fast_gate_right]

def B_final_b : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_final_b_valid : B_final_b.Valid := by norm_num [RationalBox.Valid, B_final_b]

def B_final_gain : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_final_gain_valid : B_final_gain.Valid := by norm_num [RationalBox.Valid, B_final_gain]

def B_final_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_final_gain_below_cap_left_valid : B_final_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_final_gain_below_cap_left]

def B_final_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_final_gain_below_cap_right_valid : B_final_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_final_gain_below_cap_right]

def C_quiescent_at_measurement_left : RationalBox := ⟨(3698293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (7396587770746983297508341396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_quiescent_at_measurement_left_valid : C_quiescent_at_measurement_left.Valid := by norm_num [RationalBox.Valid, C_quiescent_at_measurement_left]

def C_quiescent_at_measurement_right : RationalBox := ⟨(7899 / 10 : ℚ), (7899 / 10 : ℚ)⟩
theorem C_quiescent_at_measurement_right_valid : C_quiescent_at_measurement_right.Valid := by norm_num [RationalBox.Valid, C_quiescent_at_measurement_right]

def C_last_emission_inside_fast_gate_left : RationalBox := ⟨(386005685 / 524288 : ℚ), (772011377 / 1048576 : ℚ)⟩
theorem C_last_emission_inside_fast_gate_left_valid : C_last_emission_inside_fast_gate_left.Valid := by norm_num [RationalBox.Valid, C_last_emission_inside_fast_gate_left]

def C_last_emission_inside_fast_gate_right : RationalBox := ⟨(780 / 1 : ℚ), (780 / 1 : ℚ)⟩
theorem C_last_emission_inside_fast_gate_right_valid : C_last_emission_inside_fast_gate_right.Valid := by norm_num [RationalBox.Valid, C_last_emission_inside_fast_gate_right]

def C_final_b : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_final_b_valid : C_final_b.Valid := by norm_num [RationalBox.Valid, C_final_b]

def C_final_gain : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_final_gain_valid : C_final_gain.Valid := by norm_num [RationalBox.Valid, C_final_gain]

def C_final_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_final_gain_below_cap_left_valid : C_final_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_final_gain_below_cap_left]

def C_final_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem C_final_gain_below_cap_right_valid : C_final_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_final_gain_below_cap_right]

def probe_before_root_lower_left : RationalBox := ⟨(998178201240310947902485726302510005149 / 1000000000000000000000000000000000000000 : ℚ), (9981961649839725919464288313052310149421 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_before_root_lower_left_valid : probe_before_root_lower_left.Valid := by norm_num [RationalBox.Valid, probe_before_root_lower_left]

def probe_before_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem probe_before_root_lower_right_valid : probe_before_root_lower_right.Valid := by norm_num [RationalBox.Valid, probe_before_root_lower_right]

def probe_before_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem probe_before_root_upper_left_valid : probe_before_root_upper_left.Valid := by norm_num [RationalBox.Valid, probe_before_root_upper_left]

def probe_before_root_upper_right : RationalBox := ⟨(1003820576896766608189493188295273519847 / 1000000000000000000000000000000000000000 : ℚ), (5019193267445349320005691617168449083861 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_before_root_upper_right_valid : probe_before_root_upper_right.Valid := by norm_num [RationalBox.Valid, probe_before_root_upper_right]

def probe_before_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem probe_before_flow_increases_left_valid : probe_before_flow_increases_left.Valid := by norm_num [RationalBox.Valid, probe_before_flow_increases_left]

def probe_before_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_before_flow_increases_right_valid : probe_before_flow_increases_right.Valid := by norm_num [RationalBox.Valid, probe_before_flow_increases_right]

def probe_before_return : RationalBox := ⟨(8425276594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67507868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_before_return_valid : probe_before_return.Valid := by norm_num [RationalBox.Valid, probe_before_return]

def probe_before_second_pulse_fully_protected_left : RationalBox := ⟨(5 / 1 : ℚ), (5 / 1 : ℚ)⟩
theorem probe_before_second_pulse_fully_protected_left_valid : probe_before_second_pulse_fully_protected_left.Valid := by norm_num [RationalBox.Valid, probe_before_second_pulse_fully_protected_left]

def probe_before_second_pulse_fully_protected_right : RationalBox := ⟨(8425276594870806241205538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67402212758966449929644309303261544994729 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_before_second_pulse_fully_protected_right_valid : probe_before_second_pulse_fully_protected_right.Valid := by norm_num [RationalBox.Valid, probe_before_second_pulse_fully_protected_right]

def probe_before_return_before_third_pulse_left : RationalBox := ⟨(33753934437306379942872582137007919091341 / 5000000000000000000000000000000000000000 : ℚ), (67507868874612759885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_before_return_before_third_pulse_left_valid : probe_before_return_before_third_pulse_left.Valid := by norm_num [RationalBox.Valid, probe_before_return_before_third_pulse_left]

def probe_before_return_before_third_pulse_right : RationalBox := ⟨(8 / 1 : ℚ), (8 / 1 : ℚ)⟩
theorem probe_before_return_before_third_pulse_right_valid : probe_before_return_before_third_pulse_right.Valid := by norm_num [RationalBox.Valid, probe_before_return_before_third_pulse_right]

def probe_after_root_lower_left : RationalBox := ⟨(9790304931478480597693570265572100652703 / 10000000000000000000000000000000000000000 : ℚ), (489524036966759143703319891422117957267 / 500000000000000000000000000000000000000 : ℚ)⟩
theorem probe_after_root_lower_left_valid : probe_after_root_lower_left.Valid := by norm_num [RationalBox.Valid, probe_after_root_lower_left]

def probe_after_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem probe_after_root_lower_right_valid : probe_after_root_lower_right.Valid := by norm_num [RationalBox.Valid, probe_after_root_lower_right]

def probe_after_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem probe_after_root_upper_left_valid : probe_after_root_upper_left.Valid := by norm_num [RationalBox.Valid, probe_after_root_upper_left]

def probe_after_root_upper_right : RationalBox := ⟨(2014413477662782087737588494001580679009 / 2000000000000000000000000000000000000000 : ℚ), (2014449766295220458141966018597367959459 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_after_root_upper_right_valid : probe_after_root_upper_right.Valid := by norm_num [RationalBox.Valid, probe_after_root_upper_right]

def probe_after_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem probe_after_flow_increases_left_valid : probe_after_flow_increases_left.Valid := by norm_num [RationalBox.Valid, probe_after_flow_increases_left]

def probe_after_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_after_flow_increases_right_valid : probe_after_flow_increases_right.Valid := by norm_num [RationalBox.Valid, probe_after_flow_increases_right]

def probe_after_return : RationalBox := ⟨(18256139731509105881207431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36613548563755758445841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_after_return_valid : probe_after_return.Valid := by norm_num [RationalBox.Valid, probe_after_return]

def probe_after_return_before_every_next_pulse_left : RationalBox := ⟨(457669357046946980573017451698732555939 / 125000000000000000000000000000000000000 : ℚ), (36613548563755758445841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_after_return_before_every_next_pulse_left_valid : probe_after_return_before_every_next_pulse_left.Valid := by norm_num [RationalBox.Valid, probe_after_return_before_every_next_pulse_left]

def probe_after_return_before_every_next_pulse_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem probe_after_return_before_every_next_pulse_right_valid : probe_after_return_before_every_next_pulse_right.Valid := by norm_num [RationalBox.Valid, probe_after_return_before_every_next_pulse_right]

def probe_C_before_positive_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem probe_C_before_positive_coefficient_left_valid : probe_C_before_positive_coefficient_left.Valid := by norm_num [RationalBox.Valid, probe_C_before_positive_coefficient_left]

def probe_C_before_positive_coefficient_right : RationalBox := ⟨(234619652182025324597025620160078202879 / 1000000000000000000000000000000000000000 : ℚ), (586560861554983020919224180575194350001 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem probe_C_before_positive_coefficient_right_valid : probe_C_before_positive_coefficient_right.Valid := by norm_num [RationalBox.Valid, probe_C_before_positive_coefficient_right]

def probe_C_before_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem probe_C_before_flow_increases_left_valid : probe_C_before_flow_increases_left.Valid := by norm_num [RationalBox.Valid, probe_C_before_flow_increases_left]

def probe_C_before_flow_increases_right : RationalBox := ⟨(72262701797365403720056619589354882941 / 2500000000000000000000000000000000000000 : ℚ), (289305227751807229853387545682035567811 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_C_before_flow_increases_right_valid : probe_C_before_flow_increases_right.Valid := by norm_num [RationalBox.Valid, probe_C_before_flow_increases_right]

def probe_C_before_no_firing_even_in_infinite_train_left : RationalBox := ⟨(2934833184523160954196053880940963649213 / 10000000000000000000000000000000000000000 : ℚ), (293487188157382063411024829656494348539 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem probe_C_before_no_firing_even_in_infinite_train_left_valid : probe_C_before_no_firing_even_in_infinite_train_left.Valid := by norm_num [RationalBox.Valid, probe_C_before_no_firing_even_in_infinite_train_left]

def probe_C_before_no_firing_even_in_infinite_train_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem probe_C_before_no_firing_even_in_infinite_train_right_valid : probe_C_before_no_firing_even_in_infinite_train_right.Valid := by norm_num [RationalBox.Valid, probe_C_before_no_firing_even_in_infinite_train_right]

def Bounds15Valid : Prop :=
  A_fast_23_gain_after.Valid ∧
  A_fast_23_emission.Valid ∧
  C_fast_24_aux_separation_left.Valid ∧
  C_fast_24_aux_separation_right.Valid ∧
  C_fast_24_gain_below_cap_left.Valid ∧
  C_fast_24_gain_below_cap_right.Valid ∧
  C_fast_24_ready_at_input_left.Valid ∧
  C_fast_24_ready_at_input_right.Valid ∧
  C_fast_24_positive_derivative_coefficient_left.Valid ∧
  C_fast_24_positive_derivative_coefficient_right.Valid ∧
  C_fast_24_fixed_flow_increases_left.Valid ∧
  C_fast_24_fixed_flow_increases_right.Valid ∧
  C_fast_24_strong_crosses_by_one_left.Valid ∧
  C_fast_24_strong_crosses_by_one_right.Valid ∧
  C_fast_24_root_latency.Valid ∧
  C_fast_24_root_lower_left.Valid ∧
  C_fast_24_root_lower_right.Valid ∧
  C_fast_24_root_upper_left.Valid ∧
  C_fast_24_root_upper_right.Valid ∧
  C_fast_24_MARK_before_fire_left.Valid ∧
  C_fast_24_MARK_before_fire_right.Valid ∧
  C_fast_24_fire_before_ERROR_left.Valid ∧
  C_fast_24_fire_before_ERROR_right.Valid ∧
  C_fast_24_ERROR_protected_left.Valid ∧
  C_fast_24_ERROR_protected_right.Valid ∧
  C_fast_24_arrival.Valid ∧
  C_fast_24_b_after.Valid ∧
  C_fast_24_gain_after.Valid ∧
  C_fast_24_emission.Valid ∧
  B_fast_24_aux_separation_left.Valid ∧
  B_fast_24_aux_separation_right.Valid ∧
  B_fast_24_gain_below_cap_left.Valid ∧
  B_fast_24_gain_below_cap_right.Valid ∧
  B_fast_24_ready_at_input_left.Valid ∧
  B_fast_24_ready_at_input_right.Valid ∧
  B_fast_24_positive_derivative_coefficient_left.Valid ∧
  B_fast_24_positive_derivative_coefficient_right.Valid ∧
  B_fast_24_fixed_flow_increases_left.Valid ∧
  B_fast_24_fixed_flow_increases_right.Valid ∧
  B_fast_24_strong_crosses_by_one_left.Valid ∧
  B_fast_24_strong_crosses_by_one_right.Valid ∧
  B_fast_24_root_latency.Valid ∧
  B_fast_24_root_lower_left.Valid ∧
  B_fast_24_root_lower_right.Valid ∧
  B_fast_24_root_upper_left.Valid ∧
  B_fast_24_root_upper_right.Valid ∧
  B_fast_24_MARK_before_fire_left.Valid ∧
  B_fast_24_MARK_before_fire_right.Valid ∧
  B_fast_24_fire_before_ERROR_left.Valid ∧
  B_fast_24_fire_before_ERROR_right.Valid ∧
  B_fast_24_ERROR_protected_left.Valid ∧
  B_fast_24_ERROR_protected_right.Valid ∧
  B_fast_24_arrival.Valid ∧
  B_fast_24_b_after.Valid ∧
  B_fast_24_gain_after.Valid ∧
  B_fast_24_emission.Valid ∧
  A_fast_24_aux_separation_left.Valid ∧
  A_fast_24_aux_separation_right.Valid ∧
  A_fast_24_gain_below_cap_left.Valid ∧
  A_fast_24_gain_below_cap_right.Valid ∧
  A_fast_24_ready_at_input_left.Valid ∧
  A_fast_24_ready_at_input_right.Valid ∧
  A_fast_24_positive_derivative_coefficient_left.Valid ∧
  A_fast_24_positive_derivative_coefficient_right.Valid ∧
  A_fast_24_fixed_flow_increases_left.Valid ∧
  A_fast_24_fixed_flow_increases_right.Valid ∧
  A_fast_24_strong_crosses_by_one_left.Valid ∧
  A_fast_24_strong_crosses_by_one_right.Valid ∧
  A_fast_24_root_latency.Valid ∧
  A_fast_24_root_lower_left.Valid ∧
  A_fast_24_root_lower_right.Valid ∧
  A_fast_24_root_upper_left.Valid ∧
  A_fast_24_root_upper_right.Valid ∧
  A_fast_24_MARK_before_fire_left.Valid ∧
  A_fast_24_MARK_before_fire_right.Valid ∧
  A_fast_24_fire_before_ERROR_left.Valid ∧
  A_fast_24_fire_before_ERROR_right.Valid ∧
  A_fast_24_ERROR_protected_left.Valid ∧
  A_fast_24_ERROR_protected_right.Valid ∧
  A_fast_24_arrival.Valid ∧
  A_fast_24_b_after.Valid ∧
  A_fast_24_gain_after.Valid ∧
  A_fast_24_emission.Valid ∧
  A_quiescent_at_measurement_left.Valid ∧
  A_quiescent_at_measurement_right.Valid ∧
  A_last_emission_inside_fast_gate_left.Valid ∧
  A_last_emission_inside_fast_gate_right.Valid ∧
  A_final_b.Valid ∧
  A_final_gain.Valid ∧
  A_final_gain_below_cap_left.Valid ∧
  A_final_gain_below_cap_right.Valid ∧
  B_quiescent_at_measurement_left.Valid ∧
  B_quiescent_at_measurement_right.Valid ∧
  B_last_emission_inside_fast_gate_left.Valid ∧
  B_last_emission_inside_fast_gate_right.Valid ∧
  B_final_b.Valid ∧
  B_final_gain.Valid ∧
  B_final_gain_below_cap_left.Valid ∧
  B_final_gain_below_cap_right.Valid ∧
  C_quiescent_at_measurement_left.Valid ∧
  C_quiescent_at_measurement_right.Valid ∧
  C_last_emission_inside_fast_gate_left.Valid ∧
  C_last_emission_inside_fast_gate_right.Valid ∧
  C_final_b.Valid ∧
  C_final_gain.Valid ∧
  C_final_gain_below_cap_left.Valid ∧
  C_final_gain_below_cap_right.Valid ∧
  probe_before_root_lower_left.Valid ∧
  probe_before_root_lower_right.Valid ∧
  probe_before_root_upper_left.Valid ∧
  probe_before_root_upper_right.Valid ∧
  probe_before_flow_increases_left.Valid ∧
  probe_before_flow_increases_right.Valid ∧
  probe_before_return.Valid ∧
  probe_before_second_pulse_fully_protected_left.Valid ∧
  probe_before_second_pulse_fully_protected_right.Valid ∧
  probe_before_return_before_third_pulse_left.Valid ∧
  probe_before_return_before_third_pulse_right.Valid ∧
  probe_after_root_lower_left.Valid ∧
  probe_after_root_lower_right.Valid ∧
  probe_after_root_upper_left.Valid ∧
  probe_after_root_upper_right.Valid ∧
  probe_after_flow_increases_left.Valid ∧
  probe_after_flow_increases_right.Valid ∧
  probe_after_return.Valid ∧
  probe_after_return_before_every_next_pulse_left.Valid ∧
  probe_after_return_before_every_next_pulse_right.Valid ∧
  probe_C_before_positive_coefficient_left.Valid ∧
  probe_C_before_positive_coefficient_right.Valid ∧
  probe_C_before_flow_increases_left.Valid ∧
  probe_C_before_flow_increases_right.Valid ∧
  probe_C_before_no_firing_even_in_infinite_train_left.Valid ∧
  probe_C_before_no_firing_even_in_infinite_train_right.Valid
theorem Bounds15Valid_verified : Bounds15Valid := by
  exact ⟨A_fast_23_gain_after_valid, A_fast_23_emission_valid, C_fast_24_aux_separation_left_valid, C_fast_24_aux_separation_right_valid, C_fast_24_gain_below_cap_left_valid, C_fast_24_gain_below_cap_right_valid, C_fast_24_ready_at_input_left_valid, C_fast_24_ready_at_input_right_valid, C_fast_24_positive_derivative_coefficient_left_valid, C_fast_24_positive_derivative_coefficient_right_valid, C_fast_24_fixed_flow_increases_left_valid, C_fast_24_fixed_flow_increases_right_valid, C_fast_24_strong_crosses_by_one_left_valid, C_fast_24_strong_crosses_by_one_right_valid, C_fast_24_root_latency_valid, C_fast_24_root_lower_left_valid, C_fast_24_root_lower_right_valid, C_fast_24_root_upper_left_valid, C_fast_24_root_upper_right_valid, C_fast_24_MARK_before_fire_left_valid, C_fast_24_MARK_before_fire_right_valid, C_fast_24_fire_before_ERROR_left_valid, C_fast_24_fire_before_ERROR_right_valid, C_fast_24_ERROR_protected_left_valid, C_fast_24_ERROR_protected_right_valid, C_fast_24_arrival_valid, C_fast_24_b_after_valid, C_fast_24_gain_after_valid, C_fast_24_emission_valid, B_fast_24_aux_separation_left_valid, B_fast_24_aux_separation_right_valid, B_fast_24_gain_below_cap_left_valid, B_fast_24_gain_below_cap_right_valid, B_fast_24_ready_at_input_left_valid, B_fast_24_ready_at_input_right_valid, B_fast_24_positive_derivative_coefficient_left_valid, B_fast_24_positive_derivative_coefficient_right_valid, B_fast_24_fixed_flow_increases_left_valid, B_fast_24_fixed_flow_increases_right_valid, B_fast_24_strong_crosses_by_one_left_valid, B_fast_24_strong_crosses_by_one_right_valid, B_fast_24_root_latency_valid, B_fast_24_root_lower_left_valid, B_fast_24_root_lower_right_valid, B_fast_24_root_upper_left_valid, B_fast_24_root_upper_right_valid, B_fast_24_MARK_before_fire_left_valid, B_fast_24_MARK_before_fire_right_valid, B_fast_24_fire_before_ERROR_left_valid, B_fast_24_fire_before_ERROR_right_valid, B_fast_24_ERROR_protected_left_valid, B_fast_24_ERROR_protected_right_valid, B_fast_24_arrival_valid, B_fast_24_b_after_valid, B_fast_24_gain_after_valid, B_fast_24_emission_valid, A_fast_24_aux_separation_left_valid, A_fast_24_aux_separation_right_valid, A_fast_24_gain_below_cap_left_valid, A_fast_24_gain_below_cap_right_valid, A_fast_24_ready_at_input_left_valid, A_fast_24_ready_at_input_right_valid, A_fast_24_positive_derivative_coefficient_left_valid, A_fast_24_positive_derivative_coefficient_right_valid, A_fast_24_fixed_flow_increases_left_valid, A_fast_24_fixed_flow_increases_right_valid, A_fast_24_strong_crosses_by_one_left_valid, A_fast_24_strong_crosses_by_one_right_valid, A_fast_24_root_latency_valid, A_fast_24_root_lower_left_valid, A_fast_24_root_lower_right_valid, A_fast_24_root_upper_left_valid, A_fast_24_root_upper_right_valid, A_fast_24_MARK_before_fire_left_valid, A_fast_24_MARK_before_fire_right_valid, A_fast_24_fire_before_ERROR_left_valid, A_fast_24_fire_before_ERROR_right_valid, A_fast_24_ERROR_protected_left_valid, A_fast_24_ERROR_protected_right_valid, A_fast_24_arrival_valid, A_fast_24_b_after_valid, A_fast_24_gain_after_valid, A_fast_24_emission_valid, A_quiescent_at_measurement_left_valid, A_quiescent_at_measurement_right_valid, A_last_emission_inside_fast_gate_left_valid, A_last_emission_inside_fast_gate_right_valid, A_final_b_valid, A_final_gain_valid, A_final_gain_below_cap_left_valid, A_final_gain_below_cap_right_valid, B_quiescent_at_measurement_left_valid, B_quiescent_at_measurement_right_valid, B_last_emission_inside_fast_gate_left_valid, B_last_emission_inside_fast_gate_right_valid, B_final_b_valid, B_final_gain_valid, B_final_gain_below_cap_left_valid, B_final_gain_below_cap_right_valid, C_quiescent_at_measurement_left_valid, C_quiescent_at_measurement_right_valid, C_last_emission_inside_fast_gate_left_valid, C_last_emission_inside_fast_gate_right_valid, C_final_b_valid, C_final_gain_valid, C_final_gain_below_cap_left_valid, C_final_gain_below_cap_right_valid, probe_before_root_lower_left_valid, probe_before_root_lower_right_valid, probe_before_root_upper_left_valid, probe_before_root_upper_right_valid, probe_before_flow_increases_left_valid, probe_before_flow_increases_right_valid, probe_before_return_valid, probe_before_second_pulse_fully_protected_left_valid, probe_before_second_pulse_fully_protected_right_valid, probe_before_return_before_third_pulse_left_valid, probe_before_return_before_third_pulse_right_valid, probe_after_root_lower_left_valid, probe_after_root_lower_right_valid, probe_after_root_upper_left_valid, probe_after_root_upper_right_valid, probe_after_flow_increases_left_valid, probe_after_flow_increases_right_valid, probe_after_return_valid, probe_after_return_before_every_next_pulse_left_valid, probe_after_return_before_every_next_pulse_right_valid, probe_C_before_positive_coefficient_left_valid, probe_C_before_positive_coefficient_right_valid, probe_C_before_flow_increases_left_valid, probe_C_before_flow_increases_right_valid, probe_C_before_no_firing_even_in_infinite_train_left_valid, probe_C_before_no_firing_even_in_infinite_train_right_valid⟩

end KernelR.Certificates.Cadence010
