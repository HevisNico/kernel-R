import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def C_fast_14_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_14_aux_separation_right_valid : C_fast_14_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_aux_separation_right]

def C_fast_14_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_gain_below_cap_left_valid : C_fast_14_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_gain_below_cap_left]

def C_fast_14_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem C_fast_14_gain_below_cap_right_valid : C_fast_14_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_gain_below_cap_right]

def C_fast_14_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_14_ready_at_input_left_valid : C_fast_14_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_ready_at_input_left]

def C_fast_14_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_ready_at_input_right_valid : C_fast_14_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_ready_at_input_right]

def C_fast_14_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_14_positive_derivative_coefficient_left_valid : C_fast_14_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_positive_derivative_coefficient_left]

def C_fast_14_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_positive_derivative_coefficient_right_valid : C_fast_14_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_positive_derivative_coefficient_right]

def C_fast_14_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_14_fixed_flow_increases_left_valid : C_fast_14_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_fixed_flow_increases_left]

def C_fast_14_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_fixed_flow_increases_right_valid : C_fast_14_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_fixed_flow_increases_right]

def C_fast_14_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_14_strong_crosses_by_one_left_valid : C_fast_14_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_strong_crosses_by_one_left]

def C_fast_14_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_strong_crosses_by_one_right_valid : C_fast_14_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_strong_crosses_by_one_right]

def C_fast_14_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_14_root_latency_valid : C_fast_14_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_14_root_latency]

def C_fast_14_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_root_lower_left_valid : C_fast_14_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_root_lower_left]

def C_fast_14_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_14_root_lower_right_valid : C_fast_14_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_root_lower_right]

def C_fast_14_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_14_root_upper_left_valid : C_fast_14_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_root_upper_left]

def C_fast_14_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_root_upper_right_valid : C_fast_14_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_root_upper_right]

def C_fast_14_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_MARK_before_fire_left_valid : C_fast_14_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_MARK_before_fire_left]

def C_fast_14_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_14_MARK_before_fire_right_valid : C_fast_14_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_MARK_before_fire_right]

def C_fast_14_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_14_fire_before_ERROR_left_valid : C_fast_14_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_fire_before_ERROR_left]

def C_fast_14_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_fire_before_ERROR_right_valid : C_fast_14_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_fire_before_ERROR_right]

def C_fast_14_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_ERROR_protected_left_valid : C_fast_14_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_ERROR_protected_left]

def C_fast_14_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_ERROR_protected_right_valid : C_fast_14_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_ERROR_protected_right]

def C_fast_14_arrival : RationalBox := ⟨(696 / 1 : ℚ), (696 / 1 : ℚ)⟩
theorem C_fast_14_arrival_valid : C_fast_14_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_14_arrival]

def C_fast_14_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_14_b_after_valid : C_fast_14_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_14_b_after]

def C_fast_14_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_gain_after_valid : C_fast_14_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_14_gain_after]

def C_fast_14_emission : RationalBox := ⟨(365034165 / 524288 : ℚ), (730068337 / 1048576 : ℚ)⟩
theorem C_fast_14_emission_valid : C_fast_14_emission.Valid := by norm_num [RationalBox.Valid, C_fast_14_emission]

def B_fast_14_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_aux_separation_left_valid : B_fast_14_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_aux_separation_left]

def B_fast_14_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_14_aux_separation_right_valid : B_fast_14_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_aux_separation_right]

def B_fast_14_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_gain_below_cap_left_valid : B_fast_14_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_gain_below_cap_left]

def B_fast_14_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_fast_14_gain_below_cap_right_valid : B_fast_14_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_gain_below_cap_right]

def B_fast_14_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_14_ready_at_input_left_valid : B_fast_14_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_ready_at_input_left]

def B_fast_14_ready_at_input_right : RationalBox := ⟨(2412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2206782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_ready_at_input_right_valid : B_fast_14_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_ready_at_input_right]

def B_fast_14_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_14_positive_derivative_coefficient_left_valid : B_fast_14_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_positive_derivative_coefficient_left]

def B_fast_14_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_positive_derivative_coefficient_right_valid : B_fast_14_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_positive_derivative_coefficient_right]

def B_fast_14_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_14_fixed_flow_increases_left_valid : B_fast_14_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_fixed_flow_increases_left]

def B_fast_14_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_fixed_flow_increases_right_valid : B_fast_14_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_fixed_flow_increases_right]

def B_fast_14_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_14_strong_crosses_by_one_left_valid : B_fast_14_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_strong_crosses_by_one_left]

def B_fast_14_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_strong_crosses_by_one_right_valid : B_fast_14_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_strong_crosses_by_one_right]

def B_fast_14_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_14_root_latency_valid : B_fast_14_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_14_root_latency]

def B_fast_14_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_root_lower_left_valid : B_fast_14_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_root_lower_left]

def B_fast_14_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_14_root_lower_right_valid : B_fast_14_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_root_lower_right]

def B_fast_14_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_14_root_upper_left_valid : B_fast_14_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_root_upper_left]

def B_fast_14_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_root_upper_right_valid : B_fast_14_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_root_upper_right]

def B_fast_14_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_MARK_before_fire_left_valid : B_fast_14_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_MARK_before_fire_left]

def B_fast_14_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_14_MARK_before_fire_right_valid : B_fast_14_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_MARK_before_fire_right]

def B_fast_14_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_14_fire_before_ERROR_left_valid : B_fast_14_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_fire_before_ERROR_left]

def B_fast_14_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_fire_before_ERROR_right_valid : B_fast_14_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_fire_before_ERROR_right]

def B_fast_14_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_ERROR_protected_left_valid : B_fast_14_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_ERROR_protected_left]

def B_fast_14_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_ERROR_protected_right_valid : B_fast_14_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_ERROR_protected_right]

def B_fast_14_arrival : RationalBox := ⟨(1825957257 / 2621440 : ℚ), (3652438837 / 5242880 : ℚ)⟩
theorem B_fast_14_arrival_valid : B_fast_14_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_14_arrival]

def B_fast_14_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_14_b_after_valid : B_fast_14_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_14_b_after]

def B_fast_14_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_gain_after_valid : B_fast_14_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_14_gain_after]

def B_fast_14_emission : RationalBox := ⟨(913302921 / 1310720 : ℚ), (1826868021 / 2621440 : ℚ)⟩
theorem B_fast_14_emission_valid : B_fast_14_emission.Valid := by norm_num [RationalBox.Valid, B_fast_14_emission]

def A_fast_14_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_aux_separation_left_valid : A_fast_14_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_aux_separation_left]

def A_fast_14_aux_separation_right : RationalBox := ⟨(19 / 5 : ℚ), (21 / 5 : ℚ)⟩
theorem A_fast_14_aux_separation_right_valid : A_fast_14_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_aux_separation_right]

def A_fast_14_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_gain_below_cap_left_valid : A_fast_14_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_gain_below_cap_left]

def A_fast_14_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem A_fast_14_gain_below_cap_right_valid : A_fast_14_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_gain_below_cap_right]

def A_fast_14_input_in_SLOW_left : RationalBox := ⟨(7284960741 / 10485760 : ℚ), (113860287 / 163840 : ℚ)⟩
theorem A_fast_14_input_in_SLOW_left_valid : A_fast_14_input_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_input_in_SLOW_left]

def A_fast_14_input_in_SLOW_right : RationalBox := ⟨(913696137 / 1310720 : ℚ), (1827916597 / 2621440 : ℚ)⟩
theorem A_fast_14_input_in_SLOW_right_valid : A_fast_14_input_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_input_in_SLOW_right]

def A_fast_14_input_before_return_left : RationalBox := ⟨(913696137 / 1310720 : ℚ), (1827916597 / 2621440 : ℚ)⟩
theorem A_fast_14_input_before_return_left_valid : A_fast_14_input_before_return_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_input_before_return_left]

def A_fast_14_input_before_return_right : RationalBox := ⟨(3490101727509304871353086648008428468116319 / 5000000000000000000000000000000000000000 : ℚ), (6982206245490269838974017901059609667182761 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_input_before_return_right_valid : A_fast_14_input_before_return_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_input_before_return_right]

def A_fast_14_whole_MARK_protected_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_whole_MARK_protected_left_valid : A_fast_14_whole_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_whole_MARK_protected_left]

def A_fast_14_whole_MARK_protected_right : RationalBox := ⟨(2704226219214904958021743476140208786351 / 5000000000000000000000000000000000000000 : ℚ), (5408452438429809916043486952280417572703 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_whole_MARK_protected_right_valid : A_fast_14_whole_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_whole_MARK_protected_right]

def A_fast_14_b_below_cap_left : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_14_b_below_cap_left_valid : A_fast_14_b_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_b_below_cap_left]

def A_fast_14_b_below_cap_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem A_fast_14_b_below_cap_right_valid : A_fast_14_b_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_b_below_cap_right]

def A_fast_14_return_before_ERROR_left : RationalBox := ⟨(4201123663116421772565258809257652229273 / 5000000000000000000000000000000000000000 : ℚ), (8402247326232843545130517618515304458547 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_return_before_ERROR_left_valid : A_fast_14_return_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_return_before_ERROR_left]

def A_fast_14_return_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_return_before_ERROR_right_valid : A_fast_14_return_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_return_before_ERROR_right]

def A_fast_14_no_firing_from_raw_tail_left : RationalBox := ⟨(4580792517143762102906989960556959654769 / 10000000000000000000000000000000000000000 : ℚ), (458079251714376210290698996055695965477 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_no_firing_from_raw_tail_left_valid : A_fast_14_no_firing_from_raw_tail_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_no_firing_from_raw_tail_left]

def A_fast_14_no_firing_from_raw_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_14_no_firing_from_raw_tail_right_valid : A_fast_14_no_firing_from_raw_tail_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_no_firing_from_raw_tail_right]

def A_fast_14_reopen : RationalBox := ⟨(2704226219214904958021743476140208786351 / 5000000000000000000000000000000000000000 : ℚ), (8402247326232843545130517618515304458547 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_reopen_valid : A_fast_14_reopen.Valid := by norm_num [RationalBox.Valid, A_fast_14_reopen]

def A_fast_14_arrival : RationalBox := ⟨(913696137 / 1310720 : ℚ), (1827916597 / 2621440 : ℚ)⟩
theorem A_fast_14_arrival_valid : A_fast_14_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_14_arrival]

def A_fast_14_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_14_b_after_valid : A_fast_14_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_14_b_after]

def A_fast_14_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_gain_after_valid : A_fast_14_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_14_gain_after]

def C_fast_15_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_aux_separation_left_valid : C_fast_15_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_aux_separation_left]

def C_fast_15_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_15_aux_separation_right_valid : C_fast_15_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_aux_separation_right]

def C_fast_15_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_gain_below_cap_left_valid : C_fast_15_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_gain_below_cap_left]

def C_fast_15_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem C_fast_15_gain_below_cap_right_valid : C_fast_15_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_gain_below_cap_right]

def C_fast_15_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_15_ready_at_input_left_valid : C_fast_15_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_ready_at_input_left]

def C_fast_15_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_ready_at_input_right_valid : C_fast_15_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_ready_at_input_right]

def C_fast_15_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_15_positive_derivative_coefficient_left_valid : C_fast_15_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_positive_derivative_coefficient_left]

def C_fast_15_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_positive_derivative_coefficient_right_valid : C_fast_15_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_positive_derivative_coefficient_right]

def C_fast_15_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_15_fixed_flow_increases_left_valid : C_fast_15_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_fixed_flow_increases_left]

def C_fast_15_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_fixed_flow_increases_right_valid : C_fast_15_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_fixed_flow_increases_right]

def C_fast_15_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_15_strong_crosses_by_one_left_valid : C_fast_15_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_strong_crosses_by_one_left]

def C_fast_15_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_strong_crosses_by_one_right_valid : C_fast_15_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_strong_crosses_by_one_right]

def C_fast_15_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_15_root_latency_valid : C_fast_15_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_15_root_latency]

def C_fast_15_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_root_lower_left_valid : C_fast_15_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_root_lower_left]

def C_fast_15_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_15_root_lower_right_valid : C_fast_15_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_root_lower_right]

def C_fast_15_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_15_root_upper_left_valid : C_fast_15_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_root_upper_left]

def C_fast_15_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_root_upper_right_valid : C_fast_15_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_root_upper_right]

def C_fast_15_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_MARK_before_fire_left_valid : C_fast_15_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_MARK_before_fire_left]

def C_fast_15_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_15_MARK_before_fire_right_valid : C_fast_15_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_MARK_before_fire_right]

def C_fast_15_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_15_fire_before_ERROR_left_valid : C_fast_15_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_fire_before_ERROR_left]

def C_fast_15_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_fire_before_ERROR_right_valid : C_fast_15_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_fire_before_ERROR_right]

def C_fast_15_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_ERROR_protected_left_valid : C_fast_15_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_ERROR_protected_left]

def C_fast_15_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_ERROR_protected_right_valid : C_fast_15_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_ERROR_protected_right]

def C_fast_15_arrival : RationalBox := ⟨(700 / 1 : ℚ), (700 / 1 : ℚ)⟩
theorem C_fast_15_arrival_valid : C_fast_15_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_15_arrival]

def C_fast_15_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_15_b_after_valid : C_fast_15_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_15_b_after]

def C_fast_15_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_gain_after_valid : C_fast_15_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_15_gain_after]

def C_fast_15_emission : RationalBox := ⟨(367131317 / 524288 : ℚ), (734262641 / 1048576 : ℚ)⟩
theorem C_fast_15_emission_valid : C_fast_15_emission.Valid := by norm_num [RationalBox.Valid, C_fast_15_emission]

def B_fast_15_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_aux_separation_left_valid : B_fast_15_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_aux_separation_left]

def B_fast_15_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_15_aux_separation_right_valid : B_fast_15_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_aux_separation_right]

def B_fast_15_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_gain_below_cap_left_valid : B_fast_15_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_gain_below_cap_left]

def B_fast_15_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_fast_15_gain_below_cap_right_valid : B_fast_15_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_gain_below_cap_right]

def B_fast_15_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_15_ready_at_input_left_valid : B_fast_15_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_ready_at_input_left]

def B_fast_15_ready_at_input_right : RationalBox := ⟨(2412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2206782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_ready_at_input_right_valid : B_fast_15_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_ready_at_input_right]

def B_fast_15_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_15_positive_derivative_coefficient_left_valid : B_fast_15_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_positive_derivative_coefficient_left]

def B_fast_15_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_positive_derivative_coefficient_right_valid : B_fast_15_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_positive_derivative_coefficient_right]

def B_fast_15_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_15_fixed_flow_increases_left_valid : B_fast_15_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_fixed_flow_increases_left]

def B_fast_15_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_fixed_flow_increases_right_valid : B_fast_15_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_fixed_flow_increases_right]

def B_fast_15_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_15_strong_crosses_by_one_left_valid : B_fast_15_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_strong_crosses_by_one_left]

def B_fast_15_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_strong_crosses_by_one_right_valid : B_fast_15_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_strong_crosses_by_one_right]

def B_fast_15_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_15_root_latency_valid : B_fast_15_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_15_root_latency]

def B_fast_15_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_root_lower_left_valid : B_fast_15_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_root_lower_left]

def B_fast_15_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_15_root_lower_right_valid : B_fast_15_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_root_lower_right]

def B_fast_15_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_15_root_upper_left_valid : B_fast_15_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_root_upper_left]

def B_fast_15_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_root_upper_right_valid : B_fast_15_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_root_upper_right]

def B_fast_15_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_MARK_before_fire_left_valid : B_fast_15_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_MARK_before_fire_left]

def B_fast_15_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_15_MARK_before_fire_right_valid : B_fast_15_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_MARK_before_fire_right]

def B_fast_15_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_15_fire_before_ERROR_left_valid : B_fast_15_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_fire_before_ERROR_left]

def B_fast_15_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_fire_before_ERROR_right_valid : B_fast_15_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_fire_before_ERROR_right]

def B_fast_15_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_ERROR_protected_left_valid : B_fast_15_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_ERROR_protected_left]

def B_fast_15_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_ERROR_protected_right_valid : B_fast_15_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_ERROR_protected_right]

def B_fast_15_arrival : RationalBox := ⟨(1836443017 / 2621440 : ℚ), (3673410357 / 5242880 : ℚ)⟩
theorem B_fast_15_arrival_valid : B_fast_15_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_15_arrival]

def B_fast_15_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_15_b_after_valid : B_fast_15_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_15_b_after]

def B_fast_15_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_gain_after_valid : B_fast_15_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_15_gain_after]

def B_fast_15_emission : RationalBox := ⟨(918545801 / 1310720 : ℚ), (1837353781 / 2621440 : ℚ)⟩
theorem B_fast_15_emission_valid : B_fast_15_emission.Valid := by norm_num [RationalBox.Valid, B_fast_15_emission]

def A_fast_15_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_aux_separation_left_valid : A_fast_15_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_aux_separation_left]

def A_fast_15_aux_separation_right : RationalBox := ⟨(19 / 5 : ℚ), (21 / 5 : ℚ)⟩
theorem A_fast_15_aux_separation_right_valid : A_fast_15_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_aux_separation_right]

def A_fast_15_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_gain_below_cap_left_valid : A_fast_15_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_gain_below_cap_left]

def A_fast_15_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem A_fast_15_gain_below_cap_right_valid : A_fast_15_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_gain_below_cap_right]

def A_fast_15_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_15_ready_at_input_left_valid : A_fast_15_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_ready_at_input_left]

def A_fast_15_ready_at_input_right : RationalBox := ⟨(29597752673767156454869482381484695541453 / 10000000000000000000000000000000000000000 : ℚ), (18295773780785095041978256523859791213649 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_ready_at_input_right_valid : A_fast_15_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_ready_at_input_right]

def A_fast_15_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_15_positive_derivative_coefficient_left_valid : A_fast_15_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_positive_derivative_coefficient_left]

def A_fast_15_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (26304561621222946599484354061156233563949 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_positive_derivative_coefficient_right_valid : A_fast_15_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_positive_derivative_coefficient_right]

def A_fast_15_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_15_fixed_flow_increases_left_valid : A_fast_15_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_fixed_flow_increases_left]

def A_fast_15_fixed_flow_increases_right : RationalBox := ⟨(1577617792999862388433130063325944823129 / 2000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_fixed_flow_increases_right_valid : A_fast_15_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_fixed_flow_increases_right]

def A_fast_15_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_15_strong_crosses_by_one_left_valid : A_fast_15_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_strong_crosses_by_one_left]

def A_fast_15_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (9988759278670294666026649858690826769321 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_strong_crosses_by_one_right_valid : A_fast_15_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_strong_crosses_by_one_right]

def A_fast_15_root_latency : RationalBox := ⟨(922755 / 4194304 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_15_root_latency_valid : A_fast_15_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_latency]

def A_fast_15_root_lower_left : RationalBox := ⟨(9208802579465496091686970052463302288183 / 10000000000000000000000000000000000000000 : ℚ), (2499999696873771594038338720988526357517 / 2500000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_root_lower_left_valid : A_fast_15_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_lower_left]

def A_fast_15_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_15_root_lower_right_valid : A_fast_15_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_lower_right]

def A_fast_15_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_15_root_upper_left_valid : A_fast_15_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_upper_left]

def A_fast_15_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (10780443008510899389513848038017134517343 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_root_upper_right_valid : A_fast_15_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_upper_right]

def A_fast_15_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_MARK_before_fire_left_valid : A_fast_15_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_MARK_before_fire_left]

def A_fast_15_MARK_before_fire_right : RationalBox := ⟨(922755 / 4194304 : ℚ), (922755 / 4194304 : ℚ)⟩
theorem A_fast_15_MARK_before_fire_right_valid : A_fast_15_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_MARK_before_fire_right]

def A_fast_15_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_15_fire_before_ERROR_left_valid : A_fast_15_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_fire_before_ERROR_left]

def A_fast_15_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_fire_before_ERROR_right_valid : A_fast_15_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_fire_before_ERROR_right]

def A_fast_15_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_ERROR_protected_left_valid : A_fast_15_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_ERROR_protected_left]

def A_fast_15_ERROR_protected_right : RationalBox := ⟨(18156149411303417404644931538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36313567923344381492716396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_ERROR_protected_right_valid : A_fast_15_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_ERROR_protected_right]

def A_fast_15_arrival : RationalBox := ⟨(918939017 / 1310720 : ℚ), (1838402357 / 2621440 : ℚ)⟩
theorem A_fast_15_arrival_valid : A_fast_15_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_15_arrival]

def A_fast_15_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_15_b_after_valid : A_fast_15_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_15_b_after]

def A_fast_15_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_gain_after_valid : A_fast_15_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_15_gain_after]

def A_fast_15_emission : RationalBox := ⟨(14707638047 / 20971520 : ℚ), (3678101919 / 5242880 : ℚ)⟩
theorem A_fast_15_emission_valid : A_fast_15_emission.Valid := by norm_num [RationalBox.Valid, A_fast_15_emission]

def C_fast_16_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_16_aux_separation_left_valid : C_fast_16_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_16_aux_separation_left]

def C_fast_16_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_16_aux_separation_right_valid : C_fast_16_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_16_aux_separation_right]

def C_fast_16_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_16_gain_below_cap_left_valid : C_fast_16_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_16_gain_below_cap_left]

def C_fast_16_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem C_fast_16_gain_below_cap_right_valid : C_fast_16_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_16_gain_below_cap_right]

def C_fast_16_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_16_ready_at_input_left_valid : C_fast_16_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_16_ready_at_input_left]

def C_fast_16_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_16_ready_at_input_right_valid : C_fast_16_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_16_ready_at_input_right]

def Bounds10Valid : Prop :=
  C_fast_14_aux_separation_right.Valid ∧
  C_fast_14_gain_below_cap_left.Valid ∧
  C_fast_14_gain_below_cap_right.Valid ∧
  C_fast_14_ready_at_input_left.Valid ∧
  C_fast_14_ready_at_input_right.Valid ∧
  C_fast_14_positive_derivative_coefficient_left.Valid ∧
  C_fast_14_positive_derivative_coefficient_right.Valid ∧
  C_fast_14_fixed_flow_increases_left.Valid ∧
  C_fast_14_fixed_flow_increases_right.Valid ∧
  C_fast_14_strong_crosses_by_one_left.Valid ∧
  C_fast_14_strong_crosses_by_one_right.Valid ∧
  C_fast_14_root_latency.Valid ∧
  C_fast_14_root_lower_left.Valid ∧
  C_fast_14_root_lower_right.Valid ∧
  C_fast_14_root_upper_left.Valid ∧
  C_fast_14_root_upper_right.Valid ∧
  C_fast_14_MARK_before_fire_left.Valid ∧
  C_fast_14_MARK_before_fire_right.Valid ∧
  C_fast_14_fire_before_ERROR_left.Valid ∧
  C_fast_14_fire_before_ERROR_right.Valid ∧
  C_fast_14_ERROR_protected_left.Valid ∧
  C_fast_14_ERROR_protected_right.Valid ∧
  C_fast_14_arrival.Valid ∧
  C_fast_14_b_after.Valid ∧
  C_fast_14_gain_after.Valid ∧
  C_fast_14_emission.Valid ∧
  B_fast_14_aux_separation_left.Valid ∧
  B_fast_14_aux_separation_right.Valid ∧
  B_fast_14_gain_below_cap_left.Valid ∧
  B_fast_14_gain_below_cap_right.Valid ∧
  B_fast_14_ready_at_input_left.Valid ∧
  B_fast_14_ready_at_input_right.Valid ∧
  B_fast_14_positive_derivative_coefficient_left.Valid ∧
  B_fast_14_positive_derivative_coefficient_right.Valid ∧
  B_fast_14_fixed_flow_increases_left.Valid ∧
  B_fast_14_fixed_flow_increases_right.Valid ∧
  B_fast_14_strong_crosses_by_one_left.Valid ∧
  B_fast_14_strong_crosses_by_one_right.Valid ∧
  B_fast_14_root_latency.Valid ∧
  B_fast_14_root_lower_left.Valid ∧
  B_fast_14_root_lower_right.Valid ∧
  B_fast_14_root_upper_left.Valid ∧
  B_fast_14_root_upper_right.Valid ∧
  B_fast_14_MARK_before_fire_left.Valid ∧
  B_fast_14_MARK_before_fire_right.Valid ∧
  B_fast_14_fire_before_ERROR_left.Valid ∧
  B_fast_14_fire_before_ERROR_right.Valid ∧
  B_fast_14_ERROR_protected_left.Valid ∧
  B_fast_14_ERROR_protected_right.Valid ∧
  B_fast_14_arrival.Valid ∧
  B_fast_14_b_after.Valid ∧
  B_fast_14_gain_after.Valid ∧
  B_fast_14_emission.Valid ∧
  A_fast_14_aux_separation_left.Valid ∧
  A_fast_14_aux_separation_right.Valid ∧
  A_fast_14_gain_below_cap_left.Valid ∧
  A_fast_14_gain_below_cap_right.Valid ∧
  A_fast_14_input_in_SLOW_left.Valid ∧
  A_fast_14_input_in_SLOW_right.Valid ∧
  A_fast_14_input_before_return_left.Valid ∧
  A_fast_14_input_before_return_right.Valid ∧
  A_fast_14_whole_MARK_protected_left.Valid ∧
  A_fast_14_whole_MARK_protected_right.Valid ∧
  A_fast_14_b_below_cap_left.Valid ∧
  A_fast_14_b_below_cap_right.Valid ∧
  A_fast_14_return_before_ERROR_left.Valid ∧
  A_fast_14_return_before_ERROR_right.Valid ∧
  A_fast_14_no_firing_from_raw_tail_left.Valid ∧
  A_fast_14_no_firing_from_raw_tail_right.Valid ∧
  A_fast_14_reopen.Valid ∧
  A_fast_14_arrival.Valid ∧
  A_fast_14_b_after.Valid ∧
  A_fast_14_gain_after.Valid ∧
  C_fast_15_aux_separation_left.Valid ∧
  C_fast_15_aux_separation_right.Valid ∧
  C_fast_15_gain_below_cap_left.Valid ∧
  C_fast_15_gain_below_cap_right.Valid ∧
  C_fast_15_ready_at_input_left.Valid ∧
  C_fast_15_ready_at_input_right.Valid ∧
  C_fast_15_positive_derivative_coefficient_left.Valid ∧
  C_fast_15_positive_derivative_coefficient_right.Valid ∧
  C_fast_15_fixed_flow_increases_left.Valid ∧
  C_fast_15_fixed_flow_increases_right.Valid ∧
  C_fast_15_strong_crosses_by_one_left.Valid ∧
  C_fast_15_strong_crosses_by_one_right.Valid ∧
  C_fast_15_root_latency.Valid ∧
  C_fast_15_root_lower_left.Valid ∧
  C_fast_15_root_lower_right.Valid ∧
  C_fast_15_root_upper_left.Valid ∧
  C_fast_15_root_upper_right.Valid ∧
  C_fast_15_MARK_before_fire_left.Valid ∧
  C_fast_15_MARK_before_fire_right.Valid ∧
  C_fast_15_fire_before_ERROR_left.Valid ∧
  C_fast_15_fire_before_ERROR_right.Valid ∧
  C_fast_15_ERROR_protected_left.Valid ∧
  C_fast_15_ERROR_protected_right.Valid ∧
  C_fast_15_arrival.Valid ∧
  C_fast_15_b_after.Valid ∧
  C_fast_15_gain_after.Valid ∧
  C_fast_15_emission.Valid ∧
  B_fast_15_aux_separation_left.Valid ∧
  B_fast_15_aux_separation_right.Valid ∧
  B_fast_15_gain_below_cap_left.Valid ∧
  B_fast_15_gain_below_cap_right.Valid ∧
  B_fast_15_ready_at_input_left.Valid ∧
  B_fast_15_ready_at_input_right.Valid ∧
  B_fast_15_positive_derivative_coefficient_left.Valid ∧
  B_fast_15_positive_derivative_coefficient_right.Valid ∧
  B_fast_15_fixed_flow_increases_left.Valid ∧
  B_fast_15_fixed_flow_increases_right.Valid ∧
  B_fast_15_strong_crosses_by_one_left.Valid ∧
  B_fast_15_strong_crosses_by_one_right.Valid ∧
  B_fast_15_root_latency.Valid ∧
  B_fast_15_root_lower_left.Valid ∧
  B_fast_15_root_lower_right.Valid ∧
  B_fast_15_root_upper_left.Valid ∧
  B_fast_15_root_upper_right.Valid ∧
  B_fast_15_MARK_before_fire_left.Valid ∧
  B_fast_15_MARK_before_fire_right.Valid ∧
  B_fast_15_fire_before_ERROR_left.Valid ∧
  B_fast_15_fire_before_ERROR_right.Valid ∧
  B_fast_15_ERROR_protected_left.Valid ∧
  B_fast_15_ERROR_protected_right.Valid ∧
  B_fast_15_arrival.Valid ∧
  B_fast_15_b_after.Valid ∧
  B_fast_15_gain_after.Valid ∧
  B_fast_15_emission.Valid ∧
  A_fast_15_aux_separation_left.Valid ∧
  A_fast_15_aux_separation_right.Valid ∧
  A_fast_15_gain_below_cap_left.Valid ∧
  A_fast_15_gain_below_cap_right.Valid ∧
  A_fast_15_ready_at_input_left.Valid ∧
  A_fast_15_ready_at_input_right.Valid ∧
  A_fast_15_positive_derivative_coefficient_left.Valid ∧
  A_fast_15_positive_derivative_coefficient_right.Valid ∧
  A_fast_15_fixed_flow_increases_left.Valid ∧
  A_fast_15_fixed_flow_increases_right.Valid ∧
  A_fast_15_strong_crosses_by_one_left.Valid ∧
  A_fast_15_strong_crosses_by_one_right.Valid ∧
  A_fast_15_root_latency.Valid ∧
  A_fast_15_root_lower_left.Valid ∧
  A_fast_15_root_lower_right.Valid ∧
  A_fast_15_root_upper_left.Valid ∧
  A_fast_15_root_upper_right.Valid ∧
  A_fast_15_MARK_before_fire_left.Valid ∧
  A_fast_15_MARK_before_fire_right.Valid ∧
  A_fast_15_fire_before_ERROR_left.Valid ∧
  A_fast_15_fire_before_ERROR_right.Valid ∧
  A_fast_15_ERROR_protected_left.Valid ∧
  A_fast_15_ERROR_protected_right.Valid ∧
  A_fast_15_arrival.Valid ∧
  A_fast_15_b_after.Valid ∧
  A_fast_15_gain_after.Valid ∧
  A_fast_15_emission.Valid ∧
  C_fast_16_aux_separation_left.Valid ∧
  C_fast_16_aux_separation_right.Valid ∧
  C_fast_16_gain_below_cap_left.Valid ∧
  C_fast_16_gain_below_cap_right.Valid ∧
  C_fast_16_ready_at_input_left.Valid ∧
  C_fast_16_ready_at_input_right.Valid
theorem Bounds10Valid_verified : Bounds10Valid := by
  exact ⟨C_fast_14_aux_separation_right_valid, C_fast_14_gain_below_cap_left_valid, C_fast_14_gain_below_cap_right_valid, C_fast_14_ready_at_input_left_valid, C_fast_14_ready_at_input_right_valid, C_fast_14_positive_derivative_coefficient_left_valid, C_fast_14_positive_derivative_coefficient_right_valid, C_fast_14_fixed_flow_increases_left_valid, C_fast_14_fixed_flow_increases_right_valid, C_fast_14_strong_crosses_by_one_left_valid, C_fast_14_strong_crosses_by_one_right_valid, C_fast_14_root_latency_valid, C_fast_14_root_lower_left_valid, C_fast_14_root_lower_right_valid, C_fast_14_root_upper_left_valid, C_fast_14_root_upper_right_valid, C_fast_14_MARK_before_fire_left_valid, C_fast_14_MARK_before_fire_right_valid, C_fast_14_fire_before_ERROR_left_valid, C_fast_14_fire_before_ERROR_right_valid, C_fast_14_ERROR_protected_left_valid, C_fast_14_ERROR_protected_right_valid, C_fast_14_arrival_valid, C_fast_14_b_after_valid, C_fast_14_gain_after_valid, C_fast_14_emission_valid, B_fast_14_aux_separation_left_valid, B_fast_14_aux_separation_right_valid, B_fast_14_gain_below_cap_left_valid, B_fast_14_gain_below_cap_right_valid, B_fast_14_ready_at_input_left_valid, B_fast_14_ready_at_input_right_valid, B_fast_14_positive_derivative_coefficient_left_valid, B_fast_14_positive_derivative_coefficient_right_valid, B_fast_14_fixed_flow_increases_left_valid, B_fast_14_fixed_flow_increases_right_valid, B_fast_14_strong_crosses_by_one_left_valid, B_fast_14_strong_crosses_by_one_right_valid, B_fast_14_root_latency_valid, B_fast_14_root_lower_left_valid, B_fast_14_root_lower_right_valid, B_fast_14_root_upper_left_valid, B_fast_14_root_upper_right_valid, B_fast_14_MARK_before_fire_left_valid, B_fast_14_MARK_before_fire_right_valid, B_fast_14_fire_before_ERROR_left_valid, B_fast_14_fire_before_ERROR_right_valid, B_fast_14_ERROR_protected_left_valid, B_fast_14_ERROR_protected_right_valid, B_fast_14_arrival_valid, B_fast_14_b_after_valid, B_fast_14_gain_after_valid, B_fast_14_emission_valid, A_fast_14_aux_separation_left_valid, A_fast_14_aux_separation_right_valid, A_fast_14_gain_below_cap_left_valid, A_fast_14_gain_below_cap_right_valid, A_fast_14_input_in_SLOW_left_valid, A_fast_14_input_in_SLOW_right_valid, A_fast_14_input_before_return_left_valid, A_fast_14_input_before_return_right_valid, A_fast_14_whole_MARK_protected_left_valid, A_fast_14_whole_MARK_protected_right_valid, A_fast_14_b_below_cap_left_valid, A_fast_14_b_below_cap_right_valid, A_fast_14_return_before_ERROR_left_valid, A_fast_14_return_before_ERROR_right_valid, A_fast_14_no_firing_from_raw_tail_left_valid, A_fast_14_no_firing_from_raw_tail_right_valid, A_fast_14_reopen_valid, A_fast_14_arrival_valid, A_fast_14_b_after_valid, A_fast_14_gain_after_valid, C_fast_15_aux_separation_left_valid, C_fast_15_aux_separation_right_valid, C_fast_15_gain_below_cap_left_valid, C_fast_15_gain_below_cap_right_valid, C_fast_15_ready_at_input_left_valid, C_fast_15_ready_at_input_right_valid, C_fast_15_positive_derivative_coefficient_left_valid, C_fast_15_positive_derivative_coefficient_right_valid, C_fast_15_fixed_flow_increases_left_valid, C_fast_15_fixed_flow_increases_right_valid, C_fast_15_strong_crosses_by_one_left_valid, C_fast_15_strong_crosses_by_one_right_valid, C_fast_15_root_latency_valid, C_fast_15_root_lower_left_valid, C_fast_15_root_lower_right_valid, C_fast_15_root_upper_left_valid, C_fast_15_root_upper_right_valid, C_fast_15_MARK_before_fire_left_valid, C_fast_15_MARK_before_fire_right_valid, C_fast_15_fire_before_ERROR_left_valid, C_fast_15_fire_before_ERROR_right_valid, C_fast_15_ERROR_protected_left_valid, C_fast_15_ERROR_protected_right_valid, C_fast_15_arrival_valid, C_fast_15_b_after_valid, C_fast_15_gain_after_valid, C_fast_15_emission_valid, B_fast_15_aux_separation_left_valid, B_fast_15_aux_separation_right_valid, B_fast_15_gain_below_cap_left_valid, B_fast_15_gain_below_cap_right_valid, B_fast_15_ready_at_input_left_valid, B_fast_15_ready_at_input_right_valid, B_fast_15_positive_derivative_coefficient_left_valid, B_fast_15_positive_derivative_coefficient_right_valid, B_fast_15_fixed_flow_increases_left_valid, B_fast_15_fixed_flow_increases_right_valid, B_fast_15_strong_crosses_by_one_left_valid, B_fast_15_strong_crosses_by_one_right_valid, B_fast_15_root_latency_valid, B_fast_15_root_lower_left_valid, B_fast_15_root_lower_right_valid, B_fast_15_root_upper_left_valid, B_fast_15_root_upper_right_valid, B_fast_15_MARK_before_fire_left_valid, B_fast_15_MARK_before_fire_right_valid, B_fast_15_fire_before_ERROR_left_valid, B_fast_15_fire_before_ERROR_right_valid, B_fast_15_ERROR_protected_left_valid, B_fast_15_ERROR_protected_right_valid, B_fast_15_arrival_valid, B_fast_15_b_after_valid, B_fast_15_gain_after_valid, B_fast_15_emission_valid, A_fast_15_aux_separation_left_valid, A_fast_15_aux_separation_right_valid, A_fast_15_gain_below_cap_left_valid, A_fast_15_gain_below_cap_right_valid, A_fast_15_ready_at_input_left_valid, A_fast_15_ready_at_input_right_valid, A_fast_15_positive_derivative_coefficient_left_valid, A_fast_15_positive_derivative_coefficient_right_valid, A_fast_15_fixed_flow_increases_left_valid, A_fast_15_fixed_flow_increases_right_valid, A_fast_15_strong_crosses_by_one_left_valid, A_fast_15_strong_crosses_by_one_right_valid, A_fast_15_root_latency_valid, A_fast_15_root_lower_left_valid, A_fast_15_root_lower_right_valid, A_fast_15_root_upper_left_valid, A_fast_15_root_upper_right_valid, A_fast_15_MARK_before_fire_left_valid, A_fast_15_MARK_before_fire_right_valid, A_fast_15_fire_before_ERROR_left_valid, A_fast_15_fire_before_ERROR_right_valid, A_fast_15_ERROR_protected_left_valid, A_fast_15_ERROR_protected_right_valid, A_fast_15_arrival_valid, A_fast_15_b_after_valid, A_fast_15_gain_after_valid, A_fast_15_emission_valid, C_fast_16_aux_separation_left_valid, C_fast_16_aux_separation_right_valid, C_fast_16_gain_below_cap_left_valid, C_fast_16_gain_below_cap_right_valid, C_fast_16_ready_at_input_left_valid, C_fast_16_ready_at_input_right_valid⟩

end KernelR.Certificates.Cadence010
