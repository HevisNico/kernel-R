import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence003
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def C_fast_14_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_14_aux_separation_right_valid : C_fast_14_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_aux_separation_right]

def C_fast_14_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_gain_below_cap_left_valid : C_fast_14_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_gain_below_cap_left]

def C_fast_14_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
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

def C_fast_14_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_MARK_before_fire_left_valid : C_fast_14_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_MARK_before_fire_left]

def C_fast_14_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_14_MARK_before_fire_right_valid : C_fast_14_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_MARK_before_fire_right]

def C_fast_14_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_14_fire_before_ERROR_left_valid : C_fast_14_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_fire_before_ERROR_left]

def C_fast_14_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_fire_before_ERROR_right_valid : C_fast_14_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_14_fire_before_ERROR_right]

def C_fast_14_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

def B_fast_14_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_aux_separation_left_valid : B_fast_14_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_aux_separation_left]

def B_fast_14_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_14_aux_separation_right_valid : B_fast_14_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_aux_separation_right]

def B_fast_14_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_gain_below_cap_left_valid : B_fast_14_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_gain_below_cap_left]

def B_fast_14_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
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

def B_fast_14_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_MARK_before_fire_left_valid : B_fast_14_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_MARK_before_fire_left]

def B_fast_14_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_14_MARK_before_fire_right_valid : B_fast_14_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_MARK_before_fire_right]

def B_fast_14_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_14_fire_before_ERROR_left_valid : B_fast_14_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_14_fire_before_ERROR_left]

def B_fast_14_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_14_fire_before_ERROR_right_valid : B_fast_14_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_14_fire_before_ERROR_right]

def B_fast_14_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

def A_fast_14_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_aux_separation_left_valid : A_fast_14_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_aux_separation_left]

def A_fast_14_aux_separation_right : RationalBox := ⟨(19 / 5 : ℚ), (21 / 5 : ℚ)⟩
theorem A_fast_14_aux_separation_right_valid : A_fast_14_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_aux_separation_right]

def A_fast_14_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_gain_below_cap_left_valid : A_fast_14_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_gain_below_cap_left]

def A_fast_14_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_14_gain_below_cap_right_valid : A_fast_14_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_gain_below_cap_right]

def A_fast_14_input_in_SLOW_left : RationalBox := ⟨(7284960741 / 10485760 : ℚ), (113860287 / 163840 : ℚ)⟩
theorem A_fast_14_input_in_SLOW_left_valid : A_fast_14_input_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_input_in_SLOW_left]

def A_fast_14_input_in_SLOW_right : RationalBox := ⟨(913696137 / 1310720 : ℚ), (1827916597 / 2621440 : ℚ)⟩
theorem A_fast_14_input_in_SLOW_right_valid : A_fast_14_input_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_input_in_SLOW_right]

def A_fast_14_input_before_return_left : RationalBox := ⟨(913696137 / 1310720 : ℚ), (1827916597 / 2621440 : ℚ)⟩
theorem A_fast_14_input_before_return_left_valid : A_fast_14_input_before_return_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_input_before_return_left]

def A_fast_14_input_before_return_right : RationalBox := ⟨(3490101727509304871353086648008428468116319 / 5000000000000000000000000000000000000000 : ℚ), (6982206245490269838974017901059609667182761 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_input_before_return_right_valid : A_fast_14_input_before_return_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_input_before_return_right]

def A_fast_14_whole_MARK_protected_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_whole_MARK_protected_left_valid : A_fast_14_whole_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_whole_MARK_protected_left]

def A_fast_14_whole_MARK_protected_right : RationalBox := ⟨(5410680039004326767265307093101157280969 / 10000000000000000000000000000000000000000 : ℚ), (541068003900432676726530709310115728097 / 1000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_whole_MARK_protected_right_valid : A_fast_14_whole_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_whole_MARK_protected_right]

def A_fast_14_b_below_cap_left : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_14_b_below_cap_left_valid : A_fast_14_b_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_b_below_cap_left]

def A_fast_14_b_below_cap_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem A_fast_14_b_below_cap_right_valid : A_fast_14_b_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_b_below_cap_right]

def A_fast_14_return_before_ERROR_left : RationalBox := ⟨(8399508174254111055987070916395699444419 / 10000000000000000000000000000000000000000 : ℚ), (419975408712705552799353545819784972221 / 500000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_return_before_ERROR_left_valid : A_fast_14_return_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_return_before_ERROR_left]

def A_fast_14_return_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_return_before_ERROR_right_valid : A_fast_14_return_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_return_before_ERROR_right]

def A_fast_14_no_firing_from_raw_tail_left : RationalBox := ⟨(570270140356269552797614559639564303409 / 1250000000000000000000000000000000000000 : ℚ), (4562161122850156422380916477116514427273 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_no_firing_from_raw_tail_left_valid : A_fast_14_no_firing_from_raw_tail_left.Valid := by norm_num [RationalBox.Valid, A_fast_14_no_firing_from_raw_tail_left]

def A_fast_14_no_firing_from_raw_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_14_no_firing_from_raw_tail_right_valid : A_fast_14_no_firing_from_raw_tail_right.Valid := by norm_num [RationalBox.Valid, A_fast_14_no_firing_from_raw_tail_right]

def A_fast_14_reopen : RationalBox := ⟨(5410680039004326767265307093101157280969 / 10000000000000000000000000000000000000000 : ℚ), (419975408712705552799353545819784972221 / 500000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_reopen_valid : A_fast_14_reopen.Valid := by norm_num [RationalBox.Valid, A_fast_14_reopen]

def A_fast_14_arrival : RationalBox := ⟨(913696137 / 1310720 : ℚ), (1827916597 / 2621440 : ℚ)⟩
theorem A_fast_14_arrival_valid : A_fast_14_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_14_arrival]

def A_fast_14_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_14_b_after_valid : A_fast_14_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_14_b_after]

def A_fast_14_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_14_gain_after_valid : A_fast_14_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_14_gain_after]

def C_fast_15_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_aux_separation_left_valid : C_fast_15_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_aux_separation_left]

def C_fast_15_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_15_aux_separation_right_valid : C_fast_15_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_aux_separation_right]

def C_fast_15_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_gain_below_cap_left_valid : C_fast_15_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_gain_below_cap_left]

def C_fast_15_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
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

def C_fast_15_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_MARK_before_fire_left_valid : C_fast_15_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_MARK_before_fire_left]

def C_fast_15_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_15_MARK_before_fire_right_valid : C_fast_15_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_MARK_before_fire_right]

def C_fast_15_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_15_fire_before_ERROR_left_valid : C_fast_15_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_15_fire_before_ERROR_left]

def C_fast_15_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_15_fire_before_ERROR_right_valid : C_fast_15_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_15_fire_before_ERROR_right]

def C_fast_15_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

def B_fast_15_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_aux_separation_left_valid : B_fast_15_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_aux_separation_left]

def B_fast_15_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_15_aux_separation_right_valid : B_fast_15_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_aux_separation_right]

def B_fast_15_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_gain_below_cap_left_valid : B_fast_15_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_gain_below_cap_left]

def B_fast_15_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
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

def B_fast_15_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_MARK_before_fire_left_valid : B_fast_15_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_MARK_before_fire_left]

def B_fast_15_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_15_MARK_before_fire_right_valid : B_fast_15_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_MARK_before_fire_right]

def B_fast_15_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_15_fire_before_ERROR_left_valid : B_fast_15_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_15_fire_before_ERROR_left]

def B_fast_15_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_15_fire_before_ERROR_right_valid : B_fast_15_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_15_fire_before_ERROR_right]

def B_fast_15_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
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

def A_fast_15_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_aux_separation_left_valid : A_fast_15_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_aux_separation_left]

def A_fast_15_aux_separation_right : RationalBox := ⟨(19 / 5 : ℚ), (21 / 5 : ℚ)⟩
theorem A_fast_15_aux_separation_right_valid : A_fast_15_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_aux_separation_right]

def A_fast_15_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_gain_below_cap_left_valid : A_fast_15_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_gain_below_cap_left]

def A_fast_15_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_15_gain_below_cap_right_valid : A_fast_15_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_gain_below_cap_right]

def A_fast_15_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_15_ready_at_input_left_valid : A_fast_15_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_ready_at_input_left]

def A_fast_15_ready_at_input_right : RationalBox := ⟨(1480024591287294447200646454180215027779 / 500000000000000000000000000000000000000 : ℚ), (36589319960995673232734692906898842719031 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_ready_at_input_right_valid : A_fast_15_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_ready_at_input_right]

def A_fast_15_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_15_positive_derivative_coefficient_left_valid : A_fast_15_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_positive_derivative_coefficient_left]

def A_fast_15_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (13151132199294772766572537669866716161593 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_positive_derivative_coefficient_right_valid : A_fast_15_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_positive_derivative_coefficient_right]

def A_fast_15_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_15_fixed_flow_increases_left_valid : A_fast_15_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_fixed_flow_increases_left]

def A_fast_15_fixed_flow_increases_right : RationalBox := ⟨(986707788604585763674749378820854568279 / 1250000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_fixed_flow_increases_right_valid : A_fast_15_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_fixed_flow_increases_right]

def A_fast_15_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_15_strong_crosses_by_one_left_valid : A_fast_15_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_strong_crosses_by_one_left]

def A_fast_15_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19974731885421902248437127360413097323349 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_strong_crosses_by_one_right_valid : A_fast_15_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_strong_crosses_by_one_right]

def A_fast_15_root_latency : RationalBox := ⟨(57709 / 262144 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_15_root_latency_valid : A_fast_15_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_latency]

def A_fast_15_root_lower_left : RationalBox := ⟨(4606485538091448621000922971047320677173 / 5000000000000000000000000000000000000000 : ℚ), (124999953248230073363544885204690347809 / 125000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_root_lower_left_valid : A_fast_15_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_lower_left]

def A_fast_15_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_15_root_lower_right_valid : A_fast_15_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_lower_right]

def A_fast_15_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_15_root_upper_left_valid : A_fast_15_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_upper_left]

def A_fast_15_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (10776383195508779833435195898857142755263 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_root_upper_right_valid : A_fast_15_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_root_upper_right]

def A_fast_15_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_MARK_before_fire_left_valid : A_fast_15_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_MARK_before_fire_left]

def A_fast_15_MARK_before_fire_right : RationalBox := ⟨(57709 / 262144 : ℚ), (57709 / 262144 : ℚ)⟩
theorem A_fast_15_MARK_before_fire_right_valid : A_fast_15_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_MARK_before_fire_right]

def A_fast_15_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem A_fast_15_fire_before_ERROR_left_valid : A_fast_15_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_fire_before_ERROR_left]

def A_fast_15_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_fire_before_ERROR_right_valid : A_fast_15_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_fire_before_ERROR_right]

def A_fast_15_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_ERROR_protected_left_valid : A_fast_15_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_15_ERROR_protected_left]

def A_fast_15_ERROR_protected_right : RationalBox := ⟨(18156851554018871506207431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36314972208775289695841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_ERROR_protected_right_valid : A_fast_15_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_15_ERROR_protected_right]

def A_fast_15_arrival : RationalBox := ⟨(918939017 / 1310720 : ℚ), (1838402357 / 2621440 : ℚ)⟩
theorem A_fast_15_arrival_valid : A_fast_15_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_15_arrival]

def A_fast_15_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem A_fast_15_b_after_valid : A_fast_15_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_15_b_after]

def A_fast_15_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_15_gain_after_valid : A_fast_15_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_15_gain_after]

def A_fast_15_emission : RationalBox := ⟨(459613781 / 655360 : ℚ), (3678101919 / 5242880 : ℚ)⟩
theorem A_fast_15_emission_valid : A_fast_15_emission.Valid := by norm_num [RationalBox.Valid, A_fast_15_emission]

def C_fast_16_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_16_aux_separation_left_valid : C_fast_16_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_16_aux_separation_left]

def C_fast_16_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_16_aux_separation_right_valid : C_fast_16_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_16_aux_separation_right]

def C_fast_16_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_16_gain_below_cap_left_valid : C_fast_16_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_16_gain_below_cap_left]

def C_fast_16_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
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

end KernelR.Certificates.Cadence003
