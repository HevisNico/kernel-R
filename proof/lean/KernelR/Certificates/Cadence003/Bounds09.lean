import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence003
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def A_fast_11_arrival : RationalBox := ⟨(7183518651 / 10485760 : ℚ), (1796459317 / 2621440 : ℚ)⟩
theorem A_fast_11_arrival_valid : A_fast_11_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_11_arrival]

def A_fast_11_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem A_fast_11_b_after_valid : A_fast_11_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_11_b_after]

def A_fast_11_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_gain_after_valid : A_fast_11_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_11_gain_after]

def A_fast_11_emission : RationalBox := ⟨(898795947 / 1310720 : ℚ), (112385727 / 163840 : ℚ)⟩
theorem A_fast_11_emission_valid : A_fast_11_emission.Valid := by norm_num [RationalBox.Valid, A_fast_11_emission]

def C_fast_12_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_aux_separation_left_valid : C_fast_12_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_aux_separation_left]

def C_fast_12_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_12_aux_separation_right_valid : C_fast_12_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_aux_separation_right]

def C_fast_12_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_gain_below_cap_left_valid : C_fast_12_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_gain_below_cap_left]

def C_fast_12_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_12_gain_below_cap_right_valid : C_fast_12_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_gain_below_cap_right]

def C_fast_12_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_12_ready_at_input_left_valid : C_fast_12_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_ready_at_input_left]

def C_fast_12_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_ready_at_input_right_valid : C_fast_12_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_ready_at_input_right]

def C_fast_12_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_12_positive_derivative_coefficient_left_valid : C_fast_12_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_positive_derivative_coefficient_left]

def C_fast_12_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_positive_derivative_coefficient_right_valid : C_fast_12_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_positive_derivative_coefficient_right]

def C_fast_12_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_12_fixed_flow_increases_left_valid : C_fast_12_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_fixed_flow_increases_left]

def C_fast_12_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_fixed_flow_increases_right_valid : C_fast_12_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_fixed_flow_increases_right]

def C_fast_12_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_12_strong_crosses_by_one_left_valid : C_fast_12_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_strong_crosses_by_one_left]

def C_fast_12_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_strong_crosses_by_one_right_valid : C_fast_12_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_strong_crosses_by_one_right]

def C_fast_12_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_12_root_latency_valid : C_fast_12_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_12_root_latency]

def C_fast_12_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_root_lower_left_valid : C_fast_12_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_root_lower_left]

def C_fast_12_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_12_root_lower_right_valid : C_fast_12_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_root_lower_right]

def C_fast_12_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_12_root_upper_left_valid : C_fast_12_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_root_upper_left]

def C_fast_12_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_root_upper_right_valid : C_fast_12_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_root_upper_right]

def C_fast_12_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_MARK_before_fire_left_valid : C_fast_12_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_MARK_before_fire_left]

def C_fast_12_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_12_MARK_before_fire_right_valid : C_fast_12_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_MARK_before_fire_right]

def C_fast_12_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_12_fire_before_ERROR_left_valid : C_fast_12_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_fire_before_ERROR_left]

def C_fast_12_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_fire_before_ERROR_right_valid : C_fast_12_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_fire_before_ERROR_right]

def C_fast_12_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_ERROR_protected_left_valid : C_fast_12_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_12_ERROR_protected_left]

def C_fast_12_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_ERROR_protected_right_valid : C_fast_12_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_12_ERROR_protected_right]

def C_fast_12_arrival : RationalBox := ⟨(688 / 1 : ℚ), (688 / 1 : ℚ)⟩
theorem C_fast_12_arrival_valid : C_fast_12_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_12_arrival]

def C_fast_12_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_12_b_after_valid : C_fast_12_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_12_b_after]

def C_fast_12_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_12_gain_after_valid : C_fast_12_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_12_gain_after]

def C_fast_12_emission : RationalBox := ⟨(360839861 / 524288 : ℚ), (721679729 / 1048576 : ℚ)⟩
theorem C_fast_12_emission_valid : C_fast_12_emission.Valid := by norm_num [RationalBox.Valid, C_fast_12_emission]

def B_fast_12_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_aux_separation_left_valid : B_fast_12_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_aux_separation_left]

def B_fast_12_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_12_aux_separation_right_valid : B_fast_12_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_aux_separation_right]

def B_fast_12_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_gain_below_cap_left_valid : B_fast_12_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_gain_below_cap_left]

def B_fast_12_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_fast_12_gain_below_cap_right_valid : B_fast_12_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_gain_below_cap_right]

def B_fast_12_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_12_ready_at_input_left_valid : B_fast_12_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_ready_at_input_left]

def B_fast_12_ready_at_input_right : RationalBox := ⟨(2412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2312318539517505446917568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_ready_at_input_right_valid : B_fast_12_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_ready_at_input_right]

def B_fast_12_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_12_positive_derivative_coefficient_left_valid : B_fast_12_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_positive_derivative_coefficient_left]

def B_fast_12_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_positive_derivative_coefficient_right_valid : B_fast_12_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_positive_derivative_coefficient_right]

def B_fast_12_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_12_fixed_flow_increases_left_valid : B_fast_12_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_fixed_flow_increases_left]

def B_fast_12_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_fixed_flow_increases_right_valid : B_fast_12_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_fixed_flow_increases_right]

def B_fast_12_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_12_strong_crosses_by_one_left_valid : B_fast_12_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_strong_crosses_by_one_left]

def B_fast_12_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_strong_crosses_by_one_right_valid : B_fast_12_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_strong_crosses_by_one_right]

def B_fast_12_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_12_root_latency_valid : B_fast_12_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_12_root_latency]

def B_fast_12_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_root_lower_left_valid : B_fast_12_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_root_lower_left]

def B_fast_12_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_12_root_lower_right_valid : B_fast_12_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_root_lower_right]

def B_fast_12_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_12_root_upper_left_valid : B_fast_12_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_root_upper_left]

def B_fast_12_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_root_upper_right_valid : B_fast_12_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_root_upper_right]

def B_fast_12_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_MARK_before_fire_left_valid : B_fast_12_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_MARK_before_fire_left]

def B_fast_12_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_12_MARK_before_fire_right_valid : B_fast_12_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_MARK_before_fire_right]

def B_fast_12_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_12_fire_before_ERROR_left_valid : B_fast_12_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_fire_before_ERROR_left]

def B_fast_12_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_fire_before_ERROR_right_valid : B_fast_12_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_fire_before_ERROR_right]

def B_fast_12_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_ERROR_protected_left_valid : B_fast_12_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_12_ERROR_protected_left]

def B_fast_12_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_ERROR_protected_right_valid : B_fast_12_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_12_ERROR_protected_right]

def B_fast_12_arrival : RationalBox := ⟨(1804985737 / 2621440 : ℚ), (3610495797 / 5242880 : ℚ)⟩
theorem B_fast_12_arrival_valid : B_fast_12_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_12_arrival]

def B_fast_12_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_12_b_after_valid : B_fast_12_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_12_b_after]

def B_fast_12_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_12_gain_after_valid : B_fast_12_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_12_gain_after]

def B_fast_12_emission : RationalBox := ⟨(902817161 / 1310720 : ℚ), (1805896501 / 2621440 : ℚ)⟩
theorem B_fast_12_emission_valid : B_fast_12_emission.Valid := by norm_num [RationalBox.Valid, B_fast_12_emission]

def A_fast_12_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_aux_separation_left_valid : A_fast_12_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_12_aux_separation_left]

def A_fast_12_aux_separation_right : RationalBox := ⟨(19922909 / 5242880 : ℚ), (44261587 / 10485760 : ℚ)⟩
theorem A_fast_12_aux_separation_right_valid : A_fast_12_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_12_aux_separation_right]

def A_fast_12_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_gain_below_cap_left_valid : A_fast_12_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_12_gain_below_cap_left]

def A_fast_12_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_12_gain_below_cap_right_valid : A_fast_12_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_12_gain_below_cap_right]

def A_fast_12_input_in_SLOW_left : RationalBox := ⟨(900106667 / 1310720 : ℚ), (112549567 / 163840 : ℚ)⟩
theorem A_fast_12_input_in_SLOW_left_valid : A_fast_12_input_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, A_fast_12_input_in_SLOW_left]

def A_fast_12_input_in_SLOW_right : RationalBox := ⟨(903210377 / 1310720 : ℚ), (1806945077 / 2621440 : ℚ)⟩
theorem A_fast_12_input_in_SLOW_right_valid : A_fast_12_input_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, A_fast_12_input_in_SLOW_right]

def A_fast_12_input_before_return_left : RationalBox := ⟨(903210377 / 1310720 : ℚ), (1806945077 / 2621440 : ℚ)⟩
theorem A_fast_12_input_before_return_left_valid : A_fast_12_input_before_return_left.Valid := by norm_num [RationalBox.Valid, A_fast_12_input_before_return_left]

def A_fast_12_input_before_return_right : RationalBox := ⟨(864771386938803911709955538662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (6920388276589456509885745164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_input_before_return_right_valid : A_fast_12_input_before_return_right.Valid := by norm_num [RationalBox.Valid, A_fast_12_input_before_return_right]

def A_fast_12_whole_MARK_protected_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_whole_MARK_protected_left_valid : A_fast_12_whole_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_12_whole_MARK_protected_left]

def A_fast_12_whole_MARK_protected_right : RationalBox := ⟨(3260555732248831627235671474911160871641 / 2000000000000000000000000000000000000000 : ℚ), (8151389330622079068089178687277902179103 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_whole_MARK_protected_right_valid : A_fast_12_whole_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_12_whole_MARK_protected_right]

def A_fast_12_b_below_cap_left : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem A_fast_12_b_below_cap_left_valid : A_fast_12_b_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_12_b_below_cap_left]

def A_fast_12_b_below_cap_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem A_fast_12_b_below_cap_right_valid : A_fast_12_b_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_12_b_below_cap_right]

def A_fast_12_whole_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_whole_ERROR_protected_left_valid : A_fast_12_whole_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_12_whole_ERROR_protected_left]

def A_fast_12_whole_ERROR_protected_right : RationalBox := ⟨(3260555732248831627235671474911160871641 / 2000000000000000000000000000000000000000 : ℚ), (8151389330622079068089178687277902179103 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_whole_ERROR_protected_right_valid : A_fast_12_whole_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_12_whole_ERROR_protected_right]

def A_fast_12_no_firing_from_raw_tail_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem A_fast_12_no_firing_from_raw_tail_left_valid : A_fast_12_no_firing_from_raw_tail_left.Valid := by norm_num [RationalBox.Valid, A_fast_12_no_firing_from_raw_tail_left]

def A_fast_12_no_firing_from_raw_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_12_no_firing_from_raw_tail_right_valid : A_fast_12_no_firing_from_raw_tail_right.Valid := by norm_num [RationalBox.Valid, A_fast_12_no_firing_from_raw_tail_right]

def A_fast_12_reopen : RationalBox := ⟨(3260555732248831627235671474911160871641 / 2000000000000000000000000000000000000000 : ℚ), (9533456180443528643755405688633883052761 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_reopen_valid : A_fast_12_reopen.Valid := by norm_num [RationalBox.Valid, A_fast_12_reopen]

def A_fast_12_arrival : RationalBox := ⟨(903210377 / 1310720 : ℚ), (1806945077 / 2621440 : ℚ)⟩
theorem A_fast_12_arrival_valid : A_fast_12_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_12_arrival]

def A_fast_12_b_after : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem A_fast_12_b_after_valid : A_fast_12_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_12_b_after]

def A_fast_12_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_12_gain_after_valid : A_fast_12_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_12_gain_after]

def C_fast_13_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_aux_separation_left_valid : C_fast_13_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_aux_separation_left]

def C_fast_13_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_13_aux_separation_right_valid : C_fast_13_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_aux_separation_right]

def C_fast_13_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_gain_below_cap_left_valid : C_fast_13_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_gain_below_cap_left]

def C_fast_13_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_13_gain_below_cap_right_valid : C_fast_13_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_gain_below_cap_right]

def C_fast_13_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_13_ready_at_input_left_valid : C_fast_13_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_ready_at_input_left]

def C_fast_13_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_ready_at_input_right_valid : C_fast_13_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_ready_at_input_right]

def C_fast_13_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_13_positive_derivative_coefficient_left_valid : C_fast_13_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_positive_derivative_coefficient_left]

def C_fast_13_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_positive_derivative_coefficient_right_valid : C_fast_13_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_positive_derivative_coefficient_right]

def C_fast_13_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_13_fixed_flow_increases_left_valid : C_fast_13_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_fixed_flow_increases_left]

def C_fast_13_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_fixed_flow_increases_right_valid : C_fast_13_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_fixed_flow_increases_right]

def C_fast_13_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_13_strong_crosses_by_one_left_valid : C_fast_13_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_strong_crosses_by_one_left]

def C_fast_13_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_strong_crosses_by_one_right_valid : C_fast_13_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_strong_crosses_by_one_right]

def C_fast_13_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_13_root_latency_valid : C_fast_13_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_13_root_latency]

def C_fast_13_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_root_lower_left_valid : C_fast_13_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_root_lower_left]

def C_fast_13_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_13_root_lower_right_valid : C_fast_13_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_root_lower_right]

def C_fast_13_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_13_root_upper_left_valid : C_fast_13_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_root_upper_left]

def C_fast_13_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_root_upper_right_valid : C_fast_13_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_root_upper_right]

def C_fast_13_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_MARK_before_fire_left_valid : C_fast_13_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_MARK_before_fire_left]

def C_fast_13_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_13_MARK_before_fire_right_valid : C_fast_13_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_MARK_before_fire_right]

def C_fast_13_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_13_fire_before_ERROR_left_valid : C_fast_13_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_fire_before_ERROR_left]

def C_fast_13_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_fire_before_ERROR_right_valid : C_fast_13_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_fire_before_ERROR_right]

def C_fast_13_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_ERROR_protected_left_valid : C_fast_13_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_13_ERROR_protected_left]

def C_fast_13_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_ERROR_protected_right_valid : C_fast_13_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_13_ERROR_protected_right]

def C_fast_13_arrival : RationalBox := ⟨(692 / 1 : ℚ), (692 / 1 : ℚ)⟩
theorem C_fast_13_arrival_valid : C_fast_13_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_13_arrival]

def C_fast_13_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_13_b_after_valid : C_fast_13_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_13_b_after]

def C_fast_13_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_13_gain_after_valid : C_fast_13_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_13_gain_after]

def C_fast_13_emission : RationalBox := ⟨(362937013 / 524288 : ℚ), (725874033 / 1048576 : ℚ)⟩
theorem C_fast_13_emission_valid : C_fast_13_emission.Valid := by norm_num [RationalBox.Valid, C_fast_13_emission]

def B_fast_13_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_aux_separation_left_valid : B_fast_13_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_aux_separation_left]

def B_fast_13_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_13_aux_separation_right_valid : B_fast_13_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_aux_separation_right]

def B_fast_13_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_gain_below_cap_left_valid : B_fast_13_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_gain_below_cap_left]

def B_fast_13_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_fast_13_gain_below_cap_right_valid : B_fast_13_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_gain_below_cap_right]

def B_fast_13_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_13_ready_at_input_left_valid : B_fast_13_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_ready_at_input_left]

def B_fast_13_ready_at_input_right : RationalBox := ⟨(2412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (2206782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_ready_at_input_right_valid : B_fast_13_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_ready_at_input_right]

def B_fast_13_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_13_positive_derivative_coefficient_left_valid : B_fast_13_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_positive_derivative_coefficient_left]

def B_fast_13_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_positive_derivative_coefficient_right_valid : B_fast_13_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_positive_derivative_coefficient_right]

def B_fast_13_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_13_fixed_flow_increases_left_valid : B_fast_13_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_fixed_flow_increases_left]

def B_fast_13_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_fixed_flow_increases_right_valid : B_fast_13_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_fixed_flow_increases_right]

def B_fast_13_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_13_strong_crosses_by_one_left_valid : B_fast_13_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_strong_crosses_by_one_left]

def B_fast_13_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_strong_crosses_by_one_right_valid : B_fast_13_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_strong_crosses_by_one_right]

def B_fast_13_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_13_root_latency_valid : B_fast_13_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_13_root_latency]

def B_fast_13_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_root_lower_left_valid : B_fast_13_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_root_lower_left]

def B_fast_13_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_13_root_lower_right_valid : B_fast_13_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_root_lower_right]

def B_fast_13_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_13_root_upper_left_valid : B_fast_13_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_root_upper_left]

def B_fast_13_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_root_upper_right_valid : B_fast_13_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_root_upper_right]

def B_fast_13_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_MARK_before_fire_left_valid : B_fast_13_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_MARK_before_fire_left]

def B_fast_13_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem B_fast_13_MARK_before_fire_right_valid : B_fast_13_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_MARK_before_fire_right]

def B_fast_13_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_13_fire_before_ERROR_left_valid : B_fast_13_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_fire_before_ERROR_left]

def B_fast_13_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_fire_before_ERROR_right_valid : B_fast_13_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_fire_before_ERROR_right]

def B_fast_13_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_ERROR_protected_left_valid : B_fast_13_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_13_ERROR_protected_left]

def B_fast_13_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_ERROR_protected_right_valid : B_fast_13_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_13_ERROR_protected_right]

def B_fast_13_arrival : RationalBox := ⟨(1815471497 / 2621440 : ℚ), (3631467317 / 5242880 : ℚ)⟩
theorem B_fast_13_arrival_valid : B_fast_13_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_13_arrival]

def B_fast_13_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_13_b_after_valid : B_fast_13_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_13_b_after]

def B_fast_13_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_13_gain_after_valid : B_fast_13_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_13_gain_after]

def B_fast_13_emission : RationalBox := ⟨(908060041 / 1310720 : ℚ), (1816382261 / 2621440 : ℚ)⟩
theorem B_fast_13_emission_valid : B_fast_13_emission.Valid := by norm_num [RationalBox.Valid, B_fast_13_emission]

def A_fast_13_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_aux_separation_left_valid : A_fast_13_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_aux_separation_left]

def A_fast_13_aux_separation_right : RationalBox := ⟨(19 / 5 : ℚ), (21 / 5 : ℚ)⟩
theorem A_fast_13_aux_separation_right_valid : A_fast_13_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_aux_separation_right]

def A_fast_13_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_gain_below_cap_left_valid : A_fast_13_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_gain_below_cap_left]

def A_fast_13_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_13_gain_below_cap_right_valid : A_fast_13_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_gain_below_cap_right]

def A_fast_13_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_13_ready_at_input_left_valid : A_fast_13_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_ready_at_input_left]

def A_fast_13_ready_at_input_right : RationalBox := ⟨(9466543819556471356244594311366116947239 / 5000000000000000000000000000000000000000 : ℚ), (5139444267751168372764328525088839128359 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_ready_at_input_right_valid : A_fast_13_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_ready_at_input_right]

def A_fast_13_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_13_positive_derivative_coefficient_left_valid : A_fast_13_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_positive_derivative_coefficient_left]

def A_fast_13_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_positive_derivative_coefficient_right_valid : A_fast_13_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_positive_derivative_coefficient_right]

def A_fast_13_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_13_fixed_flow_increases_left_valid : A_fast_13_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_fixed_flow_increases_left]

def A_fast_13_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_fixed_flow_increases_right_valid : A_fast_13_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_fixed_flow_increases_right]

def A_fast_13_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_13_strong_crosses_by_one_left_valid : A_fast_13_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_strong_crosses_by_one_left]

def A_fast_13_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_strong_crosses_by_one_right_valid : A_fast_13_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_strong_crosses_by_one_right]

def A_fast_13_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_13_root_latency_valid : A_fast_13_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_13_root_latency]

def A_fast_13_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_root_lower_left_valid : A_fast_13_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_root_lower_left]

def A_fast_13_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_13_root_lower_right_valid : A_fast_13_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_root_lower_right]

def A_fast_13_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_13_root_upper_left_valid : A_fast_13_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_root_upper_left]

def A_fast_13_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_root_upper_right_valid : A_fast_13_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_root_upper_right]

def A_fast_13_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_MARK_before_fire_left_valid : A_fast_13_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_MARK_before_fire_left]

def A_fast_13_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem A_fast_13_MARK_before_fire_right_valid : A_fast_13_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_MARK_before_fire_right]

def A_fast_13_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_13_fire_before_ERROR_left_valid : A_fast_13_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_fire_before_ERROR_left]

def A_fast_13_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_fire_before_ERROR_right_valid : A_fast_13_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_fire_before_ERROR_right]

def A_fast_13_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_ERROR_protected_left_valid : A_fast_13_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_13_ERROR_protected_left]

def A_fast_13_ERROR_protected_right : RationalBox := ⟨(24627572083279480728086648008428468116319 / 5000000000000000000000000000000000000000 : ℚ), (49257481642918764755267901059609667182761 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_ERROR_protected_right_valid : A_fast_13_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_13_ERROR_protected_right]

def A_fast_13_arrival : RationalBox := ⟨(908453257 / 1310720 : ℚ), (1817430837 / 2621440 : ℚ)⟩
theorem A_fast_13_arrival_valid : A_fast_13_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_13_arrival]

def A_fast_13_b_after : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem A_fast_13_b_after_valid : A_fast_13_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_13_b_after]

def A_fast_13_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_13_gain_after_valid : A_fast_13_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_13_gain_after]

def A_fast_13_emission : RationalBox := ⟨(7274474981 / 10485760 : ℚ), (113696447 / 163840 : ℚ)⟩
theorem A_fast_13_emission_valid : A_fast_13_emission.Valid := by norm_num [RationalBox.Valid, A_fast_13_emission]

def C_fast_14_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_14_aux_separation_left_valid : C_fast_14_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_14_aux_separation_left]

def Bounds09Valid : Prop :=
  A_fast_11_arrival.Valid ∧
  A_fast_11_b_after.Valid ∧
  A_fast_11_gain_after.Valid ∧
  A_fast_11_emission.Valid ∧
  C_fast_12_aux_separation_left.Valid ∧
  C_fast_12_aux_separation_right.Valid ∧
  C_fast_12_gain_below_cap_left.Valid ∧
  C_fast_12_gain_below_cap_right.Valid ∧
  C_fast_12_ready_at_input_left.Valid ∧
  C_fast_12_ready_at_input_right.Valid ∧
  C_fast_12_positive_derivative_coefficient_left.Valid ∧
  C_fast_12_positive_derivative_coefficient_right.Valid ∧
  C_fast_12_fixed_flow_increases_left.Valid ∧
  C_fast_12_fixed_flow_increases_right.Valid ∧
  C_fast_12_strong_crosses_by_one_left.Valid ∧
  C_fast_12_strong_crosses_by_one_right.Valid ∧
  C_fast_12_root_latency.Valid ∧
  C_fast_12_root_lower_left.Valid ∧
  C_fast_12_root_lower_right.Valid ∧
  C_fast_12_root_upper_left.Valid ∧
  C_fast_12_root_upper_right.Valid ∧
  C_fast_12_MARK_before_fire_left.Valid ∧
  C_fast_12_MARK_before_fire_right.Valid ∧
  C_fast_12_fire_before_ERROR_left.Valid ∧
  C_fast_12_fire_before_ERROR_right.Valid ∧
  C_fast_12_ERROR_protected_left.Valid ∧
  C_fast_12_ERROR_protected_right.Valid ∧
  C_fast_12_arrival.Valid ∧
  C_fast_12_b_after.Valid ∧
  C_fast_12_gain_after.Valid ∧
  C_fast_12_emission.Valid ∧
  B_fast_12_aux_separation_left.Valid ∧
  B_fast_12_aux_separation_right.Valid ∧
  B_fast_12_gain_below_cap_left.Valid ∧
  B_fast_12_gain_below_cap_right.Valid ∧
  B_fast_12_ready_at_input_left.Valid ∧
  B_fast_12_ready_at_input_right.Valid ∧
  B_fast_12_positive_derivative_coefficient_left.Valid ∧
  B_fast_12_positive_derivative_coefficient_right.Valid ∧
  B_fast_12_fixed_flow_increases_left.Valid ∧
  B_fast_12_fixed_flow_increases_right.Valid ∧
  B_fast_12_strong_crosses_by_one_left.Valid ∧
  B_fast_12_strong_crosses_by_one_right.Valid ∧
  B_fast_12_root_latency.Valid ∧
  B_fast_12_root_lower_left.Valid ∧
  B_fast_12_root_lower_right.Valid ∧
  B_fast_12_root_upper_left.Valid ∧
  B_fast_12_root_upper_right.Valid ∧
  B_fast_12_MARK_before_fire_left.Valid ∧
  B_fast_12_MARK_before_fire_right.Valid ∧
  B_fast_12_fire_before_ERROR_left.Valid ∧
  B_fast_12_fire_before_ERROR_right.Valid ∧
  B_fast_12_ERROR_protected_left.Valid ∧
  B_fast_12_ERROR_protected_right.Valid ∧
  B_fast_12_arrival.Valid ∧
  B_fast_12_b_after.Valid ∧
  B_fast_12_gain_after.Valid ∧
  B_fast_12_emission.Valid ∧
  A_fast_12_aux_separation_left.Valid ∧
  A_fast_12_aux_separation_right.Valid ∧
  A_fast_12_gain_below_cap_left.Valid ∧
  A_fast_12_gain_below_cap_right.Valid ∧
  A_fast_12_input_in_SLOW_left.Valid ∧
  A_fast_12_input_in_SLOW_right.Valid ∧
  A_fast_12_input_before_return_left.Valid ∧
  A_fast_12_input_before_return_right.Valid ∧
  A_fast_12_whole_MARK_protected_left.Valid ∧
  A_fast_12_whole_MARK_protected_right.Valid ∧
  A_fast_12_b_below_cap_left.Valid ∧
  A_fast_12_b_below_cap_right.Valid ∧
  A_fast_12_whole_ERROR_protected_left.Valid ∧
  A_fast_12_whole_ERROR_protected_right.Valid ∧
  A_fast_12_no_firing_from_raw_tail_left.Valid ∧
  A_fast_12_no_firing_from_raw_tail_right.Valid ∧
  A_fast_12_reopen.Valid ∧
  A_fast_12_arrival.Valid ∧
  A_fast_12_b_after.Valid ∧
  A_fast_12_gain_after.Valid ∧
  C_fast_13_aux_separation_left.Valid ∧
  C_fast_13_aux_separation_right.Valid ∧
  C_fast_13_gain_below_cap_left.Valid ∧
  C_fast_13_gain_below_cap_right.Valid ∧
  C_fast_13_ready_at_input_left.Valid ∧
  C_fast_13_ready_at_input_right.Valid ∧
  C_fast_13_positive_derivative_coefficient_left.Valid ∧
  C_fast_13_positive_derivative_coefficient_right.Valid ∧
  C_fast_13_fixed_flow_increases_left.Valid ∧
  C_fast_13_fixed_flow_increases_right.Valid ∧
  C_fast_13_strong_crosses_by_one_left.Valid ∧
  C_fast_13_strong_crosses_by_one_right.Valid ∧
  C_fast_13_root_latency.Valid ∧
  C_fast_13_root_lower_left.Valid ∧
  C_fast_13_root_lower_right.Valid ∧
  C_fast_13_root_upper_left.Valid ∧
  C_fast_13_root_upper_right.Valid ∧
  C_fast_13_MARK_before_fire_left.Valid ∧
  C_fast_13_MARK_before_fire_right.Valid ∧
  C_fast_13_fire_before_ERROR_left.Valid ∧
  C_fast_13_fire_before_ERROR_right.Valid ∧
  C_fast_13_ERROR_protected_left.Valid ∧
  C_fast_13_ERROR_protected_right.Valid ∧
  C_fast_13_arrival.Valid ∧
  C_fast_13_b_after.Valid ∧
  C_fast_13_gain_after.Valid ∧
  C_fast_13_emission.Valid ∧
  B_fast_13_aux_separation_left.Valid ∧
  B_fast_13_aux_separation_right.Valid ∧
  B_fast_13_gain_below_cap_left.Valid ∧
  B_fast_13_gain_below_cap_right.Valid ∧
  B_fast_13_ready_at_input_left.Valid ∧
  B_fast_13_ready_at_input_right.Valid ∧
  B_fast_13_positive_derivative_coefficient_left.Valid ∧
  B_fast_13_positive_derivative_coefficient_right.Valid ∧
  B_fast_13_fixed_flow_increases_left.Valid ∧
  B_fast_13_fixed_flow_increases_right.Valid ∧
  B_fast_13_strong_crosses_by_one_left.Valid ∧
  B_fast_13_strong_crosses_by_one_right.Valid ∧
  B_fast_13_root_latency.Valid ∧
  B_fast_13_root_lower_left.Valid ∧
  B_fast_13_root_lower_right.Valid ∧
  B_fast_13_root_upper_left.Valid ∧
  B_fast_13_root_upper_right.Valid ∧
  B_fast_13_MARK_before_fire_left.Valid ∧
  B_fast_13_MARK_before_fire_right.Valid ∧
  B_fast_13_fire_before_ERROR_left.Valid ∧
  B_fast_13_fire_before_ERROR_right.Valid ∧
  B_fast_13_ERROR_protected_left.Valid ∧
  B_fast_13_ERROR_protected_right.Valid ∧
  B_fast_13_arrival.Valid ∧
  B_fast_13_b_after.Valid ∧
  B_fast_13_gain_after.Valid ∧
  B_fast_13_emission.Valid ∧
  A_fast_13_aux_separation_left.Valid ∧
  A_fast_13_aux_separation_right.Valid ∧
  A_fast_13_gain_below_cap_left.Valid ∧
  A_fast_13_gain_below_cap_right.Valid ∧
  A_fast_13_ready_at_input_left.Valid ∧
  A_fast_13_ready_at_input_right.Valid ∧
  A_fast_13_positive_derivative_coefficient_left.Valid ∧
  A_fast_13_positive_derivative_coefficient_right.Valid ∧
  A_fast_13_fixed_flow_increases_left.Valid ∧
  A_fast_13_fixed_flow_increases_right.Valid ∧
  A_fast_13_strong_crosses_by_one_left.Valid ∧
  A_fast_13_strong_crosses_by_one_right.Valid ∧
  A_fast_13_root_latency.Valid ∧
  A_fast_13_root_lower_left.Valid ∧
  A_fast_13_root_lower_right.Valid ∧
  A_fast_13_root_upper_left.Valid ∧
  A_fast_13_root_upper_right.Valid ∧
  A_fast_13_MARK_before_fire_left.Valid ∧
  A_fast_13_MARK_before_fire_right.Valid ∧
  A_fast_13_fire_before_ERROR_left.Valid ∧
  A_fast_13_fire_before_ERROR_right.Valid ∧
  A_fast_13_ERROR_protected_left.Valid ∧
  A_fast_13_ERROR_protected_right.Valid ∧
  A_fast_13_arrival.Valid ∧
  A_fast_13_b_after.Valid ∧
  A_fast_13_gain_after.Valid ∧
  A_fast_13_emission.Valid ∧
  C_fast_14_aux_separation_left.Valid
theorem Bounds09Valid_verified : Bounds09Valid := by
  exact ⟨A_fast_11_arrival_valid, A_fast_11_b_after_valid, A_fast_11_gain_after_valid, A_fast_11_emission_valid, C_fast_12_aux_separation_left_valid, C_fast_12_aux_separation_right_valid, C_fast_12_gain_below_cap_left_valid, C_fast_12_gain_below_cap_right_valid, C_fast_12_ready_at_input_left_valid, C_fast_12_ready_at_input_right_valid, C_fast_12_positive_derivative_coefficient_left_valid, C_fast_12_positive_derivative_coefficient_right_valid, C_fast_12_fixed_flow_increases_left_valid, C_fast_12_fixed_flow_increases_right_valid, C_fast_12_strong_crosses_by_one_left_valid, C_fast_12_strong_crosses_by_one_right_valid, C_fast_12_root_latency_valid, C_fast_12_root_lower_left_valid, C_fast_12_root_lower_right_valid, C_fast_12_root_upper_left_valid, C_fast_12_root_upper_right_valid, C_fast_12_MARK_before_fire_left_valid, C_fast_12_MARK_before_fire_right_valid, C_fast_12_fire_before_ERROR_left_valid, C_fast_12_fire_before_ERROR_right_valid, C_fast_12_ERROR_protected_left_valid, C_fast_12_ERROR_protected_right_valid, C_fast_12_arrival_valid, C_fast_12_b_after_valid, C_fast_12_gain_after_valid, C_fast_12_emission_valid, B_fast_12_aux_separation_left_valid, B_fast_12_aux_separation_right_valid, B_fast_12_gain_below_cap_left_valid, B_fast_12_gain_below_cap_right_valid, B_fast_12_ready_at_input_left_valid, B_fast_12_ready_at_input_right_valid, B_fast_12_positive_derivative_coefficient_left_valid, B_fast_12_positive_derivative_coefficient_right_valid, B_fast_12_fixed_flow_increases_left_valid, B_fast_12_fixed_flow_increases_right_valid, B_fast_12_strong_crosses_by_one_left_valid, B_fast_12_strong_crosses_by_one_right_valid, B_fast_12_root_latency_valid, B_fast_12_root_lower_left_valid, B_fast_12_root_lower_right_valid, B_fast_12_root_upper_left_valid, B_fast_12_root_upper_right_valid, B_fast_12_MARK_before_fire_left_valid, B_fast_12_MARK_before_fire_right_valid, B_fast_12_fire_before_ERROR_left_valid, B_fast_12_fire_before_ERROR_right_valid, B_fast_12_ERROR_protected_left_valid, B_fast_12_ERROR_protected_right_valid, B_fast_12_arrival_valid, B_fast_12_b_after_valid, B_fast_12_gain_after_valid, B_fast_12_emission_valid, A_fast_12_aux_separation_left_valid, A_fast_12_aux_separation_right_valid, A_fast_12_gain_below_cap_left_valid, A_fast_12_gain_below_cap_right_valid, A_fast_12_input_in_SLOW_left_valid, A_fast_12_input_in_SLOW_right_valid, A_fast_12_input_before_return_left_valid, A_fast_12_input_before_return_right_valid, A_fast_12_whole_MARK_protected_left_valid, A_fast_12_whole_MARK_protected_right_valid, A_fast_12_b_below_cap_left_valid, A_fast_12_b_below_cap_right_valid, A_fast_12_whole_ERROR_protected_left_valid, A_fast_12_whole_ERROR_protected_right_valid, A_fast_12_no_firing_from_raw_tail_left_valid, A_fast_12_no_firing_from_raw_tail_right_valid, A_fast_12_reopen_valid, A_fast_12_arrival_valid, A_fast_12_b_after_valid, A_fast_12_gain_after_valid, C_fast_13_aux_separation_left_valid, C_fast_13_aux_separation_right_valid, C_fast_13_gain_below_cap_left_valid, C_fast_13_gain_below_cap_right_valid, C_fast_13_ready_at_input_left_valid, C_fast_13_ready_at_input_right_valid, C_fast_13_positive_derivative_coefficient_left_valid, C_fast_13_positive_derivative_coefficient_right_valid, C_fast_13_fixed_flow_increases_left_valid, C_fast_13_fixed_flow_increases_right_valid, C_fast_13_strong_crosses_by_one_left_valid, C_fast_13_strong_crosses_by_one_right_valid, C_fast_13_root_latency_valid, C_fast_13_root_lower_left_valid, C_fast_13_root_lower_right_valid, C_fast_13_root_upper_left_valid, C_fast_13_root_upper_right_valid, C_fast_13_MARK_before_fire_left_valid, C_fast_13_MARK_before_fire_right_valid, C_fast_13_fire_before_ERROR_left_valid, C_fast_13_fire_before_ERROR_right_valid, C_fast_13_ERROR_protected_left_valid, C_fast_13_ERROR_protected_right_valid, C_fast_13_arrival_valid, C_fast_13_b_after_valid, C_fast_13_gain_after_valid, C_fast_13_emission_valid, B_fast_13_aux_separation_left_valid, B_fast_13_aux_separation_right_valid, B_fast_13_gain_below_cap_left_valid, B_fast_13_gain_below_cap_right_valid, B_fast_13_ready_at_input_left_valid, B_fast_13_ready_at_input_right_valid, B_fast_13_positive_derivative_coefficient_left_valid, B_fast_13_positive_derivative_coefficient_right_valid, B_fast_13_fixed_flow_increases_left_valid, B_fast_13_fixed_flow_increases_right_valid, B_fast_13_strong_crosses_by_one_left_valid, B_fast_13_strong_crosses_by_one_right_valid, B_fast_13_root_latency_valid, B_fast_13_root_lower_left_valid, B_fast_13_root_lower_right_valid, B_fast_13_root_upper_left_valid, B_fast_13_root_upper_right_valid, B_fast_13_MARK_before_fire_left_valid, B_fast_13_MARK_before_fire_right_valid, B_fast_13_fire_before_ERROR_left_valid, B_fast_13_fire_before_ERROR_right_valid, B_fast_13_ERROR_protected_left_valid, B_fast_13_ERROR_protected_right_valid, B_fast_13_arrival_valid, B_fast_13_b_after_valid, B_fast_13_gain_after_valid, B_fast_13_emission_valid, A_fast_13_aux_separation_left_valid, A_fast_13_aux_separation_right_valid, A_fast_13_gain_below_cap_left_valid, A_fast_13_gain_below_cap_right_valid, A_fast_13_ready_at_input_left_valid, A_fast_13_ready_at_input_right_valid, A_fast_13_positive_derivative_coefficient_left_valid, A_fast_13_positive_derivative_coefficient_right_valid, A_fast_13_fixed_flow_increases_left_valid, A_fast_13_fixed_flow_increases_right_valid, A_fast_13_strong_crosses_by_one_left_valid, A_fast_13_strong_crosses_by_one_right_valid, A_fast_13_root_latency_valid, A_fast_13_root_lower_left_valid, A_fast_13_root_lower_right_valid, A_fast_13_root_upper_left_valid, A_fast_13_root_upper_right_valid, A_fast_13_MARK_before_fire_left_valid, A_fast_13_MARK_before_fire_right_valid, A_fast_13_fire_before_ERROR_left_valid, A_fast_13_fire_before_ERROR_right_valid, A_fast_13_ERROR_protected_left_valid, A_fast_13_ERROR_protected_right_valid, A_fast_13_arrival_valid, A_fast_13_b_after_valid, A_fast_13_gain_after_valid, A_fast_13_emission_valid, C_fast_14_aux_separation_left_valid⟩

end KernelR.Certificates.Cadence003
