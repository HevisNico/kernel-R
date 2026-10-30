import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence003
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def B_fast_9_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_fast_9_MARK_before_fire_right_valid : B_fast_9_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_MARK_before_fire_right]

def B_fast_9_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_fast_9_fire_before_ERROR_left_valid : B_fast_9_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_fire_before_ERROR_left]

def B_fast_9_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_fire_before_ERROR_right_valid : B_fast_9_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_fire_before_ERROR_right]

def B_fast_9_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_ERROR_protected_left_valid : B_fast_9_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_ERROR_protected_left]

def B_fast_9_ERROR_protected_right : RationalBox := ⟨(24627572083279480728086648008428468116319 / 5000000000000000000000000000000000000000 : ℚ), (49257481642918764755267901059609667182761 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_ERROR_protected_right_valid : B_fast_9_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_ERROR_protected_right]

def B_fast_9_arrival : RationalBox := ⟨(1773528457 / 2621440 : ℚ), (3547581237 / 5242880 : ℚ)⟩
theorem B_fast_9_arrival_valid : B_fast_9_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_9_arrival]

def B_fast_9_b_after : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem B_fast_9_b_after_valid : B_fast_9_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_9_b_after]

def B_fast_9_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_gain_after_valid : B_fast_9_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_9_gain_after]

def B_fast_9_emission : RationalBox := ⟨(7100962753 / 10485760 : ℚ), (3551005867 / 5242880 : ℚ)⟩
theorem B_fast_9_emission_valid : B_fast_9_emission.Valid := by norm_num [RationalBox.Valid, B_fast_9_emission]

def A_fast_9_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_aux_separation_left_valid : A_fast_9_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_aux_separation_left]

def A_fast_9_aux_separation_right : RationalBox := ⟨(40894429 / 5242880 : ℚ), (172296619 / 20971520 : ℚ)⟩
theorem A_fast_9_aux_separation_right_valid : A_fast_9_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_aux_separation_right]

def A_fast_9_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_gain_below_cap_left_valid : A_fast_9_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_gain_below_cap_left]

def A_fast_9_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_9_gain_below_cap_right_valid : A_fast_9_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_gain_below_cap_right]

def A_fast_9_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_9_ready_at_input_left_valid : A_fast_9_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_ready_at_input_left]

def A_fast_9_ready_at_input_right : RationalBox := ⟨(10560101019796419801754835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1840446693188428377935086337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_ready_at_input_right_valid : A_fast_9_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_ready_at_input_right]

def A_fast_9_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_9_positive_derivative_coefficient_left_valid : A_fast_9_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_positive_derivative_coefficient_left]

def A_fast_9_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_positive_derivative_coefficient_right_valid : A_fast_9_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_positive_derivative_coefficient_right]

def A_fast_9_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_9_fixed_flow_increases_left_valid : A_fast_9_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_fixed_flow_increases_left]

def A_fast_9_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_fixed_flow_increases_right_valid : A_fast_9_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_fixed_flow_increases_right]

def A_fast_9_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_9_strong_crosses_by_one_left_valid : A_fast_9_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_strong_crosses_by_one_left]

def A_fast_9_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_strong_crosses_by_one_right_valid : A_fast_9_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_strong_crosses_by_one_right]

def A_fast_9_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_9_root_latency_valid : A_fast_9_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_9_root_latency]

def A_fast_9_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_root_lower_left_valid : A_fast_9_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_root_lower_left]

def A_fast_9_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_9_root_lower_right_valid : A_fast_9_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_root_lower_right]

def A_fast_9_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_9_root_upper_left_valid : A_fast_9_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_root_upper_left]

def A_fast_9_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_root_upper_right_valid : A_fast_9_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_root_upper_right]

def A_fast_9_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_MARK_before_fire_left_valid : A_fast_9_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_MARK_before_fire_left]

def A_fast_9_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem A_fast_9_MARK_before_fire_right_valid : A_fast_9_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_MARK_before_fire_right]

def A_fast_9_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_9_fire_before_ERROR_left_valid : A_fast_9_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_fire_before_ERROR_left]

def A_fast_9_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_fire_before_ERROR_right_valid : A_fast_9_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_fire_before_ERROR_right]

def A_fast_9_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_ERROR_protected_left_valid : A_fast_9_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_9_ERROR_protected_left]

def A_fast_9_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_ERROR_protected_right_valid : A_fast_9_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_9_ERROR_protected_right]

def A_fast_9_arrival : RationalBox := ⟨(7104108481 / 10485760 : ℚ), (3553103019 / 5242880 : ℚ)⟩
theorem A_fast_9_arrival_valid : A_fast_9_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_9_arrival]

def A_fast_9_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem A_fast_9_b_after_valid : A_fast_9_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_9_b_after]

def A_fast_9_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_9_gain_after_valid : A_fast_9_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_9_gain_after]

def A_fast_9_emission : RationalBox := ⟨(3555478703 / 5242880 : ℚ), (3556527649 / 5242880 : ℚ)⟩
theorem A_fast_9_emission_valid : A_fast_9_emission.Valid := by norm_num [RationalBox.Valid, A_fast_9_emission]

def C_fast_10_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_aux_separation_left_valid : C_fast_10_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_aux_separation_left]

def C_fast_10_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_10_aux_separation_right_valid : C_fast_10_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_aux_separation_right]

def C_fast_10_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_gain_below_cap_left_valid : C_fast_10_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_gain_below_cap_left]

def C_fast_10_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_10_gain_below_cap_right_valid : C_fast_10_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_gain_below_cap_right]

def C_fast_10_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_10_ready_at_input_left_valid : C_fast_10_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_ready_at_input_left]

def C_fast_10_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_ready_at_input_right_valid : C_fast_10_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_ready_at_input_right]

def C_fast_10_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_10_positive_derivative_coefficient_left_valid : C_fast_10_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_positive_derivative_coefficient_left]

def C_fast_10_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_positive_derivative_coefficient_right_valid : C_fast_10_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_positive_derivative_coefficient_right]

def C_fast_10_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_10_fixed_flow_increases_left_valid : C_fast_10_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_fixed_flow_increases_left]

def C_fast_10_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_fixed_flow_increases_right_valid : C_fast_10_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_fixed_flow_increases_right]

def C_fast_10_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_10_strong_crosses_by_one_left_valid : C_fast_10_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_strong_crosses_by_one_left]

def C_fast_10_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_strong_crosses_by_one_right_valid : C_fast_10_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_strong_crosses_by_one_right]

def C_fast_10_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_10_root_latency_valid : C_fast_10_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_10_root_latency]

def C_fast_10_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_root_lower_left_valid : C_fast_10_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_root_lower_left]

def C_fast_10_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_10_root_lower_right_valid : C_fast_10_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_root_lower_right]

def C_fast_10_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_10_root_upper_left_valid : C_fast_10_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_root_upper_left]

def C_fast_10_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_root_upper_right_valid : C_fast_10_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_root_upper_right]

def C_fast_10_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_MARK_before_fire_left_valid : C_fast_10_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_MARK_before_fire_left]

def C_fast_10_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_10_MARK_before_fire_right_valid : C_fast_10_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_MARK_before_fire_right]

def C_fast_10_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_10_fire_before_ERROR_left_valid : C_fast_10_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_fire_before_ERROR_left]

def C_fast_10_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_fire_before_ERROR_right_valid : C_fast_10_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_fire_before_ERROR_right]

def C_fast_10_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_ERROR_protected_left_valid : C_fast_10_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_10_ERROR_protected_left]

def C_fast_10_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_ERROR_protected_right_valid : C_fast_10_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_10_ERROR_protected_right]

def C_fast_10_arrival : RationalBox := ⟨(680 / 1 : ℚ), (680 / 1 : ℚ)⟩
theorem C_fast_10_arrival_valid : C_fast_10_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_10_arrival]

def C_fast_10_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_10_b_after_valid : C_fast_10_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_10_b_after]

def C_fast_10_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_10_gain_after_valid : C_fast_10_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_10_gain_after]

def C_fast_10_emission : RationalBox := ⟨(356645557 / 524288 : ℚ), (713291121 / 1048576 : ℚ)⟩
theorem C_fast_10_emission_valid : C_fast_10_emission.Valid := by norm_num [RationalBox.Valid, C_fast_10_emission]

def B_fast_10_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_aux_separation_left_valid : B_fast_10_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_10_aux_separation_left]

def B_fast_10_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_10_aux_separation_right_valid : B_fast_10_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_10_aux_separation_right]

def B_fast_10_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_gain_below_cap_left_valid : B_fast_10_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_10_gain_below_cap_left]

def B_fast_10_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_fast_10_gain_below_cap_right_valid : B_fast_10_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_10_gain_below_cap_right]

def B_fast_10_input_in_SLOW_left : RationalBox := ⟨(7111448513 / 10485760 : ℚ), (3556248747 / 5242880 : ℚ)⟩
theorem B_fast_10_input_in_SLOW_left_valid : B_fast_10_input_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, B_fast_10_input_in_SLOW_left]

def B_fast_10_input_in_SLOW_right : RationalBox := ⟨(1784014217 / 2621440 : ℚ), (3568552757 / 5242880 : ℚ)⟩
theorem B_fast_10_input_in_SLOW_right_valid : B_fast_10_input_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, B_fast_10_input_in_SLOW_right]

def B_fast_10_input_before_return_left : RationalBox := ⟨(1784014217 / 2621440 : ℚ), (3568552757 / 5242880 : ℚ)⟩
theorem B_fast_10_input_before_return_left_valid : B_fast_10_input_before_return_left.Valid := by norm_num [RationalBox.Valid, B_fast_10_input_before_return_left]

def B_fast_10_input_before_return_right : RationalBox := ⟨(3407364649796292176040586648008428468116319 / 5000000000000000000000000000000000000000 : ℚ), (6815732023307042299911517901059609667182761 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_input_before_return_right_valid : B_fast_10_input_before_return_right.Valid := by norm_num [RationalBox.Valid, B_fast_10_input_before_return_right]

def B_fast_10_whole_MARK_protected_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_whole_MARK_protected_left_valid : B_fast_10_whole_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_10_whole_MARK_protected_left]

def B_fast_10_whole_MARK_protected_right : RationalBox := ⟨(6147529069293003381038628847791823316073 / 10000000000000000000000000000000000000000 : ℚ), (3073764534646501690519314423895911658037 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_whole_MARK_protected_right_valid : B_fast_10_whole_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_10_whole_MARK_protected_right]

def B_fast_10_b_below_cap_left : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_10_b_below_cap_left_valid : B_fast_10_b_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_10_b_below_cap_left]

def B_fast_10_b_below_cap_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem B_fast_10_b_below_cap_right_valid : B_fast_10_b_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_10_b_below_cap_right]

def B_fast_10_return_before_ERROR_left : RationalBox := ⟨(1915668248595239124822052605016712171297 / 2500000000000000000000000000000000000000 : ℚ), (7662672994380956499288210420066848685189 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_return_before_ERROR_left_valid : B_fast_10_return_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_10_return_before_ERROR_left]

def B_fast_10_return_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_return_before_ERROR_right_valid : B_fast_10_return_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_10_return_before_ERROR_right]

def B_fast_10_no_firing_from_raw_tail_left : RationalBox := ⟨(7776587379230416422797200864384100443 / 20000000000000000000000000000000000000 : ℚ), (3888293689615208211398600432192050221501 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_no_firing_from_raw_tail_left_valid : B_fast_10_no_firing_from_raw_tail_left.Valid := by norm_num [RationalBox.Valid, B_fast_10_no_firing_from_raw_tail_left]

def B_fast_10_no_firing_from_raw_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_10_no_firing_from_raw_tail_right_valid : B_fast_10_no_firing_from_raw_tail_right.Valid := by norm_num [RationalBox.Valid, B_fast_10_no_firing_from_raw_tail_right]

def B_fast_10_reopen : RationalBox := ⟨(6147529069293003381038628847791823316073 / 10000000000000000000000000000000000000000 : ℚ), (7662672994380956499288210420066848685189 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_reopen_valid : B_fast_10_reopen.Valid := by norm_num [RationalBox.Valid, B_fast_10_reopen]

def B_fast_10_arrival : RationalBox := ⟨(1784014217 / 2621440 : ℚ), (3568552757 / 5242880 : ℚ)⟩
theorem B_fast_10_arrival_valid : B_fast_10_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_10_arrival]

def B_fast_10_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_10_b_after_valid : B_fast_10_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_10_b_after]

def B_fast_10_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_10_gain_after_valid : B_fast_10_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_10_gain_after]

def C_fast_11_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_aux_separation_left_valid : C_fast_11_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_aux_separation_left]

def C_fast_11_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_11_aux_separation_right_valid : C_fast_11_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_aux_separation_right]

def C_fast_11_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_gain_below_cap_left_valid : C_fast_11_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_gain_below_cap_left]

def C_fast_11_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem C_fast_11_gain_below_cap_right_valid : C_fast_11_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_gain_below_cap_right]

def C_fast_11_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_11_ready_at_input_left_valid : C_fast_11_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_ready_at_input_left]

def C_fast_11_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_ready_at_input_right_valid : C_fast_11_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_ready_at_input_right]

def C_fast_11_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_11_positive_derivative_coefficient_left_valid : C_fast_11_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_positive_derivative_coefficient_left]

def C_fast_11_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_positive_derivative_coefficient_right_valid : C_fast_11_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_positive_derivative_coefficient_right]

def C_fast_11_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_11_fixed_flow_increases_left_valid : C_fast_11_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_fixed_flow_increases_left]

def C_fast_11_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_fixed_flow_increases_right_valid : C_fast_11_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_fixed_flow_increases_right]

def C_fast_11_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_11_strong_crosses_by_one_left_valid : C_fast_11_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_strong_crosses_by_one_left]

def C_fast_11_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_strong_crosses_by_one_right_valid : C_fast_11_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_strong_crosses_by_one_right]

def C_fast_11_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_11_root_latency_valid : C_fast_11_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_11_root_latency]

def C_fast_11_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_root_lower_left_valid : C_fast_11_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_root_lower_left]

def C_fast_11_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_11_root_lower_right_valid : C_fast_11_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_root_lower_right]

def C_fast_11_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_11_root_upper_left_valid : C_fast_11_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_root_upper_left]

def C_fast_11_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_root_upper_right_valid : C_fast_11_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_root_upper_right]

def C_fast_11_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_MARK_before_fire_left_valid : C_fast_11_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_MARK_before_fire_left]

def C_fast_11_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_11_MARK_before_fire_right_valid : C_fast_11_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_MARK_before_fire_right]

def C_fast_11_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_11_fire_before_ERROR_left_valid : C_fast_11_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_fire_before_ERROR_left]

def C_fast_11_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_fire_before_ERROR_right_valid : C_fast_11_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_fire_before_ERROR_right]

def C_fast_11_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_ERROR_protected_left_valid : C_fast_11_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_11_ERROR_protected_left]

def C_fast_11_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_ERROR_protected_right_valid : C_fast_11_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_11_ERROR_protected_right]

def C_fast_11_arrival : RationalBox := ⟨(684 / 1 : ℚ), (684 / 1 : ℚ)⟩
theorem C_fast_11_arrival_valid : C_fast_11_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_11_arrival]

def C_fast_11_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_11_b_after_valid : C_fast_11_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_11_b_after]

def C_fast_11_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_11_gain_after_valid : C_fast_11_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_11_gain_after]

def C_fast_11_emission : RationalBox := ⟨(358742709 / 524288 : ℚ), (717485425 / 1048576 : ℚ)⟩
theorem C_fast_11_emission_valid : C_fast_11_emission.Valid := by norm_num [RationalBox.Valid, C_fast_11_emission]

def B_fast_11_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_aux_separation_left_valid : B_fast_11_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_aux_separation_left]

def B_fast_11_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_11_aux_separation_right_valid : B_fast_11_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_aux_separation_right]

def B_fast_11_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_gain_below_cap_left_valid : B_fast_11_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_gain_below_cap_left]

def B_fast_11_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem B_fast_11_gain_below_cap_right_valid : B_fast_11_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_gain_below_cap_right]

def B_fast_11_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_11_ready_at_input_left_valid : B_fast_11_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_ready_at_input_left]

def B_fast_11_ready_at_input_right : RationalBox := ⟨(31337327005619043500711789579933151314811 / 10000000000000000000000000000000000000000 : ℚ), (34852470930706996618961371152208176683927 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_ready_at_input_right_valid : B_fast_11_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_ready_at_input_right]

def B_fast_11_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_11_positive_derivative_coefficient_left_valid : B_fast_11_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_positive_derivative_coefficient_left]

def B_fast_11_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (13100904640521488943066812485323139529643 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_positive_derivative_coefficient_right_valid : B_fast_11_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_positive_derivative_coefficient_right]

def B_fast_11_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_11_fixed_flow_increases_left_valid : B_fast_11_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_fixed_flow_increases_left]

def B_fast_11_fixed_flow_increases_right : RationalBox := ⟨(162747574874096107185213259840228875871 / 200000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_fixed_flow_increases_right_valid : B_fast_11_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_fixed_flow_increases_right]

def B_fast_11_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_11_strong_crosses_by_one_left_valid : B_fast_11_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_strong_crosses_by_one_left]

def B_fast_11_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19852873667987842623505793379690793699689 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_strong_crosses_by_one_right_valid : B_fast_11_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_strong_crosses_by_one_right]

def B_fast_11_root_latency : RationalBox := ⟨(474603 / 2097152 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_11_root_latency_valid : B_fast_11_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_11_root_latency]

def B_fast_11_root_lower_left : RationalBox := ⟨(4697403659522546146543045759369802049919 / 5000000000000000000000000000000000000000 : ℚ), (199999970886033084216764546507934953327 / 200000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_root_lower_left_valid : B_fast_11_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_root_lower_left]

def B_fast_11_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_11_root_lower_right_valid : B_fast_11_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_root_lower_right]

def B_fast_11_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_11_root_upper_left_valid : B_fast_11_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_root_upper_left]

def B_fast_11_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (10598851864232799908592663353092056587353 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_root_upper_right_valid : B_fast_11_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_root_upper_right]

def B_fast_11_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_MARK_before_fire_left_valid : B_fast_11_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_MARK_before_fire_left]

def B_fast_11_MARK_before_fire_right : RationalBox := ⟨(474603 / 2097152 : ℚ), (474603 / 2097152 : ℚ)⟩
theorem B_fast_11_MARK_before_fire_right_valid : B_fast_11_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_MARK_before_fire_right]

def B_fast_11_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem B_fast_11_fire_before_ERROR_left_valid : B_fast_11_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_fire_before_ERROR_left]

def B_fast_11_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_fire_before_ERROR_right_valid : B_fast_11_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_fire_before_ERROR_right]

def B_fast_11_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_ERROR_protected_left_valid : B_fast_11_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_11_ERROR_protected_left]

def B_fast_11_ERROR_protected_right : RationalBox := ⟨(18187681460482494553082431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36376632021702535789591396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_ERROR_protected_right_valid : B_fast_11_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_11_ERROR_protected_right]

def B_fast_11_arrival : RationalBox := ⟨(1794499977 / 2621440 : ℚ), (3589524277 / 5242880 : ℚ)⟩
theorem B_fast_11_arrival_valid : B_fast_11_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_11_arrival]

def B_fast_11_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem B_fast_11_b_after_valid : B_fast_11_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_11_b_after]

def B_fast_11_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_11_gain_after_valid : B_fast_11_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_11_gain_after]

def B_fast_11_emission : RationalBox := ⟨(7180372923 / 10485760 : ℚ), (1795410741 / 2621440 : ℚ)⟩
theorem B_fast_11_emission_valid : B_fast_11_emission.Valid := by norm_num [RationalBox.Valid, B_fast_11_emission]

def A_fast_11_aux_separation_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_aux_separation_left_valid : A_fast_11_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_aux_separation_left]

def A_fast_11_aux_separation_right : RationalBox := ⟨(77312683 / 10485760 : ℚ), (81728717 / 10485760 : ℚ)⟩
theorem A_fast_11_aux_separation_right_valid : A_fast_11_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_aux_separation_right]

def A_fast_11_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_gain_below_cap_left_valid : A_fast_11_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_gain_below_cap_left]

def A_fast_11_gain_below_cap_right : RationalBox := ⟨(997 / 250 : ℚ), (997 / 250 : ℚ)⟩
theorem A_fast_11_gain_below_cap_right_valid : A_fast_11_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_gain_below_cap_right]

def A_fast_11_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_11_ready_at_input_left_valid : A_fast_11_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_ready_at_input_left]

def A_fast_11_ready_at_input_right : RationalBox := ⟨(6291287886556673708004835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1313590211159467196294461337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_ready_at_input_right_valid : A_fast_11_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_ready_at_input_right]

def A_fast_11_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_11_positive_derivative_coefficient_left_valid : A_fast_11_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_positive_derivative_coefficient_left]

def A_fast_11_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_positive_derivative_coefficient_right_valid : A_fast_11_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_positive_derivative_coefficient_right]

def A_fast_11_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_11_fixed_flow_increases_left_valid : A_fast_11_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_fixed_flow_increases_left]

def A_fast_11_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_fixed_flow_increases_right_valid : A_fast_11_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_fixed_flow_increases_right]

def A_fast_11_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_11_strong_crosses_by_one_left_valid : A_fast_11_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_strong_crosses_by_one_left]

def A_fast_11_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_strong_crosses_by_one_right_valid : A_fast_11_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_strong_crosses_by_one_right]

def A_fast_11_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_11_root_latency_valid : A_fast_11_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_11_root_latency]

def A_fast_11_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_root_lower_left_valid : A_fast_11_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_root_lower_left]

def A_fast_11_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_11_root_lower_right_valid : A_fast_11_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_root_lower_right]

def A_fast_11_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_11_root_upper_left_valid : A_fast_11_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_root_upper_left]

def A_fast_11_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_root_upper_right_valid : A_fast_11_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_root_upper_right]

def A_fast_11_MARK_before_fire_left : RationalBox := ⟨(62575225677031093279839518555667001003 / 1250000000000000000000000000000000000000 : ℚ), (20024072216649949849548645937813440321 / 400000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_MARK_before_fire_left_valid : A_fast_11_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_MARK_before_fire_left]

def A_fast_11_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem A_fast_11_MARK_before_fire_right_valid : A_fast_11_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_MARK_before_fire_right]

def A_fast_11_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_11_fire_before_ERROR_left_valid : A_fast_11_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_fire_before_ERROR_left]

def A_fast_11_fire_before_ERROR_right : RationalBox := ⟨(10917696909272183449651046859421734795613 / 10000000000000000000000000000000000000000 : ℚ), (5458848454636091724825523429710867397807 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_fire_before_ERROR_right_valid : A_fast_11_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_fire_before_ERROR_right]

def A_fast_11_ERROR_protected_left : RationalBox := ⟨(315925275827482447342026078234704112337 / 250000000000000000000000000000000000000 : ℚ), (12637011033099297893681043129388164493481 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_ERROR_protected_left_valid : A_fast_11_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_11_ERROR_protected_left]

def A_fast_11_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_11_ERROR_protected_right_valid : A_fast_11_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_11_ERROR_protected_right]

def Bounds08Valid : Prop :=
  B_fast_9_MARK_before_fire_right.Valid ∧
  B_fast_9_fire_before_ERROR_left.Valid ∧
  B_fast_9_fire_before_ERROR_right.Valid ∧
  B_fast_9_ERROR_protected_left.Valid ∧
  B_fast_9_ERROR_protected_right.Valid ∧
  B_fast_9_arrival.Valid ∧
  B_fast_9_b_after.Valid ∧
  B_fast_9_gain_after.Valid ∧
  B_fast_9_emission.Valid ∧
  A_fast_9_aux_separation_left.Valid ∧
  A_fast_9_aux_separation_right.Valid ∧
  A_fast_9_gain_below_cap_left.Valid ∧
  A_fast_9_gain_below_cap_right.Valid ∧
  A_fast_9_ready_at_input_left.Valid ∧
  A_fast_9_ready_at_input_right.Valid ∧
  A_fast_9_positive_derivative_coefficient_left.Valid ∧
  A_fast_9_positive_derivative_coefficient_right.Valid ∧
  A_fast_9_fixed_flow_increases_left.Valid ∧
  A_fast_9_fixed_flow_increases_right.Valid ∧
  A_fast_9_strong_crosses_by_one_left.Valid ∧
  A_fast_9_strong_crosses_by_one_right.Valid ∧
  A_fast_9_root_latency.Valid ∧
  A_fast_9_root_lower_left.Valid ∧
  A_fast_9_root_lower_right.Valid ∧
  A_fast_9_root_upper_left.Valid ∧
  A_fast_9_root_upper_right.Valid ∧
  A_fast_9_MARK_before_fire_left.Valid ∧
  A_fast_9_MARK_before_fire_right.Valid ∧
  A_fast_9_fire_before_ERROR_left.Valid ∧
  A_fast_9_fire_before_ERROR_right.Valid ∧
  A_fast_9_ERROR_protected_left.Valid ∧
  A_fast_9_ERROR_protected_right.Valid ∧
  A_fast_9_arrival.Valid ∧
  A_fast_9_b_after.Valid ∧
  A_fast_9_gain_after.Valid ∧
  A_fast_9_emission.Valid ∧
  C_fast_10_aux_separation_left.Valid ∧
  C_fast_10_aux_separation_right.Valid ∧
  C_fast_10_gain_below_cap_left.Valid ∧
  C_fast_10_gain_below_cap_right.Valid ∧
  C_fast_10_ready_at_input_left.Valid ∧
  C_fast_10_ready_at_input_right.Valid ∧
  C_fast_10_positive_derivative_coefficient_left.Valid ∧
  C_fast_10_positive_derivative_coefficient_right.Valid ∧
  C_fast_10_fixed_flow_increases_left.Valid ∧
  C_fast_10_fixed_flow_increases_right.Valid ∧
  C_fast_10_strong_crosses_by_one_left.Valid ∧
  C_fast_10_strong_crosses_by_one_right.Valid ∧
  C_fast_10_root_latency.Valid ∧
  C_fast_10_root_lower_left.Valid ∧
  C_fast_10_root_lower_right.Valid ∧
  C_fast_10_root_upper_left.Valid ∧
  C_fast_10_root_upper_right.Valid ∧
  C_fast_10_MARK_before_fire_left.Valid ∧
  C_fast_10_MARK_before_fire_right.Valid ∧
  C_fast_10_fire_before_ERROR_left.Valid ∧
  C_fast_10_fire_before_ERROR_right.Valid ∧
  C_fast_10_ERROR_protected_left.Valid ∧
  C_fast_10_ERROR_protected_right.Valid ∧
  C_fast_10_arrival.Valid ∧
  C_fast_10_b_after.Valid ∧
  C_fast_10_gain_after.Valid ∧
  C_fast_10_emission.Valid ∧
  B_fast_10_aux_separation_left.Valid ∧
  B_fast_10_aux_separation_right.Valid ∧
  B_fast_10_gain_below_cap_left.Valid ∧
  B_fast_10_gain_below_cap_right.Valid ∧
  B_fast_10_input_in_SLOW_left.Valid ∧
  B_fast_10_input_in_SLOW_right.Valid ∧
  B_fast_10_input_before_return_left.Valid ∧
  B_fast_10_input_before_return_right.Valid ∧
  B_fast_10_whole_MARK_protected_left.Valid ∧
  B_fast_10_whole_MARK_protected_right.Valid ∧
  B_fast_10_b_below_cap_left.Valid ∧
  B_fast_10_b_below_cap_right.Valid ∧
  B_fast_10_return_before_ERROR_left.Valid ∧
  B_fast_10_return_before_ERROR_right.Valid ∧
  B_fast_10_no_firing_from_raw_tail_left.Valid ∧
  B_fast_10_no_firing_from_raw_tail_right.Valid ∧
  B_fast_10_reopen.Valid ∧
  B_fast_10_arrival.Valid ∧
  B_fast_10_b_after.Valid ∧
  B_fast_10_gain_after.Valid ∧
  C_fast_11_aux_separation_left.Valid ∧
  C_fast_11_aux_separation_right.Valid ∧
  C_fast_11_gain_below_cap_left.Valid ∧
  C_fast_11_gain_below_cap_right.Valid ∧
  C_fast_11_ready_at_input_left.Valid ∧
  C_fast_11_ready_at_input_right.Valid ∧
  C_fast_11_positive_derivative_coefficient_left.Valid ∧
  C_fast_11_positive_derivative_coefficient_right.Valid ∧
  C_fast_11_fixed_flow_increases_left.Valid ∧
  C_fast_11_fixed_flow_increases_right.Valid ∧
  C_fast_11_strong_crosses_by_one_left.Valid ∧
  C_fast_11_strong_crosses_by_one_right.Valid ∧
  C_fast_11_root_latency.Valid ∧
  C_fast_11_root_lower_left.Valid ∧
  C_fast_11_root_lower_right.Valid ∧
  C_fast_11_root_upper_left.Valid ∧
  C_fast_11_root_upper_right.Valid ∧
  C_fast_11_MARK_before_fire_left.Valid ∧
  C_fast_11_MARK_before_fire_right.Valid ∧
  C_fast_11_fire_before_ERROR_left.Valid ∧
  C_fast_11_fire_before_ERROR_right.Valid ∧
  C_fast_11_ERROR_protected_left.Valid ∧
  C_fast_11_ERROR_protected_right.Valid ∧
  C_fast_11_arrival.Valid ∧
  C_fast_11_b_after.Valid ∧
  C_fast_11_gain_after.Valid ∧
  C_fast_11_emission.Valid ∧
  B_fast_11_aux_separation_left.Valid ∧
  B_fast_11_aux_separation_right.Valid ∧
  B_fast_11_gain_below_cap_left.Valid ∧
  B_fast_11_gain_below_cap_right.Valid ∧
  B_fast_11_ready_at_input_left.Valid ∧
  B_fast_11_ready_at_input_right.Valid ∧
  B_fast_11_positive_derivative_coefficient_left.Valid ∧
  B_fast_11_positive_derivative_coefficient_right.Valid ∧
  B_fast_11_fixed_flow_increases_left.Valid ∧
  B_fast_11_fixed_flow_increases_right.Valid ∧
  B_fast_11_strong_crosses_by_one_left.Valid ∧
  B_fast_11_strong_crosses_by_one_right.Valid ∧
  B_fast_11_root_latency.Valid ∧
  B_fast_11_root_lower_left.Valid ∧
  B_fast_11_root_lower_right.Valid ∧
  B_fast_11_root_upper_left.Valid ∧
  B_fast_11_root_upper_right.Valid ∧
  B_fast_11_MARK_before_fire_left.Valid ∧
  B_fast_11_MARK_before_fire_right.Valid ∧
  B_fast_11_fire_before_ERROR_left.Valid ∧
  B_fast_11_fire_before_ERROR_right.Valid ∧
  B_fast_11_ERROR_protected_left.Valid ∧
  B_fast_11_ERROR_protected_right.Valid ∧
  B_fast_11_arrival.Valid ∧
  B_fast_11_b_after.Valid ∧
  B_fast_11_gain_after.Valid ∧
  B_fast_11_emission.Valid ∧
  A_fast_11_aux_separation_left.Valid ∧
  A_fast_11_aux_separation_right.Valid ∧
  A_fast_11_gain_below_cap_left.Valid ∧
  A_fast_11_gain_below_cap_right.Valid ∧
  A_fast_11_ready_at_input_left.Valid ∧
  A_fast_11_ready_at_input_right.Valid ∧
  A_fast_11_positive_derivative_coefficient_left.Valid ∧
  A_fast_11_positive_derivative_coefficient_right.Valid ∧
  A_fast_11_fixed_flow_increases_left.Valid ∧
  A_fast_11_fixed_flow_increases_right.Valid ∧
  A_fast_11_strong_crosses_by_one_left.Valid ∧
  A_fast_11_strong_crosses_by_one_right.Valid ∧
  A_fast_11_root_latency.Valid ∧
  A_fast_11_root_lower_left.Valid ∧
  A_fast_11_root_lower_right.Valid ∧
  A_fast_11_root_upper_left.Valid ∧
  A_fast_11_root_upper_right.Valid ∧
  A_fast_11_MARK_before_fire_left.Valid ∧
  A_fast_11_MARK_before_fire_right.Valid ∧
  A_fast_11_fire_before_ERROR_left.Valid ∧
  A_fast_11_fire_before_ERROR_right.Valid ∧
  A_fast_11_ERROR_protected_left.Valid ∧
  A_fast_11_ERROR_protected_right.Valid
theorem Bounds08Valid_verified : Bounds08Valid := by
  exact ⟨B_fast_9_MARK_before_fire_right_valid, B_fast_9_fire_before_ERROR_left_valid, B_fast_9_fire_before_ERROR_right_valid, B_fast_9_ERROR_protected_left_valid, B_fast_9_ERROR_protected_right_valid, B_fast_9_arrival_valid, B_fast_9_b_after_valid, B_fast_9_gain_after_valid, B_fast_9_emission_valid, A_fast_9_aux_separation_left_valid, A_fast_9_aux_separation_right_valid, A_fast_9_gain_below_cap_left_valid, A_fast_9_gain_below_cap_right_valid, A_fast_9_ready_at_input_left_valid, A_fast_9_ready_at_input_right_valid, A_fast_9_positive_derivative_coefficient_left_valid, A_fast_9_positive_derivative_coefficient_right_valid, A_fast_9_fixed_flow_increases_left_valid, A_fast_9_fixed_flow_increases_right_valid, A_fast_9_strong_crosses_by_one_left_valid, A_fast_9_strong_crosses_by_one_right_valid, A_fast_9_root_latency_valid, A_fast_9_root_lower_left_valid, A_fast_9_root_lower_right_valid, A_fast_9_root_upper_left_valid, A_fast_9_root_upper_right_valid, A_fast_9_MARK_before_fire_left_valid, A_fast_9_MARK_before_fire_right_valid, A_fast_9_fire_before_ERROR_left_valid, A_fast_9_fire_before_ERROR_right_valid, A_fast_9_ERROR_protected_left_valid, A_fast_9_ERROR_protected_right_valid, A_fast_9_arrival_valid, A_fast_9_b_after_valid, A_fast_9_gain_after_valid, A_fast_9_emission_valid, C_fast_10_aux_separation_left_valid, C_fast_10_aux_separation_right_valid, C_fast_10_gain_below_cap_left_valid, C_fast_10_gain_below_cap_right_valid, C_fast_10_ready_at_input_left_valid, C_fast_10_ready_at_input_right_valid, C_fast_10_positive_derivative_coefficient_left_valid, C_fast_10_positive_derivative_coefficient_right_valid, C_fast_10_fixed_flow_increases_left_valid, C_fast_10_fixed_flow_increases_right_valid, C_fast_10_strong_crosses_by_one_left_valid, C_fast_10_strong_crosses_by_one_right_valid, C_fast_10_root_latency_valid, C_fast_10_root_lower_left_valid, C_fast_10_root_lower_right_valid, C_fast_10_root_upper_left_valid, C_fast_10_root_upper_right_valid, C_fast_10_MARK_before_fire_left_valid, C_fast_10_MARK_before_fire_right_valid, C_fast_10_fire_before_ERROR_left_valid, C_fast_10_fire_before_ERROR_right_valid, C_fast_10_ERROR_protected_left_valid, C_fast_10_ERROR_protected_right_valid, C_fast_10_arrival_valid, C_fast_10_b_after_valid, C_fast_10_gain_after_valid, C_fast_10_emission_valid, B_fast_10_aux_separation_left_valid, B_fast_10_aux_separation_right_valid, B_fast_10_gain_below_cap_left_valid, B_fast_10_gain_below_cap_right_valid, B_fast_10_input_in_SLOW_left_valid, B_fast_10_input_in_SLOW_right_valid, B_fast_10_input_before_return_left_valid, B_fast_10_input_before_return_right_valid, B_fast_10_whole_MARK_protected_left_valid, B_fast_10_whole_MARK_protected_right_valid, B_fast_10_b_below_cap_left_valid, B_fast_10_b_below_cap_right_valid, B_fast_10_return_before_ERROR_left_valid, B_fast_10_return_before_ERROR_right_valid, B_fast_10_no_firing_from_raw_tail_left_valid, B_fast_10_no_firing_from_raw_tail_right_valid, B_fast_10_reopen_valid, B_fast_10_arrival_valid, B_fast_10_b_after_valid, B_fast_10_gain_after_valid, C_fast_11_aux_separation_left_valid, C_fast_11_aux_separation_right_valid, C_fast_11_gain_below_cap_left_valid, C_fast_11_gain_below_cap_right_valid, C_fast_11_ready_at_input_left_valid, C_fast_11_ready_at_input_right_valid, C_fast_11_positive_derivative_coefficient_left_valid, C_fast_11_positive_derivative_coefficient_right_valid, C_fast_11_fixed_flow_increases_left_valid, C_fast_11_fixed_flow_increases_right_valid, C_fast_11_strong_crosses_by_one_left_valid, C_fast_11_strong_crosses_by_one_right_valid, C_fast_11_root_latency_valid, C_fast_11_root_lower_left_valid, C_fast_11_root_lower_right_valid, C_fast_11_root_upper_left_valid, C_fast_11_root_upper_right_valid, C_fast_11_MARK_before_fire_left_valid, C_fast_11_MARK_before_fire_right_valid, C_fast_11_fire_before_ERROR_left_valid, C_fast_11_fire_before_ERROR_right_valid, C_fast_11_ERROR_protected_left_valid, C_fast_11_ERROR_protected_right_valid, C_fast_11_arrival_valid, C_fast_11_b_after_valid, C_fast_11_gain_after_valid, C_fast_11_emission_valid, B_fast_11_aux_separation_left_valid, B_fast_11_aux_separation_right_valid, B_fast_11_gain_below_cap_left_valid, B_fast_11_gain_below_cap_right_valid, B_fast_11_ready_at_input_left_valid, B_fast_11_ready_at_input_right_valid, B_fast_11_positive_derivative_coefficient_left_valid, B_fast_11_positive_derivative_coefficient_right_valid, B_fast_11_fixed_flow_increases_left_valid, B_fast_11_fixed_flow_increases_right_valid, B_fast_11_strong_crosses_by_one_left_valid, B_fast_11_strong_crosses_by_one_right_valid, B_fast_11_root_latency_valid, B_fast_11_root_lower_left_valid, B_fast_11_root_lower_right_valid, B_fast_11_root_upper_left_valid, B_fast_11_root_upper_right_valid, B_fast_11_MARK_before_fire_left_valid, B_fast_11_MARK_before_fire_right_valid, B_fast_11_fire_before_ERROR_left_valid, B_fast_11_fire_before_ERROR_right_valid, B_fast_11_ERROR_protected_left_valid, B_fast_11_ERROR_protected_right_valid, B_fast_11_arrival_valid, B_fast_11_b_after_valid, B_fast_11_gain_after_valid, B_fast_11_emission_valid, A_fast_11_aux_separation_left_valid, A_fast_11_aux_separation_right_valid, A_fast_11_gain_below_cap_left_valid, A_fast_11_gain_below_cap_right_valid, A_fast_11_ready_at_input_left_valid, A_fast_11_ready_at_input_right_valid, A_fast_11_positive_derivative_coefficient_left_valid, A_fast_11_positive_derivative_coefficient_right_valid, A_fast_11_fixed_flow_increases_left_valid, A_fast_11_fixed_flow_increases_right_valid, A_fast_11_strong_crosses_by_one_left_valid, A_fast_11_strong_crosses_by_one_right_valid, A_fast_11_root_latency_valid, A_fast_11_root_lower_left_valid, A_fast_11_root_lower_right_valid, A_fast_11_root_upper_left_valid, A_fast_11_root_upper_right_valid, A_fast_11_MARK_before_fire_left_valid, A_fast_11_MARK_before_fire_right_valid, A_fast_11_fire_before_ERROR_left_valid, A_fast_11_fire_before_ERROR_right_valid, A_fast_11_ERROR_protected_left_valid, A_fast_11_ERROR_protected_right_valid⟩

end KernelR.Certificates.Cadence003
