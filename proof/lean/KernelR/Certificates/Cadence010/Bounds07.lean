import KernelR.Intervals

/-! Generated exact evidence checks, not hybrid-flow soundness. -/
namespace KernelR.Certificates.Cadence010
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def C_fast_7_root_lower_left : RationalBox := ⟨(9547619185730711569491381462074263589571 / 10000000000000000000000000000000000000000 : ℚ), (4999997613042884538580264980549028349439 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_root_lower_left_valid : C_fast_7_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_root_lower_left]

def C_fast_7_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_7_root_lower_right_valid : C_fast_7_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_root_lower_right]

def C_fast_7_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_7_root_upper_left_valid : C_fast_7_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_root_upper_left]

def C_fast_7_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (10448813149783160594250369329111635725273 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_root_upper_right_valid : C_fast_7_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_root_upper_right]

def C_fast_7_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_MARK_before_fire_left_valid : C_fast_7_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_MARK_before_fire_left]

def C_fast_7_MARK_before_fire_right : RationalBox := ⟨(15175 / 65536 : ℚ), (15175 / 65536 : ℚ)⟩
theorem C_fast_7_MARK_before_fire_right_valid : C_fast_7_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_MARK_before_fire_right]

def C_fast_7_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_7_fire_before_ERROR_left_valid : C_fast_7_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_fire_before_ERROR_left]

def C_fast_7_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_fire_before_ERROR_right_valid : C_fast_7_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_fire_before_ERROR_right]

def C_fast_7_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_ERROR_protected_left_valid : C_fast_7_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_7_ERROR_protected_left]

def C_fast_7_ERROR_protected_right : RationalBox := ⟨(18213900351626293381207431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36429069803990133445841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_ERROR_protected_right_valid : C_fast_7_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_7_ERROR_protected_right]

def C_fast_7_arrival : RationalBox := ⟨(668 / 1 : ℚ), (668 / 1 : ℚ)⟩
theorem C_fast_7_arrival_valid : C_fast_7_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_7_arrival]

def C_fast_7_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_7_b_after_valid : C_fast_7_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_7_b_after]

def C_fast_7_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_7_gain_after_valid : C_fast_7_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_7_gain_after]

def C_fast_7_emission : RationalBox := ⟨(43793223 / 65536 : ℚ), (700708209 / 1048576 : ℚ)⟩
theorem C_fast_7_emission_valid : C_fast_7_emission.Valid := by norm_num [RationalBox.Valid, C_fast_7_emission]

def B_fast_7_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_aux_separation_left_valid : B_fast_7_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_aux_separation_left]

def B_fast_7_aux_separation_right : RationalBox := ⟨(19604061 / 2621440 : ℚ), (80680141 / 10485760 : ℚ)⟩
theorem B_fast_7_aux_separation_right_valid : B_fast_7_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_aux_separation_right]

def B_fast_7_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_gain_below_cap_left_valid : B_fast_7_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_gain_below_cap_left]

def B_fast_7_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_fast_7_gain_below_cap_right_valid : B_fast_7_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_gain_below_cap_right]

def B_fast_7_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_7_ready_at_input_left_valid : B_fast_7_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_ready_at_input_left]

def B_fast_7_ready_at_input_right : RationalBox := ⟨(7343725668844271364254835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1188590211159467196294461337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_ready_at_input_right_valid : B_fast_7_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_ready_at_input_right]

def B_fast_7_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_7_positive_derivative_coefficient_left_valid : B_fast_7_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_positive_derivative_coefficient_left]

def B_fast_7_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_positive_derivative_coefficient_right_valid : B_fast_7_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_positive_derivative_coefficient_right]

def B_fast_7_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_7_fixed_flow_increases_left_valid : B_fast_7_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_fixed_flow_increases_left]

def B_fast_7_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_fixed_flow_increases_right_valid : B_fast_7_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_fixed_flow_increases_right]

def B_fast_7_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_7_strong_crosses_by_one_left_valid : B_fast_7_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_strong_crosses_by_one_left]

def B_fast_7_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_strong_crosses_by_one_right_valid : B_fast_7_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_strong_crosses_by_one_right]

def B_fast_7_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_fast_7_root_latency_valid : B_fast_7_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_7_root_latency]

def B_fast_7_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_root_lower_left_valid : B_fast_7_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_root_lower_left]

def B_fast_7_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_7_root_lower_right_valid : B_fast_7_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_root_lower_right]

def B_fast_7_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_7_root_upper_left_valid : B_fast_7_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_root_upper_left]

def B_fast_7_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_root_upper_right_valid : B_fast_7_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_root_upper_right]

def B_fast_7_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_MARK_before_fire_left_valid : B_fast_7_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_MARK_before_fire_left]

def B_fast_7_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem B_fast_7_MARK_before_fire_right_valid : B_fast_7_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_MARK_before_fire_right]

def B_fast_7_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_fast_7_fire_before_ERROR_left_valid : B_fast_7_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_fire_before_ERROR_left]

def B_fast_7_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_fire_before_ERROR_right_valid : B_fast_7_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_fire_before_ERROR_right]

def B_fast_7_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_ERROR_protected_left_valid : B_fast_7_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_7_ERROR_protected_left]

def B_fast_7_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_ERROR_protected_right_valid : B_fast_7_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_7_ERROR_protected_right]

def B_fast_7_arrival : RationalBox := ⟨(219064419 / 327680 : ℚ), (3505638197 / 5242880 : ℚ)⟩
theorem B_fast_7_arrival_valid : B_fast_7_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_7_arrival]

def B_fast_7_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem B_fast_7_b_after_valid : B_fast_7_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_7_b_after]

def B_fast_7_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_7_gain_after_valid : B_fast_7_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_7_gain_after]

def B_fast_7_emission : RationalBox := ⟨(7016910333 / 10485760 : ℚ), (3509062827 / 5242880 : ℚ)⟩
theorem B_fast_7_emission_valid : B_fast_7_emission.Valid := by norm_num [RationalBox.Valid, B_fast_7_emission]

def A_fast_7_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_aux_separation_left_valid : A_fast_7_aux_separation_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_aux_separation_left]

def A_fast_7_aux_separation_right : RationalBox := ⟨(19341917 / 2621440 : ℚ), (81728717 / 10485760 : ℚ)⟩
theorem A_fast_7_aux_separation_right_valid : A_fast_7_aux_separation_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_aux_separation_right]

def A_fast_7_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_gain_below_cap_left_valid : A_fast_7_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_gain_below_cap_left]

def A_fast_7_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem A_fast_7_gain_below_cap_right_valid : A_fast_7_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_gain_below_cap_right]

def A_fast_7_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_7_ready_at_input_left_valid : A_fast_7_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_ready_at_input_left]

def A_fast_7_ready_at_input_right : RationalBox := ⟨(6343725668844271364254835725984161817317 / 10000000000000000000000000000000000000000 : ℚ), (1313590211159467196294461337092306875659 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_ready_at_input_right_valid : A_fast_7_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_ready_at_input_right]

def A_fast_7_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_7_positive_derivative_coefficient_left_valid : A_fast_7_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_positive_derivative_coefficient_left]

def A_fast_7_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_positive_derivative_coefficient_right_valid : A_fast_7_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_positive_derivative_coefficient_right]

def A_fast_7_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem A_fast_7_fixed_flow_increases_left_valid : A_fast_7_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_fixed_flow_increases_left]

def A_fast_7_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_fixed_flow_increases_right_valid : A_fast_7_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_fixed_flow_increases_right]

def A_fast_7_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_7_strong_crosses_by_one_left_valid : A_fast_7_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_strong_crosses_by_one_left]

def A_fast_7_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_strong_crosses_by_one_right_valid : A_fast_7_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_strong_crosses_by_one_right]

def A_fast_7_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_7_root_latency_valid : A_fast_7_root_latency.Valid := by norm_num [RationalBox.Valid, A_fast_7_root_latency]

def A_fast_7_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_root_lower_left_valid : A_fast_7_root_lower_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_root_lower_left]

def A_fast_7_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_7_root_lower_right_valid : A_fast_7_root_lower_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_root_lower_right]

def A_fast_7_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem A_fast_7_root_upper_left_valid : A_fast_7_root_upper_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_root_upper_left]

def A_fast_7_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_root_upper_right_valid : A_fast_7_root_upper_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_root_upper_right]

def A_fast_7_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_MARK_before_fire_left_valid : A_fast_7_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_MARK_before_fire_left]

def A_fast_7_MARK_before_fire_right : RationalBox := ⟨(1369785 / 2097152 : ℚ), (1369785 / 2097152 : ℚ)⟩
theorem A_fast_7_MARK_before_fire_right_valid : A_fast_7_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_MARK_before_fire_right]

def A_fast_7_fire_before_ERROR_left : RationalBox := ⟨(342463 / 524288 : ℚ), (342463 / 524288 : ℚ)⟩
theorem A_fast_7_fire_before_ERROR_left_valid : A_fast_7_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_fire_before_ERROR_left]

def A_fast_7_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_fire_before_ERROR_right_valid : A_fast_7_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_fire_before_ERROR_right]

def A_fast_7_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_ERROR_protected_left_valid : A_fast_7_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, A_fast_7_ERROR_protected_left]

def A_fast_7_ERROR_protected_right : RationalBox := ⟨(8429232078307390713861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (67439512742105435666995164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_ERROR_protected_right_valid : A_fast_7_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, A_fast_7_ERROR_protected_right]

def A_fast_7_arrival : RationalBox := ⟨(7020056061 / 10485760 : ℚ), (3511159979 / 5242880 : ℚ)⟩
theorem A_fast_7_arrival_valid : A_fast_7_arrival.Valid := by norm_num [RationalBox.Valid, A_fast_7_arrival]

def A_fast_7_b_after : RationalBox := ⟨(17999 / 100000 : ℚ), (18001 / 100000 : ℚ)⟩
theorem A_fast_7_b_after_valid : A_fast_7_b_after.Valid := by norm_num [RationalBox.Valid, A_fast_7_b_after]

def A_fast_7_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem A_fast_7_gain_after_valid : A_fast_7_gain_after.Valid := by norm_num [RationalBox.Valid, A_fast_7_gain_after]

def A_fast_7_emission : RationalBox := ⟨(3513452493 / 5242880 : ℚ), (3514584609 / 5242880 : ℚ)⟩
theorem A_fast_7_emission_valid : A_fast_7_emission.Valid := by norm_num [RationalBox.Valid, A_fast_7_emission]

def C_fast_8_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_aux_separation_left_valid : C_fast_8_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_aux_separation_left]

def C_fast_8_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_8_aux_separation_right_valid : C_fast_8_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_aux_separation_right]

def C_fast_8_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_gain_below_cap_left_valid : C_fast_8_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_gain_below_cap_left]

def C_fast_8_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem C_fast_8_gain_below_cap_right_valid : C_fast_8_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_gain_below_cap_right]

def C_fast_8_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_8_ready_at_input_left_valid : C_fast_8_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_ready_at_input_left]

def C_fast_8_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1786099648373706618792568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_ready_at_input_right_valid : C_fast_8_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_ready_at_input_right]

def C_fast_8_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_8_positive_derivative_coefficient_left_valid : C_fast_8_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_positive_derivative_coefficient_left]

def C_fast_8_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_positive_derivative_coefficient_right_valid : C_fast_8_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_positive_derivative_coefficient_right]

def C_fast_8_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_8_fixed_flow_increases_left_valid : C_fast_8_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_fixed_flow_increases_left]

def C_fast_8_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_fixed_flow_increases_right_valid : C_fast_8_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_fixed_flow_increases_right]

def C_fast_8_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_8_strong_crosses_by_one_left_valid : C_fast_8_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_strong_crosses_by_one_left]

def C_fast_8_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_strong_crosses_by_one_right_valid : C_fast_8_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_strong_crosses_by_one_right]

def C_fast_8_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_8_root_latency_valid : C_fast_8_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_8_root_latency]

def C_fast_8_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_root_lower_left_valid : C_fast_8_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_root_lower_left]

def C_fast_8_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_8_root_lower_right_valid : C_fast_8_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_root_lower_right]

def C_fast_8_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_8_root_upper_left_valid : C_fast_8_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_root_upper_left]

def C_fast_8_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_root_upper_right_valid : C_fast_8_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_root_upper_right]

def C_fast_8_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_MARK_before_fire_left_valid : C_fast_8_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_MARK_before_fire_left]

def C_fast_8_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_8_MARK_before_fire_right_valid : C_fast_8_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_MARK_before_fire_right]

def C_fast_8_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_8_fire_before_ERROR_left_valid : C_fast_8_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_fire_before_ERROR_left]

def C_fast_8_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_fire_before_ERROR_right_valid : C_fast_8_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_fire_before_ERROR_right]

def C_fast_8_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_ERROR_protected_left_valid : C_fast_8_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_8_ERROR_protected_left]

def C_fast_8_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_ERROR_protected_right_valid : C_fast_8_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_8_ERROR_protected_right]

def C_fast_8_arrival : RationalBox := ⟨(672 / 1 : ℚ), (672 / 1 : ℚ)⟩
theorem C_fast_8_arrival_valid : C_fast_8_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_8_arrival]

def C_fast_8_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_8_b_after_valid : C_fast_8_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_8_b_after]

def C_fast_8_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_8_gain_after_valid : C_fast_8_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_8_gain_after]

def C_fast_8_emission : RationalBox := ⟨(352451253 / 524288 : ℚ), (704902513 / 1048576 : ℚ)⟩
theorem C_fast_8_emission_valid : C_fast_8_emission.Valid := by norm_num [RationalBox.Valid, C_fast_8_emission]

def B_fast_8_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_aux_separation_left_valid : B_fast_8_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_8_aux_separation_left]

def B_fast_8_aux_separation_right : RationalBox := ⟨(20447197 / 5242880 : ℚ), (21579013 / 5242880 : ℚ)⟩
theorem B_fast_8_aux_separation_right_valid : B_fast_8_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_8_aux_separation_right]

def B_fast_8_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_gain_below_cap_left_valid : B_fast_8_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_8_gain_below_cap_left]

def B_fast_8_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_fast_8_gain_below_cap_right_valid : B_fast_8_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_8_gain_below_cap_right]

def B_fast_8_input_in_SLOW_left : RationalBox := ⟨(7027396093 / 10485760 : ℚ), (3514305707 / 5242880 : ℚ)⟩
theorem B_fast_8_input_in_SLOW_left_valid : B_fast_8_input_in_SLOW_left.Valid := by norm_num [RationalBox.Valid, B_fast_8_input_in_SLOW_left]

def B_fast_8_input_in_SLOW_right : RationalBox := ⟨(1763042697 / 2621440 : ℚ), (3526609717 / 5242880 : ℚ)⟩
theorem B_fast_8_input_in_SLOW_right_valid : B_fast_8_input_in_SLOW_right.Valid := by norm_num [RationalBox.Valid, B_fast_8_input_in_SLOW_right]

def B_fast_8_input_before_return_left : RationalBox := ⟨(1763042697 / 2621440 : ℚ), (3526609717 / 5242880 : ℚ)⟩
theorem B_fast_8_input_before_return_left_valid : B_fast_8_input_before_return_left.Valid := by norm_num [RationalBox.Valid, B_fast_8_input_before_return_left]

def B_fast_8_input_before_return_right : RationalBox := ⟨(844093672233336687588861788662907693124341 / 1250000000000000000000000000000000000000 : ℚ), (6753914054406228970823245164274015838182683 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_input_before_return_right_valid : B_fast_8_input_before_return_right.Valid := by norm_num [RationalBox.Valid, B_fast_8_input_before_return_right]

def B_fast_8_whole_MARK_protected_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_whole_MARK_protected_left_valid : B_fast_8_whole_MARK_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_8_whole_MARK_protected_left]

def B_fast_8_whole_MARK_protected_right : RationalBox := ⟨(8488168043338175467269134096525269600733 / 5000000000000000000000000000000000000000 : ℚ), (16976336086676350934538268193050539201467 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_whole_MARK_protected_right_valid : B_fast_8_whole_MARK_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_8_whole_MARK_protected_right]

def B_fast_8_b_below_cap_left : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem B_fast_8_b_below_cap_left_valid : B_fast_8_b_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_8_b_below_cap_left]

def B_fast_8_b_below_cap_right : RationalBox := ⟨(11 / 10 : ℚ), (11 / 10 : ℚ)⟩
theorem B_fast_8_b_below_cap_right_valid : B_fast_8_b_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_8_b_below_cap_right]

def B_fast_8_whole_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_whole_ERROR_protected_left_valid : B_fast_8_whole_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, B_fast_8_whole_ERROR_protected_left]

def B_fast_8_whole_ERROR_protected_right : RationalBox := ⟨(8488168043338175467269134096525269600733 / 5000000000000000000000000000000000000000 : ℚ), (16976336086676350934538268193050539201467 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_whole_ERROR_protected_right_valid : B_fast_8_whole_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, B_fast_8_whole_ERROR_protected_right]

def B_fast_8_no_firing_from_raw_tail_left : RationalBox := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem B_fast_8_no_firing_from_raw_tail_left_valid : B_fast_8_no_firing_from_raw_tail_left.Valid := by norm_num [RationalBox.Valid, B_fast_8_no_firing_from_raw_tail_left]

def B_fast_8_no_firing_from_raw_tail_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_8_no_firing_from_raw_tail_right_valid : B_fast_8_no_firing_from_raw_tail_right.Valid := by norm_num [RationalBox.Valid, B_fast_8_no_firing_from_raw_tail_right]

def B_fast_8_reopen : RationalBox := ⟨(8488168043338175467269134096525269600733 / 5000000000000000000000000000000000000000 : ℚ), (18427785429069487226257260580233688850327 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_reopen_valid : B_fast_8_reopen.Valid := by norm_num [RationalBox.Valid, B_fast_8_reopen]

def B_fast_8_arrival : RationalBox := ⟨(1763042697 / 2621440 : ℚ), (3526609717 / 5242880 : ℚ)⟩
theorem B_fast_8_arrival_valid : B_fast_8_arrival.Valid := by norm_num [RationalBox.Valid, B_fast_8_arrival]

def B_fast_8_b_after : RationalBox := ⟨(27999 / 100000 : ℚ), (28001 / 100000 : ℚ)⟩
theorem B_fast_8_b_after_valid : B_fast_8_b_after.Valid := by norm_num [RationalBox.Valid, B_fast_8_b_after]

def B_fast_8_gain_after : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_8_gain_after_valid : B_fast_8_gain_after.Valid := by norm_num [RationalBox.Valid, B_fast_8_gain_after]

def C_fast_9_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_aux_separation_left_valid : C_fast_9_aux_separation_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_aux_separation_left]

def C_fast_9_aux_separation_right : RationalBox := ⟨(4 / 1 : ℚ), (4 / 1 : ℚ)⟩
theorem C_fast_9_aux_separation_right_valid : C_fast_9_aux_separation_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_aux_separation_right]

def C_fast_9_gain_below_cap_left : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_gain_below_cap_left_valid : C_fast_9_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_gain_below_cap_left]

def C_fast_9_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem C_fast_9_gain_below_cap_right_valid : C_fast_9_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_gain_below_cap_right]

def C_fast_9_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_9_ready_at_input_left_valid : C_fast_9_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_ready_at_input_left]

def C_fast_9_ready_at_input_right : RationalBox := ⟨(3412229253016702491658603864101395524879 / 10000000000000000000000000000000000000000 : ℚ), (1706782555478198806292568461777175976289 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_ready_at_input_right_valid : C_fast_9_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_ready_at_input_right]

def C_fast_9_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_9_positive_derivative_coefficient_left_valid : C_fast_9_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_positive_derivative_coefficient_left]

def C_fast_9_positive_derivative_coefficient_right : RationalBox := ⟨(6465634520918123437868110083426111659403 / 2500000000000000000000000000000000000000 : ℚ), (25863055339606709301638497706358408511659 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_positive_derivative_coefficient_right_valid : C_fast_9_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_positive_derivative_coefficient_right]

def C_fast_9_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem C_fast_9_fixed_flow_increases_left_valid : C_fast_9_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_fixed_flow_increases_left]

def C_fast_9_fixed_flow_increases_right : RationalBox := ⟨(8959237350023184447660006239728104215247 / 10000000000000000000000000000000000000000 : ℚ), (8961926414324982212865722928405075842499 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_fixed_flow_increases_right_valid : C_fast_9_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_fixed_flow_increases_right]

def C_fast_9_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_9_strong_crosses_by_one_left_valid : C_fast_9_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_strong_crosses_by_one_left]

def C_fast_9_strong_crosses_by_one_right : RationalBox := ⟨(19441575529629720790074058948369779353599 / 10000000000000000000000000000000000000000 : ℚ), (19441944364828653079306121755832463488841 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_strong_crosses_by_one_right_valid : C_fast_9_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_strong_crosses_by_one_right]

def C_fast_9_root_latency : RationalBox := ⟨(129717 / 524288 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_9_root_latency_valid : C_fast_9_root_latency.Valid := by norm_num [RationalBox.Valid, C_fast_9_root_latency]

def C_fast_9_root_lower_left : RationalBox := ⟨(9999814993629262840459125868533681991661 / 10000000000000000000000000000000000000000 : ℚ), (9999994991729110424255111464780060019401 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_root_lower_left_valid : C_fast_9_root_lower_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_root_lower_left]

def C_fast_9_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_9_root_lower_right_valid : C_fast_9_root_lower_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_root_lower_right]

def C_fast_9_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem C_fast_9_root_upper_left_valid : C_fast_9_root_upper_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_root_upper_left]

def C_fast_9_root_upper_right : RationalBox := ⟨(2500000532850055750314782251347578590011 / 2500000000000000000000000000000000000000 : ℚ), (1250022766655357929007755113674555163259 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_root_upper_right_valid : C_fast_9_root_upper_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_root_upper_right]

def C_fast_9_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_MARK_before_fire_left_valid : C_fast_9_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_MARK_before_fire_left]

def C_fast_9_MARK_before_fire_right : RationalBox := ⟨(129717 / 524288 : ℚ), (129717 / 524288 : ℚ)⟩
theorem C_fast_9_MARK_before_fire_right_valid : C_fast_9_MARK_before_fire_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_MARK_before_fire_right]

def C_fast_9_fire_before_ERROR_left : RationalBox := ⟨(259441 / 1048576 : ℚ), (259441 / 1048576 : ℚ)⟩
theorem C_fast_9_fire_before_ERROR_left_valid : C_fast_9_fire_before_ERROR_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_fire_before_ERROR_left]

def C_fast_9_fire_before_ERROR_right : RationalBox := ⟨(4984090909090909090909090909090909090909 / 5000000000000000000000000000000000000000 : ℚ), (9968181818181818181818181818181818181819 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_fire_before_ERROR_right_valid : C_fast_9_fire_before_ERROR_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_fire_before_ERROR_right]

def C_fast_9_ERROR_protected_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_ERROR_protected_left_valid : C_fast_9_ERROR_protected_left.Valid := by norm_num [RationalBox.Valid, C_fast_9_ERROR_protected_left]

def C_fast_9_ERROR_protected_right : RationalBox := ⟨(18293217444521801193707431538222824023711 / 5000000000000000000000000000000000000000 : ℚ), (36587703989781149070841396135898604475121 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_ERROR_protected_right_valid : C_fast_9_ERROR_protected_right.Valid := by norm_num [RationalBox.Valid, C_fast_9_ERROR_protected_right]

def C_fast_9_arrival : RationalBox := ⟨(676 / 1 : ℚ), (676 / 1 : ℚ)⟩
theorem C_fast_9_arrival_valid : C_fast_9_arrival.Valid := by norm_num [RationalBox.Valid, C_fast_9_arrival]

def C_fast_9_b_after : RationalBox := ⟨(37999 / 100000 : ℚ), (38001 / 100000 : ℚ)⟩
theorem C_fast_9_b_after_valid : C_fast_9_b_after.Valid := by norm_num [RationalBox.Valid, C_fast_9_b_after]

def C_fast_9_gain_after : RationalBox := ⟨(8267299612071714163546520260190771954567 / 2500000000000000000000000000000000000000 : ℚ), (33069859838869706173461596013866802027669 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem C_fast_9_gain_after_valid : C_fast_9_gain_after.Valid := by norm_num [RationalBox.Valid, C_fast_9_gain_after]

def C_fast_9_emission : RationalBox := ⟨(354548405 / 524288 : ℚ), (709096817 / 1048576 : ℚ)⟩
theorem C_fast_9_emission_valid : C_fast_9_emission.Valid := by norm_num [RationalBox.Valid, C_fast_9_emission]

def B_fast_9_aux_separation_left : RationalBox := ⟨(6983333333333333333333333333333333333333 / 5000000000000000000000000000000000000000 : ℚ), (13966666666666666666666666666666666666667 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_aux_separation_left_valid : B_fast_9_aux_separation_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_aux_separation_left]

def B_fast_9_aux_separation_right : RationalBox := ⟨(39 / 10 : ℚ), (41 / 10 : ℚ)⟩
theorem B_fast_9_aux_separation_right_valid : B_fast_9_aux_separation_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_aux_separation_right]

def B_fast_9_gain_below_cap_left : RationalBox := ⟨(9074380452361174978828165839328809819283 / 5000000000000000000000000000000000000000 : ℚ), (1134320242723138799004301248955570147203 / 625000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_gain_below_cap_left_valid : B_fast_9_gain_below_cap_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_gain_below_cap_left]

def B_fast_9_gain_below_cap_right : RationalBox := ⟨(18 / 5 : ℚ), (18 / 5 : ℚ)⟩
theorem B_fast_9_gain_below_cap_right_valid : B_fast_9_gain_below_cap_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_gain_below_cap_right]

def B_fast_9_ready_at_input_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_9_ready_at_input_left_valid : B_fast_9_ready_at_input_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_ready_at_input_left]

def B_fast_9_ready_at_input_right : RationalBox := ⟨(20572214570930512773742739419766311149673 / 10000000000000000000000000000000000000000 : ℚ), (12011831956661824532730865903474730399267 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_ready_at_input_right_valid : B_fast_9_ready_at_input_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_ready_at_input_right]

def B_fast_9_positive_derivative_coefficient_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_9_positive_derivative_coefficient_left_valid : B_fast_9_positive_derivative_coefficient_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_positive_derivative_coefficient_left]

def B_fast_9_positive_derivative_coefficient_right : RationalBox := ⟨(7096830919622184189335376056698418974567 / 5000000000000000000000000000000000000000 : ℚ), (2838789143063980911772855264151660206877 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_positive_derivative_coefficient_right_valid : B_fast_9_positive_derivative_coefficient_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_positive_derivative_coefficient_right]

def B_fast_9_fixed_flow_increases_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem B_fast_9_fixed_flow_increases_left_valid : B_fast_9_fixed_flow_increases_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_fixed_flow_increases_left]

def B_fast_9_fixed_flow_increases_right : RationalBox := ⟨(153654178381904175679511629728496919479 / 312500000000000000000000000000000000000 : ℚ), (4918409497999965294131471985264556758491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_fixed_flow_increases_right_valid : B_fast_9_fixed_flow_increases_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_fixed_flow_increases_right]

def B_fast_9_strong_crosses_by_one_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_9_strong_crosses_by_one_left_valid : B_fast_9_strong_crosses_by_one_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_strong_crosses_by_one_left]

def B_fast_9_strong_crosses_by_one_right : RationalBox := ⟨(11120951238567649100123122369075856696129 / 10000000000000000000000000000000000000000 : ℚ), (5560576829808312097743889676615023258197 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_strong_crosses_by_one_right_valid : B_fast_9_strong_crosses_by_one_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_strong_crosses_by_one_right]

def B_fast_9_root_latency : RationalBox := ⟨(1369785 / 2097152 : ℚ), (342463 / 524288 : ℚ)⟩
theorem B_fast_9_root_latency_valid : B_fast_9_root_latency.Valid := by norm_num [RationalBox.Valid, B_fast_9_root_latency]

def B_fast_9_root_lower_left : RationalBox := ⟨(2499954877295465167651011783235953034311 / 2500000000000000000000000000000000000000 : ℚ), (1999999901474404041894635192109074776207 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_root_lower_left_valid : B_fast_9_root_lower_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_root_lower_left]

def B_fast_9_root_lower_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_9_root_lower_right_valid : B_fast_9_root_lower_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_root_lower_right]

def B_fast_9_root_upper_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem B_fast_9_root_upper_left_valid : B_fast_9_root_upper_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_root_upper_left]

def B_fast_9_root_upper_right : RationalBox := ⟨(10000000751852143612946300731862253368619 / 10000000000000000000000000000000000000000 : ℚ), (1250022594208399100781248886875516962203 / 1250000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_root_upper_right_valid : B_fast_9_root_upper_right.Valid := by norm_num [RationalBox.Valid, B_fast_9_root_upper_right]

def B_fast_9_MARK_before_fire_left : RationalBox := ⟨(261111111111111111111111111111111111111 / 5000000000000000000000000000000000000000 : ℚ), (522222222222222222222222222222222222223 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem B_fast_9_MARK_before_fire_left_valid : B_fast_9_MARK_before_fire_left.Valid := by norm_num [RationalBox.Valid, B_fast_9_MARK_before_fire_left]

def Bounds07Valid : Prop :=
  C_fast_7_root_lower_left.Valid ∧
  C_fast_7_root_lower_right.Valid ∧
  C_fast_7_root_upper_left.Valid ∧
  C_fast_7_root_upper_right.Valid ∧
  C_fast_7_MARK_before_fire_left.Valid ∧
  C_fast_7_MARK_before_fire_right.Valid ∧
  C_fast_7_fire_before_ERROR_left.Valid ∧
  C_fast_7_fire_before_ERROR_right.Valid ∧
  C_fast_7_ERROR_protected_left.Valid ∧
  C_fast_7_ERROR_protected_right.Valid ∧
  C_fast_7_arrival.Valid ∧
  C_fast_7_b_after.Valid ∧
  C_fast_7_gain_after.Valid ∧
  C_fast_7_emission.Valid ∧
  B_fast_7_aux_separation_left.Valid ∧
  B_fast_7_aux_separation_right.Valid ∧
  B_fast_7_gain_below_cap_left.Valid ∧
  B_fast_7_gain_below_cap_right.Valid ∧
  B_fast_7_ready_at_input_left.Valid ∧
  B_fast_7_ready_at_input_right.Valid ∧
  B_fast_7_positive_derivative_coefficient_left.Valid ∧
  B_fast_7_positive_derivative_coefficient_right.Valid ∧
  B_fast_7_fixed_flow_increases_left.Valid ∧
  B_fast_7_fixed_flow_increases_right.Valid ∧
  B_fast_7_strong_crosses_by_one_left.Valid ∧
  B_fast_7_strong_crosses_by_one_right.Valid ∧
  B_fast_7_root_latency.Valid ∧
  B_fast_7_root_lower_left.Valid ∧
  B_fast_7_root_lower_right.Valid ∧
  B_fast_7_root_upper_left.Valid ∧
  B_fast_7_root_upper_right.Valid ∧
  B_fast_7_MARK_before_fire_left.Valid ∧
  B_fast_7_MARK_before_fire_right.Valid ∧
  B_fast_7_fire_before_ERROR_left.Valid ∧
  B_fast_7_fire_before_ERROR_right.Valid ∧
  B_fast_7_ERROR_protected_left.Valid ∧
  B_fast_7_ERROR_protected_right.Valid ∧
  B_fast_7_arrival.Valid ∧
  B_fast_7_b_after.Valid ∧
  B_fast_7_gain_after.Valid ∧
  B_fast_7_emission.Valid ∧
  A_fast_7_aux_separation_left.Valid ∧
  A_fast_7_aux_separation_right.Valid ∧
  A_fast_7_gain_below_cap_left.Valid ∧
  A_fast_7_gain_below_cap_right.Valid ∧
  A_fast_7_ready_at_input_left.Valid ∧
  A_fast_7_ready_at_input_right.Valid ∧
  A_fast_7_positive_derivative_coefficient_left.Valid ∧
  A_fast_7_positive_derivative_coefficient_right.Valid ∧
  A_fast_7_fixed_flow_increases_left.Valid ∧
  A_fast_7_fixed_flow_increases_right.Valid ∧
  A_fast_7_strong_crosses_by_one_left.Valid ∧
  A_fast_7_strong_crosses_by_one_right.Valid ∧
  A_fast_7_root_latency.Valid ∧
  A_fast_7_root_lower_left.Valid ∧
  A_fast_7_root_lower_right.Valid ∧
  A_fast_7_root_upper_left.Valid ∧
  A_fast_7_root_upper_right.Valid ∧
  A_fast_7_MARK_before_fire_left.Valid ∧
  A_fast_7_MARK_before_fire_right.Valid ∧
  A_fast_7_fire_before_ERROR_left.Valid ∧
  A_fast_7_fire_before_ERROR_right.Valid ∧
  A_fast_7_ERROR_protected_left.Valid ∧
  A_fast_7_ERROR_protected_right.Valid ∧
  A_fast_7_arrival.Valid ∧
  A_fast_7_b_after.Valid ∧
  A_fast_7_gain_after.Valid ∧
  A_fast_7_emission.Valid ∧
  C_fast_8_aux_separation_left.Valid ∧
  C_fast_8_aux_separation_right.Valid ∧
  C_fast_8_gain_below_cap_left.Valid ∧
  C_fast_8_gain_below_cap_right.Valid ∧
  C_fast_8_ready_at_input_left.Valid ∧
  C_fast_8_ready_at_input_right.Valid ∧
  C_fast_8_positive_derivative_coefficient_left.Valid ∧
  C_fast_8_positive_derivative_coefficient_right.Valid ∧
  C_fast_8_fixed_flow_increases_left.Valid ∧
  C_fast_8_fixed_flow_increases_right.Valid ∧
  C_fast_8_strong_crosses_by_one_left.Valid ∧
  C_fast_8_strong_crosses_by_one_right.Valid ∧
  C_fast_8_root_latency.Valid ∧
  C_fast_8_root_lower_left.Valid ∧
  C_fast_8_root_lower_right.Valid ∧
  C_fast_8_root_upper_left.Valid ∧
  C_fast_8_root_upper_right.Valid ∧
  C_fast_8_MARK_before_fire_left.Valid ∧
  C_fast_8_MARK_before_fire_right.Valid ∧
  C_fast_8_fire_before_ERROR_left.Valid ∧
  C_fast_8_fire_before_ERROR_right.Valid ∧
  C_fast_8_ERROR_protected_left.Valid ∧
  C_fast_8_ERROR_protected_right.Valid ∧
  C_fast_8_arrival.Valid ∧
  C_fast_8_b_after.Valid ∧
  C_fast_8_gain_after.Valid ∧
  C_fast_8_emission.Valid ∧
  B_fast_8_aux_separation_left.Valid ∧
  B_fast_8_aux_separation_right.Valid ∧
  B_fast_8_gain_below_cap_left.Valid ∧
  B_fast_8_gain_below_cap_right.Valid ∧
  B_fast_8_input_in_SLOW_left.Valid ∧
  B_fast_8_input_in_SLOW_right.Valid ∧
  B_fast_8_input_before_return_left.Valid ∧
  B_fast_8_input_before_return_right.Valid ∧
  B_fast_8_whole_MARK_protected_left.Valid ∧
  B_fast_8_whole_MARK_protected_right.Valid ∧
  B_fast_8_b_below_cap_left.Valid ∧
  B_fast_8_b_below_cap_right.Valid ∧
  B_fast_8_whole_ERROR_protected_left.Valid ∧
  B_fast_8_whole_ERROR_protected_right.Valid ∧
  B_fast_8_no_firing_from_raw_tail_left.Valid ∧
  B_fast_8_no_firing_from_raw_tail_right.Valid ∧
  B_fast_8_reopen.Valid ∧
  B_fast_8_arrival.Valid ∧
  B_fast_8_b_after.Valid ∧
  B_fast_8_gain_after.Valid ∧
  C_fast_9_aux_separation_left.Valid ∧
  C_fast_9_aux_separation_right.Valid ∧
  C_fast_9_gain_below_cap_left.Valid ∧
  C_fast_9_gain_below_cap_right.Valid ∧
  C_fast_9_ready_at_input_left.Valid ∧
  C_fast_9_ready_at_input_right.Valid ∧
  C_fast_9_positive_derivative_coefficient_left.Valid ∧
  C_fast_9_positive_derivative_coefficient_right.Valid ∧
  C_fast_9_fixed_flow_increases_left.Valid ∧
  C_fast_9_fixed_flow_increases_right.Valid ∧
  C_fast_9_strong_crosses_by_one_left.Valid ∧
  C_fast_9_strong_crosses_by_one_right.Valid ∧
  C_fast_9_root_latency.Valid ∧
  C_fast_9_root_lower_left.Valid ∧
  C_fast_9_root_lower_right.Valid ∧
  C_fast_9_root_upper_left.Valid ∧
  C_fast_9_root_upper_right.Valid ∧
  C_fast_9_MARK_before_fire_left.Valid ∧
  C_fast_9_MARK_before_fire_right.Valid ∧
  C_fast_9_fire_before_ERROR_left.Valid ∧
  C_fast_9_fire_before_ERROR_right.Valid ∧
  C_fast_9_ERROR_protected_left.Valid ∧
  C_fast_9_ERROR_protected_right.Valid ∧
  C_fast_9_arrival.Valid ∧
  C_fast_9_b_after.Valid ∧
  C_fast_9_gain_after.Valid ∧
  C_fast_9_emission.Valid ∧
  B_fast_9_aux_separation_left.Valid ∧
  B_fast_9_aux_separation_right.Valid ∧
  B_fast_9_gain_below_cap_left.Valid ∧
  B_fast_9_gain_below_cap_right.Valid ∧
  B_fast_9_ready_at_input_left.Valid ∧
  B_fast_9_ready_at_input_right.Valid ∧
  B_fast_9_positive_derivative_coefficient_left.Valid ∧
  B_fast_9_positive_derivative_coefficient_right.Valid ∧
  B_fast_9_fixed_flow_increases_left.Valid ∧
  B_fast_9_fixed_flow_increases_right.Valid ∧
  B_fast_9_strong_crosses_by_one_left.Valid ∧
  B_fast_9_strong_crosses_by_one_right.Valid ∧
  B_fast_9_root_latency.Valid ∧
  B_fast_9_root_lower_left.Valid ∧
  B_fast_9_root_lower_right.Valid ∧
  B_fast_9_root_upper_left.Valid ∧
  B_fast_9_root_upper_right.Valid ∧
  B_fast_9_MARK_before_fire_left.Valid
theorem Bounds07Valid_verified : Bounds07Valid := by
  exact ⟨C_fast_7_root_lower_left_valid, C_fast_7_root_lower_right_valid, C_fast_7_root_upper_left_valid, C_fast_7_root_upper_right_valid, C_fast_7_MARK_before_fire_left_valid, C_fast_7_MARK_before_fire_right_valid, C_fast_7_fire_before_ERROR_left_valid, C_fast_7_fire_before_ERROR_right_valid, C_fast_7_ERROR_protected_left_valid, C_fast_7_ERROR_protected_right_valid, C_fast_7_arrival_valid, C_fast_7_b_after_valid, C_fast_7_gain_after_valid, C_fast_7_emission_valid, B_fast_7_aux_separation_left_valid, B_fast_7_aux_separation_right_valid, B_fast_7_gain_below_cap_left_valid, B_fast_7_gain_below_cap_right_valid, B_fast_7_ready_at_input_left_valid, B_fast_7_ready_at_input_right_valid, B_fast_7_positive_derivative_coefficient_left_valid, B_fast_7_positive_derivative_coefficient_right_valid, B_fast_7_fixed_flow_increases_left_valid, B_fast_7_fixed_flow_increases_right_valid, B_fast_7_strong_crosses_by_one_left_valid, B_fast_7_strong_crosses_by_one_right_valid, B_fast_7_root_latency_valid, B_fast_7_root_lower_left_valid, B_fast_7_root_lower_right_valid, B_fast_7_root_upper_left_valid, B_fast_7_root_upper_right_valid, B_fast_7_MARK_before_fire_left_valid, B_fast_7_MARK_before_fire_right_valid, B_fast_7_fire_before_ERROR_left_valid, B_fast_7_fire_before_ERROR_right_valid, B_fast_7_ERROR_protected_left_valid, B_fast_7_ERROR_protected_right_valid, B_fast_7_arrival_valid, B_fast_7_b_after_valid, B_fast_7_gain_after_valid, B_fast_7_emission_valid, A_fast_7_aux_separation_left_valid, A_fast_7_aux_separation_right_valid, A_fast_7_gain_below_cap_left_valid, A_fast_7_gain_below_cap_right_valid, A_fast_7_ready_at_input_left_valid, A_fast_7_ready_at_input_right_valid, A_fast_7_positive_derivative_coefficient_left_valid, A_fast_7_positive_derivative_coefficient_right_valid, A_fast_7_fixed_flow_increases_left_valid, A_fast_7_fixed_flow_increases_right_valid, A_fast_7_strong_crosses_by_one_left_valid, A_fast_7_strong_crosses_by_one_right_valid, A_fast_7_root_latency_valid, A_fast_7_root_lower_left_valid, A_fast_7_root_lower_right_valid, A_fast_7_root_upper_left_valid, A_fast_7_root_upper_right_valid, A_fast_7_MARK_before_fire_left_valid, A_fast_7_MARK_before_fire_right_valid, A_fast_7_fire_before_ERROR_left_valid, A_fast_7_fire_before_ERROR_right_valid, A_fast_7_ERROR_protected_left_valid, A_fast_7_ERROR_protected_right_valid, A_fast_7_arrival_valid, A_fast_7_b_after_valid, A_fast_7_gain_after_valid, A_fast_7_emission_valid, C_fast_8_aux_separation_left_valid, C_fast_8_aux_separation_right_valid, C_fast_8_gain_below_cap_left_valid, C_fast_8_gain_below_cap_right_valid, C_fast_8_ready_at_input_left_valid, C_fast_8_ready_at_input_right_valid, C_fast_8_positive_derivative_coefficient_left_valid, C_fast_8_positive_derivative_coefficient_right_valid, C_fast_8_fixed_flow_increases_left_valid, C_fast_8_fixed_flow_increases_right_valid, C_fast_8_strong_crosses_by_one_left_valid, C_fast_8_strong_crosses_by_one_right_valid, C_fast_8_root_latency_valid, C_fast_8_root_lower_left_valid, C_fast_8_root_lower_right_valid, C_fast_8_root_upper_left_valid, C_fast_8_root_upper_right_valid, C_fast_8_MARK_before_fire_left_valid, C_fast_8_MARK_before_fire_right_valid, C_fast_8_fire_before_ERROR_left_valid, C_fast_8_fire_before_ERROR_right_valid, C_fast_8_ERROR_protected_left_valid, C_fast_8_ERROR_protected_right_valid, C_fast_8_arrival_valid, C_fast_8_b_after_valid, C_fast_8_gain_after_valid, C_fast_8_emission_valid, B_fast_8_aux_separation_left_valid, B_fast_8_aux_separation_right_valid, B_fast_8_gain_below_cap_left_valid, B_fast_8_gain_below_cap_right_valid, B_fast_8_input_in_SLOW_left_valid, B_fast_8_input_in_SLOW_right_valid, B_fast_8_input_before_return_left_valid, B_fast_8_input_before_return_right_valid, B_fast_8_whole_MARK_protected_left_valid, B_fast_8_whole_MARK_protected_right_valid, B_fast_8_b_below_cap_left_valid, B_fast_8_b_below_cap_right_valid, B_fast_8_whole_ERROR_protected_left_valid, B_fast_8_whole_ERROR_protected_right_valid, B_fast_8_no_firing_from_raw_tail_left_valid, B_fast_8_no_firing_from_raw_tail_right_valid, B_fast_8_reopen_valid, B_fast_8_arrival_valid, B_fast_8_b_after_valid, B_fast_8_gain_after_valid, C_fast_9_aux_separation_left_valid, C_fast_9_aux_separation_right_valid, C_fast_9_gain_below_cap_left_valid, C_fast_9_gain_below_cap_right_valid, C_fast_9_ready_at_input_left_valid, C_fast_9_ready_at_input_right_valid, C_fast_9_positive_derivative_coefficient_left_valid, C_fast_9_positive_derivative_coefficient_right_valid, C_fast_9_fixed_flow_increases_left_valid, C_fast_9_fixed_flow_increases_right_valid, C_fast_9_strong_crosses_by_one_left_valid, C_fast_9_strong_crosses_by_one_right_valid, C_fast_9_root_latency_valid, C_fast_9_root_lower_left_valid, C_fast_9_root_lower_right_valid, C_fast_9_root_upper_left_valid, C_fast_9_root_upper_right_valid, C_fast_9_MARK_before_fire_left_valid, C_fast_9_MARK_before_fire_right_valid, C_fast_9_fire_before_ERROR_left_valid, C_fast_9_fire_before_ERROR_right_valid, C_fast_9_ERROR_protected_left_valid, C_fast_9_ERROR_protected_right_valid, C_fast_9_arrival_valid, C_fast_9_b_after_valid, C_fast_9_gain_after_valid, C_fast_9_emission_valid, B_fast_9_aux_separation_left_valid, B_fast_9_aux_separation_right_valid, B_fast_9_gain_below_cap_left_valid, B_fast_9_gain_below_cap_right_valid, B_fast_9_ready_at_input_left_valid, B_fast_9_ready_at_input_right_valid, B_fast_9_positive_derivative_coefficient_left_valid, B_fast_9_positive_derivative_coefficient_right_valid, B_fast_9_fixed_flow_increases_left_valid, B_fast_9_fixed_flow_increases_right_valid, B_fast_9_strong_crosses_by_one_left_valid, B_fast_9_strong_crosses_by_one_right_valid, B_fast_9_root_latency_valid, B_fast_9_root_lower_left_valid, B_fast_9_root_lower_right_valid, B_fast_9_root_upper_left_valid, B_fast_9_root_upper_right_valid, B_fast_9_MARK_before_fire_left_valid⟩

end KernelR.Certificates.Cadence010
