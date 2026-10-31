import KernelR.Intervals

/-! Generated rational endpoint checks; analytic enclosure membership is separate. -/
namespace KernelR.Robust.Evidence.Latency4
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def nu : RationalBox := ⟨(3 / 2000 : ℚ), (3 / 2000 : ℚ)⟩
theorem nu_valid : nu.Valid := by norm_num [RationalBox.Valid, nu]

def alpha : RationalBox := ⟨(1 / 20 : ℚ), (1 / 20 : ℚ)⟩
theorem alpha_valid : alpha.Valid := by norm_num [RationalBox.Valid, alpha]

def latency_radius : RationalBox := ⟨(693 / 6250 : ℚ), (693 / 6250 : ℚ)⟩
theorem latency_radius_valid : latency_radius.Valid := by norm_num [RationalBox.Valid, latency_radius]

def reference_lower : RationalBox := ⟨(64377 / 100000 : ℚ), (64377 / 100000 : ℚ)⟩
theorem reference_lower_valid : reference_lower.Valid := by norm_num [RationalBox.Valid, reference_lower]

def reference_upper : RationalBox := ⟨(331461 / 500000 : ℚ), (331461 / 500000 : ℚ)⟩
theorem reference_upper_valid : reference_upper.Valid := by norm_num [RationalBox.Valid, reference_upper]

def learned_gain : RationalBox := ⟨(1127485627319296029966383952190571845289 / 625000000000000000000000000000000000000 : ℚ), (9129387717125600929115173948984023290419 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem learned_gain_valid : learned_gain.Valid := by norm_num [RationalBox.Valid, learned_gain]

def reference_before_all_roots_left : RationalBox := ⟨(1249999817289293047528539275345475661741 / 1250000000000000000000000000000000000000 : ℚ), (9999998538314344380228314202763805293929 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem reference_before_all_roots_left_valid : reference_before_all_roots_left.Valid := by norm_num [RationalBox.Valid, reference_before_all_roots_left]

def reference_before_all_roots_right : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem reference_before_all_roots_right_valid : reference_before_all_roots_right.Valid := by norm_num [RationalBox.Valid, reference_before_all_roots_right]

def reference_after_all_roots_left : RationalBox := ⟨(1 / 1 : ℚ), (1 / 1 : ℚ)⟩
theorem reference_after_all_roots_left_valid : reference_after_all_roots_left.Valid := by norm_num [RationalBox.Valid, reference_after_all_roots_left]

def reference_after_all_roots_right : RationalBox := ⟨(10000000047316352224069488941334262795337 / 10000000000000000000000000000000000000000 : ℚ), (5000000023658176112034744470667131397669 / 5000000000000000000000000000000000000000 : ℚ)⟩
theorem reference_after_all_roots_right_valid : reference_after_all_roots_right.Valid := by norm_num [RationalBox.Valid, reference_after_all_roots_right]

def response_strictly_concave_through_raw_window_left : RationalBox := ⟨(6065306597126334236037995349911804534419 / 2500000000000000000000000000000000000000 : ℚ), (24261226388505336944151981399647218137677 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem response_strictly_concave_through_raw_window_left_valid : response_strictly_concave_through_raw_window_left.Valid := by norm_num [RationalBox.Valid, response_strictly_concave_through_raw_window_left]

def response_strictly_concave_through_raw_window_right : RationalBox := ⟨(9609060278364028493342050526533299434611 / 1250000000000000000000000000000000000000 : ℚ), (76872482226912227946736404212266395476889 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem response_strictly_concave_through_raw_window_right_valid : response_strictly_concave_through_raw_window_right.Valid := by norm_num [RationalBox.Valid, response_strictly_concave_through_raw_window_right]

def positive_early_time_left : RationalBox := ⟨(693 / 6250 : ℚ), (693 / 6250 : ℚ)⟩
theorem positive_early_time_left_valid : positive_early_time_left.Valid := by norm_num [RationalBox.Valid, positive_early_time_left]

def positive_early_time_right : RationalBox := ⟨(64377 / 100000 : ℚ), (64377 / 100000 : ℚ)⟩
theorem positive_early_time_right_valid : positive_early_time_right.Valid := by norm_num [RationalBox.Valid, positive_early_time_right]

def late_time_before_local_ERROR_gate_left : RationalBox := ⟨(386901 / 500000 : ℚ), (386901 / 500000 : ℚ)⟩
theorem late_time_before_local_ERROR_gate_left_valid : late_time_before_local_ERROR_gate_left.Valid := by norm_num [RationalBox.Valid, late_time_before_local_ERROR_gate_left]

def late_time_before_local_ERROR_gate_right : RationalBox := ⟨(9 / 10 : ℚ), (9 / 10 : ℚ)⟩
theorem late_time_before_local_ERROR_gate_right_valid : late_time_before_local_ERROR_gate_right.Valid := by norm_num [RationalBox.Valid, late_time_before_local_ERROR_gate_right]

def positive_minimum_slope_left : RationalBox := ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩
theorem positive_minimum_slope_left_valid : positive_minimum_slope_left.Valid := by norm_num [RationalBox.Valid, positive_minimum_slope_left]

def positive_minimum_slope_right : RationalBox := ⟨(949787744302141902246967258465993412203 / 2500000000000000000000000000000000000000 : ℚ), (3799150977208567608987869033863973648813 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem positive_minimum_slope_right_valid : positive_minimum_slope_right.Valid := by norm_num [RationalBox.Valid, positive_minimum_slope_right]

def late_reference_separation_dominates_perturbation_left : RationalBox := ⟨(2045364220191684043750981543227881457 / 40000000000000000000000000000000000000 : ℚ), (511341055047921010937745385806970364251 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem late_reference_separation_dominates_perturbation_left_valid : late_reference_separation_dominates_perturbation_left.Valid := by norm_num [RationalBox.Valid, late_reference_separation_dominates_perturbation_left]

def late_reference_separation_dominates_perturbation_right : RationalBox := ⟨(51135187631268880127737293301559050549 / 1000000000000000000000000000000000000000 : ℚ), (511351876312688801277372933015590505491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem late_reference_separation_dominates_perturbation_right_valid : late_reference_separation_dominates_perturbation_right.Valid := by norm_num [RationalBox.Valid, late_reference_separation_dominates_perturbation_right]

def early_reference_separation_dominates_perturbation_left : RationalBox := ⟨(22462548172874567974922593245323637467 / 500000000000000000000000000000000000000 : ℚ), (449250963457491359498451864906472749341 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem early_reference_separation_dominates_perturbation_left_valid : early_reference_separation_dominates_perturbation_left.Valid := by norm_num [RationalBox.Valid, early_reference_separation_dominates_perturbation_left]

def early_reference_separation_dominates_perturbation_right : RationalBox := ⟨(89444391048142217737382584950118001723 / 1250000000000000000000000000000000000000 : ℚ), (143111025677027548379812135920188802757 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem early_reference_separation_dominates_perturbation_right_valid : early_reference_separation_dominates_perturbation_right.Valid := by norm_num [RationalBox.Valid, early_reference_separation_dominates_perturbation_right]

def minimum_slope : RationalBox := ⟨(949787744302141902246967258465993412203 / 2500000000000000000000000000000000000000 : ℚ), (3799150977208567608987869033863973648813 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem minimum_slope_valid : minimum_slope.Valid := by norm_num [RationalBox.Valid, minimum_slope]

def late_separation : RationalBox := ⟨(51135187631268880127737293301559050549 / 1000000000000000000000000000000000000000 : ℚ), (511351876312688801277372933015590505491 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem late_separation_valid : late_separation.Valid := by norm_num [RationalBox.Valid, late_separation]

def early_separation : RationalBox := ⟨(89444391048142217737382584950118001723 / 1250000000000000000000000000000000000000 : ℚ), (143111025677027548379812135920188802757 / 2000000000000000000000000000000000000000 : ℚ)⟩
theorem early_separation_valid : early_separation.Valid := by norm_num [RationalBox.Valid, early_separation]

def late_perturbation : RationalBox := ⟨(2045364220191684043750981543227881457 / 40000000000000000000000000000000000000 : ℚ), (511341055047921010937745385806970364251 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem late_perturbation_valid : late_perturbation.Valid := by norm_num [RationalBox.Valid, late_perturbation]

def early_perturbation : RationalBox := ⟨(22462548172874567974922593245323637467 / 500000000000000000000000000000000000000 : ℚ), (449250963457491359498451864906472749341 / 10000000000000000000000000000000000000000 : ℚ)⟩
theorem early_perturbation_valid : early_perturbation.Valid := by norm_num [RationalBox.Valid, early_perturbation]

theorem reference_before_all_roots_verified : RationalBox.StrictBefore reference_before_all_roots_left reference_before_all_roots_right := by
  norm_num [RationalBox.StrictBefore, reference_before_all_roots_left, reference_before_all_roots_right]

theorem reference_after_all_roots_verified : RationalBox.StrictBefore reference_after_all_roots_left reference_after_all_roots_right := by
  norm_num [RationalBox.StrictBefore, reference_after_all_roots_left, reference_after_all_roots_right]

theorem response_strictly_concave_through_raw_window_verified : RationalBox.StrictBefore response_strictly_concave_through_raw_window_left response_strictly_concave_through_raw_window_right := by
  norm_num [RationalBox.StrictBefore, response_strictly_concave_through_raw_window_left, response_strictly_concave_through_raw_window_right]

theorem positive_early_time_verified : RationalBox.StrictBefore positive_early_time_left positive_early_time_right := by
  norm_num [RationalBox.StrictBefore, positive_early_time_left, positive_early_time_right]

theorem late_time_before_local_ERROR_gate_verified : RationalBox.StrictBefore late_time_before_local_ERROR_gate_left late_time_before_local_ERROR_gate_right := by
  norm_num [RationalBox.StrictBefore, late_time_before_local_ERROR_gate_left, late_time_before_local_ERROR_gate_right]

theorem positive_minimum_slope_verified : RationalBox.StrictBefore positive_minimum_slope_left positive_minimum_slope_right := by
  norm_num [RationalBox.StrictBefore, positive_minimum_slope_left, positive_minimum_slope_right]

theorem late_reference_separation_dominates_perturbation_verified : RationalBox.StrictBefore late_reference_separation_dominates_perturbation_left late_reference_separation_dominates_perturbation_right := by
  norm_num [RationalBox.StrictBefore, late_reference_separation_dominates_perturbation_left, late_reference_separation_dominates_perturbation_right]

theorem early_reference_separation_dominates_perturbation_verified : RationalBox.StrictBefore early_reference_separation_dominates_perturbation_left early_reference_separation_dominates_perturbation_right := by
  norm_num [RationalBox.StrictBefore, early_reference_separation_dominates_perturbation_left, early_reference_separation_dominates_perturbation_right]

def Obligations : Prop :=
  RationalBox.StrictBefore reference_before_all_roots_left reference_before_all_roots_right ∧
  RationalBox.StrictBefore reference_after_all_roots_left reference_after_all_roots_right ∧
  RationalBox.StrictBefore response_strictly_concave_through_raw_window_left response_strictly_concave_through_raw_window_right ∧
  RationalBox.StrictBefore positive_early_time_left positive_early_time_right ∧
  RationalBox.StrictBefore late_time_before_local_ERROR_gate_left late_time_before_local_ERROR_gate_right ∧
  RationalBox.StrictBefore positive_minimum_slope_left positive_minimum_slope_right ∧
  RationalBox.StrictBefore late_reference_separation_dominates_perturbation_left late_reference_separation_dominates_perturbation_right ∧
  RationalBox.StrictBefore early_reference_separation_dominates_perturbation_left early_reference_separation_dominates_perturbation_right
theorem obligations_verified : Obligations := by
  exact ⟨reference_before_all_roots_verified, reference_after_all_roots_verified, response_strictly_concave_through_raw_window_verified, positive_early_time_verified, late_time_before_local_ERROR_gate_verified, positive_minimum_slope_verified, late_reference_separation_dominates_perturbation_verified, early_reference_separation_dominates_perturbation_verified⟩

end KernelR.Robust.Evidence.Latency4
