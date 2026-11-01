import KernelR.HybridCellInputs
import KernelR.HybridBirthInput
/-! First actual input after quiet READY relaxation, retaining other-cell traffic. -/
namespace KernelR.Hybrid

structure RestingCellInput {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) where
  coordinates : ReadyCoordinates cut.afterArrival i
  gain_preserved : ∀ q, cut.afterArrival.x i (.z q) = s.x i (.z q)
  recovery_preserved : cut.afterArrival.x i .b = s.x i .b
  raw_active : cut.afterArrival.raw i d.port = some cut.afterArrival.time
  raw_other : ∀ q, q ≠ d.port → cut.afterArrival.raw i q = none
  emissions_before : cut.span.emissionTimes i = []

/-- The first receiving-cell delivery need not be the first global event.
A quiet READY cell retains its bands and memories up to that actual arrival. -/
theorem CellDeliveryStep.resting_input {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) (hs : ReadyCoordinates s i)
    (hr : ∀ q, s.raw i q = none) : Nonempty (RestingCellInput cut) := by
  have hno := cut.no_arrivals_before
  have hm := cut.span.ready_without_input_band i hs.ready hs.charge.2 hr hno
  have hflows := cut.span.allStates_main_flows i .ready hm
  have hraw := fun q => cut.span.raw_absent_of_no_arrival i q (hr q) (hno q)
  have hsol := cut.span.ready_no_current_solution i hflows (fun q => (hraw q).2)
  have hlo := cut.span.ready_charge_lower i hflows hs.charge.1
  have hdecay := decay_upper (show s.x i .q - 1 / 10 ≤ (1 / 25 : ℝ) by linarith [hs.charge.2])
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) (sub_nonneg.mpr cut.span.time_monotone)
  have hhi : cut.beforeArrival.x i .q ≤ 7 / 50 := by linarith
  have haux := fun q => cut.span.aux_no_input_rest_band i q (hs.auxiliary q).1
    (hs.auxiliary q).2 (hr q) (hno q)
  have hb := cut.span.recovery_constant_ready i hflows
  refine ⟨⟨?_,?_,?_,?_,?_,cut.span.no_emissions_of_ready_states i hm⟩⟩
  · refine ⟨?_,?_,?_⟩
    · rw [cut.modes_after.1]
      exact cut.span.allStates_final hm
    · rw [cut.entry.physical_continuous]
      exact ⟨hlo,hhi⟩
    · intro q
      rw [cut.modes_after.2,cut.entry.physical_continuous]
      exact (haux q).1
  · intro q
    rw [cut.entry.physical_continuous]
    exact (haux q).2
  · rw [cut.entry.physical_continuous]
    exact hb
  · simpa only [cut.cell] using cut.raw_after
  · intro q hq
    rw [cut.raw_other i q (Or.inr hq)]
    exact (hraw q).1

end KernelR.Hybrid
