import KernelR.HybridFirstReverseInterleavedPair

/-! Memory and ledger consequences of the actual first reverse interleaving.
These equalities use the retained receiver cut and both cells' own memories. -/
namespace KernelR.Hybrid
namespace FirstReverseInterleavedPair
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f} (p : FirstReverseInterleavedPair r)

theorem a_gain_other (q : Port) (hq : q ≠ 2) :
    p.final.x 0 (.z q) = r.final.x 0 (.z q) := by
  rw [p.a_values]
  exact (p.receiver.cut352.cut.aux_no_input_rest_band 0 q
    ((r.receiver_local_prepared 0).auxiliary q).1
    ((r.receiver_local_prepared 0).auxiliary q).2
    (r.receiver_local_other 0 q (Or.inr hq)) (p.receiver.cut_no_arrival q)).2

theorem b_gains_at_receipt (q : Port) :
    p.final.x 1 (.z q) = r.final.x 1 (.z q) := by
  rw [p.b_gains,r.gains,f.gains]

theorem b_recovery_at_receipt : p.final.x 1 .b = r.final.x 1 .b := by
  rw [p.b_recovery,r.recovery,f.recovery,w.recovery]

theorem a_error_other (q : Port) (hq : q ≠ 2) : p.execution.ledger.error 0 q = 0 := by
  have h := p.execution.gain_balance 0 q
  rw [p.a_gain_other q hq] at h
  linarith

theorem b_error_zero (q : Port) : p.execution.ledger.error 1 q = 0 := by
  have h := p.execution.gain_balance 1 q
  rw [p.b_gains_at_receipt q] at h
  linarith

/-- Only the received Aport2 weak pulse can contribute ERROR in this suffix. -/
theorem error_other (i : Fin 2) (q : Port) (h : i ≠ 0 ∨ q ≠ 2) :
    p.execution.ledger.error i q = 0 := by
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
  · exact p.a_error_other q (by simpa using h)
  · exact p.b_error_zero q

theorem a_recovery_zero : p.execution.ledger.recovery 0 = 0 := by
  have h := p.execution.recovery_balance 0
  rw [p.a_recovery] at h
  linarith

theorem b_recovery_zero : p.execution.ledger.recovery 1 = 0 := by
  have h := p.execution.recovery_balance 1
  rw [p.b_recovery_at_receipt] at h
  linarith

theorem recovery_zero (i : Fin 2) : p.execution.ledger.recovery i = 0 := by
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
  · exact p.a_recovery_zero
  · exact p.b_recovery_zero

end FirstReverseInterleavedPair
end KernelR.Hybrid
