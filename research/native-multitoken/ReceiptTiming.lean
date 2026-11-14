import NativeMultiTokenMilestone
import ProtectedReceipt

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid Set MeasureTheory

/-- The input date of the child routed by a launch. -/
noncomputable def receiptDate (p : Parameters N) (source : Fin N) : ℝ :=
  launchDate p + latency p source + p.delay source

/-- The receiving cell enters SLOW at its own FAST exit. -/
noncomputable def receiverFastEnd (p : Parameters N) (source : Fin N) : ℝ :=
  launchDate p + latency p (p.successor source) + 1

/-- The charge margin between the receiver's FAST exit and the arrival is
computed from the clocks of the two cells, with T3 reserving an entire
auxiliary cycle beyond the arrival. -/
theorem receipt_timing {p : Parameters N} (accepted : p.check = true) (source : Fin N) :
    receiverFastEnd p source < receiptDate p source ∧
    (9 / 50) * (receiptDate p source - receiverFastEnd p source) +
      (7 / 25) * (419 / 300) < 9 / 10 ∧
    receiptDate p source + 19 / 5 < launchDate p + 19 / 2 := by
  have good : p.Valid := of_decide_eq_true accepted
  have t2 := good.2.2.2.2.1 source
  have lower : (8 / 5 : ℚ) < p.delay source := by linarith
  have lowerReal : (8 / 5 : ℝ) < (p.delay source : ℝ) := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr lower
  have t3 := good.2.2.2.2.2 source
  change (9 / 50 : ℚ) * (p.delay source + 3 / 5 - 1) +
    (7 / 25) * (419 / 300) < 9 / 10 at t3
  have upper : (9 / 50 : ℝ) * ((p.delay source : ℝ) + 3 / 5 - 1) +
      (7 / 25) * (419 / 300) < 9 / 10 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr t3
  obtain ⟨early, late, _, _⟩ := scalar_latency accepted source
  obtain ⟨receiverEarly, receiverLate, _, _⟩ := scalar_latency accepted (p.successor source)
  unfold receiverFastEnd receiptDate
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Execute the guard-free SLOW portion before the receipt, retaining its
charge, auxiliary coordinates and physical clock. -/
theorem slow_span_to_receipt {p : Parameters N} (accepted : p.check = true) (source : Fin N)
    {θ : Fin 1 → KernelR.Hybrid.Parameters} {route : Router 1}
    (s : Snapshot 1) (T : ℝ) (advance : s.time < T) (beforeReceipt : T ≤ receiptDate p source)
    (main : s.main 0 = .slow)
    (charge : s.x 0 .q = (1 / 4) * Real.exp
      (-(9 / 50) * (s.time - receiverFastEnd p source)))
    (recovery : s.x 0 .b = 9 / 50)
    (aux : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (raw : ∀ q, s.raw 0 q = none)
    (pending : ∀ d ∈ s.pending, T ≤ d.due) :
    ∃ (u : Snapshot 1) (run : Execution θ route s u),
      u.time = T ∧ u.main 0 = .slow ∧
      u.x 0 .q = (1 / 4) * Real.exp (-(9 / 50) * (u.time - receiverFastEnd p source)) ∧
      u.x 0 .b = 9 / 50 ∧ (∀ q, u.x 0 (.z q) = s.x 0 (.z q)) ∧
      (∀ q, u.aux 0 q = .ready ∧ RestBand (u.x 0 (.m q))) ∧
      (∀ q, u.raw 0 q = none) ∧ u.pending = s.pending ∧
      run.deliveries = [] ∧ run.ledger.emissions = [] ∧
      (∀ q, run.ledger.mark 0 q = 0) := by
  classical
  obtain ⟨_, budget, _⟩ := receipt_timing accepted source
  have chargeClock (t : ℝ) :
      s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) =
        (1 / 4) * Real.exp (-(9 / 50) * (t - receiverFastEnd p source)) := by
    rw [charge, recovery, mul_assoc, attenuation_split]
  have slowGuard (t : ℝ) (before : t ≤ T) :
      (1 / 10 : ℝ) < (1 / 4) * Real.exp (-(9 / 50) * (t - receiverFastEnd p source)) := by
    have cost : (9 / 50) * (t - receiverFastEnd p source) < Real.log (5 / 2) := by
      linarith [KernelR.log_recovery_bounds.1, before.trans beforeReceipt]
    have ref : Real.exp (-Real.log (5 / 2)) = (2 / 5 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]
      norm_num
    have strict : (2 / 5 : ℝ) < Real.exp (-(9 / 50) * (t - receiverFastEnd p source)) := by
      rw [← ref]
      apply Real.exp_lt_exp.mpr
      linarith
    linarith
  have absent (j : Fin 1) (h : j ≠ 0) : False := h (Subsingleton.elim _ _)
  have modes (j : Fin 1) (q : Port) : s.aux j q = .ready := by
    rw [show j = 0 from Subsingleton.elim _ _]
    exact (aux q).1
  have rawNone (j : Fin 1) (q : Port) : s.raw j q = none := by
    rw [show j = 0 from Subsingleton.elim _ _]
    exact raw q
  have below (j : Fin 1) (q : Port) : s.x j (.m q) < 1 := by
    rw [show j = 0 from Subsingleton.elim _ _]
    linarith [(aux q).2.2]
  let flow : Flow θ s (protectedMainEnd θ s 0 2 .slow .ready none T) :=
    protectedMainFlow s 0 2 .slow .ready none advance (Or.inr rfl) (Or.inl rfl)
      main (fun j h => (absent j h).elim) (aux 2).1 (fun j q _ => modes j q)
      (raw 2) (fun j q _ => rawNone j q) (by intros; contradiction)
      (fun j h => (absent j h).elim) (fun j q _ => below j q)
      (fun t ht => by
        simpa only [protectedMainRate, reduceCtorEq, ite_false, chargeClock] using
          slowGuard t ht.2.le)
      (fun t ht => by
        simp only [ite_true, rawInputScale, mul_zero, auxPulse_zero_eq_relax]
        exact relax_lt (by norm_num) ht.1 (below 0 2) (by norm_num)) pending
  refine ⟨_, .cons (.flow flow) (.nil _), rfl, main, ?_, recovery, (fun _ => rfl),
    ?_, raw, rfl, rfl, rfl, ?_⟩
  · simpa only [protectedMainEnd, protectedMainValues, ite_true, protectedMainRate,
      reduceCtorEq, ite_false] using chargeClock T
  · intro q
    refine ⟨(aux q).1, ?_⟩
    have band := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) advance.le (aux q).2
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    by_cases atPort : q = 2
    · subst q
      simpa [protectedMainEnd, protectedMainValues, rawInputScale, auxPulse_zero_eq_relax, RestBand] using band
    · simpa [protectedMainEnd, protectedMainValues, atPort, RestBand] using band
  · intro q
    change (∫ v in s.time..T, markAct θ s (flow.path v) 0 q) + 0 = 0
    simp [markAct, (aux q).1]

end NetworkStability.NativeMultiToken
