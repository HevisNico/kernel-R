import KernelR.HybridCadenceWeakStepExistence

/-! A genuine three-response weak prefix for any period-four source budget.
The source at the initial clock has already arrived. The three subsequent
arrivals are consumed from the actual queue, with all remaining occurrences
and the cell's own memories retained. No output calendar is supplied. -/
namespace KernelR.Hybrid

structure ConstructedCadenceWeakWarmupK (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) (K : ℕ) where
  first : CadenceWeakResponse θ route s p 0
  sourceFirst : CadenceWeakNextSource first (sourceTrain 0 p (s.time + 8) 4 (K - 2))
  second : CadenceWeakResponse θ route sourceFirst.final p 1
  sourceSecond : CadenceWeakNextSource second (sourceTrain 0 p (s.time + 12) 4 (K - 3))
  third : CadenceWeakResponse θ route sourceSecond.final p 2
  sourceThird : CadenceWeakNextSource third (sourceTrain 0 p (s.time + 16) 4 (K - 4))
  execution : Execution θ route s sourceThird.final
  contacts_transversal : execution.ContactsTransversal
  reconstruct : execution = sourceFirst.execution.append
    (sourceSecond.execution.append sourceThird.execution)
  date_first : sourceFirst.final.time = s.time + 4
  date_second : sourceSecond.final.time = s.time + 8
  date : sourceThird.final.time = s.time + 12
  coordinates : CadenceReadyCoordinates sourceThird.final 0 (3 / 10)
  charge_lower : 1 / 10 ≤ sourceThird.final.x 0 .q
  gain_target : sourceThird.final.x 0 (.z p) = s.x 0 (.z p) + 9 / 5
  gain_other : ∀ q, q ≠ p → sourceThird.final.x 0 (.z q) = s.x 0 (.z q)
  recovery : sourceThird.final.x 0 .b = s.x 0 .b
  raw_active : sourceThird.final.raw 0 p = some sourceThird.final.time
  raw_other : ∀ q, q ≠ p → sourceThird.final.raw 0 q = none
  pending : sourceThird.final.pending = sourceTrain 0 p (s.time + 16) 4 (K - 4)
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries =
    [⟨0,p,s.time + 4⟩,⟨0,p,s.time + 8⟩,⟨0,p,s.time + 12⟩]
  error_target : execution.ledger.error 0 p = 9 / 5
  error_other : ∀ q, q ≠ p → execution.ledger.error 0 q = 0
  mark_zero : ∀ q, execution.ledger.mark 0 q = 0
  physical : PhysicalInvariant θ sourceThird.final
  raw_valid : RawValid sourceThird.final
  complete : CompleteThrough execution (s.time + 12)

noncomputable def ConstructedCadenceWeakWarmupK.final {θ route s p K}
    (w : ConstructedCadenceWeakWarmupK θ route s p K) : Snapshot 1 := w.sourceThird.final

theorem ConstructedCadenceWeakWarmupK.final_eq {θ route s p K}
    (w : ConstructedCadenceWeakWarmupK θ route s p K) : w.final = w.sourceThird.final := rfl

/-- Construct the first three weak responses from the real current RAW and
the remaining K-1 source occurrences. K=4 is allowed and leaves no pending
source after the third new arrival. -/
theorem constructed_cadence_weak_warmup_k_exists {θ ε route}
    (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port) (K : ℕ) (hK : 4 ≤ K)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 0) (hq : s.x 0 .q = 1 / 10)
    (hz : s.x 0 (.z p) ≤ Real.log (3 / 10) + 1 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hqueue : s.pending = sourceTrain 0 p (s.time + 4) 4 (K - 1)) :
    Nonempty (ConstructedCadenceWeakWarmupK θ route s p K) := by
  have hcoords0 : CadenceReadyCoordinates s 0 (cadenceWeakInputCap 0) := by
    refine ⟨hs.ready,?_,hs.auxiliary⟩
    rw [hq]
    norm_num [cadenceWeakInputCap]
  have hz0 : s.x 0 (.z p) ≤
      Real.log (3 / 10) + (3 / 5) * ((0 : Fin 3).val : ℝ) + 1 / 100000 := by
    simpa using hz
  have hp0 : ∀ d ∈ s.pending, s.time + 4 ≤ d.due := by
    intro d hd
    rw [hqueue] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change s.time + 4 ≤ s.time + 4 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨first⟩ := cadence_weak_response_exists (route := route) hb s p 0
    hf hv hcoords0 hz0 hr ho hp0
  have hq0 : s.pending = ⟨0,p,s.time + 4⟩ :: sourceTrain 0 p (s.time + 8) 4 (K - 2) := by
    rw [hqueue,show K - 1 = (K - 2) + 1 by omega,sourceTrain_succ,
      show s.time + 4 + 4 = s.time + 8 by ring]
  have hl0 : ∀ d ∈ sourceTrain (0 : Fin 1) p (s.time + 8) 4 (K - 2),
      s.time + 4 < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change s.time + 4 < s.time + 8 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨a⟩ := cadence_weak_next_source_exists first hb hf hv _ hq0 hl0
  have hta : a.final.time = s.time + 4 := a.date
  have hcoords1 : CadenceReadyCoordinates a.final 0 (cadenceWeakInputCap 1) := by
    simpa [cadenceWeakOutputCap,cadenceWeakInputCap] using a.coordinates
  have hz1 : a.final.x 0 (.z p) ≤
      Real.log (3 / 10) + (3 / 5) * ((1 : Fin 3).val : ℝ) + 1 / 100000 := by
    rw [a.gain_target]
    norm_num
    linarith
  have hp1 : ∀ d ∈ a.final.pending, a.final.time + 4 ≤ d.due := by
    intro d hd
    rw [a.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hta]
    change s.time + 4 + 4 ≤ s.time + 8 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨second⟩ := cadence_weak_response_exists (route := route) hb a.final p 1
    a.physical a.raw_valid hcoords1 hz1 a.raw_active a.raw_other hp1
  have hq1 : a.final.pending = ⟨0,p,a.final.time + 4⟩ ::
      sourceTrain 0 p (s.time + 12) 4 (K - 3) := by
    rw [a.pending,hta,show K - 2 = (K - 3) + 1 by omega,sourceTrain_succ,
      show s.time + 4 + 4 = s.time + 8 by ring,
      show s.time + 8 + 4 = s.time + 12 by ring]
  have hl1 : ∀ d ∈ sourceTrain (0 : Fin 1) p (s.time + 12) 4 (K - 3),
      a.final.time + 4 < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hta]
    change s.time + 4 + 4 < s.time + 12 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨b⟩ := cadence_weak_next_source_exists second hb a.physical a.raw_valid _ hq1 hl1
  have htb : b.final.time = s.time + 8 := by rw [b.date,hta]; ring
  have hcoords2 : CadenceReadyCoordinates b.final 0 (cadenceWeakInputCap 2) := by
    simpa [cadenceWeakOutputCap,cadenceWeakInputCap] using b.coordinates
  have hz2 : b.final.x 0 (.z p) ≤
      Real.log (3 / 10) + (3 / 5) * ((2 : Fin 3).val : ℝ) + 1 / 100000 := by
    rw [b.gain_target,a.gain_target]
    norm_num
    linarith
  have hp2 : ∀ d ∈ b.final.pending, b.final.time + 4 ≤ d.due := by
    intro d hd
    rw [b.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [htb]
    change s.time + 8 + 4 ≤ s.time + 12 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨third⟩ := cadence_weak_response_exists (route := route) hb b.final p 2
    b.physical b.raw_valid hcoords2 hz2 b.raw_active b.raw_other hp2
  have hq2 : b.final.pending = ⟨0,p,b.final.time + 4⟩ ::
      sourceTrain 0 p (s.time + 16) 4 (K - 4) := by
    rw [b.pending,htb,show K - 3 = (K - 4) + 1 by omega,sourceTrain_succ,
      show s.time + 8 + 4 = s.time + 12 by ring,
      show s.time + 12 + 4 = s.time + 16 by ring]
  have hl2 : ∀ d ∈ sourceTrain (0 : Fin 1) p (s.time + 16) 4 (K - 4),
      b.final.time + 4 < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [htb]
    change s.time + 8 + 4 < s.time + 16 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨c⟩ := cadence_weak_next_source_exists third hb b.physical b.raw_valid _ hq2 hl2
  have htc : c.final.time = s.time + 12 := by rw [c.date,htb]; ring
  let trace := a.execution.append (b.execution.append c.execution)
  have hGain : c.final.x 0 (.z p) = s.x 0 (.z p) + 9 / 5 := by
    rw [c.gain_target,b.gain_target,a.gain_target]
    ring
  have hOther : ∀ q, q ≠ p → c.final.x 0 (.z q) = s.x 0 (.z q) := by
    intro q hq
    rw [c.gain_other q hq,b.gain_other q hq,a.gain_other q hq]
  have hRec : c.final.x 0 .b = s.x 0 .b := by rw [c.recovery,b.recovery,a.recovery]
  have hEm : trace.ledger.emissions = [] := by
    rw [Execution.emissions_append,Execution.emissions_append,a.emissions,b.emissions,c.emissions]
    rfl
  have hDel : trace.deliveries =
      [⟨0,p,s.time + 4⟩,⟨0,p,s.time + 8⟩,⟨0,p,s.time + 12⟩] := by
    rw [Execution.deliveries_append,Execution.deliveries_append,a.deliveries,b.deliveries,c.deliveries,
      hta,htb,show s.time + 4 + 4 = s.time + 8 by ring,
      show s.time + 8 + 4 = s.time + 12 by ring]
    rfl
  have hLower : 1 / 10 ≤ c.final.x 0 .q := by
    rw [c.values]
    apply third.charge_lower
    rw [b.values]
    apply second.charge_lower
    rw [a.values]
    apply first.charge_lower
    rw [hq]
  have hCoords : CadenceReadyCoordinates c.final 0 (3 / 10) := by
    simpa [cadenceWeakOutputCap] using c.coordinates
  have hMark : ∀ q, trace.ledger.mark 0 q = 0 := by
    intro q
    have hm := trace.ready_states_of_no_emissions 0 hs.ready (by simp [Execution.emissionTimes,hEm])
    exact trace.mark_zero_ready 0 q (trace.allStates_main_flows 0 .ready hm)
  refine ⟨{
    first := first, sourceFirst := a, second := second, sourceSecond := b, third := third, sourceThird := c
    contacts_transversal := by
      simp [trace, a.contacts_transversal, b.contacts_transversal, c.contacts_transversal]
    execution := trace, reconstruct := rfl, date_first := hta, date_second := htb, date := htc
    coordinates := hCoords, charge_lower := hLower, gain_target := hGain, gain_other := hOther
    recovery := hRec, raw_active := c.raw_active, raw_other := c.raw_other, pending := c.pending
    emissions := hEm, deliveries := hDel, error_target := ?_, error_other := ?_, mark_zero := hMark
    physical := c.physical, raw_valid := c.raw_valid, complete := ?_
  }⟩
  · have h := trace.gain_balance 0 p
    rw [hGain] at h
    linarith
  · intro q hq
    have h := trace.gain_balance 0 q
    rw [hOther q hq] at h
    linarith
  · have h := c.complete
    rw [htb,show s.time + 8 + 4 = s.time + 12 by ring] at h
    exact h

end KernelR.Hybrid
