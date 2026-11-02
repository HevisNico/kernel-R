import KernelR.HybridCadenceWeakStepExistence

/-! Three actual C responses at640/644/648 reach the real fresh source652.
Their own gain, recovery, energy residues, and exact source queue are carried. -/
namespace KernelR.Hybrid

structure ConstructedCadenceWeakWarmup (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) where
  first : CadenceWeakResponse θ route s 0 0
  source644 : CadenceWeakNextSource first (sourceTrain 0 0 648 4 23)
  second : CadenceWeakResponse θ route source644.final 0 1
  source648 : CadenceWeakNextSource second (sourceTrain 0 0 652 4 22)
  third : CadenceWeakResponse θ route source648.final 0 2
  source652 : CadenceWeakNextSource third (sourceTrain 0 0 656 4 21)
  execution : Execution θ route s source652.final
  reconstruct : execution = source644.execution.append (source648.execution.append source652.execution)
  date : source652.final.time = 652
  coordinates : CadenceReadyCoordinates source652.final 0 (3 / 10)
  charge_lower : 1 / 10 ≤ source652.final.x 0 .q
  gain_target : source652.final.x 0 (.z 0) = s.x 0 (.z 0) + 9 / 5
  gain_other : ∀ q, q ≠ 0 → source652.final.x 0 (.z q) = s.x 0 (.z q)
  recovery : source652.final.x 0 .b = s.x 0 .b
  raw_active : source652.final.raw 0 0 = some source652.final.time
  raw_other : ∀ q, q ≠ 0 → source652.final.raw 0 q = none
  pending : source652.final.pending = sourceTrain 0 0 656 4 21
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,0,644⟩,⟨0,0,648⟩,⟨0,0,652⟩]
  error_target : execution.ledger.error 0 0 = 9 / 5
  error_other : ∀ q, q ≠ 0 → execution.ledger.error 0 q = 0
  mark_zero : ∀ q, execution.ledger.mark 0 q = 0
  physical : PhysicalInvariant θ source652.final
  raw_valid : RawValid source652.final
  complete : CompleteThrough execution 652

noncomputable def ConstructedCadenceWeakWarmup.final {θ route s}
    (w : ConstructedCadenceWeakWarmup θ route s) : Snapshot 1 := w.source652.final

theorem ConstructedCadenceWeakWarmup.final_eq {θ route s}
    (w : ConstructedCadenceWeakWarmup θ route s) : w.final = w.source652.final := rfl

/-- Only the actual source640 state and its remaining twenty-four source
occurrences are supplied. All three responses and the next three deliveries
are constructed; no reaching trace, dose, or output calendar is a premise. -/
theorem constructed_cadence_weak_warmup_exists {θ ε route}
    (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ht : s.time = 640) (hs : PreparedSection s 0) (hq : s.x 0 .q = 1 / 10)
    (hz : s.x 0 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000)
    (hr : s.raw 0 0 = some s.time) (ho : ∀ q, q ≠ 0 → s.raw 0 q = none)
    (hqueue : s.pending = sourceTrain 0 0 644 4 24) :
    Nonempty (ConstructedCadenceWeakWarmup θ route s) := by
  have hcoords0 : CadenceReadyCoordinates s 0 (cadenceWeakInputCap 0) := by
    refine ⟨hs.ready,?_,hs.auxiliary⟩
    rw [hq]
    norm_num [cadenceWeakInputCap]
  have hz0 : s.x 0 (.z 0) ≤ Real.log (3 / 10) + (3 / 5) * ((0 : Fin 3).val : ℝ) + 1 / 100000 := by
    simpa using hz
  have hp0 : ∀ d ∈ s.pending, s.time + 4 ≤ d.due := by
    intro d hd
    rw [hqueue] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [ht]
    change 640 + 4 ≤ 644 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨first⟩ := cadence_weak_response_exists (route := route) hb s 0 0 hf hv hcoords0 hz0 hr ho hp0
  have hq0 : s.pending = ⟨0,0,s.time + 4⟩ :: sourceTrain 0 0 648 4 23 := by
    rw [hqueue,ht,sourceTrain_succ]
    norm_num
  have hl0 : ∀ d ∈ sourceTrain (0 : Fin 1) 0 648 4 23, s.time + 4 < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [ht]
    change 640 + 4 < 648 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨a⟩ := cadence_weak_next_source_exists first hb hf hv _ hq0 hl0
  have hta : a.final.time = 644 := by rw [a.date,ht]; norm_num
  have hcoords1 : CadenceReadyCoordinates a.final 0 (cadenceWeakInputCap 1) := by
    simpa [cadenceWeakOutputCap,cadenceWeakInputCap] using a.coordinates
  have hz1 : a.final.x 0 (.z 0) ≤ Real.log (3 / 10) + (3 / 5) * ((1 : Fin 3).val : ℝ) + 1 / 100000 := by
    rw [a.gain_target]
    norm_num
    linarith
  have hp1 : ∀ d ∈ a.final.pending, a.final.time + 4 ≤ d.due := by
    intro d hd
    rw [a.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hta]
    change 644 + 4 ≤ 648 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨second⟩ := cadence_weak_response_exists (route := route) hb a.final 0 1 a.physical a.raw_valid
    hcoords1 hz1 a.raw_active a.raw_other hp1
  have hq1 : a.final.pending = ⟨0,0,a.final.time + 4⟩ :: sourceTrain 0 0 652 4 22 := by
    rw [a.pending,hta,sourceTrain_succ]
    norm_num
  have hl1 : ∀ d ∈ sourceTrain (0 : Fin 1) 0 652 4 22, a.final.time + 4 < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hta]
    change 644 + 4 < 652 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨b⟩ := cadence_weak_next_source_exists second hb a.physical a.raw_valid _ hq1 hl1
  have htb : b.final.time = 648 := by rw [b.date,hta]; norm_num
  have hcoords2 : CadenceReadyCoordinates b.final 0 (cadenceWeakInputCap 2) := by
    simpa [cadenceWeakOutputCap,cadenceWeakInputCap] using b.coordinates
  have hz2 : b.final.x 0 (.z 0) ≤ Real.log (3 / 10) + (3 / 5) * ((2 : Fin 3).val : ℝ) + 1 / 100000 := by
    rw [b.gain_target,a.gain_target]
    norm_num
    linarith
  have hp2 : ∀ d ∈ b.final.pending, b.final.time + 4 ≤ d.due := by
    intro d hd
    rw [b.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [htb]
    change 648 + 4 ≤ 652 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨third⟩ := cadence_weak_response_exists (route := route) hb b.final 0 2 b.physical b.raw_valid
    hcoords2 hz2 b.raw_active b.raw_other hp2
  have hq2 : b.final.pending = ⟨0,0,b.final.time + 4⟩ :: sourceTrain 0 0 656 4 21 := by
    rw [b.pending,htb,sourceTrain_succ]
    norm_num
  have hl2 : ∀ d ∈ sourceTrain (0 : Fin 1) 0 656 4 21, b.final.time + 4 < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [htb]
    change 648 + 4 < 656 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨c⟩ := cadence_weak_next_source_exists third hb b.physical b.raw_valid _ hq2 hl2
  have htc : c.final.time = 652 := by rw [c.date,htb]; norm_num
  let trace := a.execution.append (b.execution.append c.execution)
  have hGain : c.final.x 0 (.z 0) = s.x 0 (.z 0) + 9 / 5 := by
    rw [c.gain_target,b.gain_target,a.gain_target]
    ring
  have hOther : ∀ q, q ≠ 0 → c.final.x 0 (.z q) = s.x 0 (.z q) := by
    intro q hq
    rw [c.gain_other q hq,b.gain_other q hq,a.gain_other q hq]
  have hRec : c.final.x 0 .b = s.x 0 .b := by rw [c.recovery,b.recovery,a.recovery]
  have hEm : trace.ledger.emissions = [] := by
    rw [Execution.emissions_append,Execution.emissions_append,a.emissions,b.emissions,c.emissions]
    rfl
  have hDel : trace.deliveries = [⟨0,0,644⟩,⟨0,0,648⟩,⟨0,0,652⟩] := by
    rw [Execution.deliveries_append,Execution.deliveries_append,a.deliveries,b.deliveries,c.deliveries,ht,hta,htb]
    norm_num
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
    first := first, source644 := a, second := second, source648 := b, third := third, source652 := c
    execution := trace, reconstruct := rfl, date := htc
    coordinates := hCoords, charge_lower := hLower, gain_target := hGain, gain_other := hOther
    recovery := hRec, raw_active := c.raw_active, raw_other := c.raw_other, pending := c.pending
    emissions := hEm, deliveries := hDel, error_target := ?_, error_other := ?_, mark_zero := hMark
    physical := c.physical, raw_valid := c.raw_valid, complete := ?_
  }⟩
  · have h := trace.gain_balance 0 0
    rw [hGain] at h
    linarith
  · intro q hq
    have h := trace.gain_balance 0 q
    rw [hOther q hq] at h
    linarith
  · have h := c.complete
    rw [htb] at h
    norm_num at h
    exact h

end KernelR.Hybrid
