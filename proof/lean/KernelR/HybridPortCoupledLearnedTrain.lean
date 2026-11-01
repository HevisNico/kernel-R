import KernelR.HybridPortCoupledLearnedCycle
import KernelR.HybridCoupledLearnedTrain

/-! Construct a finite train by actual coupled cycles and actual external A
arrivals. All B wire tokens are issued and consumed inside the real cycles. -/
namespace KernelR.Hybrid

private theorem port_cycle_s_times {θS θR route pS pR delay s}
    (c : PortCoupledLearnedCycle θS θR route s pS pR delay) : c.execution.emissionTimes 0 = [c.fireS] := by
  simp [Execution.emissionTimes,c.emissions,PortCoupledLearnedCycle.fireS]

private theorem port_cycle_r_times {θS θR route pS pR delay s}
    (c : PortCoupledLearnedCycle θS θR route s pS pR delay) : c.execution.emissionTimes 1 = [c.fireR] := by
  simp [Execution.emissionTimes,c.emissions,PortCoupledLearnedCycle.fireR]

structure PortCoupledLearnedTrain (θS θR : Fin 1 → Parameters) (route : Router 2)
    (source : Snapshot 2) (pS pR : Port) (delay : ℝ → ℝ) (count : ℕ) (later : List (Delivery 2)) where
  final : Snapshot 2
  execution : Execution (extendParameters θS (θR 0)) route source final
  date : final.time = source.time + 8 * ((count : ℝ) + 1)
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i p, final.raw i p = none
  pending : final.pending = later
  gains : ∀ i p, final.x i (.z p) = source.x i (.z p)
  recovery : ∀ i, final.x i .b = source.x i .b
  a_emission_count : (execution.emissionTimes 0).length = count + 1
  b_emission_count : (execution.emissionTimes 1).length = count + 1
  a_deliveries : execution.cellDeliveries 0 = sourceTrain 0 pS (source.time + 8) 8 count
  wireTimes : List ℝ
  wire_count : wireTimes.length = count + 1
  b_deliveries : execution.cellDeliveries 1 = wireTimes.map (fun t => (⟨1,pR,t⟩ : Delivery 2))
  wire_provenance : ∀ t ∈ wireTimes, ∃ F ∈ execution.emissionTimes 0, t = F + delay F
  initial_prepared : ∀ i, PreparedSection source i
  initial_raw_other : ∀ i p, i ≠ 0 ∨ p ≠ pS → source.raw i p = none
  physical : PhysicalInvariant (extendParameters θS (θR 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (source.time + 8 * ((count : ℝ) + 1))

/-- The only supplied calendar is the already queued external source list.
Pulse outputs, contact arrivals and the final prepared section are constructed. -/
theorem port_coupled_learned_train_exists {θS θR : Fin 1 → Parameters} {ε route pS pR delay}
    (hb : @PhysicalBox 2 (extendParameters θS (θR 0)) ε) (source : Snapshot 2)
    (count : ℕ) (later : List (Delivery 2))
    (hf : PhysicalInvariant (extendParameters θS (θR 0)) source) (hv : RawValid source)
    (hwindow : 480 ≤ source.time ∧ source.time + 8 * (count : ℝ) ≤ 600)
    (hs : ∀ i, PreparedSection source i) (hq : ∀ i, source.x i .q = 1 / 10)
    (hGA : 9 / 5 ≤ Real.exp (source.x 0 (.z pS)) ∧ Real.exp (source.x 0 (.z pS)) ≤ 2)
    (hGB : 9 / 5 ≤ Real.exp (source.x 1 (.z pR)) ∧ Real.exp (source.x 1 (.z pR)) ≤ 11 / 5)
    (hr : source.raw 0 pS = some source.time)
    (ho : ∀ i p, i ≠ 0 ∨ p ≠ pS → source.raw i p = none)
    (hqueue : source.pending = sourceTrain 0 pS (source.time + 8) 8 count ++ later)
    (hLater : ∀ d ∈ later, source.time + 8 * ((count : ℝ) + 1) < d.due)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5)
    (hroute : ∀ F, 480 ≤ F → F < 601 → route 0 F = [⟨1,pR,F + delay F⟩])
    (hclosed : ∀ t, 480 ≤ t → t ≤ 608 → route 1 t = []) :
    Nonempty (PortCoupledLearnedTrain θS θR route source pS pR delay count later) := by
  induction count generalizing source with
  | zero =>
    have hpending : source.pending = later := by simpa [sourceTrain] using hqueue
    obtain ⟨c⟩ := port_coupled_learned_cycle_exists hb source hf hv
      ⟨hwindow.1,by simpa using hwindow.2⟩ hs hq hGA hGB hr ho
      (by intro d hd; rw [hpending] at hd; have h := hLater d hd; norm_num at h; exact h.le)
      hdelay hroute hclosed
    refine ⟨{
      final := c.final, execution := c.execution
      date := by simpa using c.date
      prepared := c.prepared, charge := c.charge, raw_none := c.raw_none
      pending := c.pending.trans hpending, gains := c.gains, recovery := c.recovery
      a_emission_count := by rw [port_cycle_s_times]; rfl
      b_emission_count := by rw [port_cycle_r_times]; rfl
      a_deliveries := by simp [Execution.cellDeliveries,c.deliveries,sourceTrain]
      wireTimes := [c.wireTime]
      wire_count := rfl
      b_deliveries := by simp [Execution.cellDeliveries,c.deliveries,PortCoupledLearnedCycle.wireTime]
      wire_provenance := ?_
      initial_prepared := hs, initial_raw_other := ho
      physical := c.physical, raw_valid := c.raw_valid
      complete := by
        have h := c.complete (by intro d hd; rw [hpending] at hd; simpa using hLater d hd)
        simpa using h
    }⟩
    intro t ht
    have ht' : t = c.wireTime := List.mem_singleton.mp ht
    subst t
    exact ⟨c.fireS,by rw [port_cycle_s_times]; simp,c.wire_date⟩
  | succ count ih =>
    have hSourceMax : source.time ≤ 600 := by
      have hn : (0 : ℝ) ≤ ((count + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hwindow.2]
    have htailBound : source.time + 8 ≤ source.time + 8 * ((((count + 1 : ℕ) : ℝ)) + 1) := by
      have hn : (0 : ℝ) ≤ (count : ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
    have hpending : ∀ d ∈ source.pending, source.time + 8 ≤ d.due := by
      intro d hd
      rw [hqueue] at hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
        change source.time + 8 ≤ source.time + 8 + 8 * (k.val : ℝ)
        nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
      · exact htailBound.trans (hLater d hd).le
    obtain ⟨c⟩ := port_coupled_learned_cycle_exists hb source hf hv ⟨hwindow.1,hSourceMax⟩
      hs hq hGA hGB hr ho hpending hdelay hroute hclosed
    let nextSources := sourceTrain (0 : Fin 2) pS (source.time + 16) 8 count ++ later
    have hhead : c.final.pending = [] ++ (⟨0,pS,source.time + 8⟩ : Delivery 2) :: nextSources := by
      rw [c.pending,hqueue,sourceTrain_succ]
      have ht : source.time + 8 + 8 = source.time + 16 := by ring
      simp only [List.cons_append,ht,List.nil_append]
      rfl
    let next : Snapshot 2 := { (setRaw c.final 0 pS (some c.final.time)) with pending := nextSources }
    let arrival : Jump route c.final next :=
      .arrive c.final ⟨0,pS,source.time + 8⟩ [] nextSources hhead c.date.symm (c.raw_none 0 pS)
    let headTrace := c.execution.append (.cons (.jump arrival) (.nil _))
    have hNextDate : next.time = source.time + 8 := c.date
    have hnextPrepared : ∀ i, PreparedSection next i := fun i =>
      ⟨(c.prepared i).ready,(c.prepared i).charge,(c.prepared i).recovery,(c.prepared i).auxiliary⟩
    have hnextQ : ∀ i, next.x i .q = 1 / 10 := c.charge
    have hnextGA : 9 / 5 ≤ Real.exp (next.x 0 (.z pS)) ∧ Real.exp (next.x 0 (.z pS)) ≤ 2 := by
      change 9 / 5 ≤ Real.exp (c.final.x 0 (.z pS)) ∧ Real.exp (c.final.x 0 (.z pS)) ≤ 2
      rw [c.gains]
      exact hGA
    have hnextGB : 9 / 5 ≤ Real.exp (next.x 1 (.z pR)) ∧ Real.exp (next.x 1 (.z pR)) ≤ 11 / 5 := by
      change 9 / 5 ≤ Real.exp (c.final.x 1 (.z pR)) ∧ Real.exp (c.final.x 1 (.z pR)) ≤ 11 / 5
      rw [c.gains]
      exact hGB
    have hnextRaw : next.raw 0 pS = some next.time := by simp [next,setRaw]
    have hnextOther : ∀ i p, i ≠ (0 : Fin 2) ∨ p ≠ pS → next.raw i p = none := by
      intro i p h
      change (setRaw c.final 0 pS (some c.final.time)).raw i p = none
      rw [raw_update_other _ _ _ _ _ _ h]
      exact c.raw_none i p
    have hhorizon : next.time + 8 * ((count : ℝ) + 1) =
        source.time + 8 * ((((count + 1 : ℕ) : ℝ)) + 1) := by
      rw [hNextDate]
      push_cast
      ring
    obtain ⟨t⟩ := ih next (headTrace.physical_invariant hb hf) (headTrace.raw_valid hv)
      (by
        rw [hNextDate]
        constructor
        · linarith [hwindow.1]
        · push_cast at hwindow
          linarith [hwindow.2])
      hnextPrepared hnextQ hnextGA hnextGB hnextRaw hnextOther
      (by
        change nextSources = _
        rw [hNextDate]
        have ht : source.time + 8 + 8 = source.time + 16 := by ring
        rw [ht])
      (by intro d hd; rw [hhorizon]; exact hLater d hd)
    let e := headTrace.append t.execution
    have hPrefixEm : headTrace.ledger.emissions = c.execution.ledger.emissions := by
      have hj : arrival.ledger.emissions = [] := rfl
      simp only [headTrace,Execution.emissions_append,Execution.ledger,Move.ledger,hj,Ledger.add,Ledger.zero,List.append_nil]
    have hPrefixA : headTrace.emissionTimes 0 = [c.fireS] := by
      simp only [Execution.emissionTimes,hPrefixEm]
      exact port_cycle_s_times c
    have hPrefixB : headTrace.emissionTimes 1 = [c.fireR] := by
      simp only [Execution.emissionTimes,hPrefixEm]
      exact port_cycle_r_times c
    have hPrefixDelA : headTrace.cellDeliveries 0 = [⟨0,pS,source.time + 8⟩] := by
      have hj : arrival.deliveries = [⟨0,pS,source.time + 8⟩] := rfl
      simp [headTrace,Execution.cellDeliveries,Execution.deliveries_append,c.deliveries,
        Execution.deliveries,Move.deliveries,hj]
    have hPrefixDelB : headTrace.cellDeliveries 1 = [⟨1,pR,c.wireTime⟩] := by
      have hj : arrival.deliveries = [⟨0,pS,source.time + 8⟩] := rfl
      simp [headTrace,Execution.cellDeliveries,Execution.deliveries_append,c.deliveries,
        Execution.deliveries,Move.deliveries,hj,PortCoupledLearnedCycle.wireTime]
    refine ⟨{
      final := t.final, execution := e
      date := t.date.trans hhorizon
      prepared := t.prepared, charge := t.charge, raw_none := t.raw_none
      pending := t.pending
      gains := fun i p => (t.gains i p).trans (c.gains i p)
      recovery := fun i => (t.recovery i).trans (c.recovery i)
      a_emission_count := ?_, b_emission_count := ?_
      a_deliveries := ?_
      wireTimes := c.wireTime :: t.wireTimes
      wire_count := by simp only [List.length_cons,t.wire_count]
      b_deliveries := ?_
      wire_provenance := ?_
      initial_prepared := hs, initial_raw_other := ho
      physical := t.physical, raw_valid := t.raw_valid
      complete := by
        change CompleteThrough t.execution _
        rw [← hhorizon]
        exact t.complete
    }⟩
    · simp only [e,Execution.emissionTimes_append,List.length_append,hPrefixA,List.length_singleton,t.a_emission_count]
      omega
    · simp only [e,Execution.emissionTimes_append,List.length_append,hPrefixB,List.length_singleton,t.b_emission_count]
      omega
    · rw [show e.cellDeliveries 0 = headTrace.cellDeliveries 0 ++ t.execution.cellDeliveries 0 from Execution.cellDeliveries_append _ _ _]
      rw [hPrefixDelA,t.a_deliveries,sourceTrain_succ,hNextDate]
      rfl
    · rw [show e.cellDeliveries 1 = headTrace.cellDeliveries 1 ++ t.execution.cellDeliveries 1 from Execution.cellDeliveries_append _ _ _]
      rw [hPrefixDelB,t.b_deliveries]
      rfl
    · intro time htime
      rcases List.mem_cons.mp htime with heq | ht
      · subst time
        refine ⟨c.fireS,?_,c.wire_date⟩
        rw [show e.emissionTimes 0 = headTrace.emissionTimes 0 ++ t.execution.emissionTimes 0 from Execution.emissionTimes_append _ _ _]
        rw [hPrefixA]
        simp
      · obtain ⟨F,hF,hdate⟩ := t.wire_provenance time ht
        refine ⟨F,?_,hdate⟩
        rw [show e.emissionTimes 0 = headTrace.emissionTimes 0 ++ t.execution.emissionTimes 0 from Execution.emissionTimes_append _ _ _]
        exact List.mem_append_right _ hF

namespace PortCoupledLearnedTrain
variable {θS θR route source pS pR delay count later}
  (c : PortCoupledLearnedTrain θS θR route source pS pR delay count later)

theorem ready : ∀ i, ReadyCoordinates c.final i := fun i =>
  ⟨(c.prepared i).ready,(c.prepared i).charge,(c.prepared i).auxiliary⟩

theorem b_wire_count : (c.execution.cellDeliveries 1).length = count + 1 := by
  rw [c.b_deliveries,List.length_map,c.wire_count]

theorem error_zero (i : Fin 2) (p : Port) : c.execution.ledger.error i p = 0 := by
  have h := c.execution.gain_balance i p
  rw [c.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : c.execution.ledger.recovery i = 0 := by
  have h := c.execution.recovery_balance i
  rw [c.recovery] at h
  linarith

/-- No other receiving port is introduced by the constructed real deliveries. -/
theorem b_delivery_port (d : Delivery 2) (hd : d ∈ c.execution.deliveries) (hc : d.cell = 1) : d.port = pR := by
  have hmem : d ∈ c.execution.cellDeliveries 1 := by simp [Execution.cellDeliveries,hd,hc]
  rw [c.b_deliveries] at hmem
  obtain ⟨time,_,rfl⟩ := List.mem_map.mp hmem
  rfl

theorem a_delivery_port (d : Delivery 2) (hd : d ∈ c.execution.deliveries) (hc : d.cell = 0) : d.port = pS := by
  have hmem : d ∈ c.execution.cellDeliveries 0 := by simp [Execution.cellDeliveries,hd,hc]
  rw [c.a_deliveries] at hmem
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hmem
  rfl

private theorem mark_other_zero (i : Fin 2) (q : Port)
    (hraw : source.raw i q = none)
    (hno : NoArrivalAt c.execution i q) : c.execution.ledger.mark i q = 0 := by
  have hquiet := c.execution.aux_ready_without_input_band i q ((c.initial_prepared i).auxiliary q).1
    ((c.initial_prepared i).auxiliary q).2.2 hraw hno
  exact c.execution.mark_zero_aux i q .ready (by decide)
    (c.execution.allStates_aux_flows i q .ready hquiet)

theorem mark_zero (i : Fin 2) (q : Port) : c.execution.ledger.mark i q = 0 := by
  have isolate (j : Fin 2) (active : Port)
      (hport : ∀ d ∈ c.execution.deliveries, d.cell = j → d.port = active)
      (hraw : ∀ r, r ≠ active → source.raw j r = none) :
      ∀ r, c.execution.ledger.mark j r = 0 := by
    have hother : ∀ r, r ≠ active → c.execution.ledger.mark j r = 0 := by
      intro r hr
      apply c.mark_other_zero j r (hraw r hr)
      intro d hd
      by_cases hc : d.cell = j
      · exact Or.inr (by rw [hport d hd hc]; exact Ne.symm hr)
      · exact Or.inl hc
    have hsum : (∑ r : Port, c.execution.ledger.mark j r) = c.execution.ledger.mark j active :=
      Finset.sum_eq_single active (fun r _ hr => hother r hr) (by simp)
    have hmain : c.execution.ledger.mark j active = 0 := by
      have h := c.execution.recovery_sum_marks j
      rw [c.recovery_zero j,hsum] at h
      exact h.symm
    intro r
    by_cases hr : r = active
    · subst r; exact hmain
    · exact hother r hr
  fin_cases i
  · exact isolate 0 pS c.a_delivery_port
      (fun r hr => c.initial_raw_other 0 r (Or.inr hr)) q
  · exact isolate 1 pR c.b_delivery_port
      (fun r _ => c.initial_raw_other 1 r (Or.inl (by decide))) q

end PortCoupledLearnedTrain
end KernelR.Hybrid
