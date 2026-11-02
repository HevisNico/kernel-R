import KernelR.HybridCadenceWeakWarmupK
import KernelR.HybridCadenceStrongSlowSpan
import KernelR.HybridCadenceMarkOnlyJitterNextSource

/-! The first strong leaf response retains the weak prefix's carried charge.
Its actual FAST and SLOW paths reach the fourth period-four source, then the
protected MARK response reaches the fifth. Every arrival consumes the real
source queue; neither charge nor energy is reset at either handoff. -/
namespace KernelR.Hybrid

structure ConstructedCadenceLeafFirstMarkK {θ : Fin 1 → Parameters} {s : Snapshot 1}
    {p : Port} {K : ℕ}
    (warmup : ConstructedCadenceWeakWarmupK θ (fun _ _ => []) s p K) where
  fire : FirstLearnedFire θ (fun _ _ => []) warmup.final 0 p
  fast : PortFastCompletion θ (fun _ _ => []) fire.final p
  span : CadenceStrongSlowSpan fast
  source : Snapshot 1
  source_state : source = {setRaw span.final 0 p (some span.final.time) with
    pending := sourceTrain 0 p (s.time + 20) 4 (K - 5)}
  arrival : Jump (fun _ _ => []) span.final source
  strong : Execution θ (fun _ _ => []) warmup.final source
  strong_reconstruct : strong = ((fire.execution.append fast.execution).append span.execution).append
    (.cons (.jump arrival) (.nil _))
  source_date : source.time = s.time + 16
  source_values : source.x = span.final.x
  source_slow : source.main 0 = .slow
  source_charge : 37 / 250 ≤ source.x 0 .q ∧ source.x 0 .q ≤ 1 / 4
  source_energy : source.x 0 .energy = span.final.x 0 .energy
  mark : CadenceMarkOnlyJitterNextSource θ source p (s.time + 20)
    (sourceTrain 0 p (s.time + 24) 4 (K - 6))
  execution : Execution θ (fun _ _ => []) warmup.final mark.final
  reconstruct : execution = strong.append mark.execution
  date : mark.final.time = s.time + 20
  ready : ∀ j, ReadyCoordinates mark.final j
  charge : mark.final.x 0 .q = 1 / 10
  raw_active : mark.final.raw 0 p = some mark.final.time
  raw_other : ∀ q, q ≠ p → mark.final.raw 0 q = none
  pending : mark.final.pending = sourceTrain 0 p (s.time + 24) 4 (K - 6)
  gains : ∀ q, mark.final.x 0 (.z q) = warmup.final.x 0 (.z q)
  gain_target : mark.final.x 0 (.z p) = s.x 0 (.z p) + 9 / 5
  gain_other : ∀ q, q ≠ p → mark.final.x 0 (.z q) = s.x 0 (.z q)
  recovery : mark.final.x 0 .b = warmup.final.x 0 .b + 1 / 10
  recovery_own : mark.final.x 0 .b = s.x 0 .b + 1 / 10
  recovery_band : 27999 / 100000 ≤ mark.final.x 0 .b ∧ mark.final.x 0 .b ≤ 28001 / 100000
  emissions : execution.ledger.emissions = [(0,fire.final.time)]
  emission_count : (execution.emissionTimes 0).length = 1
  deliveries : execution.deliveries = [⟨0,p,s.time + 16⟩,⟨0,p,s.time + 20⟩]
  error_zero : ∀ q, execution.ledger.error 0 q = 0
  recovery_dose : execution.ledger.recovery 0 = 1 / 10
  mark_target : execution.ledger.mark 0 p = 1 / 10
  mark_other : ∀ q, q ≠ p → execution.ledger.mark 0 q = 0
  physical : PhysicalInvariant θ mark.final
  raw_valid : RawValid mark.final
  complete : CompleteThrough execution (s.time + 20)

noncomputable def ConstructedCadenceLeafFirstMarkK.final {θ s p K}
    {w : ConstructedCadenceWeakWarmupK θ (fun _ _ => []) s p K}
    (c : ConstructedCadenceLeafFirstMarkK w) : Snapshot 1 := c.mark.final

/-- Build the first actual strong/MARK pair from the genuine weak prefix.
The original cell's own nominal gain and recovery bands are the only scalar
data used to derive the two physical response bounds. -/
theorem constructed_cadence_leaf_first_mark_k_exists {θ ε s p K}
    (hb : @PhysicalBox 1 θ ε)
    (warmup : ConstructedCadenceWeakWarmupK θ (fun _ _ => []) s p K) (hK : 7 ≤ K)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 1 / 100000)
    (hB : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000) :
    Nonempty (ConstructedCadenceLeafFirstMarkK warmup) := by
  have hWdate : warmup.final.time = s.time + 12 := warmup.date
  have hWgain : warmup.final.x 0 (.z p) = s.x 0 (.z p) + 9 / 5 := warmup.gain_target
  have hWrecovery : warmup.final.x 0 .b = s.x 0 .b := warmup.recovery
  have hWqueue : warmup.final.pending = sourceTrain 0 p (s.time + 16) 4 (K - 4) := warmup.pending
  have hzW : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ warmup.final.x 0 (.z p) ∧
      warmup.final.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [hWgain]
    constructor <;> linarith [hz.1,hz.2]
  have hg := cadence_three_dose_gain_bounds hzW
  have hBW : 17999 / 100000 ≤ warmup.final.x 0 .b ∧
      warmup.final.x 0 .b ≤ 18001 / 100000 := by
    rw [hWrecovery]
    exact hB
  have hp : ∀ d ∈ warmup.final.pending, warmup.final.time + 4 ≤ d.due := by
    intro d hd
    rw [hWqueue] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hWdate]
    change s.time + 12 + 4 ≤ s.time + 16 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨fire⟩ := cadence_first_strong_fire_exists hb warmup.final p
    warmup.physical warmup.raw_valid warmup.coordinates hg warmup.raw_active warmup.raw_other hp
  obtain ⟨fast⟩ := fire.cadence_residual_fast_completion_exists hb
    warmup.coordinates hg.2 warmup.raw_other hp
  obtain ⟨span⟩ := fire.cadence_strong_slow_span_exists hb fast warmup.coordinates hg.2 hBW hp
  have hSpanDate : span.final.time = s.time + 16 := by rw [span.date,hWdate]; ring
  have hSpanQueue : span.final.pending = ⟨0,p,s.time + 16⟩ ::
      sourceTrain 0 p (s.time + 20) 4 (K - 5) := by
    rw [span.pending,fast.pending,fire.pending,List.append_nil,hWqueue,
      show K - 4 = (K - 5) + 1 by omega,sourceTrain_succ,
      show s.time + 16 + 4 = s.time + 20 by ring]
  let source : Snapshot 1 := {setRaw span.final 0 p (some span.final.time) with
    pending := sourceTrain 0 p (s.time + 20) 4 (K - 5)}
  let arrival : Jump (fun _ _ => []) span.final source :=
    .arrive span.final ⟨0,p,s.time + 16⟩ [] _ hSpanQueue hSpanDate.symm (span.raw_none 0 p)
  let strong := ((fire.execution.append fast.execution).append span.execution).append
    (.cons (.jump arrival) (.nil _))
  have hSourceDate : source.time = s.time + 16 := hSpanDate
  have hSourceRaw : source.raw 0 p = some source.time := by simp [source,setRaw]
  have hSourceOther (q : Port) (hq : q ≠ p) : source.raw 0 q = none := by
    simp [source,setRaw,hq,span.raw_none]
  have hSourceGains (q : Port) : source.x 0 (.z q) = warmup.final.x 0 (.z q) :=
    (span.gains 0 q).trans ((fast.gains 0 q).trans (fire.gain_preserved 0 q))
  have hSourceRecovery : source.x 0 .b = warmup.final.x 0 .b :=
    (span.recovery 0).trans ((fast.recovery 0).trans (fire.recovery_preserved 0))
  have hSourceB : 17999 / 100000 ≤ source.x 0 .b ∧ source.x 0 .b ≤ 18001 / 100000 := by
    rw [hSourceRecovery]
    exact hBW
  have hSourceQueue : source.pending = ⟨0,p,s.time + 20⟩ ::
      sourceTrain 0 p (s.time + 24) 4 (K - 6) := by
    change sourceTrain 0 p (s.time + 20) 4 (K - 5) = _
    rw [show K - 5 = (K - 6) + 1 by omega,sourceTrain_succ,
      show s.time + 20 + 4 = s.time + 24 by ring]
  have hLater : ∀ d ∈ sourceTrain (0 : Fin 1) p (s.time + 24) 4 (K - 6),
      s.time + 20 < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change s.time + 20 < s.time + 24 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  have heStrong : strong.ledger.emissions = [(0,fire.final.time)] := by
    have heArrival : arrival.ledger.emissions = [] := rfl
    simp only [strong,Execution.emissions_append,fire.emissions,fast.emissions,span.emissions,
      Execution.ledger,Move.ledger,heArrival,Ledger.add,Ledger.zero,List.append_nil]
    rfl
  have hdStrong : strong.deliveries = [⟨0,p,s.time + 16⟩] := by
    have hdArrival : arrival.deliveries = [⟨0,p,s.time + 16⟩] := rfl
    simp only [strong,Execution.deliveries_append,fire.deliveries,fast.deliveries,span.deliveries,
      Execution.deliveries,Move.deliveries,hdArrival,List.nil_append,List.append_nil]
  have hSourcePhysical := strong.physical_invariant hb warmup.physical
  have hSourceValid := strong.raw_valid warmup.raw_valid
  obtain ⟨mark⟩ := cadence_mark_only_jitter_next_source_exists hb source p (s.time + 20)
    (sourceTrain 0 p (s.time + 24) 4 (K - 6)) hSourcePhysical hSourceValid span.main_slow
    span.charge hSourceB (fun q => ⟨span.auxiliary 0 q,span.rest q⟩) hSourceRaw hSourceOther
    hSourceQueue (by rw [hSourceDate]; linarith) hLater
  let trace := strong.append mark.execution
  have hGain (q : Port) : mark.final.x 0 (.z q) = warmup.final.x 0 (.z q) :=
    (mark.gains 0 q).trans (hSourceGains q)
  have hRecovery : mark.final.x 0 .b = warmup.final.x 0 .b + 1 / 10 := by
    rw [mark.recovery_gain,hSourceRecovery]
  have heTrace : trace.ledger.emissions = [(0,fire.final.time)] := by
    rw [Execution.emissions_append,heStrong,mark.emissions,List.append_nil]
  have hdTrace : trace.deliveries = [⟨0,p,s.time + 16⟩,⟨0,p,s.time + 20⟩] := by
    rw [Execution.deliveries_append,hdStrong,mark.deliveries]
    rfl
  have hError (q : Port) : trace.ledger.error 0 q = 0 := by
    have h := trace.gain_balance 0 q
    rw [hGain] at h
    linarith
  have hRecoveryDose : trace.ledger.recovery 0 = 1 / 10 := by
    have h := trace.recovery_balance 0
    rw [hRecovery] at h
    linarith
  have hMarkOther (q : Port) (hq : q ≠ p) : trace.ledger.mark 0 q = 0 := by
    have hNo : NoArrivalAt trace 0 q := by simp [NoArrivalAt,hdTrace,Ne.symm hq]
    have hAux := trace.aux_ready_without_input_band 0 q (warmup.coordinates.auxiliary q).1
      (warmup.coordinates.auxiliary q).2.2 (warmup.raw_other q hq) hNo
    exact trace.mark_zero_aux 0 q .ready (by decide) (trace.allStates_aux_flows 0 q .ready hAux)
  have hMark : trace.ledger.mark 0 p = 1 / 10 := by
    have hsum : (∑ q : Port,trace.ledger.mark 0 q) = trace.ledger.mark 0 p :=
      Finset.sum_eq_single p (fun q _ hq => hMarkOther q hq) (by simp)
    have h := trace.recovery_sum_marks 0
    rw [hRecoveryDose,hsum] at h
    exact h.symm
  refine ⟨{
    fire := fire, fast := fast, span := span, source := source, source_state := rfl
    arrival := arrival, strong := strong, strong_reconstruct := rfl
    source_date := hSourceDate, source_values := rfl, source_slow := span.main_slow
    source_charge := span.charge, source_energy := rfl, mark := mark
    execution := trace, reconstruct := rfl, date := mark.date, ready := mark.ready, charge := mark.charge
    raw_active := ?_, raw_other := mark.raw_other, pending := mark.pending, gains := hGain
    gain_target := (hGain p).trans warmup.gain_target
    gain_other := fun q hq => (hGain q).trans (warmup.gain_other q hq)
    recovery := hRecovery, recovery_own := ?_, recovery_band := mark.recovery_band
    emissions := heTrace, emission_count := ?_, deliveries := hdTrace
    error_zero := hError, recovery_dose := hRecoveryDose, mark_target := hMark, mark_other := hMarkOther
    physical := mark.physical, raw_valid := mark.raw_valid, complete := mark.complete
  }⟩
  · rw [mark.date]
    exact mark.raw_active
  · rw [hRecovery,hWrecovery]
  · simp [Execution.emissionTimes,heTrace]

end KernelR.Hybrid
