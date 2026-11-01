import KernelR.HybridCadenceSecondStrongSlowSpan

/-! Construct the second strong cadence response and consume its real next
source while it is still SLOW, retaining the exact mixed-input coordinates. -/
namespace KernelR.Hybrid

structure CadenceSecondStrongResponse (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    (later : List (Delivery 1)) where
  fire : FirstLearnedFire θ (fun _ _ => []) s 0 p
  fast : PortFastCompletion θ (fun _ _ => []) fire.final p
  slow : CadenceSecondStrongSlowSpan fast
  final : Snapshot 1
  arrival : Jump (fun _ _ => []) slow.final final
  execution : Execution θ (fun _ _ => []) s final
  reconstruct : execution = ((fire.execution.append fast.execution).append slow.execution).append
    (.cons (.jump arrival) (.nil _))
  date : final.time = s.time + 4
  values : final.x = slow.final.x
  main_slow : final.main 0 = .slow
  auxiliary : ∀ j q, final.aux j q = .ready
  rest : ∀ q, RestBand (final.x 0 (.m q))
  trained_rest : final.x 0 (.m p) = 1 / 40
  charge : 61 / 500 ≤ final.x 0 .q ∧ final.x 0 .q ≤ 7 / 50
  raw_active : final.raw 0 p = some final.time
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  pending : final.pending = later
  emissions : execution.ledger.emissions = [(0,fire.final.time)]
  deliveries : execution.deliveries = [⟨0,p,s.time + 4⟩]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (s.time + 4)

theorem cadence_second_strong_response_exists {θ ε}
    (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (3 / 10)) (hq : s.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hB : 27999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 28001 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (later : List (Delivery 1)) (hqueue : s.pending = ⟨0,p,s.time + 4⟩ :: later)
    (hlater : ∀ d ∈ later, s.time + 4 < d.due) :
    Nonempty (CadenceSecondStrongResponse θ s p later) := by
  have hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due := by
    intro d hd
    rw [hqueue] at hd
    rcases List.mem_cons.mp hd with he | he
    · subst d; exact le_rfl
    · exact (hlater d he).le
  have hg := cadence_three_dose_gain_bounds hz
  obtain ⟨fire⟩ := cadence_first_strong_fire_exists hb s p hf hv hs hg hr ho hp
  obtain ⟨fast⟩ := fire.cadence_residual_fast_completion_exists hb hs hg.2 ho hp
  obtain ⟨slow⟩ := fire.cadence_second_strong_slow_span_exists hb fast hq hz hB hp
  have hqueueSlow : slow.final.pending = [] ++ (⟨0,p,s.time + 4⟩ : Delivery 1) :: later := by
    rw [slow.pending,fast.pending,fire.pending,List.append_nil]
    exact hqueue
  let final : Snapshot 1 := {setRaw slow.final 0 p (some slow.final.time) with pending := later}
  let arrival : Jump (fun _ _ => []) slow.final final :=
    .arrive slow.final ⟨0,p,s.time + 4⟩ [] later hqueueSlow slow.date.symm (slow.raw_none 0 p)
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨0,p,s.time + 4⟩] := rfl
  let execution := ((fire.execution.append fast.execution).append slow.execution).append
    (.cons (.jump arrival) (.nil _))
  have hRaw : final.raw 0 p = some final.time := by simp [final,setRaw]
  have hOther : ∀ q, q ≠ p → final.raw 0 q = none := by
    intro q hq
    simp [final,setRaw,hq,slow.raw_none]
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ later at hd
    change slow.final.time < d.due
    rw [slow.date]
    exact hlater d hd
  have hComplete : CompleteThrough execution (s.time + 4) := by
    refine ⟨slow.date,?_,?_⟩
    · intro u
      apply BeforeGuards.no_jump
      · constructor
        · intro j
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          change (match slow.final.main 0 with
            | .ready => slow.final.x 0 .q < 1
            | .fast => 1 / 4 < slow.final.x 0 .q
            | .slow => 1 / 10 < slow.final.x 0 .q)
          rw [slow.main_slow]
          linarith [slow.charge.1]
        · intro j q
          change (match slow.final.aux j q with
            | .ready => slow.final.x j (.m q) < 1
            | .mark => 4 / 5 < slow.final.x j (.m q)
            | .silent => 1 / 10 < slow.final.x j (.m q)
            | .error => 1 / 40 < slow.final.x j (.m q))
          rw [slow.auxiliary]
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          linarith [(slow.rest q).2]
      · intro j q origin hraw
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        by_cases hq : q = p
        · subst q
          have he : origin = final.time := Option.some.inj (hraw.symm.trans hRaw)
          rw [he]; linarith
        · rw [hOther q hq] at hraw
          contradiction
      · exact hFuture
    · intro d hd
      have h := hFuture d hd
      change slow.final.time < d.due at h
      rw [slow.date] at h
      exact h
  refine ⟨{
    fire := fire, fast := fast, slow := slow, final := final, arrival := arrival
    execution := execution, reconstruct := rfl, date := slow.date, values := rfl
    main_slow := slow.main_slow, auxiliary := slow.auxiliary, rest := slow.rest
    trained_rest := slow.trained_rest, charge := slow.charge, raw_active := hRaw, raw_other := hOther
    gains := fun j q => (slow.gains j q).trans ((fast.gains j q).trans (fire.gain_preserved j q))
    recovery := fun j => (slow.recovery j).trans ((fast.recovery j).trans (fire.recovery_preserved j))
    pending := rfl, emissions := ?_, deliveries := ?_
    physical := execution.physical_invariant hb hf, raw_valid := execution.raw_valid hv, complete := hComplete
  }⟩
  · simp only [execution,Execution.emissions_append,fire.emissions,fast.emissions,slow.emissions,
      Execution.ledger,Move.ledger,haEm,Ledger.add,Ledger.zero,List.append_nil]
    rw [fire.date]
  · simp only [execution,Execution.deliveries_append,fire.deliveries,fast.deliveries,slow.deliveries,
      Execution.deliveries,Move.deliveries,haDel,List.nil_append,List.append_nil]

end KernelR.Hybrid
