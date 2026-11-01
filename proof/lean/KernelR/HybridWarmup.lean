import KernelR.HybridBirthInput
/-! Select the silent low-port warmup prefix from actual period-eight source deliveries. -/
namespace KernelR.Hybrid

/-- The first three low-port gain levels lie in the proved silent regime. -/
theorem low_training_headroom {stage : ℕ} {z : ℝ} (hs : stage ≤ 2)
    (hz : z ≤ Real.log (3 / 10) + (3 / 5) * stage + 1 / 100000) :
    z ≤ Real.log (6 / 5) + 1 / 1000 := by
  have hlog : Real.log (6 / 5 : ℝ) = Real.log (3 / 10) + Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (3 / 10 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    norm_num
  have hs' : (stage : ℝ) ≤ 2 := by exact_mod_cast hs
  rw [hlog]
  linarith [KernelR.log_four_bounds.1]

structure Warmup {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (weak future : ℕ) where
  entry : Snapshot n
  head : Execution θ route s entry
  rest : Execution θ route entry u
  reconstruct : e = head.append rest
  coordinates : ReadyCoordinates entry i
  recovery_preserved : entry.x i .b = s.x i .b
  gain_target : entry.x i (.z p) = s.x i (.z p) + (3 / 5) * weak
  gain_other : ∀ q, q ≠ p → entry.x i (.z q) = s.x i (.z q)
  emissions : head.emissionTimes i = []
  mark_zero : ∀ q, head.ledger.mark i q = 0
  raw_active : entry.raw i p = some entry.time
  raw_other : ∀ q, q ≠ p → entry.raw i q = none
  date : entry.time = s.time + 8 * weak
  calendar : rest.deliveries = sourceTrain i p (entry.time + 8) 8 future

/-- Every weak case is proved from its gain and actual isolated delivery span.
The resulting strong-entry prefix is reconstructed from the original execution. -/
theorem warmup_prefix {n θ ε route born} (hborn : @BirthState n born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) : ∀ (weak stage future : ℕ) {s u : Snapshot n}
    (e : Execution θ route s u) (_past : Execution θ route born s)
    (_hs : ReadyCoordinates s i) (_hst : stage + weak = 3)
    (_hz : Real.log (3 / 10) + (3 / 5) * stage - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + (3 / 5) * stage + 1 / 100000)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.deliveries = sourceTrain i p (s.time + 8) 8 (weak + future)),
    Nonempty (Warmup e i p weak future) := by
  intro weak
  induction weak with
  | zero =>
    intro stage future s u e past hs hst hz hr ho hcalendar
    exact ⟨⟨s,.nil _,e,rfl,hs,rfl,by simp,fun _ _ => rfl,rfl,fun _ => rfl,hr,ho,
      by simp,by simpa only [Nat.zero_add] using hcalendar⟩⟩
  | succ weak ih =>
    intro stage future s u e past hs hst hz hr ho hcalendar
    have hstage : stage ≤ 2 := by omega
    have hsilent := low_training_headroom hstage hz.2
    have hcal : e.deliveries = ⟨i,p,s.time + 8⟩ :: sourceTrain i p (s.time + 8 + 8) 8 (weak + future) := by
      rw [hcalendar,show (weak + 1) + future = (weak + future) + 1 by omega,sourceTrain_succ]
    obtain ⟨cut⟩ := e.first_delivery _ _ hcal
    have hdate := cut.date
    obtain ⟨pulse⟩ := cut.span.silent_pulse past hborn hb i p hs hsilent hr ho
      (cut.no_arrivals_before i) (by have h := hdate.1; dsimp at h; linarith)
    have hnext := cut.ready_coordinates i pulse.coordinates
    have hznext : Real.log (3 / 10) + (3 / 5) * (stage + 1 : ℕ) - 1 / 100000 ≤ cut.afterArrival.x i (.z p) ∧
        cut.afterArrival.x i (.z p) ≤ Real.log (3 / 10) + (3 / 5) * (stage + 1 : ℕ) + 1 / 100000 := by
      rw [cut.entry.physical_continuous,pulse.gain_target]
      push_cast
      constructor <;> linarith [hz.1,hz.2]
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hnextCal : cut.rest.deliveries = sourceTrain i p (cut.afterArrival.time + 8) 8 (weak + future) := by
      rw [cut.later,hdate.2]
    let progressed := past.append (cut.span.append (.cons (.jump cut.entry) (.nil _)))
    obtain ⟨warm⟩ := ih (stage + 1) future cut.rest progressed hnext (by omega) hznext hrnext honext hnextCal
    let head := cut.span.append (.cons (.jump cut.entry) warm.head)
    have hd : (⟨i,p,s.time + 8⟩ : Delivery n) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
    refine ⟨{
      entry := warm.entry
      head := head
      rest := warm.rest
      reconstruct := ?_
      coordinates := warm.coordinates
      recovery_preserved := ?_
      gain_target := ?_
      gain_other := ?_
      emissions := ?_
      mark_zero := ?_
      raw_active := warm.raw_active
      raw_other := warm.raw_other
      date := ?_
      calendar := warm.calendar
    }⟩
    · calc
        e = cut.span.append (.cons (.jump cut.entry) cut.rest) := cut.reconstruct
        _ = cut.span.append (.cons (.jump cut.entry) (warm.head.append warm.rest)) :=
          congrArg (fun actual => cut.span.append (.cons (.jump cut.entry) actual)) warm.reconstruct
        _ = _ := by simp only [head,Execution.append_assoc,Execution.append]
    · rw [warm.recovery_preserved,cut.entry.physical_continuous,pulse.recovery_preserved]
    · rw [warm.gain_target,cut.entry.physical_continuous,pulse.gain_target]
      push_cast
      ring
    · intro q hq
      rw [warm.gain_other q hq,cut.entry.physical_continuous,pulse.gain_other q hq]
    · simp [head,Execution.emissionTimes_append,Execution.emissionTimes_cons,Move.ledger,
        cut.entry.no_emissions_of_delivery _ hd,pulse.emissions,warm.emissions]
    · intro q
      simp [head,Execution.mark_append,Execution.ledger,Move.ledger,Ledger.add,
        cut.entry.mark_zero,pulse.mark_zero q,warm.mark_zero q]
    · rw [warm.date,hdate.2]
      push_cast
      ring

theorem Warmup.error_target {n θ route s u i p weak future} {e : @Execution n θ route s u}
    (warm : Warmup e i p weak future) : warm.head.ledger.error i p = (3 / 5) * weak := by
  have h := warm.head.gain_balance i p
  rw [warm.gain_target] at h
  linarith

theorem Warmup.error_other {n θ route s u i p weak future} {e : @Execution n θ route s u}
    (warm : Warmup e i p weak future) (q : Port) (hq : q ≠ p) : warm.head.ledger.error i q = 0 := by
  have h := warm.head.gain_balance i q
  rw [warm.gain_other q hq] at h
  linarith

end KernelR.Hybrid
