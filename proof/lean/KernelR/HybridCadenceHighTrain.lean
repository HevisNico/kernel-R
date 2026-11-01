import KernelR.HybridHighGainReturn
import KernelR.HybridCellInputs
/-! Actual variable-gap learned trains after the two cadence MARK doses. -/
namespace KernelR.Hybrid

structure CadenceHighTrain {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (count : ℕ) where
  emissions : (e.emissionTimes i).length = count
  error_zero : ∀ p, e.ledger.error i p = 0
  mark_zero : ∀ p, e.ledger.mark i p = 0
  gain_preserved : ∀ p, u.x i (.z p) = s.x i (.z p)
  recovery_preserved : u.x i .b = s.x i .b
  ready : u.main i = .ready
  charge_rest : u.x i .q = 1 / 10
  auxiliary : ∀ p, u.aux i p = .ready ∧ RestBand (u.x i (.m p))
  raw_finished : ∀ p, u.raw i p = none

/-- Every actual high-gain input fires exactly once and settles before a
3.8-gap successor. The first pulse retains its real initial residual charge;
later cuts use exact physical returns. All other-cell traffic is retained. -/
theorem cadence_high_train_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : ∀ (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (_hf : PhysicalInvariant θ s) (_hv : RawValid s) (_hm : s.main i = .ready)
    (_hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 2)
    (_hgain : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (_hbrecovery : 37999 / 100000 ≤ s.x i .b)
    (_ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (_hspace : (s.time :: times).Pairwise (fun t v => t + 19 / 5 ≤ v))
    (_hquiet : ∀ t ∈ s.time :: times, t + 19 / 5 ≤ u.time),
    Nonempty (CadenceHighTrain e i (times.length + 1)) := by
  intro times
  induction times with
  | nil =>
    intro s u e hf hv hm hq hgain hbrecovery ha hr ho hcalendar hspace hquiet
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.high_gain_pulse_of_valid hb hf.region hv i p hm hq hgain
      ⟨hbrecovery,hf.recovery_cap i⟩ ha hr ho hn (hquiet s.time (by simp))
    exact ⟨⟨by rw [pulse.emissions]; rfl,pulse.error_zero,pulse.mark_zero,pulse.gain_preserved,
      pulse.recovery_preserved,pulse.ready,pulse.charge_rest,pulse.auxiliary,pulse.raw_finished⟩⟩
  | cons next times ih =>
    intro s u e hf hv hm hq hgain hbrecovery ha hr ho hcalendar hspace hquiet
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: times.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hgap : s.time + 19 / 5 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.high_gain_pulse_of_valid hb hf.region hv i p hm hq hgain
      ⟨hbrecovery,hf.recovery_cap i⟩ ha hr ho cut.no_arrivals_before (by rw [cut.date.1]; exact hgap)
    have hmnext : cut.afterArrival.main i = .ready := by rw [cut.modes_after.1]; exact pulse.ready
    have hqnext : cut.afterArrival.x i .q = 1 / 10 := by rw [cut.entry.physical_continuous,pulse.charge_rest]
    have hgainnext : 16 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 7 / 2 := by
      rw [cut.entry.physical_continuous,pulse.gain_preserved p]
      exact hgain
    have hbnext : 37999 / 100000 ≤ cut.afterArrival.x i .b := by
      rw [cut.entry.physical_continuous,pulse.recovery_preserved]
      exact hbrecovery
    have hanext : ∀ q, cut.afterArrival.aux i q = .ready ∧ RestBand (cut.afterArrival.x i (.m q)) := by
      intro q
      rw [cut.modes_after.2,cut.entry.physical_continuous]
      exact pulse.auxiliary q
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: times).Pairwise (fun t v => t + 19 / 5 ≤ v) := by
      rw [cut.date.2]
      exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: times, t + 19 / 5 ≤ u.time := by
      rw [cut.date.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    obtain ⟨train⟩ := ih cut.rest (advanced.physical_invariant hb hf) (advanced.raw_valid hv)
      hmnext (by rw [hqnext]; norm_num) hgainnext hbnext hanext hrnext honext cut.later hspaceNext hquietNext
    have hg : ∀ q, u.x i (.z q) = s.x i (.z q) := by
      intro q
      rw [train.gain_preserved q,cut.entry.physical_continuous,pulse.gain_preserved q]
    refine ⟨⟨?_,?_,?_,hg,?_,train.ready,train.charge_rest,train.auxiliary,train.raw_finished⟩⟩
    · rw [cut.emissions,List.length_append,pulse.emissions,train.emissions]
      simp only [List.length_cons,List.length_nil]
      omega
    · intro q
      have h := e.gain_balance i q
      rw [hg q] at h
      linarith
    · intro q
      have h := e.mark_split cut.span cut.entry cut.rest cut.reconstruct i q
      rw [pulse.mark_zero q,train.mark_zero q] at h
      simpa only [zero_add] using h
    · rw [train.recovery_preserved,cut.entry.physical_continuous,pulse.recovery_preserved]

end KernelR.Hybrid
