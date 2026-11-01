import KernelR.HybridCadenceCPhase
import KernelR.HybridCadenceWireCalendar
import KernelR.HybridCadenceAPhase
/-! Physical period-four cascade, retaining the complete actual execution. -/
namespace KernelR.Hybrid

structure CadenceCascade {θ route s u} (e : @Execution 3 θ route s u) where
  a_emissions : (e.emissionTimes 0).length = 16
  b_emissions : (e.emissionTimes 1).length = 18
  c_emissions : (e.emissionTimes 2).length = 20
  a_error : e.ledger.error 0 2 = 3 / 5
  b_error : e.ledger.error 1 2 = 3 / 5
  c_error : e.ledger.error 2 0 = 12 / 5
  a_mark : e.ledger.mark 0 2 = 1 / 5
  b_mark : e.ledger.mark 1 2 = 1 / 5
  c_mark : e.ledger.mark 2 0 = 1 / 5
  gain_a : u.x 0 (.z 2) = s.x 0 (.z 2) + 3 / 5
  gain_b : u.x 1 (.z 2) = s.x 1 (.z 2) + 3 / 5
  gain_c : u.x 2 (.z 0) = s.x 2 (.z 0) + 12 / 5
  gain_a_other : ∀ p, p ≠ 2 → u.x 0 (.z p) = s.x 0 (.z p)
  gain_b_other : ∀ p, p ≠ 2 → u.x 1 (.z p) = s.x 1 (.z p)
  gain_c_other : ∀ p, p ≠ 0 → u.x 2 (.z p) = s.x 2 (.z p)
  recovery : ∀ i, u.x i .b = s.x i .b + 1 / 5
  ready : ∀ i, u.main i = .ready
  charge_rest : ∀ i, u.x i .q = 1 / 10
  auxiliary : ∀ i p, u.aux i p = .ready ∧ RestBand (u.x i (.m p))
  raw_finished : ∀ i p, u.raw i p = none
  physical : PhysicalInvariant θ u
  raw_valid : RawValid u
  pending_empty : u.pending = []

/-- The last cadence gate closes strictly before the supplied endpoint. All
initial and actually routed tokens are past due there, so none can remain in
the physical queue. No case word or output count enters this conservation fact. -/
theorem Execution.cadence_queue_empty {θ s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u)
    (hA : s.pending.filter (fun d => d.cell = 0) = [])
    (hB : s.pending.filter (fun d => d.cell = 1) = [])
    (hC : (s.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 25))
    (hu : u.time = 7899 / 10) (hpf : PendingFuture u)
    (hf : ∀ t, forward t ≤ 2 / 5) (hb : ∀ t, backward t ≤ 2 / 5) : u.pending = [] := by
  have hsource : ∀ d ∈ s.pending, d.due < u.time := by
    intro d hd
    by_cases h0 : d.cell = 0
    · have hm : d ∈ s.pending.filter (fun d => d.cell = 0) := by
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨hd,h0⟩
      rw [hA] at hm
      contradiction
    by_cases h1 : d.cell = 1
    · have hm : d ∈ s.pending.filter (fun d => d.cell = 1) := by
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨hd,h1⟩
      rw [hB] at hm
      contradiction
    have h2 : d.cell = 2 := by have h := d.cell.isLt; omega
    have hm : d ∈ s.pending.filter (fun d => d.cell = 2) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hd,h2⟩
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (hC.mem_iff.mp hm)
    have hk : (k.val : ℝ) ≤ 24 := by exact_mod_cast (show k.val ≤ 24 by omega)
    rw [hu]
    change 640 + 4 * (k.val : ℝ) < 7899 / 10
    linarith
  have hroute : ∀ event ∈ e.ledger.emissions,
      ∀ d ∈ cadenceRouter forward backward event.1 event.2, d.due < u.time := by
    intro event _ d hd
    rcases List.mem_append.mp hd with hd | hd
    · unfold Contact.route at hd
      split_ifs at hd with h
      · simp only [List.mem_singleton] at hd
        subst d
        have ht : event.2 < (780 : ℝ) := h.2.2
        change event.2 + forward event.2 < u.time
        rw [hu]
        linarith [hf event.2]
      · contradiction
    · unfold Contact.route at hd
      split_ifs at hd with h
      · simp only [List.mem_singleton] at hd
        subst d
        have ht : event.2 < (780 : ℝ) := h.2.2
        change event.2 + backward event.2 < u.time
        rw [hu]
        linarith [hb event.2]
      · contradiction
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  have hfuture := hpf d hd
  rcases e.pending_provenance d hd with h | ⟨event,he,hr⟩
  · exact not_lt_of_ge hfuture (hsource d h)
  · exact not_lt_of_ge hfuture (hroute event he d hr)

/-- Actual source conservation and the two actual wire calendars derive the
complete C-to-B-to-A cadence cascade. No output list, case word or desired
count/dose is a premise. The reaching execution itself is supplied. -/
theorem Execution.cadence_cascade {θ ε s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : ∀ i, PreparedSection s i) (hq : ∀ i, s.x i .q = 1 / 10)
    (hr : ∀ i p, s.raw i p = none)
    (hza : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z 2) ∧
      s.x 0 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hzb : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 1 (.z 2) ∧
      s.x 1 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hzc : Real.log (3 / 10) - 1 / 100000 ≤ s.x 2 (.z 0) ∧
      s.x 2 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000)
    (hA : s.pending.filter (fun d => d.cell = 0) = [])
    (hB : s.pending.filter (fun d => d.cell = 1) = [])
    (hC : (s.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 25))
    (hu : u.time = 7899 / 10) (hpf : PendingFuture s)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (CadenceCascade e) := by
  have hcausal := cadenceRouter.causal forward backward
    (fun t => by linarith [(hforward t).1]) (fun t => by linarith [(hbackward t).1])
  have hfuture := e.pending_future hcausal hpf
  obtain ⟨pre⟩ := e.cadence_prelude forward backward hb hf hv
    (hs 0) (hq 0) (hr 0) (hs 1) (hq 1) (hr 1) (hs 2) (hq 2) (hr 2) hzc.2
    hA hB hC hu hpf (fun t => by linarith [(hforward t).1]) (fun t => by linarith [(hbackward t).1])
  obtain ⟨cphase⟩ := pre.c_phase hb hzc (hs 2).recovery hu
  obtain ⟨ccal⟩ := cphase.output_calendar hb hzc (hs 2).recovery hu
  obtain ⟨bphase⟩ := ccal.b_phase hb hf hv (hs 1) (hq 1) (hr 1) hzb hB hu hfuture hforward
  obtain ⟨aphase⟩ := bphase.a_phase hb hf hv (hs 0) (hq 0) (hr 0) hza hA hu hfuture hforward hbackward
  refine ⟨⟨aphase.emission_count,bphase.emission_count,cphase.emissions,
    aphase.relay.error_target,bphase.relay.error_target,cphase.error_target,
    aphase.relay.mark_target,bphase.relay.mark_target,cphase.mark_target,
    aphase.relay.gain_target,bphase.relay.gain_target,cphase.gain_target,
    aphase.relay.gain_other,bphase.relay.gain_other,cphase.gain_other,?_,?_,?_,?_,?_,
    e.physical_invariant hb hf,e.raw_valid hv,
    e.cadence_queue_empty forward backward hA hB hC hu hfuture
      (fun t => (hforward t).2) (fun t => (hbackward t).2)⟩⟩
  · intro i
    fin_cases i
    · exact aphase.relay.recovery_gain
    · exact bphase.relay.recovery_gain
    · exact cphase.recovery_gain
  · intro i
    fin_cases i
    · exact aphase.relay.ready
    · exact bphase.relay.ready
    · exact cphase.ready
  · intro i
    fin_cases i
    · exact aphase.relay.charge_rest
    · exact bphase.relay.charge_rest
    · exact cphase.charge_rest
  · intro i p
    fin_cases i
    · exact aphase.relay.auxiliary p
    · exact bphase.relay.auxiliary p
    · exact cphase.auxiliary p
  · intro i p
    fin_cases i
    · exact aphase.relay.raw_finished p
    · exact bphase.relay.raw_finished p
    · exact cphase.raw_finished p

end KernelR.Hybrid
