import KernelR.HybridFastTeachingCalendar
import KernelR.HybridPreparedSourceContact
import KernelR.HybridCTeachingRouter
import KernelR.HybridBoundaryIdle
/-! The B-to-C epoch after C's birth, with A retained and quiescent. -/
namespace KernelR.Hybrid

structure CIntroductionActivePhase {θ route s u} (e : @Execution 3 θ route s u) where
  a_idle : IdlePrepared e 0
  b_train : PreparedTrain e 1 16
  c_phase : BTeachingPhase e 2 1

/-- Once B's source at 480 is active, its actual pending successors and the
B-to-C contact yield sixteen B outputs and fourteen C outputs. A remains in
the same execution and contributes no emission or memory change. -/
theorem Execution.c_introduction_active_phase {θ ε route s u} (e : @Execution 3 θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : PreparedSection s 0) (hqa : s.x 0 .q = 1 / 10) (hra : ∀ p, s.raw 0 p = none)
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hclosedA : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ 0)
    (hsb : PreparedSection s 1) (hqb : s.x 1 .q = 1 / 10)
    (hzb : 9 / 5 ≤ Real.exp (s.x 1 (.z 2)) ∧ Real.exp (s.x 1 (.z 2)) ≤ 12 / 5)
    (hrb : s.raw 1 2 = some s.time) (hob : ∀ p, p ≠ 2 → s.raw 1 p = none)
    (hBqueue : (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 488 8 15))
    (hclosedB : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ 1)
    (ht : s.time = 480) (hu : u.time = 6399 / 10) (hpf : PendingFuture u)
    (hsc : ReadyCoordinates s 2)
    (hbc : 7999 / 100000 ≤ s.x 2 .b ∧ s.x 2 .b ≤ 8001 / 100000)
    (hzc : Real.log (6 / 5) - 1 / 1000 ≤ s.x 2 (.z 1) ∧ s.x 2 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000)
    (hrc : ∀ p, s.raw 2 p = none)
    (hfuture : ∀ d ∈ s.pending, d.cell = 2 → 640 ≤ d.due)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = 2) = (cTeachingContact delay).route event.1 event.2) :
    Nonempty (CIntroductionActivePhase e) := by
  have hfinish : (480 : ℝ) + 129 ≤ u.time := by rw [hu]; norm_num
  have hqueue : (s.pending.filter (fun d => d.cell = (cTeachingContact delay).source)).Perm
      (sourceTrain (cTeachingContact delay).source 2 (480 + 8) 8 15 ++ []) := by
    change (s.pending.filter (fun d => d.cell = (1 : Fin 3))).Perm
      (sourceTrain 1 2 ((480 : ℝ) + 8) 8 15 ++ [])
    rw [show (480 : ℝ) + 8 = 488 by norm_num,List.append_nil]
    exact hBqueue
  have hfuture' : ∀ d ∈ s.pending, d.cell = (cTeachingContact delay).target → u.time < d.due := by
    intro d hd hc
    rw [hu]
    linarith [hfuture d hd hc]
  have hgate : (cTeachingContact delay).opens ≤ (480 : ℝ) + 3 / 10 ∧
      (480 : ℝ) + 120 + 9 / 10 ≤ (cTeachingContact delay).closes := by norm_num [cTeachingContact]
  obtain ⟨sender⟩ := e.prepared_source_contact hb hf.region hv (cTeachingContact delay) 2 480
    hsb hqb hzb hrb hob [] hqueue (by simp) hclosedB ht hfinish hpf hfuture' hwire hgate hdelay
  have hcalC : e.cellDeliveries 2 = List.ofFn (fun k : Fin 16 =>
      ⟨2,1,480 + 8 * (k.val : ℝ) + restLatency (Real.exp (s.x 1 (.z 2))) +
        delay (480 + 8 * (k.val : ℝ) + restLatency (Real.exp (s.x 1 (.z 2))))⟩) := by
    simpa only [cTeachingContact,Contact.token] using sender.calendar
  obtain ⟨receiver⟩ := e.fast_teaching_of_calendar hb hf hv 2 1 hsc hbc hzc hrc
    480 hfinish (Real.exp (s.x 1 (.z 2))) hzb delay hdelay hcalC
  have hnoA : ∀ p, NoArrivalAt e 0 p := by
    intro p d hd
    rcases e.delivery_provenance d hd with hs | ⟨event,he,hroute⟩
    · by_cases hc : d.cell = 0
      · have hm : d ∈ s.pending.filter (fun d => d.cell = 0) := by
          simpa only [List.mem_filter,decide_eq_true_eq] using And.intro hs hc
        rw [hAempty] at hm
        contradiction
      · exact Or.inl hc
    · exact Or.inl (hclosedA event he d hroute)
  obtain ⟨idle⟩ := e.idle_prepared 0 ha hqa hra hnoA
  exact ⟨⟨idle,sender.sender,receiver⟩⟩

/-- Concrete B-to-C wiring discharges the absence/projection premises from
its declared destination; no receiving calendar or pulse-case word is given. -/
theorem Execution.c_introduction_active {θ ε s u} (delay : ℝ → ℝ)
    (e : @Execution 3 θ (cTeachingRouter delay) s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : PreparedSection s 0) (hqa : s.x 0 .q = 1 / 10) (hra : ∀ p, s.raw 0 p = none)
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hsb : PreparedSection s 1) (hqb : s.x 1 .q = 1 / 10)
    (hzb : 9 / 5 ≤ Real.exp (s.x 1 (.z 2)) ∧ Real.exp (s.x 1 (.z 2)) ≤ 12 / 5)
    (hrb : s.raw 1 2 = some s.time) (hob : ∀ p, p ≠ 2 → s.raw 1 p = none)
    (hBqueue : (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 488 8 15))
    (ht : s.time = 480) (hu : u.time = 6399 / 10) (hpf : PendingFuture u)
    (hsc : ReadyCoordinates s 2)
    (hbc : 7999 / 100000 ≤ s.x 2 .b ∧ s.x 2 .b ≤ 8001 / 100000)
    (hzc : Real.log (6 / 5) - 1 / 1000 ≤ s.x 2 (.z 1) ∧ s.x 2 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000)
    (hrc : ∀ p, s.raw 2 p = none)
    (hfuture : ∀ d ∈ s.pending, d.cell = 2 → 640 ≤ d.due)
    (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) :
    Nonempty (CIntroductionActivePhase e) := by
  exact e.c_introduction_active_phase hb hf hv ha hqa hra hAempty
    (fun event _ => cTeachingRouter.closed_to_a delay event.1 event.2)
    hsb hqb hzb hrb hob hBqueue (fun event _ => cTeachingRouter.closed_to_b delay event.1 event.2)
    ht hu hpf hsc hbc hzc hrc hfuture delay hdelay
    (fun event _ => cTeachingRouter.to_c delay event.1 event.2)

end KernelR.Hybrid
