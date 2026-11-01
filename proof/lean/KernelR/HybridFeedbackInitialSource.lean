import KernelR.HybridFeedbackSender
import KernelR.HybridFeedbackCalendar
import KernelR.HybridCellDueSources
/-! Start the return epoch from its actual pending B source queue. -/
namespace KernelR.Hybrid

/-- The source at 320 and all its successors are selected from the actual B
queue. Its quiet prefix retains exact preparation and contributes no output. -/
theorem Execution.feedback_from_sources {θ ε route s u} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 1) (hq : s.x 1 .q = 1 / 10)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x 1 (.z 2) ∧
      s.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hr : ∀ p, s.raw 1 p = none)
    (later : List (Delivery 2))
    (hqueue : (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 320 8 16 ++ later))
    (hlater : ∀ d ∈ later, u.time < d.due)
    (hclosed : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ 1)
    (hu : u.time = 4599 / 10) (hpf : PendingFuture u) : Nonempty (FeedbackSender e) := by
  have hcal : e.cellDeliveries 1 = sourceTrain 1 2 320 8 16 := by
    apply e.cell_deliveries_due_prefix_exact 1 2 (sourceTrain 1 2 320 8 16) later
      hqueue ?_ hlater hpf hclosed ?_ ?_
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
      rw [hu]
      change 320 + 8 * (k.val : ℝ) < 4599 / 10
      linarith
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨rfl,rfl⟩
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
      change 320 + 8 * (k.val : ℝ) ≤ 320 + 8 * (l.val : ℝ)
      linarith
  have htrain : sourceTrain (1 : Fin 2) 2 320 8 16 = ⟨1,2,320⟩ :: sourceTrain 1 2 328 8 15 := by
    simpa only [show (320 : ℝ) + 8 = 328 by norm_num] using sourceTrain_succ (1 : Fin 2) 2 320 8 15
  obtain ⟨cut⟩ := e.first_cell_delivery 1 ⟨1,2,320⟩ (sourceTrain 1 2 328 8 15) (hcal.trans htrain)
  obtain ⟨input⟩ := cut.resting_input hs.ready_coordinates hr
  have hprep := cut.prepared_rest_input hs hq hr
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  have invariant := advanced.physical_invariant hb hf
  have valid := advanced.raw_valid hv
  have hznext : Real.log (3 / 10) - 1 / 100000 ≤ cut.afterArrival.x 1 (.z 2) ∧
      cut.afterArrival.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [input.gain_preserved 2]
    exact hz
  obtain ⟨sender⟩ := cut.rest.feedback_sender hb invariant valid hprep.1 (by rw [hprep.2]) hznext
    input.raw_active input.raw_other cut.date.2 hu cut.later
  have hgain : u.x 1 (.z 2) = s.x 1 (.z 2) + 9 / 5 := by
    rw [sender.learning.gain_target,input.gain_preserved 2]
  have hother : ∀ p, p ≠ 2 → u.x 1 (.z p) = s.x 1 (.z p) := by
    intro p hp
    rw [sender.learning.gain_other p hp,input.gain_preserved p]
  have hrec : u.x 1 .b = s.x 1 .b := by
    rw [sender.learning.recovery_preserved,input.recovery_preserved]
  have hmark : ∀ p, cut.span.ledger.mark 1 p = 0 := by
    intro p
    have hm := cut.span.aux_ready_without_input_band 1 p (hs.auxiliary p).1
      (hs.auxiliary p).2.2 (hr p) (cut.no_arrivals_before p)
    exact cut.span.mark_zero_aux 1 p .ready (by decide) (cut.span.allStates_aux_flows 1 p .ready hm)
  refine ⟨⟨⟨?_,?_,?_,?_,hgain,hother,hrec,sender.learning.prepared,
    sender.learning.charge_rest,sender.learning.raw_finished⟩,sender.first,sender.first_lower,sender.first_upper,?_,?_⟩⟩
  · rw [cut.emissions,input.emissions_before,List.nil_append]
    exact sender.learning.emissions
  · have h := e.gain_balance 1 2
    linarith
  · intro p hp
    have h := e.gain_balance 1 p
    rw [hother p hp] at h
    linarith
  · intro p
    rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 1 p,hmark p,zero_add]
    exact sender.learning.mark_zero p
  · simpa only [input.gain_preserved 2] using sender.first_le_rest
  · rw [cut.emissions,input.emissions_before,List.nil_append,sender.emissions,input.gain_preserved 2]

end KernelR.Hybrid
