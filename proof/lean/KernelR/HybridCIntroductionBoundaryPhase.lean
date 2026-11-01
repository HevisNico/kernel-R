import KernelR.HybridCIntroductionActivePhase
import KernelR.HybridSourceActivation
import KernelR.HybridTeachingBoundaryPhase
/-! Both legal source/birth orders at C's introduction. -/
namespace KernelR.Hybrid

theorem Execution.c_introduction_boundary_phase {θ ε s u} (delay : ℝ → ℝ)
    (e : @Execution 3 θ (cTeachingRouter delay) s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : PreparedSection s 0) (hqa : s.x 0 .q = 1 / 10) (hra : ∀ p, s.raw 0 p = none)
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hsb : PreparedSection s 1) (hqb : s.x 1 .q = 1 / 10)
    (hzb : 9 / 5 ≤ Real.exp (s.x 1 (.z 2)) ∧ Real.exp (s.x 1 (.z 2)) ≤ 12 / 5)
    (hboundary :
      (s.raw 1 2 = none ∧ (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 480 8 16)) ∨
      (s.raw 1 2 = some s.time ∧ (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 488 8 15)))
    (hob : ∀ p, p ≠ 2 → s.raw 1 p = none)
    (ht : s.time = 480) (hu : u.time = 6399 / 10) (hpf : PendingFuture u)
    (hsc : ReadyCoordinates s 2)
    (hbc : 7999 / 100000 ≤ s.x 2 .b ∧ s.x 2 .b ≤ 8001 / 100000)
    (hzc : Real.log (6 / 5) - 1 / 1000 ≤ s.x 2 (.z 1) ∧ s.x 2 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000)
    (hrc : ∀ p, s.raw 2 p = none)
    (hfuture : ∀ d ∈ s.pending, d.cell = 2 → 640 ≤ d.due)
    (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) :
    Nonempty (CIntroductionActivePhase e) := by
  rcases hboundary with ⟨hnone,hqueue⟩ | ⟨hactive,hqueue⟩
  · have hrB : ∀ p, s.raw 1 p = none := by
      intro p
      by_cases hp : p = 2
      · subst p; exact hnone
      · exact hob p hp
    have hcal : e.cellDeliveries 1 = sourceTrain 1 2 480 8 16 := by
      apply e.cell_deliveries_due_prefix_exact 1 2 (sourceTrain 1 2 480 8 16) []
        (by simpa only [List.append_nil] using hqueue) ?_ (by simp) hpf
        (fun event _ => cTeachingRouter.closed_to_b delay event.1 event.2) ?_ ?_
      · intro d hd
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
        have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
        rw [hu]
        change 480 + 8 * (k.val : ℝ) < 6399 / 10
        linarith
      · intro d hd
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
        exact ⟨rfl,rfl⟩
      · apply List.pairwise_ofFn.mpr
        intro k l hkl
        have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
        change 480 + 8 * (k.val : ℝ) ≤ 480 + 8 * (l.val : ℝ)
        linarith
    have htrain : sourceTrain (1 : Fin 3) 2 480 8 16 = ⟨1,2,480⟩ :: sourceTrain 1 2 488 8 15 := by
      simpa only [show (480 : ℝ) + 8 = 488 by norm_num] using sourceTrain_succ (1 : Fin 3) 2 480 8 15
    obtain ⟨cut⟩ := e.first_cell_delivery 1 ⟨1,2,480⟩ (sourceTrain 1 2 488 8 15) (hcal.trans htrain)
    have hready : ∀ k, ReadyCoordinates s k := by
      intro k
      fin_cases k
      · exact ha.ready_coordinates
      · exact hsb.ready_coordinates
      · exact hsc
    have hraw : ∀ k p, s.raw k p = none := by
      intro k p
      fin_cases k
      · exact hra p
      · exact hrB p
      · exact hrc p
    have hotherFuture : ∀ d ∈ s.pending, d.cell ≠ 1 → (480 : ℝ) < d.due := by
      intro d hd hn
      have hc : d.cell = 0 ∨ d.cell = 2 := by have h := d.cell.isLt; omega
      rcases hc with hc | hc
      · have hm : d ∈ s.pending.filter (fun d => d.cell = 0) := by
          simp only [List.mem_filter,decide_eq_true_eq]
          exact ⟨hd,hc⟩
        rw [hAempty] at hm
        contradiction
      · linarith [hfuture d hd hc]
    obtain ⟨act⟩ := cut.source_activation hready hraw ht hotherFuture
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have invariant := advanced.physical_invariant hb hf
    have valid := advanced.raw_valid hv
    obtain ⟨phase⟩ := cut.rest.c_introduction_active delay hb invariant valid
      (act.prepared 0 ha) (by rw [act.coordinates]; exact hqa)
      (fun p => act.raw_other 0 p (Or.inl (by decide))) (act.empty 0 hAempty)
      (act.prepared 1 hsb) (by rw [act.coordinates]; exact hqb)
      (by rw [act.coordinates]; exact hzb) act.raw_active (fun p hp => act.raw_other 1 p (Or.inr hp))
      (act.pending (hqueue.trans (List.Perm.of_eq htrain))) cut.date.2 hu hpf (act.ready 2)
      (by rw [act.coordinates]; exact hbc) (by rw [act.coordinates]; exact hzc)
      (fun p => act.raw_other 2 p (Or.inl (by decide))) (act.future 2 640 hfuture) hdelay
    have span_time : cut.beforeArrival.time = s.time := cut.date.1.trans ht.symm
    have span_mark : ∀ i p, cut.span.ledger.mark i p = 0 :=
      fun i p => cut.span.zero_duration_mark span_time i p
    have span_emissions : ∀ i, cut.span.emissionTimes i = [] := by
      intro i
      simp only [Execution.emissionTimes,act.before_emissions,List.filter_nil,List.map_nil]
    have gainB : ∀ p, u.x 1 (.z p) = s.x 1 (.z p) := by
      intro p
      rw [phase.b_train.gain_preserved p,act.coordinates]
    have gainC : u.x 2 (.z 1) = s.x 2 (.z 1) + 3 / 5 := by
      rw [phase.c_phase.gain_target,act.coordinates]
    have otherC : ∀ p, p ≠ 1 → u.x 2 (.z p) = s.x 2 (.z p) := by
      intro p hp
      rw [phase.c_phase.gain_other p hp,act.coordinates]
    refine ⟨⟨⟨phase.a_idle.prepared,phase.a_idle.charge_rest,?_,?_,?_⟩,
      ⟨?_,?_,?_,gainB,?_,phase.b_train.prepared,phase.b_train.charge_rest,phase.b_train.raw_finished⟩,
      ⟨?_,?_,?_,?_,?_,gainC,otherC,?_,phase.c_phase.prepared,phase.c_phase.charge_rest,
        phase.c_phase.raw_finished⟩⟩⟩
    · intro p; rw [phase.a_idle.gain_preserved p,act.coordinates]
    · rw [phase.a_idle.recovery_preserved,act.coordinates]
    · rw [cut.emissions_at 0,span_emissions 0,List.nil_append]; exact phase.a_idle.emissions
    · rw [cut.emissions,span_emissions 1,List.nil_append]; exact phase.b_train.emissions
    · intro p
      have h := e.gain_balance 1 p
      rw [gainB p] at h
      linarith
    · intro p
      rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 1 p,span_mark 1 p,zero_add]
      exact phase.b_train.mark_zero p
    · rw [phase.b_train.recovery_preserved,act.coordinates]
    · rw [cut.emissions_at 2,span_emissions 2,List.nil_append]; exact phase.c_phase.emissions
    · have h := e.gain_balance 2 1
      linarith
    · intro p hp
      have h := e.gain_balance 2 p
      rw [otherC p hp] at h
      linarith
    · rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 2 1,span_mark 2 1,zero_add]
      exact phase.c_phase.mark_target
    · intro p hp
      rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 2 p,span_mark 2 p,zero_add]
      exact phase.c_phase.mark_other p hp
    · rw [phase.c_phase.recovery_gain,act.coordinates]
  · exact e.c_introduction_active delay hb hf hv ha hqa hra hAempty hsb hqb hzb hactive hob
      hqueue ht hu hpf hsc hbc hzc hrc hfuture hdelay

end KernelR.Hybrid
