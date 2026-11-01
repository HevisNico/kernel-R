import KernelR.HybridCellDueSources
import KernelR.HybridBoundaryIdle
import KernelR.HybridSilentReturn
/-! Select source 160 after birth when it remains queued, retaining both cells. -/
namespace KernelR.Hybrid

structure TeachingActivation {θ route s u} (e : @Execution 2 θ route s u) where
  cut : CellDeliveryStep e 0 ⟨0,0,160⟩ (sourceTrain 0 0 168 8 15)
  date : cut.afterArrival.time = 160
  coordinates : cut.afterArrival.x = s.x
  preparedA : PreparedSection cut.afterArrival 0
  charge_restA : cut.afterArrival.x 0 .q = 1 / 10
  raw_activeA : cut.afterArrival.raw 0 0 = some cut.afterArrival.time
  raw_otherA : ∀ p, p ≠ 0 → cut.afterArrival.raw 0 p = none
  queueA : (cut.afterArrival.pending.filter (fun d => d.cell = 0)).Perm (sourceTrain 0 0 168 8 15)
  readyB : ReadyCoordinates cut.afterArrival 1
  rawB : ∀ p, cut.afterArrival.raw 1 p = none
  futureB : ∀ d ∈ cut.afterArrival.pending, d.cell = 1 → 320 ≤ d.due
  before_emissions : cut.span.ledger.emissions = []
  emissionsA_before : cut.span.emissionTimes 0 = []
  emissionsB_before : cut.span.emissionTimes 1 = []
  advanced_emissions : (cut.span.append (.cons (.jump cut.entry) (.nil _))).ledger.emissions = []

/-- A source due at 160 is selected from the same post-birth execution. The
prefix and arrival have no elapsed time and give no output or memory reset. -/
theorem Execution.teaching_activation {θ route s u} (e : @Execution 2 θ route s u)
    (hsA : PreparedSection s 0) (hqA : s.x 0 .q = 1 / 10) (hsB : ReadyCoordinates s 1)
    (hrA : ∀ p, s.raw 0 p = none) (hrB : ∀ p, s.raw 1 p = none)
    (ht : s.time = 160) (hu : u.time = 3199 / 10) (hf : PendingFuture u)
    (hqueue : (s.pending.filter (fun d => d.cell = 0)).Perm (sourceTrain 0 0 160 8 16))
    (hclosed : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ 0)
    (hfuture : ∀ d ∈ s.pending, d.cell = 1 → 320 ≤ d.due) : Nonempty (TeachingActivation e) := by
  have hcal : e.cellDeliveries 0 = sourceTrain 0 0 160 8 16 := by
    apply e.cell_deliveries_due_prefix_exact 0 0 (sourceTrain 0 0 160 8 16) []
      (by simpa only [List.append_nil] using hqueue) ?_ (by simp) hf hclosed ?_ ?_
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
      rw [hu]
      change 160 + 8 * (k.val : ℝ) < 3199 / 10
      linarith
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨rfl,rfl⟩
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
      change 160 + 8 * (k.val : ℝ) ≤ 160 + 8 * (l.val : ℝ)
      linarith
  have htrain : sourceTrain (0 : Fin 2) 0 160 8 16 = ⟨0,0,160⟩ :: sourceTrain 0 0 168 8 15 := by
    simpa only [show (160 : ℝ) + 8 = 168 by norm_num] using sourceTrain_succ (0 : Fin 2) 0 160 8 15
  obtain ⟨cut⟩ := e.first_cell_delivery 0 ⟨0,0,160⟩ (sourceTrain 0 0 168 8 15) (hcal.trans htrain)
  have hdate : cut.afterArrival.time = 160 := cut.date.2
  have hbefore : cut.beforeArrival.time = s.time := cut.date.1.trans ht.symm
  have hspanx : cut.beforeArrival.x = s.x := cut.span.zero_duration_continuous hbefore
  have hmainA := cut.span.zero_duration_ready_main hbefore 0 hsA.ready (by rw [hqA]; norm_num)
  have hmainB := cut.span.zero_duration_ready_main hbefore 1 hsB.ready (by linarith [hsB.charge.2])
  have hauxA : ∀ p, cut.span.AllStates (fun v => v.aux 0 p = .ready) := by
    intro p
    exact cut.span.zero_duration_ready_aux hbefore 0 p (hsA.auxiliary p).1 (by
      have h := (hsA.auxiliary p).2.2
      linarith)
  have hauxB : ∀ p, cut.span.AllStates (fun v => v.aux 1 p = .ready) := by
    intro p
    exact cut.span.zero_duration_ready_aux hbefore 1 p (hsB.auxiliary p).1 (by
      have h := (hsB.auxiliary p).2.2
      linarith)
  have hnoneA := cut.span.no_emissions_of_ready_states 0 hmainA
  have hnoneB := cut.span.no_emissions_of_ready_states 1 hmainB
  have hbeforeEm : cut.span.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event he
    have hnone : ∀ i : Fin 2, cut.span.emissionTimes i = [] := by
      intro i
      fin_cases i
      · exact hnoneA
      · exact hnoneB
    have hm : event.2 ∈ cut.span.emissionTimes event.1 := by
      apply List.mem_map.mpr
      exact ⟨event,by simp [List.mem_filter,he],rfl⟩
    rw [hnone event.1] at hm
    contradiction
  have hd : (⟨0,0,160⟩ : Delivery 2) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  have hentryEm := cut.entry.no_emissions_of_delivery _ hd
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  have hadvancedEm : advanced.ledger.emissions = [] := by
    simp only [advanced,Execution.emissions_append,Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,
      hbeforeEm,hentryEm,List.append_nil]
  have hqinit : (s.pending.filter (fun d => d.cell = 0)).Perm
      ([⟨0,0,160⟩] ++ sourceTrain 0 0 168 8 15) := by
    simpa only [List.singleton_append] using hqueue.trans (List.Perm.of_eq htrain)
  have hdelAdvanced : (advanced.cellDeliveries 0).Perm [⟨0,0,160⟩] := by
    have hh : advanced.cellDeliveries 0 = [⟨0,0,160⟩] := by
      simp only [advanced,Execution.cellDeliveries,Execution.deliveries_append,
        List.filter_append,Execution.deliveries,Move.deliveries,cut.delivery,List.append_nil]
      change cut.span.cellDeliveries 0 ++ List.filter (fun d : Delivery 2 => d.cell = 0) [⟨0,0,160⟩] = _
      rw [cut.no_earlier]
      simp
    exact List.Perm.of_eq hh
  have hqueueAfter := advanced.cell_pending_perm_of_prefix 0 [⟨0,0,160⟩] (sourceTrain 0 0 168 8 15)
    hqinit hdelAdvanced (by intro event he; rw [hadvancedEm] at he; contradiction)
  have hcoordinates : cut.afterArrival.x = s.x := cut.entry.physical_continuous.trans hspanx
  have hpreparedBefore : PreparedSection cut.beforeArrival 0 :=
    ⟨cut.span.allStates_final hmainA,by rw [hspanx]; exact hsA.charge,
      by rw [hspanx]; exact hsA.recovery,
      fun p => ⟨cut.span.allStates_final (hauxA p),by rw [hspanx]; exact (hsA.auxiliary p).2⟩⟩
  have hreadyBeforeB : ReadyCoordinates cut.beforeArrival 1 :=
    ⟨cut.span.allStates_final hmainB,by rw [hspanx]; exact hsB.charge,
      fun p => ⟨cut.span.allStates_final (hauxB p),by rw [hspanx]; exact (hsB.auxiliary p).2⟩⟩
  have hreadyAfterB : ReadyCoordinates cut.afterArrival 1 := by
    refine ⟨?_,?_,?_⟩
    · rw [cut.modes_after.1]; exact hreadyBeforeB.ready
    · rw [hcoordinates]; exact hsB.charge
    · intro p
      refine ⟨?_,?_⟩
      · rw [cut.modes_after.2]; exact (hreadyBeforeB.auxiliary p).1
      · rw [hcoordinates]; exact (hsB.auxiliary p).2
  have hfutureAfter : ∀ d ∈ cut.afterArrival.pending, d.cell = 1 → 320 ≤ d.due := by
    intro d hd hc
    rcases advanced.pending_provenance d hd with h | ⟨event,he,hroute⟩
    · exact hfuture d h hc
    · rw [hadvancedEm] at he
      contradiction
  have hnoB : ∀ p, NoArrivalAt advanced 1 p := by
    apply advanced.no_arrival_before_due 1
    · intro d hd hc
      rw [hdate]
      linarith [hfuture d hd hc]
    · intro event he
      rw [hadvancedEm] at he
      contradiction
  refine ⟨⟨cut,hdate,hcoordinates,cut.prepared hpreparedBefore,?_,cut.raw_after,?_,hqueueAfter,
    hreadyAfterB,?_,hfutureAfter,hbeforeEm,hnoneA,hnoneB,hadvancedEm⟩⟩
  · rw [hcoordinates]; exact hqA
  · intro p hp
    rw [cut.raw_other 0 p (Or.inr hp)]
    exact (cut.span.raw_absent_of_no_arrival 0 p (hrA p) (cut.no_arrivals_before p)).1
  · intro p
    exact (advanced.raw_absent_of_no_arrival 1 p (hrB p) (hnoB p)).1

end KernelR.Hybrid
