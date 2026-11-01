import KernelR.HybridEntryRouter
import KernelR.HybridFeedbackCalendar
import KernelR.HybridRestingInput
/-! The actual period-four source and two forward contacts of the cadence epoch. -/
namespace KernelR.Hybrid

def cadenceForwardContact (delay : ℝ → ℝ) : Contact 3 := ⟨2,1,2,640,780,delay⟩
def cadenceReturnContact (delay : ℝ → ℝ) : Contact 3 := ⟨1,0,2,640,780,delay⟩

/-- Each emission uses its own delay function on its own wire. -/
noncomputable def cadenceRouter (forward backward : ℝ → ℝ) : Router 3 := fun i t =>
  (cadenceForwardContact forward).route i t ++ (cadenceReturnContact backward).route i t

theorem cadenceRouter.causal (forward backward : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ forward t) (hb : ∀ t, 0 ≤ backward t) :
    CausalRouter (cadenceRouter forward backward) := by
  intro i t d hd
  rcases List.mem_append.mp hd with h | h
  · exact (cadenceForwardContact forward).causal hf i t d h
  · exact (cadenceReturnContact backward).causal hb i t d h

/-- The source cells of the two contacts differ, so a firing issues at most
one routed pulse even though both contacts are open during the same epoch. -/
theorem cadenceRouter.fanout (forward backward : ℝ → ℝ) :
    FanoutBound (cadenceRouter forward backward) 1 := by
  classical
  intro i t
  fin_cases i <;>
    simp [cadenceRouter,cadenceForwardContact,cadenceReturnContact,Contact.route]
  all_goals split_ifs <;> simp

theorem cadenceRouter.closed_to_c (forward backward : ℝ → ℝ) (i : Fin 3) (t : ℝ) :
    ∀ d ∈ cadenceRouter forward backward i t, d.cell ≠ 2 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · have hc : d.cell = (1 : Fin 3) := (cadenceForwardContact forward).route_target hd
    rw [hc]
    decide
  · have hc : d.cell = (0 : Fin 3) := (cadenceReturnContact backward).route_target hd
    rw [hc]
    decide

/-- No input from A or B can be hidden in the projection received by B. -/
theorem cadenceRouter.to_b (forward backward : ℝ → ℝ) (i : Fin 3) (t : ℝ) :
    (cadenceRouter forward backward i t).filter (fun d => d.cell = 1) =
      (cadenceForwardContact forward).route i t := by
  classical
  have hreturn : ((cadenceReturnContact backward).route i t).filter (fun d => d.cell = 1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    have hc : d.cell = (0 : Fin 3) := (cadenceReturnContact backward).route_target hd
    simp only [decide_eq_true_eq]
    rw [hc]
    decide
  rw [cadenceRouter,List.filter_append,hreturn,List.append_nil]
  exact (cadenceForwardContact forward).filter_target i t

/-- The only routed inputs of A are actual B emissions on the return contact. -/
theorem cadenceRouter.to_a (forward backward : ℝ → ℝ) (i : Fin 3) (t : ℝ) :
    (cadenceRouter forward backward i t).filter (fun d => d.cell = 0) =
      (cadenceReturnContact backward).route i t := by
  classical
  have hforward : ((cadenceForwardContact forward).route i t).filter (fun d => d.cell = 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    have hc : d.cell = (1 : Fin 3) := (cadenceForwardContact forward).route_target hd
    simp only [decide_eq_true_eq]
    rw [hc]
    decide
  rw [cadenceRouter,List.filter_append,hforward,List.nil_append]
  exact (cadenceReturnContact backward).filter_target i t

theorem cadenceRouter.before_open (forward backward : ℝ → ℝ) (i : Fin 3)
    {t : ℝ} (ht : t < 640) : cadenceRouter forward backward i t = [] := by
  classical
  have hforward : (cadenceForwardContact forward).route i t = [] := by
    unfold Contact.route
    split_ifs with h
    · have hg : (640 : ℝ) ≤ t := h.2.1
      linarith
    · rfl
  have hbackward : (cadenceReturnContact backward).route i t = [] := by
    unfold Contact.route
    split_ifs with h
    · have hg : (640 : ℝ) ≤ t := h.2.1
      linarith
    · rfl
  simp only [cadenceRouter,hforward,hbackward,List.nil_append]

theorem cadenceRouter.after_close (forward backward : ℝ → ℝ) (i : Fin 3)
    {t : ℝ} (ht : 780 ≤ t) : cadenceRouter forward backward i t = [] := by
  classical
  have hforward : (cadenceForwardContact forward).route i t = [] := by
    unfold Contact.route
    split_ifs with h
    · have hg : t < (780 : ℝ) := h.2.2
      linarith
    · rfl
  have hbackward : (cadenceReturnContact backward).route i t = [] := by
    unfold Contact.route
    split_ifs with h
    · have hg : t < (780 : ℝ) := h.2.2
      linarith
    · rfl
  simp only [cadenceRouter,hforward,hbackward,List.nil_append]

/-- C's twenty-five sources are derived from its actual initial queue. The
routing projections, all events at A/B and their queued tokens are retained. -/
theorem Execution.cadence_source_calendar {θ s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u)
    (hqueue : (s.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 25))
    (hu : u.time = 7899 / 10) (hf : PendingFuture u) :
    e.cellDeliveries 2 = sourceTrain 2 0 640 4 25 := by
  apply e.cell_deliveries_due_prefix_exact 2 0 (sourceTrain 2 0 640 4 25) []
    (by simpa only [List.append_nil] using hqueue) ?_ (by simp) hf
    (fun event _ => cadenceRouter.closed_to_c forward backward event.1 event.2) ?_ ?_
  · intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (k.val : ℝ) ≤ 24 := by exact_mod_cast (show k.val ≤ 24 by omega)
    rw [hu]
    change 640 + 4 * (k.val : ℝ) < 7899 / 10
    linarith
  · intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    exact ⟨rfl,rfl⟩
  · apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
    change 640 + 4 * (k.val : ℝ) ≤ 640 + 4 * (l.val : ℝ)
    linarith

theorem Execution.cadence_source_calendar_of_causal {θ s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u)
    (hqueue : (s.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 25))
    (hu : u.time = 7899 / 10) (hf : PendingFuture s)
    (hforward : ∀ t, 0 ≤ forward t) (hbackward : ∀ t, 0 ≤ backward t) :
    e.cellDeliveries 2 = sourceTrain 2 0 640 4 25 :=
  e.cadence_source_calendar forward backward hqueue hu
    (e.pending_future (cadenceRouter.causal forward backward hforward hbackward) hf)

/-- The actual first C input after its quiet wait, with all other-cell events
retained in the cut and every succeeding source retained in the remaining trace. -/
structure CadenceSourceActivation {θ route s u} (e : @Execution 3 θ route s u) where
  cut : CellDeliveryStep e 2 ⟨2,0,640⟩ (sourceTrain 2 0 644 4 24)
  input : RestingCellInput cut
  prepared : PreparedSection cut.afterArrival 2
  charge_rest : cut.afterArrival.x 2 .q = 1 / 10
  physical : PhysicalInvariant θ cut.afterArrival
  raw_valid : RawValid cut.afterArrival

/-- Neither an input case word nor an output calendar is required to activate
C's first pulse. Its READY preparation and exact resting charge survive the
quiet prefix from the supplied initial state to the actual source at 640. -/
theorem Execution.cadence_source_activation {θ ε s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 2) (hq : s.x 2 .q = 1 / 10) (hr : ∀ p, s.raw 2 p = none)
    (hqueue : (s.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 25))
    (hu : u.time = 7899 / 10) (hpf : PendingFuture u) :
    Nonempty (CadenceSourceActivation e) := by
  have hcal := e.cadence_source_calendar forward backward hqueue hu hpf
  have htrain : sourceTrain (2 : Fin 3) 0 640 4 25 = ⟨2,0,640⟩ :: sourceTrain 2 0 644 4 24 := by
    simpa only [show (640 : ℝ) + 4 = 644 by norm_num] using sourceTrain_succ (2 : Fin 3) 0 640 4 24
  obtain ⟨cut⟩ := e.first_cell_delivery 2 ⟨2,0,640⟩ (sourceTrain 2 0 644 4 24) (hcal.trans htrain)
  obtain ⟨input⟩ := cut.resting_input hs.ready_coordinates hr
  have hprep := cut.prepared_rest_input hs hq hr
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  exact ⟨⟨cut,input,hprep.1,hprep.2,advanced.physical_invariant hb hf,advanced.raw_valid hv⟩⟩

end KernelR.Hybrid
