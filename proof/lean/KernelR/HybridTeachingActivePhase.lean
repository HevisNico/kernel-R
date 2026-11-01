import KernelR.HybridPreparedContact
import KernelR.HybridBTeachingCalendar
/-! The actual A-to-B teaching epoch once A's source at 160 is active. -/
namespace KernelR.Hybrid

structure TeachingActivePhase {θ route s u} (e : @Execution 2 θ route s u) where
  a_train : PreparedTrain e 0 16
  b_phase : BTeachingPhase e 1 1

/-- Both source and wire calendars are derived from the actual queues and
routing. The initial active A pulse is preserved, and no output count or
pulse-case word is supplied. -/
theorem Execution.teaching_active_phase {θ ε route s u} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : PreparedSection s 0) (hqa : s.x 0 .q = 1 / 10)
    (hza : 9 / 5 ≤ Real.exp (s.x 0 (.z 0)) ∧ Real.exp (s.x 0 (.z 0)) ≤ 12 / 5)
    (hra : s.raw 0 0 = some s.time) (hoa : ∀ q, q ≠ 0 → s.raw 0 q = none)
    (hqueue : (s.pending.filter (fun d => d.cell = 0)).Perm (sourceTrain 0 0 168 8 15))
    (hclosed : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ 0)
    (ht : s.time = 160) (hu : u.time = 3199 / 10) (hpf : PendingFuture u)
    (hsb : ReadyCoordinates s 1)
    (hbb : 7999 / 100000 ≤ s.x 1 .b ∧ s.x 1 .b ≤ 8001 / 100000)
    (hzb : Real.log (6 / 5) - 1 / 1000 ≤ s.x 1 (.z 1) ∧ s.x 1 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000)
    (hrb : ∀ q, s.raw 1 q = none)
    (hfuture : ∀ d ∈ s.pending, d.cell = 1 → 320 ≤ d.due)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = 1) = (teachingContact delay).route event.1 event.2) :
    Nonempty (TeachingActivePhase e) := by
  have hcal : e.cellDeliveries 0 = sourceTrain 0 0 168 8 15 := by
    apply e.cell_deliveries_due_prefix_exact 0 0 (sourceTrain 0 0 168 8 15) []
      (by simpa only [List.append_nil] using hqueue) ?_ (by simp) hpf hclosed ?_ ?_
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      have hk : (k.val : ℝ) ≤ 14 := by exact_mod_cast (show k.val ≤ 14 by omega)
      rw [hu]
      change 168 + 8 * (k.val : ℝ) < 3199 / 10
      linarith
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨rfl,rfl⟩
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
      change 168 + 8 * (k.val : ℝ) ≤ 168 + 8 * (l.val : ℝ)
      linarith
  let times : List ℝ := List.ofFn (fun k : Fin 15 => (168 : ℝ) + 8 * (k.val : ℝ))
  have htimes : (160 : ℝ) :: times = List.ofFn (fun k : Fin 16 => (160 : ℝ) + 8 * (k.val : ℝ)) := by
    have h := congrArg (List.map Delivery.due) (sourceTrain_succ (0 : Fin 2) 0 160 8 15)
    simpa only [sourceTrain,times,List.map_ofFn,Function.comp_def,List.map_cons,
      show (160 : ℝ) + 8 = 168 by norm_num] using h.symm
  have hcal' : e.cellDeliveries 0 = times.map (fun t => ⟨0,0,t⟩) := by
    simpa only [times,sourceTrain,List.map_ofFn,Function.comp_def] using hcal
  have hspace : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
    rw [ht,htimes]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    linarith
  have hquiet : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time := by
    intro t hm
    rw [ht,htimes] at hm
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hm
    have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
    rw [hu]
    linarith
  obtain ⟨train⟩ := prepared_cell_train_of_valid hb 0 0 times e hf.region hv ha hza hra hoa
    hcal' hspace hquiet
  have hwireCal := e.teaching_contact_sources hb hf.region hv ha hqa hza hra hoa hqueue hclosed
    ht hu hpf hfuture delay hdelay hwire
  obtain ⟨phase⟩ := e.b_teaching_of_calendar hb hf hv hsb hbb hzb hrb hu
    (Real.exp (s.x 0 (.z 0))) hza delay hdelay hwireCal
  refine ⟨⟨?_,phase⟩⟩
  simpa only [times,List.length_ofFn] using train

end KernelR.Hybrid
