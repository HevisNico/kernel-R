import KernelR.HybridCadenceBPhase
/-! The actual B return wire selects A's four sparse and subsequent dense
physical cases, with A's own independent gains and recovery memories. -/
namespace KernelR.Hybrid

/-- A constant auxiliary return delay transfers the proved receiving geometry
back to B's output spacing, without assuming an output separation certificate. -/
theorem cadenceB_output_spacing {v : CadenceReturnLatencies} (hv : CadenceReturnLatencyBounds v)
    {forward : ℝ → ℝ} (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5) :
    (List.ofFn (fun j : Fin 18 => cadenceBOutputDate v forward j.val)).Pairwise
      (fun t u => t + 1 / 10 ≤ u) := by
  have hb : ∀ t : ℝ, 3 / 10 ≤ (fun _ : ℝ => (3 / 10 : ℝ)) t ∧
      (fun _ : ℝ => (3 / 10 : ℝ)) t ≤ 2 / 5 := by intro t; norm_num
  have hstep : ∀ j : ℕ, j < 17 → cadenceBOutputDate v forward j + 1 / 10 ≤ cadenceBOutputDate v forward (j + 1) := by
    intro j hj
    by_cases hlo : j < 4
    · have h := cadenceA_sparse_spacing hv hforward hb (i := j) (j := j + 1) (by omega) (by omega)
      dsimp only [cadenceAInputDate] at h
      linarith
    · by_cases he : j = 4
      · subst j
        have h := (cadenceA_first_strong_gap hv hforward hb).1
        dsimp only [cadenceAInputDate] at h
        linarith
      · have h := (cadenceA_rest_pair_gap (v := v) hforward hb (j - 5)).1
        rw [show j - 5 + 5 = j by omega,show j - 5 + 6 = j + 1 by omega] at h
        dsimp only [cadenceAInputDate] at h
        linarith
  have hmono : ∀ j : ℕ, j < 18 → ∀ i : ℕ, i ≤ j →
      cadenceBOutputDate v forward i ≤ cadenceBOutputDate v forward j := by
    intro j
    induction j with
    | zero =>
      intro hj i hi
      have he : i = 0 := by omega
      subst i
      exact le_rfl
    | succ j ih =>
      intro hj i hi
      by_cases he : i = j + 1
      · subst i; exact le_rfl
      · have h := hstep j (by omega)
        exact (ih (by omega) i (by omega)).trans (by linarith)
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact (hstep i.val (by omega)).trans (hmono j.val j.isLt (i.val + 1) (by omega))

/-- All eighteen actual B output dates are inside the physical return gate. -/
theorem cadenceB_output_gate {v : CadenceReturnLatencies} (hv : CadenceReturnLatencyBounds v)
    (hfirst : 3 / 10 < v.firstLowC) {forward : ℝ → ℝ}
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5) :
    ∀ t ∈ List.ofFn (fun j : Fin 18 => cadenceBOutputDate v forward j.val), 640 ≤ t ∧ t < 780 := by
  intro t ht
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
  rcases j with ⟨j,hj⟩
  have hd := hforward (cadenceCOutputDate v (cadenceBOutputSourceIndex j))
  change 640 ≤ cadenceBOutputDate v forward j ∧ cadenceBOutputDate v forward j < 780
  dsimp only [cadenceBOutputDate,cadenceBInputDate]
  interval_cases j <;>
    norm_num [cadenceCOutputDate,cadenceBOutputSourceIndex,cadenceBOutputLatency] at hd ⊢
  all_goals constructor <;> linarith [hv.firstLow_le,hv.lowC_lower,hv.lowC_upper,
    hv.firstHighC_lower,hv.firstHighC_le,hv.highC_upper,hv.lowB_lower,hv.lowB_upper,
    hv.firstHighB_lower,hv.firstHighB_le,hv.highB_upper]

structure CadenceAPhase {θ forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} {ccal : CadenceCCalendar cphase}
    (phaseB : CadenceBPhase ccal) where
  input_calendar : e.cellDeliveries 0 =
    (cadenceAInputCalendar phaseB.returnLatencies forward backward).map (fun t => ⟨0,2,t⟩)
  preA : CadenceSparsePrefix e 0 2 (cadenceASparseCalendar phaseB.returnLatencies forward backward)
    (cadenceAInputDate phaseB.returnLatencies forward backward 4)
    ((cadenceAInputDate phaseB.returnLatencies forward backward 5 ::
      cadenceAInputDate phaseB.returnLatencies forward backward 6 ::
      cadenceAInputDate phaseB.returnLatencies forward backward 7 ::
      cadenceAInputDate phaseB.returnLatencies forward backward 8 ::
      cadenceAHighTail phaseB.returnLatencies forward backward).map (fun t => ⟨0,2,t⟩))
  relay : CadenceRelayPhase preA
  calendar : CadenceRelayCalendar relay

theorem CadenceAPhase.emission_count {θ forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} {ccal : CadenceCCalendar cphase}
    {phaseB : CadenceBPhase ccal} (phase : CadenceAPhase phaseB) :
    (e.emissionTimes 0).length = 16 := by
  simpa [cadenceASparseCalendar,cadenceAHighTail] using phase.relay.emissions

/-- The entire A incoming list is derived from B's already proved actual
outputs and the return contact; no A output calendar, count or dose is supplied. -/
theorem CadenceBPhase.a_phase {θ ε forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} {ccal : CadenceCCalendar cphase}
    (phaseB : CadenceBPhase ccal)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 0) (hq : s.x 0 .q = 1 / 10) (hr : ∀ p, s.raw 0 p = none)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z 2) ∧
      s.x 0 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hqueue : s.pending.filter (fun d => d.cell = 0) = [])
    (hu : u.time = 7899 / 10) (hpf : PendingFuture u)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (CadenceAPhase phaseB) := by
  let v := phaseB.returnLatencies
  have bounds := phaseB.returnBounds
  have geometry := cadence_return_geometry bounds hforward hbackward
  have hfirst : 3 / 10 < v.firstLowC := ccal.firstLow_lower
  have hwire := e.cadence_return_calendar forward backward
    (List.ofFn (fun j : Fin 18 => cadenceBOutputDate v forward j.val))
    phaseB.b_emission_calendar (cadenceB_output_spacing bounds hforward)
    (cadenceB_output_gate bounds hfirst hforward) hu hpf hqueue hbackward
  have hcalendar : e.cellDeliveries 0 =
      (cadenceAInputCalendar v forward backward).map (fun t => ⟨0,2,t⟩) := by
    rw [hwire]
    simp only [cadenceAInputCalendar,List.map_ofFn,Function.comp_def,
      cadenceReturnContact,Contact.token,cadenceAInputDate]
  have hcalendar' : e.cellDeliveries 0 =
      (cadenceASparseCalendar v forward backward).map (fun t => ⟨0,2,t⟩) ++
        ⟨0,2,cadenceAInputDate v forward backward 4⟩ ::
        ((cadenceAInputDate v forward backward 5 :: cadenceAInputDate v forward backward 6 ::
          cadenceAInputDate v forward backward 7 :: cadenceAInputDate v forward backward 8 ::
          cadenceAHighTail v forward backward).map (fun t => ⟨0,2,t⟩)) := by
    rw [hcalendar,cadenceAInputCalendar_decomposition]
    simp only [List.map_append,List.map_cons,List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨preA⟩ := e.cadence_sparse_prefix hb hf hv 0 2 (cadenceASparseCalendar v forward backward)
    (cadenceAInputDate v forward backward 4)
    ((cadenceAInputDate v forward backward 5 :: cadenceAInputDate v forward backward 6 ::
      cadenceAInputDate v forward backward 7 :: cadenceAInputDate v forward backward 8 ::
      cadenceAHighTail v forward backward).map (fun t => ⟨0,2,t⟩))
    hs hq hz hr hcalendar' geometry.sparse_calendar_spacing
  have hgap1 := geometry.first_strong_gap
  have hgap2 := geometry.rest_gaps 0
  have hgap3 := geometry.rest_gaps 1
  have hgap4 := geometry.rest_gaps 2
  norm_num only [Nat.reduceAdd] at hgap2 hgap3 hgap4
  have hquiet : ∀ t ∈ cadenceAInputDate v forward backward 8 :: cadenceAHighTail v forward backward,
      t + 19 / 5 ≤ u.time := by
    intro t ht
    rw [hu]
    apply geometry.calendar_quiet t
    rw [cadenceAInputCalendar_decomposition]
    rcases List.mem_cons.mp ht with heq | ht
    · subst t
      exact List.mem_append_left _ (List.mem_append_right _ (by simp [v]))
    · exact List.mem_append_right _ ht
  obtain ⟨relay⟩ := preA.relay_phase hb hf hv hz
    ⟨hgap1.1,by linarith [hgap1.2]⟩ hgap2 hgap3 hgap4 geometry.high_calendar_spacing hquiet
  obtain ⟨calendar⟩ := relay.output_calendar hb hf hv hz hgap1.1 hgap3.1 geometry.high_calendar_spacing hquiet
  exact ⟨⟨hcalendar,preA,relay,calendar⟩⟩

end KernelR.Hybrid
