import KernelR.HybridBTeachingCalendar
/-! A sixteen-input fast-gain receiver at any cell and source epoch. -/
namespace KernelR.Hybrid

private theorem ofFn_four {α} (f : ℕ → α) (count : ℕ) :
    List.ofFn (fun k : Fin (count + 4) => f k.val) =
      f 0 :: f 1 :: f 2 :: f 3 :: List.ofFn (fun k : Fin count => f (k.val + 4)) := by
  simp only [List.ofFn_succ,Fin.val_zero,Fin.val_succ]

/-- A fresh fast-gain receiver has the same physical bootstrap at any epoch.
The source latency belongs to its sender; receiver gains and fabrication
parameters remain independent. The old B-specific wrapper is unchanged. -/
theorem Execution.fast_teaching_of_calendar {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i)
    (hbrecovery : 7999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 8001 / 100000)
    (hz : Real.log (6 / 5) - 1 / 1000 ≤ s.x i (.z p) ∧ s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (hr : ∀ q, s.raw i q = none)
    (start : ℝ) (hfinish : start + 129 ≤ u.time)
    (G : ℝ) (hG : 9 / 5 ≤ G ∧ G ≤ 12 / 5)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hcalendar : e.cellDeliveries i = List.ofFn (fun k : Fin 16 =>
      ⟨i,p,start + 8 * (k.val : ℝ) + restLatency G + delay (start + 8 * (k.val : ℝ) + restLatency G)⟩)) :
    Nonempty (BTeachingPhase e i p) := by
  let date : ℕ → ℝ := fun k => start + 8 * (k : ℝ) + restLatency G + delay (start + 8 * (k : ℝ) + restLatency G)
  let tail : List ℝ := List.ofFn (fun k : Fin 12 => date (k.val + 4))
  have hdates : List.ofFn (fun k : Fin 16 => date k.val) = date 0 :: date 1 :: date 2 :: date 3 :: tail :=
    ofFn_four date 12
  have hcal : e.cellDeliveries i = (date 0 :: date 1 :: date 2 :: date 3 :: tail).map (fun t => ⟨i,p,t⟩) := by
    rw [← hdates,List.map_ofFn]
    simpa only [date,Function.comp_def] using hcalendar
  have hcal' : e.cellDeliveries i = ⟨i,p,date 0⟩ :: (date 1 :: date 2 :: date 3 :: tail).map (fun t => ⟨i,p,t⟩) := by
    simpa only [List.map_cons] using hcal
  obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal'
  obtain ⟨input⟩ := cut.resting_input hs hr
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  have invariant := advanced.physical_invariant hb hf
  have valid := advanced.raw_valid hv
  have recovery : 7999 / 100000 ≤ cut.afterArrival.x i .b ∧ cut.afterArrival.x i .b ≤ 8001 / 100000 := by
    rw [input.recovery_preserved]
    exact hbrecovery
  have gain : Real.log (6 / 5) - 1 / 1000 ≤ cut.afterArrival.x i (.z p) ∧
      cut.afterArrival.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000 := by
    rw [input.gain_preserved p]
    exact hz
  have hspace : (cut.afterArrival.time :: date 1 :: date 2 :: date 3 :: tail).Pairwise
      (fun t v => t + 15 / 2 ≤ v) := by
    rw [cut.date.2,← hdates]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hreal : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    have h₁ := (hdelay (start + 8 * (k.val : ℝ) + restLatency G)).2
    have h₂ := (hdelay (start + 8 * (l.val : ℝ) + restLatency G)).1
    dsimp [date]
    linarith
  have hupper : date 2 ≤ date 1 + 17 / 2 := by
    have h₁ := (hdelay (start + 8 * (1 : ℝ) + restLatency G)).1
    have h₂ := (hdelay (start + 8 * (2 : ℝ) + restLatency G)).2
    dsimp [date]
    norm_num at h₁ h₂ ⊢
    linarith
  have hquiet : ∀ t ∈ cut.afterArrival.time :: date 1 :: date 2 :: date 3 :: tail,
      t + 15 / 2 ≤ u.time := by
    intro t ht
    rw [cut.date.2,← hdates] at ht
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
    have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
    have hl := (restLatency_spec hG).2.1
    have hd := (hdelay (start + 8 * (k.val : ℝ) + restLatency G)).2
    dsimp [date]
    linarith
  obtain ⟨phase⟩ := cut.rest.fast_teaching_phase hb invariant valid i p input.coordinates recovery gain
    input.raw_active input.raw_other (date 1) (date 2) (date 3) tail (by simp [tail])
    cut.later hspace hupper hquiet
  have target_gain : u.x i (.z p) = s.x i (.z p) + 3 / 5 := by
    rw [phase.gain_target,input.gain_preserved p]
  have other_gain : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q) := by
    intro q hq
    rw [phase.gain_other q hq,input.gain_preserved q]
  have recovery_gain : u.x i .b = s.x i .b + 1 / 10 := by
    rw [phase.recovery_gain,input.recovery_preserved]
  have before_mark : ∀ q, cut.span.ledger.mark i q = 0 := by
    intro q
    have hquiet := cut.span.aux_ready_without_input_band i q (hs.auxiliary q).1
      (hs.auxiliary q).2.2 (hr q) (cut.no_arrivals_before q)
    exact cut.span.mark_zero_aux i q .ready (by decide) (cut.span.allStates_aux_flows i q .ready hquiet)
  refine ⟨⟨?_,?_,?_,?_,?_,target_gain,other_gain,recovery_gain,phase.prepared,phase.charge_rest,phase.raw_finished⟩⟩
  · rw [cut.emissions,input.emissions_before,List.nil_append]
    exact phase.emissions
  · have h := e.gain_balance i p
    linarith
  · intro q hq
    have h := e.gain_balance i q
    rw [other_gain q hq] at h
    linarith
  · rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct i p,before_mark p,zero_add]
    exact phase.mark_target
  · intro q hq
    rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct i q,before_mark q,zero_add]
    exact phase.mark_other q hq

end KernelR.Hybrid
