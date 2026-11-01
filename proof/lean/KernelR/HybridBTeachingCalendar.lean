import KernelR.HybridPreparedContact
import KernelR.HybridRestingInput
import KernelR.HybridBTeachingPhase
/-! The complete B teaching phase from its actual jittered receiving calendar. -/
namespace KernelR.Hybrid

private theorem ofFn_four {α} (f : ℕ → α) (count : ℕ) :
    List.ofFn (fun k : Fin (count + 4) => f k.val) =
      f 0 :: f 1 :: f 2 :: f 3 :: List.ofFn (fun k : Fin count => f (k.val + 4)) := by
  simp only [List.ofFn_succ,Fin.val_zero,Fin.val_succ]

/-- The receiving calendar below is the actual A-to-B wire calendar. The B
proof retains its quiet pre-input prefix and all other-cell events. -/
theorem Execution.b_teaching_of_calendar {θ ε route s u} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : ReadyCoordinates s 1)
    (hbrecovery : 7999 / 100000 ≤ s.x 1 .b ∧ s.x 1 .b ≤ 8001 / 100000)
    (hz : Real.log (6 / 5) - 1 / 1000 ≤ s.x 1 (.z 1) ∧ s.x 1 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000)
    (hr : ∀ p, s.raw 1 p = none) (hu : u.time = 3199 / 10)
    (G : ℝ) (hG : 9 / 5 ≤ G ∧ G ≤ 12 / 5)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hcalendar : e.cellDeliveries 1 = List.ofFn (fun k : Fin 16 =>
      (teachingContact delay).token (160 + 8 * k.val + restLatency G))) :
    Nonempty (BTeachingPhase e 1 1) := by
  let date : ℕ → ℝ := fun k => 160 + 8 * (k : ℝ) + restLatency G + delay (160 + 8 * (k : ℝ) + restLatency G)
  let tail : List ℝ := List.ofFn (fun k : Fin 12 => date (k.val + 4))
  have hdates : List.ofFn (fun k : Fin 16 => date k.val) = date 0 :: date 1 :: date 2 :: date 3 :: tail :=
    ofFn_four date 12
  have hcal : e.cellDeliveries 1 = (date 0 :: date 1 :: date 2 :: date 3 :: tail).map (fun t => ⟨1,1,t⟩) := by
    rw [← hdates,List.map_ofFn]
    simpa only [Contact.token,teachingContact,date,Function.comp_def] using hcalendar
  have hcal' : e.cellDeliveries 1 = ⟨1,1,date 0⟩ :: (date 1 :: date 2 :: date 3 :: tail).map (fun t => ⟨1,1,t⟩) := by
    simpa only [List.map_cons] using hcal
  obtain ⟨cut⟩ := e.first_cell_delivery 1 _ _ hcal'
  obtain ⟨input⟩ := cut.resting_input hs hr
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  have invariant := advanced.physical_invariant hb hf
  have valid := advanced.raw_valid hv
  have recovery : 7999 / 100000 ≤ cut.afterArrival.x 1 .b ∧ cut.afterArrival.x 1 .b ≤ 8001 / 100000 := by
    rw [input.recovery_preserved]
    exact hbrecovery
  have gain : Real.log (6 / 5) - 1 / 1000 ≤ cut.afterArrival.x 1 (.z 1) ∧
      cut.afterArrival.x 1 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000 := by
    rw [input.gain_preserved 1]
    exact hz
  have hspace : (cut.afterArrival.time :: date 1 :: date 2 :: date 3 :: tail).Pairwise
      (fun t v => t + 15 / 2 ≤ v) := by
    rw [cut.date.2,← hdates]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hreal : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    have h₁ := (hdelay (160 + 8 * (k.val : ℝ) + restLatency G)).2
    have h₂ := (hdelay (160 + 8 * (l.val : ℝ) + restLatency G)).1
    dsimp [date]
    linarith
  have hupper : date 2 ≤ date 1 + 17 / 2 := by
    have h₁ := (hdelay (160 + 8 * (1 : ℝ) + restLatency G)).1
    have h₂ := (hdelay (160 + 8 * (2 : ℝ) + restLatency G)).2
    dsimp [date]
    norm_num at h₁ h₂ ⊢
    linarith
  have hquiet : ∀ t ∈ cut.afterArrival.time :: date 1 :: date 2 :: date 3 :: tail,
      t + 15 / 2 ≤ u.time := by
    intro t ht
    rw [cut.date.2,← hdates] at ht
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
    have hbound := (teachingContact.date_bounds hG delay hdelay k).2
    change date k.val < 2813 / 10 at hbound
    rw [hu]
    linarith
  obtain ⟨phase⟩ := cut.rest.fast_teaching_phase hb invariant valid 1 1 input.coordinates recovery gain
    input.raw_active input.raw_other (date 1) (date 2) (date 3) tail (by simp [tail])
    cut.later hspace hupper hquiet
  have target_gain : u.x 1 (.z 1) = s.x 1 (.z 1) + 3 / 5 := by
    rw [phase.gain_target,input.gain_preserved 1]
  have other_gain : ∀ q, q ≠ 1 → u.x 1 (.z q) = s.x 1 (.z q) := by
    intro q hq
    rw [phase.gain_other q hq,input.gain_preserved q]
  have recovery_gain : u.x 1 .b = s.x 1 .b + 1 / 10 := by
    rw [phase.recovery_gain,input.recovery_preserved]
  have before_mark : ∀ p, cut.span.ledger.mark 1 p = 0 := by
    intro p
    have hquiet := cut.span.aux_ready_without_input_band 1 p (hs.auxiliary p).1
      (hs.auxiliary p).2.2 (hr p) (cut.no_arrivals_before p)
    exact cut.span.mark_zero_aux 1 p .ready (by decide) (cut.span.allStates_aux_flows 1 p .ready hquiet)
  refine ⟨⟨?_,?_,?_,?_,?_,target_gain,other_gain,recovery_gain,phase.prepared,phase.charge_rest,phase.raw_finished⟩⟩
  · rw [cut.emissions,input.emissions_before,List.nil_append]
    exact phase.emissions
  · have h := e.gain_balance 1 1
    linarith
  · intro q hq
    have h := e.gain_balance 1 q
    rw [other_gain q hq] at h
    linarith
  · rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 1 1,before_mark 1,zero_add]
    exact phase.mark_target
  · intro q hq
    rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 1 q,before_mark q,zero_add]
    exact phase.mark_other q hq

end KernelR.Hybrid
