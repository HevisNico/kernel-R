import KernelR.HybridPreparedLearningTrain
import KernelR.HybridFeedbackCalendar
/-! Actual A relearning from B's return-wire receiving calendar. -/
namespace KernelR.Hybrid

private theorem ofFn_three {α} (f : ℕ → α) (count : ℕ) :
    List.ofFn (fun k : Fin (count + 3) => f k.val) =
      f 0 :: f 1 :: f 2 :: List.ofFn (fun k : Fin count => f (k.val + 3)) := by
  simp only [List.ofFn_succ,Fin.val_zero,Fin.val_succ]

/-- The receiving list is the actual B-to-A wire calendar. Three silent inputs
and ten learned emissions follow from the ODE and current prepared state. -/
theorem Execution.feedback_receiver_phase {θ ε route s u} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 0) (hq : s.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x 0 (.z 2) ∧ s.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hr : ∀ p, s.raw 0 p = none) (hu : u.time = 4599 / 10)
    (first rest : ℝ) (hfirst : 3 / 10 < first ∧ first < 9 / 10)
    (hrest : 3 / 10 < rest ∧ rest < 9 / 10) (hle : first ≤ rest)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hcalendar : e.cellDeliveries 0 = (feedbackArrivalDates first rest delay).map (fun t => ⟨0,2,t⟩)) :
    Nonempty (PreparedLearningTrain e 0 2 10) := by
  let firstDate : ℝ := 344 + first + delay (344 + first)
  let date : ℕ → ℝ := fun k => 352 + 8 * (k : ℝ) + rest + delay (352 + 8 * (k : ℝ) + rest)
  let tail : List ℝ := List.ofFn (fun k : Fin 9 => date (k.val + 3))
  have hdates : List.ofFn (fun k : Fin 12 => date k.val) = date 0 :: date 1 :: date 2 :: tail :=
    ofFn_three date 9
  have hcal : e.cellDeliveries 0 = ⟨0,2,firstDate⟩ ::
      (List.ofFn (fun k : Fin 12 => date k.val)).map (fun t => ⟨0,2,t⟩) := by
    simpa only [feedbackArrivalDates,List.map_cons,firstDate,date] using hcalendar
  obtain ⟨cut⟩ := e.first_cell_delivery 0 _ _ hcal
  obtain ⟨input⟩ := cut.resting_input hs.ready_coordinates hr
  have hprepared := (cut.prepared_rest_input hs hq hr).1
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  have invariant := advanced.physical_invariant hb hf
  have valid := advanced.raw_valid hv
  have gain : Real.log (3 / 10) - 1 / 100000 ≤ cut.afterArrival.x 0 (.z 2) ∧
      cut.afterArrival.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [input.gain_preserved 2]
    exact hz
  have hcalRest : cut.rest.cellDeliveries 0 = (date 0 :: date 1 :: date 2 :: tail).map (fun t => ⟨0,2,t⟩) := by
    rw [← hdates]
    exact cut.later
  have hspace : (cut.afterArrival.time :: date 0 :: date 1 :: date 2 :: tail).Pairwise
      (fun t v => t + 15 / 2 ≤ v) := by
    rw [cut.date.2,← hdates]
    exact feedbackArrivalDates.spaced hle delay hdelay
  have hquiet : ∀ t ∈ cut.afterArrival.time :: date 0 :: date 1 :: date 2 :: tail,
      t + 15 / 2 ≤ u.time := by
    intro t ht
    rw [cut.date.2,← hdates] at ht
    have hm : t ∈ feedbackArrivalDates first rest delay := ht
    have hbound := (feedbackArrivalDates.bounds hfirst hrest delay hdelay t hm).2
    rw [hu]
    linarith
  obtain ⟨phase⟩ := cut.rest.prepared_learning_train hb invariant valid 0 2 hprepared gain
    input.raw_active input.raw_other (date 0) (date 1) (date 2) tail hcalRest hspace hquiet
  have hztarget : u.x 0 (.z 2) = s.x 0 (.z 2) + 9 / 5 := by
    rw [phase.gain_target,input.gain_preserved 2]
  have hzother : ∀ q, q ≠ 2 → u.x 0 (.z q) = s.x 0 (.z q) := by
    intro q hq
    rw [phase.gain_other q hq,input.gain_preserved q]
  have hbfinal : u.x 0 .b = s.x 0 .b := by
    rw [phase.recovery_preserved,input.recovery_preserved]
  have hbeforemark : ∀ p, cut.span.ledger.mark 0 p = 0 := by
    intro p
    have hquiet := cut.span.aux_ready_without_input_band 0 p (hs.auxiliary p).1
      (hs.auxiliary p).2.2 (hr p) (cut.no_arrivals_before p)
    exact cut.span.mark_zero_aux 0 p .ready (by decide) (cut.span.allStates_aux_flows 0 p .ready hquiet)
  refine ⟨⟨?_,?_,?_,?_,hztarget,hzother,hbfinal,phase.prepared,phase.charge_rest,phase.raw_finished⟩⟩
  · rw [cut.emissions,input.emissions_before,List.nil_append]
    simpa only [tail,List.length_ofFn] using phase.emissions
  · have h := e.gain_balance 0 2
    linarith
  · intro p hp
    have h := e.gain_balance 0 p
    rw [hzother p hp] at h
    linarith
  · intro p
    rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 0 p,hbeforemark p,zero_add]
    exact phase.mark_zero p

end KernelR.Hybrid
