import KernelR.LearnedReturn

/-! A physical one-cell PulseContract. The complete reacting execution is
constructed before applying the future-prefix theorem. No birth reachability,
multi-cell routing or universal refinement of all event orders is asserted. -/
namespace KernelR.Hybrid

structure SettledLearnedCycle (theta : Fin 1 → Parameters) (active : Fin 1 → Port)
    (initial : Snapshot 1) (port : Port) where
  returned : LearnedReturn theta active initial port
  last : Snapshot 1
  execution : Execution theta (fun _ _ => [])
    (withFuture initial [sourceToken 0 port initial.time]) last
  domain : LearnedDomain theta active initial last
  date : last.time = initial.time+15/2
  emissions : execution.ledger.emissions = [(0, initial.time+returned.firing.mark.clock.fire)]
  complete : CompleteThrough execution (initial.time+15/2)

theorem settled_learned_cycle_exists {theta active initial epsilon}
    (hs : LearnedRest theta active initial) (hb : PhysicalBox theta epsilon) :
    Nonempty (SettledLearnedCycle theta active initial (active 0)) := by
  obtain ⟨returned⟩ := learned_return_exists hs hb
  have order := returned.firing.mark.clock.chronology hb 0 (active 0) (hs.recovery 0)
  have ht : returned.last.time ≤ initial.time+15/2 := by
    rw [returned.date]
    linarith [order.reopen_before_gap]
  obtain ⟨waiting, hc, hr, he⟩ := learned_idle_complete (route := fun _ _ => []) returned.domain.1 ht
  let run := returned.execution.append waiting
  have hd := returned.domain.idle ht
  refine ⟨⟨returned, idleAt returned.last (initial.time+15/2), run, hd, rfl, ?_, hc⟩⟩
  change (returned.execution.append waiting).ledger.emissions = _
  rw [Execution.append_ledger]
  change returned.execution.ledger.emissions ++ waiting.ledger.emissions = _
  rw [returned.emissions, he, List.append_nil]

/-- Fixed latency is selected once from the reference memory. Every cycle's
physical firing has the same first crossing because that memory is retained. -/
noncomputable def learnedPulseContract {theta : Fin 1 → Parameters} {active reference epsilon}
    (hb : PhysicalBox theta epsilon) (href : LearnedRest theta active reference) :
    PulseContract theta (fun _ _ => []) active reference 0 (active 0) := by
  let latency := Classical.choose (learned_latency_exists (href.gain 0))
  have hl := Classical.choose_spec (learned_latency_exists (href.gain 0))
  change 3/10 < latency ∧ latency ≤ 9/10 ∧
    learnedHead (Real.exp (reference.x 0 (.z (active 0)))) latency = 1 ∧
      A22.Crossing.IsFirstCrossing
        (learnedHead (Real.exp (reference.x 0 (.z (active 0))))) 0 latency at hl
  refine ⟨15/2, by norm_num, fun _ => latency, (fun _ => by linarith [hl.1]),
    (fun _ => by linarith [hl.2.1]), ?_⟩
  intro initial hi
  obtain ⟨cycle⟩ := settled_learned_cycle_exists hi.1 hb
  have hz : Real.exp (initial.x 0 (.z (active 0))) =
      Real.exp (reference.x 0 (.z (active 0))) := congrArg Real.exp ((hi.2 0).2 (active 0))
  have hfirst : A22.Crossing.IsFirstCrossing
      (learnedHead (Real.exp (reference.x 0 (.z (active 0))))) 0
      cycle.returned.firing.mark.clock.fire := by
    rw [← hz]
    exact ⟨by linarith [cycle.returned.firing.mark.clock.fire_lower],
      le_of_eq cycle.returned.firing.mark.clock.fire_value.symm, cycle.returned.firing.mark.clock.fire_before⟩
  have hlat := learned_latency_unique hfirst hl.2.2.2
  refine ⟨⟨cycle.last, cycle.execution, ⟨cycle.domain.1, ?_⟩, cycle.date, ?_⟩⟩
  · intro i
    exact ⟨(cycle.domain.2 i).1.trans (hi.2 i).1,
      fun p => ((cycle.domain.2 i).2 p).trans ((hi.2 i).2 p)⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [Execution.emissionTimes, cycle.emissions, hlat]

theorem learned_unbounded_responding_prefixes {theta active reference epsilon}
    (hb : PhysicalBox theta epsilon) (href : LearnedRest theta active reference)
    (schedule : FutureSchedule (15/2)) (initial : Snapshot 1)
    (hi : LearnedDomain theta active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (T : ℝ) :
    let law := learnedPulseContract hb href
    ∃ k, T ≤ (law.readyStates schedule initial hi hfirst k).val.time ∧
      ∀ i, (law.prefixes schedule initial hi hfirst k).emissionTimes i =
        (List.range k).map (fun j => schedule.time j+law.latency i) :=
  (learnedPulseContract hb href).unbounded_responding_prefixes schedule initial hi hfirst T

theorem learned_complete_at_every_horizon {theta active reference epsilon}
    (hb : PhysicalBox theta epsilon) (href : LearnedRest theta active reference)
    (schedule : FutureSchedule (15/2)) (initial : Snapshot 1)
    (hi : LearnedDomain theta active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (T : ℝ) (hT : initial.time ≤ T) :
    ∃ (k : ℕ) (last : Snapshot 1)
      (run : Execution theta (fun _ _ => [])
        (withFuture initial (sourceQueue 0 (active 0) schedule.time k)) last),
      CompleteThrough run T ∧ ∀ j, schedule.time j ≤ T → j < k :=
  (learnedPulseContract hb href).complete_at_every_horizon schedule initial hi hfirst T hT

end KernelR.Hybrid
