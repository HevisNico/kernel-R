import KernelR.LearnedSingleCell
import KernelR.HybridUniversalExecution

/-! Universal observations for repeatable learned operation. The schedules may
be irregular, subject to the actual pulse contract's settling duration. The
generic statements require a physical PulseContract; the one-cell wrappers
instantiate it with the proved learned cycle. No multi-cell pulse contract,
infinite maximal run or new progress theorem is assumed or supplied here. -/
namespace KernelR.Hybrid

theorem LearnedRest.physical_invariant {n θ active s}
    (h : @LearnedRest n θ active s) : PhysicalInvariant θ s where
  region := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · linarith [(h.recovery i).1]
    · rw [h.charge i]
      norm_num
    · intro p
      rw [h.aux i p]
      change s.x i (.m p) ≤ 1
      have hm := (abs_le.mp (h.sensor i p)).2
      linarith
  gain_cap := h.cap
  recovery_cap := fun i => by linarith [(h.recovery i).2]
  reserve := h.reserve

private theorem learned_future_physical {n θ active s}
    (h : @LearnedRest n θ active s) (future : List (Delivery n)) :
    PhysicalInvariant θ (withFuture s future) :=
  ⟨h.physical_invariant.region, h.cap, h.physical_invariant.recovery_cap, h.reserve⟩

theorem LearnedRest.of_observational_eq {n θ active s u}
    (hs : @LearnedRest n θ active s) (h : s.ObservationalEq u) :
    LearnedRest θ active u where
  main := by intro i; rw [←h.main]; exact hs.main i
  aux := by intro i p; rw [←h.aux]; exact hs.aux i p
  raw := by intro i p; rw [←h.raw]; exact hs.raw i p
  pending := (List.Perm.nil_eq (hs.pending ▸ h.pending)).symm
  charge := by intro i; rw [←h.values]; exact hs.charge i
  sensor := by intro i p; rw [←h.values]; exact hs.sensor i p
  reserve := by intro i; rw [←h.values]; exact hs.reserve i
  gain := by intro i; rw [←h.values]; exact hs.gain i
  cap := by intro i p; rw [←h.values]; exact hs.cap i p
  recovery := by intro i; rw [←h.values]; exact hs.recovery i

theorem LearnedDomain.of_observational_eq {n θ active reference s u}
    (hs : @LearnedDomain n θ active reference s) (h : s.ObservationalEq u) :
    LearnedDomain θ active reference u := by
  refine ⟨hs.1.of_observational_eq h, ?_⟩
  intro i
  constructor
  · rw [←h.values]
    exact (hs.2 i).1
  · intro p
    rw [←h.values]
    exact (hs.2 i).2 p

/-- Every complete finite execution of the same queued prefix has the actual
learned endpoint and exact per-cell responses. Thus retained memories and
inter-input timing are independent of legal flow subdivision and jump order.
The reference states are the recursive states left by the preceding cycles. -/
theorem PulseContract.every_complete_prefix {n θ route active reference cell port ε}
    (law : @PulseContract n θ route active reference cell port)
    (hb : PhysicalBox θ ε) (schedule : FutureSchedule law.duration)
    (initial : Snapshot n) (hi : LearnedDomain θ active reference initial)
    (hfirst : initial.time ≤ schedule.time 0) (k : ℕ) {u : Snapshot n}
    (run : Execution θ route (withFuture initial (sourceQueue cell port schedule.time k)) u)
    (hc : CompleteThrough run (law.readyStates schedule initial hi hfirst k).val.time) :
    (law.readyStates schedule initial hi hfirst k).val.ObservationalEq u ∧
      LearnedDomain θ active reference u ∧
      ∀ i, run.emissionTimes i =
        (List.range k).map (fun j => schedule.time j + law.latency i) := by
  let canonical := law.prefixes schedule initial hi hfirst k
  have hcanonical := law.prefix_complete schedule initial hi hfirst k
  have hinvariant := learned_future_physical hi.1 (sourceQueue cell port schedule.time k)
  have hobs := (canonical.observational_unique run hb hinvariant hcanonical hc).1
  refine ⟨hobs, (law.readyStates schedule initial hi hfirst k).property.1.of_observational_eq hobs, ?_⟩
  intro i
  exact (run.emissionTimes_unique canonical hb hinvariant hc hcanonical i).trans
    (law.prefix_response schedule initial hi hfirst k i)

/-- At each finite horizon there is a complete witness including every source
due by that horizon. Every complete trace from that same finite initial queue
has the same physical observations and ordered per-cell emission lists.
This does not claim a closed output formula for a horizon inside a cycle. -/
theorem PulseContract.complete_at_every_horizon_universal
    {n θ route active reference cell port ε}
    (law : @PulseContract n θ route active reference cell port)
    (hb : PhysicalBox θ ε) (schedule : FutureSchedule law.duration)
    (initial : Snapshot n) (hi : LearnedDomain θ active reference initial)
    (hfirst : initial.time ≤ schedule.time 0) (T : ℝ) (hT : initial.time ≤ T) :
    ∃ (k : ℕ) (last : Snapshot n)
      (witness : Execution θ route (withFuture initial (sourceQueue cell port schedule.time k)) last),
      CompleteThrough witness T ∧ (∀ j, schedule.time j ≤ T → j < k) ∧
      ∀ (u : Snapshot n)
        (run : Execution θ route (withFuture initial (sourceQueue cell port schedule.time k)) u),
        CompleteThrough run T →
          last.ObservationalEq u ∧ ∀ i, run.emissionTimes i = witness.emissionTimes i := by
  obtain ⟨k, last, witness, hw, hcovered⟩ :=
    law.complete_at_every_horizon schedule initial hi hfirst T hT
  have hinvariant := learned_future_physical hi.1 (sourceQueue cell port schedule.time k)
  refine ⟨k, last, witness, hw, hcovered, ?_⟩
  intro u run hc
  exact ⟨(witness.observational_unique run hb hinvariant hw hc).1,
    fun i => run.emissionTimes_unique witness hb hinvariant hc hw i⟩

/-- Physical one-cell instance: arbitrary irregular inputs with gaps at least
7.5, actual state retention, and universal responses at every settled prefix. -/
theorem learned_every_complete_prefix {theta active reference epsilon}
    (hb : PhysicalBox theta epsilon) (href : LearnedRest theta active reference)
    (schedule : FutureSchedule (15/2)) (initial : Snapshot 1)
    (hi : LearnedDomain theta active reference initial)
    (hfirst : initial.time ≤ schedule.time 0) (k : ℕ) {u : Snapshot 1}
    (run : Execution theta (fun _ _ => [])
      (withFuture initial (sourceQueue 0 (active 0) schedule.time k)) u)
    (hc : CompleteThrough run
      ((learnedPulseContract hb href).readyStates schedule initial hi hfirst k).val.time) :
    ((learnedPulseContract hb href).readyStates schedule initial hi hfirst k).val.ObservationalEq u ∧
      LearnedDomain theta active reference u ∧
      ∀ i, run.emissionTimes i = (List.range k).map
        (fun j => schedule.time j + (learnedPulseContract hb href).latency i) :=
  (learnedPulseContract hb href).every_complete_prefix hb schedule initial hi hfirst k run hc

/-- Nonvacuous universal comparison at every finite horizon of the physically
instantiated one-cell learned regime. Queues remain finite horizon restrictions. -/
theorem learned_complete_at_every_horizon_universal {theta active reference epsilon}
    (hb : PhysicalBox theta epsilon) (href : LearnedRest theta active reference)
    (schedule : FutureSchedule (15/2)) (initial : Snapshot 1)
    (hi : LearnedDomain theta active reference initial)
    (hfirst : initial.time ≤ schedule.time 0) (T : ℝ) (hT : initial.time ≤ T) :
    ∃ (k : ℕ) (last : Snapshot 1)
      (witness : Execution theta (fun _ _ => [])
        (withFuture initial (sourceQueue 0 (active 0) schedule.time k)) last),
      CompleteThrough witness T ∧ (∀ j, schedule.time j ≤ T → j < k) ∧
      ∀ (u : Snapshot 1)
        (run : Execution theta (fun _ _ => [])
          (withFuture initial (sourceQueue 0 (active 0) schedule.time k)) u),
        CompleteThrough run T →
          last.ObservationalEq u ∧ ∀ i, run.emissionTimes i = witness.emissionTimes i :=
  (learnedPulseContract hb href).complete_at_every_horizon_universal
    hb schedule initial hi hfirst T hT

#print axioms PulseContract.every_complete_prefix
#print axioms PulseContract.complete_at_every_horizon_universal
#print axioms learned_every_complete_prefix
#print axioms learned_complete_at_every_horizon_universal

end KernelR.Hybrid
