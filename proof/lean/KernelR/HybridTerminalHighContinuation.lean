import KernelR.HybridUniversalBirthCadenceChain
import KernelR.HybridLocalCadenceHighBudgetTrain
import KernelR.HybridUniversalExecution
import KernelR.HybridFuture

/-! Isolated high-gain continuations from actual finite-chain endpoints.

The global terminal queue is proved empty before taking its destination
projection. All physical coordinates, including sensor residues and reserve,
are retained. New incoming dates are arbitrary protocol data with gaps at
least 3.7; output dates are derived from physical first crossings. These are
isolated one-cell continuations with empty routing, not continuations of the
original network router (whose finite contact window closes at T+1).
-/
namespace KernelR.Hybrid

/-- Destination projection preserves observational equality, including the
actual pending-token multiset rather than replacing it by an empty queue. -/
theorem Snapshot.ObservationalEq.autonomousView {n s u}
    (h : @Snapshot.ObservationalEq n s u) (i : Fin n) :
    (s.autonomousView i).ObservationalEq (u.autonomousView i) where
  time := h.time
  values := by funext j q; exact congrFun (congrFun h.values i) q
  main := by funext j; exact congrFun h.main i
  aux := by funext j q; exact congrFun (congrFun h.aux i) q
  raw := by funext j q; exact congrFun (congrFun h.raw i) q
  pending := List.Perm.filterMap (Delivery.atCell i) h.pending

/-- The high-gain resting section actually reached by the finite-chain
factory. This is separate from the older low-gain `LearnedRest` section. -/
structure IsolatedHighRest (θ : Fin 1 → Parameters) (p : Port) (s : Snapshot 1) : Prop where
  physical : PhysicalInvariant θ s
  ready : ∀ j, ReadyCoordinates s j
  charge : s.x 0 .q = 1 / 10
  raw_none : ∀ j q, s.raw j q = none
  pending : s.pending = []
  gain : 16 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 7 / 2
  recovery : 37999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 38001 / 100000

/-- The reusable physical section does not depend on the presentation order
of an empty queue or on a particular legal simultaneous-event ordering. -/
theorem IsolatedHighRest.of_observational_eq {θ p s u}
    (hs : IsolatedHighRest θ p s) (h : s.ObservationalEq u) : IsolatedHighRest θ p u where
  physical := h.physical_invariant hs.physical
  ready := by
    intro j
    refine ⟨?_,?_,?_⟩
    · rw [←h.main]; exact (hs.ready j).ready
    · rw [←h.values]; exact (hs.ready j).charge
    · intro q
      rw [←h.aux,←h.values]
      exact (hs.ready j).auxiliary q
  charge := by rw [←h.values]; exact hs.charge
  raw_none := by intro j q; rw [←h.raw]; exact hs.raw_none j q
  pending := (List.Perm.nil_eq (hs.pending ▸ h.pending)).symm
  gain := by rw [←h.values]; exact hs.gain
  recovery := by rw [←h.values]; exact hs.recovery

/-- The only new operational tokens are the declared isolated input train. -/
noncomputable def isolatedHighSource (s : Snapshot 1) (p : Port)
    (first : ℝ) (later : List ℝ) : Snapshot 1 :=
  withFuture s ((first :: later).map (fun t => (⟨0,p,t⟩ : Delivery 1)))

/-- An actual complete physical response to every member of a supplied finite
irregular train. Every memory coordinate is retained throughout the train. -/
structure IsolatedHighContinuation (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (first : ℝ) (later : List ℝ) (terminal : ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) (isolatedHighSource s p first later) final
  date : final.time = terminal
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = []
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  deliveries : execution.deliveries =
    (first :: later).map (fun t => (⟨0,p,t⟩ : Delivery 1))
  calendar : execution.emissionTimes 0 =
    (first :: later).map (fun t => t + highRestLatency (Real.exp (s.x 0 (.z p))))
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution terminal

/-- Start with the retained resting state, wait physically until the first
new source, consume it by an arrival, then construct every high response.
No reaching execution, response calendar, reset or memory update is supplied. -/
theorem isolated_high_continuation_exists {θ ε s p first later terminal}
    (hb : PhysicalBox θ ε) (hs : IsolatedHighRest θ p s)
    (hfirst : s.time < first)
    (hSchedule : CadenceHighBudgetSchedule first later terminal) :
    Nonempty (IsolatedHighContinuation θ s p first later terminal) := by
  let source := isolatedHighSource s p first later
  let token : Delivery 1 := ⟨0,p,first⟩
  let future := later.map (fun t => (⟨0,p,t⟩ : Delivery 1))
  have hphysical : PhysicalInvariant θ source :=
    ⟨hs.physical.region,hs.physical.gain_cap,hs.physical.recovery_cap,hs.physical.reserve⟩
  have hvalid : RawValid source := by
    intro j q origin h
    rw [show source.raw j q = none from hs.raw_none j q] at h
    contradiction
  have hready : ∀ j, ReadyCoordinates source j := fun j =>
    ⟨(hs.ready j).ready,(hs.ready j).charge,(hs.ready j).auxiliary⟩
  have hraw : ∀ j q, source.raw j q = none := hs.raw_none
  have hqueue : source.pending = token :: future := by
    simp [source,isolatedHighSource,withFuture,hs.pending,token,future]
  have hfuture : ∀ d ∈ future, token.due ≤ d.due := by
    intro d hd
    obtain ⟨time,ht,rfl⟩ := List.mem_map.mp hd
    change first ≤ time
    linarith [hSchedule.source_lower time ht]
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) hb source token future
    hphysical hvalid hready hraw hfirst hqueue hfuture
  have hcharge : arrival.final.x 0 .q = 1 / 10 := by
    rw [arrival.values]
    change relax (1 / 2) (1 / 10) (s.x 0 .q) s.time first = 1 / 10
    rw [hs.charge]
    simp [relax]
  have hcoordinates : CadenceReadyCoordinates arrival.final 0 (8 / 25) := by
    refine ⟨(arrival.ready 0).ready,?_,(arrival.ready 0).auxiliary⟩
    rw [hcharge]
    constructor <;> norm_num
  have hgain : 16 / 5 ≤ Real.exp (arrival.final.x 0 (.z p)) ∧
      Real.exp (arrival.final.x 0 (.z p)) ≤ 7 / 2 := by
    rw [arrival.gain_preserved]
    exact hs.gain
  have hrecovery : 37999 / 100000 ≤ arrival.final.x 0 .b ∧
      arrival.final.x 0 .b ≤ 38001 / 100000 := by
    rw [arrival.recovery_preserved]
    exact hs.recovery
  obtain ⟨train⟩ := local_cadence_high_full_budget_train_exists hb arrival.final p later terminal
    arrival.physical arrival.raw_valid hcoordinates (by rw [hcharge]) hgain hrecovery
    arrival.raw_active (fun q hq => arrival.raw_other 0 q (Or.inr hq)) arrival.pending
    (by rw [arrival.date]; exact hSchedule)
  let execution := arrival.execution.append train.execution
  have hfirstFire : train.first.final.time =
      first + highRestLatency (Real.exp (s.x 0 (.z p))) := by
    rw [train.first.date,train.first.exact_rest_latency hcharge hgain]
    change arrival.final.time + highRestLatency (Real.exp (arrival.final.x 0 (.z p))) = _
    rw [arrival.date,arrival.gain_preserved]
    rfl
  have htimes : execution.emissionTimes 0 = train.execution.emissionTimes 0 := by
    rw [Execution.emissionTimes_append]
    have ha : arrival.execution.emissionTimes 0 = [] := by
      simp [Execution.emissionTimes,arrival.emissions]
    rw [ha,List.nil_append]
  refine ⟨{
    final := train.final, execution := execution, date := train.date
    ready := train.ready, charge := train.charge, raw_none := train.raw_none
    pending := train.pending
    gains := fun j q => (train.gains j q).trans (arrival.gain_preserved j q)
    recovery := fun j => (train.recovery j).trans (arrival.recovery_preserved j)
    deliveries := by
      rw [Execution.deliveries_append,arrival.deliveries,train.deliveries]
      rfl
    calendar := ?_, physical := train.physical, raw_valid := train.raw_valid
    complete := by simpa only [CompleteThrough] using train.complete
  }⟩
  rw [htimes,train.calendar,hfirstFire,arrival.gain_preserved]
  rfl

/-- The resting high section is preserved by every constructed train, so
another irregular finite train may start from the actual final coordinates. -/
theorem IsolatedHighContinuation.high_rest {θ s p first later terminal}
    (c : IsolatedHighContinuation θ s p first later terminal) (hs : IsolatedHighRest θ p s) :
    IsolatedHighRest θ p c.final where
  physical := c.physical
  ready := c.ready
  charge := c.charge
  raw_none := c.raw_none
  pending := c.pending
  gain := by rw [c.gains]; exact hs.gain
  recovery := by rw [c.recovery]; exact hs.recovery

theorem IsolatedHighContinuation.emission_count {θ s p first later terminal}
    (c : IsolatedHighContinuation θ s p first later terminal) :
    (c.execution.emissionTimes 0).length = later.length + 1 := by
  rw [c.calendar]
  simp

/-- A subsequent train starts from the actual returned state, including its
evolved reserve and sensor residues, rather than a replacement reference. -/
theorem IsolatedHighContinuation.next_exists {θ ε s p first later terminal}
    (c : IsolatedHighContinuation θ s p first later terminal)
    (hb : PhysicalBox θ ε) (hs : IsolatedHighRest θ p s)
    (nextFirst : ℝ) (nextLater : List ℝ) (nextTerminal : ℝ)
    (hfirst : c.final.time < nextFirst)
    (hSchedule : CadenceHighBudgetSchedule nextFirst nextLater nextTerminal) :
    Nonempty (IsolatedHighContinuation θ c.final p nextFirst nextLater nextTerminal) :=
  isolated_high_continuation_exists hb (c.high_rest hs) hfirst hSchedule

/-- Every complete finite isolated execution from this same retained source
has the constructed endpoint observations and exact ordered response dates. -/
theorem IsolatedHighContinuation.every_complete_execution {θ ε s p first later terminal}
    (c : IsolatedHighContinuation θ s p first later terminal)
    (hb : PhysicalBox θ ε) (hs : IsolatedHighRest θ p s) {u}
    (e : Execution θ (fun _ _ => []) (isolatedHighSource s p first later) u)
    (hc : CompleteThrough e terminal) :
    c.final.ObservationalEq u ∧ e.emissionTimes 0 =
      (first :: later).map (fun t => t + highRestLatency (Real.exp (s.x 0 (.z p)))) := by
  have hphysical : PhysicalInvariant θ (isolatedHighSource s p first later) :=
    ⟨hs.physical.region,hs.physical.gain_cap,hs.physical.recovery_cap,hs.physical.reserve⟩
  exact ⟨(c.execution.observational_unique e hb hphysical c.complete hc).1,
    (e.emissionTimes_unique c.execution hb hphysical hc c.complete 0).trans c.calendar⟩

/-- Repeatability belongs to every complete physical execution of the new
input program, not only to the constructor's chosen witness. -/
theorem IsolatedHighContinuation.every_complete_high_rest {θ ε s p first later terminal}
    (c : IsolatedHighContinuation θ s p first later terminal)
    (hb : PhysicalBox θ ε) (hs : IsolatedHighRest θ p s) {u}
    (e : Execution θ (fun _ _ => []) (isolatedHighSource s p first later) u)
    (hc : CompleteThrough e terminal) : IsolatedHighRest θ p u :=
  (c.high_rest hs).of_observational_eq (c.every_complete_execution hb hs e hc).1

namespace ConstructedBirthCadenceChain
variable {n θ bornCells K sigma centre delay T}
  (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)

/-- Projection keeps the actual destination-filtered queue. At the proved
terminal endpoint this queue is empty because the entire global queue is empty. -/
theorem terminal_high_rest (i : Fin (n+1)) :
    IsolatedHighRest (fun _ : Fin 1 => θ i) (cadenceActivePort n i) (c.final.autonomousView i) := by
  have hborn := c.preparation.initial_birth i
  have hport : cadenceActivePort n i ≠ 1 := by
    unfold cadenceActivePort
    split_ifs <;> decide
  have hnominal : nominalGain (cadenceActivePort n i) = 3 / 10 := by
    simp only [nominalGain,hport,ite_false]
  have hgain := (((hborn.2.2 0).2.2.2.2 (cadenceActivePort n i)).1)
  rw [hnominal] at hgain
  have hhigh : 16 / 5 ≤ Real.exp (c.final.x i (.z (cadenceActivePort n i))) ∧
      Real.exp (c.final.x i (.z (cadenceActivePort n i))) ≤ 7 / 2 := by
    apply cadence_four_dose_gain_bounds
    rw [c.gain_target]
    constructor <;> linarith [hgain.1,hgain.2]
  have hb := (hborn.2.2 0).2.2.1
  refine ⟨Snapshot.autonomousView_physical c.physical i,?_,c.charge i,
    fun _ q => c.raw_none i q,?_,hhigh,?_⟩
  · intro j
    exact ⟨(c.ready i).ready,(c.ready i).charge,(c.ready i).auxiliary⟩
  · change cellQueue i c.final.pending = []
    rw [c.pending]
    rfl
  · change 37999 / 100000 ≤ c.final.x i .b ∧ c.final.x i .b ≤ 38001 / 100000
    rw [c.recovery]
    constructor <;> linarith [hb.1,hb.2]

/-- Every actual terminal cell can physically answer any new finite irregular
isolated train with spacing at least3.7, preserving all of its learned memories.
The first input is strictly after the actual terminal date; no state is reset. -/
theorem terminal_high_continuation_exists {ε} (hb : PhysicalBox θ ε)
    (i : Fin (n+1)) (first : ℝ) (later : List ℝ) (terminal : ℝ)
    (hfirst : c.final.time < first)
    (hSchedule : CadenceHighBudgetSchedule first later terminal) :
    Nonempty (IsolatedHighContinuation (fun _ : Fin 1 => θ i)
      (c.final.autonomousView i) (cadenceActivePort n i) first later terminal) :=
  isolated_high_continuation_exists (autonomous_physical_box hb i) (c.terminal_high_rest i)
    hfirst hSchedule

/-- The high section is reached by every complete execution of the original
birth program, rather than only by the factory's selected execution. -/
theorem terminal_high_rest_of_complete_execution {ε u} (hb : PhysicalBox θ ε)
    (e : Execution θ c.router (familyPreparationBornSource bornCells K) u)
    (hc : CompleteThrough e T) (i : Fin (n+1)) :
    IsolatedHighRest (fun _ : Fin 1 => θ i) (cadenceActivePort n i) (u.autonomousView i) :=
  (c.terminal_high_rest i).of_observational_eq ((c.all_complete hb u e hc).1.autonomousView i)

/-- Isolated reuse can start from any actual complete original-chain endpoint.
The new queue retains that endpoint's destination-filtered pending list. -/
theorem terminal_high_continuation_of_complete_execution_exists {ε u} (hb : PhysicalBox θ ε)
    (e : Execution θ c.router (familyPreparationBornSource bornCells K) u)
    (hc : CompleteThrough e T) (i : Fin (n+1))
    (first : ℝ) (later : List ℝ) (terminal : ℝ) (hfirst : u.time < first)
    (hSchedule : CadenceHighBudgetSchedule first later terminal) :
    Nonempty (IsolatedHighContinuation (fun _ : Fin 1 => θ i)
      (u.autonomousView i) (cadenceActivePort n i) first later terminal) :=
  isolated_high_continuation_exists (autonomous_physical_box hb i)
    (c.terminal_high_rest_of_complete_execution hb e hc i) hfirst hSchedule

end ConstructedBirthCadenceChain

#print axioms isolated_high_continuation_exists
#print axioms IsolatedHighContinuation.every_complete_execution
#print axioms ConstructedBirthCadenceChain.terminal_high_continuation_exists
#print axioms ConstructedBirthCadenceChain.terminal_high_continuation_of_complete_execution_exists

end KernelR.Hybrid
