import NativeWeakStep

namespace NetworkStability.NativePeriodicRing

open KernelR.Hybrid
open NativeStrong

/-- A READY section with all inputs closed at a cut between transactions. -/
structure QuietCut {θ : Fin N → KernelR.Hybrid.Parameters} (s : Snapshot N) : Prop where
  physical : PhysicalInvariant θ s
  valid : RawValid s
  ready : ∀ i, PreparedSection s i
  raw : ∀ i port, s.raw i port = none

/-- An internal token is appended after the pre-existing external launches.
Take it from its actual queue position and retain the other entries in order. -/
theorem quiet_arrival_from_queue {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    (box : PhysicalBox θ ε) (s : Snapshot N) (token : Delivery N)
    (before after : List (Delivery N)) (cut : @QuietCut N θ s)
    (time : s.time < token.due) (queue : s.pending = before ++ token :: after)
    (earliest : ∀ d ∈ before ++ after, token.due ≤ d.due) :
    Nonempty (QuietSourceArrival θ route s token (before ++ after)) := by
  have future : ∀ d ∈ s.pending, token.due ≤ d.due := by
    intro d member
    rw [queue] at member
    rcases List.mem_append.mp member with left | right
    · exact earliest d (List.mem_append_left _ left)
    · rcases List.mem_cons.mp right with rfl | afterToken
      · exact le_rfl
      · exact earliest d (List.mem_append_right _ afterToken)
  let flow := quietFlow (θ := θ) s time (fun i => (cut.ready i).ready)
    (fun i port => ((cut.ready i).auxiliary port).1) cut.raw
    (fun i => by linarith [(cut.ready i).charge.2])
    (fun i port => by linarith [((cut.ready i).auxiliary port).2.2]) future
  let v := quietAt s token.due
  let u := quietSourceAfter s token (before ++ after)
  let jump : Jump route v u := .arrive v token before after queue rfl (cut.raw token.cell token.port)
  let e : Execution θ route s u := .cons (.flow flow) (.cons (.jump jump) (.nil _))
  refine ⟨{
    final := u
    execution := e
    ready_flows := fun i => ⟨(cut.ready i).ready, trivial⟩
    contacts_transversal := by simp [e, jump, Execution.ContactsTransversal, Jump.ContactTransversal]
    date := rfl
    deliveries := rfl
    pending := rfl
    ready := fun i => by
      have ready := quietAt_ready_coordinates s i (cut.ready i).ready_coordinates time.le
      exact ⟨ready.ready, ready.charge, ready.auxiliary⟩
    values := rfl
    gain_preserved := fun _ _ => rfl
    recovery_preserved := fun _ => rfl
    raw_active := ?_
    raw_other := ?_
    emissions := rfl
    physical := e.physical_invariant box cut.physical
    raw_valid := e.raw_valid cut.valid
  }⟩
  · simp [u, quietSourceAfter, setRaw, quietAt]
  · intro i port different
    rcases different with cell | coord
    · simp [u, quietSourceAfter, setRaw, quietAt, cell, cut.raw]
    · by_cases cell : i = token.cell
      · subst i
        simp [u, quietSourceAfter, setRaw, quietAt, coord, cut.raw]
      · simp [u, quietSourceAfter, setRaw, quietAt, cell, cut.raw]

private theorem splice_local_start (s : Snapshot N) (i : Fin N) :
    splice s i (localView s i) s.pending = s := by
  have h := quietValues_initial s
  cases s
  simp [splice, localView, h]

/-- A strong return acknowledges the lap through a closed contact. The
isolated strong leg is transported with the actual router and pending list. -/
theorem closed_strong_step {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    (box : PhysicalBox θ ε) (s : Snapshot N) (i : Fin N) (port : Port)
    (physical : PhysicalInvariant θ s) (valid : RawValid s) (ready : ∀ j, PreparedSection s j)
    (gain : 9 / 5 ≤ Real.exp (s.x i (.z port)) ∧ Real.exp (s.x i (.z port)) ≤ 2)
    (active : s.raw i port = some s.time) (other : ∀ q, q ≠ port → s.raw i q = none)
    (spectators : Spectators s i)
    (future : ∀ token ∈ s.pending, s.time + 15 / 2 ≤ token.due)
    (closed : ∀ fire, s.time + 3 / 10 < fire → fire < s.time + 9 / 10 → route i fire = []) :
    ∃ (u : Snapshot N) (run : Execution θ route s u) (fire : ℝ),
      u.time = s.time + 15 / 2 ∧ u.pending = s.pending ∧
      run.deliveries = [] ∧ run.ledger.emissions = [(i, fire)] ∧
      (∀ j q, u.x j (.z q) = s.x j (.z q)) ∧
      (∀ j, u.x j .b = s.x j .b) ∧ @QuietCut N θ u := by
  let localParameters : Fin 1 → KernelR.Hybrid.Parameters := fun _ => θ i
  have localBox : PhysicalBox localParameters ε := ⟨box.1, fun _ q => box.2 i q⟩
  have localPhysical : PhysicalInvariant localParameters (localView s i) :=
    ⟨fun _ => physical.region i, fun _ q => physical.gain_cap i q,
      fun _ => physical.recovery_cap i, fun _ => physical.reserve i⟩
  have localValid : RawValid (localView s i) := fun _ q date seen => valid i q date seen
  obtain ⟨leg⟩ := local_leg_exists localBox (localView s i) port localPhysical localValid
    (show PreparedSection (localView s i) 0 from
      ⟨(ready i).ready, (ready i).charge, (ready i).recovery, (ready i).auxiliary⟩) gain active other rfl
  let fire := leg.cycle.fire.final.time
  have window : s.time + 3 / 10 < fire ∧ fire < s.time + 9 / 10 := by
    have bounds := leg.cycle.fire_bounds
    change s.time + 2 / 5 < fire ∧ fire < s.time + 7 / 10 at bounds
    constructor <;> linarith [bounds.1, bounds.2]
  have departure : issuedBy route i leg.execution.ledger.emissions = [] := by
    simp [issuedBy, leg.emissions, show route i leg.cycle.fire.final.time = [] from
      closed fire window.1 window.2]
  have allFuture : ∀ d ∈ s.pending ++ issuedBy route i leg.execution.ledger.emissions,
      leg.final.time ≤ d.due := by
    rw [departure, List.append_nil, leg.date]
    exact future
  obtain ⟨lifted, events, arrivals⟩ := splice_execution s i spectators leg.execution le_rfl
    leg.deliveries s.pending allFuture
  let u := splice s i leg.final (s.pending ++ issuedBy route i leg.execution.ledger.emissions)
  let run : Execution θ route s u := lifted.cast_source (splice_local_start s i).symm
  have clock : u.time = s.time + 15 / 2 := leg.date
  have pending : u.pending = s.pending := by simp [u, splice, departure]
  have seen : run.ledger.emissions = [(i, fire)] := by
    rw [Execution.cast_source_ledger, events, leg.emissions]; rfl
  have noDelivery : run.deliveries = [] := by rw [Execution.cast_source_deliveries, arrivals]
  have gains (j : Fin N) (q : Port) : u.x j (.z q) = s.x j (.z q) := by
    by_cases eq : j = i
    · subst j; simpa [u, splice, localView] using leg.gains q
    · simp [u, splice, eq, quietValues]
  have recovery (j : Fin N) : u.x j .b = s.x j .b := by
    by_cases eq : j = i
    · subst j; simpa [u, splice, localView] using leg.recovery
    · simp [u, splice, eq, quietValues]
  refine ⟨u, run, fire, clock, pending, noDelivery, seen, gains, recovery, ?_⟩
  refine ⟨run.physical_invariant box physical, run.raw_valid valid, ?_, ?_⟩
  · intro j
    by_cases eq : j = i
    · subst j
      exact ⟨by simpa [u, splice] using leg.ready.ready,
        by simpa [u, splice] using leg.ready.charge, by simpa [u, splice] using leg.ready.recovery,
        fun q => by simpa [u, splice] using leg.ready.auxiliary q⟩
    · have weakClock : s.time ≤ u.time := by rw [clock]; linarith
      have idle := quietAt_ready_coordinates s j (spectators.ready j eq) weakClock
      exact ⟨by simpa [u, splice, quietAt, eq] using idle.ready,
        by simpa [u, splice, quietAt, eq] using idle.charge,
        by rw [recovery]; exact (ready j).recovery,
        fun q => by simpa [u, splice, quietAt, eq] using idle.auxiliary q⟩
  · intro j q
    by_cases eq : j = i
    · subst j; simpa [u, splice] using leg.raw q
    · simpa [u, splice, eq] using spectators.raw j eq q

end NetworkStability.NativePeriodicRing
