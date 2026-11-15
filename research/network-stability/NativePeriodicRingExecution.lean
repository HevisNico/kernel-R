import NativePeriodicRingSteps
import NativePeriodicRingProfile
import NativePeriodicRingTiming

namespace NetworkStability.NativePeriodicRing

open KernelR.Hybrid
open NativeRing (Input Probe root inputCell inputPort toDelivery nativeParameters BelowRail successor horizon)
open NativeStrong

private theorem box : PhysicalBox (nativeParameters N) (1 / 10) :=
  ⟨KernelR.FutureControls.parameters_box.1, fun _ => KernelR.FutureControls.parameters_box.2 0⟩

abbrev Run (p : Parameters N) (size : 2 ≤ N) (s u : Snapshot N) :=
  Execution (nativeParameters N) (router p size) s u

abbrev ReadyCut (s : Snapshot N) := @QuietCut N (nativeParameters N) s

private def PortAt (size : 2 ≤ N) (i : Fin N) (port : Port) : Option (Input N) :=
  if port = 0 then some (.inl i) else if i = root size ∧ port = 2 then some (.inr ()) else none

private theorem portAt_eq (size : 2 ≤ N) (i : Fin N) (port : Port) (key : Input N) :
    PortAt size i port = some key ↔ i = inputCell size key ∧ port = inputPort key := by
  rcases key with j | ⟨⟩
  · simp only [NativeRing.inputCell, NativeRing.inputPort]
    unfold PortAt
    split <;> rename_i condition
    · simp [condition]
    · split <;> simp_all
  · simp only [NativeRing.inputCell, NativeRing.inputPort]
    unfold PortAt
    split <;> rename_i condition
    · have impossible : port ≠ 2 := condition.trans_ne (by decide)
      simp [impossible]
    · split <;> simp_all

private theorem prepared_gain_for_key (p : Parameters N) (size : 2 ≤ N) (key : Input N) :
    (NativeRing.prepared p.ring size).x (inputCell size key) (.z (inputPort key)) =
      Real.log (initialAmplitude p key) := by
  have different : (2 : Port) ≠ 0 := by decide
  rcases key with i | ⟨⟩ <;>
    simp [NativeRing.prepared, NativeRing.Parameters.amplitude, NativeRing.inputCell,
      NativeRing.inputPort, initialAmplitude, different]

private def writesAt (p : Parameters N) (size : 2 ≤ N) (lap : Nat) (i : Fin N) (port : Port) : Nat :=
  (PortAt size i port).elim 0 (earned p lap)

private def MemoryAt (p : Parameters N) (size : 2 ≤ N) (lap : Nat) (s : Snapshot N) : Prop :=
  (∀ i port, s.x i (.z port) = (NativeRing.prepared p.ring size).x i (.z port) +
    (3 / 5 : ℝ) * writesAt p size lap i port) ∧
  ∀ i, s.x i .b = (NativeRing.prepared p.ring size).x i .b

private theorem memory_gain {p : Parameters N} {size : 2 ≤ N} {lap : Nat} {s : Snapshot N}
    (matchMemory : MemoryAt p size lap s) (key : Input N) :
    s.x (inputCell size key) (.z (inputPort key)) =
      Real.log (initialAmplitude p key) + (3 / 5 : ℝ) * earned p lap key := by
  rw [matchMemory.1, prepared_gain_for_key, writesAt]
  rw [(portAt_eq size _ _ key).2 ⟨rfl, rfl⟩]
  rfl

private theorem memory_preserved {p : Parameters N} {size : 2 ≤ N} {lap : Nat} {s u : Snapshot N}
    (memory : MemoryAt p size lap s)
    (gain : ∀ j q, u.x j (.z q) = s.x j (.z q)) (recovery : ∀ j, u.x j .b = s.x j .b) :
    MemoryAt p size lap u :=
  ⟨fun j q => (gain j q).trans (memory.1 j q), fun j => (recovery j).trans (memory.2 j)⟩

private structure SettledStep (p : Parameters N) (size : 2 ≤ N) (s : Snapshot N) (x : Probe N)
    (sources children : List (Delivery N)) (fired : Bool) where
  last : Snapshot N
  run : Run p size s last
  cut : ReadyCut last
  clock : last.time = x.due + 15 / 2
  queue : last.pending = sources ++ children
  deliveries : run.deliveries = [toDelivery size x]
  emissions : run.ledger.emissions.map Prod.fst = if fired then [inputCell size x.input] else []
  gain : ∀ i q, last.x i (.z q) = s.x i (.z q) +
    if fired = false ∧ i = inputCell size x.input ∧ q = inputPort x.input then 3 / 5 else 0
  recovery : ∀ i, last.x i .b = s.x i .b

private def TokenPlaced (size : 2 ≤ N) (s : Snapshot N) (x : Probe N) (sources : List (Delivery N)) : Prop :=
  s.pending = toDelivery size x :: sources ∨ s.pending = sources ++ [toDelivery size x]

private theorem admit_token {p : Parameters N} {size : 2 ≤ N} (s : Snapshot N)
    (cut : ReadyCut s) (x : Probe N) (sources : List (Delivery N)) (placement : TokenPlaced size s x sources)
    (future : ∀ token ∈ sources, x.due + 15 / 2 < token.due) (time : s.time < x.due) :
    Nonempty (QuietSourceArrival (nativeParameters N) (router p size) s (toDelivery size x) sources) := by
  have later : ∀ token ∈ sources, (toDelivery size x).due ≤ token.due := by
    intro token seen
    change x.due ≤ token.due
    linarith [future token seen]
  rcases placement with head | tail
  · exact quiet_source_arrival_exists box s (toDelivery size x) sources cut.physical cut.valid
      (fun i => (cut.ready i).ready_coordinates) cut.raw time head later
  · have placed : s.pending = sources ++ toDelivery size x :: [] := tail
    simpa only [List.append_nil] using quiet_arrival_from_queue (route := router p size) box s
      (toDelivery size x) sources [] cut time placed (by simpa only [List.append_nil] using later)

private theorem ready_after_intake {p : Parameters N} {size : 2 ≤ N} {s : Snapshot N}
    {token : Delivery N} {sources}
    (a : QuietSourceArrival (nativeParameters N) (router p size) s token sources)
    (cut : ReadyCut s) (i : Fin N) : PreparedSection a.final i :=
  ⟨(a.ready i).ready, (a.ready i).charge, by rw [a.recovery_preserved]; exact (cut.ready i).recovery,
    (a.ready i).auxiliary⟩

private theorem weak_transaction {p : Parameters N} {size : 2 ≤ N} (s : Snapshot N)
    (cut : ReadyCut s) (x : Probe N) (sources : List (Delivery N)) (placement : TokenPlaced size s x sources)
    (future : ∀ token ∈ sources, x.due + 15 / 2 < token.due) (time : s.time < x.due)
    (gain : Real.exp (s.x (inputCell size x.input) (.z (inputPort x.input))) ≤ 1) :
    Nonempty (SettledStep p size s x sources [] false) := by
  let token := toDelivery size x
  obtain ⟨a⟩ := admit_token (p := p) (size := size) s cut x sources placement future time
  have g : Real.exp (a.final.x token.cell (.z token.port)) ≤ 1 := by
    rw [a.gain_preserved]; exact gain
  have later : ∀ d ∈ a.final.pending, a.final.time + 15 / 2 ≤ d.due := by
    rw [a.date, a.pending]
    exact fun d seen => (future d seen).le
  obtain ⟨u, pulse, clock, pending, noDelivery, noFire, gains, rec, ready, raw⟩ :=
    weak_step_exists box a.final token.cell token.port a.physical a.raw_valid
      (ready_after_intake (size := size) a cut _) g a.raw_active (fun q neq => a.raw_other _ _ (Or.inr neq))
      ⟨fun j _ => a.ready j, fun j neq q => a.raw_other j q (Or.inl neq)⟩ later
  exact ⟨{
    last := u, run := a.execution.append pulse
    cut := ⟨pulse.physical_invariant box a.physical, pulse.raw_valid a.raw_valid,
      fun j => ready j (ready_after_intake (size := size) a cut j), raw⟩
    clock := clock.trans (congrArg (· + 15 / 2) a.date)
    queue := by rw [pending, a.pending, List.append_nil]
    deliveries := by simp [Execution.deliveries_append, a.deliveries, noDelivery]
    emissions := by simp [Execution.emissions_append, a.emissions, noFire]
    gain := fun i q => by rw [gains, a.gain_preserved]; simp [token, toDelivery]
    recovery := fun j => (rec j).trans (a.recovery_preserved j)
  }⟩

private theorem forward_transaction {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {lap : Nat} (s : Snapshot N) (cut : ReadyCut s) (x : Probe N) (sources : List (Delivery N))
    (placement : TokenPlaced size s x sources) (future : ∀ token ∈ sources, x.due + 15 / 2 < token.due)
    (time : s.time < x.due) (intake : IntakeWindow p lap x) (i : Fin N) (key : x.input = .inl i)
    (gain : 9 / 5 ≤ Real.exp (s.x (inputCell size x.input) (.z (inputPort x.input))) ∧
      Real.exp (s.x (inputCell size x.input) (.z (inputPort x.input))) ≤ 2) :
    ∃ child : Probe N, child.input = successor i ∧ IntakeWindow p lap child ∧
      x.due + 15 / 2 < child.due ∧
      Nonempty (SettledStep p size s x sources [toDelivery size child] true) := by
  let token := toDelivery size x
  obtain ⟨a⟩ := admit_token (p := p) (size := size) s cut x sources placement future time
  have render : token.cell = i := by simp [token, toDelivery, key, NativeRing.inputCell]
  have g : 9 / 5 ≤ Real.exp (a.final.x token.cell (.z token.port)) ∧
      Real.exp (a.final.x token.cell (.z token.port)) ≤ 2 := by
    rw [a.gain_preserved]; exact gain
  have later : ∀ d ∈ a.final.pending, a.final.time + 15 / 2 < d.due := by
    rw [a.date, a.pending]; exact future
  have wire {fire : ℝ} (lo : x.due + 3 / 10 < fire) (hi : fire < x.due + 9 / 10) :
      router p size token.cell fire = [toDelivery size ⟨fire + p.ring.delay i, successor i⟩] := by
    rw [render]
    exact forward_routes size i key intake ⟨lo, hi⟩
  obtain ⟨pulse⟩ := strong_step_exists box a.final token.cell token.port a.physical a.raw_valid
    (ready_after_intake (size := size) a cut _) g a.raw_active (fun q neq => a.raw_other _ _ (Or.inr neq))
    ⟨fun j _ => a.ready j, fun j neq q => a.raw_other j q (Or.inl neq)⟩ later (by
      rw [a.date]
      intro fire lo hi
      exact ⟨toDelivery size ⟨fire + p.ring.delay i, successor i⟩,
        wire lo hi, (intake.routed valid i key ⟨lo, hi⟩).2⟩)
  let child : Probe N := ⟨pulse.fireTime + p.ring.delay i, successor i⟩
  have window : x.due + 3 / 10 < pulse.fireTime ∧ pulse.fireTime < x.due + 9 / 10 := by
    simpa only [a.date, toDelivery] using pulse.fireBounds
  have childEq : pulse.child = toDelivery size child :=
    (List.singleton_inj.mp (pulse.routeAtFire.symm.trans (wire window.1 window.2)))
  have ready (j : Fin N) : PreparedSection pulse.final j := by
    by_cases eq : j = token.cell
    · subst j; exact pulse.selectedReady
    · have prep := pulse.spectatorReady j eq
      exact ⟨prep.ready, prep.charge, by rw [pulse.recoveryPreserved]; exact (ready_after_intake (size := size) a cut j).recovery,
        prep.auxiliary⟩
  have clocks := intake.routed valid i key window
  refine ⟨child, rfl, clocks.1, clocks.2, ⟨{
    last := pulse.final, run := a.execution.append pulse.execution
    cut := ⟨pulse.physical, pulse.rawValid, ready, pulse.inactive⟩
    clock := pulse.date.trans (congrArg (· + 15 / 2) a.date)
    queue := by rw [pulse.pending, a.pending, childEq]
    deliveries := by simp [Execution.deliveries_append, a.deliveries, pulse.deliveries]
    emissions := by simp [Execution.emissions_append, a.emissions, pulse.emissions, token, toDelivery]
    gain := ?_
    recovery := fun j => (pulse.recoveryPreserved j).trans (a.recovery_preserved j)
  }⟩⟩
  intro j q
  simpa using (pulse.gains j q).trans (a.gain_preserved j q)

private theorem return_transaction {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {lap : Nat} (s : Snapshot N) (cut : ReadyCut s) (x : Probe N) (sources : List (Delivery N))
    (placement : TokenPlaced size s x sources) (future : ∀ token ∈ sources, x.due + 15 / 2 < token.due)
    (time : s.time < x.due) (intake : IntakeWindow p lap x) (key : x.input = .inr ())
    (gain : 9 / 5 ≤ Real.exp (s.x (inputCell size x.input) (.z (inputPort x.input))) ∧
      Real.exp (s.x (inputCell size x.input) (.z (inputPort x.input))) ≤ 2) :
    Nonempty (SettledStep p size s x sources [] true) := by
  let token := toDelivery size x
  obtain ⟨a⟩ := admit_token (p := p) (size := size) s cut x sources placement future time
  have render : token.cell = root size := by simp [token, toDelivery, key, NativeRing.inputCell]
  have g : 9 / 5 ≤ Real.exp (a.final.x token.cell (.z token.port)) ∧
      Real.exp (a.final.x token.cell (.z token.port)) ≤ 2 := by
    rw [a.gain_preserved]; exact gain
  have later : ∀ d ∈ a.final.pending, a.final.time + 15 / 2 ≤ d.due := by
    rw [a.date, a.pending]; exact fun d seen => (future d seen).le
  obtain ⟨u, pulse, fire, clock, pending, noDelivery, emits, gains, rec, prep⟩ :=
    closed_strong_step box a.final token.cell token.port a.physical a.raw_valid (ready_after_intake (size := size) a cut)
      g a.raw_active (fun q neq => a.raw_other _ _ (Or.inr neq))
      ⟨fun j _ => a.ready j, fun j neq q => a.raw_other j q (Or.inl neq)⟩ later (by
        rw [a.date, render]
        intro fire lo hi
        exact return_route_closed valid size key intake ⟨lo, hi⟩)
  exact ⟨{
    last := u, run := a.execution.append pulse, cut := prep
    clock := clock.trans (congrArg (· + 15 / 2) a.date)
    queue := by rw [pending, a.pending, List.append_nil]
    deliveries := by simp [Execution.deliveries_append, a.deliveries, noDelivery]
    emissions := by simp [Execution.emissions_append, a.emissions, emits, token, toDelivery]
    gain := fun j q => by simpa using (gains j q).trans (a.gain_preserved j q)
    recovery := fun j => (rec j).trans (a.recovery_preserved j)
  }⟩


private def Link (a b : Input N) : Prop := ∃ i : Fin N, a = .inl i ∧ b = successor i

private theorem ports_length (N : Nat) : (ports N).length = N + 1 := by simp [ports]

private theorem ports_forward (i : Nat) (h : i < N) :
    (ports N)[i]'(by rw [ports_length]; omega) = .inl ⟨i, h⟩ := by
  unfold ports
  rw [List.getElem_append_left (by simpa using h)]
  simp

private theorem ports_chain (N : Nat) : (ports N).IsChain Link := by
  rw [List.isChain_iff_getElem]
  intro k h
  have klt : k < N := by rw [ports_length] at h; omega
  refine ⟨⟨k, klt⟩, ports_forward k klt, ?_⟩
  by_cases next : k + 1 < N
  · rw [ports_forward _ next]
    simp [successor, next]
  · have atEnd : k + 1 = N := by omega
    have last : (ports N)[k + 1]? = some (.inr ()) := by
      rw [atEnd, ports, List.getElem?_append_right (by simp)]
      simp
    have eq : (ports N)[k + 1] = .inr () := (List.getElem?_eq_some_iff.mp last).2
    rw [eq]
    simp [successor, next]

private theorem ports_last (N : Nat) : (ports N).getLast? = some (.inr ()) := by simp [ports]

private theorem ports_head (size : 2 ≤ N) :
    ports N = .inl (root size) :: (ports N).drop 1 := by
  have nonempty : 0 < (ports N).length := by simp [ports_length]
  have h := List.drop_eq_getElem_cons (i := 0) nonempty
  rw [ports_forward 0 (show 0 < N by omega)] at h
  exact h

private noncomputable def doseFor (size : 2 ≤ N) (target : Option (Input N)) (i : Fin N) (port : Port) : ℝ :=
  match target with
  | none => 0
  | some key => if i = inputCell size key ∧ port = inputPort key then 3 / 5 else 0

private def strongPrefix (target : Option (Input N)) (remaining : List (Input N)) : List (Input N) :=
  remaining.takeWhile fun key => decide (some key ≠ target)

private structure LapPulse (p : Parameters N) (size : 2 ≤ N) (lap : Nat) (s : Snapshot N)
    (sources : List (Delivery N)) (remaining : List (Input N)) (target : Option (Input N)) where
  last : Snapshot N
  run : Run p size s last
  cut : ReadyCut last
  beforeBoundary : last.time < boundary p (lap + 1)
  queue : last.pending = sources
  deliveries : run.deliveries.map (fun token => (token.cell, token.port)) =
    (strongPrefix target remaining ++ target.toList).map (fun key => (inputCell size key, inputPort key))
  emissions : run.ledger.emissions.map Prod.fst = (strongPrefix target remaining).map (inputCell size)
  gain : ∀ i port, last.x i (.z port) = s.x i (.z port) + doseFor size target i port
  recovery : ∀ i, last.x i .b = s.x i .b

private theorem parked_are_future {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {lap sourceCount : Nat} {x : Probe N} (window : IntakeWindow p lap x) :
    ∀ token ∈ (launchQueue p size sourceCount).drop (lap + 1), x.due + 15 / 2 < token.due := by
  intro d seen
  exact window.settled_before_boundary.trans
    ((boundary_before_launch valid (lap + 1)).trans_le (launch_queue_future valid size d seen))

private theorem silent_lap_finish {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {lap sourceCount : Nat} {s : Snapshot N} {x : Probe N}
    (remaining : List (Input N)) (cut : ReadyCut s) (memory : MemoryAt p size lap s)
    (placement : TokenPlaced size s x ((launchQueue p size sourceCount).drop (lap + 1)))
    (time : s.time < x.due) (window : IntakeWindow p lap x)
    (weak : earned p lap x.input < planned p x.input) :
    Nonempty (LapPulse p size lap s ((launchQueue p size sourceCount).drop (lap + 1))
      (x.input :: remaining) (some x.input)) := by
  have gain := checked_native_weak valid x.input _ weak
  rw [← memory_gain (size := size) memory x.input] at gain
  obtain ⟨tx⟩ := weak_transaction (p := p) (size := size) s cut x _ placement
    (parked_are_future valid size window (sourceCount := sourceCount)) time gain
  exact ⟨{
    last := tx.last, run := tx.run, cut := tx.cut
    beforeBoundary := tx.clock.trans_lt window.settled_before_boundary
    queue := tx.queue.trans (List.append_nil _)
    deliveries := by simp [tx.deliveries, toDelivery, strongPrefix]
    emissions := by simp [tx.emissions, strongPrefix]
    gain := fun i q => by simpa [doseFor] using tx.gain i q
    recovery := tx.recovery
  }⟩

set_option maxHeartbeats 1500000 in
/-- One traversal of the relay suffix. Strong steps pass the single
internal token on, while either a weak step or the strong return ends it. -/
private theorem traverse {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    (lap sourceCount : Nat) (target : Option (Input N)) (remaining : List (Input N))
    (s : Snapshot N) (x : Probe N) (cut : ReadyCut s) (memory : MemoryAt p size lap s)
    (placement : TokenPlaced size s x ((launchQueue p size sourceCount).drop (lap + 1)))
    (time : s.time < x.due) (window : IntakeWindow p lap x)
    (links : (x.input :: remaining).IsChain Link)
    (endKey : (x.input :: remaining).getLast? = some (.inr ()))
    (strong : ∀ k ∈ strongPrefix target (x.input :: remaining), earned p lap k = planned p k)
    (weak : ∀ k, target = some k → earned p lap k < planned p k)
    (targetInPath : ∀ k, target = some k → k ∈ x.input :: remaining) :
    Nonempty (LapPulse p size lap s ((launchQueue p size sourceCount).drop (lap + 1))
      (x.input :: remaining) target) := by
  induction remaining generalizing s x with
  | nil =>
    have parked := parked_are_future valid size window (sourceCount := sourceCount)
    by_cases stops : target = some x.input
    · rw [stops]
      exact silent_lap_finish valid size ([]) cut memory placement time window (weak _ stops)
    · have targetNone : target = none := by
        cases h : target with
        | none => rfl
        | some key =>
          have eq := List.mem_singleton.mp (targetInPath key h)
          exact (stops (h.trans (congrArg some eq))).elim
      have key : x.input = .inr () := by simpa using endKey
      have gain := checked_native_strong valid x.input
      rw [← strong _ (by simp [strongPrefix, Ne.symm stops]), ← memory_gain memory x.input] at gain
      obtain ⟨tx⟩ := return_transaction (p := p) valid size s cut x _ placement parked time window key gain
      refine ⟨{
        last := tx.last, run := tx.run, cut := tx.cut
        beforeBoundary := tx.clock.trans_lt window.settled_before_boundary
        queue := tx.queue.trans (List.append_nil _)
        deliveries := by simp [tx.deliveries, toDelivery, strongPrefix, targetNone]
        emissions := by simp [tx.emissions, strongPrefix, targetNone]
        gain := fun i q => by simpa [doseFor, targetNone] using tx.gain i q
        recovery := tx.recovery
      }⟩
  | cons next tail ih =>
    have parked := parked_are_future valid size window (sourceCount := sourceCount)
    by_cases stops : target = some x.input
    · rw [stops]
      exact silent_lap_finish valid size (next :: tail) cut memory placement time window (weak _ stops)
    · obtain ⟨⟨i, forward, successorKey⟩, restLinks⟩ := List.isChain_cons_cons.mp links
      have gain := checked_native_strong valid x.input
      rw [← strong _ (by simp [strongPrefix, Ne.symm stops]), ← memory_gain memory x.input] at gain
      obtain ⟨child, childKey, childWindow, sep, ⟨tx⟩⟩ :=
        forward_transaction valid size s cut x _ placement parked time window i forward gain
      have nextEq : child.input = next := childKey.trans successorKey.symm
      have sameGain (j : Fin N) (q : Port) : tx.last.x j (.z q) = s.x j (.z q) := by
        simpa using tx.gain j q
      have nextMemory := memory_preserved (size := size) memory sameGain tx.recovery
      have first : strongPrefix target (x.input :: next :: tail) =
          x.input :: strongPrefix target (child.input :: tail) := by
        simp [strongPrefix, Ne.symm stops, nextEq]
      have tailStrong : ∀ k ∈ strongPrefix target (child.input :: tail), earned p lap k = planned p k := by
        intro k seen
        exact strong k (first.symm ▸ List.mem_cons_of_mem _ seen)
      have tailTarget : ∀ k, target = some k → k ∈ child.input :: tail := by
        intro k eq
        rw [nextEq]
        rcases List.mem_cons.mp (targetInPath k eq) with same | tailSeen
        · exact (stops (eq.trans (congrArg some same))).elim
        · exact tailSeen
      have last : (child.input :: tail).getLast? = some (.inr ()) := by
        simpa only [nextEq, List.getLast?_cons_cons] using endKey
      obtain ⟨finish⟩ := ih tx.last child tx.cut nextMemory (Or.inr tx.queue)
        (tx.clock.trans_lt sep) childWindow (by simpa only [nextEq] using restLinks) last tailStrong tailTarget
      refine ⟨{
        last := finish.last, run := tx.run.append finish.run, cut := finish.cut
        beforeBoundary := finish.beforeBoundary, queue := finish.queue
        deliveries := ?_, emissions := ?_
        gain := fun i q => by rw [finish.gain, sameGain]
        recovery := fun i => (finish.recovery i).trans (tx.recovery i)
      }⟩
      · rw [Execution.deliveries_append, List.map_append, tx.deliveries, finish.deliveries, first]
        rfl
      · rw [Execution.emissions_append, List.map_append, tx.emissions, finish.emissions, first]
        rfl


private theorem ready_no_enabled_jump {p : Parameters N} {size : 2 ≤ N} {s : Snapshot N}
    (cut : ReadyCut s) (future : ∀ d ∈ s.pending, s.time < d.due) :
    ∀ v, IsEmpty (Jump (router p size) s v) :=
  ready_no_jump s (fun i => (cut.ready i).ready) (fun i q => ((cut.ready i).auxiliary q).1) cut.raw
    (fun i => by linarith [(cut.ready i).charge.2])
    (fun i q => by linarith [((cut.ready i).auxiliary q).2.2]) future

private structure QuietStretch (p : Parameters N) (size : 2 ≤ N) (s : Snapshot N) (T : ℝ) where
  last : Snapshot N
  run : Run p size s last
  complete : CompleteThrough run T
  cut : ReadyCut last
  queue : last.pending = s.pending
  deliveries : run.deliveries = []
  emissions : run.ledger.emissions = []
  gain : ∀ i q, last.x i (.z q) = s.x i (.z q)
  recovery : ∀ i, last.x i .b = s.x i .b

private theorem quiet_stretch {p : Parameters N} {size : 2 ≤ N} {s : Snapshot N} {T : ℝ}
    (cut : ReadyCut s) (time : s.time ≤ T) (future : ∀ d ∈ s.pending, T < d.due) :
    Nonempty (QuietStretch p size s T) := by
  by_cases clock : s.time = T
  · subst T
    exact ⟨⟨s, .nil _, ⟨rfl, ready_no_enabled_jump (size := size) cut future, future⟩,
      cut, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩⟩
  · let flow := quietFlow (θ := nativeParameters N) s (lt_of_le_of_ne time clock)
      (fun i => (cut.ready i).ready) (fun i q => ((cut.ready i).auxiliary q).1) cut.raw
      (fun i => by linarith [(cut.ready i).charge.2])
      (fun i q => by linarith [((cut.ready i).auxiliary q).2.2])
      (fun d seen => (future d seen).le)
    let run : Run p size s (quietAt s T) := .cons (.flow flow) (.nil _)
    have quiet : ReadyCut (quietAt s T) := by
      refine ⟨run.physical_invariant box cut.physical, run.raw_valid cut.valid, ?_, cut.raw⟩
      intro i
      have ready := quietAt_ready_coordinates s i (cut.ready i).ready_coordinates time
      exact ⟨ready.ready, ready.charge, (cut.ready i).recovery, ready.auxiliary⟩
    exact ⟨⟨_, run, ⟨rfl, ready_no_enabled_jump (size := size) quiet future, future⟩,
      quiet, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩⟩

private theorem memory_after_lap {p : Parameters N} {size : 2 ≤ N} {lap : Nat} {s u : Snapshot N}
    (memory : MemoryAt p size lap s)
    (gain : ∀ i port, u.x i (.z port) = s.x i (.z port) + doseFor size (trainingOrder p)[lap]? i port)
    (recovery : ∀ i, u.x i .b = s.x i .b) : MemoryAt p size (lap + 1) u := by
  refine ⟨?_, fun i => (recovery i).trans (memory.2 i)⟩
  intro i port
  rw [gain, memory.1]
  unfold writesAt
  rcases addr : PortAt size i port with _ | key
  · cases next : (trainingOrder p)[lap]? with
    | none => simp [doseFor]
    | some target =>
      have diff : ¬(i = inputCell size target ∧ port = inputPort target) := by
        rw [← portAt_eq size i port target, addr]
        simp
      simp [doseFor, diff]
  · change _ + doseFor size (trainingOrder p)[lap]? i port =
      _ + (3 / 5 : ℝ) * earned p (lap + 1) key
    rw [earned_next]
    cases next : (trainingOrder p)[lap]? with
    | none => simp [doseFor]
    | some target =>
      by_cases eq : target = key
      · subst target
        have atPort := (portAt_eq size i port key).mp addr
        simp [doseFor, atPort.1, atPort.2, Nat.cast_add]
        ring
      · have diff : ¬(i = inputCell size target ∧ port = inputPort target) := by
          rw [← portAt_eq, addr]
          simp [Ne.symm eq]
        simp [doseFor, diff, eq]

private structure LapBoundary (p : Parameters N) (size : 2 ≤ N) (sourceCount lap : Nat)
    (s : Snapshot N) : Prop where
  clock : s.time = boundary p lap
  queue : s.pending = (launchQueue p size sourceCount).drop lap
  cut : ReadyCut s
  memory : MemoryAt p size lap s

set_option maxHeartbeats 1500000 in
private theorem next_lap {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N) {lap sourceCount : Nat}
    {s : Snapshot N} (start : LapBoundary p size sourceCount lap s) (available : lap < sourceCount) :
    ∃ (u : Snapshot N) (run : Run p size s u),
      SettledLap p size sourceCount lap run ∧ LapBoundary p size sourceCount (lap + 1) u := by
  let x : Probe N := ⟨launchDate p lap, .inl (root size)⟩
  let marker := (trainingOrder p)[lap]?
  have shape : ports N = x.input :: (ports N).drop 1 := ports_head size
  have links : (x.input :: (ports N).drop 1).IsChain Link := by rw [← shape]; exact ports_chain N
  have endKey : (x.input :: (ports N).drop 1).getLast? = some (.inr ()) := by
    rw [← shape]; exact ports_last N
  have strong : ∀ k ∈ strongPrefix marker (x.input :: (ports N).drop 1), earned p lap k = planned p k := by
    rw [← shape]
    change ∀ k ∈ firingKeys p lap, earned p lap k = planned p k
    cases next : (trainingOrder p)[lap]? with
    | none => exact fun k _ => (trained_branch p lap next).2.2 k
    | some key =>
      obtain ⟨left, right, order, firing, admitted, below, trained⟩ := training_branch p lap next
      rwa [firing]
  have weak : ∀ k, marker = some k → earned p lap k < planned p k := by
    intro key next
    obtain ⟨_, _, _, _, _, less, _⟩ := training_branch p lap next
    exact less
  have targetInPath : ∀ k, marker = some k → k ∈ x.input :: (ports N).drop 1 := by
    intro k _
    rw [← shape]
    exact key_in_ports k
  have window : IntakeWindow p lap x := by
    constructor <;> simp [x, stage, root]
  have placement : TokenPlaced size s x ((launchQueue p size sourceCount).drop (lap + 1)) :=
    Or.inl (start.queue.trans (launch_queue_next p size available))
  obtain ⟨body⟩ := traverse valid size lap sourceCount marker (ports N |>.drop 1) s x
    start.cut start.memory placement (by rw [start.clock]; exact boundary_before_launch valid lap) window
    links endKey strong weak targetInPath
  have future : ∀ d ∈ body.last.pending, boundary p (lap + 1) < d.due := by
    intro d seen
    rw [body.queue] at seen
    exact (boundary_before_launch valid (lap + 1)).trans_le (launch_queue_future valid size d seen)
  obtain ⟨idle⟩ := quiet_stretch (p := p) (size := size) body.cut body.beforeBoundary.le future
  let run := body.run.append idle.run
  have endpointGain (i : Fin N) (port : Port) :
      idle.last.x i (.z port) = s.x i (.z port) + doseFor size marker i port :=
    (idle.gain i port).trans (body.gain i port)
  have recovery (i : Fin N) : idle.last.x i .b = s.x i .b :=
    (idle.recovery i).trans (body.recovery i)
  have endQueue := idle.queue.trans body.queue
  have endpoint := memory_after_lap (size := size) start.memory endpointGain recovery
  refine ⟨idle.last, run, ?_, ⟨idle.complete.1, endQueue, idle.cut, endpoint⟩⟩
  refine ⟨start.clock, idle.complete, start.queue, endQueue, idle.cut.ready, idle.cut.raw, ?_, ?_, ?_⟩
  · rw [show run.deliveries = body.run.deliveries by
      rw [Execution.deliveries_append, idle.deliveries, List.append_nil]]
    simpa only [← shape, admittedKeys, firingKeys, strongPrefix, marker] using body.deliveries
  · rw [show run.ledger.emissions = body.run.ledger.emissions by
      rw [Execution.emissions_append, idle.emissions, List.append_nil]]
    simpa only [← shape, firingKeys, strongPrefix, marker] using body.emissions
  · intro i port
    have balance := run.gain_balance i port
    rw [endpointGain] at balance
    have eq : run.ledger.error i port = doseFor size marker i port := by linarith
    exact eq


private theorem rail_of_memory {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {lap : Nat} {s : Snapshot N} (memory : MemoryAt p size lap s) : BelowRail s.x := by
  constructor
  · intro i port
    change s.x i (.z port) < Real.log 4
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    rcases address : PortAt size i port with _ | key
    · have amplitude : p.ring.amplitude size i port = 1 := by
        unfold PortAt at address
        unfold NativeRing.Parameters.amplitude
        split at address
        · contradiction
        · split at address
          · contradiction
          · split <;> simp_all
      rw [memory.1]
      norm_num [writesAt, address, NativeRing.prepared, amplitude]
    · obtain ⟨rfl, rfl⟩ := (portAt_eq size i port key).mp address
      rw [memory_gain (size := size) memory key]
      have upper := (checked_native_strong valid key).2
      have bound : (earned p lap key : ℝ) ≤ planned p key := by exact_mod_cast earned_bound p lap key
      apply lt_of_le_of_lt _ (by norm_num : (2 : ℝ) < 4)
      exact (Real.exp_le_exp.mpr (by linarith)).trans upper
  · intro i
    rw [memory.2]
    norm_num [NativeRing.prepared]

private theorem memory_frozen {p : Parameters N} {size : 2 ≤ N} {lap : Nat} {s : Snapshot N}
    (full : (trainingOrder p).length ≤ lap) (memory : MemoryAt p size lap s) :
    FrozenMemory p size s.x := by
  have counts (k : Input N) : earned p lap k = planned p k := by
    rw [earned, List.take_of_length_le full, total_count]
  refine ⟨?_, memory.2⟩
  intro i port
  rw [memory.1]
  unfold writesAt expectedWrites PortAt
  split
  · simp [counts, planned, planFor]
  · split
    · simp [counts, planned, planFor]
    · rfl

private theorem at_boundary_frozen {p : Parameters N} (valid : p.Valid)
    {size : 2 ≤ N} {lap count : Nat} {s : Snapshot N}
    (start : LapBoundary p size count lap s) (late : freezeTime p ≤ s.time) :
    FrozenMemory p size s.x := by
  rw [start.clock, freezeTime] at late
  exact memory_frozen ((boundary_mono valid).le_iff_le.mp late) start.memory

private theorem initial_boundary {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N) (count : Nat) :
    LapBoundary p size count 0 (prepared p size count) := by
  have memory : MemoryAt p size 0 (prepared p size count) := by
    refine ⟨?_, fun _ => rfl⟩
    intro i port
    have none (k : Input N) : earned p 0 k = 0 := rfl
    cases address : PortAt size i port <;> simp [prepared, writesAt, address, none]
  have rail := rail_of_memory valid size memory
  refine ⟨rfl, rfl, ⟨?_, ?_, ?_, fun _ _ => rfl⟩, memory⟩
  · refine ⟨?_, fun i port => (rail.1 i port).le, ?_, ?_⟩
    · intro i
      norm_num [prepared, NativeRing.prepared, UpperRegion, auxUpper]
    · intro i
      norm_num [prepared, NativeRing.prepared]
    · intro i
      norm_num [prepared, NativeRing.prepared]
  · intro i p t active
    cases active
  · intro i
    refine ⟨rfl, by norm_num [prepared, NativeRing.prepared], by norm_num [prepared, NativeRing.prepared],
      fun q => ⟨rfl, by norm_num [prepared, NativeRing.prepared, RestBand]⟩⟩

private structure Between (s u : Snapshot N) (t : ℝ) (x : Values N) : Prop where
  fromStart : s.time ≤ t
  upToEnd : t ≤ u.time
  gain : ∀ i q, s.x i (.z q) ≤ x i (.z q) ∧ x i (.z q) ≤ u.x i (.z q)
  recovery : ∀ i, s.x i .b ≤ x i .b ∧ x i .b ≤ u.x i .b
  atEnd : t = u.time → x = u.x

private theorem flow_memory_bounds {s u : Snapshot N} (f : Flow (nativeParameters N) s u) (t : ℝ)
    (inside : t ∈ Set.Icc s.time u.time) : Between s u t (f.path t) := by
  have gainLo := fun i q => f.gain_nondecreasing box i q t inside
  have recLo := fun i => f.recovery_nondecreasing box i t inside
  refine ⟨inside.1, inside.2, fun i q => ⟨gainLo i q, ?_⟩, fun i => ⟨recLo i, ?_⟩,
    by intro eq; rw [eq, f.final]⟩
  · by_cases endDate : t = u.time
    · rw [endDate, f.final]
    · let rest := f.suffix inside.1 (lt_of_le_of_ne inside.2 endDate)
      exact (rest.gain_nondecreasing box i q u.time ⟨inside.2, le_rfl⟩).trans_eq
        (congrFun (congrFun f.final i) (.z q))
  · by_cases endDate : t = u.time
    · rw [endDate, f.final]
    · let rest := f.suffix inside.1 (lt_of_le_of_ne inside.2 endDate)
      exact (rest.recovery_nondecreasing box i u.time ⟨inside.2, le_rfl⟩).trans_eq
        (congrFun (congrFun f.final i) .b)

private theorem run_memory_bounds {r : Router N} {s u : Snapshot N}
    (e : Execution (nativeParameters N) r s u) :
    e.AllStates (fun v => Between s u v.time v.x) ∧
      e.AllFlows (fun {v w} f => ∀ t ∈ Set.Icc v.time w.time, Between s u t (f.path t)) := by
  induction e with
  | nil => exact ⟨⟨le_rfl, le_rfl, fun _ _ => ⟨le_rfl, le_rfl⟩, fun _ => ⟨le_rfl, le_rfl⟩,
      fun _ => rfl⟩, trivial⟩
  | @cons s v u move tail ih =>
    let first : Execution (nativeParameters N) r s v := .cons move (.nil _)
    let whole := first.append tail
    have weaken {t : ℝ} {x : Values N} (h : Between v u t x) : Between s u t x :=
      ⟨first.time_monotone.trans h.fromStart, h.upToEnd,
        fun i q => ⟨(first.gain_nondecreasing box i q).trans (h.gain i q).1, (h.gain i q).2⟩,
        fun i => ⟨(first.recovery_nondecreasing box i).trans (h.recovery i).1, (h.recovery i).2⟩,
        h.atEnd⟩
    have head : Between s u s.time s.x :=
      ⟨le_rfl, whole.time_monotone, fun i q => ⟨le_rfl, whole.gain_nondecreasing box i q⟩,
        fun i => ⟨le_rfl, whole.recovery_nondecreasing box i⟩,
        fun eq => (whole.zero_duration_continuous eq.symm).symm⟩
    refine ⟨⟨head, tail.allStates_mono (fun _ => weaken) ih.1⟩, ?_⟩
    have rest := tail.allFlows_mono (fun _ h t seen => weaken (h t seen)) ih.2
    cases move with
    | jump => exact rest
    | flow f =>
      refine ⟨fun t seen => ?_, rest⟩
      have b := flow_memory_bounds f t seen
      refine ⟨b.fromStart, b.upToEnd.trans tail.time_monotone, ?_, ?_, ?_⟩
      · intro i q
        exact ⟨(b.gain i q).1, (b.gain i q).2.trans (tail.gain_nondecreasing box i q)⟩
      · intro i
        exact ⟨(b.recovery i).1, (b.recovery i).2.trans (tail.recovery_nondecreasing box i)⟩
      · intro eq
        have same : v.time = u.time := le_antisymm tail.time_monotone (eq ▸ b.upToEnd)
        exact (b.atEnd (eq.trans same.symm)).trans (tail.zero_duration_continuous same.symm).symm

private def SafeAt (p : Parameters N) (size : 2 ≤ N) (time : ℝ) (x : Values N) : Prop :=
  BelowRail x ∧ (freezeTime p ≤ time → FrozenMemory p size x) ∧
  ∀ i, x i .b = (NativeRing.prepared p.ring size).x i .b

private def SafeDuring (p : Parameters N) (size : 2 ≤ N) {s u : Snapshot N} (run : Run p size s u) : Prop :=
  run.AllStates (fun v => SafeAt p size v.time v.x) ∧
  run.AllFlows (fun {v w} f => ∀ t ∈ Set.Icc v.time w.time, SafeAt p size t (f.path t))

private theorem safe_segment {p : Parameters N} (size : 2 ≤ N) {s u : Snapshot N} (run : Run p size s u)
    (rail : BelowRail u.x) (before : freezeTime p ≤ s.time ∨ u.time ≤ freezeTime p)
    (head : freezeTime p ≤ s.time → FrozenMemory p size s.x)
    (tail : freezeTime p ≤ u.time → FrozenMemory p size u.x)
    (recStart : ∀ i, s.x i .b = (NativeRing.prepared p.ring size).x i .b)
    (recEnd : ∀ i, u.x i .b = (NativeRing.prepared p.ring size).x i .b) : SafeDuring p size run := by
  have point {t : ℝ} {x : Values N} (b : Between s u t x) : SafeAt p size t x := by
    have recovery (i : Fin N) : x i .b = (NativeRing.prepared p.ring size).x i .b :=
      le_antisymm ((b.recovery i).2.trans_eq (recEnd i)) ((recStart i).symm.le.trans (b.recovery i).1)
    refine ⟨⟨fun i q => (b.gain i q).2.trans_lt (rail.1 i q),
      fun i => (b.recovery i).2.trans_lt (rail.2 i)⟩, ?_, recovery⟩
    intro hit
    have last := tail (hit.trans b.upToEnd)
    rcases before with late | early
    · have first := head late
      exact ⟨fun i q => le_antisymm ((b.gain i q).2.trans_eq (last.1 i q))
        ((first.1 i q).symm.le.trans (b.gain i q).1), recovery⟩
    · have date : t = u.time := le_antisymm b.upToEnd (early.trans hit)
      exact (b.atEnd date).symm ▸ last
  have path := run_memory_bounds run
  exact ⟨run.allStates_mono (fun _ => point) path.1,
    run.allFlows_mono (fun _ h t seen => point (h t seen)) path.2⟩

private theorem safe_append {p : Parameters N} {size : 2 ≤ N} {s v u : Snapshot N}
    {a : Run p size s v} {b : Run p size v u} (A : SafeDuring p size a) (B : SafeDuring p size b) :
    SafeDuring p size (a.append b) :=
  ⟨(a.allStates_append b _).2 ⟨A.1, B.1⟩, (a.allFlows_append b _).2 ⟨A.2, B.2⟩⟩

private theorem safe_prefix {p : Parameters N} {size : 2 ≤ N} {s u v : Snapshot N}
    {run : Run p size s u} {cut : Run p size s v} (hprefix : run.IsPrefix cut)
    (safe : SafeDuring p size run) : SafeDuring p size cut := by
  induction hprefix with
  | nil run => exact ⟨run.allStates_initial safe.1, trivial⟩
  | flowCut f rest ht hend =>
    exact ⟨⟨safe.1.1, safe.2.1 _ ⟨ht.le, hend⟩⟩,
      ⟨fun t seen => safe.2.1 t ⟨seen.1, seen.2.trans hend⟩, trivial⟩⟩
  | step move rest cut link ih =>
    cases move with
    | jump =>
      obtain ⟨states, flows⟩ := ih ⟨safe.1.2, safe.2⟩
      exact ⟨⟨safe.1.1, states⟩, flows⟩
    | flow f =>
      obtain ⟨states, flows⟩ := ih ⟨safe.1.2, safe.2.2⟩
      exact ⟨⟨safe.1.1, states⟩, ⟨safe.2.1, flows⟩⟩


private theorem safe_lap {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {sourceCount lap : Nat} {s u : Snapshot N} (run : Run p size s u)
    (head : LapBoundary p size sourceCount lap s) (tail : LapBoundary p size sourceCount (lap + 1) u) :
    SafeDuring p size run := by
  apply safe_segment size run (rail_of_memory valid size tail.memory) _
    (at_boundary_frozen valid head) (at_boundary_frozen valid tail) head.memory.2 tail.memory.2
  by_cases passed : (trainingOrder p).length ≤ lap
  · exact Or.inl ((boundary_mono valid).monotone passed |>.trans_eq head.clock.symm)
  · exact Or.inr (tail.clock.trans_le ((boundary_mono valid).monotone (show lap + 1 ≤ _ by omega)))

private theorem safe_idle {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    {sourceCount lap : Nat} {s : Snapshot N} {T : ℝ}
    (head : LapBoundary p size sourceCount lap s)
    (idle : QuietStretch p size s T) (before : T < launchDate p lap) :
    SafeDuring p size idle.run := by
  have mem : MemoryAt p size lap idle.last :=
    memory_preserved (size := size) head.memory idle.gain idle.recovery
  have advance : (trainingOrder p).length ≤ lap ∨ idle.last.time < freezeTime p := by
    by_cases trained : (trainingOrder p).length ≤ lap
    · exact Or.inl trained
    · exact Or.inr (idle.complete.1.trans_lt
        (before.trans ((boundary_after_launch p lap).trans_le
          ((boundary_mono valid).monotone (show lap + 1 ≤ _ by omega)))))
  apply safe_segment size idle.run (rail_of_memory valid size mem) _
    (at_boundary_frozen valid head) _ head.memory.2 mem.2
  · exact advance.imp (fun done => ((boundary_mono valid).monotone done).trans_eq head.clock.symm) le_of_lt
  · intro seen
    rcases advance with done | earlier
    · exact memory_frozen done mem
    · exact (not_lt_of_ge seen earlier).elim

private structure Observed (p : Parameters N) (size : 2 ≤ N) (sourceCount lap : Nat)
    (s : Snapshot N) (T : ℝ) where
  last : Snapshot N
  run : Run p size s last
  complete : CompleteThrough run T
  safe : SafeDuring p size run
  laps : ∀ k, lap ≤ k → boundary p (k + 1) ≤ T →
    ∃ (start stop : Snapshot N)
      (before : Run p size s start) (during : Run p size start stop) (after : Run p size stop last),
      run = before.append (during.append after) ∧ SettledLap p size sourceCount k during

set_option maxHeartbeats 1500000 in
private theorem observe_from {p : Parameters N} (valid : p.Valid) (size : 2 ≤ N)
    (sourceCount : Nat) (T : ℝ) (completeCalendar : T < launchDate p sourceCount)
    (lap : Nat) (s : Snapshot N) (start : LapBoundary p size sourceCount lap s) (time : s.time ≤ T) :
    Nonempty (Observed p size sourceCount lap s T) := by
  suffices inductionOn : ∀ remaining lap (s : Snapshot N),
      sourceCount - lap = remaining → LapBoundary p size sourceCount lap s → s.time ≤ T →
        Nonempty (Observed p size sourceCount lap s T) by
    exact inductionOn _ lap s rfl start time
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro lap s measure start time
    by_cases idle : T < launchDate p lap
    · have future : ∀ d ∈ s.pending, T < d.due := by
        intro d present
        rw [start.queue] at present
        exact idle.trans_le (launch_queue_future valid size d present)
      obtain ⟨wait⟩ := quiet_stretch (p := p) (size := size) start.cut time future
      refine ⟨⟨wait.last, wait.run, wait.complete, safe_idle valid size start wait idle, ?_⟩⟩
      intro k lower done
      exact (not_lt_of_ge
        (((boundary_mono valid).monotone (Nat.succ_le_succ lower)).trans done)
        (idle.trans (boundary_after_launch p lap))).elim
    · have available : lap < sourceCount :=
        (launch_mono valid).lt_iff_lt.mp ((le_of_not_gt idle).trans_lt completeCalendar)
      obtain ⟨next, head, settled, boundary⟩ := next_lap valid size start available
      have safe := safe_lap valid size head start boundary
      by_cases inside : T < NativePeriodicRing.boundary p (lap + 1)
      · obtain ⟨last, cut, comparison, complete⟩ := head.complete_prefix_at T time
          (inside.trans_eq boundary.clock.symm)
        refine ⟨⟨last, cut, complete, safe_prefix (size := size) comparison safe, ?_⟩⟩
        intro k lower done
        exact (not_lt_of_ge
          (((boundary_mono valid).monotone (Nat.succ_le_succ lower)).trans done) inside).elim
      · have less : sourceCount - (lap + 1) < remaining := by rw [← measure]; omega
        have room : next.time ≤ T := boundary.clock.trans_le (le_of_not_gt inside)
        obtain ⟨tail⟩ := ih _ less (lap + 1) next rfl boundary room
        refine ⟨⟨tail.last, head.append tail.run, tail.complete, safe_append safe tail.safe, ?_⟩⟩
        intro k lower done
        by_cases here : k = lap
        · subst k
          exact ⟨s, next, .nil _, head, tail.run, rfl, settled⟩
        · have after : lap + 1 ≤ k := by omega
          obtain ⟨v, w, pre, during, post, split, cert⟩ := tail.laps k after done
          refine ⟨v, w, head.append pre, during, post, ?_, cert⟩
          exact (congrArg (fun suffix => head.append suffix) split).trans
            (Execution.append_assoc head pre (during.append post)).symm

private theorem mark_nonneg_for_run {p : Parameters N} {size : 2 ≤ N} {s u : Snapshot N}
    (e : Run p size s u) (i : Fin N) (port : Port) : 0 ≤ e.ledger.mark i port := by
  induction e with
  | nil => exact le_rfl
  | cons step rest ih =>
    change 0 ≤ step.ledger.mark i port + rest.ledger.mark i port
    cases step with
    | jump j => simpa only [Move.ledger, j.mark_zero, zero_add] using ih
    | flow f =>
      exact add_nonneg (intervalIntegral.integral_nonneg f.positive.le
        (fun t seen => f.mark_act_nonnegative box i port seen)) ih

/-- A complete native execution at every observed horizon of every
checked periodic ring, with the certified integral doses and frozen gains. -/
theorem native_periodic_ring_refinement : NativePeriodicRingRefinement := by
  intro N p valid size sourceCount T nonnegative calendar
  let start := prepared p size sourceCount
  obtain ⟨trace⟩ := observe_from valid size sourceCount T calendar 0 start
    (initial_boundary valid size sourceCount) nonnegative
  have endpoint := trace.run.allStates_final trace.safe.1
  have noRecovery (i : Fin N) : trace.run.ledger.recovery i = 0 := by
    have balance := trace.run.recovery_balance i
    rw [endpoint.2.2 i] at balance
    change (NativeRing.prepared p.ring size).x i .b =
      (NativeRing.prepared p.ring size).x i .b + trace.run.ledger.recovery i at balance
    linarith
  have noMark (i : Fin N) (port : Port) : trace.run.ledger.mark i port = 0 := by
    have integrated : (∑ q : Port, trace.run.ledger.mark i q) = 0 := by
      rw [← trace.run.recovery_sum_marks, noRecovery]
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun q : Port => trace.run.ledger.mark i q)
      (fun q _ => mark_nonneg_for_run trace.run i q) (Finset.mem_univ port)
    exact le_antisymm (h.trans_eq integrated) (mark_nonneg_for_run trace.run i port)
  refine ⟨trace.last, trace.run, trace.complete, ?_, ?_, noMark, noRecovery,
    fun k done => trace.laps k (Nat.zero_le k) done, ?_⟩
  · exact trace.run.allStates_mono (fun _ h => ⟨h.1, h.2.1⟩) trace.safe.1
  · exact trace.run.allFlows_mono (fun _ h t ht => ⟨(h t ht).1, (h t ht).2.1⟩) trace.safe.2
  · intro frozen i port
    have lastFrozen := endpoint.2.1 (trace.complete.1.symm ▸ frozen)
    have balance := trace.run.gain_balance i port
    rw [lastFrozen.1] at balance
    change (NativeRing.prepared p.ring size).x i (.z port) + (3 / 5 : ℝ) * expectedWrites p size i port =
      (NativeRing.prepared p.ring size).x i (.z port) + trace.run.ledger.error i port at balance
    linarith

end NetworkStability.NativePeriodicRing
