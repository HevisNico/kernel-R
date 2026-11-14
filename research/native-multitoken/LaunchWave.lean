import NativeMultiTokenMilestone
import SynchronizedProduct

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid NativeStrong Set

private theorem at_offset (q gain start offset : ℝ) :
    readyPulse q gain start (start + offset) = readyPulse q gain 0 offset := by
  simp only [readyPulse, add_sub_cancel_left, sub_zero]

private theorem local_launch_clock {p : Parameters N} (accepted : p.check = true)
    (i : Fin N) (s : Snapshot 1) (port : Port) {θ}
    (leg : LocalLeg θ s port) (charge : s.x 0 .q = launchCharge p i)
    (gain : Real.exp (s.x 0 (.z port)) = launchAmplitude p i)
    (lower : 9 / 5 ≤ Real.exp (s.x 0 (.z port))) (upper : s.x 0 .q ≤ 7 / 50) :
    leg.cycle.fire.final.time = s.time + latency p i := by
  let fire := leg.cycle.fire
  obtain ⟨early, late, root, _⟩ := scalar_latency accepted i
  rw [fire.date]
  apply readyPulse_root_unique (start := s.time) upper lower
  · exact ⟨by linarith [fire.early], by linarith [fire.deadline]⟩
  · exact ⟨by linarith, by linarith⟩
  · exact fire.response_root
  · rw [at_offset, charge, gain]
    exact root

private theorem launch_prefix {θ} {s : Snapshot 1} {port : Port} (leg : LocalLeg θ s port) :
    ∃ (cut : Snapshot 1) (run : Execution θ (EmptyRouter 1) s cut),
      leg.execution.IsPrefix run ∧ cut.time = s.time + 9 / 10 ∧ run.deliveries = [] ∧
      run.ledger.emissions = [(0, leg.cycle.fire.final.time)] := by
  obtain ⟨cut, run, pre, date⟩ := leg.execution.prefix_at (s.time + 9 / 10)
    (by linarith) (by rw [leg.date]; linarith)
  obtain ⟨tail, deliveries, emissions⟩ := pre.continuation
  rw [leg.deliveries] at deliveries
  have silent : tail.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event seen
    have all := List.mem_append_right run.ledger.emissions seen
    rw [← emissions, leg.emissions, List.mem_singleton] at all
    have later := (tail.emission_time_bounds event seen).1
    rw [date, all, leg.cycle.fire.date] at later
    linarith [leg.cycle.fire.deadline]
  refine ⟨cut, run, pre, date, (List.append_eq_nil_iff.mp deliveries.symm).1, ?_⟩
  rw [silent, List.append_nil, leg.emissions] at emissions
  exact emissions.symm

private theorem router_launch {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    router p i (launchDate p + latency p i) =
      [⟨p.successor i, 2, launchDate p + latency p i + (p.delay i : ℝ)⟩] := by
  obtain ⟨early, late, _, _⟩ := scalar_latency accepted i
  unfold router
  rw [ite_eq_left ⟨by linarith, by linarith⟩]

private theorem launch_child_future {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    launchDate p + 9 / 10 < launchDate p + latency p i + (p.delay i : ℝ) := by
  have d := (of_decide_eq_true accepted : p.Valid).2.2.2.2.1 i
  have lower : (8 / 5 : ℚ) < p.delay i := by linarith
  have realLower : (8 / 5 : ℝ) < (p.delay i : ℝ) := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr lower
  linarith [(scalar_latency accepted i).1]

private theorem emission_cell_perm {l : List (Fin N × ℝ)} {fire : Fin N → ℝ}
    (one : ∀ i, (l.filter (fun e => e.1 = i)).map Prod.snd = [fire i]) :
    (l.map Prod.fst).Perm (List.finRange N) := by
  classical
  apply List.perm_iff_count.mpr
  intro i
  have length : (l.filter (fun e => e.1 = i)).length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length (one i)
  rw [List.count_eq_length_filter, List.filter_map, List.length_map]
  have predicate : (fun e : Fin N × ℝ => (e.1 == i)) = (fun e => decide (e.1 = i)) := by
    funext e
    exact Bool.beq_eq_decide_eq _ _
  rw [Function.comp_def, predicate, length]
  exact (List.count_eq_one_of_mem (List.nodup_finRange N) (List.mem_finRange i)).symm

/-- Launch at the frozen calendar date, with all RAW pulses already admitted.
The common cut is after every launch FIRE and before any child is due. Each
isolated prefix belongs to the strong leg and the native product follows it. -/
theorem launch_wave {p : Parameters N} (accepted : p.check = true) {ε : ℝ}
    (box : PhysicalBox (nativeParameters N) ε) (s : Snapshot N)
    (physical : PhysicalInvariant (nativeParameters N) s) (valid : RawValid s)
    (date : s.time = launchDate p) (prepared : ∀ i, PreparedSection s i)
    (charge : ∀ i, s.x i .q = launchCharge p i)
    (gain : ∀ i, Real.exp (s.x i (.z 0)) = launchAmplitude p i)
    (window : ∀ i, 9 / 5 ≤ Real.exp (s.x i (.z 0)) ∧ Real.exp (s.x i (.z 0)) ≤ 2)
    (active : ∀ i, s.raw i 0 = some s.time)
    (other : ∀ i q, q ≠ 0 → s.raw i q = none) (empty : s.pending = []) :
    ∃ (u : Snapshot N) (run : Execution (nativeParameters N) (router p) s u),
      u.time = launchDate p + 9 / 10 ∧ run.deliveries = [] ∧
      (∀ i, run.emissionTimes i = [launchDate p + latency p i]) ∧
      u.pending = run.ledger.emissions.map (fun e => ⟨p.successor e.1, 2, e.2 + (p.delay e.1 : ℝ)⟩) ∧
      run.ledger.issued = N ∧ u.pending.length = N := by
  classical
  have localExists (i : Fin N) :
      Nonempty (LocalLeg (fun _ => nativeParameters N i) (localView s i) 0) := by
    refine local_leg_exists ⟨box.1, fun _ q => box.2 i q⟩ (localView s i) 0 ?_ ?_ ?_
      (window i) (active i) (other i) rfl
    · exact ⟨fun _ => physical.region i, fun _ q => physical.gain_cap i q,
        fun _ => physical.recovery_cap i, fun _ => physical.reserve i⟩
    · exact fun _ q o h => valid i q o h
    · exact ⟨(prepared i).ready, (prepared i).charge, (prepared i).recovery, (prepared i).auxiliary⟩
  let leg (i : Fin N) := Classical.choice (localExists i)
  have clock (i : Fin N) : (leg i).cycle.fire.final.time = launchDate p + latency p i :=
    (local_launch_clock accepted i _ _ (leg i) (charge i) (gain i)
      (window i).1 (prepared i).charge.2).trans (by rw [show (localView s i).time = launchDate p from date])
  have localPrefix (i : Fin N) := launch_prefix (leg i)
  choose cuts legs follows finish deliveries fires using localPrefix
  have cutDate (i : Fin N) : (cuts i).time = launchDate p + 9 / 10 :=
    (finish i).trans (by rw [show (localView s i).time = launchDate p from date])
  obtain ⟨out, body, noArrival, queue, emitted, count, _, _, _, _⟩ :=
    synchronized_ledger (route := router p) (localView s) cuts legs (fun _ => date) cutDate
      (by linarith) deliveries [] (by simp)
      (fun i e h d mem => by
        rw [fires i, List.mem_singleton] at h
        rw [h, clock i, router_launch accepted] at mem
        rcases List.mem_singleton.mp mem with rfl
        exact (launch_child_future accepted i).le)
  have start : assemble (launchDate p) (localView s) [] = s := by
    rw [← date, ← empty]
    cases s
    rfl
  let run := body.cast_source start.symm
  have ledger : run.ledger = body.ledger := body.cast_source_ledger start.symm
  have exactFires (i : Fin N) : body.emissionTimes i = [launchDate p + latency p i] := by
    simp only [emitted, fires, clock, List.map_cons, List.map_nil]
  have routeEach (e : Fin N × ℝ) (h : e ∈ body.ledger.emissions) :
      router p e.1 e.2 = [⟨p.successor e.1, 2, e.2 + (p.delay e.1 : ℝ)⟩] := by
    have mem : e.2 ∈ body.emissionTimes e.1 := List.mem_map_of_mem (f := Prod.snd)
      (List.mem_filter.mpr ⟨h, by simp⟩)
    rw [exactFires, List.mem_singleton] at mem
    rw [mem, router_launch accepted]
  let child (e : Fin N × ℝ) : Delivery N :=
    ⟨p.successor e.1, 2, e.2 + (p.delay e.1 : ℝ)⟩
  have routes : (body.ledger.emissions.flatMap fun e => router p e.1 e.2) =
      body.ledger.emissions.map child := by
    calc
      _ = body.ledger.emissions.flatMap (fun e => [child e]) :=
        List.flatMap_congr routeEach
      _ = (body.ledger.emissions.map child).flatMap (fun d => [d]) :=
        (List.flatMap_map child (fun d => [d]) _).symm
      _ = _ := List.flatMap_singleton' _
  have total : body.ledger.emissions.length = N := by
    have perm := emission_cell_perm (fun i => exactFires i)
    simpa using perm.length_eq
  refine ⟨_, run, rfl, (body.cast_source_deliveries start.symm).trans noArrival, ?_, ?_, ?_, ?_⟩
  · intro i
    change (((run.ledger.emissions).filter fun e => e.1 = i).map Prod.snd) = _
    rw [ledger]
    exact exactFires i
  · change out = _
    rw [ledger]
    exact queue.trans routes
  · rw [ledger, count, routes, List.length_map, total]
  · change out.length = _
    rw [queue, List.nil_append, routes, List.length_map, total]

end NetworkStability.NativeMultiToken
