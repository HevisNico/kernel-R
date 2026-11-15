import LaunchWave
import ReceiptWave

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid NativeStrong

private theorem receipt_after_fast_cut {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    launchDate p + 19 / 10 < receiptDate p i := by
  have h := (of_decide_eq_true accepted : p.Valid).2.2.2.2.1 i
  have delay : (8 / 5 : ℚ) < p.delay i := by linarith
  have bound : (8 / 5 : ℝ) < (p.delay i : ℝ) := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr delay
  unfold receiptDate
  linarith [(scalar_latency accepted i).1]

private theorem launch_receipt_order {p : Parameters N} (accepted : p.check = true) :
    ((List.finRange N).map (fun i => (⟨p.successor i, 2, receiptDate p i⟩ : Delivery N))).Perm
      ((List.finRange N).map (fun i => ⟨i, 2, receiptDate p (sourceOf accepted i)⟩)) := by
  classical
  let source := sourceOf accepted
  have injective : Function.Injective source := by
    intro i j eq
    have hw := congrArg p.successor eq
    simpa only [source, sourceOf_receives] using hw
  have onto (i : Fin N) : source (p.successor i) = i := by
    apply (of_decide_eq_true accepted : p.Valid).2.2.2.1.1
    exact sourceOf_receives accepted (p.successor i)
  have perm : ((List.finRange N).map source).Perm (List.finRange N) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange N).map injective)
      (List.nodup_finRange N)).mpr
    intro i
    refine ⟨fun _ => List.mem_finRange i, fun _ => ?_⟩
    exact List.mem_map.mpr ⟨p.successor i, List.mem_finRange _, onto i⟩
  have ordered := perm.symm.map (fun i => (⟨p.successor i, 2, receiptDate p i⟩ : Delivery N))
  simp only [List.map_map, Function.comp_def, source, sourceOf_receives] at ordered
  exact ordered

/-- Continue all strong launch legs to a common cut strictly before any
receipt. By this cut every cell has left FAST and its RAW is inactive. -/
theorem launch_through_fast {p : Parameters N} (accepted : p.check = true) {ε : ℝ}
    (box : PhysicalBox (nativeParameters N) ε) (s : Snapshot N)
    (physical : PhysicalInvariant (nativeParameters N) s) (valid : RawValid s)
    (date : s.time = launchDate p) (prepared : ∀ i, PreparedSection s i)
    (charge : ∀ i, s.x i .q = launchCharge p i)
    (gain : ∀ i, Real.exp (s.x i (.z 0)) = launchAmplitude p i)
    (window : ∀ i, 9 / 5 ≤ Real.exp (s.x i (.z 0)) ∧ Real.exp (s.x i (.z 0)) ≤ 2)
    (recovery : ∀ i, s.x i .b = 9 / 50)
    (active : ∀ i, s.raw i 0 = some s.time)
    (other : ∀ i q, q ≠ 0 → s.raw i q = none) (empty : s.pending = []) :
    ∃ (u : Snapshot N) (run : Execution (nativeParameters N) (router p) s u),
      u.time = launchDate p + 19 / 10 ∧ run.deliveries = [] ∧
      (∀ i, run.emissionTimes i = [launchDate p + latency p i]) ∧
      u.pending.Perm ((List.finRange N).map (fun i => ⟨i, 2, receiptDate p (sourceOf accepted i)⟩)) ∧
      ∀ i, u.main i = .slow ∧
        u.x i .q = (1 / 4) * Real.exp (-(9 / 50) * (u.time - receiverFastEnd p (sourceOf accepted i))) ∧
        u.x i .b = 9 / 50 ∧ (∀ q, u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧
        (∀ q, u.raw i q = none) ∧ (∀ q, u.x i (.z q) = s.x i (.z q)) := by
  classical
  let T := launchDate p + 19 / 10
  have localLeg (i : Fin N) :
      ∃ (u : Snapshot 1) (run : Execution (fun _ => nativeParameters N i)
        (EmptyRouter 1) (localView s i) u),
        u.time = T ∧ run.ledger.emissions = [(0, launchDate p + latency p i)] ∧
        run.deliveries = [] ∧ u.main 0 = .slow ∧
        u.x 0 .q = (1 / 4) * Real.exp (-(9 / 50) * (u.time - receiverFastEnd p (sourceOf accepted i))) ∧
        u.x 0 .b = 9 / 50 ∧ (∀ q, u.aux 0 q = .ready ∧ RestBand (u.x 0 (.m q))) ∧
        (∀ q, u.raw 0 q = none) ∧ (∀ q, u.x 0 (.z q) = s.x i (.z q)) := by
    obtain ⟨leg⟩ := local_leg_exists ⟨box.1, fun _ q => box.2 i q⟩ (localView s i) 0
      ⟨fun _ => physical.region i, fun _ q => physical.gain_cap i q,
        fun _ => physical.recovery_cap i, fun _ => physical.reserve i⟩
      (fun _ q o h => valid i q o h)
      ⟨(prepared i).ready, (prepared i).charge, (prepared i).recovery, (prepared i).auxiliary⟩
      (window i) (active i) (other i) rfl
    let F := leg.cycle.fire
    let fast := leg.cycle.fast
    have fireDate : F.final.time = launchDate p + latency p i :=
      (local_launch_clock accepted i _ _ leg (charge i) (gain i) (window i).1 (prepared i).charge.2).trans
        (by rw [show (localView s i).time = launchDate p from date])
    have fastDate : fast.final.time = receiverFastEnd p (sourceOf accepted i) := by
      rw [fast.date, fireDate, receiverFastEnd, sourceOf_receives]
    have afterFast : fast.final.time < T := by
      rw [fast.date, fireDate]
      dsimp [T]
      linarith [(scalar_latency accepted i).2.1]
    have fastRecovery : fast.final.x 0 .b = 9 / 50 :=
      (fast.recovery 0).trans ((F.recovery_preserved 0).trans (recovery i))
    have fastGain (q : Port) : fast.final.x 0 (.z q) = s.x i (.z q) :=
      (fast.gains 0 q).trans (F.gain_preserved 0 q)
    have fastEmpty : fast.final.pending = [] := by
      rw [fast.pending, F.pending]
      rfl
    obtain ⟨u, slow, time, mode, qClock, b, z, aux, raw, _, hd, he, _⟩ :=
      slow_span_to_receipt (route := EmptyRouter 1) accepted (sourceOf accepted i) fast.final T
        afterFast (receipt_after_fast_cut accepted _).le fast.main_slow
        (by rw [fastDate]; simp [fast.charge]) fastRecovery
        (fun q => ⟨fast.auxiliary 0 q, fast.rest q⟩) (fast.raw_none 0)
        (by simp [fastEmpty])
    let run := F.execution.append (fast.execution.append slow)
    refine ⟨u, run, time, ?_, ?_, mode, qClock, b, aux, raw, fun q => (z q).trans (fastGain q)⟩
    · rw [Execution.emissions_append, Execution.emissions_append, F.emissions, fast.emissions, he, fireDate]
      rfl
    · rw [Execution.deliveries_append, Execution.deliveries_append, F.deliveries, fast.deliveries, hd]
      rfl
  choose cuts legs time fires delivered mode qClock b aux raw z using localLeg
  obtain ⟨out, body, noArrivals, queued, fireClocks, _, _, _, _, _⟩ :=
    synchronized_ledger (route := router p) (localView s) cuts legs (fun _ => date) time
      (by dsimp [T]; linarith) delivered [] (by simp)
      (fun i e mem child childMem => by
        rw [fires, List.mem_singleton] at mem
        rw [mem, router_launch accepted] at childMem
        rcases List.mem_singleton.mp childMem with rfl
        exact (receipt_after_fast_cut accepted i).le)
  have begins : assemble (launchDate p) (localView s) [] = s := by
    rw [← date, ← empty]
    cases s
    rfl
  have exactFires (i : Fin N) : body.emissionTimes i = [launchDate p + latency p i] := by
    simp only [fireClocks, fires, List.map_cons, List.map_nil]
  have timeOf (e : Fin N × ℝ) (h : e ∈ body.ledger.emissions) :
      e.2 = launchDate p + latency p e.1 := by
    have mem : e.2 ∈ body.emissionTimes e.1 := List.mem_map_of_mem
      (List.mem_filter.mpr ⟨h, by simp⟩)
    rw [exactFires, List.mem_singleton] at mem
    exact mem
  let token (i : Fin N) : Delivery N := ⟨p.successor i, 2, receiptDate p i⟩
  have routing : (body.ledger.emissions.flatMap (fun e => router p e.1 e.2)) =
      (body.ledger.emissions.map Prod.fst).map token := by
    rw [List.map_map]
    calc
      _ = body.ledger.emissions.flatMap (fun e => [token e.1]) := by
        apply List.flatMap_congr
        intro event mem
        rw [timeOf event mem, router_launch accepted]
        rfl
      _ = (body.ledger.emissions.map (token ∘ Prod.fst)).flatMap (fun d => [d]) :=
        (List.flatMap_map _ _ _).symm
      _ = _ := List.flatMap_singleton' _
  have perm := (emission_cell_perm exactFires).map token
  let run := body.cast_source begins.symm
  have led : run.ledger = body.ledger := body.cast_source_ledger begins.symm
  refine ⟨_, run, rfl, (body.cast_source_deliveries begins.symm).trans noArrivals, ?_, ?_, ?_⟩
  · intro i
    change ((run.ledger.emissions.filter fun e => e.1 = i).map Prod.snd) = _
    rw [led]
    exact exactFires i
  · change out.Perm _
    rw [queued, List.nil_append, routing]
    exact perm.trans (launch_receipt_order accepted)
  · intro i
    refine ⟨mode i, ?_, b i, aux i, raw i, z i⟩
    rw [qClock i, time i]
    rfl

/-- From the post-intake launch section to the common horizon, every
launched child is consumed, and the final quiet suffix is complete. -/
theorem launch_receipt_chain {p : Parameters N} (accepted : p.check = true) {ε : ℝ}
    (box : PhysicalBox (nativeParameters N) ε) (s : Snapshot N)
    (physical : PhysicalInvariant (nativeParameters N) s) (valid : RawValid s)
    (date : s.time = launchDate p) (prepared : ∀ i, PreparedSection s i)
    (charge : ∀ i, s.x i .q = launchCharge p i)
    (gain : ∀ i, Real.exp (s.x i (.z 0)) = launchAmplitude p i)
    (window : ∀ i, 9 / 5 ≤ Real.exp (s.x i (.z 0)) ∧ Real.exp (s.x i (.z 0)) ≤ 2)
    (recovery : ∀ i, s.x i .b = 9 / 50)
    (active : ∀ i, s.raw i 0 = some s.time)
    (other : ∀ i q, q ≠ 0 → s.raw i q = none) (empty : s.pending = []) :
    ∃ (cut last : Snapshot N)
      (launch : Execution (nativeParameters N) (router p) s cut)
      (receipt : Execution (nativeParameters N) (router p) cut last),
      cut.time = launchDate p + 19 / 10 ∧
      CompleteThrough (launch.append receipt) (horizon p) ∧ last.pending = [] ∧
      launch.deliveries = [] ∧ receipt.ledger.emissions = [] ∧
      (∀ i, launch.emissionTimes i = [launchDate p + latency p i]) ∧
      cut.pending.Perm receipt.deliveries ∧
      (∀ i, cut.x i .b = 9 / 50) ∧
      ∀ i, ReadyCoordinates last i ∧ (∀ q, last.raw i q = none) ∧
        receipt.ledger.recovery i = 1 / 10 ∧
        ∀ q, last.x i (.z q) = s.x i (.z q) ∧
          receipt.ledger.mark i q = if q = 2 then 1 / 10 else 0 := by
  obtain ⟨cut, launch, cutDate, launched, fires, queue, sections⟩ :=
    launch_through_fast accepted box s physical valid date prepared charge gain window recovery active other empty
  obtain ⟨last, receipt, complete, finalQueue, taken, quiet, doses⟩ :=
    protected_receipt_wave accepted box cut (launch.physical_invariant box physical) (launch.raw_valid valid)
      (fun i => by rw [cutDate]; exact receipt_after_fast_cut accepted _)
      (fun i => (sections i).1) (fun i => (sections i).2.1) (fun i => (sections i).2.2.1)
      (fun i => (sections i).2.2.2.1) (fun i => (sections i).2.2.2.2.1) queue
  refine ⟨cut, last, launch, receipt, cutDate, complete, finalQueue, launched, quiet, fires, taken,
    (fun i => (sections i).2.2.1), ?_⟩
  intro i
  obtain ⟨ready, inactive, recoveryDose, doses⟩ := doses i
  refine ⟨ready, inactive, recoveryDose, fun q => ⟨?_, (doses q).2⟩⟩
  have balance := receipt.gain_balance i q
  rw [(doses q).1, add_zero] at balance
  exact balance.trans ((sections i).2.2.2.2.2 q)

end NetworkStability.NativeMultiToken
