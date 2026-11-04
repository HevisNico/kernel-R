import KernelR.HybridCadenceHighCompletion

/-! A finite isolated cadence train from actual high FIREs and actual next
source arrivals. The first residual latency is retained; later rest inputs
use the same cell's proved exact-rest root. This is a local execution only. -/
namespace KernelR.Hybrid

structure LocalCadenceHighTrain (θ : Fin 1 → Parameters) (source : Snapshot 1)
    (count : ℕ) (later : List (Delivery 1)) where
  first : CadenceHighFire θ (fun _ _ => []) source 0 0
  final : Snapshot 1
  afterFirst : Execution θ (fun _ _ => []) first.final final
  afterFirst_transversal : afterFirst.ContactsTransversal
  execution : Execution θ (fun _ _ => []) source final
  contacts_transversal : execution.ContactsTransversal
  reconstruct : execution = first.execution.append afterFirst
  date : final.time = source.time + 4 * ((count : ℝ) + 1)
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = later
  gains : ∀ j q, final.x j (.z q) = source.x j (.z q)
  recovery : ∀ j, final.x j .b = source.x j .b
  emission_count : (execution.emissionTimes 0).length = count + 1
  calendar : execution.emissionTimes 0 = first.final.time ::
    (sourceTrain (0 : Fin 1) 0 (source.time + 4) 4 count).map
      (fun d => d.due + highRestLatency (Real.exp (source.x 0 (.z 0))))
  first_latency_le_rest : first.latency ≤ highRestLatency (Real.exp (source.x 0 (.z 0)))
  deliveries : execution.deliveries = sourceTrain 0 0 (source.time + 4) 4 count
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (source.time + 4 * ((count : ℝ) + 1))

theorem local_cadence_high_train_exists {θ ε} (hb : PhysicalBox θ ε) (source : Snapshot 1)
    (count : ℕ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ source) (hv : RawValid source)
    (hs : CadenceReadyCoordinates source 0 (8 / 25)) (hq : 1 / 10 ≤ source.x 0 .q)
    (hg : 16 / 5 ≤ Real.exp (source.x 0 (.z 0)) ∧ Real.exp (source.x 0 (.z 0)) ≤ 7 / 2)
    (hB : 37999 / 100000 ≤ source.x 0 .b ∧ source.x 0 .b ≤ 38001 / 100000)
    (hr : source.raw 0 0 = some source.time) (ho : ∀ q, q ≠ 0 → source.raw 0 q = none)
    (hqueue : source.pending = sourceTrain 0 0 (source.time + 4) 4 count ++ later)
    (hLater : ∀ d ∈ later, source.time + 4 * ((count : ℝ) + 1) < d.due) :
    Nonempty (LocalCadenceHighTrain θ source count later) := by
  induction count generalizing source with
  | zero =>
    have hPending : source.pending = later := by simpa [sourceTrain] using hqueue
    have hp : ∀ d ∈ source.pending, source.time + 4 ≤ d.due := by
      intro d hd
      rw [hPending] at hd
      simpa using (hLater d hd).le
    obtain ⟨fire⟩ := cadence_high_fire_exists hb source 0 hf hv hs hq hg hr ho hp
    obtain ⟨done⟩ := fire.high_completion_exists hb hs hB ho hp
    let execution := fire.execution.append done.execution
    have hTimes : execution.emissionTimes 0 = [fire.final.time] := by
      change (fire.execution.append done.execution).emissionTimes 0 = _
      rw [Execution.emissionTimes_append]
      have hFire : fire.execution.emissionTimes 0 = [fire.final.time] := by
        simp [Execution.emissionTimes,fire.emissions,fire.date]
      have hDone : done.execution.emissionTimes 0 = [] := by simp [Execution.emissionTimes,done.emissions]
      rw [hFire,hDone,List.append_nil]
    have hc := done.complete_if_strict_future (by
      intro d hd
      rw [done.pending,fire.pending,List.append_nil,hPending] at hd
      rw [done.date]
      simpa using hLater d hd)
    refine ⟨{
      first := fire, final := done.final, afterFirst := done.execution, execution := execution, reconstruct := rfl
      afterFirst_transversal := done.contacts_transversal
      contacts_transversal := by simp [execution, done.contacts_transversal]
      date := by simpa using done.date
      ready := done.ready, charge := done.charge, raw_none := done.raw_none
      pending := by rw [done.pending,fire.pending,List.append_nil,hPending]
      gains := fun j q => (done.gains j q).trans (fire.gain_preserved j q)
      recovery := fun j => (done.recovery j).trans (fire.recovery_preserved j)
      emission_count := by rw [hTimes]; rfl
      calendar := by rw [hTimes]; simp [sourceTrain]
      first_latency_le_rest := fire.latency_le_rest hq hg
      deliveries := by simp [execution,Execution.deliveries_append,fire.deliveries,done.deliveries,sourceTrain]
      physical := done.physical, raw_valid := done.raw_valid
      complete := by simpa only [CompleteThrough,done.date,Nat.cast_zero,zero_add,mul_one] using hc
    }⟩
  | succ count ih =>
    have hn : (0 : ℝ) ≤ count := Nat.cast_nonneg _
    have hp : ∀ d ∈ source.pending, source.time + 4 ≤ d.due := by
      intro d hd
      rw [hqueue] at hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
        change source.time + 4 ≤ source.time + 4 + 4 * (k.val : ℝ)
        nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
      · have h := hLater d hd
        push_cast at h
        linarith
    obtain ⟨fire⟩ := cadence_high_fire_exists hb source 0 hf hv hs hq hg hr ho hp
    obtain ⟨done⟩ := fire.high_completion_exists hb hs hB ho hp
    let tail := sourceTrain 0 0 (source.time + 8) 4 count ++ later
    have hHead : done.final.pending = [] ++ (⟨0,0,source.time + 4⟩ : Delivery 1) :: tail := by
      rw [done.pending,fire.pending,List.append_nil,hqueue,sourceTrain_succ]
      norm_num [tail]
      congr 1
      ring
    let nextSource : Snapshot 1 := {setRaw done.final 0 0 (some done.final.time) with pending := tail}
    let arrival : Jump (fun _ _ => []) done.final nextSource :=
      .arrive done.final ⟨0,0,source.time + 4⟩ [] tail hHead done.date.symm (done.raw_none 0 0)
    let entry : Execution θ (fun _ _ => []) done.final nextSource := .cons (.jump arrival) (.nil _)
    have hDate : nextSource.time = source.time + 4 := done.date
    have hGains (j : Fin 1) (q : Port) : nextSource.x j (.z q) = source.x j (.z q) :=
      (done.gains j q).trans (fire.gain_preserved j q)
    have hRec (j : Fin 1) : nextSource.x j .b = source.x j .b :=
      (done.recovery j).trans (fire.recovery_preserved j)
    have hCharge : nextSource.x 0 .q = 1 / 10 := done.charge
    have hCoords : CadenceReadyCoordinates nextSource 0 (8 / 25) :=
      ⟨(done.ready 0).ready,by rw [hCharge]; constructor <;> norm_num,(done.ready 0).auxiliary⟩
    have hRaw : nextSource.raw 0 0 = some nextSource.time := by simp [nextSource,setRaw]
    have hOther : ∀ q, q ≠ 0 → nextSource.raw 0 q = none := by
      intro q hq
      simp [nextSource,setRaw,hq,done.raw_none]
    have hQueue : nextSource.pending = sourceTrain 0 0 (nextSource.time + 4) 4 count ++ later := by
      change sourceTrain 0 0 (source.time + 8) 4 count ++ later = _
      rw [hDate]
      rw [show source.time + 4 + 4 = source.time + 8 by ring]
    obtain ⟨rest⟩ := ih nextSource (entry.physical_invariant hb done.physical) (entry.raw_valid done.raw_valid)
      hCoords (by rw [hCharge]) (by rw [hGains]; exact hg) (by rw [hRec]; exact hB) hRaw hOther hQueue
      (by intro d hd; rw [hDate]; have h := hLater d hd; push_cast at h; linarith)
    let afterFirst := done.execution.append (entry.append rest.execution)
    let execution := fire.execution.append afterFirst
    have hEntryEm : entry.ledger.emissions = [] := rfl
    have hEntryDel : entry.deliveries = [⟨0,0,source.time + 4⟩] := rfl
    have hTimes : execution.emissionTimes 0 = fire.final.time :: rest.execution.emissionTimes 0 := by
      change (fire.execution.append (done.execution.append (entry.append rest.execution))).emissionTimes 0 = _
      rw [Execution.emissionTimes_append,Execution.emissionTimes_append,Execution.emissionTimes_append]
      have hFire : fire.execution.emissionTimes 0 = [fire.final.time] := by
        simp [Execution.emissionTimes,fire.emissions,fire.date]
      have hDone : done.execution.emissionTimes 0 = [] := by simp [Execution.emissionTimes,done.emissions]
      have hEntry : entry.emissionTimes 0 = [] := by simp [Execution.emissionTimes,hEntryEm]
      rw [hFire,hDone,hEntry,List.nil_append,List.nil_append]
      rfl
    have hRestRoot : rest.first.final.time = source.time + 4 + highRestLatency (Real.exp (source.x 0 (.z 0))) := by
      rw [rest.first.date,rest.first.exact_rest_latency hCharge (by rw [hGains]; exact hg),hDate,hGains]
    have hHorizon : nextSource.time + 4 * ((count : ℝ) + 1) =
        source.time + 4 * (((count + 1 : ℕ) : ℝ) + 1) := by
      rw [hDate]
      push_cast
      ring
    refine ⟨{
      first := fire, final := rest.final, afterFirst := afterFirst, execution := execution, reconstruct := rfl
      afterFirst_transversal := by
        simp [afterFirst, entry, arrival, Execution.ContactsTransversal, Jump.ContactTransversal,
          done.contacts_transversal, rest.contacts_transversal]
      contacts_transversal := by
        simp [execution, afterFirst, entry, arrival, Execution.ContactsTransversal, Jump.ContactTransversal,
          done.contacts_transversal, rest.contacts_transversal]
      date := by rw [rest.date,hDate]; push_cast; ring
      ready := rest.ready, charge := rest.charge, raw_none := rest.raw_none, pending := rest.pending
      gains := fun j q => (rest.gains j q).trans (hGains j q)
      recovery := fun j => (rest.recovery j).trans (hRec j)
      emission_count := by rw [hTimes,List.length_cons,rest.emission_count]
      calendar := ?_, first_latency_le_rest := fire.latency_le_rest hq hg
      deliveries := ?_, physical := rest.physical, raw_valid := rest.raw_valid
      complete := by simpa only [CompleteThrough,hHorizon] using rest.complete
    }⟩
    · rw [hTimes,rest.calendar,hRestRoot,hDate,hGains,sourceTrain_succ]
      simp only [List.map_cons]
    · simp only [execution,afterFirst,Execution.deliveries_append,fire.deliveries,done.deliveries,
        hEntryDel,rest.deliveries,List.nil_append]
      rw [hDate,sourceTrain_succ]
      norm_num

end KernelR.Hybrid
