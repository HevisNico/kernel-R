import KernelR.HybridLocalCadenceHighJitterTrain
import KernelR.HybridCadenceHighBudgetNextSource

/-! Separate full3/20-budget autonomous high trains with received gaps3.7.
Every response and next input is constructed. The first carried latency and
all subsequent own exact-rest latencies remain distinct in the calendar. -/
namespace KernelR.Hybrid

def CadenceHighBudgetSchedule (source : ℝ) (dates : List ℝ) (terminal : ℝ) : Prop :=
  match dates with
  | [] => source + 37 / 10 ≤ terminal
  | H :: later => source + 37 / 10 ≤ H ∧ CadenceHighBudgetSchedule H later terminal

theorem CadenceHighBudgetSchedule.source_lower {S dates T}
    (h : CadenceHighBudgetSchedule S dates T) : ∀ H ∈ dates, S + 37 / 10 ≤ H := by
  induction dates generalizing S with
  | nil => simp
  | cons H later ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x; exact h.1
    · have hh := ih h.2 x hx
      linarith [h.1]

theorem local_cadence_high_full_budget_train_exists {θ ε} (hb : PhysicalBox θ ε)
    (source : Snapshot 1) (p : Port) (dates : List ℝ) (terminal : ℝ)
    (hf : PhysicalInvariant θ source) (hv : RawValid source)
    (hs : CadenceReadyCoordinates source 0 (8 / 25)) (hq : 1 / 10 ≤ source.x 0 .q)
    (hg : 16 / 5 ≤ Real.exp (source.x 0 (.z p)) ∧ Real.exp (source.x 0 (.z p)) ≤ 7 / 2)
    (hB : 37999 / 100000 ≤ source.x 0 .b ∧ source.x 0 .b ≤ 38001 / 100000)
    (hr : source.raw 0 p = some source.time) (ho : ∀ q, q ≠ p → source.raw 0 q = none)
    (hqueue : source.pending = dates.map (fun H => (⟨0,p,H⟩ : Delivery 1)))
    (hSchedule : CadenceHighBudgetSchedule source.time dates terminal) :
    Nonempty (LocalCadenceHighJitterTrain θ source p dates terminal) := by
  induction dates generalizing source with
  | nil =>
    obtain ⟨r⟩ := cadence_high_full_budget_ready_at_exists hb source p terminal [] hf hv hs hq hg hB hr ho
      hqueue hSchedule (by simp)
    have hTimes : r.execution.emissionTimes 0 = [r.fire.final.time] := by
      simp [Execution.emissionTimes,r.emissions]
    have hFuture : ∀ d ∈ r.final.pending, terminal < d.due := by rw [r.pending]; simp
    have hComplete : CompleteThrough r.execution terminal := by
      refine ⟨r.date,?_,hFuture⟩
      intro u
      apply BeforeGuards.no_jump
      · constructor
        · intro j; rw [(r.ready j).ready]; linarith [(r.ready j).charge.2]
        · intro j q; rw [((r.ready j).auxiliary q).1]; linarith [((r.ready j).auxiliary q).2.2]
      · intro j q origin hraw; rw [r.raw_none j q] at hraw; contradiction
      · intro d hd
        rw [r.date]
        exact hFuture d hd
    exact ⟨{
      first := r.fire, final := r.final, execution := r.execution, date := r.date
      ready := r.ready, charge := r.charge, raw_none := r.raw_none, pending := r.pending
      gains := r.gains, recovery := r.recovery
      emission_count := by rw [hTimes]; rfl
      calendar := by rw [hTimes]; rfl
      first_latency_le_rest := r.fire.latency_le_rest hq hg
      deliveries := r.deliveries, physical := r.physical, raw_valid := r.raw_valid, complete := hComplete
    }⟩
  | cons H dates ih =>
    let later := dates.map (fun t => (⟨0,p,t⟩ : Delivery 1))
    have hLater : ∀ d ∈ later, H < d.due := by
      intro d hd
      obtain ⟨time,ht,rfl⟩ := List.mem_map.mp hd
      change H < time
      linarith [hSchedule.2.source_lower time ht]
    obtain ⟨r⟩ := cadence_high_full_budget_next_source_exists hb source p H later hf hv hs hq hg hB hr ho
      hqueue hSchedule.1 hLater
    have hsRest : CadenceReadyCoordinates r.final 0 (8 / 25) := by
      refine ⟨(r.ready 0).ready,⟨(r.ready 0).charge.1,?_⟩,(r.ready 0).auxiliary⟩
      rw [r.charge]
      norm_num
    have hgRest : 16 / 5 ≤ Real.exp (r.final.x 0 (.z p)) ∧ Real.exp (r.final.x 0 (.z p)) ≤ 7 / 2 := by
      rw [r.gains]
      exact hg
    obtain ⟨rest⟩ := ih r.final r.physical r.raw_valid hsRest (by rw [r.charge]) hgRest
      (by rw [r.recovery]; exact hB) (by rw [r.date]; exact r.raw_active) r.raw_other r.pending
      (by rw [r.date]; exact hSchedule.2)
    let execution := r.execution.append rest.execution
    have hFirst : r.execution.emissionTimes 0 = [r.readyAt.fire.final.time] := by
      simp [Execution.emissionTimes,r.emissions]
    have hTimes : execution.emissionTimes 0 = r.readyAt.fire.final.time :: rest.execution.emissionTimes 0 := by
      rw [Execution.emissionTimes_append,hFirst]
      rfl
    have hRestRoot : rest.first.final.time = H + highRestLatency (Real.exp (source.x 0 (.z p))) := by
      rw [rest.first.date,rest.first.exact_rest_latency r.charge hgRest]
      change r.final.time + highRestLatency (Real.exp (r.final.x 0 (.z p))) = _
      rw [r.date,r.gains]
    have hCalendar : execution.emissionTimes 0 = r.readyAt.fire.final.time ::
        (H :: dates).map (fun time => time + highRestLatency (Real.exp (source.x 0 (.z p)))) := by
      rw [hTimes,rest.calendar,hRestRoot,r.gains]
      rfl
    exact ⟨{
      first := r.readyAt.fire, final := rest.final, execution := execution, date := rest.date
      ready := rest.ready, charge := rest.charge, raw_none := rest.raw_none, pending := rest.pending
      gains := fun j q => (rest.gains j q).trans (r.gains j q)
      recovery := fun j => (rest.recovery j).trans (r.recovery j)
      emission_count := by rw [hTimes,List.length_cons,rest.emission_count,List.length_cons]
      calendar := hCalendar, first_latency_le_rest := r.readyAt.fire.latency_le_rest hq hg
      deliveries := by rw [Execution.deliveries_append,r.deliveries,rest.deliveries]; rfl
      physical := rest.physical, raw_valid := rest.raw_valid
      complete := by simpa only [CompleteThrough] using rest.complete
    }⟩

end KernelR.Hybrid
