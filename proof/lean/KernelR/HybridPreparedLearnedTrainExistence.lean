import KernelR.HybridPreparedLearnedCycle
import KernelR.HybridQuietSourceArrival

namespace KernelR.Hybrid

structure PreparedLearnedTrain (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (count : ℕ) (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  date : final.time = s.time + 8 * (count : ℝ) + 15 / 2
  ready : ∀ j, ReadyCoordinates final j
  prepared : ∀ j, PreparedSection final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j p, final.raw j p = none
  pending : final.pending = later
  deliveries : execution.deliveries = sourceTrain 0 0 (s.time + 8) 8 count
  gains : ∀ j p, final.x j (.z p) = s.x j (.z p)
  recovery : ∀ j, final.x j .b = s.x j .b
  emission_count : execution.ledger.emissions.length = count + 1
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (s.time + 8 * (count : ℝ) + 15 / 2)

theorem prepared_learned_train_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (count : ℕ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : ∀ j, PreparedSection s j)
    (hg : 9 / 5 ≤ Real.exp (s.x 0 (.z 0)) ∧ Real.exp (s.x 0 (.z 0)) ≤ 2)
    (hr : s.raw 0 0 = some s.time) (ho : ∀ p, p ≠ 0 → s.raw 0 p = none)
    (hqueue : s.pending = sourceTrain 0 0 (s.time + 8) 8 count ++ later)
    (hLater : ∀ d ∈ later, s.time + 8 * ((count : ℝ) + 1) ≤ d.due) :
    Nonempty (PreparedLearnedTrain θ s count later) := by
  induction count generalizing s with
  | zero =>
    have hpending : s.pending = later := by simpa [sourceTrain] using hqueue
    obtain ⟨c⟩ := prepared_learned_cycle_exists hb s hf hv hs hg hr ho (by
      intro d hd; rw [hpending] at hd; simpa using hLater d hd)
    exact ⟨{
      final := c.final
      execution := c.execution
      date := by simpa using c.date
      ready := c.ready
      prepared := c.prepared
      charge := c.charge
      raw_none := c.raw_none
      pending := c.pending.trans hpending
      deliveries := by simpa [sourceTrain] using c.deliveries
      gains := c.gains
      recovery := c.recovery
      emission_count := by rw [c.emissions]; rfl
      physical := c.physical
      raw_valid := c.raw_valid
      complete := by simpa using c.complete
    }⟩
  | succ count ih =>
    have htailTime : s.time + 8 ≤ s.time + 8 * (((count + 1 : ℕ) : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ (count : ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
    have hpending : ∀ d ∈ s.pending, s.time + 8 ≤ d.due := by
      intro d hd
      rw [hqueue] at hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
        dsimp
        have hk : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
        linarith
      · exact htailTime.trans (hLater d hd)
    obtain ⟨c⟩ := prepared_learned_cycle_exists hb s hf hv hs hg hr ho hpending
    obtain ⟨a⟩ := quiet_source_arrival_exists (route := fun _ _ => []) hb c.final
      (⟨0,0,s.time + 8⟩ : Delivery 1) (sourceTrain 0 0 (s.time + 16) 8 count ++ later)
      c.physical c.raw_valid c.ready c.raw_none (by rw [c.date]; norm_num)
      (by
        rw [c.pending,hqueue,sourceTrain_succ]
        have h : s.time + 8 + 8 = s.time + 16 := by ring
        simp only [List.cons_append,h])
      (by
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
          dsimp
          have hk : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
          linarith
        · exact htailTime.trans (hLater d hd))
    have hprepared : ∀ j, PreparedSection a.final j := by
      intro j
      refine ⟨(a.ready j).ready,(a.ready j).charge,?_,(a.ready j).auxiliary⟩
      rw [a.recovery_preserved,c.recovery]
      exact (hs j).recovery
    have hga : 9 / 5 ≤ Real.exp (a.final.x 0 (.z 0)) ∧ Real.exp (a.final.x 0 (.z 0)) ≤ 2 := by
      rw [a.gain_preserved,c.gains]
      exact hg
    obtain ⟨t⟩ := ih a.final a.physical a.raw_valid hprepared hga a.raw_active
      (fun p hp => a.raw_other 0 p (Or.inr hp))
      (by
        rw [a.pending,a.date]
        have h : s.time + 8 + 8 = s.time + 16 := by ring
        rw [h])
      (by
        intro d hd
        have h := hLater d hd
        rw [a.date]
        push_cast at h
        linarith)
    let e := (c.execution.append a.execution).append t.execution
    have hdate : a.final.time + 8 * (count : ℝ) + 15 / 2 =
        s.time + 8 * (((count + 1 : ℕ) : ℝ)) + 15 / 2 := by
      rw [a.date]
      push_cast
      ring
    refine ⟨{
      final := t.final
      execution := e
      date := t.date.trans hdate
      ready := t.ready
      prepared := t.prepared
      charge := t.charge
      raw_none := t.raw_none
      pending := t.pending
      deliveries := ?_
      gains := fun j p => (t.gains j p).trans ((a.gain_preserved j p).trans (c.gains j p))
      recovery := fun j => (t.recovery j).trans ((a.recovery_preserved j).trans (c.recovery j))
      emission_count := ?_
      physical := t.physical
      raw_valid := t.raw_valid
      complete := ?_
    }⟩
    · simp only [e,Execution.deliveries_append,c.deliveries,a.deliveries,t.deliveries,List.nil_append]
      rw [sourceTrain_succ,a.date]
      rfl
    · simp only [e,Execution.emissions_append,c.emissions,a.emissions,List.append_nil,
        List.length_append,List.length_singleton,t.emission_count]
      omega
    · change CompleteThrough t.execution (s.time + 8 * (((count + 1 : ℕ) : ℝ)) + 15 / 2)
      rw [← hdate]
      exact t.complete

end KernelR.Hybrid
