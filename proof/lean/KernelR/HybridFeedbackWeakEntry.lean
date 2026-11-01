import KernelR.HybridFirstCoupledTeaching
import KernelR.HybridWeakInputCycleExistence
import KernelR.HybridQuietSourceArrival
import KernelR.HybridBirthWeakSources
import KernelR.HybridBoundaryIdle
import KernelR.HybridResidualLatency

/-! Construct the reciprocal weak prefix from the actual first-teaching
endpoint. The fourth B source is delivered, with its real residual charge. -/
namespace KernelR.Hybrid
open Set

private theorem feedback_sources_future (start bound : ℝ) (count : ℕ)
    (hs : bound ≤ start) (hl : bound ≤ 480) :
    ∀ d ∈ sourceTrain (1 : Fin 2) 2 start 8 count ++ sourceTrain 1 2 480 8 16,
      bound ≤ d.due := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  all_goals
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    dsimp
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

private theorem quiet_arrival_charge_ge_rest {n θ route s d later}
    (a : @QuietSourceArrival n θ route s d later) (i : Fin n)
    (hq : 1 / 10 ≤ s.x i .q) : 1 / 10 ≤ a.final.x i .q := by
  rw [a.values]
  change 1 / 10 ≤ relax (1 / 2) (1 / 10) (s.x i .q) s.time d.due
  unfold relax
  have h := mul_nonneg (sub_nonneg.mpr hq)
    (Real.exp_pos (-(1 / 2 : ℝ) * (d.due - s.time))).le
  linarith

private theorem quiet_arrival_prepared {n θ route s d later}
    (a : @QuietSourceArrival n θ route s d later)
    (hs : ∀ i, PreparedSection s i) : ∀ i, PreparedSection a.final i := by
  intro i
  refine ⟨(a.ready i).ready,(a.ready i).charge,?_,(a.ready i).auxiliary⟩
  rw [a.recovery_preserved]
  exact (hs i).recovery

private structure FeedbackWeakStep (θ : Fin 2 → Parameters) (route : Router 2)
    (s : Snapshot 2) (next : ℝ) (later : List (Delivery 2)) where
  final : Snapshot 2
  execution : Execution θ route s final
  date : final.time = next
  prepared : ∀ i, PreparedSection final i
  a_charge : final.x 0 .q = 1 / 10
  b_charge : 1 / 10 ≤ final.x 1 .q
  raw_active : final.raw 1 2 = some final.time
  raw_other : ∀ i p, i ≠ 1 ∨ p ≠ 2 → final.raw i p = none
  pending : final.pending = later
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨1,2,next⟩]
  gain_target : final.x 1 (.z 2) = s.x 1 (.z 2) + 3 / 5
  gain_other : ∀ i p, i ≠ 1 ∨ p ≠ 2 → final.x i (.z p) = s.x i (.z p)
  recovery : ∀ i, final.x i .b = s.x i .b
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution next

private theorem feedback_weak_step_exists {θ ε route} (hb : @PhysicalBox 2 θ ε)
    (s : Snapshot 2) (next : ℝ) (later : List (Delivery 2))
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : ∀ i, PreparedSection s i) (hqA : s.x 0 .q = 1 / 10)
    (hqB : 1 / 10 ≤ s.x 1 .q)
    (hg : Real.exp (s.x 1 (.z 2)) ≤ 7 / 6)
    (hz : s.x 1 (.z 2) ≤ Real.log (6 / 5) + 1 / 1000)
    (hr : s.raw 1 2 = some s.time)
    (ho : ∀ i p, i ≠ 1 ∨ p ≠ 2 → s.raw i p = none)
    (ht : next = s.time + 8)
    (hp : s.pending = ⟨1,2,next⟩ :: later)
    (hlater : ∀ d ∈ later, next + 8 ≤ d.due) :
    Nonempty (FeedbackWeakStep θ route s next later) := by
  obtain ⟨c⟩ := weak_input_cycle_exists (route := route) s hb hf hv 1 2
    (fun i => (hs i).ready_coordinates) hg hz hr ho (by
      intro d hd
      rw [hp] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · change s.time + 8 ≤ next
        exact ht.ge
      · linarith [hlater d hd])
  have hno : ∀ i p, NoArrivalAt c.execution i p := by
    intro i p
    simp [NoArrivalAt,c.deliveries]
  obtain ⟨idle⟩ := c.execution.idle_prepared 0 (hs 0) hqA
    (fun p => ho 0 p (Or.inl (by decide))) (hno 0)
  have hprepared : ∀ i, PreparedSection c.final i := by
    intro i
    fin_cases i
    · exact idle.prepared
    · exact c.pulse.prepared (hs 1)
  have hraw : ∀ i p, c.final.raw i p = none := by
    intro i p
    fin_cases i
    · exact (c.execution.raw_absent_of_no_arrival 0 p
        (ho 0 p (Or.inl (by decide))) (hno 0 p)).1
    · exact c.pulse.raw_finished p
  have hmain := c.execution.ready_states_of_no_emissions 1 (hs 1).ready
    (by simp [Execution.emissionTimes,c.emissions])
  have hq := c.execution.ready_charge_ge_rest 1
    (c.execution.allStates_main_flows 1 .ready hmain) hqB
  obtain ⟨a⟩ := quiet_source_arrival_exists (route := route) hb c.final
    (⟨1,2,next⟩ : Delivery 2) later c.physical c.raw_valid
    (fun i => (hprepared i).ready_coordinates) hraw
    (by rw [c.date]; linarith) (by rw [c.pending,hp])
    (by intro d hd; linarith [hlater d hd])
  let e := c.execution.append a.execution
  have hA : a.final.x 0 .q = 1 / 10 := by
    rw [a.values]
    change relax (1 / 2) (1 / 10) (c.final.x 0 .q) c.final.time next = _
    rw [idle.charge_rest]
    simp [relax]
  refine ⟨{
    final := a.final, execution := e, date := a.date
    prepared := quiet_arrival_prepared a hprepared
    a_charge := hA, b_charge := quiet_arrival_charge_ge_rest a 1 hq
    raw_active := a.raw_active, raw_other := a.raw_other, pending := a.pending
    emissions := by rw [Execution.emissions_append,c.emissions,a.emissions]; rfl
    deliveries := by rw [Execution.deliveries_append,c.deliveries,a.deliveries]; rfl
    gain_target := by rw [a.gain_preserved,c.pulse.gain_target]
    gain_other := ?_, recovery := ?_
    physical := a.physical, raw_valid := a.raw_valid
    complete := a.complete (by intro d hd; linarith [hlater d hd])
  }⟩
  · intro i p h
    rw [a.gain_preserved]
    fin_cases i
    · exact idle.gain_preserved p
    · exact c.pulse.gain_other p (by simpa using h)
  · intro i
    rw [a.recovery_preserved]
    fin_cases i
    · exact idle.recovery_preserved
    · exact c.pulse.recovery_preserved

structure FeedbackWeakEntry (θ : Fin 2 → Parameters) (route : Router 2)
    (start : Snapshot 2) where
  initial_prepared : ∀ i, PreparedSection start i
  final : Snapshot 2
  execution : Execution θ route start final
  date : final.time = 344
  prepared : ∀ i, PreparedSection final i
  a_charge : final.x 0 .q = 1 / 10
  b_charge : 1 / 10 ≤ final.x 1 .q
  raw_active : final.raw 1 2 = some final.time
  raw_other : ∀ i p, i ≠ 1 ∨ p ≠ 2 → final.raw i p = none
  pending : final.pending = sourceTrain 1 2 352 8 12 ++ sourceTrain 1 2 480 8 16
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = sourceTrain 1 2 320 8 4
  gain_target : final.x 1 (.z 2) = start.x 1 (.z 2) + 9 / 5
  gain_other : ∀ i p, i ≠ 1 ∨ p ≠ 2 → final.x i (.z p) = start.x i (.z p)
  recovery : ∀ i, final.x i .b = start.x i .b
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution 344

/-- The queued sources themselves drive three real weak cycles and the
fresh source344. No continuation, pulse word or dose is supplied. -/
theorem feedback_weak_entry_exists {θ ε route} (hb : @PhysicalBox 2 θ ε)
    (start : Snapshot 2) (hf : PhysicalInvariant θ start) (hv : RawValid start)
    (hs : ∀ i, PreparedSection start i) (hq : ∀ i, start.x i .q = 1 / 10)
    (hr : ∀ i p, start.raw i p = none) (ht : start.time = 3199 / 10)
    (hp : start.pending = sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 16)
    (hz : start.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    Nonempty (FeedbackWeakEntry θ route start) := by
  obtain ⟨a320⟩ := quiet_source_arrival_exists (route := route) hb start
    (⟨1,2,320⟩ : Delivery 2)
    (sourceTrain 1 2 328 8 15 ++ sourceTrain 1 2 480 8 16) hf hv
    (fun i => (hs i).ready_coordinates) hr (by rw [ht]; norm_num)
    (by rw [hp,sourceTrain_succ]; norm_num)
    (feedback_sources_future 328 320 15 (by norm_num) (by norm_num))
  have hA320 : a320.final.x 0 .q = 1 / 10 := by
    rw [a320.values]
    change relax (1 / 2) (1 / 10) (start.x 0 .q) start.time 320 = _
    rw [hq]; simp [relax]
  have hz320 : a320.final.x 1 (.z 2) = start.x 1 (.z 2) := a320.gain_preserved 1 2
  have hg320 := (own_birth_weak_gain_bounds hz (stage := 0) (by norm_num)
    (current := a320.final.x 1 (.z 2)) (by simpa using hz320)).2
  obtain ⟨c0⟩ := feedback_weak_step_exists (route := route) hb a320.final 328
    (sourceTrain 1 2 336 8 14 ++ sourceTrain 1 2 480 8 16)
    a320.physical a320.raw_valid (quiet_arrival_prepared a320 hs) hA320
    (quiet_arrival_charge_ge_rest a320 1 (by rw [hq])) hg320.1 hg320.2
    a320.raw_active a320.raw_other (by rw [a320.date]; norm_num)
    (by rw [a320.pending,sourceTrain_succ]; norm_num)
    (feedback_sources_future 336 (328 + 8) 14 (by norm_num) (by norm_num))
  have hz328 : c0.final.x 1 (.z 2) = start.x 1 (.z 2) + 3 / 5 := by
    rw [c0.gain_target,hz320]
  have hg328 := (own_birth_weak_gain_bounds hz (stage := 1) (by norm_num)
    (current := c0.final.x 1 (.z 2)) (by simpa using hz328)).2
  obtain ⟨c1⟩ := feedback_weak_step_exists (route := route) hb c0.final 336
    (sourceTrain 1 2 344 8 13 ++ sourceTrain 1 2 480 8 16)
    c0.physical c0.raw_valid c0.prepared c0.a_charge c0.b_charge hg328.1 hg328.2
    c0.raw_active c0.raw_other (by rw [c0.date]; norm_num)
    (by rw [c0.pending,sourceTrain_succ]; norm_num)
    (feedback_sources_future 344 (336 + 8) 13 (by norm_num) (by norm_num))
  have hz336 : c1.final.x 1 (.z 2) = start.x 1 (.z 2) + 6 / 5 := by
    rw [c1.gain_target,hz328]; ring
  have hg336 := (own_birth_weak_gain_bounds hz (stage := 2) (by norm_num)
    (current := c1.final.x 1 (.z 2)) (by norm_num; exact hz336)).2
  obtain ⟨c2⟩ := feedback_weak_step_exists (route := route) hb c1.final 344
    (sourceTrain 1 2 352 8 12 ++ sourceTrain 1 2 480 8 16)
    c1.physical c1.raw_valid c1.prepared c1.a_charge c1.b_charge hg336.1 hg336.2
    c1.raw_active c1.raw_other (by rw [c1.date]; norm_num)
    (by rw [c1.pending,sourceTrain_succ]; norm_num)
    (feedback_sources_future 352 (344 + 8) 12 (by norm_num) (by norm_num))
  let e := ((a320.execution.append c0.execution).append c1.execution).append c2.execution
  refine ⟨{
    initial_prepared := hs
    final := c2.final, execution := e, date := c2.date
    prepared := c2.prepared, a_charge := c2.a_charge, b_charge := c2.b_charge
    raw_active := c2.raw_active, raw_other := c2.raw_other, pending := c2.pending
    emissions := by simp only [e,Execution.emissions_append,a320.emissions,c0.emissions,
      c1.emissions,c2.emissions,List.append_nil]
    deliveries := ?_, gain_target := ?_, gain_other := ?_, recovery := ?_
    physical := c2.physical, raw_valid := c2.raw_valid, complete := c2.complete
  }⟩
  · simp only [e,Execution.deliveries_append,a320.deliveries,c0.deliveries,c1.deliveries,c2.deliveries]
    norm_num [sourceTrain,List.ofFn_succ]
  · rw [c2.gain_target,hz336]; ring
  · intro i p h
    rw [c2.gain_other i p h,c1.gain_other i p h,c0.gain_other i p h,a320.gain_preserved]
  · intro i
    rw [c2.recovery,c1.recovery,c0.recovery,a320.recovery_preserved]

namespace FeedbackWeakEntry
variable {θ route start} (w : FeedbackWeakEntry θ route start)

theorem pending_length : w.final.pending.length = 28 := by
  rw [w.pending]
  simp [sourceTrain]

theorem emission_times (i : Fin 2) : w.execution.emissionTimes i = [] := by
  simp only [Execution.emissionTimes,w.emissions,List.filter_nil,List.map_nil]

theorem error_target : w.execution.ledger.error 1 2 = 9 / 5 := by
  have h := w.execution.gain_balance 1 2
  rw [w.gain_target] at h
  linarith

theorem error_other (i : Fin 2) (p : Port) (hother : i ≠ 1 ∨ p ≠ 2) :
    w.execution.ledger.error i p = 0 := by
  have h := w.execution.gain_balance i p
  rw [w.gain_other i p hother] at h
  linarith

theorem recovery_zero (i : Fin 2) : w.execution.ledger.recovery i = 0 := by
  have h := w.execution.recovery_balance i
  rw [w.recovery] at h
  linarith

theorem mark_zero (i : Fin 2) (p : Port) : w.execution.ledger.mark i p = 0 := by
  have hm := w.execution.ready_states_of_no_emissions i (w.initial_prepared i).ready (w.emission_times i)
  exact w.execution.mark_zero_ready i p (w.execution.allStates_main_flows i .ready hm)

end FeedbackWeakEntry

namespace FirstCoupledTeaching
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {v : SecondWiredArrival s}
  {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
  {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t} (z : FirstCoupledTeaching x)

theorem feedback_weak_entry_exists {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) :
    Nonempty (FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final) := by
  apply KernelR.Hybrid.feedback_weak_entry_exists hb z.final z.physical z.raw_valid
    z.prepared z.charge z.raw_none z.date
  · exact z.pending
  · rw [z.b_gain_other 2 (by decide)]
    have h := (newborn.gain (2 : Port)).2
    simpa only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] using h

/-- Append the newly constructed weak prefix to the very same birth-to319.9
execution. The shared endpoint is an index, rather than an assumed equality. -/
noncomputable def feedback_weak_staged
    (w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final) :
    StagedExecution θ fresh (fun _ _ => []) (reciprocalEntryRouter forward backward) born w.final :=
  { z.staged with after := z.staged.after.append w.execution }

theorem feedback_weak_a_cumulative {ε} (hb : PhysicalBox θ ε)
    (w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final) :
    ((z.feedback_weak_staged w).before.emissionTimes 0 ++
      (z.feedback_weak_staged w).after.emissionTimes 0).length = 28 := by
  simpa only [feedback_weak_staged,Execution.emissionTimes_append,w.emission_times,List.append_nil]
    using z.a_cumulative hb

theorem feedback_weak_b_count
    (w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final) :
    ((z.feedback_weak_staged w).after.emissionTimes 1).length = 14 := by
  simpa only [feedback_weak_staged,Execution.emissionTimes_append,w.emission_times,List.append_nil]
    using z.staged_b_count

theorem feedback_weak_b_gain_own
    (w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final) :
    w.final.x 1 (.z 2) = newborn.x (.z 2) + 9 / 5 := by
  rw [w.gain_target,z.b_gain_other 2 (by decide)]

end FirstCoupledTeaching

/-- From the original A birth, construct the complete first teaching epoch
and its actual reciprocal weak successor through fresh B344. -/
theorem birth_protocol_feedback_weak_entry_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ v : SecondWiredArrival s,
          ∃ f : FirstReceiverFire v, ∃ g : FirstReceiverFastEnd f, ∃ u : FirstPostReceiverPair g,
            ∃ t : ThirdWiredArrival u, ∃ x : FirstCoupledPreparedPair t, ∃ z : FirstCoupledTeaching x,
              ∃ w : FeedbackWeakEntry (extendParameters θ fresh)
                  (reciprocalEntryRouter forward backward) z.final,
                CompleteThrough (z.feedback_weak_staged w).after 344 ∧
                  w.final.pending.length = 28 ∧
                  ((z.feedback_weak_staged w).before.emissionTimes 0 ++
                    (z.feedback_weak_staged w).after.emissionTimes 0).length = 28 ∧
                  ((z.feedback_weak_staged w).after.emissionTimes 1).length = 14 ∧
                  w.final.x 1 (.z 2) = newborn.x (.z 2) + 9 / 5 := by
  obtain ⟨c,b,r,s,v,f,g,u,t,x,z,_,_,_,_⟩ := birth_protocol_first_coupled_teaching_exists
    hborn hb ha hqueue newborn forward backward hd
  obtain ⟨w⟩ := z.feedback_weak_entry_exists hb
  exact ⟨c,b,r,s,v,f,g,u,t,x,z,w,w.complete,w.pending_length,
    z.feedback_weak_a_cumulative hb.extend_old w,z.feedback_weak_b_count w,z.feedback_weak_b_gain_own w⟩

end KernelR.Hybrid
