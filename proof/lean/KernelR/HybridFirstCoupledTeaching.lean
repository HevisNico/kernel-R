import KernelR.HybridFirstCoupledPreparedPair
import KernelR.HybridCoupledLearnedTrain

namespace KernelR.Hybrid
namespace FirstCoupledPreparedPair
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g}
  {t : ThirdWiredArrival v} (x : FirstCoupledPreparedPair t)

theorem learned_gain_a {ε} (hb : PhysicalBox θ ε) :
    9 / 5 ≤ Real.exp (x.final.x 0 (.z 0)) ∧ Real.exp (x.final.x 0 (.z 0)) ≤ 2 := by
  rw [x.a_gains]
  exact b.localA_gain hb

theorem learned_gain_b {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    9 / 5 ≤ Real.exp (x.final.x 1 (.z 1)) ∧ Real.exp (x.final.x 1 (.z 1)) ≤ 11 / 5 := by
  have hz := newborn.gain (1 : Port)
  simp only [nominalGain,ite_true] at hz
  apply fast_learned_gain_sharp_bounds
  · rw [x.b_gain_target hb hd]
    linarith [hz.1]
  · rw [x.b_gain_target hb hd]
    linarith [hz.2]

theorem learned_train_pending : x.final.pending =
    sourceTrain 0 0 (x.final.time + 8) 8 12 ++ constructedBBirthSources := by
  rw [x.pending,x.date]
  norm_num [firstCoupledPreparedPending]

theorem learned_tail_future (d : Delivery 2) (hd : d ∈ constructedBBirthSources) :
    x.final.time + 8 * (12 + 1 : ℝ) < d.due := by
  rw [x.date]
  simp only [constructedBBirthSources,List.mem_append] at hd
  rcases hd with hd | hd <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd <;>
    dsimp <;> nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

theorem staged_a_count : (x.staged.after.emissionTimes 0).length = 3 := by
  simp [Execution.emissionTimes,x.staged_emissions]

theorem staged_b_count : (x.staged.after.emissionTimes 1).length = 1 := by
  simp [Execution.emissionTimes,x.staged_emissions]

theorem before_birth_a_count {ε} (hb : PhysicalBox θ ε) :
    (x.staged.before.emissionTimes 0).length = 12 := by
  change ((c.execution.append b.wait).emissionTimes 0).length = 12
  rw [Execution.emissionTimes_append]
  have hwait : b.wait.emissionTimes 0 = [] := by
    simp [Execution.emissionTimes,b.wait_emissions]
  rw [hwait,List.append_nil]
  obtain ⟨outcome⟩ := c.outcome hb
  exact outcome.emissions

end FirstCoupledPreparedPair

structure FirstCoupledTeaching {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g}
    {t : ThirdWiredArrival v} (x : FirstCoupledPreparedPair t) where
  train : CoupledLearnedTrain θ fresh forward backward x.final 12 constructedBBirthSources
  final : Snapshot 2
  wait : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) train.final final
  wait_emissions : wait.ledger.emissions = []
  wait_deliveries : wait.deliveries = []
  date : final.time = 3199 / 10
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i p, final.raw i p = none
  pending : final.pending = constructedBBirthSources
  gains : ∀ i p, final.x i (.z p) = x.final.x i (.z p)
  recovery : ∀ i, final.x i .b = x.final.x i .b
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final
  complete : CompleteThrough (train.execution.append wait) (3199 / 10)

theorem first_coupled_teaching_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g}
    {t : ThirdWiredArrival v} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (x : FirstCoupledPreparedPair t)
    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    Nonempty (FirstCoupledTeaching x) := by
  obtain ⟨tr⟩ := coupled_learned_train_exists hb x.final 12 constructedBBirthSources x.physical x.raw_valid
    (by rw [x.date]; norm_num) x.prepared x.charge (x.learned_gain_a hb.extend_old)
    (x.learned_gain_b hb hd) (by rw [x.date]; exact x.raw_active) x.raw_other x.learned_train_pending
    (by intro d h; simpa using x.learned_tail_future d h) forward backward hd
  have ht : tr.final.time = (288 : ℝ) := by rw [tr.date,x.date]; norm_num
  have hwait : tr.final.time < (3199 / 10 : ℝ) := by rw [ht]; norm_num
  have hm : ∀ i, tr.final.main i = .ready := fun i => (tr.prepared i).ready
  have ha : ∀ i p, tr.final.aux i p = .ready := fun i p => ((tr.prepared i).auxiliary p).1
  have hq : ∀ i, tr.final.x i .q < 1 := by intro i; rw [tr.charge]; norm_num
  have hx : ∀ i p, tr.final.x i (.m p) < 1 := by
    intro i p
    linarith [((tr.prepared i).auxiliary p).2.2]
  have hp : ∀ d ∈ tr.final.pending, (3199 / 10 : ℝ) < d.due := by
    intro d h
    rw [tr.pending] at h
    simp only [constructedBBirthSources,List.mem_append] at h
    rcases h with h | h <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp h <;>
      dsimp <;> nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  let flow : Flow (extendParameters θ fresh) tr.final (quietAt tr.final (3199 / 10)) :=
    quietFlow tr.final hwait hm ha tr.raw_none hq hx (fun d h => (hp d h).le)
  let wait : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward)
      tr.final (quietAt tr.final (3199 / 10)) := .cons (.flow flow) (.nil _)
  obtain ⟨_,hc⟩ := quiet_complete_exists (θ := extendParameters θ fresh)
    (route := reciprocalEntryRouter forward backward) tr.final hwait hm ha tr.raw_none hq hx hp
  have hready : ∀ i, ReadyCoordinates (quietAt tr.final (3199 / 10)) i :=
    fun i => quietAt_ready_coordinates tr.final i (tr.ready i) hwait.le
  refine ⟨{
    train := tr
    final := quietAt tr.final (3199 / 10)
    wait := wait
    wait_emissions := rfl
    wait_deliveries := rfl
    date := rfl
    prepared := fun i => ⟨(hready i).ready,(hready i).charge,(tr.prepared i).recovery,(hready i).auxiliary⟩
    charge := ?_
    raw_none := tr.raw_none
    pending := tr.pending
    gains := tr.gains
    recovery := tr.recovery
    physical := wait.physical_invariant hb tr.physical
    raw_valid := wait.raw_valid tr.raw_valid
    complete := hc
  }⟩
  intro i
  change relax (1 / 2) (1 / 10) (tr.final.x i .q) tr.final.time (3199 / 10) = _
  rw [tr.charge]
  simp [relax]

namespace FirstCoupledTeaching
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g}
  {t : ThirdWiredArrival v} {x : FirstCoupledPreparedPair t} (z : FirstCoupledTeaching x)

noncomputable def execution : Execution (extendParameters θ fresh)
    (reciprocalEntryRouter forward backward) x.final z.final := z.train.execution.append z.wait

noncomputable def staged : StagedExecution θ fresh (fun _ _ => [])
    (reciprocalEntryRouter forward backward) born z.final :=
  { x.staged with after := x.staged.after.append z.execution }

theorem staged_complete : CompleteThrough z.staged.after (3199 / 10) := z.complete

theorem pending_length : z.final.pending.length = 32 := by
  rw [z.pending]
  simp [constructedBBirthSources,sourceTrain]

theorem a_emission_count : (z.execution.emissionTimes 0).length = 13 := by
  have hw : z.wait.emissionTimes 0 = [] := by simp [Execution.emissionTimes,z.wait_emissions]
  rw [execution,Execution.emissionTimes_append,hw,List.append_nil]
  exact z.train.a_emission_count

theorem b_emission_count : (z.execution.emissionTimes 1).length = 13 := by
  have hw : z.wait.emissionTimes 1 = [] := by simp [Execution.emissionTimes,z.wait_emissions]
  rw [execution,Execution.emissionTimes_append,hw,List.append_nil]
  exact z.train.b_emission_count

theorem staged_a_count : (z.staged.after.emissionTimes 0).length = 16 := by
  change ((x.staged.after.append z.execution).emissionTimes 0).length = 16
  rw [Execution.emissionTimes_append,List.length_append,x.staged_a_count,z.a_emission_count]

theorem staged_b_count : (z.staged.after.emissionTimes 1).length = 14 := by
  change ((x.staged.after.append z.execution).emissionTimes 1).length = 14
  rw [Execution.emissionTimes_append,List.length_append,x.staged_b_count,z.b_emission_count]

theorem a_cumulative {ε} (hb : PhysicalBox θ ε) :
    (z.staged.before.emissionTimes 0 ++ z.staged.after.emissionTimes 0).length = 28 := by
  rw [List.length_append,z.staged_a_count]
  change (x.staged.before.emissionTimes 0).length + 16 = 28
  rw [x.before_birth_a_count hb]

theorem a_deliveries : z.execution.cellDeliveries 0 = sourceTrain 0 0 192 8 12 := by
  have hw : z.wait.cellDeliveries 0 = [] := by simp [Execution.cellDeliveries,z.wait_deliveries]
  rw [execution,Execution.cellDeliveries_append,hw,List.append_nil,z.train.a_deliveries,x.date]
  norm_num

theorem b_deliveries : z.execution.cellDeliveries 1 =
    z.train.wireTimes.map (fun time => (⟨1,1,time⟩ : Delivery 2)) := by
  have hw : z.wait.cellDeliveries 1 = [] := by simp [Execution.cellDeliveries,z.wait_deliveries]
  rw [execution,Execution.cellDeliveries_append,hw,List.append_nil,z.train.b_deliveries]

theorem wire_provenance (time : ℝ) (h : time ∈ z.train.wireTimes) :
    ∃ F ∈ z.execution.emissionTimes 0, time = F + forward F := by
  obtain ⟨F,hF,hdate⟩ := z.train.wire_provenance time h
  refine ⟨F,?_,hdate⟩
  rw [execution,Execution.emissionTimes_append]
  exact List.mem_append_left _ hF

theorem staged_a_deliveries : z.staged.after.cellDeliveries 0 = sourceTrain 0 0 160 8 16 := by
  change (x.staged.after.append z.execution).cellDeliveries 0 = _
  rw [Execution.cellDeliveries_append,z.a_deliveries]
  norm_num [Execution.cellDeliveries,x.staged_deliveries,sourceTrain,List.ofFn_succ]

theorem a_gain_target {ε} (hb : PhysicalBox θ ε) :
    z.final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5 := by
  rw [z.gains,x.a_gain_target hb]

theorem a_gain_other {ε} (hb : PhysicalBox θ ε) (p : Port) (hp : p ≠ 0) :
    z.final.x 0 (.z p) = born.x 0 (.z p) := by
  rw [z.gains,x.a_gain_other hb p hp]

theorem b_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    z.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [z.gains,x.b_gain_target hb hd]

theorem b_gain_other (p : Port) (hp : p ≠ 1) : z.final.x 1 (.z p) = newborn.x (.z p) := by
  rw [z.gains,x.b_gain_other p hp]

theorem a_recovery_own {ε} (hb : PhysicalBox θ ε) :
    z.final.x 0 .b = born.x 0 .b + 1 / 10 := by
  rw [z.recovery,x.a_recovery_own hb]

theorem b_recovery_own : z.final.x 1 .b = newborn.x .b + 1 / 10 := by
  rw [z.recovery,x.b_recovery_own]

end FirstCoupledTeaching

theorem birth_protocol_first_coupled_teaching_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w, ∃ g : FirstReceiverFastEnd f, ∃ v : FirstPostReceiverPair g,
            ∃ t : ThirdWiredArrival v, ∃ x : FirstCoupledPreparedPair t, ∃ z : FirstCoupledTeaching x,
              CompleteThrough z.staged.after (3199 / 10) ∧ z.final.pending.length = 32 ∧
                (z.staged.before.emissionTimes 0 ++ z.staged.after.emissionTimes 0).length = 28 ∧
                (z.staged.after.emissionTimes 1).length = 14 := by
  obtain ⟨c,b,r,s,w,f,g,v,t,x,_,_,_,_⟩ := birth_protocol_first_coupled_prepared_pair_exists
    hborn hb ha hqueue newborn forward backward hd
  obtain ⟨z⟩ := first_coupled_teaching_exists hb x hd
  exact ⟨c,b,r,s,w,f,g,v,t,x,z,z.staged_complete,z.pending_length,z.a_cumulative hb.extend_old,z.staged_b_count⟩

end KernelR.Hybrid
