import KernelR.HybridBirthReverseTeaching
import KernelR.HybridCTeachingRouter

/-! Construct C's independent birth at480 and consume B's actual queued
boundary source. The original two-cell history remains the supplied t. -/
namespace KernelR.Hybrid

noncomputable def constructedCBirthSources : List (Delivery 3) := sourceTrain 2 0 640 4 25

structure ConstructedCBirth {θ born freshB newbornB forward backward}
    (t : ConstructedReverseTeaching θ born freshB newbornB forward backward)
    (freshC : Parameters) (newbornC : Newborn) (delay : ℝ → ℝ) where
  beforeBirth : Snapshot 2
  afterBirth : Snapshot 3
  final : Snapshot 3
  wait : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) t.final beforeBirth
  birth : BirthStep beforeBirth afterBirth
  arrival : Jump (cTeachingRouter delay) afterBirth final
  before_state : beforeBirth = quietAt t.final 480
  before_date : beforeBirth.time = 480
  after_date : afterBirth.time = 480
  date : final.time = 480
  newborn_origin : birth.newborn = newbornC
  sources_origin : birth.sources = constructedCBirthSources
  before_pending : beforeBirth.pending = sourceTrain 1 2 480 8 16
  old_source_casts : beforeBirth.pending.map liftDelivery = sourceTrain 1 2 480 8 16
  after_pending : afterBirth.pending = sourceTrain 1 2 480 8 16 ++ constructedCBirthSources
  pending : final.pending = sourceTrain 1 2 488 8 15 ++ constructedCBirthSources
  old_coordinates : ∀ i : Fin 2, final.x i.castSucc = beforeBirth.x i
  old_prepared : ∀ i : Fin 2, PreparedSection final i.castSucc
  old_charge : ∀ i : Fin 2, final.x i.castSucc .q = 1 / 10
  old_gains : ∀ (i : Fin 2) q, final.x i.castSucc (.z q) = t.final.x i (.z q)
  old_recovery : ∀ i : Fin 2, final.x i.castSucc .b = t.final.x i .b
  c_coordinates : final.x 2 = newbornC.x
  ready : ∀ i, ReadyCoordinates final i
  raw_active : final.raw 1 2 = some (480 : ℝ)
  raw_other : ∀ i q, i ≠ 1 ∨ q ≠ 2 → final.raw i q = none
  wait_emissions : wait.ledger.emissions = []
  wait_deliveries : wait.deliveries = []
  arrival_emissions : arrival.ledger.emissions = []
  arrival_deliveries : arrival.deliveries = [⟨1,2,480⟩]
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  pending_future : PendingFuture final

noncomputable def ConstructedCBirth.staged {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} (c : ConstructedCBirth t freshC newbornC delay) :
    StagedExecution (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) t.final c.final where
  beforeBirth := c.beforeBirth
  afterBirth := c.afterBirth
  before := c.wait
  birth := c.birth
  after := .cons (.jump c.arrival) (.nil _)

theorem constructed_c_birth_exists {θ born freshB newbornB forward backward freshC ε}
    (t : ConstructedReverseTeaching θ born freshB newbornB forward backward)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (newbornC : Newborn) (delay : ℝ → ℝ) :
    Nonempty (ConstructedCBirth t freshC newbornC delay) := by
  have ht : t.final.time < (480 : ℝ) := by rw [t.date]; norm_num
  have hp : ∀ d ∈ t.final.pending, (480 : ℝ) ≤ d.due := by
    intro d hd
    rw [t.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change (480 : ℝ) ≤ 480 + 8 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  let flow : Flow (extendParameters θ freshB) t.final (quietAt t.final 480) :=
    quietFlow t.final ht (fun i => (t.prepared i).ready)
      (fun i q => ((t.prepared i).auxiliary q).1) t.raw_none
      (fun i => by rw [t.charge]; norm_num)
      (fun i q => by linarith [((t.prepared i).auxiliary q).2.2]) hp
  let wait : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward)
      t.final (quietAt t.final 480) := .cons (.flow flow) (.nil _)
  let before := quietAt t.final 480
  let after := addNewborn before newbornC constructedCBirthSources
  have hsourcecell : ∀ d ∈ constructedCBirthSources, d.cell = Fin.last 2 := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rfl
  have hsourcefuture : ∀ d ∈ constructedCBirthSources, before.time ≤ d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change (480 : ℝ) ≤ 640 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  let birth : BirthStep before after := ⟨newbornC,constructedCBirthSources,hsourcecell,hsourcefuture,rfl⟩
  have hOldCoordinates (i : Fin 2) : after.x i.castSucc = before.x i := birth.old_coordinates i
  have hOldRaw (i : Fin 2) : after.raw i.castSucc = before.raw i := birth.old_raw i
  have hOldRawNone (i : Fin 2) (q : Port) : after.raw i.castSucc q = none := by
    rw [hOldRaw]
    exact t.raw_none i q
  have hNewCoordinates : after.x 2 = newbornC.x := birth.new_coordinates
  have hNewRaw (q : Port) : after.raw 2 q = none := birth.new_raw q
  have hbefore_prepared (i : Fin 2) : PreparedSection before i := by
    have hr := quietAt_ready_coordinates t.final i
      ⟨(t.prepared i).ready,(t.prepared i).charge,(t.prepared i).auxiliary⟩ ht.le
    exact ⟨hr.ready,hr.charge,(t.prepared i).recovery,hr.auxiliary⟩
  have hbefore_pending : before.pending = sourceTrain 1 2 480 8 16 := t.pending
  have hmap : (sourceTrain (1 : Fin 2) 2 480 8 16).map liftDelivery =
      sourceTrain (1 : Fin 3) 2 480 8 16 := by simp [sourceTrain,liftDelivery]
  have hcast : before.pending.map liftDelivery = sourceTrain (1 : Fin 3) 2 480 8 16 := by
    rw [hbefore_pending,hmap]
  have hafter_pending : after.pending = sourceTrain 1 2 480 8 16 ++ constructedCBirthSources := by
    change before.pending.map liftDelivery ++ _ = _
    rw [hcast]
  have hhead : after.pending = [] ++ (⟨1,2,480⟩ : Delivery 3) ::
      (sourceTrain 1 2 488 8 15 ++ constructedCBirthSources) := by
    rw [hafter_pending,sourceTrain_succ]
    norm_num
  have hfree : after.raw 1 2 = none := hOldRawNone 1 2
  let final : Snapshot 3 := { (setRaw after 1 2 (some (480 : ℝ))) with
    pending := sourceTrain 1 2 488 8 15 ++ constructedCBirthSources }
  let arrival : Jump (cTeachingRouter delay) after final := .arrive after ⟨1,2,480⟩ [] _ hhead rfl hfree
  let afterExec : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cTeachingRouter delay) after final := .cons (.jump arrival) (.nil _)
  have hOldPrepared (i : Fin 2) : PreparedSection after i.castSucc := birth.old_prepared i (hbefore_prepared i)
  have hC : ReadyCoordinates after 2 := birth.new_ready
  have hready : ∀ i, ReadyCoordinates final i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨hC.ready,hC.charge,hC.auxiliary⟩
    · exact ⟨(hOldPrepared j).ready,(hOldPrepared j).charge,(hOldPrepared j).auxiliary⟩
  have hpending : final.pending = sourceTrain 1 2 488 8 15 ++ constructedCBirthSources := rfl
  refine ⟨{
    beforeBirth := before, afterBirth := after, final := final
    wait := wait, birth := birth, arrival := arrival
    before_state := rfl, before_date := rfl, after_date := rfl, date := rfl
    newborn_origin := rfl, sources_origin := rfl
    before_pending := hbefore_pending, old_source_casts := hcast
    after_pending := hafter_pending, pending := hpending
    old_coordinates := hOldCoordinates
    old_prepared := fun i => ⟨(hOldPrepared i).ready,(hOldPrepared i).charge,
      (hOldPrepared i).recovery,(hOldPrepared i).auxiliary⟩
    old_charge := ?_, old_gains := ?_, old_recovery := ?_, c_coordinates := hNewCoordinates
    ready := hready, raw_active := ?_, raw_other := ?_
    wait_emissions := rfl, wait_deliveries := rfl, arrival_emissions := rfl, arrival_deliveries := rfl
    physical := afterExec.physical_invariant hb
      (birth.physical_invariant hb (wait.physical_invariant hb.extend_old t.physical))
    raw_valid := afterExec.raw_valid (birth.raw_valid (wait.raw_valid t.raw_valid))
    pending_future := ?_
  }⟩
  · intro i
    change after.x i.castSucc .q = 1 / 10
    rw [hOldCoordinates]
    simp [before,quietAt,quietValues,relax,t.charge]
  · intro i q
    change after.x i.castSucc (.z q) = t.final.x i (.z q)
    rw [hOldCoordinates]
    rfl
  · intro i
    change after.x i.castSucc .b = t.final.x i .b
    rw [hOldCoordinates]
    rfl
  · simp [final,setRaw]
  · intro i q
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hiq
      simpa [final,setRaw] using hNewRaw q
    · intro hiq
      by_cases hi : j = 1
      · subst j
        have hq : q ≠ 2 := by simpa using hiq
        simpa [final,setRaw,hq] using hOldRawNone 1 q
      · have hcastne : j.castSucc ≠ (1 : Fin 3) := by
          intro h
          apply hi
          exact Fin.ext (congrArg (fun k : Fin 3 => k.val) h)
        simpa [final,setRaw,hcastne] using hOldRawNone j q
  · intro d hd
    rw [hpending] at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      change (480 : ℝ) ≤ 488 + 8 * (k.val : ℝ)
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
    · exact hsourcefuture d hd

namespace ConstructedCBirth
variable {θ born freshB newbornB forward backward}
  {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
  {freshC newbornC delay} (c : ConstructedCBirth t freshC newbornC delay)

theorem after_pending_length : c.afterBirth.pending.length = 41 := by
  rw [c.after_pending]
  simp [constructedCBirthSources,sourceTrain]

theorem pending_length : c.final.pending.length = 40 := by
  rw [c.pending]
  simp [constructedCBirthSources,sourceTrain]

theorem c_charge : 1 / 10 - 1 / 100000 ≤ c.final.x 2 .q ∧
    c.final.x 2 .q ≤ 1 / 10 + 1 / 100000 := by
  rw [c.c_coordinates]
  exact newbornC.charge

theorem c_recovery : 2 / 25 - 1 / 100000 ≤ c.final.x 2 .b ∧
    c.final.x 2 .b ≤ 2 / 25 + 1 / 100000 := by
  rw [c.c_coordinates]
  exact newbornC.recovery

theorem c_not_prepared : ¬ PreparedSection c.final 2 := by
  intro h
  linarith [h.recovery.1,c.c_recovery.2]

theorem before_emission_times (i : Fin 2) : c.staged.before.emissionTimes i = [] := by
  simp only [staged,Execution.emissionTimes,c.wait_emissions,List.filter_nil,List.map_nil]

theorem after_emission_times (i : Fin 3) : c.staged.after.emissionTimes i = [] := by
  simp only [staged,Execution.emissionTimes,Execution.ledger,Move.ledger,c.arrival_emissions,
    Ledger.add,Ledger.zero,List.append_nil,List.filter_nil,List.map_nil]

theorem after_deliveries : c.staged.after.deliveries = [⟨1,2,480⟩] := by
  simp only [staged,Execution.deliveries,Move.deliveries,c.arrival_deliveries,List.append_nil]

theorem complete : CompleteThrough c.staged.after (480 : ℝ) := by
  have hfuture : ∀ d ∈ c.final.pending, c.final.time < d.due := by
    intro d hd
    rw [c.pending] at hd
    rw [c.date]
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      change (480 : ℝ) < 488 + 8 * (k.val : ℝ)
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      change (480 : ℝ) < 640 + 4 * (k.val : ℝ)
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  refine ⟨c.date,?_,?_⟩
  · intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        have h := c.ready i
        rw [h.ready]
        linarith [h.charge.2]
      · intro i q
        have h := (c.ready i).auxiliary q
        rw [h.1]
        linarith [h.2.2]
    · intro i q origin hraw
      by_cases h : i = 1 ∧ q = 2
      · rcases h with ⟨rfl,rfl⟩
        have he : origin = (480 : ℝ) := Option.some.inj (hraw.symm.trans c.raw_active)
        rw [he,c.date]
        norm_num
      · rw [c.raw_other i q (by tauto)] at hraw
        contradiction
    · exact hfuture
  · intro d hd
    have h := hfuture d hd
    rw [c.date] at h
    exact h

end ConstructedCBirth
end KernelR.Hybrid
