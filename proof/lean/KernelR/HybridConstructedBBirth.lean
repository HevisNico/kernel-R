import KernelR.HybridBirthPreparationExists
import KernelR.HybridStagedBirth
import KernelR.HybridEntryRouter
/-! Construct B's real birth at 160 and consume A's genuine boundary source. -/
namespace KernelR.Hybrid

noncomputable def constructedBBirthSources : List (Delivery 2) :=
  sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 16

structure ConstructedBBirth {θ born} (c : ConstructedBirthPreparation θ born)
    (fresh : Parameters) (newborn : Newborn) (routeAfter : Router 2) (sourcesB : List (Delivery 2)) where
  beforeBirth : Snapshot 1
  afterBirth : Snapshot 2
  final : Snapshot 2
  wait : Execution θ (fun _ _ => []) c.final beforeBirth
  birth : BirthStep beforeBirth afterBirth
  arrival : Jump routeAfter afterBirth final
  before_date : beforeBirth.time = 160
  after_date : afterBirth.time = 160
  date : final.time = 160
  newborn_state : birth.newborn = newborn
  source_list : birth.sources = sourcesB
  before_pending : beforeBirth.pending = sourceTrain 0 0 160 8 16
  after_pending : afterBirth.pending = sourceTrain 0 0 160 8 16 ++ sourcesB
  pending : final.pending = sourceTrain 0 0 168 8 15 ++ sourcesB
  a_prepared : PreparedSection final 0
  a_charge : final.x 0 .q = 1 / 10
  a_gain_preserved : ∀ p, final.x 0 (.z p) = c.final.x 0 (.z p)
  a_recovery : final.x 0 .b = c.final.x 0 .b
  b_coordinates : final.x 1 = newborn.x
  ready : ∀ j, ReadyCoordinates final j
  raw_active : final.raw 0 0 = some (160 : ℝ)
  raw_other : ∀ j p, j ≠ 0 ∨ p ≠ 0 → final.raw j p = none
  wait_emissions : wait.ledger.emissions = []
  wait_deliveries : wait.deliveries = []
  arrival_emissions : arrival.ledger.emissions = []
  arrival_deliveries : arrival.deliveries = [⟨0,0,160⟩]
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final
  pending_future : PendingFuture final

/-- The source type and route change through an actual BirthStep; the only
post-birth move here is the real delivery of A's existing token at 160. -/
noncomputable def ConstructedBBirth.staged {θ born} {c : ConstructedBirthPreparation θ born}
    {fresh newborn routeAfter sourcesB} (b : ConstructedBBirth c fresh newborn routeAfter sourcesB) :
    StagedExecution θ fresh (fun _ _ => []) routeAfter born b.final where
  beforeBirth := b.beforeBirth
  afterBirth := b.afterBirth
  before := c.execution.append b.wait
  birth := b.birth
  after := .cons (.jump b.arrival) (.nil _)

/-- Birth sources are supplied only as the new cell's external sources.
The construction does not insert any contact token or assume a wire output. -/
theorem constructed_b_birth_exists {θ fresh ε born} (c : ConstructedBirthPreparation θ born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (newborn : Newborn)
    (routeAfter : Router 2) (sourcesB : List (Delivery 2))
    (hcell : ∀ d ∈ sourcesB, d.cell = 1) (hfuture : ∀ d ∈ sourcesB, (160 : ℝ) ≤ d.due) :
    Nonempty (ConstructedBBirth c fresh newborn routeAfter sourcesB) := by
  obtain ⟨outcome⟩ := c.outcome hb.extend_old
  have ht : c.final.time < (160 : ℝ) := by rw [c.date]; norm_num
  have hp : ∀ d ∈ c.final.pending, (160 : ℝ) ≤ d.due := by
    intro d hd
    rw [c.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change (160 : ℝ) ≤ 160 + 8 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  let flow : Flow θ c.final (quietAt c.final 160) := quietFlow c.final ht
    (fun j => (c.ready j).ready) (fun j p => ((c.ready j).auxiliary p).1) c.raw_none
    (fun j => by linarith [(c.ready j).charge.2])
    (fun j p => by linarith [((c.ready j).auxiliary p).2.2]) hp
  let wait : Execution θ (fun _ _ => []) c.final (quietAt c.final 160) := .cons (.flow flow) (.nil _)
  let before := quietAt c.final 160
  let after := addNewborn before newborn sourcesB
  have source_cell : ∀ d ∈ sourcesB, d.cell = Fin.last 1 := by simpa using hcell
  have source_future : ∀ d ∈ sourcesB, before.time ≤ d.due := hfuture
  let birth : BirthStep before after := ⟨newborn,sourcesB,source_cell,source_future,rfl⟩
  have hcast : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
  have hlast : Fin.last 1 = (1 : Fin 2) := rfl
  have hOldCoordinates : after.x 0 = before.x 0 := by
    simpa only [hcast] using birth.old_coordinates (0 : Fin 1)
  have hOldRaw : after.raw 0 = before.raw 0 := by
    simpa only [hcast] using birth.old_raw (0 : Fin 1)
  have hNewCoordinates : after.x 1 = newborn.x := by
    simpa only [hlast] using birth.new_coordinates
  have hNewRaw : ∀ p, after.raw 1 p = none := by
    simpa only [hlast] using birth.new_raw
  have hOldRawNone : ∀ p, after.raw 0 p = none := by
    intro p
    rw [hOldRaw]
    exact c.raw_none 0 p
  have hbefore_ready := quietAt_ready_coordinates c.final 0 (c.ready 0) ht.le
  have hbefore_prepared : PreparedSection before 0 :=
    ⟨hbefore_ready.ready,hbefore_ready.charge,outcome.prepared.recovery,hbefore_ready.auxiliary⟩
  have hbefore_pending : before.pending = sourceTrain 0 0 160 8 16 := c.pending
  have hmap : (sourceTrain (0 : Fin 1) 0 160 8 16).map liftDelivery = sourceTrain (0 : Fin 2) 0 160 8 16 := by
    simp [sourceTrain,liftDelivery]
  have hafter_pending : after.pending = sourceTrain 0 0 160 8 16 ++ sourcesB := by
    change before.pending.map liftDelivery ++ sourcesB = _
    rw [hbefore_pending,hmap]
  have hhead : after.pending = [] ++ (⟨0,0,160⟩ : Delivery 2) :: (sourceTrain 0 0 168 8 15 ++ sourcesB) := by
    rw [hafter_pending,sourceTrain_succ]
    norm_num
  have hfree : after.raw 0 0 = none := hOldRawNone 0
  let final : Snapshot 2 := { (setRaw after 0 0 (some (160 : ℝ))) with pending := sourceTrain 0 0 168 8 15 ++ sourcesB }
  let arrival : Jump routeAfter after final := .arrive after ⟨0,0,160⟩ [] _ hhead rfl hfree
  let afterExec : Execution (extendParameters θ fresh) routeAfter after final := .cons (.jump arrival) (.nil _)
  have hA : PreparedSection after 0 := by
    simpa using birth.old_prepared (0 : Fin 1) hbefore_prepared
  have hB : ReadyCoordinates after 1 := by simpa using birth.new_ready
  have hready : ∀ j, ReadyCoordinates final j := by
    intro j
    fin_cases j
    · exact ⟨hA.ready,hA.charge,hA.auxiliary⟩
    · exact ⟨hB.ready,hB.charge,hB.auxiliary⟩
  have hpending : final.pending = sourceTrain 0 0 168 8 15 ++ sourcesB := rfl
  refine ⟨{
    beforeBirth := before
    afterBirth := after
    final := final
    wait := wait
    birth := birth
    arrival := arrival
    before_date := rfl
    after_date := rfl
    date := rfl
    newborn_state := rfl
    source_list := rfl
    before_pending := hbefore_pending
    after_pending := hafter_pending
    pending := hpending
    a_prepared := ⟨hA.ready,hA.charge,hA.recovery,hA.auxiliary⟩
    a_charge := ?_
    a_gain_preserved := ?_
    a_recovery := ?_
    b_coordinates := ?_
    ready := hready
    raw_active := ?_
    raw_other := ?_
    wait_emissions := rfl
    wait_deliveries := rfl
    arrival_emissions := rfl
    arrival_deliveries := rfl
    physical := afterExec.physical_invariant hb (birth.physical_invariant hb (wait.physical_invariant hb.extend_old c.physical))
    raw_valid := afterExec.raw_valid (birth.raw_valid (wait.raw_valid c.raw_valid))
    pending_future := ?_
  }⟩
  · change after.x 0 .q = 1 / 10
    rw [hOldCoordinates]
    simp [before,quietAt,quietValues,relax,c.charge]
  · intro p
    change after.x 0 (.z p) = c.final.x 0 (.z p)
    rw [hOldCoordinates]
    rfl
  · change after.x 0 .b = c.final.x 0 .b
    rw [hOldCoordinates]
    rfl
  · exact hNewCoordinates
  · simp [final,setRaw]
  · intro j p h
    fin_cases j
    · have hp : p ≠ 0 := by simpa using h
      simp [final,setRaw,hp,hOldRawNone]
    · simp [final,setRaw,hNewRaw]
  · intro d hd
    rw [hpending] at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      change (160 : ℝ) ≤ 168 + 8 * (k.val : ℝ)
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
    · exact hfuture d hd

/-- Once A's boundary source has been delivered, the birth endpoint is
saturated precisely when all newborn sources are strictly later. -/
theorem ConstructedBBirth.complete {θ born} {c : ConstructedBirthPreparation θ born}
    {fresh newborn routeAfter sourcesB} (b : ConstructedBBirth c fresh newborn routeAfter sourcesB)
    (hf : ∀ d ∈ sourcesB, (160 : ℝ) < d.due) : CompleteThrough b.staged.after (160 : ℝ) := by
  have hfuture : ∀ d ∈ b.final.pending, b.final.time < d.due := by
    intro d hd
    rw [b.pending] at hd
    rw [b.date]
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      change (160 : ℝ) < 168 + 8 * (k.val : ℝ)
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
    · exact hf d hd
  refine ⟨b.date,?_,?_⟩
  · intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro j
        have h := b.ready j
        rw [h.ready]
        linarith [h.charge.2]
      · intro j p
        have h := (b.ready j).auxiliary p
        rw [h.1]
        linarith [h.2.2]
    · intro j p origin hraw
      by_cases h : j = 0 ∧ p = 0
      · rcases h with ⟨rfl,rfl⟩
        have he : origin = (160 : ℝ) := Option.some.inj (hraw.symm.trans b.raw_active)
        rw [he,b.date]
        norm_num
      · rw [b.raw_other j p (by tauto)] at hraw
        contradiction
    · exact hfuture
  · intro d hd
    have h := hfuture d hd
    rw [b.date] at h
    exact h

/-- The complete protocol's own B-port2 sources are installed at birth;
both 320..440 and the later 480..600 train remain present. -/
theorem constructed_protocol_b_birth_exists {θ fresh ε born} (c : ConstructedBirthPreparation θ born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (newborn : Newborn)
    (forward backward : ℝ → ℝ) :
    Nonempty (ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources) := by
  apply constructed_b_birth_exists c hb newborn (reciprocalEntryRouter forward backward) constructedBBirthSources
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    all_goals obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd; rfl
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

theorem constructedBBirthSources_strict_future :
    ∀ d ∈ constructedBBirthSources, (160 : ℝ) < d.due := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  all_goals
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    dsimp
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

theorem ConstructedBBirth.protocol_pending_length {θ born} {c : ConstructedBirthPreparation θ born}
    {fresh newborn routeAfter} (b : ConstructedBBirth c fresh newborn routeAfter constructedBBirthSources) :
    b.final.pending.length = 47 := by
  rw [b.pending]
  simp [constructedBBirthSources,sourceTrain]

theorem ConstructedBBirth.protocol_complete {θ born} {c : ConstructedBirthPreparation θ born}
    {fresh newborn routeAfter} (b : ConstructedBBirth c fresh newborn routeAfter constructedBBirthSources) :
    CompleteThrough b.staged.after (160 : ℝ) := b.complete constructedBBirthSources_strict_future

/-- The original birth assumptions already construct A's preparation and B's
birth with its first A input. No reaching execution or preparation witness
is required as a premise. -/
theorem birth_protocol_b_birth_exists {θ fresh ε born}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ) :
    ∃ c : ConstructedBirthPreparation θ born,
      Nonempty (ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources) := by
  obtain ⟨c,_⟩ := birth_protocol_preparation_exists hborn hb.extend_old ha hqueue
  exact ⟨c,constructed_protocol_b_birth_exists c hb newborn forward backward⟩

/-- The constructed endpoint at 160 is saturated after its real A arrival,
with all forty-seven remaining external sources retained exactly. -/
theorem birth_protocol_b_birth_complete_exists {θ fresh ε born}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        CompleteThrough b.staged.after (160 : ℝ) ∧ b.final.pending.length = 47 := by
  obtain ⟨c,⟨b⟩⟩ := birth_protocol_b_birth_exists hborn hb ha hqueue newborn forward backward
  exact ⟨c,b,b.protocol_complete,b.protocol_pending_length⟩

end KernelR.Hybrid
