import KernelR.HybridConstructedBBirth
import KernelR.HybridQuietExecutionProduct
import KernelR.HybridFirstLearnedFireExistence
import KernelR.HybridFirstFireSchedule

/-! Lift the real first learned A pulse alongside the newborn's quiet physical
trajectory, then create the contact token only through the actual global FIRE. -/
namespace KernelR.Hybrid

noncomputable def Snapshot.cellProjection (s : Snapshot 2) (i : Fin 2)
    (Q : List (Delivery 1)) : Snapshot 1 where
  time := s.time
  x := fun _ => s.x i
  main := fun _ => s.main i
  aux := fun _ => s.aux i
  raw := fun _ => s.raw i
  pending := Q

theorem Snapshot.cellProjection_product (s : Snapshot 2) (QA QB : List (Delivery 1)) :
    (s.cellProjection 0 QA).product (s.cellProjection 1 QB) s.pending = s := by
  cases s
  simp only [cellProjection,product]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

noncomputable def constructedBBirthQueue : List (Delivery 2) :=
  sourceTrain 0 0 168 8 15 ++ constructedBBirthSources

namespace ConstructedBBirth
variable {θ born} {c : ConstructedBirthPreparation θ born} {fresh newborn route}
    (b : ConstructedBBirth c fresh newborn route constructedBBirthSources)

noncomputable def localA : Snapshot 1 := b.final.cellProjection 0 (sourceTrain 0 0 168 8 15)
noncomputable def localB : Snapshot 1 := b.final.cellProjection 1
  (sourceTrain 0 2 320 8 16 ++ sourceTrain 0 2 480 8 16)

theorem product_initial : b.localA.product b.localB constructedBBirthQueue = b.final := by
  rw [show constructedBBirthQueue = b.final.pending from b.pending.symm]
  exact b.final.cellProjection_product _ _

theorem queue_future (d : Delivery 2) (hd : d ∈ constructedBBirthQueue) : (168 : ℝ) ≤ d.due := by
  simp only [constructedBBirthQueue,constructedBBirthSources,List.mem_append] at hd
  rcases hd with hd | hd | hd <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd <;>
    change (168 : ℝ) ≤ _ + 8 * (k.val : ℝ) <;> nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

theorem localA_physical : PhysicalInvariant θ b.localA := by
  have hθ : extendParameters θ fresh (0 : Fin 2) = θ (0 : Fin 1) := rfl
  refine ⟨fun j => b.physical.region 0,?_,fun j => b.physical.recovery_cap 0,
    fun j => b.physical.reserve 0⟩
  intro j p
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simpa only [localA,Snapshot.cellProjection,hθ] using b.physical.gain_cap 0 p

theorem localA_raw_valid : RawValid b.localA := fun _ p o h => b.raw_valid 0 p o h

theorem localA_ready : ∀ j, ReadyCoordinates b.localA j :=
  fun _ => ⟨(b.ready 0).ready,(b.ready 0).charge,(b.ready 0).auxiliary⟩

theorem localB_ready : ReadyCoordinates b.localB 0 :=
  ⟨(b.ready 1).ready,(b.ready 1).charge,(b.ready 1).auxiliary⟩

theorem localB_raw_none : ∀ p, b.localB.raw 0 p = none :=
  fun p => b.raw_other 1 p (Or.inl (by decide))

theorem localA_gain {ε} (hb : PhysicalBox θ ε) :
    9 / 5 ≤ Real.exp (b.localA.x 0 (.z 0)) ∧ Real.exp (b.localA.x 0 (.z 0)) ≤ 2 := by
  obtain ⟨outcome⟩ := c.outcome hb
  have hz := ((c.at40.mark.first.weak.birth.2.2 0).2.2.2.2 (0 : Port)).1
  simp only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] at hz
  apply learned_gain_bounds
  · change _ ≤ b.final.x 0 (.z 0)
    rw [b.a_gain_preserved,outcome.gain_target]
    linarith [hz.1]
  · change b.final.x 0 (.z 0) ≤ _
    rw [b.a_gain_preserved,outcome.gain_target]
    linarith [hz.2]

end ConstructedBBirth

noncomputable def FirstLearnedFire.before {θ : Fin 1 → Parameters} {s : Snapshot 1} (f : FirstLearnedFire θ (fun _ _ => []) s 0 0) : Snapshot 1 :=
  f.firstSilent.learnedFireBefore f.latency

noncomputable def FirstLearnedFire.beforeExecution {θ : Fin 1 → Parameters} {s : Snapshot 1}
    (f : FirstLearnedFire θ (fun _ _ => []) s 0 0) : Execution θ (fun _ _ => []) s f.before :=
  (f.firstSilent.execution (fun _ _ => [])).append (.cons (.flow f.flow) (.nil _))

theorem FirstLearnedFire.before_emissions {θ : Fin 1 → Parameters} {s : Snapshot 1} (f : FirstLearnedFire θ (fun _ _ => []) s 0 0) :
    f.beforeExecution.ledger.emissions = [] := by
  simp [beforeExecution,FirstInputSilent.execution,FirstInputSilent.continuation,
    FirstInputMark.execution,Execution.emissions_append,Execution.ledger,Move.ledger,
    Flow.ledger,Jump.ledger,Ledger.add,Ledger.zero]

theorem FirstLearnedFire.before_deliveries {θ : Fin 1 → Parameters} {s : Snapshot 1} (f : FirstLearnedFire θ (fun _ _ => []) s 0 0) :
    f.beforeExecution.deliveries = [] := by
  simp [beforeExecution,FirstInputSilent.execution,FirstInputSilent.continuation,
    FirstInputMark.execution,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries]

theorem FirstLearnedFire.final_empty {θ : Fin 1 → Parameters} {s : Snapshot 1} (f : FirstLearnedFire θ (fun _ _ => []) s 0 0) :
    f.final = setMain f.before 0 .fast := by
  simp only [final,FirstInputSilent.learnedFireFinal,List.append_nil,before]
  rfl

structure TwoCellFirstFire {θ born} {c : ConstructedBirthPreparation θ born}
    {fresh newborn route} (b : ConstructedBBirth c fresh newborn route constructedBBirthSources) where
  firelocal : FirstLearnedFire θ (fun _ _ => []) b.localA 0 0
  before : Snapshot 2
  final : Snapshot 2
  span : Execution (extendParameters θ fresh) route b.final before
  fire : Jump route before final
  execution : Execution (extendParameters θ fresh) route b.final final
  product_before : before = firelocal.before.product (quietAt b.localB before.time) constructedBBirthQueue
  product_final : final = firelocal.final.product (quietAt b.localB final.time)
    (constructedBBirthQueue ++ route 0 final.time)
  date : final.time = 160 + firelocal.latency
  early : 160 + 2 / 5 < final.time
  deadline : final.time < 160 + 9 / 10
  pending : final.pending = constructedBBirthQueue ++ route 0 final.time
  span_emissions : span.ledger.emissions = []
  span_deliveries : span.deliveries = []
  emissions : execution.ledger.emissions = [(0,final.time)]
  deliveries : execution.deliveries = []
  a_coordinates : final.x 0 = firelocal.final.x 0
  b_coordinates : final.x 1 = (quietAt b.localB final.time).x 0
  a_main_fast : final.main 0 = .fast
  a_aux_silent : final.aux 0 0 = .silent
  a_sensor_above : 1 / 10 < final.x 0 (.m 0)
  a_aux_other : ∀ p, p ≠ 0 → final.aux 0 p = .ready ∧ RestBand (final.x 0 (.m p))
  b_ready : ReadyCoordinates final 1
  raw_active : final.raw 0 0 = some (160 : ℝ)
  raw_other : ∀ j p, j ≠ 0 ∨ p ≠ 0 → final.raw j p = none
  gains : ∀ j p, final.x j (.z p) = b.final.x j (.z p)
  recovery : ∀ j, final.x j .b = b.final.x j .b
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- The global FIRE is constructed after the event-free product. Its routed
queue is appended only here; no contact delivery is present in the input. -/
theorem two_cell_first_fire_exists {θ born fresh ε newborn route}
    {c : ConstructedBirthPreparation θ born}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (b : ConstructedBBirth c fresh newborn route constructedBBirthSources) :
    Nonempty (TwoCellFirstFire b) := by
  have hg := b.localA_gain hb.extend_old
  have hr : b.localA.raw 0 0 = some b.localA.time := by
    change b.final.raw 0 0 = some b.final.time
    rw [b.date]
    exact b.raw_active
  have ho : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ 0 → b.localA.raw j p = none := by
    intro j p h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact b.raw_other 0 p (Or.inr (by simpa using h))
  have hp : ∀ d ∈ b.localA.pending, b.localA.time + 8 ≤ d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change b.final.time + 8 ≤ 168 + 8 * (k.val : ℝ)
    rw [b.date]
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨f⟩ := first_learned_fire_exists (route := fun _ _ => []) b.localA hb.extend_old
    b.localA_physical b.localA_raw_valid 0 0 b.localA_ready hg hr ho hp
  have htime : f.before.time = 160 + f.latency := by change b.final.time + _ = _; rw [b.date]
  have hearly : 160 + 2 / 5 < f.before.time := by
    have h := readyPulse_root_after_four_tenths (b.localA_ready 0).charge.2 hg.2
      (by linarith [f.early] : b.localA.time ≤ b.localA.time + f.latency) f.response_root
    change b.final.time + 2 / 5 < b.final.time + f.latency at h
    rw [b.date] at h
    rw [htime]
    exact h
  have hend : f.before.time < 160 + 9 / 10 := by rw [htime]; linarith [f.deadline]
  have hQ : ∀ d ∈ constructedBBirthQueue, f.before.time ≤ d.due := by
    intro d hd
    linarith [ConstructedBBirth.queue_future d hd]
  obtain ⟨lifted,hle,hld⟩ := f.beforeExecution.product_with_quiet_left
    (θB := fun _ : Fin 1 => fresh) f.before_emissions f.before_deliveries b.localB rfl
    b.localB_ready b.localB_raw_none constructedBBirthQueue hQ route
  let before := f.before.product (quietAt b.localB f.before.time) constructedBBirthQueue
  let final := f.final.product (quietAt b.localB f.before.time)
    (constructedBBirthQueue ++ route 0 f.before.time)
  let span : Execution (extendParameters θ fresh) route b.final before :=
    lifted.cast_source b.product_initial.symm
  have hmode : before.main 0 = .ready := f.firstSilent.main_ready 0
  have hthreshold : before.x 0 .q = 1 := f.threshold
  have hfinal : final = { (setMain before 0 .fast) with pending := before.pending ++ route 0 before.time } := by
    dsimp [final,before]
    rw [f.final_empty,Snapshot.product_setMain_left]
    rfl
  let jump : Jump route before final := hfinal.symm ▸ Jump.fire before 0 hmode hthreshold
  let e : Execution (extendParameters θ fresh) route b.final final :=
    span.append (.cons (.jump jump) (.nil _))
  have hFast : final.main 0 = .fast := f.main_fast
  have hjEm : jump.ledger.emissions = [(0,before.time)] :=
    jump.ready_main_departure_emission 0 hmode (by rw [hFast]; decide)
  have hjDel : jump.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have hz := jump.no_emissions_of_delivery d hd
    rw [hjEm] at hz
    contradiction
  have hsEm : span.ledger.emissions = [] := by
    simpa only [span,Execution.cast_source_ledger] using hle
  have hsDel : span.deliveries = [] := by
    simpa only [span,Execution.cast_source_deliveries] using hld
  have hB := quietAt_ready_coordinates b.localB 0 b.localB_ready (T := f.before.time)
    (by change b.final.time ≤ f.before.time; rw [b.date]; linarith)
  refine ⟨{
    firelocal := f, before := before, final := final, span := span, fire := jump, execution := e
    product_before := rfl, product_final := rfl, date := htime, early := hearly, deadline := hend
    pending := rfl, span_emissions := hsEm, span_deliveries := hsDel
    emissions := ?_, deliveries := ?_, a_coordinates := rfl, b_coordinates := rfl
    a_main_fast := hFast, a_aux_silent := f.aux_silent, a_sensor_above := f.sensor_above
    a_aux_other := ?_, b_ready := ⟨hB.ready,hB.charge,hB.auxiliary⟩
    raw_active := ?_, raw_other := ?_, gains := ?_, recovery := ?_
    physical := e.physical_invariant hb b.physical, raw_valid := e.raw_valid b.raw_valid
  }⟩
  · simp only [e,Execution.emissions_append,hsEm,Execution.ledger,Move.ledger,
      hjEm,Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
    rfl
  · simp only [e,Execution.deliveries_append,hsDel,Execution.deliveries,Move.deliveries,
      hjDel,List.append_nil]
  · intro p hp0
    have h := f.execution.aux_no_input_rest_band 0 p ((b.localA_ready 0).auxiliary p).1
      ((b.localA_ready 0).auxiliary p).2 (ho 0 p (Or.inr hp0)) (by
        intro d hd
        rw [f.deliveries] at hd
        contradiction)
    exact h.1
  · change f.final.raw 0 0 = some (160 : ℝ)
    rw [f.raw_active]
    change some b.final.time = _
    rw [b.date]
  · intro j p h
    fin_cases j
    · exact f.raw_other 0 p (Or.inr (by simpa using h))
    · exact b.localB_raw_none p
  · intro j p
    fin_cases j
    · exact f.gain_preserved 0 p
    · rfl
  · intro j
    fin_cases j
    · exact f.recovery_preserved 0
    · rfl

namespace TwoCellFirstFire
variable {θ born} {c : ConstructedBirthPreparation θ born} {fresh newborn route}
    {b : ConstructedBBirth c fresh newborn route constructedBBirthSources} (f : TwoCellFirstFire b)

theorem charge : f.final.x 0 .q = 1 := by rw [f.a_coordinates]; exact f.firelocal.charge

theorem complete (hr : ∀ d ∈ route 0 f.final.time, f.final.time < d.due) :
    CompleteThrough f.execution f.final.time := by
  have hfuture : ∀ d ∈ f.final.pending, f.final.time < d.due := by
    intro d hd
    rw [f.pending] at hd
    rcases List.mem_append.mp hd with h | h
    · linarith [ConstructedBBirth.queue_future d h,f.deadline]
    · exact hr d h
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro j
      by_cases hj : j = 0
      · subst j
        rw [f.a_main_fast]
        rw [f.charge]
        norm_num
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [f.b_ready.ready]
        linarith [f.b_ready.charge.2]
    · intro j p
      by_cases hj : j = 0
      · subst j
        by_cases hp : p = 0
        · subst p
          rw [f.a_aux_silent]
          exact f.a_sensor_above
        · rw [(f.a_aux_other p hp).1]
          linarith [(f.a_aux_other p hp).2.2]
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [(f.b_ready.auxiliary p).1]
        linarith [(f.b_ready.auxiliary p).2.2]
  · intro j p origin hraw
    by_cases h : j = 0 ∧ p = 0
    · rcases h with ⟨rfl,rfl⟩
      have he : origin = (160 : ℝ) := Option.some.inj (hraw.symm.trans f.raw_active)
      rw [he]
      linarith [f.deadline]
    · rw [f.raw_other j p (by tauto)] at hraw
      contradiction
  · exact hfuture

/-- B remains on its own newborn relaxation curve, not on A's parameters. -/
theorem b_gain (p : Port) : f.final.x 1 (.z p) = newborn.x (.z p) := by
  rw [f.gains,b.b_coordinates]

theorem b_recovery : f.final.x 1 .b = newborn.x .b := by
  rw [f.recovery,b.b_coordinates]

end TwoCellFirstFire

/-- During the first actual A firing the return contact is closed. The
freshly created token uses the delay at this actual firing time. -/
theorem TwoCellFirstFire.protocol_route {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (f : TwoCellFirstFire b) :
    reciprocalEntryRouter forward backward 0 f.final.time =
      [⟨1,1,f.final.time + forward f.final.time⟩] := by
  classical
  rw [reciprocalEntryRouter.before_reverse forward backward 0 (by linarith [f.deadline])]
  have hg : (160 : ℝ) ≤ f.final.time ∧ f.final.time < 310 := by
    constructor <;> linarith [f.early,f.deadline]
  simp [Contact.route,teachingContact,hg.1,hg.2,Contact.token]

theorem TwoCellFirstFire.protocol_pending {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (f : TwoCellFirstFire b) :
    f.final.pending = constructedBBirthQueue ++ [⟨1,1,f.final.time + forward f.final.time⟩] := by
  rw [f.pending,f.protocol_route]

theorem TwoCellFirstFire.protocol_complete {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (f : TwoCellFirstFire b) (hf : ∀ t, (3 / 10 : ℝ) ≤ forward t) :
    CompleteThrough f.execution f.final.time := by
  apply f.complete
  intro d hd
  rw [f.protocol_route] at hd
  have he := List.mem_singleton.mp hd
  subst d
  change f.final.time < f.final.time + forward f.final.time
  linarith [hf f.final.time]

/-- The first genuine post-birth output and its one pending wire token are
exhibited without any supplied firing date, pulse word or output calendar. -/
theorem protocol_two_cell_first_fire_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources)
    (hf : ∀ t, (3 / 10 : ℝ) ≤ forward t) :
    ∃ f : TwoCellFirstFire b, CompleteThrough f.execution f.final.time ∧
      f.final.pending = constructedBBirthQueue ++ [⟨1,1,f.final.time + forward f.final.time⟩] ∧
      (160 + 7 / 10 : ℝ) < f.final.time + forward f.final.time := by
  obtain ⟨f⟩ := two_cell_first_fire_exists hb b
  refine ⟨f,f.protocol_complete hf,f.protocol_pending,?_⟩
  linarith [f.early,hf f.final.time]

end KernelR.Hybrid
