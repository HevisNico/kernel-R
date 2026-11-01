import KernelR.HybridFirstInterleavedPair
import KernelR.HybridGuardedQuietProduct
import KernelR.HybridReceiverQuietReady
import KernelR.HybridSameGainLatency

/-! The second real A firing is constructed from source168, alongside the
actual receiver residue. Its wire token is created only by the global FIRE. -/
namespace KernelR.Hybrid
namespace FirstInterleavedPair
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} (s : FirstInterleavedPair r)

noncomputable def localA : Snapshot 1 := s.final.cellProjection 0 []
noncomputable def localB : Snapshot 1 := s.receiver.cut168.state

theorem product_initial : s.localA.product s.localB firstInterleavedPending = s.final := by
  have extensionality {n} (a u : Snapshot n) (ht : a.time = u.time) (hx : a.x = u.x)
      (hm : a.main = u.main) (ha : a.aux = u.aux) (hr : a.raw = u.raw)
      (hp : a.pending = u.pending) : a = u := by
    cases a
    cases u
    simp_all only
  apply extensionality
  · rfl
  · funext j
    by_cases hj : j = 0
    · subst j; rfl
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; exact s.b_values.symm
  · funext j
    by_cases hj : j = 0
    · subst j; rfl
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; exact s.b_main.symm
  · funext j
    by_cases hj : j = 0
    · subst j; rfl
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; funext p; exact (s.b_aux p).symm
  · funext j
    by_cases hj : j = 0
    · subst j; rfl
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; funext p; exact (s.b_raw p).symm
  · exact s.pending.symm

theorem localA_physical : PhysicalInvariant θ s.localA := by
  have hθ : extendParameters θ fresh (0 : Fin 2) = θ (0 : Fin 1) := rfl
  refine ⟨fun j => s.physical.region 0,?_,fun j => s.physical.recovery_cap 0,
    fun j => s.physical.reserve 0⟩
  intro j p
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simpa only [localA,Snapshot.cellProjection,hθ] using s.physical.gain_cap 0 p

theorem localA_raw_valid : RawValid s.localA := fun _ p o h => s.raw_valid 0 p o h

theorem localA_ready : ∀ j, ReadyCoordinates s.localA j :=
  fun _ => ⟨s.a_prepared.ready,s.a_prepared.charge,s.a_prepared.auxiliary⟩

theorem localA_gain {ε} (hb : PhysicalBox θ ε) :
    9 / 5 ≤ Real.exp (s.localA.x 0 (.z 0)) ∧ Real.exp (s.localA.x 0 (.z 0)) ≤ 2 := by
  have h := b.localA_gain hb
  change 9 / 5 ≤ Real.exp (s.final.x 0 (.z 0)) ∧ Real.exp (s.final.x 0 (.z 0)) ≤ 2
  rw [s.a_gains]
  exact h

theorem local_clock : s.localA.time = s.localB.time := s.date.trans s.receiver.cut168.date.symm

theorem queue_future (d : Delivery 2) (hd : d ∈ firstInterleavedPending) : (176 : ℝ) ≤ d.due := by
  simp only [firstInterleavedPending,constructedBBirthSources,List.mem_append] at hd
  rcases hd with hd | hd | hd <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd <;>
    change (176 : ℝ) ≤ _ + 8 * (k.val : ℝ) <;> nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

end FirstInterleavedPair

structure SecondSenderFire {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} (s : FirstInterleavedPair r) where
  firelocal : FirstLearnedFire θ (fun _ _ => []) s.localA 0 0
  before : Snapshot 2
  final : Snapshot 2
  span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s.final before
  fire : Jump (reciprocalEntryRouter forward backward) before final
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s.final final
  product_before : before = firelocal.before.product (quietAt s.localB before.time) firstInterleavedPending
  product_final : final = firelocal.final.product (quietAt s.localB final.time)
    (firstInterleavedPending ++ reciprocalEntryRouter forward backward 0 final.time)
  date : final.time = 168 + firelocal.latency
  early : 168 + 2 / 5 < final.time
  deadline : final.time < 168 + 9 / 10
  firing_gap : final.time = r.fire.final.time + 8
  pending : final.pending = firstInterleavedPending ++ reciprocalEntryRouter forward backward 0 final.time
  span_emissions : span.ledger.emissions = []
  span_deliveries : span.deliveries = []
  emissions : execution.ledger.emissions = [(0,final.time)]
  deliveries : execution.deliveries = []
  a_coordinates : final.x 0 = firelocal.final.x 0
  b_coordinates : final.x 1 = (quietAt s.localB final.time).x 0
  a_main_fast : final.main 0 = .fast
  a_aux_silent : final.aux 0 0 = .silent
  a_sensor_above : 1 / 10 < final.x 0 (.m 0)
  a_aux_other : ∀ p, p ≠ 0 → final.aux 0 p = .ready ∧ RestBand (final.x 0 (.m p))
  b_ready : ReadyCoordinates final 1
  raw_active : final.raw 0 0 = some (168 : ℝ)
  raw_other : ∀ j p, j ≠ 0 ∨ p ≠ 0 → final.raw j p = none
  gains : ∀ j p, final.x j (.z p) = s.final.x j (.z p)
  recovery : ∀ j, final.x j .b = s.final.x j .b
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Construct the current sensor crossings and actual A threshold, weave its
pre-FIRE trace with the current quiet B residue, then issue the wire token. -/
theorem second_sender_fire_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (s : FirstInterleavedPair r)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (SecondSenderFire s) := by
  have hg := s.localA_gain hb.extend_old
  have hr : s.localA.raw 0 0 = some s.localA.time := by
    change s.final.raw 0 0 = some s.final.time
    rw [s.date]
    exact s.raw_active
  have ho : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ 0 → s.localA.raw j p = none := by
    intro j p h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.raw_other_a p (by simpa using h)
  obtain ⟨f⟩ := first_learned_fire_exists (route := fun _ _ => []) s.localA hb.extend_old
    s.localA_physical s.localA_raw_valid 0 0 s.localA_ready hg hr ho (by
      intro d hd
      change d ∈ ([] : List (Delivery 1)) at hd
      contradiction)
  have htime : f.before.time = 168 + f.latency := by change s.final.time + _ = _; rw [s.date]
  have hearly : 168 + 2 / 5 < f.before.time := by
    have h := readyPulse_root_after_four_tenths (s.localA_ready 0).charge.2 hg.2
      (by linarith [f.early] : s.localA.time ≤ s.localA.time + f.latency) f.response_root
    change s.final.time + 2 / 5 < s.final.time + f.latency at h
    rw [s.date] at h
    rw [htime]
    exact h
  have hend : f.before.time < 168 + 9 / 10 := by rw [htime]; linarith [f.deadline]
  have hqOld : b.localA.x 0 .q = 1 / 10 := b.a_charge
  have hqNew : s.localA.x 0 .q = 1 / 10 := s.a_charge
  have hz : b.localA.x 0 (.z 0) = s.localA.x 0 (.z 0) := by
    change b.final.x 0 (.z 0) = s.final.x 0 (.z 0)
    exact (s.a_gains 0).symm
  have hstep : s.localA.time = b.localA.time + 8 := by
    change s.final.time = b.final.time + 8
    rw [s.date,b.date]
    norm_num
  have hgapLocal := r.fire.firelocal.firing_gap_eight_of_rest_gain f hqOld hqNew hz hstep
  have hclockOld : r.fire.firelocal.final.time = r.fire.final.time :=
    (congrArg Snapshot.time r.fire.product_final).symm
  have hgap : f.before.time = r.fire.final.time + 8 := by
    change f.final.time = _
    rw [hgapLocal,hclockOld]
  have hBreturn : r.final.time + 15 / 2 ≤ f.before.time := by
    rw [r.date,hgap]
    linarith [(hdelay r.fire.final.time).2]
  have hBready := s.receiver.quiet_after_cut_ready hb hdelay hBreturn
  have hQ : ∀ d ∈ firstInterleavedPending, f.before.time ≤ d.due := by
    intro d hd
    linarith [FirstInterleavedPair.queue_future d hd]
  have hmB : s.localB.main 0 = .ready := s.receiver.cut_main_ready
  have haB : ∀ p, s.localB.aux 0 p = .ready := fun p => (s.receiver.cut_aux_rest hb hdelay p).1
  have hqB : s.localB.x 0 .q < 1 := by
    have h := s.receiver.before_guards.1 0
    rw [s.receiver.cut_main_ready] at h
    exact h
  have hxB : ∀ p, s.localB.x 0 (.m p) < 1 := by
    intro p
    have h := s.receiver.before_guards.2 0 p
    rw [(s.receiver.cut_aux_rest hb hdelay p).1] at h
    exact h
  obtain ⟨lifted,hle,hld⟩ := f.beforeExecution.product_with_guarded_quiet_left
    (θB := fun _ : Fin 1 => fresh) f.before_emissions f.before_deliveries s.localB s.local_clock
    hmB haB (s.receiver.cut_raw_none hdelay) hqB hxB firstInterleavedPending hQ
    (reciprocalEntryRouter forward backward)
  let before := f.before.product (quietAt s.localB f.before.time) firstInterleavedPending
  let final := f.final.product (quietAt s.localB f.before.time)
    (firstInterleavedPending ++ reciprocalEntryRouter forward backward 0 f.before.time)
  let span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s.final before :=
    lifted.cast_source s.product_initial.symm
  have hmode : before.main 0 = .ready := f.firstSilent.main_ready 0
  have hthreshold : before.x 0 .q = 1 := f.threshold
  have hfinal : final = { (setMain before 0 .fast) with
      pending := before.pending ++ reciprocalEntryRouter forward backward 0 before.time } := by
    dsimp [final,before]
    rw [f.final_empty,Snapshot.product_setMain_left]
    rfl
  let jump : Jump (reciprocalEntryRouter forward backward) before final :=
    hfinal.symm ▸ Jump.fire before 0 hmode hthreshold
  let e : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s.final final :=
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
  refine ⟨{
    firelocal := f, before := before, final := final, span := span, fire := jump, execution := e
    product_before := rfl, product_final := rfl, date := htime, early := hearly, deadline := hend
    firing_gap := hgap, pending := rfl, span_emissions := hsEm, span_deliveries := hsDel
    emissions := ?_, deliveries := ?_, a_coordinates := rfl, b_coordinates := rfl
    a_main_fast := hFast, a_aux_silent := f.aux_silent, a_sensor_above := f.sensor_above
    a_aux_other := ?_, b_ready := ⟨hBready.ready,hBready.charge,hBready.auxiliary⟩
    raw_active := ?_, raw_other := ?_, gains := ?_, recovery := ?_
    physical := e.physical_invariant hb s.physical, raw_valid := e.raw_valid s.raw_valid
  }⟩
  · simp only [e,Execution.emissions_append,hsEm,Execution.ledger,Move.ledger,
      hjEm,Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
    rfl
  · simp only [e,Execution.deliveries_append,hsDel,Execution.deliveries,Move.deliveries,
      hjDel,List.append_nil]
  · intro p hp0
    have h := f.execution.aux_no_input_rest_band 0 p ((s.localA_ready 0).auxiliary p).1
      ((s.localA_ready 0).auxiliary p).2 (ho 0 p (Or.inr hp0)) (by
        intro d hd
        rw [f.deliveries] at hd
        contradiction)
    exact h.1
  · change f.final.raw 0 0 = some (168 : ℝ)
    rw [f.raw_active]
    change some s.final.time = _
    rw [s.date]
  · intro j p h
    fin_cases j
    · exact f.raw_other 0 p (Or.inr (by simpa using h))
    · exact s.receiver.cut_raw_none hdelay p
  · intro j p
    fin_cases j
    · exact f.gain_preserved 0 p
    · exact (congrFun s.b_values (.z p)).symm
  · intro j
    fin_cases j
    · exact f.recovery_preserved 0
    · exact (congrFun s.b_values .b).symm

namespace SecondSenderFire
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} (f : SecondSenderFire s)

theorem charge : f.final.x 0 .q = 1 := by rw [f.a_coordinates]; exact f.firelocal.charge

theorem protocol_route : reciprocalEntryRouter forward backward 0 f.final.time =
    [⟨1,1,f.final.time + forward f.final.time⟩] := by
  classical
  rw [reciprocalEntryRouter.before_reverse forward backward 0 (by linarith [f.deadline])]
  have hg : (160 : ℝ) ≤ f.final.time ∧ f.final.time < 310 := by
    constructor <;> linarith [f.early,f.deadline]
  simp [Contact.route,teachingContact,hg.1,hg.2,Contact.token]

theorem protocol_pending : f.final.pending = firstInterleavedPending ++
    [⟨1,1,f.final.time + forward f.final.time⟩] := by rw [f.pending,f.protocol_route]

theorem pending_length : f.final.pending.length = 47 := by
  rw [f.protocol_pending]
  simp [firstInterleavedPending,constructedBBirthSources,sourceTrain]

theorem received_gap
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    79 / 10 ≤ (f.final.time + forward f.final.time) - r.final.time ∧
      (f.final.time + forward f.final.time) - r.final.time ≤ 81 / 10 := by
  rw [r.date]
  exact received_gap_eight_of_fire_gap f.firing_gap (hdelay r.fire.final.time) (hdelay f.final.time)

theorem b_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    f.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [f.gains,s.b_gain_target hb hdelay]

theorem b_recovery : f.final.x 1 .b = newborn.x .b := by rw [f.recovery,s.b_recovery]

theorem complete
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    CompleteThrough f.execution f.final.time := by
  have hfuture : ∀ d ∈ f.final.pending, f.final.time < d.due := by
    intro d hd
    rw [f.protocol_pending] at hd
    rcases List.mem_append.mp hd with h | h
    · linarith [FirstInterleavedPair.queue_future d h,f.deadline]
    · have he := List.mem_singleton.mp h
      subst d
      change f.final.time < f.final.time + forward f.final.time
      linarith [(hdelay f.final.time).1]
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro j
      by_cases hj : j = 0
      · subst j
        rw [f.a_main_fast,f.charge]
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
      have he : origin = (168 : ℝ) := Option.some.inj (hraw.symm.trans f.raw_active)
      rw [he]
      linarith [f.deadline]
    · rw [f.raw_other j p (by tauto)] at hraw
      contradiction
  · exact hfuture

end SecondSenderFire
end KernelR.Hybrid
