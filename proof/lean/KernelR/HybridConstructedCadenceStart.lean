import KernelR.HybridBirthCTeaching
import KernelR.HybridCadenceRouter
import KernelR.HybridCadenceWeakStages

/-! The completed C teaching history reaches its genuine first period-four
source. Only the router changes: quiet evolution carries all three physical
states to640, then the actual queued C token is consumed. -/
namespace KernelR.Hybrid

structure ConstructedCadenceStart {θ born freshB freshC newbornB newbornC forward backward delay}
    (c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay)
    (cascadeForward cascadeBackward : ℝ → ℝ) where
  before : Snapshot 3
  final : Snapshot 3
  wait : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) c.final before
  arrival : Jump (cadenceRouter cascadeForward cascadeBackward) before final
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) c.final final
  reconstruct_execution : execution = wait.append (.cons (.jump arrival) (.nil _))
  before_state : before = quietAt c.final 640
  date : final.time = 640
  values : ∀ i, final.x i = (quietAt c.final 640).x i
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_active : final.raw 2 0 = some (640 : ℝ)
  raw_other : ∀ i q, i ≠ 2 ∨ q ≠ 0 → final.raw i q = none
  pending : final.pending = sourceTrain 2 0 644 4 24
  gains : ∀ i q, final.x i (.z q) = c.final.x i (.z q)
  recovery : ∀ i, final.x i .b = c.final.x i .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨2,0,640⟩]
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (640 : ℝ)

theorem constructed_cadence_start_exists {θ born freshB freshC newbornB newbornC forward backward delay ε}
    (c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (cascadeForward cascadeBackward : ℝ → ℝ) :
    Nonempty (ConstructedCadenceStart c cascadeForward cascadeBackward) := by
  have htime : c.final.time < (640 : ℝ) := by rw [c.date]; norm_num
  have hQ : ∀ d ∈ c.final.pending, (640 : ℝ) ≤ d.due := by
    intro d hd
    rw [c.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    dsimp
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  let flow : Flow (extendParameters (extendParameters θ freshB) freshC)
      c.final (quietAt c.final 640) := quietFlow c.final htime
    (fun i => (c.prepared i).ready) (fun i q => ((c.prepared i).auxiliary q).1) c.raw_none
    (fun i => by rw [c.charge]; norm_num)
    (fun i q => by linarith [((c.prepared i).auxiliary q).2.2]) hQ
  let before := quietAt c.final 640
  let wait : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cadenceRouter cascadeForward cascadeBackward) c.final before := .cons (.flow flow) (.nil _)
  let final : Snapshot 3 := {(setRaw before 2 0 (some (640 : ℝ))) with pending := sourceTrain 2 0 644 4 24}
  have hhead : before.pending = [] ++ (⟨2,0,640⟩ : Delivery 3) :: sourceTrain 2 0 644 4 24 := by
    change c.final.pending = _
    rw [c.pending,sourceTrain_succ]
    norm_num
  let arrival : Jump (cadenceRouter cascadeForward cascadeBackward) before final :=
    .arrive before ⟨2,0,640⟩ [] (sourceTrain 2 0 644 4 24) hhead rfl (c.raw_none 2 0)
  let trace := wait.append (.cons (.jump arrival) (.nil _))
  have hready : ∀ i, ReadyCoordinates before i := fun i =>
    quietAt_ready_coordinates c.final i (c.prepared i).ready_coordinates htime.le
  have hprepared : ∀ i, PreparedSection final i := fun i =>
    ⟨(hready i).ready,(hready i).charge,(c.prepared i).recovery,(hready i).auxiliary⟩
  have hcharge : ∀ i, final.x i .q = 1 / 10 := by
    intro i
    change relax (1 / 2) (1 / 10) (c.final.x i .q) c.final.time 640 = _
    rw [c.charge]
    simp [relax]
  have hraw : ∀ i q, i ≠ 2 ∨ q ≠ 0 → final.raw i q = none := by
    intro i q h
    change (setRaw before 2 0 (some (640 : ℝ))).raw i q = none
    rw [raw_update_other _ _ _ _ _ _ h]
    exact c.raw_none i q
  have hactive : final.raw 2 0 = some (640 : ℝ) := by simp [final,setRaw]
  have hfuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change (640 : ℝ) < 644 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  have hcomplete : CompleteThrough trace (640 : ℝ) := by
    refine ⟨rfl,?_,hfuture⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i; rw [(hprepared i).ready,hcharge]; norm_num
      · intro i q
        rw [((hprepared i).auxiliary q).1]
        linarith [((hprepared i).auxiliary q).2.2]
    · intro i q origin hr
      by_cases h : i = 2 ∧ q = 0
      · obtain ⟨rfl,rfl⟩ := h
        have ho : origin = (640 : ℝ) := Option.some.inj (hr.symm.trans hactive)
        rw [ho]; change (640 : ℝ) < 640 + 1; norm_num
      · rw [hraw i q (by tauto)] at hr; contradiction
    · exact hfuture
  exact ⟨{
    before := before, final := final, wait := wait, arrival := arrival, execution := trace
    reconstruct_execution := rfl, before_state := rfl, date := rfl, values := fun _ => rfl
    prepared := hprepared, charge := hcharge, raw_active := hactive, raw_other := hraw, pending := rfl
    gains := fun _ _ => rfl, recovery := fun _ => rfl
    emissions := rfl, deliveries := rfl
    physical := trace.physical_invariant hb c.physical
    raw_valid := trace.raw_valid c.raw_valid, complete := hcomplete
  }⟩

namespace ConstructedCadenceStart
variable {θ born freshB freshC newbornB newbornC forward backward delay}
  {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
  {cascadeForward cascadeBackward} (s : ConstructedCadenceStart c cascadeForward cascadeBackward)

/-- The existing two-cell projection is specialized to dimension2; this
three-cell projection retains the same single-cell coordinate convention. -/
noncomputable def cellProjection (i : Fin 3) (Q : List (Delivery 1)) : Snapshot 1 where
  time := s.final.time
  x := fun _ => s.final.x i
  main := fun _ => s.final.main i
  aux := fun _ => s.final.aux i
  raw := fun _ => s.final.raw i
  pending := Q

noncomputable def sC : Snapshot 1 := s.cellProjection 2 (sourceTrain 0 0 644 4 24)
noncomputable def quietA : Snapshot 1 := s.cellProjection 0 []
noncomputable def quietB : Snapshot 1 := s.cellProjection 1 []

theorem c_date : s.sC.time = 640 := s.date

theorem c_pending : s.sC.pending = sourceTrain 0 0 644 4 24 := rfl

theorem c_pending_length : s.sC.pending.length = 24 := by
  rw [s.c_pending]
  simp only [sourceTrain,List.length_ofFn]

theorem c_prepared (i : Fin 1) : PreparedSection s.sC i :=
  ⟨(s.prepared 2).ready,(s.prepared 2).charge,(s.prepared 2).recovery,(s.prepared 2).auxiliary⟩

theorem c_charge (i : Fin 1) : s.sC.x i .q = 1 / 10 := s.charge 2

theorem c_raw_active : s.sC.raw 0 0 = some s.sC.time := by rw [s.c_date]; exact s.raw_active

theorem c_raw_other (q : Port) (hq : q ≠ 0) : s.sC.raw 0 q = none := s.raw_other 2 q (Or.inr hq)

theorem c_physical : PhysicalInvariant (fun _ : Fin 1 => freshC) s.sC := by
  refine ⟨fun _ => s.physical.region 2,?_,fun _ => s.physical.recovery_cap 2,fun _ => s.physical.reserve 2⟩
  intro i q
  exact s.physical.gain_cap 2 q

theorem c_raw_valid : RawValid s.sC := fun _ q origin h => s.raw_valid 2 q origin h

theorem c_gain_own (q : Port) : s.sC.x 0 (.z q) = c.final.x 2 (.z q) := s.gains 2 q

theorem c_gain_low : Real.log (3 / 10) - 1 / 100000 ≤ s.sC.x 0 (.z 0) ∧
    s.sC.x 0 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000 := by
  rw [s.c_gain_own,c.c_gain_other 0 (by decide)]
  simpa only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] using newbornC.gain (0 : Port)

theorem c_gain_exp_upper : Real.exp (s.sC.x 0 (.z 0)) ≤ 1 / 3 := by
  have h := cadenceWeak_raw_gain_upper (0 : Fin 3) (z := s.sC.x 0 (.z 0))
    (by norm_num; linarith [s.c_gain_low.2])
  simpa [cadenceWeakDriveCap] using h

theorem c_recovery_own : s.sC.x 0 .b = newbornC.x .b + 1 / 10 :=
  (s.recovery 2).trans c.c_recovery

theorem c_recovery_band : 17999 / 100000 ≤ s.sC.x 0 .b ∧ s.sC.x 0 .b ≤ 18001 / 100000 := by
  rw [s.c_recovery_own]
  constructor <;> linarith [newbornC.recovery.1,newbornC.recovery.2]

theorem quiet_a_date : s.quietA.time = 640 := s.date

theorem quiet_b_date : s.quietB.time = 640 := s.date

theorem quiet_a_prepared (i : Fin 1) : PreparedSection s.quietA i :=
  ⟨(s.prepared 0).ready,(s.prepared 0).charge,(s.prepared 0).recovery,(s.prepared 0).auxiliary⟩

theorem quiet_b_prepared (i : Fin 1) : PreparedSection s.quietB i :=
  ⟨(s.prepared 1).ready,(s.prepared 1).charge,(s.prepared 1).recovery,(s.prepared 1).auxiliary⟩

theorem quiet_a_raw_none (i : Fin 1) (q : Port) : s.quietA.raw i q = none :=
  s.raw_other 0 q (Or.inl (by decide))

theorem quiet_b_raw_none (i : Fin 1) (q : Port) : s.quietB.raw i q = none :=
  s.raw_other 1 q (Or.inl (by decide))

theorem quiet_a_pending : s.quietA.pending = [] := rfl

theorem quiet_b_pending : s.quietB.pending = [] := rfl

theorem queue_map : (s.sC.pending.map Delivery.succ).map Delivery.succ = s.final.pending := by
  rw [s.pending,s.c_pending]
  simp [sourceTrain,Delivery.succ]

theorem reconstruct : (s.sC.prependQuiet s.quietB).prependQuiet s.quietA = s.final := by
  have extensionality {n} (a b : Snapshot n)
      (ht : a.time = b.time) (hx : a.x = b.x) (hm : a.main = b.main)
      (ha : a.aux = b.aux) (hr : a.raw = b.raw) (hp : a.pending = b.pending) : a = b := by
    cases a; cases b; simp_all only
  apply extensionality
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i q; fin_cases i <;> rfl
  · funext i q; fin_cases i <;> rfl
  · exact s.queue_map

theorem parameters_nested :
    prependParameters θ (prependParameters (fun _ : Fin 1 => freshB) (fun _ : Fin 1 => freshC)) =
      extendParameters (extendParameters θ freshB) freshC := by
  funext i
  fin_cases i <;> rfl

theorem error_zero (i : Fin 3) (q : Port) : s.execution.ledger.error i q = 0 := by
  have h := s.execution.gain_balance i q
  rw [s.gains] at h
  linarith

theorem recovery_zero (i : Fin 3) : s.execution.ledger.recovery i = 0 := by
  have h := s.execution.recovery_balance i
  rw [s.recovery] at h
  linarith

end ConstructedCadenceStart
end KernelR.Hybrid
