import KernelR.HybridProtectedInputCycle

/-! A protected input is physically completed by 6.5 after its actual source. -/
namespace KernelR.Hybrid
open Set

structure ShortProtectedReturn (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) (source : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  date : final.time = source + 13 / 2
  prepared : ∀ j, PreparedSection final j
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j p, final.raw j p = none
  gains : ∀ j p, final.x j (.z p) = s.x j (.z p)
  recovery : ∀ j, final.x j .b = s.x j .b
  pending : final.pending = s.pending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (source + 13 / 2)
  returnState : Snapshot 1
  returnSpan : Execution θ route s returnState
  returnRest : Execution θ route returnState final
  reconstruct : execution = returnSpan.append returnRest
  returnDate : returnState.time = s.time + slowReopenDuration s 0
  returnDeadline : returnState.time < source + 65 / 12
  returnReady : returnState.main 0 = .ready
  returnCharge : returnState.x 0 .q = 1 / 10

theorem protected_short_return_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1)
    (source : ℝ) (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 1 / 10 < s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hbown : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (ha : ∀ p, s.aux 0 p = .ready ∧ RestBand (s.x 0 (.m p)))
    (hr : ∀ j p, s.raw j p = none)
    (htime : s.time < source + 17 / 12)
    (hp : ∀ d ∈ s.pending, source + 31 / 4 ≤ d.due) : Nonempty (ShortProtectedReturn θ route s source) := by
  have hD := slowReopenDuration_bounds s 0 hq hbown
  have hbpos : 0 < s.x 0 .b := by linarith [hbown.1]
  have hqpos : 1 / 10 < s.x 0 .q := hq.1
  let T := s.time + slowReopenDuration s 0
  let horizon := source + 13 / 2
  have hT : s.time < T := by dsimp [T]; linarith [hD.1]
  have hwait : T < horizon := by dsimp [T,horizon]; linarith [hD.2]
  have hmo : ∀ j : Fin 1, j ≠ 0 → s.main j = .ready := by intro j hj; exact (hj (Subsingleton.elim _ _)).elim
  have hao : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ (0 : Port) → s.aux j p = .ready := by
    intro j p _
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (ha p).1
  have hqOther : ∀ j : Fin 1, j ≠ 0 → s.x j .q < 1 := by intro j hj; exact (hj (Subsingleton.elim _ _)).elim
  have hmOther : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ (0 : Port) → s.x j (.m p) < 1 := by
    intro j p _
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    linarith [(ha p).2.2]
  let slowFlow : Flow θ s (protectedMainEnd θ s 0 0 .slow .ready none T) :=
    protectedMainFlow s 0 0 .slow .ready none hT (Or.inr rfl) (Or.inl rfl) hm hmo (ha 0).1 hao
      (hr 0 0) (fun j p _ => hr j p) (by intros; contradiction) hqOther hmOther
      (by intro t ht; simpa [protectedMainRate] using slowReopen_preguard s 0 hqpos hbpos ht.2)
      (by intro t ht; simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax];
          exact relax_lt (by norm_num) ht.1 (by linarith [(ha 0).2.2]) (by norm_num))
      (fun d hd => by dsimp [horizon] at hwait; linarith [hp d hd])
  let before := protectedMainEnd θ s 0 0 .slow .ready none T
  have hthreshold : before.x 0 .q = 1 / 10 := by
    simpa [before,protectedMainEnd,protectedMainValues,protectedMainRate,T] using slowReopen_root s 0 hqpos hbpos
  let reopened := setMain before 0 .ready
  let head : Execution θ route s reopened :=
    .cons (.flow slowFlow) (.cons (.jump (.reopen before 0 hm hthreshold)) (.nil _))
  have haux : ∀ j p, reopened.aux j p = .ready ∧ RestBand (reopened.x j (.m p)) := by
    intro j p
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    constructor
    · exact (ha p).1
    · have hband := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (ha p).2
        (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
      by_cases hp : p = 0
      · subst p
        simpa [reopened,setMain,before,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hband
      · simpa [reopened,setMain,before,protectedMainEnd,protectedMainValues,hp,RestBand] using hband
  have hready : ∀ j, ReadyCoordinates reopened j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    refine ⟨by simp [reopened,setMain],?_,haux 0⟩
    change 1 / 10 - 1 / 100000 ≤ before.x 0 .q ∧ before.x 0 .q ≤ 7 / 50
    rw [hthreshold]
    constructor <;> norm_num
  have hraw : ∀ j p, reopened.raw j p = none := hr
  have hfuture : ∀ d ∈ reopened.pending, horizon < d.due := by
    intro d hd
    change d ∈ s.pending at hd
    dsimp [horizon]
    linarith [hp d hd]
  let waitFlow : Flow θ reopened (quietAt reopened horizon) := quietFlow reopened hwait
    (fun j => (hready j).ready) (fun j p => (haux j p).1) hraw
    (fun j => by linarith [(hready j).charge.2]) (fun j p => by linarith [(haux j p).2.2])
    (fun d hd => (hfuture d hd).le)
  let wait : Execution θ route reopened (quietAt reopened horizon) := .cons (.flow waitFlow) (.nil _)
  let final := quietAt reopened horizon
  let e := head.append wait
  have hfinalReady : ∀ j, ReadyCoordinates final j := fun j => quietAt_ready_coordinates reopened j (hready j) hwait.le
  have hfinalQ : final.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (before.x 0 .q) T horizon = 1 / 10
    rw [hthreshold]
    simp [relax]
  have hfinalRaw : ∀ j p, final.raw j p = none := hr
  have hfinalFuture : ∀ d ∈ final.pending, horizon < d.due := hfuture
  have hcomplete : CompleteThrough e horizon := by
    refine ⟨rfl,?_,hfinalFuture⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro j
        have h := hfinalReady j
        rw [h.ready]
        linarith [h.charge.2]
      · intro j p
        have h := (hfinalReady j).auxiliary p
        rw [h.1]
        linarith [h.2.2]
    · intro j p origin hraw
      rw [hfinalRaw j p] at hraw
      contradiction
    · exact hfinalFuture
  refine ⟨{
    final := final
    execution := e
    date := rfl
    prepared := ?_
    ready := hfinalReady
    charge := hfinalQ
    raw_none := hfinalRaw
    gains := fun _ _ => rfl
    recovery := fun _ => rfl
    pending := rfl
    emissions := rfl
    deliveries := rfl
    physical := e.physical_invariant hb hf
    raw_valid := e.raw_valid hv
    complete := hcomplete
    returnState := reopened
    returnSpan := head
    returnRest := wait
    reconstruct := rfl
    returnDate := rfl
    returnDeadline := by change T < source + 65 / 12; dsimp [T]; linarith [hD.2]
    returnReady := by simp [reopened,setMain]
    returnCharge := hthreshold
  }⟩
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact ⟨(hfinalReady 0).ready,(hfinalReady 0).charge,hbown,(hfinalReady 0).auxiliary⟩


/-- Three actual phases of one protected input. The initial quiet ports are
retained so that their zero MARK doses can also be proved on the full trace. -/
structure ProtectedInputShortCycle (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) where
  markPhase : SlowInputMark θ route s p
  auxPhase : PortProtectedAuxReturn θ route markPhase.final p s.time
  returnPhase : ShortProtectedReturn θ route auxPhase.final s.time
  auxiliary_initial : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q))
  raw_active_initial : s.raw 0 p = some s.time
  raw_other_initial : ∀ q, q ≠ p → s.raw 0 q = none

noncomputable def ProtectedInputShortCycle.final {θ route s p} (c : ProtectedInputShortCycle θ route s p) : Snapshot 1 :=
  c.returnPhase.final

noncomputable def ProtectedInputShortCycle.execution {θ route s p} (c : ProtectedInputShortCycle θ route s p) :
    Execution θ route s c.final :=
  c.markPhase.execution.append (c.auxPhase.execution.append c.returnPhase.execution)

/-- A SLOW input physically adds its own MARK recovery dose, completes the
protected sensor cycle, reopens at the actual logarithmic root, then waits.
No output calendar, phase word, dose or incoming execution is supplied. -/
theorem protected_input_short_cycle_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 7 / 50 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hbown : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 31 / 4 ≤ d.due) :
    Nonempty (ProtectedInputShortCycle θ route s p) := by
  obtain ⟨m⟩ := slow_input_mark_775_exists (route := route) hb s p hf hv hm hq hbown ha hr ho hp
  have hbm : 17999 / 100000 ≤ m.final.x 0 .b ∧ m.final.x 0 .b ≤ 18001 / 100000 := by
    rw [m.recovery_gain]
    constructor <;> linarith [hbown.1,hbown.2]
  have hpm : ∀ d ∈ m.final.pending, s.time + 31 / 4 ≤ d.due := by
    intro d hd
    rw [m.pending] at hd
    exact hp d hd
  obtain ⟨a⟩ := port_protected_aux_return_exists (route := route) hb m.final p s.time m.physical m.raw_valid
    ⟨m.early,m.deadline⟩ m.main_slow m.aux_silent m.sensor_charge m.charge hbm
    m.auxiliary_other m.raw_active m.raw_other hpm
  have hba : 17999 / 100000 ≤ a.final.x 0 .b ∧ a.final.x 0 .b ≤ 18001 / 100000 := by
    rw [a.recovery]
    exact hbm
  have hpa : ∀ d ∈ a.final.pending, s.time + 31 / 4 ≤ d.due := by
    intro d hd
    rw [a.pending] at hd
    exact hpm d hd
  obtain ⟨ret⟩ := protected_short_return_exists (route := route) hb a.final s.time a.physical a.raw_valid
    a.main_slow a.charge hba (fun q => ⟨a.auxiliary 0 q,a.rest q⟩) a.raw_none a.time_bounds.2 hpa
  exact ⟨⟨m,a,ret,ha,hr,ho⟩⟩

namespace ProtectedInputShortCycle
variable {θ route s p} (c : ProtectedInputShortCycle θ route s p)

theorem date : c.final.time = s.time + 13 / 2 := c.returnPhase.date

theorem prepared : ∀ j, PreparedSection c.final j := c.returnPhase.prepared

theorem ready : ∀ j, ReadyCoordinates c.final j := c.returnPhase.ready

theorem charge : c.final.x 0 .q = 1 / 10 := c.returnPhase.charge

theorem raw_none : ∀ j q, c.final.raw j q = none := c.returnPhase.raw_none

theorem pending : c.final.pending = s.pending :=
  c.returnPhase.pending.trans (c.auxPhase.pending.trans c.markPhase.pending)

theorem gains (j : Fin 1) (q : Port) : c.final.x j (.z q) = s.x j (.z q) := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact (c.returnPhase.gains 0 q).trans ((c.auxPhase.gains 0 q).trans (c.markPhase.gain_preserved q))

theorem recovery_gain : c.final.x 0 .b = s.x 0 .b + 1 / 10 :=
  (c.returnPhase.recovery 0).trans ((c.auxPhase.recovery 0).trans c.markPhase.recovery_gain)

theorem emissions : c.execution.ledger.emissions = [] := by
  change (c.markPhase.execution.append (c.auxPhase.execution.append c.returnPhase.execution)).ledger.emissions = []
  rw [Execution.emissions_append c.markPhase.execution (c.auxPhase.execution.append c.returnPhase.execution),
    c.markPhase.emissions,Execution.emissions_append c.auxPhase.execution c.returnPhase.execution,
    c.auxPhase.emissions,c.returnPhase.emissions]
  rfl

theorem deliveries : c.execution.deliveries = [] := by
  change (c.markPhase.execution.append (c.auxPhase.execution.append c.returnPhase.execution)).deliveries = []
  rw [Execution.deliveries_append c.markPhase.execution (c.auxPhase.execution.append c.returnPhase.execution),
    c.markPhase.deliveries,Execution.deliveries_append c.auxPhase.execution c.returnPhase.execution,
    c.auxPhase.deliveries,c.returnPhase.deliveries]
  rfl

theorem error_zero (q : Port) : c.execution.ledger.error 0 q = 0 := by
  have h := c.execution.gain_balance 0 q
  rw [c.gains] at h
  linarith

theorem mark_other (q : Port) (hq : q ≠ p) : c.execution.ledger.mark 0 q = 0 := by
  have hquiet := c.execution.aux_ready_without_input_band 0 q (c.auxiliary_initial q).1
    (c.auxiliary_initial q).2.2 (c.raw_other_initial q hq)
    (by simp [NoArrivalAt,c.deliveries])
  exact c.execution.mark_zero_aux 0 q .ready (by decide)
    (c.execution.allStates_aux_flows 0 q .ready hquiet)

theorem mark_dose : c.execution.ledger.mark 0 p = 1 / 10 := by
  have h := c.execution.recovery_balance 0
  rw [c.recovery_gain,c.execution.recovery_sum_marks 0,
    Finset.sum_eq_single p (fun q _ hq => c.mark_other q hq) (by simp)] at h
  linarith

theorem physical : PhysicalInvariant θ c.final := c.returnPhase.physical

theorem raw_valid : RawValid c.final := c.returnPhase.raw_valid

theorem complete : CompleteThrough c.execution (s.time + 13 / 2) := c.returnPhase.complete

/-- The own post-sensor charge reaches its physical SLOW root well before
6.5; this is the root used in the actual constructed return flow. -/
theorem reopen_deadline : c.auxPhase.final.time + slowReopenDuration c.auxPhase.final 0 < s.time + 65 / 12 := by
  have hb : 17999 / 100000 ≤ c.auxPhase.final.x 0 .b ∧ c.auxPhase.final.x 0 .b ≤ 18001 / 100000 := by
    have h := (c.prepared 0).recovery
    change 17999 / 100000 ≤ c.returnPhase.final.x 0 .b ∧ c.returnPhase.final.x 0 .b ≤ 18001 / 100000 at h
    rwa [c.returnPhase.recovery] at h
  have h := (slowReopenDuration_bounds c.auxPhase.final 0 c.auxPhase.charge hb).2
  linarith [c.auxPhase.time_bounds.2]

end ProtectedInputShortCycle

end KernelR.Hybrid
