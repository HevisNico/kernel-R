import KernelR.HybridContactTransversality
import KernelR.HybridSlowInputMarkExistence
import KernelR.HybridPreparedSlowReturn
import KernelR.HybridPortSlowAux

namespace KernelR.Hybrid
open Set

/-- The actual first sensor crossing, two physical flows and both auxiliary
jumps are built from the current SLOW section. No incoming execution or
learning dose is supplied, and all queued tokens retain their multiplicity. -/
theorem slow_input_mark_775_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 7 / 50 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hbown : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 31 / 4 ≤ d.due) : Nonempty (SlowInputMark θ route s p) := by
  obtain ⟨latency,hearly,hdeadline,hroot,hprior,hslope⟩ :=
    hb.first_sensor_crossing_transversal 0 p (ha p).2.1 (ha p).2.2
  let M := s.time + latency
  let beforeMark := protectedMainEnd θ s 0 p .slow .ready (some s.time) M
  have hM : s.time < M := by dsimp [M]; linarith
  have hmOther : ∀ j : Fin 1, j ≠ 0 → s.main j = .ready := by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))
  have haOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (ha q).1
  have hrOther : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho q (by simpa using h)
  have hqx : ∀ j : Fin 1, j ≠ 0 → s.x j .q < 1 := by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))
  have hmx : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    linarith [(ha q).2.2]
  have preCharge : ∀ t ∈ Icc s.time M, 1397 / 10000 ≤ s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) ∧
      s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) ≤ 4 / 25 := by
    intro t ht
    exact slow_input_mark_initial_charge hq hbown ht.1 (by dsimp [M] at ht; linarith [ht.2])
  let firstFlow := protectedMainFlow (θ := θ) s 0 p .slow .ready (some s.time) hM (Or.inr rfl) (Or.inl rfl)
    hm hmOther (ha p).1 haOther hr hrOther
    (by intro o he; cases Option.some.inj he; exact ⟨le_rfl,by dsimp [M]; linarith⟩)
    hqx hmx
    (by intro t ht; simp only [reduceCtorEq,ite_false,protectedMainRate]; linarith [(preCharge t ⟨ht.1,ht.2.le⟩).1])
    (by intro t ht; simpa [rawInputScale] using hprior t ht)
    (fun d hd => by dsimp [M]; linarith [hp d hd])
  have hthreshold : beforeMark.x 0 (.m p) = 1 := by
    simpa [beforeMark,protectedMainEnd,protectedMainValues,rawInputScale,M] using hroot
  let markStart := setAux beforeMark 0 p .mark
  let first : Execution θ route s markStart :=
    .cons (.flow firstFlow) (.cons (.jump (.mark _ 0 p (ha p).1 hthreshold)) (.nil _))
  have hmarkm : markStart.x 0 (.m p) = 1 := hthreshold
  have hmarkb : markStart.x 0 .b = s.x 0 .b := rfl
  have hmarkq : 1397 / 10000 ≤ markStart.x 0 .q ∧ markStart.x 0 .q ≤ 4 / 25 := by
    simpa [markStart,setAux,beforeMark,protectedMainEnd,protectedMainValues,protectedMainRate] using preCharge M ⟨hM.le,le_rfl⟩
  have hmarkB : 7999 / 100000 ≤ markStart.x 0 .b ∧ markStart.x 0 .b ≤ 8001 / 100000 := by rw [hmarkb]; exact hbown
  have hmarkhead : markStart.x 0 .b + (1 / 2) * (markStart.x 0 (.m p) - 4 / 5) < 11 / 10 := by
    rw [hmarkm,hmarkb]
    linarith [hbown.2]
  let T := markStart.time + slowMarkDuration θ markStart 0 p
  have hT : markStart.time < T := by dsimp [T]; linarith [slowMarkDuration_positive hb markStart 0 p (by rw [hmarkm]; norm_num)]
  have hTupper : T < s.time + 1 / 20 := by
    have hd := slowMarkDuration_upper hb markStart 0 p (by rw [hmarkm]; norm_num) hmarkm.le
    change s.time + latency + slowMarkDuration θ markStart 0 p < s.time + 1 / 20
    linarith
  have markCharge : ∀ t ∈ Icc markStart.time T, 17 / 125 ≤ slowMarkMain θ markStart 0 p t ∧
      slowMarkMain θ markStart 0 p t ≤ 4 / 25 := by
    intro t ht
    exact slow_input_mark_final_charge hb markStart p hmarkm hmarkq hmarkB ht.1 ht.2
  have hmarkmode : markStart.aux 0 p = .mark := by simp [markStart,setAux]
  have hmarkmain : markStart.main 0 = .slow := hm
  have hmOther' : ∀ j : Fin 1, j ≠ 0 → markStart.main j = .ready := by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))
  have haOther' : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → markStart.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ p := by simpa using h
    simpa [markStart,setAux,beforeMark,protectedMainEnd,hq] using (ha q).1
  have hr' : markStart.raw 0 p = some s.time := hr
  have hrOther' : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → markStart.raw j q = none := hrOther
  have hqx' : ∀ j : Fin 1, j ≠ 0 → markStart.x j .q < 1 := by intro j hj; exact False.elim (hj (Subsingleton.elim _ _))
  have hmx' : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → markStart.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hqp : q ≠ p := by simpa using h
    have hrest := relax_lt (rate := (1 / 2 : ℝ)) (target := (1 / 40 : ℝ))
      (initial := s.x 0 (.m q)) (start := s.time) (t := M)
      (by norm_num) hM.le (hmx 0 q (Or.inr hqp)) (by norm_num : (1 / 40 : ℝ) < 1)
    simpa [markStart,setAux,beforeMark,protectedMainEnd,protectedMainValues,hqp] using hrest
  let secondFlow := slowMarkFlow hb markStart 0 p (some s.time) hT le_rfl hmarkmain hmOther' hmarkmode haOther'
    hr' hrOther' (by rw [hmarkm]; norm_num) hmarkm.le ((first.physical_invariant hb hf).reserve 0) hmarkhead
    (by intro o he; cases Option.some.inj he; exact ⟨hM.le,by linarith⟩) hqx' hmx'
    (by intro t ht; linarith [(markCharge t ⟨ht.1,ht.2.le⟩).1])
    (fun d hd => by change d ∈ s.pending at hd; linarith [hp d hd])
  let final := setAux (slowMarkEnd θ markStart 0 p T) 0 p .silent
  let e : Execution θ route s final := first.append
    (.cons (.flow secondFlow) (.cons (.jump (.silent (slowMarkEnd θ markStart 0 p T) 0 p hmarkmode
      (slowMarkEnd_sensor hb markStart 0 p (by rw [hmarkm]; norm_num)))) (.nil _)))
  have firstContacts : first.ContactsTransversal := by
    simp only [first, Execution.ContactsTransversal, Jump.ContactTransversal, and_true]
    exact firstFlow.aux_contact_field_positive 0 p (ha p).1 hr
      (by change M < s.time + 1; dsimp [M]; linarith)
      (by simpa only [protectedMainEnd, M] using hslope)
  have contacts : e.ContactsTransversal := by
    simpa [e, Jump.ContactTransversal] using firstContacts
  have hno : ∀ q, NoArrivalAt e 0 q := by simp [NoArrivalAt,e,first,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries]
  refine ⟨{
    final := final
    execution := e
    contacts_transversal := contacts
    early := by change s.time + 1 / 100 < T; change s.time + 1 / 100 < s.time + latency + slowMarkDuration θ markStart 0 p; linarith [slowMarkDuration_positive hb markStart 0 p (by rw [hmarkm]; norm_num)]
    deadline := hTupper
    main_slow := hm
    aux_silent := by simp [final,setAux]
    auxiliary_other := fun q hq => (e.aux_no_input_rest_band 0 q (ha q).1 (ha q).2 (ho q hq) (hno q)).1
    sensor_charge := slowMarkEnd_sensor hb markStart 0 p (by rw [hmarkm]; norm_num)
    charge := markCharge T ⟨hT.le,le_rfl⟩
    recovery_gain := ?_
    gain_preserved := fun _ => rfl
    raw_active := hr
    raw_other := ho
    pending := rfl
    emissions := by simp [e,first,Execution.emissions_append,Execution.ledger,Move.ledger,Flow.ledger,Jump.ledger,Ledger.add,Ledger.zero]
    deliveries := by simp [e,first,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries]
    physical := e.physical_invariant hb hf
    raw_valid := e.raw_valid hv
  }⟩
  have h := slowMarkEnd_recovery hb markStart 0 p (by rw [hmarkm]; norm_num)
  rw [hmarkm,hmarkb] at h
  change (slowMarkEnd θ markStart 0 p (markStart.time + slowMarkDuration θ markStart 0 p)).x 0 .b = s.x 0 .b + 1 / 10
  linarith


/-- A current prepared SLOW state reaches its logarithmic return root, takes
its actual reopen jump, then waits until 7.5 after the source. No execution,
READY substitution or return date is supplied to the construction. -/
theorem protected_slow_return_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1)
    (source : ℝ) (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 1 / 10 < s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hbown : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (ha : ∀ p, s.aux 0 p = .ready ∧ RestBand (s.x 0 (.m p)))
    (hr : ∀ j p, s.raw j p = none)
    (htime : s.time < source + 17 / 12)
    (hp : ∀ d ∈ s.pending, source + 31 / 4 ≤ d.due) : Nonempty (PreparedSlowReturn θ route s source) := by
  have hD := slowReopenDuration_bounds s 0 hq hbown
  have hbpos : 0 < s.x 0 .b := by linarith [hbown.1]
  have hqpos : 1 / 10 < s.x 0 .q := hq.1
  let T := s.time + slowReopenDuration s 0
  let horizon := source + 15 / 2
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
    contacts_transversal := by simp [e, head, wait, Execution.ContactsTransversal, Jump.ContactTransversal]
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
  }⟩
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact ⟨(hfinalReady 0).ready,(hfinalReady 0).charge,hbown,(hfinalReady 0).auxiliary⟩


/-- Three actual phases of one protected input. The initial quiet ports are
retained so that their zero MARK doses can also be proved on the full trace. -/
structure ProtectedInputCycle (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) where
  markPhase : SlowInputMark θ route s p
  auxPhase : PortProtectedAuxReturn θ route markPhase.final p s.time
  returnPhase : PreparedSlowReturn θ route auxPhase.final s.time
  auxiliary_initial : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q))
  raw_active_initial : s.raw 0 p = some s.time
  raw_other_initial : ∀ q, q ≠ p → s.raw 0 q = none

noncomputable def ProtectedInputCycle.final {θ route s p} (c : ProtectedInputCycle θ route s p) : Snapshot 1 :=
  c.returnPhase.final

noncomputable def ProtectedInputCycle.execution {θ route s p} (c : ProtectedInputCycle θ route s p) :
    Execution θ route s c.final :=
  c.markPhase.execution.append (c.auxPhase.execution.append c.returnPhase.execution)

@[simp] theorem ProtectedInputCycle.contacts_transversal {θ route s p}
    (c : ProtectedInputCycle θ route s p) : c.execution.ContactsTransversal := by
  exact (Execution.contactsTransversal_append _ _).mpr
    ⟨c.markPhase.contacts_transversal, (Execution.contactsTransversal_append _ _).mpr
      ⟨c.auxPhase.contacts_transversal, c.returnPhase.contacts_transversal⟩⟩

/-- A SLOW input physically adds its own MARK recovery dose, completes the
protected sensor cycle, reopens at the actual logarithmic root, then waits.
No output calendar, phase word, dose or incoming execution is supplied. -/
theorem protected_input_cycle_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 7 / 50 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hbown : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 31 / 4 ≤ d.due) :
    Nonempty (ProtectedInputCycle θ route s p) := by
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
  obtain ⟨ret⟩ := protected_slow_return_exists (route := route) hb a.final s.time a.physical a.raw_valid
    a.main_slow a.charge hba (fun q => ⟨a.auxiliary 0 q,a.rest q⟩) a.raw_none a.time_bounds.2 hpa
  exact ⟨⟨m,a,ret,ha,hr,ho⟩⟩

namespace ProtectedInputCycle
variable {θ route s p} (c : ProtectedInputCycle θ route s p)

theorem date : c.final.time = s.time + 15 / 2 := c.returnPhase.date

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

theorem complete : CompleteThrough c.execution (s.time + 15 / 2) := c.returnPhase.complete

/-- The own post-sensor charge reaches its physical SLOW root well before
7.5; this is the root used in the actual constructed return flow. -/
theorem reopen_deadline : c.auxPhase.final.time + slowReopenDuration c.auxPhase.final 0 < s.time + 65 / 12 := by
  have hb : 17999 / 100000 ≤ c.auxPhase.final.x 0 .b ∧ c.auxPhase.final.x 0 .b ≤ 18001 / 100000 := by
    have h := (c.prepared 0).recovery
    change 17999 / 100000 ≤ c.returnPhase.final.x 0 .b ∧ c.returnPhase.final.x 0 .b ≤ 18001 / 100000 at h
    rwa [c.returnPhase.recovery] at h
  have h := (slowReopenDuration_bounds c.auxPhase.final 0 c.auxPhase.charge hb).2
  linarith [c.auxPhase.time_bounds.2]

end ProtectedInputCycle
end KernelR.Hybrid
