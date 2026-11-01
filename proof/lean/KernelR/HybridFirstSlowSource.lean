import KernelR.HybridProtectedMainFlowExistence
import KernelR.HybridFirstFireSchedule
import KernelR.HybridBirthFirstFire

namespace KernelR.Hybrid
open Set

noncomputable def firstSlowSourceFinal (θ : Fin 1 → Parameters) (s : Snapshot 1) : Snapshot 1 :=
  { (setRaw (protectedMainEnd θ s 0 0 .slow .ready none 32) 0 0 (some 32)) with
    pending := sourceTrain 0 0 40 8 11 ++ sourceTrain 0 0 160 8 16 }

structure FirstSlowSource (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) where
  execution : Execution θ route s (firstSlowSourceFinal θ s)
  main_slow : (firstSlowSourceFinal θ s).main 0 = .slow
  aux_ready : ∀ j p, (firstSlowSourceFinal θ s).aux j p = .ready
  gain_preserved : ∀ p, (firstSlowSourceFinal θ s).x 0 (.z p) = s.x 0 (.z p)
  recovery_preserved : (firstSlowSourceFinal θ s).x 0 .b = s.x 0 .b
  charge : 7 / 50 < (firstSlowSourceFinal θ s).x 0 .q ∧ (firstSlowSourceFinal θ s).x 0 .q < 4 / 25
  trained_rest : (firstSlowSourceFinal θ s).x 0 (.m 0) = 1 / 40
  raw_active : (firstSlowSourceFinal θ s).raw 0 0 = some 32
  raw_other : ∀ p, p ≠ 0 → (firstSlowSourceFinal θ s).raw 0 p = none
  rest : ∀ p, RestBand ((firstSlowSourceFinal θ s).x 0 (.m p))
  deliveries : execution.deliveries = [⟨0,0,32⟩]
  emissions : execution.ledger.emissions = []
  physical : PhysicalInvariant θ (firstSlowSourceFinal θ s)
  raw_valid : RawValid (firstSlowSourceFinal θ s)

/-- The real first SLOW suffix reaches and consumes source32 while still
strictly above its return guard; no READY state is substituted. -/
theorem first_slow_source_exists {θ ε route} (hbox : PhysicalBox θ ε) (s : Snapshot 1) (fireTime : ℝ)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (htime : s.time = fireTime + 1)
    (hfire : 24 + 2 / 5 < fireTime ∧ fireTime < 24 + 9 / 10)
    (hm : s.main 0 = .slow) (hq : s.x 0 .q = 1 / 4)
    (hrecovery : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000)
    (ha : ∀ j p, s.aux j p = .ready) (hr : ∀ j p, s.raw j p = none)
    (hsensor : s.x 0 (.m 0) = 1 / 40) (hrest : ∀ p, RestBand (s.x 0 (.m p)))
    (hqueue : s.pending = sourceTrain 0 0 32 8 12 ++ sourceTrain 0 0 160 8 16) :
    Nonempty (FirstSlowSource θ route s) := by
  have hT : s.time < (32 : ℝ) := by rw [htime]; linarith [hfire.2]
  have hqguard := birth_first_strong_slow_guards_to32 hrecovery hfire
  have hfuture : ∀ d ∈ s.pending, (32 : ℝ) ≤ d.due := by
    intro d hd; rw [hqueue] at hd
    exact a_source_tail_future 32 32 12 (by norm_num) (by norm_num) d hd
  let flow : Flow θ s (protectedMainEnd θ s 0 0 .slow .ready none 32) :=
    protectedMainFlow s 0 0 .slow .ready none hT (Or.inr rfl) (Or.inl rfl) hm
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (ha 0 0)
      (fun j p _ => ha j p) (hr 0 0) (fun j p _ => hr j p) (by intros; contradiction)
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
      (by intro j p _; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hrest p).2])
      (by
        intro t ht
        simpa [protectedMainRate,hq,htime] using (hqguard t ⟨by linarith [ht.1],ht.2.le⟩).1)
      (by
        intro t ht
        simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
        exact relax_lt (by norm_num) ht.1 (by rw [hsensor]; norm_num) (by norm_num)) hfuture
  let v := protectedMainEnd θ s 0 0 .slow .ready none 32
  have hhead : v.pending = [] ++ (⟨0,0,32⟩ : Delivery 1) ::
      (sourceTrain 0 0 40 8 11 ++ sourceTrain 0 0 160 8 16) := by
    change s.pending = _
    rw [hqueue,sourceTrain_succ]
    norm_num
  let e : Execution θ route s (firstSlowSourceFinal θ s) :=
    .cons (.flow flow) (.cons (.jump (.arrive v ⟨0,0,32⟩ [] _ hhead rfl (hr 0 0))) (.nil _))
  refine ⟨{
    execution := e
    main_slow := hm
    aux_ready := ha
    gain_preserved := fun _ => rfl
    recovery_preserved := rfl
    charge := ?_
    trained_rest := ?_
    raw_active := by simp [firstSlowSourceFinal,setRaw]
    raw_other := by intro p hp; simp [firstSlowSourceFinal,setRaw,protectedMainEnd,hp,hr]
    rest := ?_
    deliveries := rfl
    emissions := rfl
    physical := e.physical_invariant hbox hf
    raw_valid := e.raw_valid hv
  }⟩
  · simpa [firstSlowSourceFinal,setRaw,protectedMainEnd,protectedMainValues,protectedMainRate,hq,htime] using
      birth_first_strong_slow_at32_bounds hrecovery hfire
  · simp [firstSlowSourceFinal,setRaw,protectedMainEnd,protectedMainValues,rawInputScale,
      auxPulse_zero_eq_relax,relax,hsensor]
  · intro p
    have hi := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hrest p)
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    by_cases hp : p = 0
    · subst p
      simpa [firstSlowSourceFinal,setRaw,protectedMainEnd,protectedMainValues,rawInputScale,
        auxPulse_zero_eq_relax,RestBand] using hi
    · simpa [firstSlowSourceFinal,setRaw,protectedMainEnd,protectedMainValues,hp,RestBand] using hi


noncomputable def FirstSlowSource.final {θ route s} (_c : FirstSlowSource θ route s) : Snapshot 1 :=
  firstSlowSourceFinal θ s

theorem FirstSlowSource.date {θ route s} (c : FirstSlowSource θ route s) : c.final.time = 32 := rfl

theorem FirstSlowSource.pending {θ route s} (c : FirstSlowSource θ route s) :
    c.final.pending = sourceTrain 0 0 40 8 11 ++ sourceTrain 0 0 160 8 16 := rfl

theorem FirstSlowSource.complete {θ route s} (c : FirstSlowSource θ route s) :
    CompleteThrough c.execution 32 := by
  have hguard : BeforeGuards c.final c.final.x := by
    constructor
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hm : c.final.main 0 = .slow := c.main_slow
      have hq : 7 / 50 < c.final.x 0 .q := c.charge.1
      rw [hm]; linarith
    · intro j p
      have ha : c.final.aux j p = .ready := c.aux_ready j p
      rw [ha]
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hu : c.final.x 0 (.m p) ≤ 1 / 40 + 1 / 100000 := (c.rest p).2
      linarith
  have hfuture : ∀ d ∈ c.final.pending, (32 : ℝ) < d.due := by
    intro d hd
    rw [c.pending] at hd
    have hl := a_source_tail_future 40 40 11 (by norm_num) (by norm_num) d hd
    linarith
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply hguard.no_jump
  · intro j p origin hraw
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    by_cases hp : p = 0
    · subst p
      have he : origin = (32 : ℝ) := Option.some.inj (hraw.symm.trans c.raw_active)
      rw [he,c.date]; norm_num
    · have hr : c.final.raw 0 p = none := c.raw_other p hp
      rw [hr] at hraw
      contradiction
  · intro d hd
    rw [c.date]
    exact hfuture d hd

end KernelR.Hybrid
