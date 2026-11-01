import KernelR.HybridSlowReopenExistence
/-! Prepared recovery gives an actual SLOW return and quiet section before the next eight-gap source. -/
namespace KernelR.Hybrid
open Set

theorem preparedSlowDuration_bounds {n} (s : Snapshot n) (i : Fin n) (hq : s.x i .q = 1 / 4)
    (hb : 17999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 18001 / 100000) :
    0 < slowReopenDuration s i ∧ slowReopenDuration s i < 28 / 5 := by
  have hbpos : 0 < s.x i .b := by linarith [hb.1]
  have hform : slowReopenDuration s i = Real.log (5 / 2 : ℝ) / s.x i .b := by
    norm_num [slowReopenDuration,hq]
  rw [hform]
  constructor
  · exact div_pos (Real.log_pos (by norm_num)) hbpos
  · apply (div_lt_iff₀ hbpos).mpr
    linarith [KernelR.log_recovery_bounds.2,hb.1]

structure PreparedSlowReturn (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) (source : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  date : final.time = source + 15 / 2
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
  complete : CompleteThrough execution (source + 15 / 2)

/-- A current prepared SLOW state reaches its logarithmic return root, takes
its actual reopen jump, then waits until 7.5 after the source. No execution,
READY substitution or return date is supplied to the construction. -/
theorem prepared_slow_return_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1)
    (source latency : ℝ) (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : s.x 0 .q = 1 / 4)
    (hbown : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (ha : ∀ p, s.aux 0 p = .ready ∧ RestBand (s.x 0 (.m p)))
    (hr : ∀ j p, s.raw j p = none)
    (htime : s.time = source + latency + 1) (hlat : 0 < latency ∧ latency < 9 / 10)
    (hp : ∀ d ∈ s.pending, source + 8 ≤ d.due) : Nonempty (PreparedSlowReturn θ route s source) := by
  have hD := preparedSlowDuration_bounds s 0 hq hbown
  have hbpos : 0 < s.x 0 .b := by linarith [hbown.1]
  have hqpos : 1 / 10 < s.x 0 .q := by rw [hq]; norm_num
  let T := s.time + slowReopenDuration s 0
  let horizon := source + 15 / 2
  have hT : s.time < T := by dsimp [T]; linarith [hD.1]
  have hwait : T < horizon := by dsimp [T,horizon]; rw [htime]; linarith [hD.2,hlat.2]
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
  }⟩
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact ⟨(hfinalReady 0).ready,(hfinalReady 0).charge,hbown,(hfinalReady 0).auxiliary⟩

end KernelR.Hybrid
