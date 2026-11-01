import KernelR.HybridProtectedMainFlowExistence
import KernelR.HybridQuietSourceArrival
/-! A raw-free SLOW state reaches its own physical return root and reopens. -/
namespace KernelR.Hybrid
open Set

noncomputable def slowReopenDuration {n} (s : Snapshot n) (i : Fin n) : ℝ :=
  Real.log (s.x i .q / (1 / 10)) / s.x i .b

theorem slowReopenDuration_bounds {n} (s : Snapshot n) (i : Fin n)
    (hq : 1 / 10 < s.x i .q ∧ s.x i .q ≤ 4 / 25)
    (hb : 17999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 18001 / 100000) :
    0 < slowReopenDuration s i ∧ slowReopenDuration s i < 4 := by
  have hbpos : 0 < s.x i .b := by linarith [hb.1]
  have hratio : 1 < s.x i .q / (1 / 10) := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 10)).mpr (by linarith [hq.1])
  have hratioUpper : s.x i .q / (1 / 10) ≤ (8 / 5 : ℝ) :=
    (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 10)).mpr (by linarith [hq.2])
  have hlog : Real.log (s.x i .q / (1 / 10)) ≤ 3 / 5 := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < s.x i .q / (1 / 10))]
  constructor
  · exact div_pos (Real.log_pos hratio) hbpos
  · exact (div_lt_iff₀ hbpos).mpr (by linarith [hb.1])

theorem slowReopen_root {n} (s : Snapshot n) (i : Fin n)
    (hq : 1 / 10 < s.x i .q) (hb : 0 < s.x i .b) :
    s.x i .q * Real.exp (-s.x i .b * slowReopenDuration s i) = 1 / 10 := by
  have hratio : 0 < s.x i .q / (1 / 10) := div_pos (by linarith) (by norm_num)
  have he : -s.x i .b * slowReopenDuration s i = -Real.log (s.x i .q / (1 / 10)) := by
    dsimp [slowReopenDuration]
    field_simp [ne_of_gt hb]
  rw [he,Real.exp_neg,Real.exp_log hratio]
  field_simp

theorem slowReopen_preguard {n} (s : Snapshot n) (i : Fin n)
    (hq : 1 / 10 < s.x i .q) (hb : 0 < s.x i .b) {t : ℝ}
    (ht : t < s.time + slowReopenDuration s i) :
    1 / 10 < s.x i .q * Real.exp (-s.x i .b * (t - s.time)) := by
  rw [← slowReopen_root s i hq hb]
  apply mul_lt_mul_of_pos_left ?_ (by linarith)
  apply Real.exp_lt_exp.mpr
  nlinarith

structure SlowReopen (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) where
  final : Snapshot 1
  execution : Execution θ route s final
  date : final.time = s.time + slowReopenDuration s 0
  deadline : final.time < 38
  ready : ∀ j, ReadyCoordinates final j
  raw_none : ∀ j p, final.raw j p = none
  charge : final.x 0 .q = 1 / 10
  recovery : ∀ j, final.x j .b = s.x j .b
  gains : ∀ j p, final.x j (.z p) = s.x j (.z p)
  pending : final.pending = s.pending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- An actual SLOW flow, followed by its guarded reopen jump, is built from
the current section. The return date is the cell's own logarithmic root. -/
theorem slow_reopen_exists {θ ε route} (hb : @PhysicalBox 1 θ ε) (s : Snapshot 1)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 1 / 10 < s.x 0 .q ∧ s.x 0 .q ≤ 4 / 25)
    (hbown : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (ha : ∀ p, s.aux 0 p = .ready ∧ RestBand (s.x 0 (.m p)))
    (hr : ∀ j p, s.raw j p = none) (ht : s.time < 34)
    (hp : ∀ d ∈ s.pending, (40 : ℝ) ≤ d.due) : Nonempty (SlowReopen θ route s) := by
  have hD := slowReopenDuration_bounds s 0 hq hbown
  have hbpos : 0 < s.x 0 .b := by linarith [hbown.1]
  let T := s.time + slowReopenDuration s 0
  have hT : s.time < T := by dsimp [T]; linarith [hD.1]
  have hTupper : T < (38 : ℝ) := by dsimp [T]; linarith [hD.2]
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
  let flow : Flow θ s (protectedMainEnd θ s 0 0 .slow .ready none T) :=
    protectedMainFlow s 0 0 .slow .ready none hT (Or.inr rfl) (Or.inl rfl) hm hmo (ha 0).1 hao
      (hr 0 0) (fun j p _ => hr j p) (by intros; contradiction) hqOther hmOther
      (by intro t ht; simpa [protectedMainRate] using slowReopen_preguard s 0 hq.1 hbpos ht.2)
      (by intro t ht; simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax];
          exact relax_lt (by norm_num) ht.1 (by linarith [(ha 0).2.2]) (by norm_num))
      (fun d hd => by linarith [hp d hd])
  let before := protectedMainEnd θ s 0 0 .slow .ready none T
  have hthreshold : before.x 0 .q = 1 / 10 := by
    simpa [before,protectedMainEnd,protectedMainValues,protectedMainRate,T] using slowReopen_root s 0 hq.1 hbpos
  let final := setMain before 0 .ready
  let e : Execution θ route s final := .cons (.flow flow) (.cons (.jump (.reopen before 0 hm hthreshold)) (.nil _))
  have haux : ∀ j p, final.aux j p = .ready ∧ RestBand (final.x j (.m p)) := by
    intro j p
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    constructor
    · exact (ha p).1
    · have hband := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (ha p).2
        (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
      by_cases hp : p = 0
      · subst p
        simpa [final,setMain,before,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hband
      · simpa [final,setMain,before,protectedMainEnd,protectedMainValues,hp,RestBand] using hband
  refine ⟨{
    final := final
    execution := e
    date := rfl
    deadline := hTupper
    ready := ?_
    raw_none := hr
    charge := hthreshold
    recovery := fun _ => rfl
    gains := fun _ _ => rfl
    pending := rfl
    emissions := rfl
    deliveries := rfl
    physical := e.physical_invariant hb hf
    raw_valid := e.raw_valid hv
  }⟩
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  refine ⟨by simp [final,setMain],?_,haux 0⟩
  change 1 / 10 - 1 / 100000 ≤ before.x 0 .q ∧ before.x 0 .q ≤ 7 / 50
  rw [hthreshold]
  constructor <;> norm_num

theorem SlowReopen.complete {θ route s} (c : SlowReopen θ route s)
    (hp : ∀ d ∈ s.pending, (40 : ℝ) ≤ d.due) : CompleteThrough c.execution c.final.time := by
  have hfuture : ∀ d ∈ c.final.pending, c.final.time < d.due := by
    intro d hd
    rw [c.pending] at hd
    linarith [c.deadline,hp d hd]
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro j
      have h := c.ready j
      rw [h.ready]
      linarith [h.charge.2]
    · intro j p
      have h := (c.ready j).auxiliary p
      rw [h.1]
      linarith [h.2.2]
  · intro j p origin hr
    rw [c.raw_none j p] at hr
    contradiction
  · exact hfuture

end KernelR.Hybrid
