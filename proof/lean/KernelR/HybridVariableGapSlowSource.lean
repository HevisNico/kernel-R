import KernelR.HybridMidLearnedFastEnd
import KernelR.HybridGuardNoJump

/-! A genuinely queued next input reaches the continuing low-recovery SLOW
trajectory at a variable gap. No READY state or nominal charge is substituted. -/
namespace KernelR.Hybrid
open Set

/-- The physical SLOW clock at a gap in [7.9,8.1], with the actual firing
latency and the own low recovery. -/
theorem variable_gap_first_slow_charge {B S latency T : ℝ}
    (hb : 7999 / 100000 ≤ B ∧ B ≤ 8001 / 100000)
    (hlat : 2 / 5 < latency ∧ latency < 9 / 10)
    (hgap : S + 79 / 10 ≤ T ∧ T ≤ S + 81 / 10) :
    7 / 50 < (1 / 4 : ℝ) * Real.exp (-B * (T - (S + latency + 1))) ∧
      (1 / 4 : ℝ) * Real.exp (-B * (T - (S + latency + 1))) < 4 / 25 := by
  have hd : 6 < T - (S + latency + 1) ∧ T - (S + latency + 1) < 67 / 10 := by
    constructor <;> linarith [hlat.1,hlat.2,hgap.1,hgap.2]
  have hlo := mul_le_mul hb.1 hd.1.le (by norm_num : (0 : ℝ) ≤ 6)
    (show 0 ≤ B by linarith [hb.1])
  have hhi := mul_le_mul hb.2 hd.2.le (show 0 ≤ T - (S + latency + 1) by linarith [hd.1])
    (by norm_num : (0 : ℝ) ≤ 8001 / 100000)
  have hIlo : (47 / 100 : ℝ) ≤ B * (T - (S + latency + 1)) := by nlinarith
  have hIhi : B * (T - (S + latency + 1)) ≤ (27 / 50 : ℝ) := by nlinarith
  have heLo : (14 / 25 : ℝ) < Real.exp (-(27 / 50 : ℝ)) := by
    have h := Real.exp_bound (x := -(27 / 50 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have heHi : Real.exp (-(47 / 100 : ℝ)) < 16 / 25 := by
    have h := Real.exp_bound (x := -(47 / 100 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hExpLo := Real.exp_le_exp.mpr (show -(27 / 50 : ℝ) ≤ -B * (T - (S + latency + 1)) by nlinarith)
  have hExpHi := Real.exp_le_exp.mpr (show -B * (T - (S + latency + 1)) ≤ -(47 / 100 : ℝ) by nlinarith)
  constructor <;> linarith

theorem variable_gap_first_slow_guards {B S latency T : ℝ}
    (hb : 7999 / 100000 ≤ B ∧ B ≤ 8001 / 100000)
    (hlat : 2 / 5 < latency ∧ latency < 9 / 10)
    (hgap : S + 79 / 10 ≤ T ∧ T ≤ S + 81 / 10) :
    ∀ t ∈ Icc (S + latency + 1) T,
      1 / 10 < (1 / 4 : ℝ) * Real.exp (-B * (t - (S + latency + 1))) ∧
        (1 / 4 : ℝ) * Real.exp (-B * (t - (S + latency + 1))) ≤ 1 / 4 := by
  intro t ht
  have hend := variable_gap_first_slow_charge hb hlat hgap
  have hbpos : 0 ≤ B := by linarith [hb.1]
  have hlo := Real.exp_le_exp.mpr (show -B * (T - (S + latency + 1)) ≤
    -B * (t - (S + latency + 1)) by nlinarith [ht.2])
  have hhi := Real.exp_le_one_iff.mpr (show -B * (t - (S + latency + 1)) ≤ 0 by nlinarith [ht.1])
  constructor <;> linarith [hend.1]

structure VariableGapSlowSource {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    {f : FirstLearnedFire θ (fun _ _ => []) s 0 p} (fast : MidLearnedFastEnd f)
    (T : ℝ) (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) fast.final final
  date : final.time = T
  main_slow : final.main 0 = .slow
  auxiliary : ∀ j q, final.aux j q = .ready
  charge : 7 / 50 < final.x 0 .q ∧ final.x 0 .q < 4 / 25
  charge_clock : final.x 0 .q = (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (T - (s.time + f.latency + 1)))
  trained_rest : final.x 0 (.m p) = 1 / 40
  rest : ∀ q, RestBand (final.x 0 (.m q))
  raw_active : final.raw 0 p = some T
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = later
  gains : ∀ j q, final.x j (.z q) = fast.final.x j (.z q)
  recovery : ∀ j, final.x j .b = fast.final.x j .b
  deliveries : execution.deliveries = [⟨0,p,T⟩]
  emissions : execution.ledger.emissions = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution T

/-- From an actual learned FIRE and its actual FAST completion, continue the
SLOW trajectory to the exact next queued input and consume that occurrence. -/
theorem FirstLearnedFire.variable_gap_slow_source_exists {θ ε} {s : Snapshot 1} {p : Port}
    (f : FirstLearnedFire θ (fun _ _ => []) s 0 p) (hb : PhysicalBox θ ε)
    (fast : MidLearnedFastEnd f) (hs : ReadyCoordinates s 0)
    (hg : Real.exp (s.x 0 (.z p)) ≤ 11 / 5)
    (hB : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000)
    (T : ℝ) (later : List (Delivery 1))
    (hgap : s.time + 79 / 10 ≤ T ∧ T ≤ s.time + 81 / 10)
    (hqueue : fast.final.pending = ⟨0,p,T⟩ :: later)
    (hfuture : ∀ d ∈ later, T + 31 / 4 ≤ d.due) :
    Nonempty (VariableGapSlowSource fast T later) := by
  have hlat : 2 / 5 < f.latency ∧ f.latency < 9 / 10 := by
    have h := readyPulse_mid_root_after_four_tenths hs.charge.2 hg
      (by linarith [f.early] : s.time ≤ s.time + f.latency) f.response_root
    exact ⟨by linarith,f.deadline⟩
  have hbfast : fast.final.x 0 .b = s.x 0 .b := by
    rw [fast.recovery,f.recovery_preserved]
  have hclock : fast.final.time = s.time + f.latency + 1 := by rw [fast.date,f.date]
  have hT : fast.final.time < T := by rw [hclock]; linarith [hlat.2,hgap.1]
  have hguards := variable_gap_first_slow_guards hB hlat hgap
  have hpending : ∀ d ∈ fast.final.pending, T ≤ d.due := by
    intro d hd
    rw [hqueue] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_rfl
    · linarith [hfuture d hd]
  let flow : Flow θ fast.final (protectedMainEnd θ fast.final 0 p .slow .ready none T) :=
    protectedMainFlow fast.final 0 p .slow .ready none hT (Or.inr rfl) (Or.inl rfl)
      fast.main_slow (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (fast.auxiliary 0 p)
      (fun j q _ => fast.auxiliary j q) (fast.raw_none 0 p) (fun j q _ => fast.raw_none j q)
      (by intros; contradiction) (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
      (by intro j q _; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(fast.rest q).2])
      (by intro t ht
          simpa [protectedMainRate,fast.charge,hbfast,hclock] using
            (hguards t ⟨by linarith [ht.1],ht.2.le⟩).1)
      (by intro t ht
          simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (by rw [fast.sensor_charge]; norm_num) (by norm_num)) hpending
  let before := protectedMainEnd θ fast.final 0 p .slow .ready none T
  let final := { (setRaw before 0 p (some T)) with pending := later }
  let jump : Jump (fun _ _ => []) before final :=
    .arrive before ⟨0,p,T⟩ [] later hqueue rfl (fast.raw_none 0 p)
  let e : Execution θ (fun _ _ => []) fast.final final :=
    .cons (.flow flow) (.cons (.jump jump) (.nil _))
  have hcharge : 7 / 50 < final.x 0 .q ∧ final.x 0 .q < 4 / 25 := by
    simpa [final,setRaw,before,protectedMainEnd,protectedMainValues,protectedMainRate,fast.charge,hbfast,hclock]
      using variable_gap_first_slow_charge hB hlat hgap
  have haux : ∀ j q, final.aux j q = .ready := fast.auxiliary
  have hrawOther : ∀ q, q ≠ p → final.raw 0 q = none := by
    intro q hq
    simp [final,setRaw,before,protectedMainEnd,hq,fast.raw_none]
  have hrest : ∀ q, RestBand (final.x 0 (.m q)) := by
    intro q
    have hband := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (fast.rest q)
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    by_cases hq : q = p
    · subst q
      simpa [final,setRaw,before,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hband
    · simpa [final,setRaw,before,protectedMainEnd,protectedMainValues,hq,RestBand] using hband
  have hcomplete : CompleteThrough e T := by
    refine ⟨rfl,?_,?_⟩
    · intro u
      apply BeforeGuards.no_jump
      · constructor
        · intro j
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          have hm : final.main 0 = .slow := fast.main_slow
          rw [hm]
          change 1 / 10 < final.x 0 .q
          linarith [hcharge.1]
        · intro j q
          rw [haux]
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          linarith [(hrest q).2]
      · intro j q origin hraw
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        by_cases hq : q = p
        · subst q
          have hr : final.raw 0 p = some T := by simp [final,setRaw]
          have he : origin = T := Option.some.inj (hraw.symm.trans hr)
          change T < origin + 1
          rw [he]; norm_num
        · rw [hrawOther q hq] at hraw; contradiction
      · intro d hd
        change d ∈ later at hd
        change T < d.due
        linarith [hfuture d hd]
    · intro d hd
      change d ∈ later at hd
      linarith [hfuture d hd]
  refine ⟨{
    final := final
    execution := e
    date := rfl
    main_slow := fast.main_slow
    auxiliary := haux
    charge := hcharge
    charge_clock := by simp [final,setRaw,before,protectedMainEnd,protectedMainValues,protectedMainRate,fast.charge,hbfast,hclock]
    trained_rest := ?_
    rest := hrest
    raw_active := by simp [final,setRaw]
    raw_other := hrawOther
    pending := rfl
    gains := fun _ _ => rfl
    recovery := fun _ => rfl
    deliveries := rfl
    emissions := rfl
    physical := e.physical_invariant hb fast.physical
    raw_valid := e.raw_valid fast.raw_valid
    complete := hcomplete
  }⟩
  simp [final,setRaw,before,protectedMainEnd,protectedMainValues,rawInputScale,
    auxPulse_zero_eq_relax,relax,fast.sensor_charge]

end KernelR.Hybrid
