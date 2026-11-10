import KernelR.HybridParameterJumpDiamond
import KernelR.HybridWork

/-! Physical bounds for realized charge thresholds. A common upper
bound on all charges makes the state invariant independent of the mode.
The energy reserve follows from the original field and work terms. -/
namespace KernelR.Hybrid
open MeasureTheory Set

/-- The charge bounds needed by the comparison proof. The READY
contacts are below 1.1 and all protected contacts are nonnegative. -/
structure ParameterThresholdBounds {n} (θ : Fin n → Parameters) : Prop where
  fire : ∀ i, (θ i).thresholds.fire ≤ 11 / 10
  fastEnd : ∀ i, 0 ≤ (θ i).thresholds.fastEnd
  fastBelowFire : ∀ i, (θ i).thresholds.fastEnd < (θ i).thresholds.fire
  reopen : ∀ i, 0 ≤ (θ i).thresholds.reopen
  mark : ∀ i p, (θ i).thresholds.mark p ≤ 11 / 10
  silent : ∀ i p, 0 ≤ (θ i).thresholds.silent p
  error : ∀ i p, 0 ≤ (θ i).thresholds.error p
  auxReady : ∀ i p, 0 ≤ (θ i).thresholds.auxReady p

/-- Starting-state bounds for arbitrary networks in the parameterized
operational semantics. Continuous coordinates survive every jump. -/
structure ParameterPhysicalInvariant {n} (θ : Fin n → Parameters) (s : Snapshot n) : Prop where
  charge : ∀ i, s.x i .q ≤ 11 / 10
  sensor : ∀ i p, s.x i (.m p) ≤ 11 / 10
  gain : ∀ i p, s.x i (.z p) ≤ Real.log ((θ i).cap p)
  recovery : ∀ i, 0 ≤ s.x i .b ∧ s.x i .b ≤ 11 / 10
  reserve : ∀ i, 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100

noncomputable def ParameterFlow.at {n θ s u} (f : @ParameterFlow n θ s u) (t : ℝ) :
    Snapshot n := {s with time := t, x := f.path t}

private theorem ParameterFlow.coordinate_upper {n θ s u} (f : @ParameterFlow n θ s u)
    (i : Fin n) (c : Coord) {cap : ℝ} (initial : s.x i c ≤ cap)
    (barrier : ∀ t ∈ Icc s.time u.time, cap ≤ f.path t i c → field θ s (f.path t) t i c ≤ 0)
    {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    f.path t i c ≤ cap := by
  have sub : Icc s.time t ⊆ Icc s.time u.time := Icc_subset_Icc le_rfl ht.2
  apply integral_upper_barrier ht.1 ((f.continuous i c).mono sub)
    ((f.integrable i c).mono_set (by
      rw [uIcc_of_le ht.1,uIcc_of_le f.positive.le]; exact sub))
  · intro v hv
    simpa only [f.initial] using f.integral_eq v (sub hv) i c
  · simpa only [f.initial] using initial
  · intro v hv
    exact barrier v (sub hv)

theorem ParameterFlow.protected_aux_nonnegative {n θ s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (i : Fin n) (p : Port) (hm : s.aux i p ≠ .ready)
    {t : ℝ} (ht : t ∈ Icc s.time u.time) : 0 ≤ f.path t i (.m p) := by
  have h := continuous_bound_from_Ico (cap := 0) f.positive (f.continuous i (.m p)).neg
    (fun v hv => by
      have guard := (f.guards v hv).2 i p
      change -(f.path v i (.m p)) ≤ 0
      cases mode : s.aux i p with
      | ready => exact (hm mode).elim
      | mark => rw [mode] at guard; linarith [bounds.silent i p]
      | silent => rw [mode] at guard; linarith [bounds.error i p]
      | error => rw [mode] at guard; linarith [bounds.auxReady i p]) t ht
  exact neg_nonpos.mp h

private theorem ParameterFlow.protected_main_nonnegative {n θ s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (i : Fin n) (hm : s.main i ≠ .ready)
    {t : ℝ} (ht : t ∈ Icc s.time u.time) : 0 ≤ f.path t i .q := by
  have h := continuous_bound_from_Ico (cap := 0) f.positive (f.continuous i .q).neg
    (fun v hv => by
      have guard := (f.guards v hv).1 i
      change -(f.path v i .q) ≤ 0
      cases mode : s.main i with
      | ready => exact (hm mode).elim
      | fast => rw [mode] at guard; linarith [bounds.fastEnd i]
      | slow => rw [mode] at guard; linarith [bounds.reopen i]) t ht
  exact neg_nonpos.mp h

private theorem ParameterFlow.mark_nonnegative {n θ ε s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (box : PhysicalBox θ ε)
    (i : Fin n) (p : Port) {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    0 ≤ markAct θ s (f.path t) i p := by
  unfold markAct
  split_ifs with h
  · have hm := f.protected_aux_nonnegative bounds i p (by rw [h.1]; decide) ht
    exact mul_nonneg (mul_nonneg (by norm_num) (box.rates_positive i p).1.le) hm
  · exact le_rfl

theorem ParameterFlow.recovery_nondecreasing {n θ ε s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (box : PhysicalBox θ ε)
    (i : Fin n) {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    s.x i .b ≤ f.path t i .b := by
  have h := f.integral_eq t ht i .b
  have work : 0 ≤ ∫ v in s.time..t, ∑ p : Port, markAct θ s (f.path v) i p :=
    intervalIntegral.integral_nonneg ht.1 (fun v hv =>
      Finset.sum_nonneg (fun p _ => f.mark_nonnegative bounds box i p ⟨hv.1, hv.2.trans ht.2⟩))
  simp only [field] at h
  linarith

private theorem ParameterFlow.charge_bound {n θ ε s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (box : PhysicalBox θ ε)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) :
    ∀ t ∈ Icc s.time u.time, f.path t i .q ≤ 11 / 10 := by
  cases hm : s.main i with
  | ready =>
    apply continuous_bound_from_Ico f.positive (f.continuous i .q)
    intro t ht
    have h := (f.guards t ht).1 i
    rw [hm] at h
    exact h.le.trans (bounds.fire i)
  | fast =>
    intro t ht
    apply f.coordinate_upper i .q (hs.charge i) _ ht
    intro v _ hq
    simp only [field, hm]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [a_coarse_bounds.1]) (by linarith)
  | slow =>
    intro t ht
    apply f.coordinate_upper i .q (hs.charge i) _ ht
    intro v hv hq
    simp only [field, hm]
    have hb := (hs.recovery i).1.trans (f.recovery_nondecreasing bounds box i hv)
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (by linarith)

private theorem ParameterFlow.sensor_bound {n θ ε s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (box : PhysicalBox θ ε)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) (p : Port) :
    ∀ t ∈ Icc s.time u.time, f.path t i (.m p) ≤ 11 / 10 := by
  cases hm : s.aux i p with
  | ready =>
    apply continuous_bound_from_Ico f.positive (f.continuous i (.m p))
    intro t ht
    have h := (f.guards t ht).2 i p
    rw [hm] at h
    exact h.le.trans (bounds.mark i p)
  | mark | silent | error =>
    intro t ht
    apply f.coordinate_upper i (.m p) (hs.sensor i p) _ ht
    intro v _ hq
    rcases box.rates_positive i p with ⟨hmpos, hspos, hepos⟩
    simp only [field, hm, reduceCtorEq, ite_false, auxDrain]
    all_goals
      apply neg_nonpos.mpr (mul_nonneg _ (by linarith : 0 ≤ f.path v i (.m p)))
      first | exact hmpos.le | exact hspos.le | exact hepos.le

private theorem ParameterFlow.gain_bound {n θ s u} (f : @ParameterFlow n θ s u)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) (p : Port)
    {t : ℝ} (ht : t ∈ Icc s.time u.time) : f.path t i (.z p) ≤ Real.log ((θ i).cap p) := by
  apply f.coordinate_upper i (.z p) (hs.gain i p) _ ht
  intro v _ hv
  simp [field, errorAct, not_lt.mpr hv]

private theorem ParameterFlow.work_bound {n θ ε s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (box : PhysicalBox θ ε)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n)
    {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    0 ≤ work θ s (f.path t) i t ∧ work θ s (f.path t) i t ≤ 500 := by
  let x := f.path t
  have ha : 0 ≤ a := by linarith [a_coarse_bounds.1]
  have cur (p : Port) : 0 ≤ current s i p t ∧ current s i p t ≤ 7 / 5 :=
    ⟨(current_bounds s i p t).1, (current_bounds s i p t).2.trans a_coarse_bounds.2.le⟩
  have gain (p : Port) : Real.exp (x i (.z p)) ≤ 5 := by
    calc
      _ ≤ Real.exp (Real.log ((θ i).cap p)) :=
        Real.exp_le_exp.mpr (f.gain_bound hs i p ht)
      _ = _ := Real.exp_log (box.cap_positive i p)
      _ ≤ _ := (box.coarse_upper i p).1
  have drive₀ : 0 ≤ drive s x i t :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (Real.exp_pos _).le (cur p).1)
  have drive₁ : drive s x i t ≤ 21 := by
    have h := sum_three_le (fun p => mul_le_mul (gain p) (cur p).2 (cur p).1 (by norm_num : (0 : ℝ) ≤ 5))
    change drive s x i t ≤ _ at h
    linarith
  let mainWork := match s.main i with
    | .ready => drive s x i t
    | .fast => a * x i .q
    | .slow => 11 / 10
  have main : 0 ≤ mainWork ∧ mainWork ≤ 21 := by
    dsimp only [mainWork]
    cases hm : s.main i with
    | ready => exact ⟨drive₀, drive₁⟩
    | fast =>
      have hq := f.protected_main_nonnegative bounds i (by rw [hm]; decide) ht
      have h := mul_le_mul a_coarse_bounds.2.le (f.charge_bound bounds box hs i t ht)
        hq (by norm_num : (0 : ℝ) ≤ 7 / 5)
      exact ⟨mul_nonneg ha hq, h.trans (by norm_num)⟩
    | slow => norm_num
  let portWork := fun p =>
    (if s.aux i p = .ready then (θ i).inputGain p * current s i p t
      else auxDrain (θ i) (s.aux i p) p (x i (.m p))) +
        errorAct θ s x i p + markAct θ s x i p
  have port (p : Port) : 0 ≤ portWork p ∧ portWork p ≤ 110 := by
    have hm := f.sensor_bound bounds box hs i p t ht
    rcases box.rates_positive i p with ⟨hmp,hsp,hep⟩
    rcases box.coarse_upper i p with ⟨_,hmu,hsu,heu,hiu⟩
    cases hmode : s.aux i p with
    | ready =>
      simp only [portWork, hmode, ite_true, errorAct, markAct, reduceCtorEq,
        false_and, ite_false, add_zero]
      exact ⟨mul_nonneg (box.input_gain_positive i p).le (cur p).1,
        (mul_le_mul hiu (cur p).2 (cur p).1 (by norm_num : (0 : ℝ) ≤ 60)).trans (by norm_num)⟩
    | mark =>
      have pos := f.protected_aux_nonnegative bounds i p (by rw [hmode]; decide) ht
      have h := mul_le_mul hmu hm pos (by norm_num : (0 : ℝ) ≤ 14)
      have zero := mul_nonneg hmp.le pos
      simp only [portWork, hmode, reduceCtorEq, ite_false, auxDrain, errorAct,
        false_and, add_zero, markAct, true_and]
      split_ifs <;> constructor <;> nlinarith
    | silent =>
      have pos := f.protected_aux_nonnegative bounds i p (by rw [hmode]; decide) ht
      have h := mul_le_mul hsu hm pos (by norm_num : (0 : ℝ) ≤ 3)
      simp only [portWork, hmode, reduceCtorEq, ite_false, auxDrain, errorAct,
        false_and, add_zero, markAct]
      exact ⟨mul_nonneg hsp.le pos, h.trans (by norm_num)⟩
    | error =>
      have pos := f.protected_aux_nonnegative bounds i p (by rw [hmode]; decide) ht
      have h := mul_le_mul heu hm pos (by norm_num : (0 : ℝ) ≤ 11)
      have zero := mul_nonneg hep.le pos
      simp only [portWork, hmode, reduceCtorEq, ite_false, auxDrain, markAct,
        false_and, add_zero, errorAct, true_and]
      split_ifs <;> constructor <;> nlinarith
  have eq : work θ s x i t = mainWork + ∑ p : Port, portWork p := by
    simp only [work, portWork, mainWork, Finset.sum_add_distrib]
    ac_rfl
  rw [eq]
  exact ⟨add_nonneg main.1 (Finset.sum_nonneg fun p _ => (port p).1),
    (add_le_add main.2 (sum_three_le fun p => (port p).2)).trans (by norm_num)⟩

theorem ParameterFlow.reserve_on {n θ ε s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (box : PhysicalBox θ ε)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n)
    {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    50 ≤ f.path t i .energy ∧ f.path t i .energy ≤ 100 := by
  have hi := f.coordinate_upper i .energy (hs.reserve i).2
    (fun v hv h => by dsimp [field]; linarith [(f.work_bound bounds box hs i hv).1]) ht
  have sub : Icc s.time t ⊆ Icc s.time u.time := Icc_subset_Icc le_rfl ht.2
  have integ := (f.integrable i .energy).mono_set (by
    rw [uIcc_of_le ht.1,uIcc_of_le f.positive.le]; exact sub)
  have lo := integral_upper_barrier (cap := -50) ht.1
    (((f.continuous i .energy).mono sub).neg) integ.neg
    (by
      intro v hv
      have eq := f.integral_eq v (sub hv) i .energy
      simp only [Pi.neg_apply, intervalIntegral.integral_neg, f.initial]
      linarith)
    (by simpa only [Pi.neg_apply, f.initial] using neg_le_neg (hs.reserve i).1)
    (fun v hv h => by
      simp only [Pi.neg_apply, field] at h ⊢
      linarith [(f.work_bound bounds box hs i (sub hv)).2])
  exact ⟨by simpa only [Pi.neg_apply, neg_le_neg_iff] using lo, hi⟩

theorem ParameterFlow.invariant_at {n θ ε s u} (f : @ParameterFlow n θ s u)
    (bounds : ParameterThresholdBounds θ) (box : PhysicalBox θ ε)
    (hs : ParameterPhysicalInvariant θ s) {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    ParameterPhysicalInvariant θ (f.at t) := by
  refine ⟨fun i => f.charge_bound bounds box hs i t ht,
    fun i p => f.sensor_bound bounds box hs i p t ht,
    fun i p => f.gain_bound hs i p ht, ?_,
    fun i => f.reserve_on bounds box hs i ht⟩
  intro i
  refine ⟨(hs.recovery i).1.trans (f.recovery_nondecreasing bounds box i ht), ?_⟩
  apply f.coordinate_upper i .b (hs.recovery i).2 _ ht
  intro v _ hv
  simp [field, markAct, not_lt.mpr hv]

theorem ParameterFlow.at_final {n θ s u} (f : @ParameterFlow n θ s u) : f.at u.time = u := by
  cases s; cases u
  dsimp only [ParameterFlow.at]
  congr 1
  · exact f.final
  · exact f.main_fixed.symm
  · exact f.aux_fixed.symm
  · exact f.raw_fixed.symm
  · exact f.queue_fixed.symm

theorem ParameterJump.physical_invariant {n θ route s u} (j : @ParameterJump n θ route s u)
    (hs : ParameterPhysicalInvariant θ s) : ParameterPhysicalInvariant θ u := by
  rcases hs with ⟨hq, hm, hz, hb, he⟩
  exact ⟨by simpa only [j.physical_continuous] using hq,
    by simpa only [j.physical_continuous] using hm, by simpa only [j.physical_continuous] using hz,
    by simpa only [j.physical_continuous] using hb, by simpa only [j.physical_continuous] using he⟩

end KernelR.Hybrid
