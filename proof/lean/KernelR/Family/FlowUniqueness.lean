import KernelR.Family.Model
import KernelR.HybridInvariants
import KernelR.HybridSnapshotObservational

/-! Uniqueness of the parametric cell's actual integral flows.

Only sign assumptions on the relevant coefficients and rates are used. The
actual flow hypotheses state positive energy and nonnegative recovery and
auxiliary charges; no uniqueness, solution formula or protocol calendar is
assumed. Cap gates remain discontinuous and are handled by the existing,
model-independent integral comparison lemma.
-/
namespace KernelR.Family
open KernelR.Hybrid MeasureTheory Set

/-- The gain cap is a structural integral barrier. No coefficient signs,
fabrication box, energy lower bound or protocol assumptions are required. -/
theorem Flow.gain_cap {n C θ s u} (f : @Flow n C θ s u)
    (i : Fin n) (p : Port) (hinit : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) ≤ Real.log ((θ i).cap p) := by
  have h := KernelR.Hybrid.integral_cap_barrier f.positive.le
    (f.continuous i (.z p)) (f.integrable i (.z p))
    (by simpa only [f.initial] using fun t ht => f.integral_eq t ht i (.z p))
    (by simpa only [f.initial] using hinit)
    (fun t ht hcap => by simp [field, errorAct, not_lt.mpr hcap])
  simpa only [f.final] using h

/-- The shared recovery cap has the same structural barrier property. -/
theorem Flow.recovery_cap {n C θ s u} (f : @Flow n C θ s u)
    (i : Fin n) (hinit : s.x i .b ≤ C.recoveryCap) :
    u.x i .b ≤ C.recoveryCap := by
  have h := KernelR.Hybrid.integral_cap_barrier f.positive.le
    (f.continuous i .b) (f.integrable i .b)
    (by simpa only [f.initial] using fun t ht => f.integral_eq t ht i .b)
    (by simpa only [f.initial] using hinit)
    (fun t ht hcap => by simp [field, markAct, not_lt.mpr hcap])
  simpa only [f.final] using h

/-- Physical jumps preserve coordinates, so the gain barrier extends to traces. -/
theorem Execution.gain_cap {n C θ route s u} (e : @Execution n C θ route s u)
    (i : Fin n) (p : Port) (hinit : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) ≤ Real.log ((θ i).cap p) := by
  induction e with
  | nil => exact hinit
  | cons move rest ih =>
    apply ih
    cases move with
    | flow f => exact f.gain_cap i p hinit
    | jump j => simpa only [j.physical_continuous] using hinit

theorem Execution.recovery_cap {n C θ route s u} (e : @Execution n C θ route s u)
    (i : Fin n) (hinit : s.x i .b ≤ C.recoveryCap) : u.x i .b ≤ C.recoveryCap := by
  induction e with
  | nil => exact hinit
  | cons move rest ih =>
    apply ih
    cases move with
    | flow f => exact f.recovery_cap i hinit
    | jump j => simpa only [j.physical_continuous] using hinit

/-- The coefficient signs used by flow uniqueness. Threshold levels and pulse
width do not occur here. Zero coefficients and zero fabrication rates are
permitted by this structural theorem. -/
structure FlowSigns (C : Constants) : Prop where
  a_nonneg : 0 ≤ C.a
  kappa_nonneg : 0 ≤ C.kappa
  gainFactor_nonneg : 0 ≤ C.gainFactor
  recoveryFactor_nonneg : 0 ≤ C.recoveryFactor
  energyRate_nonneg : 0 ≤ C.energyRate

/-- Ordered positive family members satisfy the weaker uniqueness signs. -/
theorem Admissible.flowSigns {C : Constants} (h : Admissible C) : FlowSigns C :=
  ⟨h.a_pos.le, h.kappa_nonneg, h.gainFactor_pos.le,
    h.recoveryFactor_pos.le, h.energyRate_pos.le⟩

/-- A coordinate cannot cross below zero if its field points inward whenever
that coordinate is nonpositive. This is an integral comparison, including
discontinuous gates and both endpoints. -/
theorem Flow.coordinate_nonnegative {n C θ s u}
    (f : @Flow n C θ s u) (i : Fin n) (k : Coord)
    (initial : 0 ≤ s.x i k)
    (inward : ∀ t ∈ Icc s.time u.time, f.path t i k ≤ 0 →
      0 ≤ field C θ s (f.path t) t i k) {t : ℝ}
    (ht : t ∈ Icc s.time u.time) : 0 ≤ f.path t i k := by
  have sub : Icc s.time t ⊆ Icc s.time u.time := Icc_subset_Icc le_rfl ht.2
  have hi : IntervalIntegrable (fun v => field C θ s (f.path v) v i k)
      volume s.time t := (f.integrable i k).mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le f.positive.le]
    exact sub)
  have h := KernelR.Hybrid.integral_upper_barrier (cap := 0) ht.1
    (((f.continuous i k).mono sub).neg) hi.neg
    (by
      intro v hv
      change -f.path v i k = -f.path s.time i k +
        ∫ w in s.time..v, -field C θ s (f.path w) w i k
      rw [intervalIntegral.integral_neg, f.initial]
      have balance := f.integral_eq v (sub hv) i k
      linarith)
    (by change -f.path s.time i k ≤ 0; rw [f.initial]; linarith)
    (by
      intro v hv hnegative
      change 0 ≤ -f.path v i k at hnegative
      change -field C θ s (f.path v) v i k ≤ 0
      have sign := inward v (sub hv) (by linarith)
      linarith)
  change -f.path t i k ≤ 0 at h
  linarith

theorem pulse_nonnegative {C : Constants} (ha : 0 ≤ C.a) (origin t : ℝ) :
    0 ≤ pulse C origin t := by
  unfold pulse
  split_ifs
  · exact mul_nonneg ha (Real.exp_pos _).le
  · exact le_rfl

theorem current_nonnegative {n C} (ha : 0 ≤ C.a) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) : 0 ≤ current C s i p t := by
  unfold current
  cases s.raw i p with
  | none => exact le_rfl
  | some origin => exact pulse_nonnegative ha origin t

/-- Nonnegative auxiliary charge follows from initial charge and coefficient
signs, without a numerical box or any assumption on an event calendar. -/
theorem Flow.aux_nonnegative {n C θ s u} (f : @Flow n C θ s u)
    (signs : FlowSigns C) (rest : 0 ≤ C.auxRest) (rates : RatesNonnegative θ)
    (i : Fin n) (p : Port) (input : 0 ≤ (θ i).inputGain p)
    (initial : 0 ≤ s.x i (.m p)) {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    0 ≤ f.path t i (.m p) := by
  apply f.coordinate_nonnegative i (.m p) initial _ ht
  intro v hv hm
  rcases rates i p with ⟨mark, silent, error⟩
  have forcing := mul_nonneg input (current_nonnegative signs.a_nonneg s i p v)
  have relax := mul_nonneg signs.kappa_nonneg (sub_nonneg.mpr (hm.trans rest))
  cases mode : s.aux i p with
  | ready => simpa [field, mode] using add_nonneg relax forcing
  | mark =>
    simp only [field, mode, reduceCtorEq, ↓reduceIte, auxDrain]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos mark hm)
  | silent =>
    simp only [field, mode, reduceCtorEq, ↓reduceIte, auxDrain]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos silent hm)
  | error =>
    simp only [field, mode, reduceCtorEq, ↓reduceIte, auxDrain]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos error hm)

/-- MARK actuation never lowers recovery while auxiliary charges and the
coefficient/rates are nonnegative; closed energy/cap gates remain allowed. -/
theorem Flow.recovery_nondecreasing {n C θ s u} (f : @Flow n C θ s u)
    (factor : 0 ≤ C.recoveryFactor) (rates : RatesNonnegative θ)
    (aux : ∀ t ∈ Icc s.time u.time, ∀ i p, 0 ≤ f.path t i (.m p))
    (i : Fin n) {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    s.x i .b ≤ f.path t i .b := by
  have balance := f.integral_eq t ht i .b
  have sign : 0 ≤ ∫ v in s.time..t, field C θ s (f.path v) v i .b := by
    apply intervalIntegral.integral_nonneg ht.1
    intro v hv
    simp only [field]
    apply Finset.sum_nonneg
    intro p _
    unfold markAct
    split_ifs
    · exact mul_nonneg (mul_nonneg factor (rates i p).1)
        (aux v ⟨hv.1, hv.2.trans ht.2⟩ i p)
    · exact le_rfl
  linarith

theorem Flow.recovery_nonnegative {n C θ s u} (f : @Flow n C θ s u)
    (factor : 0 ≤ C.recoveryFactor) (rates : RatesNonnegative θ)
    (aux : ∀ t ∈ Icc s.time u.time, ∀ i p, 0 ≤ f.path t i (.m p))
    (i : Fin n) (initial : 0 ≤ s.x i .b) {t : ℝ}
    (ht : t ∈ Icc s.time u.time) : 0 ≤ f.path t i .b :=
  initial.trans (f.recovery_nondecreasing factor rates aux i ht)

/-- Discharge every Safe premise except positive energy from initial-state
and coefficient signs. A separate reserve barrier supplies `energy`. -/
theorem Flow.safe_of_initial_and_energy {n C θ s u} (f : @Flow n C θ s u)
    (signs : FlowSigns C) (rest : 0 ≤ C.auxRest) (rates : RatesNonnegative θ)
    (input : ∀ i p, 0 ≤ (θ i).inputGain p)
    (initialAux : ∀ i p, 0 ≤ s.x i (.m p))
    (initialRecovery : ∀ i, 0 ≤ s.x i .b)
    (energy : ∀ t ∈ Icc s.time u.time, ∀ i, 0 < f.path t i .energy) :
    f.Safe := by
  have aux : ∀ t ∈ Icc s.time u.time, ∀ i p, 0 ≤ f.path t i (.m p) :=
    fun t ht i p => f.aux_nonnegative signs rest rates i p (input i p) (initialAux i p) ht
  intro t ht i
  exact ⟨energy t ht i,
    f.recovery_nonnegative signs.recoveryFactor_nonneg rates aux i (initialRecovery i) ht,
    aux t ht i⟩

/-- Scalar comparison on the common interval of two actual integral flows. -/
theorem Flow.coordinate_le_of_field_order {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (i : Fin n) (c : Coord)
    {t : ℝ} (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time)
    (horder : ∀ a ∈ Icc s.time t, g.path a i c ≤ f.path a i c →
      field C θ s (f.path a) a i c ≤ field C θ s (g.path a) a i c) :
    f.path t i c ≤ g.path t i c := by
  have hsubf : Icc s.time t ⊆ Icc s.time u.time := Icc_subset_Icc le_rfl hf.2
  have hsubg : Icc s.time t ⊆ Icc s.time v.time := Icc_subset_Icc le_rfl hg.2
  have hif : IntervalIntegrable (fun a => field C θ s (f.path a) a i c) volume s.time t :=
    (f.integrable i c).mono_set (by
      rw [uIcc_of_le hf.1,uIcc_of_le f.positive.le]; exact hsubf)
  have hig : IntervalIntegrable (fun a => field C θ s (g.path a) a i c) volume s.time t :=
    (g.integrable i c).mono_set (by
      rw [uIcc_of_le hg.1,uIcc_of_le g.positive.le]; exact hsubg)
  have h := KernelR.Hybrid.integral_upper_barrier (cap:=0) hf.1
    (((f.continuous i c).mono hsubf).sub ((g.continuous i c).mono hsubg)) (hif.sub hig)
    (by
      intro a ha
      change f.path a i c-g.path a i c=(f.path s.time i c-g.path s.time i c)+_
      rw [intervalIntegral.integral_sub (hif.mono_set (by
        rw [uIcc_of_le ha.1,uIcc_of_le hf.1]; exact Icc_subset_Icc le_rfl ha.2))
        (hig.mono_set (by
        rw [uIcc_of_le ha.1,uIcc_of_le hg.1]; exact Icc_subset_Icc le_rfl ha.2))]
      rw [f.integral_eq a (hsubf ha) i c,g.integral_eq a (hsubg ha) i c,f.initial,g.initial]
      ring)
    (by change f.path s.time i c-g.path s.time i c≤0; simp only [f.initial,g.initial,sub_self,le_refl])
    (by
      intro a ha h
      change 0≤f.path a i c-g.path a i c at h
      exact sub_nonpos.mpr (horder a ha (by linarith)))
  exact sub_nonpos.mp h

/-- Auxiliary coordinates agree before every common observation time. -/
theorem Flow.aux_path_unique {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (i : Fin n) (p : Port) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i (.m p)=g.path t i (.m p) := by
  have cmp : ∀ (f : Flow C θ s u) (g : Flow C θ s v),
      t ∈ Icc s.time u.time → t ∈ Icc s.time v.time →
      f.path t i (.m p)≤g.path t i (.m p) := by
    intro f g hf hg
    apply f.coordinate_le_of_field_order g i (.m p) hf hg
    intro a ha h
    rcases rates i p with ⟨hm,hs,he⟩
    have hk := hc.kappa_nonneg
    cases hmode : s.aux i p <;> simp [field,hmode,auxDrain] <;>
      nlinarith [mul_nonneg hk (sub_nonneg.mpr h),
        mul_nonneg hm (sub_nonneg.mpr h), mul_nonneg hs (sub_nonneg.mpr h),
        mul_nonneg he (sub_nonneg.mpr h)]
  exact le_antisymm (cmp f g hf hg) (by
    apply g.coordinate_le_of_field_order f i (.m p) hg hf
    intro a ha h
    rcases rates i p with ⟨hm,hs,he⟩
    have hk := hc.kappa_nonneg
    cases hmode : s.aux i p <;> simp [field,hmode,auxDrain] <;>
      nlinarith [mul_nonneg hk (sub_nonneg.mpr h),
        mul_nonneg hm (sub_nonneg.mpr h), mul_nonneg hs (sub_nonneg.mpr h),
        mul_nonneg he (sub_nonneg.mpr h)])

private theorem gated_density_antitone {x y cap force : ℝ} (hxy : y≤x) (hforce : 0≤force) :
    (if x<cap then force else 0)≤(if y<cap then force else 0) := by
  split_ifs <;> linarith

private theorem Flow.gain_path_le {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) (p : Port) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i (.z p)≤g.path t i (.z p) := by
  apply f.coordinate_le_of_field_order g i (.z p) hf hg
  intro a ha h
  have haf : a ∈ Icc s.time u.time := ⟨ha.1,ha.2.trans hf.2⟩
  have hag : a ∈ Icc s.time v.time := ⟨ha.1,ha.2.trans hg.2⟩
  have hm := f.aux_path_unique g hc rates i p haf hag
  have hpf := (safeF a haf i).1
  have hpg := (safeG a hag i).1
  by_cases he : s.aux i p=.error
  · by_cases hr : s.main i=.ready
    · have hpos := (safeF a haf i).2.2 p
      have hforce : 0≤C.gainFactor*(θ i).le p*f.path a i (.m p) :=
        mul_nonneg (mul_nonneg hc.gainFactor_nonneg (rates i p).2.2) hpos
      simpa only [field,errorAct,he,hr,hpf,hpg,true_and,hm] using
        gated_density_antitone (cap:=Real.log ((θ i).cap p)) h
          (show 0≤C.gainFactor*(θ i).le p*g.path a i (.m p) by simpa only [←hm] using hforce)
    · simp [field,errorAct,hr]
  · simp [field,errorAct,he]

/-- Gain equality includes the discontinuous cap gate. -/
theorem Flow.gain_path_unique {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) (p : Port) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i (.z p)=g.path t i (.z p) :=
  le_antisymm (f.gain_path_le g hc rates safeF safeG i p hf hg) (g.gain_path_le f hc rates safeG safeF i p hg hf)

private theorem Flow.recovery_path_le {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .b≤g.path t i .b := by
  apply f.coordinate_le_of_field_order g i .b hf hg
  intro a ha h
  have haf : a ∈ Icc s.time u.time := ⟨ha.1,ha.2.trans hf.2⟩
  have hag : a ∈ Icc s.time v.time := ⟨ha.1,ha.2.trans hg.2⟩
  have hpf := (safeF a haf i).1
  have hpg := (safeG a hag i).1
  simp only [field]
  apply Finset.sum_le_sum
  intro p _
  have hm := f.aux_path_unique g hc rates i p haf hag
  by_cases he : s.aux i p=.mark
  · by_cases hr : s.main i=.ready
    · simp [markAct,hr]
    · have hpos := (safeF a haf i).2.2 p
      have hforce : 0≤C.recoveryFactor*(θ i).lm p*f.path a i (.m p) :=
        mul_nonneg (mul_nonneg hc.recoveryFactor_nonneg (rates i p).1) hpos
      simpa [markAct,he,hr,hpf,hpg,hm] using
        gated_density_antitone (cap:=C.recoveryCap) h
          (show 0≤C.recoveryFactor*(θ i).lm p*g.path a i (.m p) by simpa only [←hm] using hforce)
  · simp [markAct,he]

/-- Recovery equality includes the discontinuous shared cap gate. -/
theorem Flow.recovery_path_unique {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .b=g.path t i .b :=
  le_antisymm (f.recovery_path_le g hc rates safeF safeG i hf hg) (g.recovery_path_le f hc rates safeG safeF i hg hf)

private theorem Flow.charge_path_le {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .q≤g.path t i .q := by
  apply f.coordinate_le_of_field_order g i .q hf hg
  intro a ha h
  have haf : a ∈ Icc s.time u.time := ⟨ha.1,ha.2.trans hf.2⟩
  have hag : a ∈ Icc s.time v.time := ⟨ha.1,ha.2.trans hg.2⟩
  have hbpath := f.recovery_path_unique g hc rates safeF safeG i haf hag
  have hz : drive C s (f.path a) i a=drive C s (g.path a) i a := by
    apply Finset.sum_congr rfl
    intro p _
    rw [f.gain_path_unique g hc rates safeF safeG i p haf hag]
  cases hmode : s.main i with
  | ready =>
    simp only [field,hmode,hz]
    nlinarith [mul_nonneg hc.kappa_nonneg (sub_nonneg.mpr h)]
  | fast =>
    simp only [field,hmode]
    nlinarith [mul_nonneg hc.a_nonneg (sub_nonneg.mpr h)]
  | slow =>
    have hbpos : 0≤f.path a i .b := (safeF a haf i).2.1
    simp only [field,hmode,←hbpath]
    nlinarith [mul_nonneg hbpos (sub_nonneg.mpr h)]

/-- Main charge equality after gains and recovery have been identified. -/
theorem Flow.charge_path_unique {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .q=g.path t i .q :=
  le_antisymm (f.charge_path_le g hc rates safeF safeG i hf hg) (g.charge_path_le f hc rates safeG safeF i hg hf)

private theorem Flow.work_path_unique {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    work C θ s (f.path t) i t=work C θ s (g.path t) i t := by
  have hpf := (safeF t hf i).1
  have hpg := (safeG t hg i).1
  have hq := f.charge_path_unique g hc rates safeF safeG i hf hg
  have hz (p) := f.gain_path_unique g hc rates safeF safeG i p hf hg
  have hm (p) := f.aux_path_unique g hc rates i p hf hg
  have hdrive : drive C s (f.path t) i t=drive C s (g.path t) i t := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hz p]
  have haux : (∑ p : Port, if s.aux i p=.ready then (θ i).inputGain p*current C s i p t
      else auxDrain (θ i) (s.aux i p) p (f.path t i (.m p)))=
      ∑ p : Port, if s.aux i p=.ready then (θ i).inputGain p*current C s i p t
      else auxDrain (θ i) (s.aux i p) p (g.path t i (.m p)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hm p]
  have herror : (∑ p : Port, errorAct C θ s (f.path t) i p)=
      ∑ p : Port, errorAct C θ s (g.path t) i p := by
    apply Finset.sum_congr rfl
    intro p _
    simp only [errorAct,hpf,hpg,true_and,hz p,hm p]
  have hmark : (∑ p : Port, markAct C θ s (f.path t) i p)=
      ∑ p : Port, markAct C θ s (g.path t) i p := by
    apply Finset.sum_congr rfl
    intro p _
    simp only [markAct,hpf,hpg,true_and,hm p,f.recovery_path_unique g hc rates safeF safeG i hf hg]
  simp only [work,hq,hdrive,haux,herror,hmark]

private theorem Flow.energy_path_le {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .energy≤g.path t i .energy := by
  apply f.coordinate_le_of_field_order g i .energy hf hg
  intro a ha h
  have haf : a ∈ Icc s.time u.time := ⟨ha.1,ha.2.trans hf.2⟩
  have hag : a ∈ Icc s.time v.time := ⟨ha.1,ha.2.trans hg.2⟩
  have hw := f.work_path_unique g hc rates safeF safeG i haf hag
  simp only [field,hw]
  nlinarith [mul_nonneg hc.energyRate_nonneg (sub_nonneg.mpr h)]

/-- Energy equality is derived after all actual work terms agree. -/
theorem Flow.energy_path_unique {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .energy=g.path t i .energy :=
  le_antisymm (f.energy_path_le g hc rates safeF safeG i hf hg) (g.energy_path_le f hc rates safeG safeF i hg hf)

/-- Two physical flows from the same snapshot agree at every common time,
including both endpoints. No trajectory formula or uniqueness premise is used. -/
theorem Flow.path_unique {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v) (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t=g.path t := by
  funext i c
  cases c with
  | q => exact f.charge_path_unique g hc rates safeF safeG i hf hg
  | m p => exact f.aux_path_unique g hc rates i p hf hg
  | z p => exact f.gain_path_unique g hc rates safeF safeG i p hf hg
  | b => exact f.recovery_path_unique g hc rates safeF safeG i hf hg
  | energy => exact f.energy_path_unique g hc rates safeF safeG i hf hg


/-- Equal flow endpoint dates imply equal physical endpoint observations. -/
theorem Flow.final_observational_unique {n C θ s u v}
    (f : @Flow n C θ s u) (g : Flow C θ s v)
    (hc : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (ht : u.time = v.time) :
    u.ObservationalEq v := by
  refine ⟨ht, ?_, f.main_fixed.trans g.main_fixed.symm,
    f.aux_fixed.trans g.aux_fixed.symm, f.raw_fixed.trans g.raw_fixed.symm, ?_⟩
  · have h := f.path_unique g hc rates safeF safeG ⟨f.positive.le, le_rfl⟩
      (show u.time ∈ Icc s.time v.time by rw [ht]; exact ⟨g.positive.le, le_rfl⟩)
    rw [f.final, ht, g.final] at h
    exact h
  · rw [f.queue_fixed, g.queue_fixed]

#print axioms Flow.path_unique
#print axioms Flow.final_observational_unique
end KernelR.Family
