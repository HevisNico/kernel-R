import KernelR.HybridParameterPhysical

/-! Integral comparison with realized thresholds. The coordinates are compared
in dependency order, using the physical reserve to open the power gate. -/
namespace KernelR.Hybrid
open MeasureTheory Set

/-- Scalar comparison on the common interval of two actual integral flows. -/
theorem ParameterFlow.coordinate_le_of_field_order {n θ s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (i : Fin n) (c : Coord)
    {t : ℝ} (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time)
    (horder : ∀ a ∈ Icc s.time t, g.path a i c ≤ f.path a i c →
      field θ s (f.path a) a i c ≤ field θ s (g.path a) a i c) :
    f.path t i c ≤ g.path t i c := by
  have hsubf : Icc s.time t ⊆ Icc s.time u.time := Icc_subset_Icc le_rfl hf.2
  have hsubg : Icc s.time t ⊆ Icc s.time v.time := Icc_subset_Icc le_rfl hg.2
  have hif : IntervalIntegrable (fun a => field θ s (f.path a) a i c) volume s.time t :=
    (f.integrable i c).mono_set (by
      rw [uIcc_of_le hf.1,uIcc_of_le f.positive.le]; exact hsubf)
  have hig : IntervalIntegrable (fun a => field θ s (g.path a) a i c) volume s.time t :=
    (g.integrable i c).mono_set (by
      rw [uIcc_of_le hg.1,uIcc_of_le g.positive.le]; exact hsubg)
  have h := integral_upper_barrier (cap:=0) hf.1
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
theorem ParameterFlow.aux_path_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i (.m p)=g.path t i (.m p) := by
  have cmp : ∀ (f : ParameterFlow θ s u) (g : ParameterFlow θ s v),
      t ∈ Icc s.time u.time → t ∈ Icc s.time v.time →
      f.path t i (.m p)≤g.path t i (.m p) := by
    intro f g hf hg
    apply f.coordinate_le_of_field_order g i (.m p) hf hg
    intro a ha h
    rcases hb.rates_positive i p with ⟨hm,hs,he⟩
    cases hmode : s.aux i p <;> simp [field,hmode,auxDrain] <;> nlinarith
  exact le_antisymm (cmp f g hf hg) (by
    apply g.coordinate_le_of_field_order f i (.m p) hg hf
    intro a ha h
    rcases hb.rates_positive i p with ⟨hm,hs,he⟩
    cases hmode : s.aux i p <;> simp [field,hmode,auxDrain] <;> nlinarith)

private theorem gated_density_antitone {x y cap force : ℝ} (hxy : y≤x) (hforce : 0≤force) :
    (if x<cap then force else 0)≤(if y<cap then force else 0) := by
  split_ifs <;> linarith

private theorem ParameterFlow.gain_path_le {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) (p : Port) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i (.z p)≤g.path t i (.z p) := by
  apply f.coordinate_le_of_field_order g i (.z p) hf hg
  intro a ha h
  have haf : a ∈ Icc s.time u.time := ⟨ha.1,ha.2.trans hf.2⟩
  have hag : a ∈ Icc s.time v.time := ⟨ha.1,ha.2.trans hg.2⟩
  have hm := f.aux_path_unique g hb i p haf hag
  have hpf := show 0 < f.path a i .energy by linarith [(f.reserve_on bounds hb hs i haf).1]
  have hpg := show 0 < g.path a i .energy by linarith [(g.reserve_on bounds hb hs i hag).1]
  by_cases he : s.aux i p=.error
  · by_cases hr : s.main i=.ready
    · have hpos := f.protected_aux_nonnegative bounds i p (by simp [he]) haf
      have hforce : 0≤8*(θ i).le p*f.path a i (.m p) :=
        mul_nonneg (mul_nonneg (by norm_num) (hb.rates_positive i p).2.2.le) hpos
      simpa only [field,errorAct,he,hr,hpf,hpg,true_and,hm] using
        gated_density_antitone (cap:=Real.log ((θ i).cap p)) h
          (show 0≤8*(θ i).le p*g.path a i (.m p) by simpa only [←hm] using hforce)
    · simp [field,errorAct,hr]
  · simp [field,errorAct,he]

/-- Gain equality includes the discontinuous cap gate. -/
theorem ParameterFlow.gain_path_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) (p : Port) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i (.z p)=g.path t i (.z p) :=
  le_antisymm (f.gain_path_le g hb bounds hs i p hf hg) (g.gain_path_le f hb bounds hs i p hg hf)

private theorem ParameterFlow.recovery_path_le {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .b≤g.path t i .b := by
  apply f.coordinate_le_of_field_order g i .b hf hg
  intro a ha h
  have haf : a ∈ Icc s.time u.time := ⟨ha.1,ha.2.trans hf.2⟩
  have hag : a ∈ Icc s.time v.time := ⟨ha.1,ha.2.trans hg.2⟩
  have hpf := show 0 < f.path a i .energy by linarith [(f.reserve_on bounds hb hs i haf).1]
  have hpg := show 0 < g.path a i .energy by linarith [(g.reserve_on bounds hb hs i hag).1]
  simp only [field]
  apply Finset.sum_le_sum
  intro p _
  have hm := f.aux_path_unique g hb i p haf hag
  by_cases he : s.aux i p=.mark
  · by_cases hr : s.main i=.ready
    · simp [markAct,hr]
    · have hpos := f.protected_aux_nonnegative bounds i p (by simp [he]) haf
      have hforce : 0≤(1/2:ℝ)*(θ i).lm p*f.path a i (.m p) :=
        mul_nonneg (mul_nonneg (by norm_num) (hb.rates_positive i p).1.le) hpos
      simpa [markAct,he,hr,hpf,hpg,hm] using
        gated_density_antitone (cap:=(11/10:ℝ)) h
          (show 0≤(1/2:ℝ)*(θ i).lm p*g.path a i (.m p) by simpa only [←hm] using hforce)
  · simp [markAct,he]

/-- Recovery equality includes the discontinuous shared cap gate. -/
theorem ParameterFlow.recovery_path_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .b=g.path t i .b :=
  le_antisymm (f.recovery_path_le g hb bounds hs i hf hg) (g.recovery_path_le f hb bounds hs i hg hf)

private theorem ParameterFlow.charge_path_le {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .q≤g.path t i .q := by
  apply f.coordinate_le_of_field_order g i .q hf hg
  intro a ha h
  have haf : a ∈ Icc s.time u.time := ⟨ha.1,ha.2.trans hf.2⟩
  have hag : a ∈ Icc s.time v.time := ⟨ha.1,ha.2.trans hg.2⟩
  have hbpath := f.recovery_path_unique g hb bounds hs i haf hag
  have hz : drive s (f.path a) i a=drive s (g.path a) i a := by
    apply Finset.sum_congr rfl
    intro p _
    rw [f.gain_path_unique g hb bounds hs i p haf hag]
  cases hmode : s.main i with
  | ready => simp only [field,hmode,hz]; linarith
  | fast => simp only [field,hmode]; nlinarith [a_coarse_bounds.1]
  | slow =>
    have hbpos : 0≤f.path a i .b :=
      (hs.recovery i).1.trans (f.recovery_nondecreasing bounds hb i haf)
    simp only [field,hmode,←hbpath]
    nlinarith

/-- Main charge equality after gains and recovery have been identified. -/
theorem ParameterFlow.charge_path_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .q=g.path t i .q :=
  le_antisymm (f.charge_path_le g hb bounds hs i hf hg) (g.charge_path_le f hb bounds hs i hg hf)

private theorem ParameterFlow.work_path_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    work θ s (f.path t) i t=work θ s (g.path t) i t := by
  have hpf := show 0 < f.path t i .energy by linarith [(f.reserve_on bounds hb hs i hf).1]
  have hpg := show 0 < g.path t i .energy by linarith [(g.reserve_on bounds hb hs i hg).1]
  have hq := f.charge_path_unique g hb bounds hs i hf hg
  have hz (p) := f.gain_path_unique g hb bounds hs i p hf hg
  have hm (p) := f.aux_path_unique g hb i p hf hg
  have hdrive : drive s (f.path t) i t=drive s (g.path t) i t := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hz p]
  have haux : (∑ p : Port, if s.aux i p=.ready then (θ i).inputGain p*current s i p t
      else auxDrain (θ i) (s.aux i p) p (f.path t i (.m p)))=
      ∑ p : Port, if s.aux i p=.ready then (θ i).inputGain p*current s i p t
      else auxDrain (θ i) (s.aux i p) p (g.path t i (.m p)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hm p]
  have herror : (∑ p : Port, errorAct θ s (f.path t) i p)=
      ∑ p : Port, errorAct θ s (g.path t) i p := by
    apply Finset.sum_congr rfl
    intro p _
    simp only [errorAct,hpf,hpg,true_and,hz p,hm p]
  have hmark : (∑ p : Port, markAct θ s (f.path t) i p)=
      ∑ p : Port, markAct θ s (g.path t) i p := by
    apply Finset.sum_congr rfl
    intro p _
    simp only [markAct,hpf,hpg,true_and,hm p,f.recovery_path_unique g hb bounds hs i hf hg]
  simp only [work,hq,hdrive,haux,herror,hmark]

private theorem ParameterFlow.energy_path_le {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .energy≤g.path t i .energy := by
  apply f.coordinate_le_of_field_order g i .energy hf hg
  intro a ha h
  have haf : a ∈ Icc s.time u.time := ⟨ha.1,ha.2.trans hf.2⟩
  have hag : a ∈ Icc s.time v.time := ⟨ha.1,ha.2.trans hg.2⟩
  have hw := f.work_path_unique g hb bounds hs i haf hag
  simp only [field,hw]
  linarith

/-- Energy equality is derived after all actual work terms agree. -/
theorem ParameterFlow.energy_path_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (i : Fin n) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t i .energy=g.path t i .energy :=
  le_antisymm (f.energy_path_le g hb bounds hs i hf hg) (g.energy_path_le f hb bounds hs i hg hf)

/-- Two physical flows from the same snapshot agree at every common time,
including both endpoints. No trajectory formula or uniqueness premise is used. -/
theorem ParameterFlow.path_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    f.path t=g.path t := by
  funext i c
  cases c with
  | q => exact f.charge_path_unique g hb bounds hs i hf hg
  | m p => exact f.aux_path_unique g hb i p hf hg
  | z p => exact f.gain_path_unique g hb bounds hs i p hf hg
  | b => exact f.recovery_path_unique g hb bounds hs i hf hg
  | energy => exact f.energy_path_unique g hb bounds hs i hf hg

/-- Common intermediate flow snapshots agree observationally. -/
theorem ParameterFlow.at_observational_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    (f.at t).ObservationalEq (g.at t) :=
  ⟨rfl,f.path_unique g hb bounds hs hf hg,rfl,rfl,rfl,List.Perm.refl _⟩

/-- Equal flow endpoint dates imply equal endpoint physical observations. -/
theorem ParameterFlow.final_observational_unique {n θ ε s u v}
    (f : @ParameterFlow n θ s u) (g : ParameterFlow θ s v) (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s) (ht : u.time=v.time) : u.ObservationalEq v := by
  refine ⟨ht,?_,f.main_fixed.trans g.main_fixed.symm,
    f.aux_fixed.trans g.aux_fixed.symm,f.raw_fixed.trans g.raw_fixed.symm,?_⟩
  · have h := f.path_unique g hb bounds hs ⟨f.positive.le,le_rfl⟩
      (show u.time ∈ Icc s.time v.time by rw [ht]; exact ⟨g.positive.le,le_rfl⟩)
    rw [f.final,ht,g.final] at h
    exact h
  · rw [f.queue_fixed,g.queue_fixed]

end KernelR.Hybrid
