import KernelR.HybridCellOrbitGerm

/-! A counterfactual cell continuation with every plastic actuator, including
closed cap gates. The ODE is triangular once the incoming modes are fixed. -/
namespace KernelR.Hybrid
open MeasureTheory Set Filter
open scoped Topology

noncomputable def germErrorRate {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  if s.aux i p = .error ∧ s.main i = .ready ∧
      s.x i (.z p) < Real.log ((θ i).cap p) then
    8 * (θ i).le p * cellBaseValues θ s t i (.m p) else 0

noncomputable def germMarkRate {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  if s.aux i p = .mark ∧ s.main i ≠ .ready ∧ s.x i .b < 11 / 10 then
    (1 / 2) * (θ i).lm p * cellBaseValues θ s t i (.m p) else 0

@[fun_prop] theorem germErrorRate_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) :
    Continuous (germErrorRate θ s i p) := by
  unfold germErrorRate; split_ifs <;> fun_prop

@[fun_prop] theorem germMarkRate_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) :
    Continuous (germMarkRate θ s i p) := by
  unfold germMarkRate; split_ifs <;> fun_prop

noncomputable def germGain {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  s.x i (.z p) + ∫ v in s.time..t, germErrorRate θ s i p v

noncomputable def germRecovery {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (t : ℝ) : ℝ :=
  s.x i .b + ∫ v in s.time..t, ∑ p : Port, germMarkRate θ s i p v

private theorem integral_derivative {f : ℝ → ℝ} (hc : Continuous f) (start t : ℝ) :
    HasDerivAt (fun u => ∫ v in start..u, f v) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable start t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem germGain_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    HasDerivAt (germGain θ s i p) (germErrorRate θ s i p t) t :=
  (integral_derivative (germErrorRate_continuous s i p) s.time t).const_add _

theorem germRecovery_derivative {n θ} (s : Snapshot n) (i : Fin n) (t : ℝ) :
    HasDerivAt (germRecovery θ s i) (∑ p : Port, germMarkRate θ s i p t) t :=
  (integral_derivative (continuous_finsetSum _ (fun p _ => germMarkRate_continuous s i p))
    s.time t).const_add _

@[fun_prop] theorem germGain_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) :
    Continuous (germGain θ s i p) :=
  continuous_iff_continuousAt.mpr (fun t => (germGain_derivative s i p t).continuousAt)

@[fun_prop] theorem germRecovery_continuous {n θ} (s : Snapshot n) (i : Fin n) :
    Continuous (germRecovery θ s i) :=
  continuous_iff_continuousAt.mpr (fun t => (germRecovery_derivative s i t).continuousAt)

noncomputable def germDrive {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (t : ℝ) : ℝ :=
  ∑ p : Port, Real.exp (germGain θ s i p t) * cellTailCurrent s i p t

@[fun_prop] theorem germDrive_continuous {n θ} (s : Snapshot n) (i : Fin n) :
    Continuous (germDrive θ s i) := by
  unfold germDrive
  apply continuous_finsetSum
  intro p _
  unfold cellTailCurrent
  fun_prop

noncomputable def germMain {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (t : ℝ) : ℝ :=
  match s.main i with
  | .ready => relax (1 / 2) (1 / 10) (s.x i .q) s.time t +
      linearConvolution (1 / 2) (germDrive θ s i) s.time t
  | .fast => s.x i .q * Real.exp (-a * (t - s.time))
  | .slow => s.x i .q * Real.exp (-(∫ v in s.time..t, germRecovery θ s i v))

@[fun_prop] theorem germMain_continuous {n θ} (s : Snapshot n) (i : Fin n) :
    Continuous (germMain θ s i) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  change ContinuousAt (fun v => germMain θ s i v) t
  cases hm : s.main i with
  | ready =>
    simp only [germMain, hm]
    dsimp only [relax]
    fun_prop
  | fast => simp only [germMain, hm]; fun_prop
  | slow =>
    simp only [germMain, hm]
    exact ((integral_derivative (germRecovery_continuous s i) s.time t).neg.exp.const_mul _).continuousAt

noncomputable def germWork {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (t : ℝ) : ℝ :=
  (match s.main i with
    | .ready => germDrive θ s i t
    | .fast => a * germMain θ s i t
    | .slow => 11 / 10) +
  (∑ p : Port, if s.aux i p = .ready then (θ i).inputGain p * cellTailCurrent s i p t
    else auxDrain (θ i) (s.aux i p) p (cellBaseValues θ s t i (.m p))) +
  (∑ p : Port, germErrorRate θ s i p t) + ∑ p : Port, germMarkRate θ s i p t

@[fun_prop] theorem germWork_continuous {n θ} (s : Snapshot n) (i : Fin n) :
    Continuous (germWork θ s i) := by
  unfold germWork
  have hc (p : Port) : Continuous (fun t => if s.aux i p = .ready then
      (θ i).inputGain p * cellTailCurrent s i p t else
      auxDrain (θ i) (s.aux i p) p (cellBaseValues θ s t i (.m p))) := by
    split_ifs
    · unfold cellTailCurrent; fun_prop
    · cases s.aux i p <;> simp only [auxDrain] <;> fun_prop
  cases s.main i <;> dsimp only <;> fun_prop

noncomputable def fullCellOrbitValues {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (t : ℝ) : Values n := fun i c => match c with
  | .q => germMain θ s i t
  | .m p => cellBaseValues θ s t i (.m p)
  | .z p => germGain θ s i p t
  | .b => germRecovery θ s i t
  | .energy => relax 10 100 (s.x i .energy) s.time t -
      linearConvolution 10 (germWork θ s i) s.time t

@[fun_prop] theorem fullCellOrbitValues_continuous {n θ} (s : Snapshot n) (i : Fin n) (c : Coord) :
    Continuous (fun t => fullCellOrbitValues θ s t i c) := by
  cases c <;> simp only [fullCellOrbitValues] <;> (try dsimp only [relax]) <;> fun_prop

theorem fullCellOrbitValues_initial {n θ} (s : Snapshot n) :
    fullCellOrbitValues θ s s.time = s.x := by
  funext i c
  cases c with
  | q => cases hm : s.main i <;> simp [fullCellOrbitValues, germMain, hm, relax_initial,
      linearConvolution_initial]
  | m p => simp [fullCellOrbitValues, cellBaseValues, auxPulse_initial]
  | z p => simp [fullCellOrbitValues, germGain]
  | b => simp [fullCellOrbitValues, germRecovery]
  | energy => simp [fullCellOrbitValues, relax_initial, linearConvolution_initial]

noncomputable def fullCellOrbitRhs {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (t : ℝ) (i : Fin n) : Coord → ℝ
  | .q => match s.main i with
    | .ready => (1 / 2) * (1 / 10 - germMain θ s i t) + germDrive θ s i t
    | .fast => -a * germMain θ s i t
    | .slow => -germRecovery θ s i t * germMain θ s i t
  | .m p => cellOrbitRhs θ s t i (.m p)
  | .z p => germErrorRate θ s i p t
  | .b => ∑ p : Port, germMarkRate θ s i p t
  | .energy => 10 * (100 - fullCellOrbitValues θ s t i .energy) - germWork θ s i t

theorem fullCellOrbitValues_derivative {n θ} (s : Snapshot n) (i : Fin n) (c : Coord) (t : ℝ) :
    HasDerivAt (fun v => fullCellOrbitValues θ s v i c) (fullCellOrbitRhs θ s t i c) t := by
  cases c with
  | q =>
    cases hm : s.main i with
    | ready =>
      simp only [fullCellOrbitValues, fullCellOrbitRhs, germMain, hm]
      convert ((relax_derivative (1 / 2) (1 / 10) (s.x i .q) s.time t).add
        (linearConvolution_derivative (germDrive_continuous (θ := θ) s i) (1 / 2) s.time t)) using 1; ring
    | fast =>
      convert (((((hasDerivAt_id t).sub_const s.time).const_mul (-a)).exp).const_mul
        (s.x i .q)) using 1 <;> simp only [fullCellOrbitValues, fullCellOrbitRhs, germMain, hm, id_eq]; ring
    | slow =>
      simp only [fullCellOrbitValues, fullCellOrbitRhs, germMain, hm]
      convert ((integral_derivative (germRecovery_continuous (θ := θ) s i) s.time t).neg.exp.const_mul
        (s.x i .q)) using 1; simp only [Pi.neg_apply]; ring
  | m p => exact cellOrbitValues_derivative s i (.m p) t
  | z p => exact germGain_derivative s i p t
  | b => exact germRecovery_derivative s i t
  | energy =>
    exact ((relax_derivative 10 100 (s.x i .energy) s.time t).sub
      (linearConvolution_derivative (germWork_continuous s i) 10 s.time t)).congr_deriv
        (by dsimp [fullCellOrbitValues, fullCellOrbitRhs]; ring)

theorem germGain_constant_of_closed {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (closed : ¬ s.x i (.z p) < Real.log ((θ i).cap p)) (t : ℝ) :
    germGain θ s i p t = s.x i (.z p) := by
  simp [germGain, germErrorRate, closed]

theorem germRecovery_constant_of_closed {n θ} (s : Snapshot n) (i : Fin n)
    (closed : ¬ s.x i .b < 11 / 10) (t : ℝ) :
    germRecovery θ s i t = s.x i .b := by
  simp [germRecovery, germMarkRate, closed]

/-- The frozen cap branches agree locally with the actual strict gates. Closed
branches are exactly constant, so this also handles a cap reached at the base. -/
theorem fullCellOrbitValues_local_gates {n θ} (s : Snapshot n) (i : Fin n)
    (energy : 0 < s.x i .energy) :
    ∀ᶠ t in 𝓝 s.time,
      0 < fullCellOrbitValues θ s t i .energy ∧
      (∀ p, errorAct θ s (fullCellOrbitValues θ s t) i p = germErrorRate θ s i p t) ∧
      (∀ p, markAct θ s (fullCellOrbitValues θ s t) i p = germMarkRate θ s i p t) := by
  have initial : ∀ c, fullCellOrbitValues θ s s.time i c = s.x i c :=
    fun c => congrFun (congrFun (fullCellOrbitValues_initial (θ := θ) s) i) c
  have he : ∀ᶠ t in 𝓝 s.time, 0 < fullCellOrbitValues θ s t i .energy :=
    (fullCellOrbitValues_continuous (θ := θ) s i .energy).continuousAt.eventually
      (Ioi_mem_nhds (by simpa only [initial] using energy))
  have hz : ∀ p : Port, ∀ᶠ t in 𝓝 s.time,
      (germGain θ s i p t < Real.log ((θ i).cap p) ↔
        s.x i (.z p) < Real.log ((θ i).cap p)) := by
    intro p
    by_cases hp : s.x i (.z p) < Real.log ((θ i).cap p)
    · have hi : germGain θ s i p s.time < Real.log ((θ i).cap p) := by simpa [germGain] using hp
      filter_upwards [(germGain_continuous (θ := θ) s i p).continuousAt.eventually (Iio_mem_nhds hi)] with t ht
      exact iff_of_true ht hp
    · exact Filter.Eventually.of_forall (fun t => by rw [germGain_constant_of_closed s i p hp t])
  have hb : ∀ᶠ t in 𝓝 s.time,
      (germRecovery θ s i t < 11 / 10 ↔ s.x i .b < 11 / 10) := by
    by_cases hp : s.x i .b < 11 / 10
    · have hi : germRecovery θ s i s.time < 11 / 10 := by simpa [germRecovery] using hp
      filter_upwards [(germRecovery_continuous (θ := θ) s i).continuousAt.eventually (Iio_mem_nhds hi)] with t ht
      exact iff_of_true ht hp
    · exact Filter.Eventually.of_forall (fun t => by rw [germRecovery_constant_of_closed s i hp t])
  have hzs : ∀ᶠ t in 𝓝 s.time, ∀ p : Port,
      (germGain θ s i p t < Real.log ((θ i).cap p) ↔
        s.x i (.z p) < Real.log ((θ i).cap p)) := eventually_all.mpr hz
  filter_upwards [he, hb, hzs] with t ht hb hz
  refine ⟨ht, ?_, ?_⟩
  all_goals change 0 < relax 10 100 (s.x i .energy) s.time t -
    linearConvolution 10 (germWork θ s i) s.time t at ht
  · intro p
    simp only [errorAct, germErrorRate, fullCellOrbitValues, ht, true_and, hz p]
  · intro p
    simp only [markAct, germMarkRate, fullCellOrbitValues, ht, true_and, hb]

theorem fullCellOrbitValues_field {n θ} (s : Snapshot n) (i : Fin n) (t : ℝ)
    (raw : ∀ p, current s i p t = cellTailCurrent s i p t)
    (errors : ∀ p, errorAct θ s (fullCellOrbitValues θ s t) i p = germErrorRate θ s i p t)
    (marks : ∀ p, markAct θ s (fullCellOrbitValues θ s t) i p = germMarkRate θ s i p t)
    (c : Coord) :
    field θ s (fullCellOrbitValues θ s t) t i c = fullCellOrbitRhs θ s t i c := by
  have hdrive : drive s (fullCellOrbitValues θ s t) i t = germDrive θ s i t := by
    simp only [drive, fullCellOrbitValues, germDrive, raw]
  cases c with
  | q => cases hm : s.main i <;> simp [field, fullCellOrbitRhs, hm, hdrive, fullCellOrbitValues]
  | m p => simp [field, fullCellOrbitRhs, cellOrbitRhs, fullCellOrbitValues,
      cellOrbitValues, raw]
  | z p => exact errors p
  | b => simp [field, fullCellOrbitRhs, marks]
  | energy =>
    have hwork : work θ s (fullCellOrbitValues θ s t) i t = germWork θ s i t := by
      simp only [work, errors, marks, germWork]
      cases hm : s.main i <;> simp [hdrive, fullCellOrbitValues, raw]
    simp only [field, fullCellOrbitRhs, hwork]

/-- Every state with positive energy admits a genuine full-cell incoming-mode
ODE germ, even when plastic actuators are active or their caps are closed. -/
theorem exists_cellOrbitOfPositiveEnergy {n θ} (s : Snapshot n) (i : Fin n)
    (energy : 0 < s.x i .energy) : Nonempty (CellOrbitGerm θ s i) := by
  obtain ⟨δ, hδ, hraw⟩ := current_right_germ s i
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (fullCellOrbitValues_local_gates (θ := θ) s i energy)
  let duration := min δ ε
  have positive : 0 < duration := lt_min hδ hε
  refine ⟨{
    duration := duration
    positive := positive
    path := fullCellOrbitValues θ s
    initial := congrFun (fullCellOrbitValues_initial (θ := θ) s) i
    derivative := ?_
  }⟩
  intro t ht c
  have hdist : dist t s.time < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have hbound : duration ≤ ε := min_le_right _ _
    linarith [ht.2]
  have hg := hlocal hdist
  apply (fullCellOrbitValues_derivative s i c t).congr_deriv
  symm
  apply fullCellOrbitValues_field s i t _ hg.2.1 hg.2.2 c
  intro p
  apply hraw p t
  exact ⟨ht.1, ht.2.trans_le (by dsimp [duration]; linarith [min_le_left δ ε])⟩

noncomputable def cellOrbitOfPositiveEnergy {n θ} (s : Snapshot n) (i : Fin n)
    (energy : 0 < s.x i .energy) : CellOrbitGerm θ s i :=
  Classical.choice (exists_cellOrbitOfPositiveEnergy s i energy)

/-- The physical reserve supplies the only initial condition needed here. -/
noncomputable def PhysicalInvariant.cell_orbit {n θ s} (physical : @PhysicalInvariant n θ s)
    (i : Fin n) : CellOrbitGerm θ s i :=
  cellOrbitOfPositiveEnergy s i (by linarith [(physical.reserve i).1])

end KernelR.Hybrid
