import KernelR.HybridContactTransversality
import KernelR.HybridErrorTailFlowExistence
import KernelR.HybridRawRightGerm

/-! Counterfactual continuations of one physical cell, with all its coordinates
solving the incoming-mode ODE. No threshold guard or pending-queue condition is
imposed after the contact. Other cells cannot affect this cell's vector field. -/
namespace KernelR.Hybrid
open Set Filter
open scoped Topology

/-- A genuine incoming-mode ODE germ of the entire contact cell. -/
structure CellOrbitGerm {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) where
  duration : ℝ
  positive : 0 < duration
  path : ℝ → Values n
  initial : path s.time i = s.x i
  derivative : ∀ t ∈ Ico s.time (s.time + duration), ∀ c,
    HasDerivAt (fun v => path v i c) (field θ s (path t) t i c) t

noncomputable def cellTailCurrent {n} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  current s i p s.time * Real.exp (-a * (t - s.time))

noncomputable def cellMainAmplitude {n} (s : Snapshot n) (i : Fin n) : ℝ :=
  ∑ p : Port, Real.exp (s.x i (.z p)) * (current s i p s.time / a)

noncomputable def cellAuxAmplitude {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) : ℝ := (θ i).inputGain p * (current s i p s.time / a)

noncomputable def cellBaseValues {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (t : ℝ) : Values n := fun i c => match c with
  | .q => match s.main i with
    | .ready => readyPulse (s.x i .q) (cellMainAmplitude s i) s.time t
    | .fast => s.x i .q * Real.exp (-a * (t - s.time))
    | .slow => s.x i .q * Real.exp (-s.x i .b * (t - s.time))
  | .m p => if s.aux i p = .ready then
      auxPulse (s.x i (.m p)) (cellAuxAmplitude θ s i p) s.time t
    else s.x i (.m p) * Real.exp (-protectedReadyRate (θ i) p (s.aux i p) * (t - s.time))
  | .z p => s.x i (.z p)
  | .b => s.x i .b
  | .energy => s.x i .energy

noncomputable def cellSmoothWork {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (t : ℝ) : ℝ :=
  (match s.main i with
    | .ready => ∑ p : Port, Real.exp (s.x i (.z p)) * cellTailCurrent s i p t
    | .fast => a * cellBaseValues θ s t i .q
    | .slow => 11 / 10) +
  ∑ p : Port, if s.aux i p = .ready then (θ i).inputGain p * cellTailCurrent s i p t
    else auxDrain (θ i) (s.aux i p) p (cellBaseValues θ s t i (.m p))

@[fun_prop] theorem cellBaseValues_continuous {n θ} (s : Snapshot n) (i : Fin n) (c : Coord) :
    Continuous (fun t => cellBaseValues θ s t i c) := by
  cases c with
  | q => cases hm : s.main i <;> simp only [cellBaseValues, hm, readyPulse, response] <;> fun_prop
  | m p => simp only [cellBaseValues]; split_ifs <;> (try dsimp only [auxPulse, readyPulse, response]) <;> fun_prop
  | z p => exact continuous_const
  | b => exact continuous_const
  | energy => exact continuous_const

@[fun_prop] theorem cellSmoothWork_continuous {n θ} (s : Snapshot n) (i : Fin n) :
    Continuous (cellSmoothWork θ s i) := by
  unfold cellSmoothWork
  apply Continuous.add
  · cases hm : s.main i <;> simp only [cellTailCurrent] <;> fun_prop
  · apply continuous_finsetSum
    intro p _
    split_ifs
    · unfold cellTailCurrent; fun_prop
    · cases hm : s.aux i p <;> simp only [auxDrain] <;> fun_prop

noncomputable def cellOrbitValues {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (t : ℝ) : Values n := fun i c => match c with
  | .energy => relax 10 100 (s.x i .energy) s.time t -
      linearConvolution 10 (cellSmoothWork θ s i) s.time t
  | c => cellBaseValues θ s t i c

noncomputable def cellOrbitRhs {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (t : ℝ) (i : Fin n) : Coord → ℝ
  | .q => match s.main i with
    | .ready => (1 / 2) * (1 / 10 - cellOrbitValues θ s t i .q) +
        ∑ p : Port, Real.exp (s.x i (.z p)) * cellTailCurrent s i p t
    | .fast => -a * cellOrbitValues θ s t i .q
    | .slow => -s.x i .b * cellOrbitValues θ s t i .q
  | .m p => if s.aux i p = .ready then
      (1 / 2) * (1 / 40 - cellOrbitValues θ s t i (.m p)) +
        (θ i).inputGain p * cellTailCurrent s i p t
    else -auxDrain (θ i) (s.aux i p) p (cellOrbitValues θ s t i (.m p))
  | .z _ => 0
  | .b => 0
  | .energy => 10 * (100 - cellOrbitValues θ s t i .energy) - cellSmoothWork θ s i t

theorem cellOrbitValues_initial {n θ} (s : Snapshot n) : cellOrbitValues θ s s.time = s.x := by
  funext i c
  cases c with
  | q => cases hm : s.main i <;> simp [cellOrbitValues, cellBaseValues, hm, readyPulse_initial]
  | m p => simp [cellOrbitValues, cellBaseValues, auxPulse_initial]
  | z p => rfl
  | b => rfl
  | energy => simp [cellOrbitValues, relax_initial, linearConvolution_initial]

theorem cell_main_forcing {n} (s : Snapshot n) (i : Fin n) (t : ℝ) :
    cellMainAmplitude s i * a * Real.exp (-a * (t - s.time)) =
      ∑ p : Port, Real.exp (s.x i (.z p)) * cellTailCurrent s i p t := by
  have ha : a ≠ 0 := ne_of_gt (lt_trans (by norm_num) a_coarse_bounds.1)
  simp only [cellMainAmplitude, cellTailCurrent, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  field_simp

theorem cell_aux_forcing {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    cellAuxAmplitude θ s i p * a * Real.exp (-a * (t - s.time)) =
      (θ i).inputGain p * cellTailCurrent s i p t := by
  have ha : a ≠ 0 := ne_of_gt (lt_trans (by norm_num) a_coarse_bounds.1)
  simp only [cellAuxAmplitude, cellTailCurrent]
  field_simp

theorem cellOrbitValues_derivative {n θ} (s : Snapshot n) (i : Fin n) (c : Coord) (t : ℝ) :
    HasDerivAt (fun v => cellOrbitValues θ s v i c) (cellOrbitRhs θ s t i c) t := by
  cases c with
  | q =>
    cases hm : s.main i with
    | ready =>
      simpa only [cellOrbitValues, cellBaseValues, cellOrbitRhs, hm, cell_main_forcing] using
        readyPulse_derivative (s.x i .q) (cellMainAmplitude s i) s.time t
    | fast =>
      convert (((((hasDerivAt_id t).sub_const s.time).const_mul (-a)).exp).const_mul
        (s.x i .q)) using 1 <;> simp only [cellOrbitValues, cellBaseValues, cellOrbitRhs, hm, id_eq]; ring
    | slow =>
      convert (((((hasDerivAt_id t).sub_const s.time).const_mul (-s.x i .b)).exp).const_mul
        (s.x i .q)) using 1 <;> simp only [cellOrbitValues, cellBaseValues, cellOrbitRhs, hm, id_eq]; ring
  | m p =>
    by_cases hm : s.aux i p = .ready
    · simpa only [cellOrbitValues, cellBaseValues, cellOrbitRhs, hm, ite_true, cell_aux_forcing] using
        auxPulse_derivative (s.x i (.m p)) (cellAuxAmplitude θ s i p) s.time t
    · convert (((((hasDerivAt_id t).sub_const s.time).const_mul
        (-protectedReadyRate (θ i) p (s.aux i p))).exp).const_mul (s.x i (.m p))) using 1
      · funext v; simp only [cellOrbitValues, cellBaseValues, hm, ite_false, id_eq]
      · cases ha : s.aux i p <;> simp_all [cellOrbitValues, cellBaseValues, cellOrbitRhs,
          auxDrain, protectedReadyRate] <;> ring
  | z p => exact hasDerivAt_const _ _
  | b => exact hasDerivAt_const _ _
  | energy =>
    exact ((relax_derivative 10 100 (s.x i .energy) s.time t).sub
      (linearConvolution_derivative (cellSmoothWork_continuous s i) 10 s.time t)).congr_deriv
        (by dsimp [cellOrbitValues, cellOrbitRhs]; ring)

/-- A threshold germ must actually exceed one immediately to the right. A
vanishing derivative is allowed; positivity is only a sufficient criterion. -/
def CellRightCrossing {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (c : Coord) : Prop :=
  ∃ germ : CellOrbitGerm θ s i, ∀ᶠ t in 𝓝[>] s.time, 1 < germ.path t i c

def Jump.CrossingRight {n route s u} (θ : Fin n → Parameters) : @Jump n route s u → Prop
  | .fire _ i _ _ => CellRightCrossing θ s i .q
  | .mark _ i p _ _ => CellRightCrossing θ s i (.m p)
  | _ => True

theorem CellOrbitGerm.crossing_of_positive_field {n θ s i} (germ : @CellOrbitGerm n θ s i)
    (c : Coord) (threshold : s.x i c = 1) (positive : 0 < field θ s s.x s.time i c) :
    ∀ᶠ t in 𝓝[>] s.time, 1 < germ.path t i c := by
  have hi : ∀ c, germ.path s.time i c = s.x i c := congrFun germ.initial
  have hd := germ.derivative s.time ⟨le_rfl, by linarith [germ.positive]⟩ c
  have hlocal : field θ s (germ.path s.time) s.time i c = field θ s s.x s.time i c := by
    cases c with
    | q => cases s.main i <;> simp [field, drive, hi]
    | m p => simp [field, auxDrain, hi]
    | z p => simp [field, errorAct, hi]
    | b => simp [field, markAct, hi]
    | energy => simp [field, work, drive, errorAct, markAct, auxDrain, hi]
  rw [hlocal] at hd
  have hl : Tendsto (slope (fun t => germ.path t i c) s.time) (𝓝[>] s.time)
      (𝓝 (field θ s s.x s.time i c)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s.time)).mp
      hd.hasDerivWithinAt.Ioi_of_Ici
  have hp := hl.eventually (Ioi_mem_nhds positive)
  filter_upwards [hp, self_mem_nhdsWithin] with t ht htime
  have hs : 0 < (germ.path t i c - germ.path s.time i c) / (t - s.time) := by
    simpa only [slope_def_field] using ht
  have hv : germ.path s.time i c < germ.path t i c := by
    have := (div_pos_iff_of_pos_right (sub_pos.mpr htime)).mp hs
    linarith
  simpa only [hi, threshold] using hv

end KernelR.Hybrid
