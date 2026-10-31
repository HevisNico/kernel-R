import KernelR.HybridReady
import KernelR.HybridWork

/-! Existence of active fixed-mode flows when the physical mode gates suppress
plasticity. Currents keep their actual origins; the energy solution integrates
the actual work instead of assuming a reserve trajectory. Guard and calendar
inequalities are explicit inputs for assembling a complete learned pulse cycle. -/
namespace KernelR.Hybrid
open MeasureTheory Set

def FrozenModes {n} (s : Snapshot n) : Prop :=
  (∀ i p, s.main i = .ready → s.aux i p ≠ .error) ∧
    ∀ i p, s.aux i p = .mark → s.main i = .ready

theorem FrozenModes.error_zero {n θ s} (h : @FrozenModes n s) (x : Values n)
    (i : Fin n) (p : Port) : errorAct θ s x i p = 0 := by
  unfold errorAct
  split_ifs with hg
  · exact False.elim (h.1 i p hg.2.1 hg.1)
  · rfl

theorem FrozenModes.mark_zero {n θ s} (h : @FrozenModes n s) (x : Values n)
    (i : Fin n) (p : Port) : markAct θ s x i p = 0 := by
  unfold markAct
  split_ifs with hg
  · exact False.elim (hg.2.1 (h.2 i p hg.1))
  · rfl

noncomputable def extendedCurrent {n} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  match s.raw i p with
  | none => 0
  | some origin => a * Real.exp (-a*(t-origin))

noncomputable def rawAmplitude {n} (s : Snapshot n) (i : Fin n) (p : Port) : ℝ :=
  match s.raw i p with
  | none => 0
  | some origin => Real.exp (-a*(s.time-origin))

@[fun_prop] theorem extendedCurrent_continuous {n} (s : Snapshot n) (i : Fin n) (p : Port) :
    Continuous (extendedCurrent s i p) := by
  change Continuous (fun t => extendedCurrent s i p t)
  cases hr : s.raw i p <;> simp only [extendedCurrent, hr] <;> fun_prop

theorem extendedCurrent_factor {n} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    extendedCurrent s i p t = rawAmplitude s i p * a * Real.exp (-a*(t-s.time)) := by
  cases hr : s.raw i p with
  | none => simp [extendedCurrent, rawAmplitude, hr]
  | some origin =>
    have he : Real.exp (-a*(t-origin)) =
        Real.exp (-a*(s.time-origin)) * Real.exp (-a*(t-s.time)) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [extendedCurrent, rawAmplitude, hr]
    rw [he]
    ring

noncomputable def extendedWork {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (i : Fin n) (t : ℝ) : ℝ :=
  (match s.main i with
    | .ready => ∑ p : Port, Real.exp (x i (.z p)) * extendedCurrent s i p t
    | .fast => a * x i .q
    | .slow => 11/10) +
  ∑ p : Port, if s.aux i p = .ready then (θ i).inputGain p * extendedCurrent s i p t
    else auxDrain (θ i) (s.aux i p) p (x i (.m p))

noncomputable def extendedField {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (t : ℝ) (i : Fin n) : Coord → ℝ
  | .q => match s.main i with
    | .ready => (1/2)*(1/10-x i .q) +
      ∑ p : Port, Real.exp (x i (.z p)) * extendedCurrent s i p t
    | .fast => -a * x i .q
    | .slow => -x i .b * x i .q
  | .m p => if s.aux i p = .ready then
      (1/2)*(1/40-x i (.m p)) + (θ i).inputGain p * extendedCurrent s i p t
    else -auxDrain (θ i) (s.aux i p) p (x i (.m p))
  | .z _ => 0
  | .b => 0
  | .energy => 10*(100-x i .energy) - extendedWork θ s x i t

noncomputable def mainAmplitude {n} (s : Snapshot n) (i : Fin n) : ℝ :=
  ∑ p : Port, Real.exp (s.x i (.z p)) * rawAmplitude s i p

noncomputable def frozenMain {n} (s : Snapshot n) (i : Fin n) (t : ℝ) : ℝ :=
  match s.main i with
  | .ready => readyPulse (s.x i .q) (mainAmplitude s i) s.time t
  | .fast => s.x i .q * Real.exp (-a*(t-s.time))
  | .slow => s.x i .q * Real.exp (-s.x i .b*(t-s.time))

noncomputable def frozenAux {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  if s.aux i p = .ready then
    auxPulse (s.x i (.m p)) ((θ i).inputGain p * rawAmplitude s i p) s.time t
  else s.x i (.m p) * Real.exp (-auxRate (θ i) p (s.aux i p)*(t-s.time))

noncomputable def frozenBody {n} (θ : Fin n → Parameters) (s : Snapshot n) (t : ℝ) : Values n :=
  fun i c => match c with
    | .q => frozenMain s i t
    | .m p => frozenAux θ s i p t
    | _ => s.x i c

theorem frozenBody_continuous {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (c : Coord) : Continuous (fun t => frozenBody θ s t i c) := by
  cases c with
  | q => cases hm : s.main i <;> simp [frozenBody, frozenMain, hm, readyPulse, response] <;> fun_prop
  | m p => simp only [frozenBody, frozenAux]; split_ifs <;>
      simp [auxPulse, readyPulse, response] <;> fun_prop
  | z p => exact continuous_const
  | b => exact continuous_const
  | energy => exact continuous_const

theorem extendedWork_continuous {n} (θ : Fin n → Parameters) (s : Snapshot n)
    {x : ℝ → Values n} (hx : ∀ i c, Continuous (fun t => x t i c)) (i : Fin n) :
    Continuous (fun t => extendedWork θ s (x t) i t) := by
  have haux (p : Port) : Continuous (fun t =>
      if s.aux i p = .ready then (θ i).inputGain p * extendedCurrent s i p t
      else auxDrain (θ i) (s.aux i p) p (x t i (.m p))) := by
    split_ifs
    · exact (extendedCurrent_continuous s i p).const_mul _
    · cases s.aux i p <;> simp [auxDrain] <;> fun_prop
  cases hm : s.main i <;> simp only [extendedWork, hm] <;> fun_prop

noncomputable def forcedReserve (initial start : ℝ) (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  100 + (initial-100)*Real.exp (-10*(t-start)) -
    Real.exp (-10*t) * ∫ v in start..t, Real.exp (10*v)*W v

theorem forcedReserve_initial (initial start : ℝ) (W : ℝ → ℝ) :
    forcedReserve initial start W start = initial := by simp [forcedReserve]

theorem forcedReserve_derivative (initial start : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (t : ℝ) :
    HasDerivAt (forcedReserve initial start W) (10*(100-forcedReserve initial start W t)-W t) t := by
  have hc : Continuous (fun v => Real.exp (10*v)*W v) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable start t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he := (((hasDerivAt_id t).const_mul (-10:ℝ)).exp)
  have hd := (((((hasDerivAt_id t).sub_const start).const_mul (-10:ℝ)).exp).const_mul
    (initial-100)).const_add 100
  have hcancel : Real.exp (-10*t) * Real.exp (10*t) = 1 := by
    rw [← Real.exp_add, show -10*t+10*t = 0 by ring, Real.exp_zero]
  have hwork := congrArg (fun z => z*W t) hcancel
  convert hd.sub (he.mul hi) using 1
  · rfl
  · dsimp [forcedReserve]
    nlinarith [hwork]

noncomputable def frozenValues {n} (θ : Fin n → Parameters) (s : Snapshot n) (t : ℝ) : Values n :=
  fun i c => match c with
    | .energy => forcedReserve (s.x i .energy) s.time
      (fun v => extendedWork θ s (frozenBody θ s v) i v) t
    | _ => frozenBody θ s t i c

noncomputable def frozenAt {n} (θ : Fin n → Parameters) (s : Snapshot n) (t : ℝ) : Snapshot n :=
  { s with time := t, x := frozenValues θ s t }

theorem frozenValues_initial {n} (θ : Fin n → Parameters) (s : Snapshot n) :
    frozenValues θ s s.time = s.x := by
  funext i c
  cases c with
  | q => cases hm : s.main i <;> simp [frozenValues, frozenBody, frozenMain, hm, readyPulse_initial]
  | m p => simp [frozenValues, frozenBody, frozenAux, auxPulse_initial]
  | z p => rfl
  | b => rfl
  | energy => exact forcedReserve_initial _ _ _

theorem frozenValues_continuous {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (c : Coord) : Continuous (fun t => frozenValues θ s t i c) := by
  cases c with
  | energy =>
    exact continuous_iff_continuousAt.mpr (fun t =>
      (forcedReserve_derivative _ _ (extendedWork_continuous θ s (frozenBody_continuous θ s) i) t).continuousAt)
  | q => exact frozenBody_continuous θ s i .q
  | m p => exact frozenBody_continuous θ s i (.m p)
  | z p => exact continuous_const
  | b => exact continuous_const

theorem frozenValues_derivative {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (c : Coord) (t : ℝ) :
    HasDerivAt (fun v => frozenValues θ s v i c) (extendedField θ s (frozenValues θ s t) t i c) t := by
  have hdrive : (∑ p : Port, Real.exp (s.x i (.z p)) * extendedCurrent s i p t) =
      mainAmplitude s i * a * Real.exp (-a*(t-s.time)) := by
    simp_rw [extendedCurrent_factor]
    simp only [mainAmplitude, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring
  cases c with
  | q =>
    cases hm : s.main i with
    | ready =>
      simpa only [frozenValues, frozenBody, frozenMain, hm, extendedField, hdrive]
        using readyPulse_derivative (s.x i .q) (mainAmplitude s i) s.time t
    | fast | slow =>
      have hd := (((((hasDerivAt_id t).sub_const s.time).const_mul
        (if s.main i = .fast then -a else -s.x i .b)).exp).const_mul (s.x i .q))
      convert hd using 1 <;> simp [frozenValues, frozenBody, frozenMain, extendedField, hm]
      all_goals ring
  | m p =>
    by_cases hm : s.aux i p = .ready
    · simpa only [frozenValues, frozenBody, frozenAux, hm, ite_true, extendedField,
        extendedCurrent_factor, mul_assoc]
        using auxPulse_derivative (s.x i (.m p)) ((θ i).inputGain p*rawAmplitude s i p) s.time t
    · have hd := (((((hasDerivAt_id t).sub_const s.time).const_mul
        (-auxRate (θ i) p (s.aux i p))).exp).const_mul (s.x i (.m p)))
      convert hd using 1
      · simp [frozenValues, frozenBody, frozenAux, hm]
      · cases ha : s.aux i p <;> simp_all [frozenValues, frozenBody, frozenAux, extendedField,
          auxDrain, auxRate] <;> ring
  | z p => simpa [frozenValues, frozenBody, extendedField] using hasDerivAt_const t (s.x i (.z p))
  | b => simpa [frozenValues, frozenBody, extendedField] using hasDerivAt_const t (s.x i .b)
  | energy =>
    exact forcedReserve_derivative _ _ (extendedWork_continuous θ s (frozenBody_continuous θ s) i) t

theorem extendedField_continuous {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (c : Coord) :
    Continuous (fun t => extendedField θ s (frozenValues θ s t) t i c) := by
  have hx := frozenValues_continuous θ s
  have hw := extendedWork_continuous θ s hx i
  cases c with
  | q => cases hm : s.main i <;> simp only [extendedField, hm] <;> fun_prop
  | m p =>
    simp only [extendedField]
    split_ifs
    · fun_prop
    · cases s.aux i p <;> simp only [auxDrain] <;> fun_prop
  | z p => exact continuous_const
  | b => exact continuous_const
  | energy => exact (continuous_const.sub (hx i .energy)).const_mul 10 |>.sub hw

theorem extendedField_eq_field {n θ s} (h : @FrozenModes n s) (x : Values n) (t : ℝ)
    (hraw : ∀ i p, extendedCurrent s i p t = current s i p t) (i : Fin n) (c : Coord) :
    extendedField θ s x t i c = field θ s x t i c := by
  cases c <;> simp [extendedField, field, extendedWork, work, drive,
    h.error_zero x, h.mark_zero x, hraw]
  all_goals cases hm : s.main i <;> rfl

/-- An actual active-mode flow is constructed from closed-form charges and a
forced reserve solution. Only first-guard and raw/calendar bounds remain inputs. -/
noncomputable def frozenFlow {n θ s} (h : @FrozenModes n s) {T : ℝ}
    (hT : s.time < T)
    (hguard : ∀ t ∈ Ico s.time T, BeforeGuards s (frozenValues θ s t))
    (hraw : ∀ i p origin, s.raw i p = some origin → origin ≤ s.time ∧ T ≤ origin+1)
    (hpending : ∀ d ∈ s.pending, T ≤ d.due) : Flow θ s (frozenAt θ s T) := by
  have heq (t : ℝ) (ht : t ∈ Ico s.time T) (i : Fin n) (c : Coord) :
      extendedField θ s (frozenValues θ s t) t i c = field θ s (frozenValues θ s t) t i c := by
    apply extendedField_eq_field h
    intro j p
    cases hr : s.raw j p with
    | none => simp [extendedCurrent, current, hr]
    | some origin =>
      have hb := hraw j p origin hr
      have hs : origin ≤ t ∧ t < origin+1 := ⟨hb.1.trans ht.1, ht.2.trans_le hb.2⟩
      simp [extendedCurrent, current, pulse, hr, hs]
  refine {
    positive := hT
    path := frozenValues θ s
    initial := frozenValues_initial θ s
    final := rfl
    main_fixed := rfl
    aux_fixed := rfl
    raw_fixed := rfl
    queue_fixed := rfl
    continuous := fun i c => (frozenValues_continuous θ s i c).continuousOn
    integrable := ?_
    mark_integrable := ?_
    integral_eq := ?_
    guards := hguard
    raw_support := hraw
    pending_urgent := hpending }
  · intro i c
    apply (extendedField_continuous θ s i c).intervalIntegrable s.time T |>.congr_uIoo
    intro t ht
    rw [uIoo_of_le hT.le] at ht
    exact heq t ⟨ht.1.le, ht.2⟩ i c
  · intro i p
    change IntervalIntegrable (fun t => markAct θ s (frozenValues θ s t) i p) volume s.time T
    simpa only [h.mark_zero] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume s.time T)
  · intro t ht i c
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => frozenValues_derivative θ s i c v)
      ((extendedField_continuous θ s i c).intervalIntegrable s.time t)
    have hc : (∫ v in s.time..t, extendedField θ s (frozenValues θ s v) v i c) =
        ∫ v in s.time..t, field θ s (frozenValues θ s v) v i c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact heq v ⟨hv.1.le, hv.2.trans_le ht.2⟩ i c
    rw [frozenValues_initial, hc] at hftc
    linarith

end KernelR.Hybrid
