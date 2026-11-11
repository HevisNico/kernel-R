import ParameterTraining
import StopLearningLatency

/-! A training pulse that leaves the cell silent, in the regime where the
ERROR entry threshold is low enough for the write to start after the pulse
has ended. The construction starts from any rested state and uses the
realized thresholds of the cell. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- A SILENT leg under a main-charge margin. The gain of the pulsed port is
bounded by the gain cap only. -/
theorem silent_leg_of_margin {θ ε s p origin upper level stop}
    (box : @PhysicalBox 1 θ ε)
    (positive : s.time < stop)
    (main : ∀ i, s.main i = .ready) (mode : s.aux 0 p = .silent)
    (other : ∀ i q, i ≠ 0 ∨ q ≠ p → s.aux i q = .ready)
    (rest : ∀ q ≠ p, s.x 0 (.m q) ∈ Icc (0 : ℝ) (1 / 2))
    (raw : s.raw 0 p = origin) (otherRaw : ∀ i q, i ≠ 0 ∨ q ≠ p → s.raw i q = none)
    (support : ∀ o, origin = some o → o ≤ s.time ∧ stop ≤ o + 1)
    (pending : ∀ d ∈ s.pending, stop ≤ d.due)
    (charge : ∀ t ∈ Icc s.time stop,
      readyProtectedValues θ s 0 p .silent origin t 0 .q < level)
    (sensor : ∀ t ∈ Ico s.time stop,
      upper < readyProtectedValues θ s 0 p .silent origin t 0 (.m p))
    (sensorIn : s.x 0 (.m p) ∈ Icc 0 (4 / 5))
    (gain : Real.exp (s.x 0 (.z p)) ≤ 22 / 5)
    (energy : 50 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100) :
    Nonempty (TrainingSilentLeg θ s p origin upper level stop) := by
  let path := readyProtectedValues θ s 0 p .silent origin
  have fieldEq (t : ℝ) (ht : t ∈ Ico s.time stop) (i : Fin 1) (c : Coord) :
      field θ s (path t) t i c = readyProtectedRhs θ s 0 p .silent origin t i c :=
    readyProtected_field s 0 p .silent origin (Or.inr rfl) main mode other raw otherRaw t ht.1
      (fun o h => ⟨(support o h).1, ht.2.trans_le (support o h).2⟩) i c
  have qbound (t : ℝ) (ht : t ∈ Ico s.time stop) : path t 0 .q < level :=
    charge t ⟨ht.1, ht.2.le⟩
  have mbound (t : ℝ) (ht : s.time ≤ t) (q : Port) (hq : q ≠ p) : path t 0 (.m q) < 1 := by
    have band := relax_mem_band (rate := 1 / 2) (target := 1 / 40) (start := s.time) (t := t)
      (by norm_num) ht (rest q hq) ⟨by norm_num, by norm_num⟩
    have value : path t 0 (.m q) = relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t := by
      simp [path, readyProtectedValues, hq]
    rw [value]
    linarith [band.2]
  refine ⟨⟨positive, main, mode, fun q h => other 0 q (Or.inr h), raw, otherRaw,
    ?_, ?_, ?_, qbound, sensor, fun t ht => mbound t ht.1, support, pending, ?_, ?_⟩⟩
  · intro i c
    exact (continuous_iff_continuousAt.mpr fun t =>
      (readyProtectedValues_derivative (θ := θ) s 0 p .silent origin t i c).continuousAt).continuousOn
  · intro i c
    have hc := readyProtectedRhs_continuous (θ := θ) s 0 p .silent origin i c
    apply (hc.intervalIntegrable s.time stop).congr_uIoo
    intro t ht
    rw [uIoo_of_lt positive] at ht
    exact (fieldEq t ⟨ht.1.le, ht.2⟩ i c).symm
  · intro t ht i c
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => readyProtectedValues_derivative (θ := θ) s 0 p .silent origin v i c)
      ((readyProtectedRhs_continuous (θ := θ) s 0 p .silent origin i c).intervalIntegrable s.time t)
    rw [readyProtectedValues_initial] at h
    have eq : (∫ v in s.time..t, field θ s (path v) v i c) =
        ∫ v in s.time..t, readyProtectedRhs θ s 0 p .silent origin v i c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact fieldEq v ⟨hv.1.le, hv.2.trans_le ht.2⟩ i c
    rw [eq, h]
    change path t i c = _
    ring
  · intro hu hl
    have startCharge : s.x 0 .q < 1 := by
      have h := charge s.time ⟨le_rfl, positive.le⟩
      rw [show readyProtectedValues θ s 0 p .silent origin s.time 0 .q = s.x 0 .q from
        congrFun (congrFun (readyProtectedValues_initial (θ := θ) s 0 p .silent origin) 0) .q,
        hl] at h
      exact h
    exact readyProtectedFlow s 0 p .silent origin positive (Or.inr rfl) main mode other raw otherRaw support
      (fun i => by rw [Subsingleton.elim i 0]; exact startCharge)
      (fun i q h => by
        rw [Subsingleton.elim i 0]
        linarith [(rest q (h.resolve_left (not_not_intro (Subsingleton.elim i 0)))).2])
      (fun t ht => by
        simpa only [path, readyProtectedValues, protectedRawAmplitude, ite_true, hl] using qbound t ht)
      (fun t ht => by
        simpa only [readyProtectedValues, and_self, ite_true, protectedReadyRate, reduceCtorEq,
          ite_false, hu] using sensor t ht) pending
  · let A := protectedRawAmplitude s 0 p origin 0
    let r := (θ 0).ls p
    let W := fun t => A * a * Real.exp (-a * (t - s.time)) +
      r * s.x 0 (.m p) * Real.exp (-r * (t - s.time))
    apply reserve_of_derivative positive.le (show Continuous W by dsimp [W]; fun_prop)
      (energy := fun t => path t 0 .energy)
    · intro t
      simpa [path, W, A, r, readyProtectedRhs, protectedAuxCoeff, protectedReadyRate, sub_sub] using
        readyProtectedValues_derivative (θ := θ) s 0 p .silent origin t 0 .energy
    · rw [show path s.time = s.x from readyProtectedValues_initial _ _ _ _ _]
      exact energy
    · intro t ht
      have aPos : 0 ≤ a := by linarith [a_coarse_bounds.1]
      have rp := (box.rates_positive 0 p).2.1
      have rawBound : rawInputScale origin s.time ≤ 1 := by
        cases origin with
        | none => norm_num [rawInputScale]
        | some o =>
          exact Real.exp_le_one_iff.mpr
            (by nlinarith [mul_nonneg aPos (sub_nonneg.mpr (support o rfl).1)])
      have ARange : 0 ≤ A ∧ A ≤ 22 / 5 := by
        change 0 ≤ (if (0 : Fin 1) = 0 then _ else _) ∧ (if (0 : Fin 1) = 0 then _ else _) ≤ _
        simp only [ite_true]
        exact ⟨mul_nonneg (Real.exp_pos _).le (rawInputScale_nonnegative _ _),
          by simpa using mul_le_mul gain rawBound (rawInputScale_nonnegative _ _) (by norm_num)⟩
      have h₁ := decay_upper (mul_le_mul ARange.2 a_coarse_bounds.2.le aPos
        (by norm_num : (0 : ℝ) ≤ 22 / 5)) (by norm_num) aPos (sub_nonneg.mpr ht.1)
      have h₂ := decay_upper (mul_le_mul (box.coarse_upper 0 p).2.2.1 sensorIn.2 sensorIn.1
        (by norm_num : (0 : ℝ) ≤ 3)) (by norm_num) rp.le (sub_nonneg.mpr ht.1)
      dsimp [W]
      constructor
      · exact add_nonneg (mul_nonneg (mul_nonneg ARange.1 aPos) (Real.exp_pos _).le)
          (mul_nonneg (mul_nonneg rp.le sensorIn.1) (Real.exp_pos _).le)
      · linarith

end RecursiveLearning.Native
