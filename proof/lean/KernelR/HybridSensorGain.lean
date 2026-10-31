import KernelR.HybridExecutionTools
import KernelR.HybridSensor

/-! Gain speed during clipped ERROR and gain freezing before the actual sensor ERROR phase. -/
namespace KernelR.Hybrid
open Set MeasureTheory

theorem Flow.error_gain_speed {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.aux i p = .error) (M : ℝ)
    (hx : s.x i (.m p) ≤ M) (hM : 0 ≤ M) :
    u.x i (.z p) ≤ s.x i (.z p) + 8 * (θ i).le p * M * (u.time - s.time) ∧
      u.x i (.m p) ≤ M := by
  have hr := (hb.rates_positive i p).2.2
  have hmBound : ∀ t ∈ Icc s.time u.time, f.path t i (.m p) ≤ M := by
    intro t ht
    have he := f.aux_decay_solution i p (by simp [hm]) t ht
    simp only [hm] at he
    rw [he]
    exact decay_upper hx hM hr.le (sub_nonneg.mpr ht.1)
  have hrate : 0 ≤ 8 * (θ i).le p := mul_nonneg (by norm_num) hr.le
  have hI : (∫ t in s.time..u.time, field θ s (f.path t) t i (.z p)) ≤
      ∫ _t in s.time..u.time, 8 * (θ i).le p * M := by
    apply intervalIntegral.integral_mono_on f.positive.le (f.integrable i (.z p)) intervalIntegrable_const
    intro t ht
    exact (f.error_act_upper hb i p hm t ht).trans (mul_le_mul_of_nonneg_left (hmBound t ht) hrate)
  have hz := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.z p)
  rw [f.final] at hz
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hI
  refine ⟨by nlinarith, ?_⟩
  simpa only [f.final] using hmBound u.time ⟨f.positive.le, le_rfl⟩

theorem Flow.error_gain_speed_on {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.aux i p = .error) (M : ℝ)
    (hx : s.x i (.m p) ≤ M) (hM : 0 ≤ M) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i (.z p) ≤ s.x i (.z p) + 8 * (θ i).le p * M * (t - s.time) := by
  intro t ht
  rcases ht.1.eq_or_lt with heq | hlt
  · simp [← heq, f.initial]
  · exact ((f.prefix hlt ht.2).error_gain_speed hb i p hm M hx hM).1

theorem Execution.error_gain_speed {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hm : e.AuxFlows i p .error)
    (M : ℝ) (hx : s.x i (.m p) ≤ M) (hM : 0 ≤ M) :
    u.x i (.z p) ≤ s.x i (.z p) + 8 * (θ i).le p * M * (u.time - s.time) ∧
      u.x i (.m p) ≤ M := by
  induction e with
  | nil => exact ⟨by simp, hx⟩
  | cons step rest ih => cases step with
    | flow f =>
      have hf := f.error_gain_speed hb i p hm.1 M hx hM
      have ht := ih hm.2 hf.2
      exact ⟨by linarith, ht.2⟩
    | jump j =>
      have h := ih hm (by simpa only [j.physical_continuous] using hx)
      simpa only [j.physical_continuous, j.time_unchanged] using h

theorem Execution.error_gain_flow_bounds {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hm : e.AuxFlows i p .error)
    (M : ℝ) (hx : s.x i (.m p) ≤ M) (hM : 0 ≤ M) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time,
      f.path t i (.z p) ≤ s.x i (.z p) + 8 * (θ i).le p * M * (t - s.time)) := by
  induction e with
  | nil => trivial
  | @cons s v u step rest ih => cases step with
    | flow f =>
      refine ⟨f.error_gain_speed_on hb i p hm.1 M hx hM, ?_⟩
      have hf := f.error_gain_speed hb i p hm.1 M hx hM
      have h := ih hm.2 hf.2
      exact rest.allFlows_mono (fun g hg t ht => by
        have hh := hg t ht
        linarith) h
    | jump j =>
      have h := ih hm (by simpa only [j.physical_continuous] using hx)
      simpa only [AllFlows, j.physical_continuous, j.time_unchanged] using h

theorem Execution.gain_constant_aux {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (hne : mode ≠ .error)
    (hm : e.AuxFlows i p mode) :
    u.x i (.z p) = s.x i (.z p) ∧
    e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i (.z p) = s.x i (.z p)) := by
  induction e with
  | nil => exact ⟨rfl, trivial⟩
  | cons move rest ih => cases move with
    | flow f =>
      have hf := f.gain_constant_without_error i p (by rw [hm.1]; exact hne)
      have hend := hf _ ⟨f.positive.le, le_rfl⟩
      rw [f.final] at hend
      have hrest := ih hm.2
      refine ⟨hrest.1.trans hend, hf, ?_⟩
      simpa only [hend] using hrest.2
    | jump j => simpa only [AllFlows, j.physical_continuous] using ih hm

/-- During the raw window the late ERROR phase can add at most 0.088 to
the logarithmic gain. The actual sensor cycle and all flow cuts are retained. -/
theorem SensorCycle.gain_during_raw {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, t ≤ s.time + 1 →
      f.path t i (.z p) ≤ s.x i (.z p) + 11 / 125) := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  have htr := tr.span.gain_constant_aux i p .ready (by decide) tr.flows
  have hmk := mk.span.gain_constant_aux i p .mark (by decide) mk.flows
  have hsi := si.span.gain_constant_aux i p .silent (by decide) si.flows
  have hzmk : tr.afterMark.x i (.z p) = s.x i (.z p) := by
    rw [tr.entry.physical_continuous]; exact htr.1
  have hzsi : mk.afterExit.x i (.z p) = s.x i (.z p) := by
    rw [mk.exit.physical_continuous, hmk.1, hzmk]
  have hzer : si.afterExit.x i (.z p) = s.x i (.z p) := by
    rw [si.exit.physical_continuous, hsi.1, hzsi]
  have her := er.span.error_gain_flow_bounds hb i p er.flows (1 / 10)
    (by change si.afterExit.x i (.m p) ≤ 1 / 10; rw [si.after_charge]; norm_num [protectedFloor]) (by norm_num)
  have heTime := er.span.allFlows_time_bounds
  have hrest := er.rest.allFlows_time_bounds
  let P : ∀ {v w : Snapshot n}, Flow θ v w → Prop := fun {v w} f =>
    ∀ t ∈ Icc v.time w.time, t ≤ s.time + 1 → f.path t i (.z p) ≤ s.x i (.z p) + 11 / 125
  have hPTr : tr.span.AllFlows P := tr.span.allFlows_mono (fun f hf t ht _ => by rw [hf t ht]; norm_num) htr.2
  have hPMk : mk.span.AllFlows P := mk.span.allFlows_mono (fun f hf t ht _ => by rw [hf t ht, hzmk]; norm_num) hmk.2
  have hPSi : si.span.AllFlows P := si.span.allFlows_mono (fun f hf t ht _ => by rw [hf t ht, hzsi]; norm_num) hsi.2
  have hPEr : er.span.AllFlows P := by
    have hboth := er.span.allFlows_and her heTime
    refine er.span.allFlows_mono ?_ hboth
    intro v w f hf t ht hu
    have h := hf.1 t ht
    have hd : 0 ≤ t - si.afterExit.time := sub_nonneg.mpr (hf.2 t ht).1
    have hdu : t - si.afterExit.time ≤ 1 / 100 := by linarith [cycle.error_starts_late]
    have hrate := (hb.coarse_upper i p).2.2.2.1
    have hrpos := (hb.rates_positive i p).2.2
    have hc : 8 * (θ i).le p * (1 / 10) * (t - si.afterExit.time) ≤ 11 / 125 := by
      calc
        _ ≤ 8 * 11 * (1 / 10) * (t - si.afterExit.time) := by nlinarith
        _ ≤ _ := by linarith
    rw [hzer] at h
    linarith
  have hPRest : er.rest.AllFlows P := er.rest.allFlows_mono (fun f hf t ht hu => by
    exact False.elim (by have h := (hf t ht).1; linarith [cycle.ready_after_raw])) hrest
  rw [tr.reconstruct, Execution.allFlows_append]
  refine ⟨hPTr, ?_⟩
  change tr.rest.AllFlows P
  rw [mk.reconstruct, Execution.allFlows_append]
  refine ⟨hPMk, ?_⟩
  change mk.rest.AllFlows P
  rw [si.reconstruct, Execution.allFlows_append]
  refine ⟨hPSi, ?_⟩
  change si.rest.AllFlows P
  rw [er.reconstruct, Execution.allFlows_append]
  exact ⟨hPEr, hPRest⟩

/-- Gain freezing before ERROR is extracted from the actual sensor cycle,
including arbitrary simultaneous jumps. -/
theorem SensorCycle.gain_before_error {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, t ≤ s.time + 99 / 100 →
      f.path t i (.z p) = s.x i (.z p)) := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  have htr := tr.span.gain_constant_aux i p .ready (by decide) tr.flows
  have hmk := mk.span.gain_constant_aux i p .mark (by decide) mk.flows
  have hsi := si.span.gain_constant_aux i p .silent (by decide) si.flows
  have hzmk : tr.afterMark.x i (.z p) = s.x i (.z p) := by
    rw [tr.entry.physical_continuous]; exact htr.1
  have hzsi : mk.afterExit.x i (.z p) = s.x i (.z p) := by
    rw [mk.exit.physical_continuous, hmk.1, hzmk]
  let P : ∀ {v w : Snapshot n}, Flow θ v w → Prop := fun {v w} f =>
    ∀ t ∈ Icc v.time w.time, t ≤ s.time + 99 / 100 → f.path t i (.z p) = s.x i (.z p)
  have hPTr : tr.span.AllFlows P := tr.span.allFlows_mono (fun f hf t ht _ => hf t ht) htr.2
  have hPMk : mk.span.AllFlows P := mk.span.allFlows_mono (fun f hf t ht _ => by rw [hf t ht,hzmk]) hmk.2
  have hPSi : si.span.AllFlows P := si.span.allFlows_mono (fun f hf t ht _ => by rw [hf t ht,hzsi]) hsi.2
  have hPRest : si.rest.AllFlows P := si.rest.allFlows_mono (fun f hf t ht hu => by
    exact False.elim (by have h := (hf t ht).1; linarith [cycle.error_starts_late])) si.rest.allFlows_time_bounds
  rw [tr.reconstruct, Execution.allFlows_append]
  refine ⟨hPTr, ?_⟩
  change tr.rest.AllFlows P
  rw [mk.reconstruct, Execution.allFlows_append]
  refine ⟨hPMk, ?_⟩
  change mk.rest.AllFlows P
  rw [si.reconstruct, Execution.allFlows_append]
  exact ⟨hPSi,hPRest⟩

theorem Execution.gain_flow_lower {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, s.x i (.z p) ≤ f.path t i (.z p)) := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f =>
      refine ⟨f.gain_nondecreasing hb i p, ?_⟩
      have hf := f.gain_nondecreasing hb i p _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hf
      exact rest.allFlows_mono (fun g hg t ht => hf.trans (hg t ht)) ih
    | jump j => simpa only [AllFlows,j.physical_continuous] using ih

end KernelR.Hybrid
