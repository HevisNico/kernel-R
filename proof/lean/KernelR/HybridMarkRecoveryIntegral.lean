import KernelR.HybridProtectedReturn
import KernelR.Cadence

namespace KernelR.Hybrid
open Set MeasureTheory

/-- Conservation along an actual exposed MARK flow, with other ports excluded
only from MARK (they may still be SILENT or ERROR). -/
theorem Flow.isolated_mark_conservation {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (ho : MarkOpen f i p)
    (hq : ∀ q, q ≠ p → s.aux i q ≠ .mark) :
    u.x i .b + u.x i (.m p) / 2 = s.x i .b + s.x i (.m p) / 2 := by
  have hr := f.recovery_of_only_mark i p (fun t ht q hqp => by
    simp [markAct, hq q hqp])
  have hm := f.mark_charge_balance i p ho
  have hb := f.recovery_balance i
  rw [hr, hm] at hb
  linarith

/-- The recovery profile is deduced from the integral flow and sensor ODE. -/
theorem Flow.isolated_mark_profile {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (ho : MarkOpen f i p)
    (hq : ∀ q, q ≠ p → s.aux i q ≠ .mark) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i .b = s.x i .b + s.x i (.m p) / 2 *
        (1 - Real.exp (-(θ i).lm p * (t - s.time))) := by
  intro t ht
  by_cases hs : t = s.time
  · subst t; simp [f.initial]
  let hp := f.prefix (lt_of_le_of_ne ht.1 (Ne.symm hs)) ht.2
  have hop : MarkOpen hp i p := ⟨ho.1,ho.2.1,fun v hv => ho.2.2 v ⟨hv.1,hv.2.trans ht.2⟩⟩
  have hc := hp.isolated_mark_conservation i p hop hq
  have hm := f.aux_decay_solution i p (by simp [ho.1]) t ht
  simp only [ho.1] at hm
  change f.path t i .b + f.path t i (.m p) / 2 = _ at hc
  rw [hm] at hc
  linarith

/-- Integrating the actual recovery, including its finite MARK ramp. -/
theorem Flow.isolated_mark_accumulated {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (ho : MarkOpen f i p)
    (hq : ∀ q, q ≠ p → s.aux i q ≠ .mark) (hr : (θ i).lm p ≠ 0) :
    f.accumulatedRecovery i =
      (s.x i .b + s.x i (.m p) / 2) * (u.time - s.time) +
        (u.x i (.m p) - s.x i (.m p)) / (2 * (θ i).lm p) := by
  have hprofile : ∀ t ∈ Icc s.time u.time,
      f.path t i .b = (s.x i .b + s.x i (.m p) / 2) - f.path t i (.m p) / 2 := by
    intro t ht
    have hb := f.isolated_mark_profile i p ho hq t ht
    have hm := f.aux_decay_solution i p (by simp [ho.1]) t ht
    simp only [ho.1] at hm
    rw [hm]; linarith
  have he := f.integral_eq u.time ⟨f.positive.le,le_rfl⟩ i (.m p)
  simp only [f.final, field, ho.1, reduceCtorEq, ite_false, auxDrain] at he
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at he
  have hi : f.accumulatedRecovery i =
      (s.x i .b + s.x i (.m p) / 2) * (u.time - s.time) -
        (∫ t in s.time..u.time, f.path t i (.m p)) / 2 := by
    unfold Flow.accumulatedRecovery
    calc
      _ = ∫ t in s.time..u.time,
          (s.x i .b + s.x i (.m p) / 2) - f.path t i (.m p) / 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hprofile t (by simpa [uIcc_of_le f.positive.le] using ht)
      _ = _ := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          ((f.continuous i (.m p)).intervalIntegrable_of_Icc f.positive.le |>.div_const 2),
          intervalIntegral.integral_const, intervalIntegral.integral_div]
        simp [smul_eq_mul, mul_comm]
  rw [hi]
  field_simp
  nlinarith [he]

/-- One receiving port is the only possible MARK actuator during these pieces. -/
def Execution.OtherMarkClosed {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) : Prop :=
  e.AllFlows (fun {v _w} _ => ∀ q, q ≠ p → v.aux i q ≠ .mark)

theorem Execution.isolated_mark_conservation {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) (hq : e.OtherMarkClosed i p) :
    u.x i .b + u.x i (.m p) / 2 = s.x i .b + s.x i (.m p) / 2 := by
  induction e with
  | nil => rfl
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      exact (ih ho.2 hq.2).trans (f.isolated_mark_conservation i p ho.1 hq.1)
    | jump j => simpa only [j.physical_continuous] using ih ho hq

/-- This telescopes across every actual flow and legal zero-duration jump. -/
theorem Execution.isolated_mark_accumulated {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) (hq : e.OtherMarkClosed i p) (hr : (θ i).lm p ≠ 0) :
    e.accumulatedRecovery i =
      (s.x i .b + s.x i (.m p) / 2) * (u.time - s.time) +
        (u.x i (.m p) - s.x i (.m p)) / (2 * (θ i).lm p) := by
  induction e with
  | nil => simp [Execution.accumulatedRecovery]
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      change f.accumulatedRecovery i + rest.accumulatedRecovery i = _
      rw [f.isolated_mark_accumulated i p ho.1 hq.1 hr, ih ho.2 hq.2,
        f.isolated_mark_conservation i p ho.1 hq.1]
      ring
    | jump j =>
      change rest.accumulatedRecovery i = _
      simpa only [j.physical_continuous,j.time_unchanged] using ih ho hq

theorem Execution.full_isolated_mark_accumulated {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) (hq : e.OtherMarkClosed i p) (hr : (θ i).lm p ≠ 0)
    (hs : s.x i (.m p) = 1) (hu : u.x i (.m p) = 4 / 5) :
    e.accumulatedRecovery i =
      (s.x i .b + 1 / 2) * (u.time - s.time) - 1 / (10 * (θ i).lm p) := by
  rw [e.isolated_mark_accumulated i p ho hq hr,hs,hu]
  ring

theorem Execution.isolated_mark_aux_flows {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) : e.AuxFlows i p .mark := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨ho.1.1,ih ho.2⟩
    | jump j => exact ih ho

/-- The abstract exponential integral in Cadence is exactly the clock of the
observed MARK segment, not a surrogate instantaneous jump of recovery. -/
theorem Execution.full_isolated_mark_profile_integral {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) (hq : e.OtherMarkClosed i p) (hr : (θ i).lm p ≠ 0)
    (hs : s.x i (.m p) = 1) (hu : u.x i (.m p) = 4 / 5) :
    e.accumulatedRecovery i = ∫ t in (0 : ℝ)..(u.time - s.time),
      s.x i .b + (1 / 2 : ℝ) * (1 - Real.exp (-(θ i).lm p * t)) := by
  have he := e.aux_phase_solution i p .mark (by decide) (e.isolated_mark_aux_flows i p ho)
  simp only [auxRate,hs,hu,one_mul] at he
  rw [e.full_isolated_mark_accumulated i p ho hq hr hs hu,
    Cadence.mark_profile_integral _ hr,← he]
  ring

/-- The guarded sensor endpoints identify the actual MARK duration. -/
theorem Execution.full_isolated_mark_duration {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) (hr : (θ i).lm p ≠ 0)
    (hs : s.x i (.m p) = 1) (hu : u.x i (.m p) = 4 / 5) :
    u.time - s.time = Cadence.markDuration ((θ i).lm p) := by
  have he := e.aux_phase_solution i p .mark (by decide) (e.isolated_mark_aux_flows i p ho)
  simp only [auxRate,hs,hu] at he
  have hd := duration_of_decay (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 4 / 5) hr he
  simpa [Cadence.markDuration] using hd

/-- No MARK is assumed outside the selected real MARK phase. -/
def Execution.NoMarkFlows {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) : Prop :=
  e.AllFlows (fun {v _w} _ => ∀ q, v.aux i q ≠ .mark)

theorem Flow.recovery_without_mark {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (hq : ∀ q, s.aux i q ≠ .mark) :
    ∀ t ∈ Icc s.time u.time, f.path t i .b = s.x i .b := by
  have hg (v : ℝ) : field θ s (f.path v) v i .b = 0 := by
    simp only [field]
    apply Finset.sum_eq_zero
    intro q _
    simp [markAct,hq q]
  intro t ht
  simpa only [hg,intervalIntegral.integral_zero,add_zero] using f.integral_eq t ht i .b

theorem Execution.recovery_without_mark {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (hq : e.NoMarkFlows i) :
    u.x i .b = s.x i .b ∧
      e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b = s.x i .b) := by
  induction e with
  | nil => exact ⟨rfl,trivial⟩
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      have hp := f.recovery_without_mark i hq.1
      have hv := hp v.time ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hv
      have ht := ih hq.2
      exact ⟨ht.1.trans hv,⟨hp,by simpa only [hv] using ht.2⟩⟩
    | jump j =>
      simpa only [j.physical_continuous,Execution.AllFlows] using ih hq

/-- Pre-MARK, MARK, and post-MARK are genuine execution segments. The sensor
endpoints and exposure determine both the dose and the noninstantaneous clock. -/
theorem Execution.mark_recovery_accumulated {n θ route s a b u}
    (pre : @Execution n θ route s a) (mark : Execution θ route a b)
    (post : Execution θ route b u) (i : Fin n) (p : Port)
    (hpre : pre.NoMarkFlows i) (hmark : mark.MarkExposed i p)
    (hother : mark.OtherMarkClosed i p) (hpost : post.NoMarkFlows i)
    (hr : 0 < (θ i).lm p) (hs : a.x i (.m p) = 1) (hu : b.x i (.m p) = 4 / 5) :
    (pre.append (mark.append post)).accumulatedRecovery i =
      (s.x i .b + 1 / 10) * (u.time - s.time) -
        Cadence.markDeficit (a.time - s.time) ((θ i).lm p) := by
  have hp := pre.recovery_without_mark i hpre
  have ht := post.recovery_without_mark i hpost
  have hc := mark.isolated_mark_conservation i p hmark hother
  have hb : b.x i .b = s.x i .b + 1 / 10 := by
    rw [hs,hu,hp.1] at hc
    linarith
  rw [Execution.accumulatedRecovery_append,Execution.accumulatedRecovery_append,
    pre.accumulatedRecovery_of_constant i (s.x i .b) hp.2,
    mark.full_isolated_mark_accumulated i p hmark hother (ne_of_gt hr) hs hu,
    post.accumulatedRecovery_of_constant i (b.x i .b) ht.2,hp.1,hb]
  have hd := mark.full_isolated_mark_duration i p hmark (ne_of_gt hr) hs hu
  dsimp [Cadence.markDuration] at hd
  have hdate : b.time = a.time + Real.log (5 / 4) / (θ i).lm p := by linarith
  rw [hdate]
  dsimp [Cadence.markDeficit]
  field_simp
  ring

/-- Exact return date relative to the input, after the finite MARK ramp. `D`
is the elapsed SLOW time before that input; `J` is the derived MARK deficit. -/
theorem Execution.mark_recovery_slow_return {n θ route s input a b u}
    (before : @Execution n θ route s input) (pre : Execution θ route input a)
    (mark : Execution θ route a b) (post : Execution θ route b u)
    (i : Fin n) (p : Port)
    (hbefore : before.NoMarkFlows i) (hpre : pre.NoMarkFlows i)
    (hmark : mark.MarkExposed i p) (hother : mark.OtherMarkClosed i p)
    (hpost : post.NoMarkFlows i) (hr : 0 < (θ i).lm p)
    (hs : a.x i (.m p) = 1) (hu : b.x i (.m p) = 4 / 5)
    (hslow : (before.append (pre.append (mark.append post))).MainFlows i .slow)
    (hqstart : s.x i .q = 1 / 4) (hqend : u.x i .q = 1 / 10)
    (hb : s.x i .b + 1 / 10 ≠ 0) :
    u.time - input.time =
      (Real.log (5 / 2) - s.x i .b * (input.time - s.time) +
        Cadence.markDeficit (a.time - input.time) ((θ i).lm p)) / (s.x i .b + 1 / 10) := by
  have he := (before.append (pre.append (mark.append post))).slow_exit_accumulation
    i hslow hqstart hqend
  have hconst := before.recovery_without_mark i hbefore
  rw [Execution.accumulatedRecovery_append,
    before.accumulatedRecovery_of_constant i (s.x i .b) hconst.2,
    pre.mark_recovery_accumulated mark post i p hpre hmark hother hpost hr hs hu,
    hconst.1] at he
  apply (eq_div_iff hb).2
  linarith

/-- Application to the MARK selected by the real sensor cycle. Exposure is
proved from the invariant, main protection and cap headroom, rather than a dose. -/
theorem SensorCycle.mark_recovery_integral_of_invariant
    {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hm : cycle.phases.markPhase.span.AllStates (fun v => v.main i ≠ .ready))
    (hc : cycle.phases.markPhase.span.AllFlows (fun {v w} f =>
      ∀ t ∈ Icc v.time w.time, f.path t i .b < 11 / 10))
    (ho : cycle.phases.markPhase.span.OtherMarkClosed i p) :
    cycle.phases.markPhase.span.ledger.mark i p = 1 / 10 ∧
    cycle.phases.markPhase.beforeExit.x i .b = cycle.trigger.afterMark.x i .b + 1 / 10 ∧
    cycle.phases.markPhase.span.accumulatedRecovery i =
      (cycle.trigger.afterMark.x i .b + 1 / 2) *
        Cadence.markDuration ((θ i).lm p) - 1 / (10 * (θ i).lm p) := by
  let past := cycle.trigger.span.append (.cons (.jump cycle.trigger.entry) (.nil _))
  have hex := cycle.phases.markPhase.span.mark_exposed_of_invariant hb
    (past.physical_invariant hb hf) i p cycle.phases.markPhase.flows hm hc
  have hend : cycle.phases.markPhase.beforeExit.x i (.m p) = 4 / 5 := by
    simpa only [protectedFloor] using cycle.phases.markPhase.charge
  have hd := cycle.phases.markPhase.span.full_isolated_mark_duration i p hex
    (ne_of_gt (hb.rates_positive i p).1) cycle.trigger.charge hend
  have hacc := cycle.phases.markPhase.span.full_isolated_mark_accumulated i p hex ho
    (ne_of_gt (hb.rates_positive i p).1) cycle.trigger.charge hend
  have hcons := cycle.phases.markPhase.span.isolated_mark_conservation i p hex ho
  rw [cycle.trigger.charge,hend] at hcons
  refine ⟨cycle.phases.markPhase.span.full_mark_of_open_endpoints i p hex
    cycle.trigger.charge hend,by linarith,?_⟩
  simpa only [hd] using hacc

end KernelR.Hybrid
