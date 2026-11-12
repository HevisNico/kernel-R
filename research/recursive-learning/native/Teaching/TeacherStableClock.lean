import Teaching.TeacherReopen
import KernelR.HybridSlowMarkReturn

/-! Saturating recovery removes the MARK-dependent term from the SLOW
clock. The fixed self-delay can then be centred in the certified work window. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- A native execution cannot move recovery away from its upper cap. -/
theorem teacher_recovery_stays_at_cap {n θ ε route s u} (e : @Execution n θ route s u)
    (box : PhysicalBox θ ε) (i : Fin n) (cap : s.x i .b = 11 / 10) :
    u.x i .b = 11 / 10 :=
  le_antisymm (e.recovery_cap i cap.le) (cap.symm.le.trans (e.recovery_nondecreasing box i))

noncomputable def cappedTeacherPeriod : ℝ :=
  1 + Real.log (5 / 2) / (11 / 10)

noncomputable def cappedTeacherWorkOffset : ℝ :=
  cappedTeacherPeriod - 22313 / 40000

noncomputable def cappedTeacherWorkJitter : ℝ := 73 / 40000

theorem capped_teacher_period_bounds : (183 / 100 : ℝ) < cappedTeacherPeriod ∧
    cappedTeacherPeriod < 184 / 100 := by
  unfold cappedTeacherPeriod
  constructor <;> linarith [KernelR.log_recovery_bounds.1, KernelR.log_recovery_bounds.2]

/-- With the first MARK dose already stored, an otherwise quiet teacher
    has reopened before the original timer sends the next work pulse. -/
theorem original_teacher_timer_after_next_reopen :
    1 + Real.log (5 / 2) / (9 / 50) < teacherWorkOffset := by
  unfold teacherWorkOffset
  linarith [KernelR.log_recovery_bounds.1]

/-- Exactly the symmetric budgets that fit the full fabrication-box work
window around this centre. This optimizes the stated window, not the true
precharge response beyond its certified bounds. -/
theorem capped_teacher_jitter_iff {σ : ℝ} (nonnegative : 0 ≤ σ) :
    (∀ delay ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ),
      (139 / 250 : ℝ) ≤ cappedTeacherPeriod - delay ∧
        cappedTeacherPeriod - delay ≤ 11193 / 20000) ↔ σ ≤ cappedTeacherWorkJitter := by
  constructor
  · intro all
    have bound := (all (cappedTeacherWorkOffset + σ) ⟨by linarith, le_rfl⟩).1
    unfold cappedTeacherWorkOffset cappedTeacherWorkJitter at *
    linarith
  · intro budget delay window
    unfold cappedTeacherWorkOffset cappedTeacherWorkJitter at *
    constructor <;> linarith [window.1, window.2]

/-- A complete FAST phase followed by SLOW has the exact same return date
after every firing at saturated recovery, regardless of MARK activity.
The supplied trace begins just after the FIRE (FAST, charge 1). -/
theorem capped_teacher_reopens {n θ ε route s u} (e : @Execution n θ route s u)
    (box : PhysicalBox θ ε) (i : Fin n)
    (fast : s.main i = .fast) (charge : s.x i .q = 1) (cap : s.x i .b = 11 / 10)
    (horizon : s.time + cappedTeacherPeriod < u.time) :
    ∃ (v w : Snapshot n) (head : Execution θ route s v) (exit : Jump route v w)
      (tail : Execution θ route w u) (reopen : ConstantSlowReturn tail i (11 / 10)),
      e = head.append (.cons (.jump exit) tail) ∧
      reopen.afterReturn.time = s.time + cappedTeacherPeriod ∧
      reopen.afterReturn.x i .b = 11 / 10 := by
  obtain ⟨v, w, head, exit, tail, reconstruct, _, _, slow, date, quarter⟩ :=
    e.fast_phase_completion i fast charge (by linarith [capped_teacher_period_bounds.1])
  have wDate : w.time = s.time + 1 := exit.time_unchanged.trans date
  have wCharge : w.x i .q = 1 / 4 := by rw [exit.physical_continuous, quarter]
  let lead : Execution θ route s w := head.append (.cons (.jump exit) (.nil _))
  have wCap := teacher_recovery_stays_at_cap lead box i cap
  have endCap := teacher_recovery_stays_at_cap tail box i wCap
  have stable := (tail.recovery_constant_of_end box i (endCap.trans wCap.symm)).2
  have all : tail.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b = 11 / 10) :=
    tail.allFlows_mono (fun _ h t ht => (h t ht).trans wCap) stable
  have ratio : (1 / 4 : ℝ) / (1 / 10) = 5 / 2 := by norm_num
  obtain ⟨reopen⟩ := tail.constant_slow_return i slow (by rw [wCharge]; norm_num)
    (11 / 10) (by norm_num) all (by
      rw [wCharge, wDate, ratio]
      simpa only [cappedTeacherPeriod, add_assoc] using horizon)
  let slowLead : Execution θ route w reopen.afterReturn :=
    reopen.span.append (.cons (.jump reopen.exit) (.nil _))
  refine ⟨v, w, head, exit, tail, reopen, reconstruct, ?_,
    teacher_recovery_stays_at_cap slowLead box i wCap⟩
  rw [reopen.date, wCharge, wDate, ratio]
  simp only [cappedTeacherPeriod, add_assoc]

/-- The exact capped clock places the work pulse in the certified ±10%
window for every local delay within the stated symmetric jitter budget. -/
theorem capped_teacher_work_timing {σ delay : ℝ} (nonnegative : 0 ≤ σ)
    (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : delay ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (ε : ℝ) : CappedWorkTiming ε (cappedTeacherPeriod - delay) :=
  Or.inl ((capped_teacher_jitter_iff nonnegative).2 budget delay wire)

/-- A local wire may realize a different bounded delay at each teacher FIRE. -/
noncomputable def cappedTeacherSelfRouter (work : Port) (delay : ℝ → ℝ) : Router 1 :=
  fun i fire => [⟨i, work, fire + delay fire⟩]

theorem capped_teacher_self_router_causal (work : Port) {delay : ℝ → ℝ} {σ : ℝ}
    (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    StrictCausalRouter (cappedTeacherSelfRouter work delay) := by
  intro i fire token member
  have lower := (wire fire).1
  simp [cappedTeacherSelfRouter] at member
  subst token
  change fire < fire + delay fire
  simp only [cappedTeacherWorkOffset, cappedTeacherWorkJitter] at lower budget
  linarith [capped_teacher_period_bounds.1]

private theorem teacher_raw_of_due_token {n θ route s u} (e : @Execution n θ route s u)
    (token : Delivery n) (queued : token ∈ s.pending)
    (future : s.time ≤ token.due) (due : token.due < u.time) (expiry : u.time < token.due + 1) :
    u.raw token.cell token.port = some token.due := by
  induction e with
  | nil => exact False.elim (not_lt_of_ge future due)
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      exact ih (by simpa only [f.queue_fixed] using queued) (f.pending_urgent token queued) due expiry
    | jump j =>
      have step : token ∈ v.pending ∨ v.raw token.cell token.port = some token.due := by
        cases j with
        | arrive delivered before after queue date free =>
          by_cases eq : token = delivered
          · subst token
            exact Or.inr (by simp [setRaw, date])
          · rw [queue] at queued
            refine Or.inl ?_
            simpa [List.mem_append, eq] using queued
        | fire => exact Or.inl (List.mem_append_left _ queued)
        | fastEnd => exact Or.inl queued
        | reopen => exact Or.inl queued
        | mark => exact Or.inl queued
        | silent => exact Or.inl queued
        | error => exact Or.inl queued
        | auxReady => exact Or.inl queued
        | rawEnd => exact Or.inl queued
      rcases step with queue | active
      · exact ih queue (j.time_unchanged.trans_le future) due expiry
      · exact rest.raw_persists token.cell token.port token.due active expiry

/-- Snapshot produced by the teacher FIRE under the jittered local router. -/
noncomputable def cappedTeacherFired (before : Snapshot 1) (work : Port) (delay : ℝ → ℝ) : Snapshot 1 :=
  { (setMain before 0 .fast) with
    pending := before.pending ++ cappedTeacherSelfRouter work delay 0 before.time }

/-- For any actual continuation past the capped clock's horizon, a FIRE
with a bounded self-wire has an actual reopening in the work-pulse window.
The issued work token has arrived and is still active at that reopening. -/
theorem capped_teacher_fire_work_window {θ ε before u work delay σ}
    (box : @PhysicalBox 1 θ ε) (ready : before.main 0 = .ready) (charge : before.x 0 .q = 1)
    (cap : before.x 0 .b = 11 / 10) (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (e : Execution θ (cappedTeacherSelfRouter work delay) (cappedTeacherFired before work delay) u)
    (horizon : before.time + cappedTeacherPeriod < u.time) :
    ∃ (fire : Jump (cappedTeacherSelfRouter work delay) before (cappedTeacherFired before work delay))
      (reopen : Snapshot 1)
      (cut : Execution θ (cappedTeacherSelfRouter work delay) (cappedTeacherFired before work delay) reopen),
      fire.ledger.emissions = [(0, before.time)] ∧ e.IsPrefix cut ∧
      reopen.main 0 = .ready ∧ reopen.x 0 .q = 1 / 10 ∧ reopen.x 0 .b = 11 / 10 ∧
      reopen.time = before.time + cappedTeacherPeriod ∧
      reopen.raw 0 work = some (before.time + delay before.time) ∧
      CappedWorkTiming ε (reopen.time - (before.time + delay before.time)) := by
  let routedFire : Jump (cappedTeacherSelfRouter work delay) before (cappedTeacherFired before work delay) :=
    .fire before 0 ready charge
  obtain ⟨v, w, head, exit, tail, ret, split, date, recovery⟩ :=
    capped_teacher_reopens e box 0 (by simp [cappedTeacherFired, setMain]) charge cap horizon
  let slowCut : Execution θ (cappedTeacherSelfRouter work delay) w ret.afterReturn :=
    ret.span.append (.cons (.jump ret.exit) (.nil _))
  let lead := head.append (.cons (.jump exit) slowCut)
  have splitTail : tail = slowCut.append ret.rest := by
    refine ret.reconstruct.trans ?_
    simp only [slowCut, Execution.append_assoc, Execution.append]
  have splitLead : e = lead.append ret.rest := by
    calc
      e = head.append (.cons (.jump exit) tail) := split
      _ = head.append (.cons (.jump exit) (slowCut.append ret.rest)) :=
        congrArg (fun trace => head.append (.cons (.jump exit) trace)) splitTail
      _ = lead.append ret.rest := by simp only [lead, Execution.append_assoc, Execution.append]
  have cutPrefix : e.IsPrefix lead :=
    (congrArg (fun trace => trace.IsPrefix lead) splitLead).mpr (.append_left _ _)
  have window := (capped_teacher_jitter_iff nonnegative).2 budget (delay before.time) (wire before.time)
  have date' : ret.afterReturn.time = before.time + cappedTeacherPeriod := date
  have age : ret.afterReturn.time - (before.time + delay before.time) =
      cappedTeacherPeriod - delay before.time := by rw [date']; ring
  let token : Delivery 1 := ⟨0, work, before.time + delay before.time⟩
  have queued : token ∈ (cappedTeacherFired before work delay).pending :=
    List.mem_append_right _ (by simp [cappedTeacherSelfRouter, token])
  have future : (cappedTeacherFired before work delay).time ≤ token.due := by
    exact (capped_teacher_self_router_causal work budget wire 0 before.time token
      (by simp [cappedTeacherSelfRouter, token])).le
  have stillRaw : ret.afterReturn.raw 0 work = some token.due :=
    teacher_raw_of_due_token lead token queued future
      (by change before.time + delay before.time < ret.afterReturn.time; linarith [window.1])
      (by change ret.afterReturn.time < before.time + delay before.time + 1; linarith [window.2])
  exact ⟨routedFire, ret.afterReturn, lead, rfl, cutPrefix, ret.ready_after, ret.charge_after,
    recovery, date', stillRaw, Or.inl (by rw [age]; exact window)⟩

/-- The capped clock and the physical pulse-tail estimate compose on any
isolated actual continuation to the precharge date. -/
theorem capped_teacher_precharge_of_execution {θ ε before u work delay σ}
    (box : @PhysicalBox 1 θ ε) (ready : before.main 0 = .ready) (charge : before.x 0 .q = 1)
    (cap : before.x 0 .b = 11 / 10) (workCap : before.x 0 (.z work) = Real.log ((θ 0).cap work))
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (e : Execution θ (cappedTeacherSelfRouter work delay) (cappedTeacherFired before work delay) u)
    (only : ∀ d ∈ e.deliveries, d = ⟨0, work, before.time + delay before.time⟩)
    (other : ∀ q, q ≠ work → before.raw 0 q = none)
    (finish : u.time = before.time + delay before.time + 7 / 5) :
    u.main 0 = .ready ∧ (13 / 20 ≤ u.x 0 .q ∧ u.x 0 .q ≤ 39 / 50) ∧
      u.x 0 .b = 11 / 10 ∧ u.x 0 (.z work) = Real.log ((θ 0).cap work) ∧
      ∀ q, q ≠ work → before.aux 0 q = .ready → RestBand (before.x 0 (.m q)) →
        (u.aux 0 q = .ready ∧ RestBand (u.x 0 (.m q))) ∧ u.x 0 (.z q) = before.x 0 (.z q) := by
  have timing := (capped_teacher_jitter_iff nonnegative).2 budget _ (wire before.time)
  obtain ⟨_, reopen, cut, _, prefixCut, mode, atRest, _, reopenDate, raw, window⟩ :=
    capped_teacher_fire_work_window box ready charge cap nonnegative budget wire e (by linarith [timing.2])
  obtain ⟨continuation⟩ := prefixCut.continuation
  have quiet (q : Port) : NoArrivalAt continuation.tail 0 q := by
    intro d hd
    have date := only d (continuation.deliveries ▸ List.mem_append_right _ hd)
    have impossible := (continuation.tail.delivery_time_bounds d hd).1
    rw [date] at impossible
    change reopen.time ≤ before.time + delay before.time at impossible
    linarith [timing.1]
  have noOther (q : Port) (distinct : q ≠ work) : NoArrivalAt e 0 q := by
    intro d hd
    right
    rw [only d hd]
    exact Ne.symm distinct
  have others (q : Port) (distinct : q ≠ work) : reopen.raw 0 q = none := by
    exact (cut.raw_absent_of_no_arrival 0 q (other q distinct)
      (prefixCut.no_arrival 0 q (noOther q distinct))).1
  have remains : reopen.x 0 (.z work) = Real.log ((θ 0).cap work) :=
    le_antisymm (cut.gain_cap 0 work workCap.le) (workCap.symm.le.trans (cut.gain_nondecreasing box 0 work))
  obtain ⟨endReady, _, _, band, workGain, _⟩ :=
    capped_work_precharge_of_reopened continuation.tail box 0 work
      (before.time + delay before.time) mode atRest remains window raw others quiet finish
  exact ⟨endReady, band, teacher_recovery_stays_at_cap e box 0 cap, workGain,
    fun q distinct sensor rest => e.aux_no_input_rest_band 0 q sensor rest
      (other q distinct) (noOther q distinct)⟩

end RecursiveLearning.Native
