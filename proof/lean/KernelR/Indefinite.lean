import KernelR.HybridFuture

/-! Conditional indefinite operation, built from actual finite executions.
The one-input physical cycle is an explicit, as-yet uninstantiated contract.
The construction retains states across rounds and moves later source tokens
into the initial finite queue without changing earlier physical ledgers. -/
namespace KernelR.Hybrid

def SameMemory {n} (reference s : Snapshot n) : Prop :=
  ∀ i, s.x i .b = reference.x i .b ∧ ∀ p, s.x i (.z p) = reference.x i (.z p)

def LearnedDomain {n} (θ : Fin n → Parameters) (active : Fin n → Port)
    (reference s : Snapshot n) : Prop := LearnedRest θ active s ∧ SameMemory reference s

theorem LearnedDomain.idle {n θ active reference s} (h : @LearnedDomain n θ active reference s)
    {t : ℝ} (ht : s.time ≤ t) : LearnedDomain θ active reference (idleAt s t) :=
  ⟨h.1.idle ht, h.2⟩

def sourceToken {n} (cell : Fin n) (port : Port) (time : ℝ) : Delivery n := ⟨cell, port, time⟩

/-- Physical execution of one input and its entire settling interval. The
singleton lists exclude missing and additional firings at every cell. -/
structure PulseCycle {n} (θ : Fin n → Parameters) (route : Router n)
    (active : Fin n → Port) (reference : Snapshot n)
    (cell : Fin n) (port : Port) (duration : ℝ) (latency : Fin n → ℝ) (s : Snapshot n) where
  last : Snapshot n
  execution : Execution θ route (withFuture s [sourceToken cell port s.time]) last
  domain : LearnedDomain θ active reference last
  settles : last.time = s.time + duration
  response : ∀ i, execution.emissionTimes i = [s.time + latency i]

/-- This contract is a remaining physical proof obligation, not a proved
property of R. It must be instantiated from guards, flows, routing and real
inequalities for a specified learned section. -/
structure PulseContract {n} (θ : Fin n → Parameters) (route : Router n)
    (active : Fin n → Port) (reference : Snapshot n) (cell : Fin n) (port : Port) where
  duration : ℝ
  positive : 0 < duration
  latency : Fin n → ℝ
  latency_nonnegative : ∀ i, 0 ≤ latency i
  latency_before_settled : ∀ i, latency i < duration
  cycle : ∀ s, LearnedDomain θ active reference s →
    Nonempty (PulseCycle θ route active reference cell port duration latency s)

structure ServedPulse {n} (θ : Fin n → Parameters) (route : Router n)
    (active : Fin n → Port) (reference : Snapshot n)
    (cell : Fin n) (port : Port) (duration : ℝ) (latency : Fin n → ℝ)
    (s : Snapshot n) (input : ℝ) where
  last : Snapshot n
  execution : Execution θ route (withFuture s [sourceToken cell port input]) last
  domain : LearnedDomain θ active reference last
  settles : last.time = input + duration
  response : ∀ i, execution.emissionTimes i = [input + latency i]

theorem Execution.emissionTimes_append {n θ route s u v}
    (e : @Execution n θ route s u) (f : Execution θ route u v) (i : Fin n) :
    (e.append f).emissionTimes i = e.emissionTimes i ++ f.emissionTimes i := by
  simp [emissionTimes, e.append_ledger, Ledger.add, List.filter_append, List.map_append]

theorem Execution.emissionTimes_withFuture {n θ route s u} (e : @Execution n θ route s u)
    (future : List (Delivery n)) (hf : ∀ d ∈ future, u.time ≤ d.due) (i : Fin n) :
    (e.withFuture future hf).emissionTimes i = e.emissionTimes i := by
  simp [emissionTimes, e.withFuture_ledger future hf]

/-- Waiting is supplied by the proved physical idle flow, not by the pulse
contract. The queued source is due at the waiting interval's endpoint. -/
noncomputable def PulseContract.serve {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port) (s : Snapshot n)
    (hs : LearnedDomain θ active reference s) (input : ℝ) (ht : s.time ≤ input) :
    ServedPulse θ route active reference cell port law.duration law.latency s input := by
  let waiting := learned_idle_complete (route := route) hs.1 ht
  let wait := Classical.choose waiting
  have hempty := (Classical.choose_spec waiting).2.2
  let cycle := Classical.choice (law.cycle (idleAt s input) (hs.idle ht))
  let queued := wait.withFuture [sourceToken cell port input] (by
    intro d hd; have he := List.mem_singleton.mp hd; subst d; exact le_rfl)
  let cycleExecution : Execution θ route
      (withFuture (idleAt s input) [sourceToken cell port input]) cycle.last := cycle.execution
  refine ⟨cycle.last, queued.append cycleExecution, cycle.domain, cycle.settles, ?_⟩
  intro i
  have hq : queued.emissionTimes i = [] := by
    calc
      _ = wait.emissionTimes i := Execution.emissionTimes_withFuture _ _ _ _
      _ = [] := by simp [Execution.emissionTimes, wait, hempty]
  have hc : cycleExecution.emissionTimes i = [input + law.latency i] := cycle.response i
  exact (Execution.emissionTimes_append queued cycleExecution i).trans (by rw [hq, hc]; rfl)

/-- Arbitrary future dates, with a positive settling budget between inputs.
The schedule may be irregular and may contain arbitrarily long silences. -/
structure FutureSchedule (duration : ℝ) where
  time : ℕ → ℝ
  separated : ∀ k, time k + duration ≤ time (k+1)

theorem FutureSchedule.growth {D : ℝ} (schedule : FutureSchedule D) (k : ℕ) :
    schedule.time 0 + (k : ℝ) * D ≤ schedule.time k := by
  induction k with
  | zero => simp
  | succ k ih => push_cast; nlinarith [schedule.separated k]

theorem FutureSchedule.strictMono {D : ℝ} (schedule : FutureSchedule D) (hD : 0 < D) :
    StrictMono schedule.time := by
  apply strictMono_nat_of_lt_succ
  intro k
  linarith [schedule.separated k]

theorem FutureSchedule.locally_finite {D : ℝ} (schedule : FutureSchedule D) (hD : 0 < D)
    (T : ℝ) : ∃ B : ℕ, ∀ k, schedule.time k ≤ T → k ≤ B := by
  obtain ⟨B, hB⟩ := exists_nat_ge ((T - schedule.time 0) / D)
  refine ⟨B, fun k hk => ?_⟩
  have hg := schedule.growth k
  have hbound : (k : ℝ) ≤ (T - schedule.time 0) / D :=
    (le_div_iff₀ hD).mpr (by linarith)
  exact (Nat.cast_le (α := ℝ)).mp (hbound.trans hB)

/-- State choices are recursive. Round k+1 starts from the actual state left
by round k; no resetting, replacement, or independent per-horizon choice occurs. -/
noncomputable def PulseContract.readyStates {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0) :
    (k : ℕ) → {s : Snapshot n // LearnedDomain θ active reference s ∧ s.time ≤ schedule.time k}
  | 0 => ⟨initial, hinit, hfirst⟩
  | k+1 =>
    let previous := law.readyStates schedule initial hinit hfirst k
    let served := law.serve previous.val previous.property.1 (schedule.time k) previous.property.2
    ⟨served.last, served.domain, by rw [served.settles]; exact schedule.separated k⟩

noncomputable def PulseContract.round {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (k : ℕ) : ServedPulse θ route active reference cell port law.duration law.latency
      (law.readyStates schedule initial hinit hfirst k).val (schedule.time k) :=
  let state := law.readyStates schedule initial hinit hfirst k
  law.serve state.val state.property.1 (schedule.time k) state.property.2

def sourceQueue {n} (cell : Fin n) (port : Port) (time : ℕ → ℝ) : ℕ → List (Delivery n)
  | 0 => []
  | k+1 => sourceToken cell port (time k) :: sourceQueue cell port time k

/-- Every finite prefix is one actual execution with its sources already in
the initial queue. Later sources preserve the previous physical ledger. -/
noncomputable def PulseContract.prefixes {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0) :
    (k : ℕ) → Execution θ route (withFuture initial (sourceQueue cell port schedule.time k))
      (law.readyStates schedule initial hinit hfirst k).val
  | 0 => .nil initial
  | k+1 =>
    let previous := law.prefixes schedule initial hinit hfirst k
    let queued := previous.withFuture [sourceToken cell port (schedule.time k)] (by
      intro d hd; have he := List.mem_singleton.mp hd; subst d
      exact (law.readyStates schedule initial hinit hfirst k).property.2)
    queued.append (law.round schedule initial hinit hfirst k).execution

theorem PulseContract.prefix_response {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (k : ℕ) (i : Fin n) :
    (law.prefixes schedule initial hinit hfirst k).emissionTimes i =
      (List.range k).map (fun j => schedule.time j + law.latency i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (((law.prefixes schedule initial hinit hfirst k).withFuture
      [sourceToken cell port (schedule.time k)] _).append
      (law.round schedule initial hinit hfirst k).execution).emissionTimes i = _
    calc
      _ = ((law.prefixes schedule initial hinit hfirst k).withFuture
          [sourceToken cell port (schedule.time k)] _).emissionTimes i ++
          (law.round schedule initial hinit hfirst k).execution.emissionTimes i :=
        Execution.emissionTimes_append _ _ i
      _ = _ := by
        rw [Execution.emissionTimes_withFuture, ih,
          (law.round schedule initial hinit hfirst k).response i]
        simp [List.range_succ, List.map_append]

theorem PulseContract.state_time_growth {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (k : ℕ) : initial.time + (k : ℝ) * law.duration ≤
      (law.readyStates schedule initial hinit hfirst k).val.time := by
  induction k with
  | zero => simp [readyStates]
  | succ k ih =>
    change initial.time + ((k+1 : ℕ) : ℝ) * law.duration ≤
      (law.round schedule initial hinit hfirst k).last.time
    rw [(law.round schedule initial hinit hfirst k).settles]
    have ht := (law.readyStates schedule initial hinit hfirst k).property.2
    push_cast
    linarith

theorem PulseContract.prefix_complete {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (k : ℕ) : CompleteThrough (law.prefixes schedule initial hinit hfirst k)
      (law.readyStates schedule initial hinit hfirst k).val.time := by
  have h := (law.readyStates schedule initial hinit hfirst k).property.1.1
  exact ⟨rfl, h.no_jump, by simp [h.pending]⟩

theorem PulseContract.prefix_count {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (k : ℕ) (i : Fin n) : ((law.prefixes schedule initial hinit hfirst k).signal i).count = k := by
  simp [Execution.signal, law.prefix_response schedule initial hinit hfirst k i]

theorem PulseContract.prefix_time {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (k : ℕ) (i : Fin n) (j : ℕ) (hj : j < k) :
    ((law.prefixes schedule initial hinit hfirst k).signal i).time j =
      schedule.time j + law.latency i := by
  simp [Execution.signal, law.prefix_response schedule initial hinit hfirst k i, hj]

theorem PulseContract.prefix_intervals {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (k : ℕ) (i : Fin n) (j l : ℕ) (hj : j < k) (hl : l < k) :
    ((law.prefixes schedule initial hinit hfirst k).signal i).time l -
      ((law.prefixes schedule initial hinit hfirst k).signal i).time j =
      schedule.time l - schedule.time j := by
  rw [law.prefix_time schedule initial hinit hfirst k i l hl,
    law.prefix_time schedule initial hinit hfirst k i j hj]
  ring

/-- Existence of compatible responding prefixes at unbounded times. This
theorem is conditional on `PulseContract`; it does not instantiate that contract. -/
theorem PulseContract.unbounded_responding_prefixes {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (T : ℝ) : ∃ k, T ≤ (law.readyStates schedule initial hinit hfirst k).val.time ∧
      ∀ i, (law.prefixes schedule initial hinit hfirst k).emissionTimes i =
        (List.range k).map (fun j => schedule.time j + law.latency i) := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((T - initial.time) / law.duration)
  have hmul := (div_lt_iff₀ law.positive).mp hk
  refine ⟨k, ?_, law.prefix_response schedule initial hinit hfirst k⟩
  linarith [law.state_time_growth schedule initial hinit hfirst k]

/-- An actual complete execution exists at every finite horizon of the same
future schedule, conditional on the one-input physical contract. Initial queues
contain finite source restrictions; no infinite Lean list is assumed. -/
theorem PulseContract.complete_at_every_horizon {n θ route active reference cell port}
    (law : @PulseContract n θ route active reference cell port)
    (schedule : FutureSchedule law.duration) (initial : Snapshot n)
    (hinit : LearnedDomain θ active reference initial) (hfirst : initial.time ≤ schedule.time 0)
    (T : ℝ) (hT : initial.time ≤ T) :
    ∃ (k : ℕ) (v : Snapshot n)
      (e : Execution θ route (withFuture initial (sourceQueue cell port schedule.time k)) v),
      CompleteThrough e T ∧ ∀ j, schedule.time j ≤ T → j < k := by
  obtain ⟨k, hk, _⟩ := law.unbounded_responding_prefixes schedule initial hinit hfirst (T+1)
  have hbefore : T < (law.readyStates schedule initial hinit hfirst k).val.time := by linarith
  obtain ⟨v, e, he⟩ := (law.prefixes schedule initial hinit hfirst k).complete_prefix T
    (law.prefix_complete schedule initial hinit hfirst k) hT hbefore.le
  refine ⟨k, v, e, he, ?_⟩
  intro j hj
  by_contra hn
  have htime := (schedule.strictMono law.positive).monotone (le_of_not_gt hn)
  have hnext := (law.readyStates schedule initial hinit hfirst k).property.2
  linarith

end KernelR.Hybrid
