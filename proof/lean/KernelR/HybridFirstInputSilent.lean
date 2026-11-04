import KernelR.HybridFirstInputMark
import KernelR.HybridReadyProtectedFlowExistence
import KernelR.HybridPulseSpans
import KernelR.HybridStableMemory

/-! Construct the first actual MARK decay and SILENT entry from an already
constructed first MARK, with the source's original raw tail unchanged. -/
namespace KernelR.Hybrid
open Set

theorem readyPulse_restart (initial amplitude start cut t : ℝ) :
    readyPulse (readyPulse initial amplitude start cut)
      (amplitude * Real.exp (-a * (cut - start))) cut t = readyPulse initial amplitude start t := by
  simp only [readyPulse]
  rw [show t - start = (cut - start) + (t - cut) by ring,response_add,mul_add,Real.exp_add]
  ring

theorem FirstInputMark.protected_response_restart {n θ s i p} (f : @FirstInputMark n θ s i p) (t : ℝ) :
    readyPulse (f.final.x i .q) (Real.exp (f.final.x i (.z p)) * rawInputScale (some s.time) f.final.time)
      f.final.time t = readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t := by
  simpa [FirstInputMark.final,setAux,readyInputEnd,readyInputValues,readyInputMainAmplitude,rawInputScale] using
    readyPulse_restart (s.x i .q) (Real.exp (s.x i (.z p))) s.time (s.time + f.latency) t

noncomputable def FirstInputMark.silentDate {n θ s i p} (f : @FirstInputMark n θ s i p) : ℝ :=
  s.time + f.latency + Real.log (5 / 4) / (θ i).lm p

noncomputable def FirstInputMark.silentBefore {n θ s i p} (f : @FirstInputMark n θ s i p) : Snapshot n :=
  readyProtectedEnd θ f.final i p .mark (some s.time) f.silentDate

noncomputable def FirstInputMark.silentFinal {n θ s i p} (f : @FirstInputMark n θ s i p) : Snapshot n :=
  setAux f.silentBefore i p .silent

structure FirstInputSilent {n θ s i p} (f : @FirstInputMark n θ s i p) where
  flow : Flow θ f.final f.silentBefore
  threshold : f.silentBefore.x i (.m p) = 4 / 5
  main_below : ∀ j, f.silentBefore.x j .q < 1
  aux_below : ∀ j q, j ≠ i ∨ q ≠ p → f.silentBefore.x j (.m q) < 1
  deadline : f.silentDate < s.time + 1 / 20
  pending_future : ∀ d ∈ s.pending, f.silentDate < d.due

noncomputable def FirstInputSilent.final {n θ s i p} {f : @FirstInputMark n θ s i p}
    (_g : FirstInputSilent f) : Snapshot n := f.silentFinal

noncomputable def FirstInputSilent.continuation {n θ s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (route : Router n) : Execution θ route f.final g.final :=
  .cons (.flow g.flow) (.cons (.jump (.silent _ i p
    (by simp [FirstInputMark.silentBefore,readyProtectedEnd,FirstInputMark.final,setAux]) g.threshold)) (.nil _))

noncomputable def FirstInputSilent.execution {n θ s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (route : Router n) : Execution θ route s g.final :=
  (f.execution route).append (g.continuation route)

@[simp] theorem FirstInputSilent.continuation_contacts_transversal {n θ s i p}
    {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) (route : Router n) :
    (g.continuation route).ContactsTransversal := by
  simp [FirstInputSilent.continuation, Execution.ContactsTransversal, Jump.ContactTransversal]

@[simp] theorem FirstInputSilent.contacts_transversal {n θ s i p}
    {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) (route : Router n) :
    (g.execution route).ContactsTransversal := by
  simp [FirstInputSilent.execution, FirstInputSilent.continuation,
    Execution.ContactsTransversal, Jump.ContactTransversal]

theorem FirstInputSilent.date {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) :
    g.final.time = f.silentDate := rfl

theorem FirstInputSilent.queue_preserved {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) :
    g.final.pending = s.pending := rfl

theorem FirstInputSilent.gain_preserved {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f)
    (j : Fin n) (q : Port) : g.final.x j (.z q) = s.x j (.z q) := rfl

theorem FirstInputSilent.recovery_preserved {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f)
    (j : Fin n) : g.final.x j .b = s.x j .b := rfl

theorem FirstInputSilent.main_ready {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f)
    (j : Fin n) : g.final.main j = .ready := f.main_ready j

theorem FirstInputSilent.aux_silent {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) :
    g.final.aux i p = .silent := by simp [FirstInputSilent.final,FirstInputMark.silentFinal,setAux]

theorem FirstInputSilent.aux_other {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f)
    (j : Fin n) (q : Port) (h : j ≠ i ∨ q ≠ p) : g.final.aux j q = .ready := by
  rcases h with hj | hq
  · simp [FirstInputSilent.final,FirstInputMark.silentFinal,FirstInputMark.silentBefore,readyProtectedEnd,
      FirstInputMark.final,setAux,readyInputEnd,f.aux_ready,hj]
  · simp [FirstInputSilent.final,FirstInputMark.silentFinal,FirstInputMark.silentBefore,readyProtectedEnd,
      FirstInputMark.final,setAux,readyInputEnd,Function.update_apply,ite_apply,f.aux_ready,hq]

theorem FirstInputSilent.sensor_charge {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) :
    g.final.x i (.m p) = 4 / 5 := g.threshold

theorem FirstInputSilent.raw_active {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) :
    g.final.raw i p = some s.time := f.raw_active

theorem FirstInputSilent.raw_other {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f)
    (j : Fin n) (q : Port) (h : j ≠ i ∨ q ≠ p) : g.final.raw j q = none := f.raw_other j q h

theorem FirstInputSilent.charge_solution {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) :
    g.final.x i .q = readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time g.final.time := by
  simpa [FirstInputSilent.final,FirstInputMark.silentFinal,setAux,FirstInputMark.silentBefore,readyProtectedEnd,
    readyProtectedValues,protectedRawAmplitude] using f.protected_response_restart f.silentDate

theorem FirstInputSilent.final_guards {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f) :
    BeforeGuards g.final g.final.x := by
  constructor
  · intro j
    rw [g.main_ready j]
    exact g.main_below j
  · intro j q
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      rw [g.aux_silent,g.sensor_charge]
      norm_num
    · rw [g.aux_other j q (by tauto)]
      exact g.aux_below j q (by tauto)

theorem FirstInputSilent.complete {n θ s i p} {f : @FirstInputMark n θ s i p} (g : FirstInputSilent f)
    (route : Router n) : CompleteThrough (g.execution route) g.final.time := by
  refine ⟨rfl,?_,g.pending_future⟩
  intro u
  apply g.final_guards.no_jump
  · intro j q origin hr
    change s.raw j q = some origin at hr
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      have he : origin = s.time := Option.some.inj (hr.symm.trans f.raw_active)
      rw [g.date,he]
      linarith [g.deadline]
    · rw [f.raw_other j q (by tauto)] at hr
      contradiction
  · exact g.pending_future

/-- From a constructed first MARK, the physical MARK decay supplies its own
first floor time and a real SILENT jump. No new execution is supplied. -/
theorem FirstInputMark.first_silent_exists {n θ ε s i p} (f : @FirstInputMark n θ s i p)
    (hb : PhysicalBox θ ε) (hqi : s.x i .q ≤ 7 / 50)
    (hg : Real.exp (s.x i (.z p)) ≤ 4 / 3)
    (hp : ∀ d ∈ s.pending, s.time + 1 / 10 ≤ d.due) : Nonempty (FirstInputSilent f) := by
  let D := Real.log (5 / 4 : ℝ) / (θ i).lm p
  have hrate := (hb.rates_positive i p).1
  have hD : 0 < D := div_pos (Real.log_pos (by norm_num)) hrate
  have hDupper : D ≤ 1 / 45 := hb.mark_duration_upper i p
  have htime : f.final.time < f.silentDate := by
    change s.time + f.latency < s.time + f.latency + D
    linarith
  have hdate : f.silentDate < s.time + 1 / 20 := by
    change s.time + f.latency + D < s.time + 1 / 20
    linarith [f.deadline]
  have hqstart : ∀ j, f.final.x j .q < 1 := f.main_below
  have hmstart : ∀ j q, j ≠ i ∨ q ≠ p → f.final.x j (.m q) < 1 := f.aux_below
  have hm : ∀ j, f.final.main j = .ready := f.main_ready
  have ha : f.final.aux i p = .mark := by simp [FirstInputMark.final,setAux]
  have hao : ∀ j q, j ≠ i ∨ q ≠ p → f.final.aux j q = .ready := by
    intro j q h
    rcases h with hj | hq
    · simp [FirstInputMark.final,setAux,readyInputEnd,f.aux_ready,hj]
    · simp [FirstInputMark.final,setAux,readyInputEnd,Function.update_apply,ite_apply,f.aux_ready,hq]
  have hr : f.final.raw i p = some s.time := f.raw_active
  have ho : ∀ j q, j ≠ i ∨ q ≠ p → f.final.raw j q = none := f.raw_other
  have hsensor : f.final.x i (.m p) = 1 := f.sensor_threshold
  have hsupport : ∀ o, some s.time = some o → o ≤ f.final.time ∧ f.silentDate ≤ o + 1 := by
    intro o he
    have heq : o = s.time := (Option.some.inj he).symm
    subst o
    change s.time ≤ s.time + f.latency ∧ f.silentDate ≤ s.time + 1
    constructor <;> linarith [f.early]
  have hq : ∀ t ∈ Ico f.final.time f.silentDate, readyPulse (f.final.x i .q)
      (Real.exp (f.final.x i (.z p)) * rawInputScale (some s.time) f.final.time) f.final.time t < 1 := by
    intro t ht
    rw [f.protected_response_restart]
    apply readyPulse_nominal_silent hqi hg
    have hs : s.time < f.final.time := by change s.time < s.time + f.latency; linarith [f.early]
    exact hs.le.trans ht.1
  have hend : Real.exp (-(θ i).lm p * D) = (4 / 5 : ℝ) := by
    have hd : -(θ i).lm p * D = -Real.log (5 / 4 : ℝ) := by dsimp [D]; field_simp
    rw [hd,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4)]
    norm_num
  have hx : ∀ t ∈ Ico f.final.time f.silentDate, (if AuxMode.mark = .mark then (4 / 5 : ℝ) else 1 / 10) <
      f.final.x i (.m p) * Real.exp (-protectedReadyRate (θ i) p .mark * (t - f.final.time)) := by
    intro t ht
    simp only [ite_true,hsensor,one_mul,protectedReadyRate]
    rw [← hend]
    apply Real.exp_lt_exp.mpr
    have htime : t - f.final.time < D := by
      change t - (s.time + f.latency) < D
      have ht2 : t < s.time + f.latency + D := ht.2
      linarith
    nlinarith
  let flow := readyProtectedFlow f.final i p .mark (some s.time) htime (Or.inl rfl) hm ha hao hr ho
    hsupport hqstart hmstart hq hx (fun d hd => by change d ∈ s.pending at hd; linarith [hp d hd])
  have hthreshold : f.silentBefore.x i (.m p) = 4 / 5 := by
    simp [FirstInputMark.silentBefore,readyProtectedEnd,readyProtectedValues]
    rw [hsensor]
    simpa only [one_mul,protectedReadyRate,FirstInputMark.silentDate,FirstInputMark.final,
      setAux,readyInputEnd,add_sub_cancel_left,neg_mul] using hend
  refine ⟨⟨flow,hthreshold,?_,?_,hdate,fun d hd => by linarith [hp d hd]⟩⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [FirstInputMark.silentBefore,readyProtectedEnd,readyProtectedValues]
      simp only [protectedRawAmplitude,ite_true]
      rw [f.protected_response_restart]
      exact readyPulse_nominal_silent hqi hg (by
        have hs : s.time < f.final.time := by change s.time < s.time + f.latency; linarith [f.early]
        exact hs.le.trans htime.le)
    · change readyPulse (f.final.x j .q) (protectedRawAmplitude f.final i p (some s.time) j) f.final.time f.silentDate < 1
      rw [protectedRawAmplitude,ite_eq_right hj,readyPulse_zero_eq_relax]
      exact relax_lt (by norm_num) htime.le (hqstart j) (by norm_num)
  · intro j q h
    have hnot : ¬ (j = i ∧ q = p) := by tauto
    change (if j = i ∧ q = p then _ else _) < 1
    rw [ite_eq_right hnot]
    exact relax_lt (by norm_num) htime.le (hmstart j q h) (by norm_num)

end KernelR.Hybrid
