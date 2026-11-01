import KernelR.HybridReadyFlowExistence
import KernelR.HybridScalarFirstCrossing
import KernelR.HybridBirthPulseGain
import KernelR.HybridGuardNoJump
import KernelR.HybridSourceProgress

/-! Construct a nontrivial source-driven execution through its first MARK.
No execution, event date or desired case is supplied to the construction. -/
namespace KernelR.Hybrid
open Set

structure FirstInputMark {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) where
  latency : ℝ
  early : 1 / 100 < latency
  deadline : latency < 1 / 40
  main_ready : ∀ j, s.main j = .ready
  aux_ready : ∀ j q, s.aux j q = .ready
  raw_active : s.raw i p = some s.time
  raw_other : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none
  flow : Flow θ s (readyInputEnd θ s i p (s.time + latency))
  threshold : auxPulse (s.x i (.m p)) ((θ i).inputGain p) s.time (s.time + latency) = 1
  main_below : ∀ j, (readyInputEnd θ s i p (s.time + latency)).x j .q < 1
  aux_below : ∀ j q, j ≠ i ∨ q ≠ p →
    (readyInputEnd θ s i p (s.time + latency)).x j (.m q) < 1
  pending_future : ∀ d ∈ s.pending, s.time + latency < d.due

noncomputable def FirstInputMark.final {n θ s i p} (f : @FirstInputMark n θ s i p) : Snapshot n :=
  setAux (readyInputEnd θ s i p (s.time + f.latency)) i p .mark

theorem FirstInputMark.sensor_threshold {n θ s i p} (f : @FirstInputMark n θ s i p) :
    (readyInputEnd θ s i p (s.time + f.latency)).x i (.m p) = 1 := by
  simpa [readyInputEnd,readyInputValues,readyInputAuxAmplitude] using f.threshold

noncomputable def FirstInputMark.execution {n θ s i p} (f : @FirstInputMark n θ s i p)
    (route : Router n) : Execution θ route s f.final :=
  .cons (.flow f.flow) (.cons (.jump (.mark _ i p (f.aux_ready i p) f.sensor_threshold)) (.nil _))

theorem FirstInputMark.final_guards {n θ s i p} (f : @FirstInputMark n θ s i p) :
    BeforeGuards f.final f.final.x := by
  constructor
  · intro j
    simpa [FirstInputMark.final,setAux,readyInputEnd,f.main_ready] using f.main_below j
  · intro j q
    by_cases hj : j = i
    · subst j
      by_cases hq : q = p
      · subst q
        have h := f.sensor_threshold
        simpa [FirstInputMark.final,setAux,readyInputEnd,readyInputValues,
          readyInputAuxAmplitude] using (show (4 / 5 : ℝ) <
          auxPulse (s.x i (.m p)) ((θ i).inputGain p) s.time (s.time + f.latency) by
            simpa [readyInputEnd,readyInputValues,readyInputAuxAmplitude] using
              (show (4 / 5 : ℝ) < (readyInputEnd θ s i p (s.time + f.latency)).x i (.m p) by
                rw [h]; norm_num))
      · simpa [FirstInputMark.final,setAux,readyInputEnd,hq,f.aux_ready] using
          f.aux_below i q (Or.inr hq)
    · simpa [FirstInputMark.final,setAux,readyInputEnd,hj,f.aux_ready] using
        f.aux_below j q (Or.inl hj)

theorem FirstInputMark.complete {n θ s i p} (f : @FirstInputMark n θ s i p)
    (route : Router n) : CompleteThrough (f.execution route) f.final.time := by
  refine ⟨rfl,?_,f.pending_future⟩
  intro u
  apply f.final_guards.no_jump
  · intro j q origin hraw
    change s.raw j q = some origin at hraw
    by_cases hj : j = i
    · subst j
      by_cases hq : q = p
      · subst q
        have he : origin = s.time := Option.some.inj (hraw.symm.trans f.raw_active)
        change s.time + f.latency < origin + 1
        rw [he]; linarith [f.deadline]
      · rw [f.raw_other i q (Or.inr hq)] at hraw; contradiction
    · rw [f.raw_other j q (Or.inl hj)] at hraw; contradiction
  · exact f.pending_future

/-- The two active preguards are now discharged by physical bounds and a
constructed first crossing. All other READY coordinates relax below 1. -/
theorem first_input_mark_exists {n θ ε} (s : Snapshot n) (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port)
    (hm : ∀ j, s.main j = .ready) (ha : ∀ j q, s.aux j q = .ready)
    (hr : s.raw i p = some s.time)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hq : ∀ j, s.x j .q < 1) (hx : ∀ j q, s.x j (.m q) < 1)
    (hqi : s.x i .q ≤ 7 / 50) (hg : Real.exp (s.x i (.z p)) ≤ 4 / 3)
    (hs : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (hp : ∀ d ∈ s.pending, s.time + 1 / 40 ≤ d.due) :
    Nonempty (FirstInputMark θ s i p) := by
  obtain ⟨latency,hearly,hdeadline,hroot,hprior⟩ := hb.first_sensor_crossing i p hs.1 hs.2
  have htime : s.time < s.time + latency := by linarith
  have hraw : s.time + latency < s.time + 1 := by linarith
  have hmain : ∀ t, s.time ≤ t →
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t < 1 :=
    fun t ht => readyPulse_nominal_silent hqi hg ht
  refine ⟨{
    latency := latency
    early := hearly
    deadline := hdeadline
    main_ready := hm
    aux_ready := ha
    raw_active := hr
    raw_other := ho
    flow := readyInputFlow s i p htime hraw hm ha hr ho hq hx
      (fun t ht => hmain t ht.1) hprior (fun d hd => by linarith [hp d hd])
    threshold := hroot
    main_below := ?_
    aux_below := ?_
    pending_future := fun d hd => by linarith [hp d hd]
  }⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [readyInputEnd,readyInputValues,readyInputMainAmplitude] using
        hmain (s.time + latency) htime.le
    · simp only [readyInputEnd,readyInputValues,readyInputMainAmplitude,ite_eq_right hj]
      rw [readyPulse_zero_eq_relax]
      exact relax_lt (by norm_num) htime.le (hq j) (by norm_num)
  · intro j q hother
    have hne : ¬ (j = i ∧ q = p) := by tauto
    simp only [readyInputEnd,readyInputValues,readyInputAuxAmplitude,ite_eq_right hne]
    rw [auxPulse_zero_eq_relax]
    exact relax_lt (by norm_num) htime.le (hx j q) (by norm_num)


/-- Every READY A birth with the original thirty-two-source queue admits a
positive-duration physical prefix through the first actual MARK. This is an
existence theorem: no execution or desired threshold date is assumed. -/
theorem birth_protocol_first_mark_exists {θ ε route born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    ∃ f : FirstInputMark θ (birthProtocolFirstAfter born) 0 0,
      ∃ e : Execution θ route born f.final,
        CompleteThrough e f.final.time ∧
        1 / 100 < f.final.time ∧ f.final.time < 1 / 40 ∧
        e.deliveries = [⟨0,0,0⟩] ∧ e.ledger.emissions = [] ∧
        f.final.pending.length = 31 ∧
        (∀ p, f.final.x 0 (.z p) = born.x 0 (.z p)) ∧
        f.final.x 0 .b = born.x 0 .b ∧ PhysicalInvariant θ f.final ∧ RawValid f.final := by
  have haux : ∀ j p, born.aux j p = .ready := by
    intro j p
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj] using ha p
  have hm : ∀ j, born.main j = .ready := fun j => (hborn.2.2 j).1
  have hq : ∀ j, born.x j .q < 1 := by
    intro j; linarith [(hborn.2.2 j).2.1.2]
  have hx : ∀ j p, born.x j (.m p) < 1 := by
    intro j p
    rcases ((hborn.2.2 j).2.2.2.2 p).2 with h | h
    · linarith [h.2.2]
    · simp [haux] at h
  have hs : 1 / 40 - 1 / 100000 ≤ born.x 0 (.m 0) ∧
      born.x 0 (.m 0) ≤ 1 / 40 + 1 / 100000 := by
    rcases ((hborn.2.2 0).2.2.2.2 0).2 with h | h
    · exact h.2
    · simp [haux] at h
  have hr : (birthProtocolFirstAfter born).raw 0 0 =
      some (birthProtocolFirstAfter born).time := by simp [birthProtocolFirstAfter,setRaw]
  have ho : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ (0 : Port) →
      (birthProtocolFirstAfter born).raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ 0 := by simpa only [ne_self_iff_false,false_or] using h
    simpa [birthProtocolFirstAfter,setRaw,hq] using hborn.2.1 0 q
  have hp : ∀ d ∈ (birthProtocolFirstAfter born).pending,
      (birthProtocolFirstAfter born).time + 1 / 40 ≤ d.due := by
    intro d hd
    change d ∈ sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16 at hd
    change born.time + 1 / 40 ≤ d.due
    rw [hborn.1]
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      have hk : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
      linarith
  obtain ⟨f⟩ := first_input_mark_exists (birthProtocolFirstAfter born) hb 0 0 hm haux hr ho hq hx
    (by change born.x 0 .q ≤ 7 / 50; linarith [(hborn.2.2 0).2.1.2])
    (hborn.nominal_pulse_gain_upper 0 0) hs hp
  let e : Execution θ route born f.final :=
    .cons (.jump (birth_protocol_first_jump hborn hqueue)) (f.execution route)
  refine ⟨f,e,?_,?_,?_,rfl,rfl,?_,fun p => rfl,rfl,e.physical_invariant hb (hborn.physical_invariant hb),
    e.raw_valid hborn.raw_valid⟩
  · exact f.complete route
  · change 1 / 100 < born.time + f.latency
    rw [hborn.1]; simpa using f.early
  · change born.time + f.latency < 1 / 40
    rw [hborn.1]; simpa using f.deadline
  · simp [FirstInputMark.final,setAux,readyInputEnd,birthProtocolFirstAfter,sourceTrain]

end KernelR.Hybrid
