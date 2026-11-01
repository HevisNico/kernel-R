import KernelR.HybridFirstInputSilent
import KernelR.HybridRawExpiryProgress
import KernelR.HybridFirstCycleSchedule

namespace KernelR.Hybrid
open Set

noncomputable def FirstInputSilent.errorDate {n θ s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) : ℝ := g.final.time + Real.log 8 / (θ i).ls p

theorem FirstInputSilent.errorDate_bounds {n θ ε s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (hb : PhysicalBox θ ε) :
    s.time + 99 / 100 < g.errorDate ∧ g.errorDate < s.time + 123 / 100 := by
  rcases hb.first_cycle_schedule i p ⟨f.early,f.deadline⟩ with ⟨_,_,hl,hu,_,_⟩
  change s.time + 99 / 100 < s.time + f.latency + Real.log (5 / 4) / (θ i).lm p + Real.log 8 / (θ i).ls p ∧
    s.time + f.latency + Real.log (5 / 4) / (θ i).lm p + Real.log 8 / (θ i).ls p < s.time + 123 / 100
  constructor <;> linarith

theorem FirstInputSilent.errorDate_positive {n θ ε s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (hb : PhysicalBox θ ε) : g.final.time < g.errorDate := by
  have hp := (hb.aux_durations_positive i p).2.1
  change g.final.time < g.final.time + Real.log 8 / (θ i).ls p
  linarith

theorem FirstInputSilent.response_restart {n θ s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (t : ℝ) :
    readyPulse (g.final.x i .q) (Real.exp (g.final.x i (.z p)) * rawInputScale (some s.time) g.final.time)
      g.final.time t = readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t := by
  rw [g.charge_solution,g.gain_preserved]
  exact readyPulse_restart _ _ _ _ _

theorem silent_full_decay_end {rate start : ℝ} (hr : rate ≠ 0) :
    (4 / 5 : ℝ) * Real.exp (-rate * (start + Real.log 8 / rate - start)) = 1 / 10 := by
  have he : -rate * (start + Real.log 8 / rate - start) = -Real.log 8 := by
    field_simp [hr]
    ring
  rw [he,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  norm_num

structure SilentLeg {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (T : ℝ) where
  flow : Flow θ s (readyProtectedEnd θ s i p .silent origin T)
  main_below : ∀ j, (readyProtectedEnd θ s i p .silent origin T).x j .q < 1
  aux_below : ∀ j q, j ≠ i ∨ q ≠ p →
    (readyProtectedEnd θ s i p .silent origin T).x j (.m q) < 1
  charge_margin : (readyProtectedEnd θ s i p .silent origin T).x i .q ≤ 24 / 25

theorem silent_leg_exists {n : ℕ} {θ : Fin n → Parameters} {s : Snapshot n}
    {i : Fin n} {p : Port} {origin : Option ℝ} {T : ℝ}
    (hT : s.time < T) (hm : ∀ j, s.main j = .ready) (ha : s.aux i p = .silent)
    (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw i p = origin) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hq0 : ∀ j, s.x j .q < 1)
    (hm0 : ∀ j q, j ≠ i ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : ∀ t ∈ Icc s.time T, readyPulse (s.x i .q)
      (Real.exp (s.x i (.z p)) * rawInputScale origin s.time) s.time t ≤ 24 / 25)
    (hx : ∀ t ∈ Ico s.time T, 1 / 10 < s.x i (.m p) * Real.exp (-(θ i).ls p * (t - s.time)))
    (hp : ∀ d ∈ s.pending, T ≤ d.due) : Nonempty (SilentLeg θ s i p origin T) := by
  let flow := readyProtectedFlow s i p .silent origin hT (Or.inr rfl) hm ha hao hr ho
    hsupport hq0 hm0 (fun t ht => by linarith [hq t ⟨ht.1,ht.2.le⟩])
    (by simpa only [reduceCtorEq,ite_false,protectedReadyRate] using hx) hp
  refine ⟨⟨flow,?_,?_,?_⟩⟩
  · intro j
    by_cases hj : j = i
    · subst j
      change readyPulse (s.x i .q) (protectedRawAmplitude s i p origin i) s.time T < 1
      simp only [protectedRawAmplitude,ite_true]
      linarith [hq T ⟨hT.le,le_rfl⟩]
    · change readyPulse (s.x j .q) (protectedRawAmplitude s i p origin j) s.time T < 1
      rw [protectedRawAmplitude,ite_eq_right hj,readyPulse_zero_eq_relax]
      exact relax_lt (by norm_num) hT.le (hq0 j) (by norm_num)
  · intro j q hh
    have hne : ¬ (j = i ∧ q = p) := by tauto
    change (if j = i ∧ q = p then _ else _) < 1
    rw [ite_eq_right hne]
    exact relax_lt (by norm_num) hT.le (hm0 j q hh) (by norm_num)
  · change readyPulse (s.x i .q) (protectedRawAmplitude s i p origin i) s.time T ≤ 24 / 25
    simpa only [protectedRawAmplitude,ite_true] using hq T ⟨hT.le,le_rfl⟩

theorem FirstInputSilent.raw_leg_exists {n θ ε s i p T} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (hb : PhysicalBox θ ε)
    (hqi : s.x i .q ≤ 10001 / 100000) (hg : Real.exp (s.x i (.z p)) ≤ 4 / 3)
    (hp : ∀ d ∈ s.pending, s.time + 2 ≤ d.due)
    (hT : g.final.time < T) (hTE : T ≤ g.errorDate) (hTR : T ≤ s.time + 1) :
    Nonempty (SilentLeg θ g.final i p (some s.time) T) := by
  have hs : s.time ≤ g.final.time := by
    change s.time ≤ s.time + f.latency + Real.log (5 / 4) / (θ i).lm p
    linarith [f.early,(hb.aux_durations_positive i p).1]
  apply silent_leg_exists hT g.main_ready g.aux_silent g.aux_other g.raw_active g.raw_other
    (by intro o he; have ho : o = s.time := (Option.some.inj he).symm; subst o; exact ⟨hs,hTR⟩)
    g.main_below g.aux_below
  · intro t ht
    rw [g.response_restart]
    exact readyPulse_first_weak_margin hqi hg (hs.trans ht.1)
  · intro t ht
    rw [g.sensor_charge]
    have hend := silent_full_decay_end (start := g.final.time) (ne_of_gt (hb.rates_positive i p).2.1)
    change (4 / 5 : ℝ) * Real.exp (-(θ i).ls p * (g.errorDate - g.final.time)) = 1 / 10 at hend
    rw [← hend]
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    apply Real.exp_lt_exp.mpr
    have htime : t < g.errorDate := ht.2.trans_le hTE
    nlinarith [(hb.rates_positive i p).2.1]
  · intro d hd
    rw [g.queue_preserved] at hd
    linarith [hp d hd]

structure FirstInputError {n θ s i p} {f : @FirstInputMark n θ s i p}
    (route : Router n) (g : FirstInputSilent f) where
  beforeError : Snapshot n
  span : Execution θ route g.final beforeError
  span_deliveries : span.deliveries = []
  span_emissions : span.ledger.emissions = []
  date : beforeError.time = g.errorDate
  main_before : ∀ j, beforeError.main j = .ready
  silent_before : beforeError.aux i p = .silent
  other_before : ∀ j q, j ≠ i ∨ q ≠ p → beforeError.aux j q = .ready
  sensor_before : beforeError.x i (.m p) = 1 / 10
  main_below : ∀ j, beforeError.x j .q < 1
  aux_below : ∀ j q, j ≠ i ∨ q ≠ p → beforeError.x j (.m q) < 1
  charge_margin : beforeError.x i .q ≤ 24 / 25
  pending : beforeError.pending = s.pending
  gain_preserved : ∀ j q, beforeError.x j (.z q) = s.x j (.z q)
  recovery_preserved : ∀ j, beforeError.x j .b = s.x j .b
  raw_option : (beforeError.raw i p = some s.time ∧ beforeError.time < s.time + 1) ∨
    (beforeError.raw i p = none ∧ s.time + 1 ≤ beforeError.time)
  raw_other : ∀ j q, j ≠ i ∨ q ≠ p → beforeError.raw j q = none

noncomputable def FirstInputError.final {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) : Snapshot n := setAux h.beforeError i p .error

noncomputable def FirstInputError.execution {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) : Execution θ route g.final h.final :=
  h.span.append (.cons (.jump (.error _ i p h.silent_before h.sensor_before)) (.nil _))

theorem FirstInputError.error_date_exact {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) : h.final.time = g.final.time + Real.log 8 / (θ i).ls p := h.date

theorem FirstInputError.initialmode {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) : h.final.aux i p = .error := by simp [FirstInputError.final,setAux]

theorem FirstInputError.sensor_charge {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) : h.final.x i (.m p) = 1 / 10 := h.sensor_before

theorem FirstInputError.main_ready {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) (j : Fin n) : h.final.main j = .ready := h.main_before j

theorem FirstInputError.aux_other {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) (j : Fin n) (q : Port)
    (hh : j ≠ i ∨ q ≠ p) : h.final.aux j q = .ready := by
  rcases hh with hj | hq
  · simpa [FirstInputError.final,setAux,hj] using h.other_before j q (Or.inl hj)
  · by_cases hj : j = i
    · subst j
      simpa [FirstInputError.final,setAux,hq] using h.other_before i q (Or.inr hq)
    · simpa [FirstInputError.final,setAux,hj] using h.other_before j q (Or.inl hj)

theorem FirstInputError.error_date_lower {n θ ε s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) (hb : PhysicalBox θ ε) :
    s.time + 99 / 100 < h.final.time := by rw [h.error_date_exact]; exact (g.errorDate_bounds hb).1

theorem FirstInputError.error_date_upper {n θ ε s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) (hb : PhysicalBox θ ε) :
    h.final.time < s.time + 123 / 100 := by rw [h.error_date_exact]; exact (g.errorDate_bounds hb).2

theorem FirstInputError.deliveries {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) : h.execution.deliveries = [] := by
  simp only [FirstInputError.execution,Execution.deliveries_append,h.span_deliveries,
    Execution.deliveries,Move.deliveries,Jump.deliveries,List.nil_append]

theorem FirstInputError.emissions {n θ s i p route} {f : @FirstInputMark n θ s i p}
    {g : FirstInputSilent f} (h : FirstInputError route g) : h.execution.ledger.emissions = [] := by
  simp only [FirstInputError.execution,Execution.emissions_append,h.span_emissions,
    Execution.ledger,Move.ledger,Jump.ledger,Ledger.add,Ledger.zero,List.nil_append]

theorem raw_update_other {n} (s : Snapshot n) (i : Fin n) (p : Port) (value : Option ℝ)
    (j : Fin n) (q : Port) (hh : j ≠ i ∨ q ≠ p) : (setRaw s i p value).raw j q = s.raw j q := by
  rcases hh with hj | hq
  · simp [setRaw,hj]
  · by_cases hj : j = i
    · subst j; simp [setRaw,hq]
    · simp [setRaw,hj]

/-- Construct the SILENT phase, splitting at the actual raw expiry if needed.
The equality case consumes raw before entering ERROR; both orders are legal. -/
theorem FirstInputSilent.first_error_exists {n θ ε s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (route : Router n) (hb : PhysicalBox θ ε)
    (hqi : s.x i .q ≤ 10001 / 100000) (hg : Real.exp (s.x i (.z p)) ≤ 4 / 3)
    (hp : ∀ d ∈ s.pending, s.time + 2 ≤ d.due) : Nonempty (FirstInputError route g) := by
  have hpos := g.errorDate_positive hb
  have hrate := (hb.rates_positive i p).2.1
  have hfinalRawTime : g.final.time < s.time + 1 := by rw [g.date]; linarith [g.deadline]
  by_cases hE : g.errorDate ≤ s.time + 1
  · obtain ⟨leg⟩ := g.raw_leg_exists hb hqi hg hp hpos le_rfl hE
    let before := readyProtectedEnd θ g.final i p .silent (some s.time) g.errorDate
    have hthreshold : before.x i (.m p) = 1 / 10 := by
      simpa [before,readyProtectedEnd,readyProtectedValues,protectedReadyRate,g.sensor_charge,
        FirstInputSilent.errorDate] using silent_full_decay_end (start := g.final.time) (ne_of_gt hrate)
    by_cases hearly : g.errorDate < s.time + 1
    · exact ⟨{
        beforeError := before
        span := .cons (.flow leg.flow) (.nil _)
        span_deliveries := rfl
        span_emissions := rfl
        date := rfl
        main_before := g.main_ready
        silent_before := g.aux_silent
        other_before := g.aux_other
        sensor_before := hthreshold
        main_below := leg.main_below
        aux_below := leg.aux_below
        charge_margin := leg.charge_margin
        pending := g.queue_preserved
        gain_preserved := g.gain_preserved
        recovery_preserved := g.recovery_preserved
        raw_option := Or.inl ⟨g.raw_active,hearly⟩
        raw_other := g.raw_other
      }⟩
    · have heq : g.errorDate = s.time + 1 := le_antisymm hE (le_of_not_gt hearly)
      let expired := setRaw before i p none
      let expiry := rawExpiryJump (route := route) before i p s.time g.raw_active heq
      refine ⟨{
        beforeError := expired
        span := .cons (.flow leg.flow) (.cons (.jump expiry) (.nil _))
        span_deliveries := rfl
        span_emissions := rfl
        date := rfl
        main_before := g.main_ready
        silent_before := g.aux_silent
        other_before := g.aux_other
        sensor_before := hthreshold
        main_below := leg.main_below
        aux_below := leg.aux_below
        charge_margin := leg.charge_margin
        pending := g.queue_preserved
        gain_preserved := g.gain_preserved
        recovery_preserved := g.recovery_preserved
        raw_option := Or.inr ⟨by simp [expired,setRaw],heq.ge⟩
        raw_other := ?_
      }⟩
      intro j q hh
      rw [raw_update_other _ _ _ _ _ _ hh]
      exact g.raw_other j q hh
  · have hRE : s.time + 1 < g.errorDate := lt_of_not_ge hE
    obtain ⟨first⟩ := g.raw_leg_exists hb hqi hg hp hfinalRawTime hRE.le le_rfl
    let middle := readyProtectedEnd θ g.final i p .silent (some s.time) (s.time + 1)
    let expired := setRaw middle i p none
    have hraw : expired.raw i p = none := by simp [expired,setRaw]
    have hother : ∀ j q, j ≠ i ∨ q ≠ p → expired.raw j q = none := by
      intro j q hh
      rw [raw_update_other _ _ _ _ _ _ hh]
      exact g.raw_other j q hh
    have hm : ∀ j, expired.main j = .ready := g.main_ready
    have ha : expired.aux i p = .silent := g.aux_silent
    have hao : ∀ j q, j ≠ i ∨ q ≠ p → expired.aux j q = .ready := g.aux_other
    have hsensor : expired.x i (.m p) =
        (4 / 5 : ℝ) * Real.exp (-(θ i).ls p * (s.time + 1 - g.final.time)) := by
      simp [expired,middle,readyProtectedEnd,readyProtectedValues,protectedReadyRate,g.sensor_charge,setRaw]
    have hsensorpos : 0 < expired.x i (.m p) := by rw [hsensor]; positivity
    have hend : expired.x i (.m p) * Real.exp (-(θ i).ls p * (g.errorDate - expired.time)) = 1 / 10 := by
      rw [hsensor,mul_assoc,← Real.exp_add]
      change (4 / 5 : ℝ) * Real.exp
        (-(θ i).ls p * (s.time + 1 - g.final.time) + -(θ i).ls p * (g.errorDate - (s.time + 1))) = _
      rw [show -(θ i).ls p * (s.time + 1 - g.final.time) +
        -(θ i).ls p * (g.errorDate - (s.time + 1)) = -(θ i).ls p * (g.errorDate - g.final.time) by ring]
      exact silent_full_decay_end (start := g.final.time) (ne_of_gt hrate)
    have hqnone : ∀ t ∈ Icc expired.time g.errorDate, readyPulse (expired.x i .q)
        (Real.exp (expired.x i (.z p)) * rawInputScale none expired.time) expired.time t ≤ 24 / 25 := by
      intro t ht
      simp only [rawInputScale,mul_zero,readyPulse_zero_eq_relax]
      have hmargin : expired.x i .q ≤ 24 / 25 := first.charge_margin
      have hc := decay_upper (show expired.x i .q - 1 / 10 ≤ (43 / 50 : ℝ) by
        linarith) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (sub_nonneg.mpr ht.1)
      unfold relax
      linarith
    have hxnone : ∀ t ∈ Ico expired.time g.errorDate,
        1 / 10 < expired.x i (.m p) * Real.exp (-(θ i).ls p * (t - expired.time)) := by
      intro t ht
      rw [← hend]
      apply mul_lt_mul_of_pos_left _ hsensorpos
      apply Real.exp_lt_exp.mpr
      nlinarith [ht.2]
    obtain ⟨last⟩ := silent_leg_exists (show expired.time < g.errorDate from hRE) hm ha hao hraw hother
      (by intro o ho; contradiction) first.main_below first.aux_below hqnone hxnone (by
        intro d hd
        change d ∈ g.final.pending at hd
        rw [g.queue_preserved] at hd
        linarith [hp d hd,(g.errorDate_bounds hb).2])
    let before := readyProtectedEnd θ expired i p .silent none g.errorDate
    let expiry := rawExpiryJump (route := route) middle i p s.time g.raw_active rfl
    exact ⟨{
      beforeError := before
      span := .cons (.flow first.flow) (.cons (.jump expiry) (.cons (.flow last.flow) (.nil _)))
      span_deliveries := rfl
      span_emissions := rfl
      date := rfl
      main_before := hm
      silent_before := ha
      other_before := hao
      sensor_before := by
        simpa [before,readyProtectedEnd,readyProtectedValues,protectedReadyRate] using hend
      main_below := last.main_below
      aux_below := last.aux_below
      charge_margin := last.charge_margin
      pending := g.queue_preserved
      gain_preserved := g.gain_preserved
      recovery_preserved := g.recovery_preserved
      raw_option := Or.inr ⟨hraw,hRE.le⟩
      raw_other := hother
    }⟩

end KernelR.Hybrid
