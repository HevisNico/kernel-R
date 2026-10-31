import KernelR.HybridFiring

/-! Exact single-output extraction for a learned isolated input, including incomplete protected phases and all later zero-input spans. -/
namespace KernelR.Hybrid
open Set

theorem Execution.allStates_mono {n θ route s u} (e : @Execution n θ route s u)
    {P Q : Snapshot n → Prop} (h : ∀ v, P v → Q v) (hp : e.AllStates P) : e.AllStates Q := by
  induction e with
  | nil => exact h _ hp
  | cons move rest ih => exact ⟨h _ hp.1,ih hp.2⟩

theorem Execution.allStates_and {n θ route s u} (e : @Execution n θ route s u)
    {P Q : Snapshot n → Prop} (hp : e.AllStates P) (hq : e.AllStates Q) :
    e.AllStates (fun v => P v ∧ Q v) := by
  induction e with
  | nil => exact ⟨hp,hq⟩
  | cons move rest ih => exact ⟨⟨hp.1,hq.1⟩,ih hp.2 hq.2⟩

theorem Execution.allStates_forall {n θ route s u α} (e : @Execution n θ route s u)
    (P : α → Snapshot n → Prop) (h : ∀ a, e.AllStates (P a)) :
    e.AllStates (fun v => ∀ a, P a v) := by
  induction e with
  | nil => exact h
  | cons move rest ih => exact ⟨fun a => (h a).1,ih (fun a => (h a).2)⟩

theorem Execution.ready_no_current_solution {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .ready) (hr : ∀ p, e.RawAbsent i p) :
    u.x i .q = 1 / 10 + (s.x i .q - 1 / 10) * Real.exp (-(1 / 2) * (u.time - s.time)) := by
  induction e with
  | nil => simp
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hrest := ih hm.2 (fun p => (hr p).2)
      have hf := f.ready_no_current_solution i hm.1 (fun p => (hr p).1) _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hf
      rw [hrest,hf]
      have he := attenuation_split (1 / 2) s.time v.time u.time
      linear_combination (s.x i .q - 1 / 10) * he
    | jump j => simpa only [j.physical_continuous,j.time_unchanged] using ih hm hr

theorem Execution.ready_without_input {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .ready) (hx : s.x i .q ≤ 1 / 10)
    (hr : ∀ p, s.raw i p = none) (hno : ∀ p, NoArrivalAt e i p) :
    e.AllStates (fun v => v.main i = .ready) := by
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
    have hraw : ∀ p, segment.RawAbsent i p := fun p =>
      (segment.raw_absent_of_no_arrival i p (hr p) (hp.no_arrival i p (hno p))).2
    have hsol := segment.ready_no_current_solution i (segment.allStates_main_flows i .ready hstates) hraw
    have hg := exit.ready_main_departure i hv hw
    have hd : (s.x i .q - 1 / 10) * Real.exp (-(1 / 2) * (v.time - s.time)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    rw [hg.1] at hsol
    linarith

theorem Jump.no_emissions_if_not_ready {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hs : s.main i ≠ .ready) :
    j.ledger.emissions.filter (fun event => event.1 = i) = [] := by
  cases j with
  | fire k hm hq =>
    by_cases hi : k = i
    · subst k; exact False.elim (hs hm)
    · simp [Jump.ledger,hi]
  | _ => rfl

theorem Execution.no_emissions_if_not_ready {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : e.AllStates (fun v => v.main i ≠ .ready)) : e.emissionTimes i = [] := by
  have hf : e.ledger.emissions.filter (fun event => event.1 = i) = [] := by
    induction e with
    | nil => rfl
    | cons move rest ih =>
      change (move.ledger.emissions ++ rest.ledger.emissions).filter _ = []
      rw [List.filter_append,ih hs.2,List.append_nil]
      cases move with
      | flow f => rfl
      | jump j => exact j.no_emissions_if_not_ready i hs.1
  simp only [Execution.emissionTimes,hf,List.map_nil]

theorem Execution.emissionTimes_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u) (i : Fin n) :
    (segment.append rest).emissionTimes i = segment.emissionTimes i ++ rest.emissionTimes i := by
  simp [emissionTimes,emissions_append,List.filter_append,List.map_append]

theorem Execution.emissionTimes_cons {n θ route s v u} (move : @Move n θ route s v)
    (rest : Execution θ route v u) (i : Fin n) :
    (Execution.cons move rest).emissionTimes i =
      (move.ledger.emissions.filter (fun event => event.1 = i)).map Prod.snd ++ rest.emissionTimes i := by
  simp [emissionTimes,ledger,Ledger.add,List.filter_append,List.map_append]

theorem Execution.no_emissions_of_split {n θ route s u v w} (e : @Execution n θ route s u)
    (segment : Execution θ route s v) (exit : Jump route v w) (rest : Execution θ route w u)
    (he : e = segment.append (.cons (.jump exit) rest)) (i : Fin n)
    (hseg : segment.emissionTimes i = [])
    (hj : exit.ledger.emissions.filter (fun event => event.1 = i) = [])
    (hrest : rest.emissionTimes i = []) : e.emissionTimes i = [] := by
  calc
    e.emissionTimes i = (segment.append (.cons (.jump exit) rest)).emissionTimes i :=
      congrArg (fun actual => actual.emissionTimes i) he
    _ = [] := by simp [emissionTimes_append,emissionTimes_cons,Move.ledger,hseg,hj,hrest]

theorem Execution.raw_expired_states {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (origin : ℝ) (hv : RawValid s)
    (hr : ∀ p, s.raw i p = none ∨ s.raw i p = some origin) (hno : ∀ p, NoArrivalAt e i p) :
    e.AllStates (fun v => origin + 1 < v.time → ∀ p, v.raw i p = none) := by
  have ha := e.allStates_forall (fun p v => v.raw i p = none ∨ v.raw i p = some origin)
    (fun p => e.raw_allowed_states i p origin (hr p) (hno p))
  refine e.allStates_mono ?_ (e.allStates_and (e.allStates_raw_valid hv) ha)
  intro v h ht p
  rcases h.2 p with hn | hr
  · exact hn
  · exact False.elim (not_lt_of_ge (h.1 i p origin hr).2 ht)

theorem Jump.slow_main_departure {n route s u} (j : @Jump n route s u) (i : Fin n)
    (hs : s.main i = .slow) (hu : u.main i ≠ .slow) : u.main i = .ready := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]

theorem Execution.slow_tail_no_emissions {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (origin : ℝ) (hs : s.main i = .slow) (ht : origin + 1 < s.time)
    (hr : e.AllStates (fun v => origin + 1 < v.time → ∀ p, v.raw i p = none))
    (hno : ∀ p, NoArrivalAt e i p) : e.emissionTimes i = [] := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.no_emissions_if_not_ready i (e.allStates_mono (fun v hv => by rw [hv]; decide) h)
  · have hraw := hr
    rw [he,Execution.allStates_append] at hraw
    have htail := hraw.2.2
    have hraw_w := rest.allStates_initial htail
    have hwtime : origin + 1 < w.time := by rw [exit.time_unchanged]; exact ht.trans_le segment.time_monotone
    have hnoRest : ∀ p, NoArrivalAt rest i p := by
      intro p
      have hn := hno p
      rw [he,Execution.noArrivalAt_append] at hn
      exact fun d hd => hn.2 d (List.mem_append_right _ hd)
    have hq : w.x i .q ≤ 1 / 10 := by rw [exit.physical_continuous,exit.slow_departure_guard i hv hw]
    have hquiet := rest.ready_without_input i (exit.slow_main_departure i hv hw) hq (hraw_w hwtime) hnoRest
    exact e.no_emissions_of_split segment exit rest he i
      (segment.no_emissions_if_not_ready i (segment.allStates_mono (fun v hv => by rw [hv]; decide) hstates))
      (exit.no_emissions_if_not_ready i (by rw [hv]; decide))
      (rest.no_emissions_of_ready_states i hquiet)

/-- A first firing after the raw origin is followed by one full FAST unit.
The raw pulse has ended before SLOW can reopen, so no second firing is possible. -/
theorem Execution.fast_tail_no_emissions {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (origin : ℝ) (hs : s.main i = .fast) (hq : s.x i .q = 1) (ht : origin < s.time)
    (hr : e.AllStates (fun v => origin + 1 < v.time → ∀ p, v.raw i p = none))
    (hno : ∀ p, NoArrivalAt e i p) : e.emissionTimes i = [] := by
  rcases e.first_state_change (fun v => v.main i) .fast
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.no_emissions_if_not_ready i (e.allStates_mono (fun v hv => by rw [hv]; decide) h)
  · have hg := exit.fast_departure_guard i hv hw
    have hd := segment.fast_duration i (segment.allStates_main_flows i .fast hstates) hq hg.1
    have hwtime : origin + 1 < w.time := by rw [exit.time_unchanged]; linarith
    have hraw := hr
    rw [he,Execution.allStates_append] at hraw
    have hnoRest : ∀ p, NoArrivalAt rest i p := by
      intro p
      have hn := hno p
      rw [he,Execution.noArrivalAt_append] at hn
      exact fun d hd => hn.2 d (List.mem_append_right _ hd)
    have hquiet := rest.slow_tail_no_emissions i origin hg.2 hwtime hraw.2.2 hnoRest
    exact e.no_emissions_of_split segment exit rest he i
      (segment.no_emissions_if_not_ready i (segment.allStates_mono (fun v hv => by rw [hv]; decide) hstates))
      (exit.no_emissions_if_not_ready i (by rw [hv]; decide)) hquiet

theorem MainTrigger.only_emission {n θ route born s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) (past : Execution θ route born s) (hborn : BirthState born)
    (p : Port) (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) : e.emissionTimes i = [tr.beforeFire.time] := by
  have hraw := e.raw_expired_states i s.time (past.raw_valid hborn.raw_valid)
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  rw [tr.reconstruct,Execution.allStates_append] at hraw
  have hnoRest : ∀ q, NoArrivalAt tr.rest i q := by
    intro q
    have hn := hno q
    rw [tr.reconstruct,Execution.noArrivalAt_append] at hn
    exact fun d hd => hn.2 d (List.mem_append_right _ hd)
  have hquiet := tr.rest.fast_tail_no_emissions i s.time tr.fast_after tr.charge
    (by linarith [tr.early]) hraw.2.2 hnoRest
  rw [tr.emission_times,hquiet]

/-- A learned isolated input emits exactly once. The first guard and the whole
remaining trace, including incomplete protected phases, determine the count. -/
theorem Execution.learned_input_single_emission {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 419 / 300 ≤ u.time) :
    ∃ date, s.time + 3 / 10 < date ∧ date < s.time + 9 / 10 ∧
      e.emissionTimes i = [date] ∧ (e.signal i).count = 1 := by
  have hi := past.upper_region hb hborn.upper_region
  obtain ⟨tr⟩ := e.learned_input_trigger hb hi i p hm hq hz ha hr hx ho hno ht
  have he := tr.only_emission past hborn p hr ho hno
  refine ⟨tr.beforeFire.time,?_,?_,he,?_⟩
  · simpa only [tr.entry.time_unchanged] using tr.early
  · simpa only [tr.entry.time_unchanged] using tr.deadline
  · rw [Execution.signal_count,he]; rfl

end KernelR.Hybrid
