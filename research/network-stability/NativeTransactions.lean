import NativeAdmissions

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid

/-- Each list entry starts at an actual active source and ends at the next
actual same-cell arrival cut or the terminal cut. Other cells' events remain
in the execution. The FIRE list is exact, including its native dates. -/
inductive PreparedTransactions {n θ route} (i : Fin n) (p : Port) :
    {s u : Snapshot n} → Execution θ route s u → List (ℝ × ℝ) → Prop where
  | last {s u} {e : Execution θ route s u}
      (active : s.raw i p = some s.time) (ready : PreparedSection s i)
      (isolated : e.cellDeliveries i = []) (pulse : LearnedPulse e i) :
      PreparedTransactions i p e [(s.time, pulse.trigger.beforeFire.time)]
  | next {s u} {e : Execution θ route s u} {token : Delivery n} {later : List (Delivery n)}
      (cut : CellDeliveryStep e i token later)
      (active : s.raw i p = some s.time) (ready : PreparedSection s i)
      (pulse : LearnedPulse cut.span i)
      {rest} (tail : PreparedTransactions i p cut.rest rest) :
      PreparedTransactions i p e ((s.time, pulse.trigger.beforeFire.time) :: rest)

/-- The per-occurrence pulse certificate has zero physical ledger dose in
every gain coordinate and in recovery. -/
theorem prepared_pulse_zero_doses {n θ route s u i} {e : @Execution n θ route s u}
    (pulse : LearnedPulse e i) :
    (∀ q, e.ledger.error i q = 0 ∧ e.ledger.mark i q = 0) ∧
      e.ledger.recovery i = 0 := by
  refine ⟨fun q => ⟨pulse.error_zero q, pulse.mark_zero q⟩, ?_⟩
  have balance := e.recovery_balance i
  rw [pulse.recovery_preserved] at balance
  linarith

theorem PreparedTransactions.fire_word {n θ route s u i p} {e : @Execution n θ route s u}
    {word} (h : PreparedTransactions i p e word) :
    e.emissionTimes i = word.map Prod.snd := by
  induction h with
  | last _ _ _ pulse => exact pulse.emissions
  | next cut _ _ pulse _ ih =>
    rw [cut.emissions, pulse.emissions, ih]
    rfl

/-- Each certified span supplies its endpoint clock and exact issued contact
list at the native FIRE date. An empty route gives an empty list. -/
structure PreparedResponse (n : Nat) where
  admitted : ℝ
  fired : ℝ
  completed : ℝ
  issued : List (Delivery n)

theorem PreparedTransactions.responses {n θ route s u i p} {e : @Execution n θ route s u}
    {word} (h : PreparedTransactions i p e word) :
    ∃ responses : List (PreparedResponse n),
      responses.map (fun r => (r.admitted, r.fired)) = word ∧
      responses.Pairwise (fun a b => a.completed ≤ b.admitted) ∧
      (∀ r ∈ responses, r.admitted ≤ r.fired ∧ r.fired ≤ r.completed ∧
        r.completed ≤ u.time ∧ r.issued = route i r.fired) := by
  have fireBounds {s u : Snapshot n} {run : Execution θ route s u} {fire : ℝ}
      (word : run.emissionTimes i = [fire]) : s.time ≤ fire ∧ fire ≤ u.time := by
    have member : fire ∈ run.emissionTimes i := by rw [word]; simp
    obtain ⟨event, seen, time⟩ := List.mem_map.mp member
    have bounds := run.emission_time_bounds event (List.mem_of_mem_filter seen)
    simpa only [time] using bounds
  induction h with
  | last _ _ _ pulse =>
    let fire := pulse.trigger.beforeFire.time
    exact ⟨[⟨_, fire, _, route i fire⟩], rfl, by simp, by
      intro r mem
      cases List.mem_singleton.mp mem
      exact ⟨(fireBounds pulse.emissions).1, (fireBounds pulse.emissions).2, le_rfl, rfl⟩⟩
  | @next start finish run token later cut _ _ pulse residual tail ih =>
    let fire := pulse.trigger.beforeFire.time
    obtain ⟨rest, wordEq, chronology, bounds⟩ := ih
    refine ⟨⟨start.time, fire, cut.beforeArrival.time, route i fire⟩ :: rest,
      by simp only [List.map_cons, wordEq, fire], ?_, ?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_, chronology⟩
      intro r hr
      have noEarlier {s u : Snapshot n} {e : Execution θ route s u} {word}
          (tail : PreparedTransactions i p e word) :
          ∀ pair ∈ word, s.time ≤ pair.1 := by
        intro pair mem
        induction tail with
        | last => simpa using congrArg Prod.fst (List.mem_singleton.mp mem).symm |>.le
        | next cut' _ _ _ tail' ih' =>
          rcases List.mem_cons.mp mem with rfl | later
          · exact le_rfl
          · exact cut'.span.time_monotone.trans
              (cut'.entry.time_unchanged.ge.trans (ih' later))
      have mem : (r.admitted, r.fired) ∈ residual := by
        rw [← wordEq]
        exact List.mem_map.mpr ⟨r, hr, rfl⟩
      exact cut.entry.time_unchanged.ge.trans (noEarlier tail _ mem)
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | later
      · exact ⟨(fireBounds pulse.emissions).1, (fireBounds pulse.emissions).2,
          cut.entry.time_unchanged.ge.trans cut.rest.time_monotone, rfl⟩
      · exact bounds r later

/-- Retain the individual certificates that the native prepared-train
induction uses. The dose equality and phase at each receipt are attached to
the corresponding actual span, rather than inferred from an aggregate. -/
theorem prepared_transactions {n θ ε route} (box : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (times : List ℝ) {s u : Snapshot n}
    (e : Execution θ route s u) (region : UpperRegion s) (valid : RawValid s)
    (prepared : PreparedSection s i)
    (gain : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (active : s.raw i p = some s.time) (other : ∀ q, q ≠ p → s.raw i q = none)
    (calendar : e.cellDeliveries i = times.map (fun t => ⟨i, p, t⟩))
    (spacing : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (horizon : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time) :
    ∃ word, word.map Prod.fst = s.time :: times ∧ PreparedTransactions i p e word := by
  induction times generalizing s u with
  | nil =>
    have no := (e.cellDeliveries_empty_iff i).mp (by simpa using calendar)
    obtain ⟨pulse⟩ := e.learned_mid_pulse_of_valid box region valid i p prepared gain active other
      no (horizon s.time (by simp))
    exact ⟨[(s.time, pulse.trigger.beforeFire.time)], rfl, .last active prepared (by simpa using calendar) pulse⟩
  | cons t times ih =>
    obtain ⟨cut⟩ := e.first_cell_delivery i ⟨i, p, t⟩ _ (by simpa using calendar)
    have gap := (List.pairwise_cons.mp spacing).1 t (by simp)
    obtain ⟨pulse⟩ := cut.span.learned_mid_pulse_of_valid box region valid i p prepared gain active other
      cut.no_arrivals_before (by rw [cut.date.1]; exact gap)
    have gain' : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by
      rw [cut.entry.physical_continuous, pulse.gain_preserved p]
      exact gain
    have other' : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    obtain ⟨word, dates, tail⟩ := ih cut.rest (advanced.upper_region box region)
      (advanced.raw_valid valid) (cut.prepared pulse.prepared) gain' cut.raw_after other' cut.later
      (by rw [cut.date.2]; exact (List.pairwise_cons.mp spacing).2)
      (by rw [cut.date.2]; exact fun t mem => horizon t (List.mem_cons_of_mem _ mem))
    refine ⟨(s.time, pulse.trigger.beforeFire.time) :: word, ?_, .next cut active prepared pulse tail⟩
    simp only [List.map_cons, dates, cut.date.2]


private theorem source_spacing (first : ℝ) (count : Nat) :
    (first :: List.ofFn (fun k : Fin count => first + 8 + 8 * (k.val : ℝ))).Pairwise
      (fun a b => a + 15 / 2 ≤ b) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro b mem
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp mem
    linarith [Nat.cast_nonneg (α := ℝ) k.val]
  · apply List.pairwise_ofFn.mpr
    intro k l less
    have h : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr less)
    linarith

/-- The 13 learned A occurrences of the actual forward train each have
an exact READY admission, one FIRE, and zero gain and recovery dose. -/
theorem nominal_forward_sender_transactions :
    ∃ (s u : Snapshot 2) (run : Execution
      (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
      (reciprocalEntryRouter nominalDelay nominalDelay) s u) (word : List (ℝ × ℝ)),
      s.time = 184 ∧ u.time = 288 ∧ word.length = 13 ∧
        PreparedTransactions 0 0 run word ∧ run.emissionTimes 0 = word.map Prod.snd := by
  have born : BirthState nominalStart := Newborn.nominal_birth_state
  have delay : ∀ t, (3 / 10 : ℝ) ≤ nominalDelay t ∧ nominalDelay t ≤ 2 / 5 := by
    intro t
    norm_num [nominalDelay]
  obtain ⟨_, _, _, _, _, _, _, _, _, x, z, _, _, _, _⟩ :=
    birth_protocol_first_coupled_teaching_exists (born := nominalStart) born nominal_box
      (fun _ => rfl) rfl Newborn.nominal nominalDelay nominalDelay delay
  let times := List.ofFn (fun k : Fin 12 => x.final.time + 8 + 8 * (k.val : ℝ))
  have hdate : z.train.final.time = (288 : ℝ) := by rw [z.train.date, x.date]; norm_num
  have hz := x.learned_gain_a nominal_box.extend_old
  obtain ⟨word, dates, evidence⟩ := prepared_transactions nominal_box 0 0 times z.train.execution
    x.physical.region x.raw_valid (x.prepared 0) ⟨hz.1, by linarith [hz.2]⟩
    (by rw [x.date]; exact x.raw_active) (fun q h => x.raw_other 0 q (Or.inr h))
    (by simpa only [times, sourceTrain, List.map_ofFn, Function.comp_def] using z.train.a_deliveries)
    (source_spacing _ _) (by
      intro t mem
      rcases List.mem_cons.mp mem with rfl | inside
      · rw [x.date, hdate]
        norm_num
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp inside
        have kBound : (k.val : ℝ) ≤ 11 := by exact_mod_cast (show k.val ≤ 11 by omega)
        change x.final.time + 8 + 8 * (k.val : ℝ) + 15 / 2 ≤ z.train.final.time
        rw [x.date, hdate]
        linarith)
  have length := congrArg List.length dates
  simp [times] at length
  exact ⟨_, _, z.train.execution, word, x.date, hdate, length, evidence, evidence.fire_word⟩


/-- The nine B source occurrences on the reverse learned suffix each
reopen with zero dose and contribute their own FIRE. -/
theorem nominal_reverse_sender_transactions :
    ∃ (s u : Snapshot 2) (run : Execution
      (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
      (reciprocalEntryRouter nominalDelay nominalDelay) s u) (word : List (ℝ × ℝ)),
      s.time = 376 ∧ u.time = 4599 / 10 ∧ word.length = 9 ∧
        PreparedTransactions 1 2 run word ∧ run.emissionTimes 1 = word.map Prod.snd := by
  have born : BirthState nominalStart := Newborn.nominal_birth_state
  have delay : ∀ t, (3 / 10 : ℝ) ≤ nominalDelay t ∧ nominalDelay t ≤ 2 / 5 := by
    intro t
    norm_num [nominalDelay]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, z, w, a, q, p, _, _, _, _, _, _⟩ :=
    birth_protocol_first_reverse_interleaved_pair_exists (born := nominalStart) born nominal_box
      (fun _ => rfl) rfl Newborn.nominal nominalDelay nominalDelay delay delay
  have hzA : Real.log (3 / 10) - 1 / 100000 ≤ q.final.x 0 (.z 2) ∧
      q.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [z.first_reverse_wire_a_gain_own nominal_box.extend_old q 2 (by decide)]
    simpa only [nominalGain, show (2 : Port) ≠ 1 by decide, ite_false]
      using ((born.2.2 0).2.2.2.2 (2 : Port)).1
  have hzB : Real.log (3 / 10) - 1 / 100000 ≤ Newborn.nominal.x (.z 2) ∧
      Newborn.nominal.x (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    simpa only [nominalGain, show (2 : Port) ≠ 1 by decide, ite_false]
      using Newborn.nominal.gain (2 : Port)
  have hGB : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2 := by
    rw [z.feedback_weak_b_gain_own w]
    exact learned_gain_bounds (by linarith [hzB.1]) (by linarith [hzB.2])
  obtain ⟨finish⟩ := reverse_teaching_completion_exists p nominal_box hzA hGB delay
  let s := finish.entry.final
  let run := finish.epoch.execution
  let times := List.ofFn (fun k : Fin 8 => s.time + 8 + 8 * (k.val : ℝ))
  have box : PhysicalBox (extendParameters a.parametersA (a.parametersB 0)) (1 / 10) := by
    rw [a.parameters_product]
    exact nominal_box
  have region : UpperRegion s := finish.entry.physical.region
  have gain : 9 / 5 ≤ Real.exp (s.x 1 (.z 2)) ∧ Real.exp (s.x 1 (.z 2)) ≤ 12 / 5 := by
    change 9 / 5 ≤ Real.exp (finish.entry.final.x 1 (.z 2)) ∧ _
    rw [finish.entry.b_gains, p.b_gains]
    exact ⟨hGB.1, by linarith [hGB.2]⟩
  obtain ⟨word, dates, evidence⟩ := prepared_transactions box 1 2 times run region
    finish.entry.raw_valid (finish.entry.prepared 1) gain finish.entry.raw_active
    (fun port h => finish.entry.raw_other 1 port (Or.inr h))
    (by
      change finish.epoch.execution.cellDeliveries 1 = _
      rw [finish.epoch.b_deliveries]
      simp only [times, s, finish.entry.date, sourceTrain, List.map_ofFn, Function.comp_def]
      norm_num)
    (source_spacing _ _) (by
      intro t mem
      rcases List.mem_cons.mp mem with rfl | inside
      · change finish.entry.final.time + 15 / 2 ≤ finish.epoch.final.time
        rw [finish.entry.date, finish.epoch.date]
        norm_num
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp inside
        have kBound : (k.val : ℝ) ≤ 7 := by exact_mod_cast (show k.val ≤ 7 by omega)
        change finish.entry.final.time + 8 + 8 * (k.val : ℝ) + 15 / 2 ≤ finish.epoch.final.time
        rw [finish.entry.date, finish.epoch.date]
        linarith)
  have length := congrArg List.length dates
  simp [times] at length
  have projected : PreparedTransactions 1 2
      (run.cast_parameters a.parameters_product) word := by
    revert evidence
    generalize a.parameters_product = equal
    cases equal
    exact id
  exact ⟨_, _, run.cast_parameters a.parameters_product, word, finish.entry.date, finish.epoch.date,
    length, projected, projected.fire_word⟩

end NetworkStability.NativeReciprocal
