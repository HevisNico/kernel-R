import NativeTransactions
import KernelR.HybridResetRate

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid

/-- The FAST clock is fixed at one unit. With lower and upper bounds on
the actual recovery rate, these are the two possible limits on reopening. -/
noncomputable def reopenWindow (fire lower upper : ℝ) : ℝ × ℝ :=
  (fire + 1 + Real.log (5 / 2) / upper, fire + 1 + Real.log (5 / 2) / lower)

theorem slow_persists_before_earliest_reopen {n θ route s u}
    (run : @Execution n θ route s u) (i : Fin n) (upper : ℝ) (positive : 0 < upper)
    (slow : s.main i = .slow) (charge : s.x i .q = 1 / 4)
    (rate : run.RecoveryBound i upper)
    (early : u.time < s.time + Real.log (5 / 2) / upper) :
    run.AllStates (fun v => v.main i = .slow) := by
  rcases run.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) slow with kept |
      ⟨v, w, head, exit, tail, shape, stays, before, after⟩
  · exact kept
  · have bound := rate
    unfold Execution.RecoveryBound at bound
    rw [shape, Execution.allFlows_append] at bound
    have elapsed := head.slow_duration_lower_of_bound i upper positive
      (head.allStates_main_flows i .slow stays) charge
      (exit.slow_departure_guard i before after) bound.1
    have chronology := tail.time_monotone
    rw [exit.time_unchanged] at chronology
    exact (by linarith : False).elim

/-- A receipt strictly past the latest return is READY if the same cell
has no intervening FIRE. Native jumps preserve the mode of an arrival. -/
theorem ready_after_latest_reopen {n θ ε route s u}
    (run : @Execution n θ route s u) (box : PhysicalBox θ ε) (i : Fin n)
    (lower : ℝ) (positive : 0 < lower) (slow : s.main i = .slow)
    (charge : s.x i .q = 1 / 4) (rate : lower ≤ s.x i .b)
    (late : s.time + Real.log (5 / 2) / lower < u.time)
    (silent : run.emissionTimes i = []) : u.main i = .ready := by
  obtain ⟨v, w, head, exit, tail, shape, _, ready, _, _⟩ :=
    run.slow_phase_completion box i slow charge lower positive rate late
  have none : tail.emissionTimes i = [] := by
    rw [shape, Execution.emissionTimes_append] at silent
    have suffix := (List.append_eq_nil_iff.mp silent).2
    rw [Execution.emissionTimes_cons] at suffix
    exact (List.append_eq_nil_iff.mp suffix).2
  exact tail.allStates_final (tail.ready_states_of_no_emissions i ready none)


/-- A calendar phase can be predicted on either side of the uncertain
reopening window. The SLOW interval starts strictly after the FAST exit. -/
noncomputable def predictAfterFire (fire lower upper date : ℝ) : Option PhaseAdmission.Phase :=
  if fire + 1 < date ∧ date < (reopenWindow fire lower upper).1 then some .slow
  else if (reopenWindow fire lower upper).2 < date then some .ready
  else none

theorem predicted_phase_after_fire {n θ ε route s u} (run : @Execution n θ route s u)
    (box : PhysicalBox θ ε) (i : Fin n) {fire lower upper : ℝ}
    (fastEnd : s.time = fire + 1) (slow : s.main i = .slow) (charge : s.x i .q = 1 / 4)
    (lowerPos : 0 < lower) (upperPos : 0 < upper)
    (rateLower : lower ≤ s.x i .b) (rateUpper : run.RecoveryBound i upper)
    (silent : run.emissionTimes i = []) :
    (predictAfterFire fire lower upper u.time = some .slow → u.main i = .slow) ∧
    (predictAfterFire fire lower upper u.time = some .ready → u.main i = .ready) := by
  unfold predictAfterFire reopenWindow
  split_ifs with early late
  · exact ⟨fun _ => run.allStates_final
      (slow_persists_before_earliest_reopen run i upper upperPos slow charge rateUpper
        (by rw [fastEnd]; exact early.2)), by simp⟩
  · exact ⟨by simp, fun _ => ready_after_latest_reopen run box i lower lowerPos slow charge
      rateLower (by rw [fastEnd]; exact late) silent⟩
  · simp

/-- A low-recovery first firing leaves the third forward arrival strictly
inside SLOW. The numeric window uses the native allowable latency and
recovery bands, and does not query the arrival mode. -/
theorem low_recovery_window {source latency arrival recovery : ℝ}
    (low : 7999 / 100000 ≤ recovery ∧ recovery ≤ 8001 / 100000)
    (latencyBounds : 2 / 5 < latency ∧ latency < 9 / 10)
    (gap : source + 79 / 10 ≤ arrival ∧ arrival ≤ source + 81 / 10) :
    predictAfterFire (source + latency) recovery recovery arrival = some .slow := by
  have fastFinished : source + latency + 1 < arrival := by linarith [latencyBounds.2, gap.1]
  have decay := (variable_gap_first_slow_charge low latencyBounds gap).1
  rw [neg_mul] at decay
  have positive : 0 < recovery := by linarith [low.1]
  have compare : Real.exp (-Real.log (5 / 2)) <
      Real.exp (-recovery * (arrival - (source + latency + 1))) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]
    norm_num
    linarith
  have rate : recovery * (arrival - (source + latency + 1)) < Real.log (5 / 2) := by
    have h := Real.exp_lt_exp.mp compare
    linarith
  have slowBefore : arrival < (reopenWindow (source + latency) recovery recovery).1 := by
    have h := (lt_div_iff₀ positive).2 (by simpa [mul_comm] using rate)
    unfold reopenWindow
    linarith
  simp [predictAfterFire, fastFinished, slowBefore]


/-- The actual third forward token is classified by the preceding
source, native latency and recovery bound, with no mode lookup. -/
theorem third_forward_predicted_slow {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {p : FirstInterleavedPair r} {v : SecondWiredArrival p}
    {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
    (t : ThirdWiredArrival u)
    (delay : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    predictAfterFire (v.receiverFireLocal.time + f.firelocal.latency)
      (v.receiverFireLocal.x 0 .b) (v.receiverFireLocal.x 0 .b) t.final.time = some .slow := by
  apply low_recovery_window t.receiverSpan.initial_low_b t.receiverSpan.firing_bounds
  have upper := t.receiverSpan.horizon_upper
  rw [t.date]
  have first : v.receiverFireLocal.time = v.final.time := rfl
  have bound := (t.received_gap delay).1
  rw [t.date] at bound
  exact ⟨by rw [first]; linarith, upper⟩


/-- Clock certificate for the prepared train. The absolute bound comes
from the native FAST and SLOW guards. Each next admission is past it,
and the single FIRE word excludes any new FAST before that admission. -/
theorem PreparedTransactions.return_windows {n θ route s u i p}
    {run : @Execution n θ route s u} {word}
    (certified : PreparedTransactions i p run word)
    (gaps : word.Pairwise (fun a b => a.1 + 15 / 2 ≤ b.1)) :
    ∃ dates : List ℝ, dates.length = word.length ∧
      (word.zip dates).Pairwise (fun a b => a.2 < b.1.1) ∧
      ∀ item ∈ word.zip dates, item.2 < item.1.1 + 6990787 / 1000000 := by
  induction certified with
  | last _ _ _ pulse =>
    refine ⟨[pulse.admission_return.afterReturn.time], rfl, by simp, ?_⟩
    intro item mem
    cases List.mem_singleton.mp mem
    exact pulse.admission_return.date
  | @next start finish e token later cut _ _ pulse rest tail ih =>
    obtain ⟨dates, length, pairwise, bounds⟩ := ih (List.pairwise_cons.mp gaps).2
    refine ⟨pulse.admission_return.afterReturn.time :: dates, by simp [length], ?_, ?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_, pairwise⟩
      intro item mem
      have inWord : item.1 ∈ rest := by
        rw [← List.map_fst_zip (Nat.le_of_eq length.symm)]
        exact List.mem_map.mpr ⟨item, mem, rfl⟩
      have date := (List.pairwise_cons.mp gaps).1 item.1 inWord
      linarith [pulse.admission_return.date]
    · intro item mem
      rcases List.mem_cons.mp mem with same | more
      · subst item
        exact pulse.admission_return.date
      · exact bounds item more

end NetworkStability.NativeReciprocal
