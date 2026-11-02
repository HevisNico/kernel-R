import KernelR.HybridFirstReverseWiredArrival

/-! Connect the first actual reciprocal receipt to the original staged birth
trace, without a reaching execution or a receiving calendar premise. -/
namespace KernelR.Hybrid
namespace FirstReverseWiredArrival
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} (r : FirstReverseWiredArrival f)

theorem emission_times (i : Fin 2) : r.execution.emissionTimes i = [] := by
  simp [Execution.emissionTimes,r.emissions]

theorem error_zero (i : Fin 2) (p : Port) : r.execution.ledger.error i p = 0 := by
  have h := r.execution.gain_balance i p
  rw [r.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : r.execution.ledger.recovery i = 0 := by
  have h := r.execution.recovery_balance i
  rw [r.recovery] at h
  linarith

/-- The sender keeps the original B344 RAW until its real expiry. A maximal
cut consumes RAW expiry even when it coincides with the wire receipt. -/
theorem sender_raw_origin : r.final.raw 1 2 =
    if r.final.time < 345 then some (344 : ℝ) else none := by
  have hd : r.cutH.cut.deliveries = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.deliveries.symm.trans r.fast.deliveries)).1
  have hno : NoArrivalAt r.cutH.cut 0 2 := by simp [NoArrivalAt,hd]
  have hclock : r.cutH.state.time = r.final.time := r.cutH.date.trans r.date.symm
  rw [r.b_raw]
  by_cases ht : r.final.time < 345
  · rw [ite_eq_left ht]
    exact r.cutH.cut.raw_persists 0 2 344 (f.localB_raw344 0) (by rw [hclock]; linarith)
  · rw [ite_eq_right ht]
    have h := r.cutH.cut.raw_allowed_states 0 2 344 (Or.inr (f.localB_raw344 0)) hno
    rcases r.cutH.cut.allStates_final h with hn | ha
    · exact hn
    · have hs := r.cutH.raw_strict 0 2 344 ha
      have hc : r.final.time < 345 := by rw [r.date]; linarith
      exact False.elim (ht hc)

end FirstReverseWiredArrival

namespace FirstCoupledTeaching
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {v : SecondWiredArrival s}
  {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
  {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t} (z : FirstCoupledTeaching x)

noncomputable def first_reverse_wire_staged
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} (r : FirstReverseWiredArrival a) :
    StagedExecution θ fresh (fun _ _ => []) (reciprocalEntryRouter forward backward) born r.final :=
  { z.feedback_first_fire_staged a with
    after := (z.feedback_first_fire_staged a).after.append r.execution }

theorem first_reverse_wire_counts {ε} (hb : PhysicalBox θ ε)
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} (r : FirstReverseWiredArrival a) :
    ((z.first_reverse_wire_staged r).before.emissionTimes 0 ++
      (z.first_reverse_wire_staged r).after.emissionTimes 0).length = 28 ∧
      ((z.first_reverse_wire_staged r).after.emissionTimes 1).length = 15 := by
  have h := z.feedback_first_fire_counts hb a
  simpa only [first_reverse_wire_staged,Execution.emissionTimes_append,r.emission_times,List.append_nil] using h

theorem first_reverse_wire_a_gain_own {ε} (hb : PhysicalBox θ ε)
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} (r : FirstReverseWiredArrival a) (p : Port) (hp : p ≠ 0) :
    r.final.x 0 (.z p) = born.x 0 (.z p) := by
  rw [r.gains,a.gains,w.gain_other 0 p (Or.inl (by decide)),z.a_gain_other hb p hp]

theorem first_reverse_wire_b_gain_own
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} (r : FirstReverseWiredArrival a) :
    r.final.x 1 (.z 2) = newborn.x (.z 2) + 9 / 5 := by
  rw [r.gains,a.gains]
  exact z.feedback_weak_b_gain_own w

end FirstCoupledTeaching

/-- The first reverse receipt is constructed from the original birth and
actual issued wire. Counts, remaining sources and the receiving RAW follow. -/
theorem birth_protocol_first_reverse_wired_arrival_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)
    (hback : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ v : SecondWiredArrival s,
          ∃ f : FirstReceiverFire v, ∃ g : FirstReceiverFastEnd f, ∃ u : FirstPostReceiverPair g,
            ∃ t : ThirdWiredArrival u, ∃ x : FirstCoupledPreparedPair t, ∃ z : FirstCoupledTeaching x,
              ∃ w : FeedbackWeakEntry (extendParameters θ fresh)
                  (reciprocalEntryRouter forward backward) z.final,
                ∃ a : FeedbackFirstFire w, ∃ q : FirstReverseWiredArrival a,
                  CompleteThrough (z.first_reverse_wire_staged q).after q.final.time ∧
                    q.final.pending.length = 28 ∧
                    ((z.first_reverse_wire_staged q).before.emissionTimes 0 ++
                      (z.first_reverse_wire_staged q).after.emissionTimes 0).length = 28 ∧
                    ((z.first_reverse_wire_staged q).after.emissionTimes 1).length = 15 := by
  obtain ⟨c,b,r,s,v,f,g,u,t,x,z,_,_,_,_⟩ := birth_protocol_first_coupled_teaching_exists
    hborn hb ha hqueue newborn forward backward hd
  obtain ⟨w⟩ := z.feedback_weak_entry_exists hb
  obtain ⟨a⟩ := z.first_feedback_fire_exists hb w
  have hz : Real.log (3 / 10) - 1 / 100000 ≤ z.final.x 1 (.z 2) ∧
      z.final.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [z.b_gain_other 2 (by decide)]
    simpa only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] using newborn.gain (2 : Port)
  have hg : Real.exp (w.final.x 1 (.z 2)) ≤ 2 := by
    apply (learned_gain_bounds ?_ ?_).2
    · rw [w.gain_target]; linarith [hz.1]
    · rw [w.gain_target]; linarith [hz.2]
  obtain ⟨q⟩ := first_reverse_wired_arrival_exists a hb hg hback
  have hcomplete : CompleteThrough (z.first_reverse_wire_staged q).after q.final.time := by
    simpa only [CompleteThrough] using q.complete
  have hc := z.first_reverse_wire_counts hb.extend_old q
  exact ⟨c,b,r,s,v,f,g,u,t,x,z,w,a,q,hcomplete,q.pending_length,hc.1,hc.2⟩

end KernelR.Hybrid
