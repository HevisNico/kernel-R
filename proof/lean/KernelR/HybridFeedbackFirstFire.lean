import KernelR.HybridFeedbackWeakEntry
import KernelR.HybridFirstLearnedFireExistence
import KernelR.HybridResidualLatency

/-! The first actual reciprocal B FIRE uses B's carried weak-input residue.
Its reverse wire is issued by that FIRE, rather than supplied in a calendar. -/
namespace KernelR.Hybrid

structure FeedbackFirstFire {θ forward backward start}
    (w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start) where
  firing : FirstLearnedFire θ (reciprocalEntryRouter forward backward) w.final 1 2
  first_le_rest : firing.latency ≤ restLatency (Real.exp (w.final.x 1 (.z 2)))

namespace FeedbackFirstFire
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start} (f : FeedbackFirstFire w)

noncomputable def final : Snapshot 2 := f.firing.final

noncomputable def execution : Execution θ (reciprocalEntryRouter forward backward) w.final f.final :=
  f.firing.execution

theorem date : f.final.time = 344 + f.firing.latency := by
  rw [final,f.firing.date,w.date]

theorem window : 344 + (3 / 10 : ℝ) < f.final.time ∧ f.final.time < 344 + 9 / 10 := by
  rw [f.date]
  constructor <;> linarith [f.firing.early,f.firing.deadline]

theorem protocol_route : reciprocalEntryRouter forward backward 1 f.final.time =
    [⟨0,2,f.final.time + backward f.final.time⟩] := by
  classical
  have ht : (320 : ℝ) ≤ f.final.time ∧ f.final.time < 470 := by
    constructor <;> linarith [f.window.1,f.window.2]
  simp [reciprocalEntryRouter,Contact.route,teachingContact,feedbackContact,Contact.token,ht.1,ht.2]

theorem pending : f.final.pending = w.final.pending ++
    [⟨0,2,f.final.time + backward f.final.time⟩] := by
  rw [final,f.firing.pending]
  change w.final.pending ++ reciprocalEntryRouter forward backward 1 f.final.time = _
  rw [f.protocol_route]
  rfl

theorem pending_length : f.final.pending.length = 29 := by
  rw [f.pending,List.length_append,w.pending_length]
  rfl

theorem emissions : f.execution.ledger.emissions = [(1,f.final.time)] := f.firing.emissions

theorem deliveries : f.execution.deliveries = [] := f.firing.deliveries

theorem gains (i : Fin 2) (p : Port) : f.final.x i (.z p) = w.final.x i (.z p) :=
  f.firing.gain_preserved i p

theorem recovery (i : Fin 2) : f.final.x i .b = w.final.x i .b :=
  f.firing.recovery_preserved i

theorem a_prepared : PreparedSection f.final 0 := by
  obtain ⟨idle⟩ := f.execution.idle_prepared 0 (w.prepared 0) w.a_charge
    (fun p => w.raw_other 0 p (Or.inl (by decide))) (by simp [NoArrivalAt,f.deliveries])
  exact idle.prepared

theorem a_charge : f.final.x 0 .q = 1 / 10 := by
  obtain ⟨idle⟩ := f.execution.idle_prepared 0 (w.prepared 0) w.a_charge
    (fun p => w.raw_other 0 p (Or.inl (by decide))) (by simp [NoArrivalAt,f.deliveries])
  exact idle.charge_rest

theorem a_raw_none (p : Port) : f.final.raw 0 p = none :=
  f.firing.raw_other 0 p (Or.inl (by decide))

theorem complete (hdelay : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5) :
    CompleteThrough f.execution f.final.time := by
  have hfuture : ∀ d ∈ f.final.pending, f.final.time < d.due := by
    intro d hd
    rw [f.pending,w.pending] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      all_goals
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
        dsimp
        nlinarith [f.window.2,Nat.cast_nonneg (α := ℝ) k.val]
    · have he := List.mem_singleton.mp hd
      subst d
      change f.final.time < f.final.time + backward f.final.time
      linarith [(hdelay f.final.time).1]
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro i
      by_cases hi : i = 0
      · subst i
        rw [f.a_prepared.ready]
        linarith [f.a_prepared.charge.2]
      · have hi1 : i = 1 := by fin_cases i <;> simp_all
        subst i
        have hm : f.final.main 1 = .fast := f.firing.main_fast
        have hq : f.final.x 1 .q = 1 := f.firing.charge
        rw [hm,hq]
        norm_num
    · intro i p
      by_cases h : i = 1 ∧ p = 2
      · obtain ⟨rfl,rfl⟩ := h
        have hm : f.final.aux 1 2 = .silent := f.firing.aux_silent
        rw [hm]
        exact f.firing.sensor_above
      · have hother : i ≠ 1 ∨ p ≠ 2 := by tauto
        have haux := f.execution.aux_no_input_rest_band i p ((w.prepared i).auxiliary p).1
          ((w.prepared i).auxiliary p).2 (w.raw_other i p hother)
          (by simp [NoArrivalAt,f.deliveries])
        rw [haux.1.1]
        linarith [haux.1.2.2]
  · intro i p origin hraw
    by_cases h : i = 1 ∧ p = 2
    · obtain ⟨rfl,rfl⟩ := h
      have ho : origin = w.final.time := Option.some.inj (hraw.symm.trans f.firing.raw_active)
      rw [ho,w.date]
      linarith [f.window.2]
    · have hother : i ≠ 1 ∨ p ≠ 2 := by tauto
      have hn : f.final.raw i p = none := f.firing.raw_other i p hother
      rw [hn] at hraw
      contradiction
  · exact hfuture

end FeedbackFirstFire

/-- Construct B's first own learned threshold with the real carried charge.
The same-gain resting latency is only an upper bound, not a chosen date. -/
theorem FeedbackWeakEntry.first_fire_exists {θ ε forward backward start}
    (w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start)
    (hb : @PhysicalBox 2 θ ε)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ start.x 1 (.z 2) ∧
      start.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    Nonempty (FeedbackFirstFire w) := by
  have hg : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2 := by
    apply learned_gain_bounds
    · rw [w.gain_target]; linarith [hz.1]
    · rw [w.gain_target]; linarith [hz.2]
  have hfuture : ∀ d ∈ w.final.pending, w.final.time + 8 ≤ d.due := by
    intro d hd
    rw [w.pending] at hd
    rw [w.date]
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨f⟩ := first_learned_fire_exists (route := reciprocalEntryRouter forward backward)
    w.final hb w.physical w.raw_valid 1 2
    (fun i => (w.prepared i).ready_coordinates) hg w.raw_active w.raw_other hfuture
  have hrest := restLatency_spec ⟨hg.1,by linarith [hg.2]⟩
  have hroot : readyPulse (w.final.x 1 .q) (Real.exp (w.final.x 1 (.z 2))) 0 f.latency = 1 := by
    simpa only [readyPulse,add_sub_cancel_left,sub_zero] using f.response_root
  refine ⟨⟨f,?_⟩⟩
  exact first_firing_le_rest_reference w.b_charge hg.1
    ⟨by linarith [f.early],by linarith [f.deadline]⟩
    ⟨by linarith [hrest.1],by linarith [hrest.2.1]⟩ hroot hrest.2.2

namespace FirstCoupledTeaching
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {v : SecondWiredArrival s}
  {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
  {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t} (z : FirstCoupledTeaching x)

theorem first_feedback_fire_exists {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final) : Nonempty (FeedbackFirstFire w) := by
  apply w.first_fire_exists hb
  rw [z.b_gain_other 2 (by decide)]
  simpa only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] using newborn.gain (2 : Port)

noncomputable def feedback_first_fire_staged
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final} (f : FeedbackFirstFire w) :
    StagedExecution θ fresh (fun _ _ => []) (reciprocalEntryRouter forward backward) born f.final :=
  { z.staged with after := (z.staged.after.append w.execution).append f.execution }

theorem feedback_first_fire_counts {ε} (hb : PhysicalBox θ ε)
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final} (f : FeedbackFirstFire w) :
    ((z.feedback_first_fire_staged f).before.emissionTimes 0 ++
      (z.feedback_first_fire_staged f).after.emissionTimes 0).length = 28 ∧
      ((z.feedback_first_fire_staged f).after.emissionTimes 1).length = 15 := by
  have heA : f.execution.emissionTimes 0 = [] := by simp [Execution.emissionTimes,f.emissions]
  have heB : f.execution.emissionTimes 1 = [f.final.time] := by simp [Execution.emissionTimes,f.emissions]
  constructor
  · simpa only [feedback_first_fire_staged,Execution.emissionTimes_append,
      w.emission_times,heA,List.append_nil] using z.a_cumulative hb
  · simp only [feedback_first_fire_staged,Execution.emissionTimes_append,
      w.emission_times,heB,List.append_nil,List.length_append,List.length_singleton,z.staged_b_count]

end FirstCoupledTeaching

/-- The original birth factory now reaches the first actual reverse-contact
FIRE. Its wire is pending, and no receiving execution is assumed. -/
theorem birth_protocol_feedback_first_fire_exists {θ born fresh ε}
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
                ∃ a : FeedbackFirstFire w,
                  CompleteThrough (z.feedback_first_fire_staged a).after a.final.time ∧
                    a.final.pending.length = 29 ∧
                    ((z.feedback_first_fire_staged a).before.emissionTimes 0 ++
                      (z.feedback_first_fire_staged a).after.emissionTimes 0).length = 28 ∧
                    ((z.feedback_first_fire_staged a).after.emissionTimes 1).length = 15 := by
  obtain ⟨c,b,r,s,v,f,g,u,t,x,z,_,_,_,_⟩ := birth_protocol_first_coupled_teaching_exists
    hborn hb ha hqueue newborn forward backward hd
  obtain ⟨w⟩ := z.feedback_weak_entry_exists hb
  obtain ⟨a⟩ := z.first_feedback_fire_exists hb w
  have hcomplete : CompleteThrough (z.feedback_first_fire_staged a).after a.final.time := by
    simpa only [CompleteThrough] using a.complete hback
  have hc := z.feedback_first_fire_counts hb.extend_old a
  exact ⟨c,b,r,s,v,f,g,u,t,x,z,w,a,hcomplete,a.pending_length,hc.1,hc.2⟩

end KernelR.Hybrid
