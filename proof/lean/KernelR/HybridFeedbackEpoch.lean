import KernelR.HybridFeedbackInitialSource
import KernelR.HybridFeedbackReceiver
/-! Both physical sides of the B-to-A return epoch, with source and wire calendars derived. -/
namespace KernelR.Hybrid

structure FeedbackEpoch {θ route s u} (e : @Execution 2 θ route s u) where
  a_learning : PreparedLearningTrain e 0 2 10
  b_learning : PreparedLearningTrain e 1 2 13

/-- The declared return contacts and actual pending sources determine both
physical learning trains. No output count, received calendar, or pulse-case
word is supplied. Existence of the reaching execution remains a premise. -/
theorem Execution.feedback_epoch {θ ε s u} (forward backward : ℝ → ℝ)
    (e : @Execution 2 θ (reciprocalEntryRouter forward backward) s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hsA : PreparedSection s 0) (hqA : s.x 0 .q = 1 / 10)
    (hzA : Real.log (3 / 10) - 1 / 100000 ≤ s.x 0 (.z 2) ∧
      s.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hrA : ∀ p, s.raw 0 p = none)
    (hsB : PreparedSection s 1) (hqB : s.x 1 .q = 1 / 10)
    (hzB : Real.log (3 / 10) - 1 / 100000 ≤ s.x 1 (.z 2) ∧
      s.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hrB : ∀ p, s.raw 1 p = none)
    (later : List (Delivery 2))
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hBqueue : (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 320 8 16 ++ later))
    (hlater : ∀ d ∈ later, u.time < d.due)
    (ht : s.time = 3199 / 10) (hu : u.time = 4599 / 10) (hpf : PendingFuture s)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) : Nonempty (FeedbackEpoch e) := by
  have hcausal := reciprocalEntryRouter.causal forward backward
    (fun t => by linarith [(hforward t).1]) (fun t => by linarith [(hbackward t).1])
  have hfuture : PendingFuture u := e.pending_future hcausal hpf
  have htime : ∀ event ∈ e.ledger.emissions, 310 ≤ event.2 := by
    intro event he
    have h := (e.emission_time_bounds event he).1
    rw [ht] at h
    linarith
  have hclosedB : ∀ event ∈ e.ledger.emissions,
      ∀ d ∈ reciprocalEntryRouter forward backward event.1 event.2, d.cell ≠ 1 := by
    intro event he
    exact reciprocalEntryRouter.closed_to_b forward backward event.1 (htime event he)
  obtain ⟨sender⟩ := e.feedback_from_sources hb hf hv hsB hqB hzB hrB later hBqueue hlater
    hclosedB hu hfuture
  have hgain : 9 / 5 ≤ Real.exp (s.x 1 (.z 2) + 9 / 5) ∧
      Real.exp (s.x 1 (.z 2) + 9 / 5) ≤ 12 / 5 := by
    have hlog : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 1 (.z 2) + 9 / 5 ∧
        s.x 1 (.z 2) + 9 / 5 ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
      constructor <;> linarith [hzB.1,hzB.2]
    have h := learned_gain_bounds hlog.1 hlog.2
    exact ⟨h.1,by linarith [h.2]⟩
  let rest := restLatency (Real.exp (s.x 1 (.z 2) + 9 / 5))
  have hrest : 3 / 10 < rest ∧ rest < 9 / 10 :=
    ⟨(restLatency_spec hgain).1,(restLatency_spec hgain).2.1⟩
  have hfirst : 3 / 10 < sender.first ∧ sender.first < 9 / 10 := ⟨sender.first_lower,sender.first_upper⟩
  have houtputs : e.emissionTimes 1 = feedbackSendDates sender.first rest := by
    simpa only [feedbackSendDates,rest] using sender.emissions
  have hwire : ∀ event ∈ e.ledger.emissions,
      (reciprocalEntryRouter forward backward event.1 event.2).filter (fun d => d.cell = 0) =
        (feedbackContact backward).route event.1 event.2 := by
    intro event he
    exact reciprocalEntryRouter.to_a forward backward event.1 (htime event he)
  have hcalendar := e.feedback_contact_deliveries sender.first rest hfirst hrest sender.first_le_rest
    houtputs backward hbackward hu hfuture hAempty hwire
  obtain ⟨receiver⟩ := e.feedback_receiver_phase hb hf hv hsA hqA hzA hrA hu sender.first rest
    hfirst hrest sender.first_le_rest backward hbackward hcalendar
  exact ⟨⟨receiver,sender.learning⟩⟩

end KernelR.Hybrid
