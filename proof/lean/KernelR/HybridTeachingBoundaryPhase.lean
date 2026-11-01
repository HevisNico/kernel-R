import KernelR.HybridTeachingActivePhase
import KernelR.HybridTeachingActivation
/-! Merge the two legal source/birth orders at the teaching boundary. -/
namespace KernelR.Hybrid

theorem Execution.zero_duration_mark {n θ route s u} (e : @Execution n θ route s u)
    (ht : u.time = s.time) (i : Fin n) (p : Port) : e.ledger.mark i p = 0 := by
  induction e with
  | nil => rfl
  | cons move rest ih => cases move with
    | flow f => exact False.elim (by have h := rest.time_monotone; linarith [f.positive])
    | jump j =>
      simp only [Execution.ledger,Move.ledger,Ledger.add,j.mark_zero,zero_add]
      exact ih (by simpa only [j.time_unchanged] using ht)

/-- A delivery has no emission at any cell, not just its receiving cell. -/
theorem CellDeliveryStep.emissions_at {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) (k : Fin n) :
    e.emissionTimes k = cut.span.emissionTimes k ++ cut.rest.emissionTimes k := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  calc
    e.emissionTimes k = (cut.span.append (.cons (.jump cut.entry) cut.rest)).emissionTimes k :=
      congrArg (fun actual => actual.emissionTimes k) cut.reconstruct
    _ = _ := by simp [Execution.emissionTimes_append,Execution.emissionTimes_cons,
      Move.ledger,cut.entry.no_emissions_of_delivery d hd]

/-- A source at 160 may already be active or still pending at birth. Both
orders give the same complete A16/B14 teaching phase without a cell reset. -/
theorem Execution.teaching_boundary_phase {θ ε route s u} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : PreparedSection s 0) (hqa : s.x 0 .q = 1 / 10)
    (hza : 9 / 5 ≤ Real.exp (s.x 0 (.z 0)) ∧ Real.exp (s.x 0 (.z 0)) ≤ 12 / 5)
    (hboundary :
      (s.raw 0 0 = none ∧ (s.pending.filter (fun d => d.cell = 0)).Perm (sourceTrain 0 0 160 8 16)) ∨
      (s.raw 0 0 = some s.time ∧ (s.pending.filter (fun d => d.cell = 0)).Perm (sourceTrain 0 0 168 8 15)))
    (hoa : ∀ q, q ≠ 0 → s.raw 0 q = none)
    (hclosed : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ 0)
    (ht : s.time = 160) (hu : u.time = 3199 / 10) (hpf : PendingFuture u)
    (hsb : ReadyCoordinates s 1)
    (hbb : 7999 / 100000 ≤ s.x 1 .b ∧ s.x 1 .b ≤ 8001 / 100000)
    (hzb : Real.log (6 / 5) - 1 / 1000 ≤ s.x 1 (.z 1) ∧ s.x 1 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000)
    (hrb : ∀ q, s.raw 1 q = none)
    (hfuture : ∀ d ∈ s.pending, d.cell = 1 → 320 ≤ d.due)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = 1) = (teachingContact delay).route event.1 event.2) :
    Nonempty (TeachingActivePhase e) := by
  rcases hboundary with ⟨hnone,hqueue⟩ | ⟨hactive,hqueue⟩
  · have hrA : ∀ q, s.raw 0 q = none := by
      intro q
      by_cases hq : q = 0
      · subst q; exact hnone
      · exact hoa q hq
    obtain ⟨activation⟩ := e.teaching_activation ha hqa hsb hrA hrb ht hu hpf hqueue hclosed hfuture
    let cut := activation.cut
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have invariant := advanced.physical_invariant hb hf
    have valid := advanced.raw_valid hv
    have gainA : 9 / 5 ≤ Real.exp (cut.afterArrival.x 0 (.z 0)) ∧
        Real.exp (cut.afterArrival.x 0 (.z 0)) ≤ 12 / 5 := by
      rw [activation.coordinates]
      exact hza
    have recoveryB : 7999 / 100000 ≤ cut.afterArrival.x 1 .b ∧ cut.afterArrival.x 1 .b ≤ 8001 / 100000 := by
      rw [activation.coordinates]
      exact hbb
    have gainB : Real.log (6 / 5) - 1 / 1000 ≤ cut.afterArrival.x 1 (.z 1) ∧
        cut.afterArrival.x 1 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000 := by
      rw [activation.coordinates]
      exact hzb
    have tail_member : ∀ event ∈ cut.rest.ledger.emissions, event ∈ e.ledger.emissions := by
      intro event he
      rw [cut.reconstruct,Execution.emissions_append]
      exact List.mem_append_right _ (List.mem_append_right _ he)
    obtain ⟨phase⟩ := cut.rest.teaching_active_phase hb invariant valid activation.preparedA
      activation.charge_restA gainA activation.raw_activeA activation.raw_otherA activation.queueA
      (fun event he d hd => hclosed event (tail_member event he) d hd)
      activation.date hu hpf activation.readyB recoveryB gainB activation.rawB activation.futureB
      delay hdelay (fun event he => hwire event (tail_member event he))
    have span_time : cut.beforeArrival.time = s.time := cut.date.1.trans ht.symm
    have span_mark : ∀ i p, cut.span.ledger.mark i p = 0 :=
      fun i p => cut.span.zero_duration_mark span_time i p
    have gainA_whole : ∀ p, u.x 0 (.z p) = s.x 0 (.z p) := by
      intro p
      rw [phase.a_train.gain_preserved p,activation.coordinates]
    have recoveryA_whole : u.x 0 .b = s.x 0 .b := by
      rw [phase.a_train.recovery_preserved,activation.coordinates]
    have gainB_whole : u.x 1 (.z 1) = s.x 1 (.z 1) + 3 / 5 := by
      rw [phase.b_phase.gain_target,activation.coordinates]
    have otherB_whole : ∀ p, p ≠ 1 → u.x 1 (.z p) = s.x 1 (.z p) := by
      intro p hp
      rw [phase.b_phase.gain_other p hp,activation.coordinates]
    have recoveryB_whole : u.x 1 .b = s.x 1 .b + 1 / 10 := by
      rw [phase.b_phase.recovery_gain,activation.coordinates]
    refine ⟨⟨⟨?_,?_,?_,gainA_whole,recoveryA_whole,phase.a_train.prepared,
      phase.a_train.charge_rest,phase.a_train.raw_finished⟩,
      ⟨?_,?_,?_,?_,?_,gainB_whole,otherB_whole,recoveryB_whole,
        phase.b_phase.prepared,phase.b_phase.charge_rest,phase.b_phase.raw_finished⟩⟩⟩
    · rw [cut.emissions,activation.emissionsA_before,List.nil_append]
      exact phase.a_train.emissions
    · intro p
      have h := e.gain_balance 0 p
      rw [gainA_whole p] at h
      linarith
    · intro p
      rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 0 p,span_mark 0 p,zero_add]
      exact phase.a_train.mark_zero p
    · rw [cut.emissions_at 1,activation.emissionsB_before,List.nil_append]
      exact phase.b_phase.emissions
    · have h := e.gain_balance 1 1
      linarith
    · intro p hp
      have h := e.gain_balance 1 p
      rw [otherB_whole p hp] at h
      linarith
    · rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 1 1,span_mark 1 1,zero_add]
      exact phase.b_phase.mark_target
    · intro p hp
      rw [e.mark_split cut.span cut.entry cut.rest cut.reconstruct 1 p,span_mark 1 p,zero_add]
      exact phase.b_phase.mark_other p hp
  · exact e.teaching_active_phase hb hf hv ha hqa hza hactive hoa hqueue hclosed ht hu hpf
      hsb hbb hzb hrb hfuture delay hdelay hwire

end KernelR.Hybrid
