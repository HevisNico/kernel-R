import KernelR.HybridCadenceFirstStrongFireExistence
import KernelR.HybridPrefixBeforeFlow
import KernelR.HybridPrefixStableMemory

/-! The exact-rest second strong cadence FIRE continues at its own recovery
near0.28 to the mixed input time. No boundary token is consumed here. -/
namespace KernelR.Hybrid
open Set

theorem cadence_second_strong_slow_charge_bounds {B S latency time : ℝ}
    (hB : 27999 / 100000 ≤ B ∧ B ≤ 28001 / 100000)
    (hlat : 13 / 20 < latency ∧ latency < 33 / 50)
    (ht : S + latency + 1 ≤ time) (hu : time ≤ S + 4) :
    61 / 500 < (1 / 4 : ℝ) * Real.exp (-B * (time - (S + latency + 1))) ∧
      (1 / 4 : ℝ) * Real.exp (-B * (time - (S + latency + 1))) ≤ 1 / 4 := by
  have hd : 0 ≤ time - (S + latency + 1) ∧ time - (S + latency + 1) < 47 / 20 := by
    constructor <;> linarith [hlat.1]
  have hI : 0 ≤ B * (time - (S + latency + 1)) ∧ B * (time - (S + latency + 1)) < 7 / 10 := by
    constructor <;> nlinarith [hB.1,hB.2]
  have he : (61 / 125 : ℝ) < Real.exp (-(7 / 10 : ℝ)) := by
    have h := Real.exp_bound (x := -(7 / 10 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hlo := Real.exp_le_exp.mpr (show -(7 / 10 : ℝ) ≤ -B * (time - (S + latency + 1)) by nlinarith [hI.2])
  have hhi := Real.exp_le_one_iff.mpr (show -B * (time - (S + latency + 1)) ≤ 0 by nlinarith [hI.1])
  constructor <;> linarith

structure CadenceSecondStrongSlowSpan {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    {fire : FirstLearnedFire θ (fun _ _ => []) s 0 p}
    (fast : PortFastCompletion θ (fun _ _ => []) fire.final p) where
  final : Snapshot 1
  flow : Flow θ fast.final final
  execution : Execution θ (fun _ _ => []) fast.final final
  reconstruct : execution = .cons (.flow flow) (.nil _)
  final_state : final = protectedMainEnd θ fast.final 0 p .slow .ready none (s.time + 4)
  date : final.time = s.time + 4
  main_slow : final.main 0 = .slow
  auxiliary : ∀ j q, final.aux j q = .ready
  rest : ∀ q, RestBand (final.x 0 (.m q))
  trained_rest : final.x 0 (.m p) = 1 / 40
  raw_none : ∀ j q, final.raw j q = none
  charge : 61 / 500 ≤ final.x 0 .q ∧ final.x 0 .q ≤ 7 / 50
  charge_clock : final.x 0 .q = (1 / 4 : ℝ) *
    Real.exp (-s.x 0 .b * ((s.time + 4) - (s.time + fire.latency + 1)))
  energy_clock : final.x 0 .energy =
    protectedMainValues θ fast.final 0 p .slow .ready none (s.time + 4) 0 .energy
  pending : final.pending = fast.final.pending
  gains : ∀ j q, final.x j (.z q) = fast.final.x j (.z q)
  recovery : ∀ j, final.x j .b = fast.final.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

theorem FirstLearnedFire.cadence_second_strong_slow_span_exists {θ ε} {s : Snapshot 1} {p : Port}
    (fire : FirstLearnedFire θ (fun _ _ => []) s 0 p) (hb : PhysicalBox θ ε)
    (fast : PortFastCompletion θ (fun _ _ => []) fire.final p)
    (hq : s.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hB : 27999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 28001 / 100000)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    Nonempty (CadenceSecondStrongSlowSpan fast) := by
  have hg := cadence_three_dose_gain_bounds hz
  have hroot : readyPulse (1 / 10) (Real.exp (s.x 0 (.z p))) 0 fire.latency = 1 := by
    simpa only [readyPulse,hq,add_sub_cancel_left,sub_zero] using fire.response_root
  have heq := restLatency_unique ⟨hg.1,by linarith [hg.2]⟩
    ⟨by linarith [fire.early],fire.deadline.le⟩ hroot
  have hlat : 13 / 20 < fire.latency ∧ fire.latency < 33 / 50 := by
    rw [heq]
    exact restLatency_three_doses_bounds hz.1 hz.2
  have hbfast : fast.final.x 0 .b = s.x 0 .b := by rw [fast.recovery,fire.recovery_preserved]
  have hclock : fast.final.time = s.time + fire.latency + 1 := by rw [fast.date,fire.date]
  have hT : fast.final.time < s.time + 4 := by rw [hclock]; linarith [hlat.2]
  have hguards : ∀ time ∈ Icc fast.final.time (s.time + 4),
      61 / 500 < (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (time - (s.time + fire.latency + 1))) ∧
        (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (time - (s.time + fire.latency + 1))) ≤ 1 / 4 := by
    intro time ht
    exact cadence_second_strong_slow_charge_bounds hB hlat (by rw [← hclock]; exact ht.1) ht.2
  have hpending : ∀ d ∈ fast.final.pending, s.time + 4 ≤ d.due := by
    intro d hd
    rw [fast.pending,fire.pending,List.append_nil] at hd
    exact hp d hd
  let flow : Flow θ fast.final (protectedMainEnd θ fast.final 0 p .slow .ready none (s.time + 4)) :=
    protectedMainFlow fast.final 0 p .slow .ready none hT (Or.inr rfl) (Or.inl rfl)
      fast.main_slow (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (fast.auxiliary 0 p)
      (fun j q _ => fast.auxiliary j q) (fast.raw_none 0 p) (fun j q _ => fast.raw_none j q)
      (by intros; contradiction) (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
      (by intro j q _; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(fast.rest q).2])
      (by intro time ht
          have h := (hguards time ⟨ht.1,ht.2.le⟩).1
          simp only [reduceCtorEq,ite_false,protectedMainRate,fast.charge,hbfast,hclock]
          linarith)
      (by intro time ht
          simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (by rw [fast.sensor_charge]; norm_num) (by norm_num)) hpending
  let final := protectedMainEnd θ fast.final 0 p .slow .ready none (s.time + 4)
  let execution : Execution θ (fun _ _ => []) fast.final final := .cons (.flow flow) (.nil _)
  have hformula : final.x 0 .q = (1 / 4 : ℝ) *
      Real.exp (-s.x 0 .b * ((s.time + 4) - (s.time + fire.latency + 1))) := by
    simp [final,protectedMainEnd,protectedMainValues,protectedMainRate,fast.charge,hbfast,hclock]
  have hrest : ∀ q, RestBand (final.x 0 (.m q)) := by
    intro q
    have hband := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (fast.rest q)
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    by_cases hq : q = p
    · subst q
      simpa [final,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hband
    · simpa [final,protectedMainEnd,protectedMainValues,hq,RestBand] using hband
  refine ⟨{
    final := final, flow := flow, execution := execution, reconstruct := rfl, final_state := rfl
    date := rfl, main_slow := fast.main_slow, auxiliary := fast.auxiliary, rest := hrest
    trained_rest := ?_, raw_none := fast.raw_none, charge := ?_, charge_clock := hformula
    energy_clock := rfl, pending := rfl, gains := fun _ _ => rfl, recovery := fun _ => rfl
    emissions := rfl, deliveries := rfl
    physical := execution.physical_invariant hb fast.physical, raw_valid := execution.raw_valid fast.raw_valid
  }⟩
  · simp [final,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,relax,fast.sensor_charge]
  · rw [hformula]
    have h := hguards (s.time + 4) ⟨hT.le,le_rfl⟩
    have hI : (3 / 5 : ℝ) ≤ s.x 0 .b * ((s.time + 4) - (s.time + fire.latency + 1)) := by
      nlinarith [hB.1,hB.2,hlat.1,hlat.2]
    have hex : Real.exp (-(3 / 5 : ℝ)) ≤ 14 / 25 := by
      have h := Real.exp_bound (x := -(3 / 5 : ℝ)) (n := 6) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ] at h
      linarith [(abs_sub_le_iff.mp h).1]
    have hem := Real.exp_le_exp.mpr (show
      -s.x 0 .b * ((s.time + 4) - (s.time + fire.latency + 1)) ≤ -(3 / 5 : ℝ) by linarith)
    exact ⟨h.1.le,by linarith⟩

namespace CadenceSecondStrongSlowSpan
variable {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
  {fire : FirstLearnedFire θ (fun _ _ => []) s 0 p}
  {fast : PortFastCompletion θ (fun _ _ => []) fire.final p} (span : CadenceSecondStrongSlowSpan fast)

theorem contacts_transversal : span.execution.ContactsTransversal := by
  rw [span.reconstruct]
  trivial

/-- Resume the very FAST flow retained by a real wire cut, then append this
same SLOW flow. The endpoint energy and charge are never reconstructed anew. -/
noncomputable def fromCut {H : ℝ} (cut : fast.execution.BeforeFlowCut H) :
    Execution θ (fun _ _ => []) cut.state span.final :=
  (Execution.cons (.flow cut.flow) cut.rest).append span.execution

theorem fromCut_contacts_transversal {H : ℝ} (cut : fast.execution.BeforeFlowCut H) :
    (span.fromCut cut).ContactsTransversal := by
  simp only [fromCut, Execution.contactsTransversal_append, Execution.ContactsTransversal]
  exact ⟨cut.rest_contacts_transversal fast.contacts_transversal, span.contacts_transversal⟩

theorem fromCut_emissions {H : ℝ} (cut : fast.execution.BeforeFlowCut H) :
    (span.fromCut cut).ledger.emissions = [] := by
  have he : cut.rest.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (cut.emissions.symm.trans fast.emissions)).2
  simp only [fromCut,Execution.emissions_append,span.emissions,Execution.ledger,Move.ledger,
    Flow.ledger,he,Ledger.add,List.append_nil]

theorem fromCut_deliveries {H : ℝ} (cut : fast.execution.BeforeFlowCut H) :
    (span.fromCut cut).deliveries = [] := by
  have hd : cut.rest.deliveries = [] :=
    (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans fast.deliveries)).2
  simp only [fromCut,Execution.deliveries_append,span.deliveries,Execution.deliveries,
    Move.deliveries,hd,List.append_nil]

theorem fromCut_gains {ε H} (hb : PhysicalBox θ ε) (cut : fast.execution.BeforeFlowCut H) (q : Port) :
    span.final.x 0 (.z q) = cut.state.x 0 (.z q) := by
  have hc := cut.isPrefix.gain_eq_of_final hb 0 q (fast.gains 0 q)
  rw [span.gains,fast.gains,hc]

theorem fromCut_recovery {ε H} (hb : PhysicalBox θ ε) (cut : fast.execution.BeforeFlowCut H) :
    span.final.x 0 .b = cut.state.x 0 .b := by
  have hc := cut.isPrefix.recovery_eq_of_final hb 0 (fast.recovery 0)
  rw [span.recovery,fast.recovery,hc]

end CadenceSecondStrongSlowSpan
end KernelR.Hybrid
