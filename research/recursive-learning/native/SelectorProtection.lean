import KernelR.HybridCadenceHighCompletion

/-! Short protection for the selector read. This specialization uses the
    full recovery cap and a shorter deadline than the chain's helper. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

theorem selector_slow_charge_preguard {B F time : ℝ}
    (hB : 0 ≤ B ∧ B ≤ 11 / 10) (hl : F + 1 ≤ time) (hu : time ≤ F + 3 / 2) :
    1 / 10 < (1 / 4 : ℝ) * Real.exp (-B * (time - (F + 1))) := by
  have elapsed : 0 ≤ time - (F + 1) ∧ time - (F + 1) ≤ 1 / 2 := by
    constructor <;> linarith
  have product : B * (time - (F + 1)) ≤ 11 / 20 :=
    (mul_le_mul hB.2 elapsed.2 elapsed.1 (by norm_num)).trans (by norm_num)
  linarith [Real.add_one_le_exp (-B * (time - (F + 1)))]

private theorem selector_slow_aux_phase_exists {θ ε route} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (mode : AuxMode) (origin T F P initial B : ℝ)
    (hmode : mode = .silent ∨ mode = .error) (hT : s.time < T)
    (hm : s.main 0 = .slow) (ha : s.aux 0 p = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ p → s.aux j q = .ready)
    (hr : ∀ j q, s.raw j q = none)
    (hx : ∀ j q, j ≠ 0 ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : s.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (s.time - (F + 1))))
    (hs : s.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (s.time - P)))
    (hbown : s.x 0 .b = B) (hB : 0 ≤ B ∧ B ≤ 11 / 10)
    (horigin : origin < F) (hstart : F + 1 ≤ s.time) (hF : T ≤ F + 3 / 2)
    (hP : P ≤ s.time) (hi : fastAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / fastAuxFloor mode) / protectedReadyRate (θ 0) p mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Nonempty (CadenceProtectedAuxPhase θ route s p mode origin T F P initial B) := by
  have hn : mode ≠ .ready := by rcases hmode with rfl | rfl <;> decide
  have hfloor : 0 < fastAuxFloor mode := by rcases hmode with rfl | rfl <;> norm_num [fastAuxFloor]
  have hrpos : 0 < protectedReadyRate (θ 0) p mode := by
    rcases hmode with rfl | rfl
    · exact (hb.rates_positive 0 p).2.1
    · exact (hb.rates_positive 0 p).2.2
  have hdecay := protected_decay_schedule hfloor hi hrpos
  have hmain_clock (t : ℝ) : s.x 0 .q * Real.exp (-B * (t - s.time)) =
      (1 / 4 : ℝ) * Real.exp (-B * (t - (F + 1))) := by
    rw [hq,mul_assoc,attenuation_split]
  have hsensor_clock (t : ℝ) : s.x 0 (.m p) *
      Real.exp (-protectedReadyRate (θ 0) p mode * (t - s.time)) =
      initial * Real.exp (-protectedReadyRate (θ 0) p mode * (t - P)) := by
    rw [hs,mul_assoc,attenuation_split]
  let flow : Flow θ s (protectedMainEnd θ s 0 p .slow mode none T) :=
    protectedMainFlow s 0 p .slow mode none hT (Or.inr rfl)
      (by rcases hmode with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr rfl))
      hm (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) ha hao (hr 0 p)
      (fun j q _ => hr j q) (by intros; contradiction)
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) hx
      (by intro t ht
          simp only [reduceCtorEq,ite_false,protectedMainRate,hbown]
          rw [hmain_clock]
          exact selector_slow_charge_preguard hB (by linarith [ht.1]) (by linarith [ht.2]))
      (by intro t ht
          simp only [hn,ite_false]
          change fastAuxFloor mode < _
          rw [hsensor_clock]
          exact hdecay.2.2 (t - P) (by linarith [ht.1]) (by linarith [ht.2])) hp
  let final := protectedMainEnd θ s 0 p .slow mode none T
  have hfast : ¬T < F + 1 := by linarith
  have hraw : ¬T < origin + 1 := by linarith
  refine ⟨{
    final := final, execution := .cons (.flow flow) (.nil _), date := rfl
    contacts_transversal := by trivial
    main_mode := by simpa only [final,protectedMainEnd,hfast,ite_false] using hm
    main_clock := ?_, aux_mode := ha, aux_other := hao, sensor_clock := ?_
    other_below := ?_, raw_mode := by simpa only [final,protectedMainEnd,hraw,ite_false] using hr 0 p
    raw_other := fun j q _ => hr j q, pending := rfl
    gains := fun _ _ => rfl, recovery := fun _ => rfl, emissions := rfl, deliveries := rfl
  }⟩
  · simpa [final,protectedMainEnd,protectedMainValues,protectedMainRate,hbown,cadenceProtectedCharge,hfast]
      using hmain_clock T
  · simpa [final,protectedMainEnd,protectedMainValues,hn] using hsensor_clock T
  · intro j q h
    have hne : ¬ (j = 0 ∧ q = p) := by tauto
    simpa [final,protectedMainEnd,protectedMainValues,hne] using
      relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hx j q h) (by norm_num : (1 / 40 : ℝ) < 1)

/-- Continue the same auxiliary clock across the real FAST exit, consuming
RAW expiry at its original date and every equal-date boundary jump. -/
theorem selector_protected_aux_phase_exists {θ ε route} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (mode : AuxMode) (origin T F P initial B : ℝ)
    (hmode : mode = .silent ∨ mode = .error) (hT : s.time < T)
    (hm : s.main 0 = if s.time < F + 1 then .fast else .slow)
    (ha : s.aux 0 p = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw 0 p = if s.time < origin + 1 then some origin else none)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ p → s.raw j q = none)
    (horigin : origin ≤ s.time) (hFsource : origin < F)
    (hx : ∀ j q, j ≠ 0 ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : s.x 0 .q = cadenceProtectedCharge B F s.time)
    (hs : s.x 0 (.m p) = initial * Real.exp (-protectedReadyRate (θ 0) p mode * (s.time - P)))
    (hbown : s.x 0 .b = B) (hB : 0 ≤ B ∧ B ≤ 11 / 10)
    (hP : P ≤ s.time) (hF : T ≤ F + 3 / 2) (hi : fastAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / fastAuxFloor mode) / protectedReadyRate (θ 0) p mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Nonempty (CadenceProtectedAuxPhase θ route s p mode origin T F P initial B) := by
  by_cases hstart : s.time < F + 1
  · rw [ite_eq_left hstart] at hm
    have hqfast : s.x 0 .q = Real.exp (-a * (s.time - F)) := by
      simpa only [cadenceProtectedCharge,hstart,ite_true] using hq
    by_cases hstop : T < F + 1
    · obtain ⟨r,ht,hrT⟩ := port_fast_aux_phase_exists (route := route) hb s p mode origin T F P initial
        hmode hT hm ha hao hr ho horigin hx hqfast hs hP hstop.le hi hphase hp
      exact ⟨{
        final := r.final, execution := r.execution, date := ht
        contacts_transversal := r.contacts_transversal
        main_mode := by simpa only [hstop,ite_true] using r.main_fast
        main_clock := by simpa only [ht,cadenceProtectedCharge,hstop,ite_true] using r.main_clock
        aux_mode := r.aux_mode, aux_other := r.aux_other
        sensor_clock := by simpa only [ht] using r.sensor_clock
        other_below := r.other_below, raw_mode := hrT, raw_other := r.raw_other
        pending := r.pending, gains := r.gains, recovery := r.recovery
        emissions := r.emissions, deliveries := r.deliveries
      }⟩
    · obtain ⟨r,ht,hrT⟩ := port_fast_aux_phase_exists (route := route) hb s p mode origin (F + 1) F P initial
        hmode hstart hm ha hao hr ho horigin hx hqfast hs hP le_rfl hi
        (by linarith) (fun d hd => by linarith [hp d hd])
      have hquarter : r.final.x 0 .q = 1 / 4 := by
        rw [r.main_clock,ht]
        norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      let after := setMain r.final 0 .slow
      let prefixRun : Execution θ route s after := r.execution.append
        (.cons (.jump (.fastEnd r.final 0 r.main_fast hquarter)) (.nil _))
      have haftertime : after.time = F + 1 := ht
      have hafterq : after.x 0 .q = 1 / 4 := hquarter
      have hafterraw : ∀ j q, after.raw j q = none := by
        intro j q
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        by_cases hqp : q = p
        · subst q
          change r.final.raw 0 p = none
          simpa only [show ¬F + 1 < origin + 1 by linarith,ite_false] using hrT
        · exact r.raw_other 0 q (Or.inr hqp)
      have hafterclock : after.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (after.time - (F + 1))) := by
        rw [hafterq,haftertime]
        simp
      have hafterb : after.x 0 .b = B := (r.recovery 0).trans hbown
      have heP : prefixRun.ledger.emissions = [] := by
        simp only [prefixRun,Execution.emissions_append,r.emissions,Execution.ledger,Move.ledger,Jump.ledger,Ledger.add,Ledger.zero,List.append_nil]
      have hdP : prefixRun.deliveries = [] := by
        simp only [prefixRun,Execution.deliveries_append,r.deliveries,Execution.deliveries,Move.deliveries,Jump.deliveries,List.append_nil]
      have hrP : ∀ j, after.x j .b = s.x j .b := r.recovery
      have hgP : ∀ j q, after.x j (.z q) = s.x j (.z q) := r.gains
      have hqP : after.pending = s.pending := r.pending
      by_cases heq : T = F + 1
      · have hfast : ¬T < F + 1 := by linarith
        have hraw : ¬T < origin + 1 := by linarith
        exact ⟨{
          final := after, execution := prefixRun, date := haftertime.trans heq.symm
          contacts_transversal := by
            simpa [prefixRun, Execution.ContactsTransversal, Jump.ContactTransversal] using r.contacts_transversal
          main_mode := by simp [after,setMain,hfast]
          main_clock := by simp [cadenceProtectedCharge,heq,hafterq]
          aux_mode := r.aux_mode, aux_other := r.aux_other
          sensor_clock := by simpa only [after,setMain,ht,heq] using r.sensor_clock
          other_below := r.other_below
          raw_mode := by simpa only [hraw,ite_false] using hafterraw 0 p
          raw_other := fun j q _ => hafterraw j q
          pending := hqP, gains := hgP, recovery := hrP, emissions := heP, deliveries := hdP
        }⟩
      · obtain ⟨slow⟩ := selector_slow_aux_phase_exists (route := route) hb after p mode origin T F P initial B
          hmode (by rw [haftertime]; exact lt_of_le_of_ne (le_of_not_gt hstop) (Ne.symm heq))
          (by simp [after,setMain]) r.aux_mode r.aux_other hafterraw r.other_below hafterclock
          (by simpa only [after,setMain,ht] using r.sensor_clock) hafterb hB hFsource
          (by rw [haftertime]) hF (by rw [haftertime]; linarith) hi hphase
          (fun d hd => by rw [hqP] at hd; exact hp d hd)
        exact ⟨slow.prepend prefixRun hqP hgP hrP heP hdP (by
          simpa [prefixRun, Execution.ContactsTransversal, Jump.ContactTransversal] using r.contacts_transversal)⟩
  · rw [ite_eq_right hstart] at hm
    have hqslow : s.x 0 .q = (1 / 4 : ℝ) * Real.exp (-B * (s.time - (F + 1))) := by
      simpa only [cadenceProtectedCharge,hstart,ite_false] using hq
    have hrnone : ∀ j q, s.raw j q = none := by
      intro j q
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hqp : q = p
      · subst q
        simpa only [show ¬s.time < origin + 1 by linarith,ite_false] using hr
      · exact ho 0 q (Or.inr hqp)
    exact selector_slow_aux_phase_exists hb s p mode origin T F P initial B hmode hT hm ha hao
      hrnone hx hqslow hs hbown hB hFsource (le_of_not_gt hstart) hF hP hi hphase hp

end RecursiveLearning.Native
