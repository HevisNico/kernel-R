import KernelR.HybridCadenceMixedResponse

/-! Consume the next genuine cadence source after the constructed mixed
response. The READY residual charge is carried into the first high response. -/
namespace KernelR.Hybrid

structure CadenceMixedNextSource {θ s p} (mixed : CadenceMixedResponse θ s p)
    (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  contacts_transversal : execution.ContactsTransversal
  date : final.time = s.time + 4
  values : final.x = mixed.final.x
  coordinates : CadenceReadyCoordinates final 0 (8 / 25)
  charge_lower : 1 / 10 ≤ final.x 0 .q
  raw_active : final.raw 0 p = some final.time
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  gain_target : final.x 0 (.z p) = s.x 0 (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → final.x 0 (.z q) = s.x 0 (.z q)
  recovery_gain : final.x 0 .b = s.x 0 .b + 1 / 10
  pending : final.pending = later
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,p,s.time + 4⟩]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (s.time + 4)

theorem cadence_mixed_next_source_exists {θ ε s p} (mixed : CadenceMixedResponse θ s p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (later : List (Delivery 1)) (hqueue : s.pending = ⟨0,p,s.time + 4⟩ :: later)
    (hlater : ∀ d ∈ later, s.time + 4 < d.due) :
    Nonempty (CadenceMixedNextSource mixed later) := by
  let final : Snapshot 1 := {setRaw mixed.final 0 p (some mixed.final.time) with pending := later}
  let arrival : Jump (fun _ _ => []) mixed.final final := .arrive mixed.final ⟨0,p,s.time + 4⟩ [] later
    (mixed.pending.trans hqueue) mixed.date.symm (mixed.raw_none p)
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨0,p,s.time + 4⟩] := rfl
  let execution := mixed.execution.append (.cons (.jump arrival) (.nil _))
  have hRaw : final.raw 0 p = some final.time := by simp [final,setRaw]
  have hOther : ∀ q, q ≠ p → final.raw 0 q = none := by
    intro q hq
    simp [final,setRaw,hq,mixed.raw_none]
  have hCoords : CadenceReadyCoordinates final 0 (8 / 25) :=
    ⟨mixed.coordinates.ready,mixed.coordinates.charge,mixed.coordinates.auxiliary⟩
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ later at hd
    change mixed.final.time < d.due
    rw [mixed.date]
    exact hlater d hd
  have hComplete : CompleteThrough execution (s.time + 4) := by
    refine ⟨mixed.date,?_,?_⟩
    · intro u
      apply BeforeGuards.no_jump
      · constructor
        · intro j
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          rw [hCoords.ready]
          linarith [hCoords.charge.2]
        · intro j q
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          rw [(hCoords.auxiliary q).1]
          linarith [(hCoords.auxiliary q).2.2]
      · intro j q origin hraw
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        by_cases hq : q = p
        · subst q
          have he : origin = final.time := Option.some.inj (hraw.symm.trans hRaw)
          rw [he]; linarith
        · rw [hOther q hq] at hraw
          contradiction
      · exact hFuture
    · intro d hd
      have h := hFuture d hd
      change mixed.final.time < d.due at h
      rw [mixed.date] at h
      exact h
  refine ⟨{
    contacts_transversal := by
      simp [execution, arrival, Execution.ContactsTransversal, Jump.ContactTransversal,
        mixed.contacts_transversal]
    final := final, execution := execution, date := mixed.date, values := rfl
    coordinates := hCoords, charge_lower := mixed.charge_lower, raw_active := hRaw, raw_other := hOther
    gain_target := mixed.gain_target, gain_other := mixed.gain_other, recovery_gain := mixed.recovery_gain
    pending := rfl, emissions := ?_, deliveries := ?_
    physical := execution.physical_invariant hb hf, raw_valid := execution.raw_valid hv, complete := hComplete
  }⟩
  · simp only [execution,Execution.emissions_append,mixed.emissions,Execution.ledger,Move.ledger,
      haEm,Ledger.add,Ledger.zero,List.nil_append]
  · simp only [execution,Execution.deliveries_append,mixed.deliveries,Execution.deliveries,Move.deliveries,
      haDel,List.nil_append,List.append_nil]

namespace CadenceMixedNextSource
variable {θ s p} {mixed : CadenceMixedResponse θ s p} {later}
  (entry : CadenceMixedNextSource mixed later)

theorem recovery_band : 37999 / 100000 ≤ entry.final.x 0 .b ∧
    entry.final.x 0 .b ≤ 38001 / 100000 := by
  rw [entry.values]
  exact mixed.recovery_band

theorem high_gain_bounds
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    16 / 5 ≤ Real.exp (entry.final.x 0 (.z p)) ∧ Real.exp (entry.final.x 0 (.z p)) ≤ 7 / 2 := by
  rw [entry.gain_target]
  exact ⟨cadence_four_dose_gain_lower (by linarith [hz.1]),
    (cadence_high_gain_bounds (by linarith [hz.1]) (by linarith [hz.2])).2⟩

end CadenceMixedNextSource
end KernelR.Hybrid
