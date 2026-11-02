import KernelR.HybridFiniteChainLeafPreparation
import KernelR.HybridConstructedCadenceLeafK
import KernelR.HybridEvents

/-! A native one-cell leaf from its own READY birth. All preparation and
cadence sources are present from the start. The preparation consumes only
its sixteen port1 tokens and preserves the entire future port0 source train.
The subsequent cadence and its emitted packet are constructed physically. -/
namespace KernelR.Hybrid

private theorem birth_leaf_emitted_bounds {θ route s u}
    (e : @Execution 1 θ route s u) (t : ℝ) (ht : t ∈ e.emissionTimes 0) :
    s.time ≤ t ∧ t ≤ u.time := by
  change t ∈ (e.ledger.emissions.filter (fun event => event.1 = 0)).map Prod.snd at ht
  obtain ⟨event,he,rfl⟩ := List.mem_map.mp ht
  exact e.emission_time_bounds event (List.mem_filter.mp he).1

structure ConstructedBirthCadenceLeafK (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (K : ℕ) (terminal : ℝ) where
  preparation : FiniteChainLeafPreparation θ born (sourceTrain 0 0 160 4 K)
  leaf : ConstructedCadenceLeafK θ preparation.final 0 160 K terminal
  execution : Execution θ (fun _ _ => []) born leaf.final
  reconstruct : execution = preparation.execution.append leaf.execution
  date : leaf.final.time = terminal
  ready : ∀ j, ReadyCoordinates leaf.final j
  charge : leaf.final.x 0 .q = 1 / 10
  raw_none : ∀ j p, leaf.final.raw j p = none
  pending : leaf.final.pending = []
  gain_port0 : leaf.final.x 0 (.z 0) = born.x 0 (.z 0) + 12 / 5
  gain_port1 : leaf.final.x 0 (.z 1) = born.x 0 (.z 1) + 3 / 5
  gain_port2 : leaf.final.x 0 (.z 2) = born.x 0 (.z 2)
  recovery : leaf.final.x 0 .b = born.x 0 .b + 3 / 10
  emission_count : (execution.emissionTimes 0).length = K + 9
  calendar : execution.emissionTimes 0 = preparation.execution.emissionTimes 0 ++
    leaf.execution.emissionTimes 0
  fast_calendar : (execution.emissionTimes 0).filter (fun t => (160 : ℝ) ≤ t) =
    leaf.execution.emissionTimes 0
  deliveries : execution.deliveries = sourceTrain 0 1 0 8 16 ++ sourceTrain 0 0 160 4 K
  delivered_sources : execution.deliveries = born.pending
  delivery_count : execution.deliveries.length = 16 + K
  physical : PhysicalInvariant θ leaf.final
  raw_valid : RawValid leaf.final
  complete : CompleteThrough execution terminal

noncomputable abbrev ConstructedBirthCadenceLeafK.final {θ born K terminal}
    (c : ConstructedBirthCadenceLeafK θ born K terminal) : Snapshot 1 := c.leaf.final

/-- The caller supplies a full admissible birth and its real external source
program. Preparation, the K-input cadence, all doses and the actual emitted
calendar are conclusions; no prepared state or reaching trace is a premise. -/
theorem birth_cadence_leaf_k_exists {θ ε born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready) (K : ℕ) (terminal : ℝ) (hK : 9 ≤ K)
    (hqueue : born.pending = sourceTrain 0 1 0 8 16 ++ sourceTrain 0 0 160 4 K)
    (hterminal : (160 : ℝ) + 4 * (K : ℝ) < terminal) :
    Nonempty (ConstructedBirthCadenceLeafK θ born K terminal) := by
  obtain ⟨prep⟩ := finite_chain_leaf_preparation_exists hborn hb ha
    (sourceTrain 0 0 160 4 K) hqueue (by
      intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      change (160 : ℝ) ≤ 160 + 4 * (k.val : ℝ)
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val])
  have hzBorn : Real.log (3 / 10) - 1 / 100000 ≤ born.x 0 (.z 0) ∧
      born.x 0 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000 := by
    have h := ((hborn.2.2 0).2.2.2.2 (0 : Port)).1
    simpa only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] using h
  have hz : Real.log (3 / 10) - 1 / 100000 ≤ prep.final.x 0 (.z 0) ∧
      prep.final.x 0 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [prep.gain_port0]
    exact hzBorn
  have hB : 17999 / 100000 ≤ prep.final.x 0 .b ∧
      prep.final.x 0 .b ≤ 18001 / 100000 := by
    have hRec : prep.final.x 0 .b = born.x 0 .b + 1 / 10 := prep.recovery
    have h := (hborn.2.2 0).2.2.1
    rw [hRec]
    constructor <;> linarith [h.1,h.2]
  obtain ⟨leaf⟩ := constructed_cadence_leaf_k_exists hb prep.final 0 160 K terminal hK
    prep.physical prep.raw_valid prep.prepared prep.charge (fun p => prep.raw_none 0 p)
    hz hB prep.pending (by rw [prep.date]; norm_num) hterminal
  let execution := prep.execution.append leaf.execution
  have hCalendar : execution.emissionTimes 0 = prep.execution.emissionTimes 0 ++
      leaf.execution.emissionTimes 0 := prep.execution.emissionTimes_append leaf.execution 0
  have hPrepBefore : ∀ t ∈ prep.execution.emissionTimes 0, t < (160 : ℝ) := by
    intro t ht
    have h := (birth_leaf_emitted_bounds prep.execution t ht).2
    change t ≤ (1599 / 10 : ℝ) at h
    linarith
  have hFastAfter : ∀ t ∈ leaf.execution.emissionTimes 0, (160 : ℝ) ≤ t := by
    intro t ht
    rw [leaf.calendar] at ht
    rcases List.mem_cons.mp ht with ht | ht
    · subst t
      linarith [leaf.first_window.1]
    · have h := (birth_leaf_emitted_bounds leaf.tail.execution t ht).1
      linarith [leaf.mark_date]
  have hFastCalendar : (execution.emissionTimes 0).filter (fun t => (160 : ℝ) ≤ t) =
      leaf.execution.emissionTimes 0 := by
    rw [hCalendar,List.filter_append]
    have hPrep : (prep.execution.emissionTimes 0).filter (fun t => (160 : ℝ) ≤ t) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t ht
      simpa only [decide_eq_true_eq] using (not_le.mpr (hPrepBefore t ht))
    have hFast : (leaf.execution.emissionTimes 0).filter (fun t => (160 : ℝ) ≤ t) =
        leaf.execution.emissionTimes 0 := by
      apply List.filter_eq_self.mpr
      intro t ht
      simpa only [decide_eq_true_eq] using hFastAfter t ht
    rw [hPrep,hFast,List.nil_append]
  have hDeliveries : execution.deliveries = sourceTrain 0 1 0 8 16 ++ sourceTrain 0 0 160 4 K := by
    exact (prep.execution.deliveries_append leaf.execution).trans
      (congrArg₂ List.append prep.deliveries leaf.deliveries)
  refine ⟨{
    preparation := prep, leaf := leaf, execution := execution, reconstruct := rfl
    date := leaf.date, ready := leaf.ready, charge := leaf.charge, raw_none := leaf.raw_none
    pending := leaf.pending, gain_port0 := ?_, gain_port1 := ?_, gain_port2 := ?_, recovery := ?_
    emission_count := ?_, calendar := hCalendar, fast_calendar := hFastCalendar
    deliveries := hDeliveries, delivered_sources := hDeliveries.trans hqueue.symm
    delivery_count := ?_, physical := leaf.physical, raw_valid := leaf.raw_valid, complete := leaf.complete
  }⟩
  · have hGain : leaf.final.x 0 (.z 0) = prep.final.x 0 (.z 0) + 12 / 5 := leaf.gain_target
    rw [hGain,prep.gain_port0]
  · have hGain : leaf.final.x 0 (.z 1) = prep.final.x 0 (.z 1) := leaf.gain_other 1 (by decide)
    exact hGain.trans prep.gain_target
  · have hGain : leaf.final.x 0 (.z 2) = prep.final.x 0 (.z 2) := leaf.gain_other 2 (by decide)
    exact hGain.trans (prep.gain_other 2 (by decide))
  · have hRec : leaf.final.x 0 .b = prep.final.x 0 .b + 1 / 5 := leaf.recovery
    have hPrep : prep.final.x 0 .b = born.x 0 .b + 1 / 10 := prep.recovery
    rw [hRec,hPrep]
    ring
  · rw [hCalendar,List.length_append,prep.emission_count,leaf.emission_count]
    omega
  · rw [hDeliveries,List.length_append]
    simp [sourceTrain]

namespace ConstructedBirthCadenceLeafK
variable {θ born K terminal} (c : ConstructedBirthCadenceLeafK θ born K terminal)

/-- The cadence packet is the genuine post-preparation emitted signal. The
fourteen earlier preparation FIREs remain in the complete execution ledger. -/
noncomputable abbrev packet : KernelR.Chain.Packet 3 (K - 8) 0 := c.leaf.packet

theorem packet_calendar : (c.execution.emissionTimes 0).filter (fun t => (160 : ℝ) ≤ t) =
    List.ofFn (fun i : Fin (3 + (K - 8)) => c.packet.actual i.val) :=
  c.fast_calendar.trans c.leaf.packet_calendar

end ConstructedBirthCadenceLeafK
end KernelR.Hybrid
