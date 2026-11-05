import KernelR.HybridBirthPreparationExists
import KernelR.HybridLocalSourceRestriction
import KernelR.HybridContactSourceRestriction
import KernelR.HybridBirthPreparationSectionCovers
import KernelR.HybridDoseCountingQueueTransport

/-! A sixteen-input low-port preparation with an independently selected future
source program. The existing birth constructor is restricted as an entire
isolated source program, before any finite-family network is assembled. -/
namespace KernelR.Hybrid
attribute [local instance] Classical.propDecidable

private theorem restriction_contacts {θ s u cutoff}
    {e : @Execution 1 θ (fun _ _ => []) s u}
    {f : Execution θ (fun _ _ => []) ((retainSourcesRequeue cutoff).apply s)
      ((retainSourcesRequeue cutoff).apply u)}
    (copy : Execution.RequeueCopy (retainSourcesRequeue cutoff) e f) :
    f.ContactsTransversal ↔ e.ContactsTransversal := by
  induction copy with
  | nil => rfl
  | cons step tail ih =>
    cases step with
    | flow f g path => exact ih
    | jump j j' => exact Iff.and (j.contactTransversal_requeue j').symm ih

noncomputable def lowPreparationShadow (born : Snapshot 1) : Snapshot 1 :=
  {born with pending := sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16}

private theorem low_preparation_initial_filter (born : Snapshot 1)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16) :
    retainSourcesThrough 128 (lowPreparationShadow born) = born := by
  have hFirst : (sourceTrain (0 : Fin 1) 0 0 8 16).filter (fun d => decide (d.due ≤ (128 : ℝ))) =
      sourceTrain 0 0 0 8 16 := by
    apply List.filter_eq_self.mpr
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (k.val : ℝ) < 16 := by exact_mod_cast k.isLt
    simp only [decide_eq_true_eq]
    change (0 : ℝ) + 8 * (k.val : ℝ) ≤ 128
    linarith
  have hSecond : (sourceTrain (0 : Fin 1) 0 160 8 16).filter (fun d => decide (d.due ≤ (128 : ℝ))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    simp only [decide_eq_true_eq]
    change ¬(160 : ℝ) + 8 * (k.val : ℝ) ≤ 128
    linarith
  simp only [retainSourcesThrough,lowPreparationShadow,List.filter_append,hFirst,hSecond,List.append_nil]
  cases born
  simp_all

structure FiniteChainLowPreparation (θ : Fin 1 → Parameters) (born : Snapshot 1) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) born final
  covered : execution.SectionCovered
  contacts_transversal : execution.ContactsTransversal
  date : final.time = 1599 / 10
  prepared : PreparedSection final 0
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j p, final.raw j p = none
  pending : final.pending = []
  gain_target : final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5
  gain_other : ∀ p, p ≠ 0 → final.x 0 (.z p) = born.x 0 (.z p)
  recovery : final.x 0 .b = born.x 0 .b + 1 / 10
  emission_count : (execution.emissionTimes 0).length = 12
  deliveries : execution.deliveries = sourceTrain 0 0 0 8 16
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (1599 / 10)

theorem finite_chain_low_preparation_exists {θ ε born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16) :
    Nonempty (FiniteChainLowPreparation θ born) := by
  have hShadow : BirthState (lowPreparationShadow born) := hborn
  obtain ⟨c,⟨outcome⟩⟩ := birth_protocol_preparation_exists hShadow hb ha rfl
  have hInitial := low_preparation_initial_filter born hqueue
  obtain ⟨rawCut, copy, hLedger, hDelivered⟩ :=
    c.execution.retainSourcesThrough_emptyRoute_copy 128 c.date.le
  have cCovered := c.section_covered hb
  have rawCovered : rawCut.SectionCovered := by
    constructor
    · intro i p
      obtain ⟨cover⟩ := cCovered.1 i p
      exact cover.requeueCopy_exists copy
    · intro i p
      obtain ⟨cover⟩ := cCovered.2 i p
      exact cover.requeueCopy_exists copy
  have hTransport : ∃ cut : Execution θ (fun _ _ => [])
      (retainSourcesThrough 128 (lowPreparationShadow born)) (retainSourcesThrough 128 c.final),
      cut.ledger = c.execution.ledger ∧ cut.deliveries = c.execution.deliveries ∧
        cut.ContactsTransversal ∧ cut.SectionCovered :=
    ⟨rawCut, hLedger, hDelivered, (restriction_contacts copy).mpr c.contacts_transversal, rawCovered⟩
  rw [hInitial] at hTransport
  obtain ⟨cut,hLedger,hDelivered,hCutTransversal,cutCovered⟩ := hTransport
  let resting := retainSourcesThrough 128 c.final
  have hPending : resting.pending = [] := by
    change c.final.pending.filter _ = []
    rw [c.pending]
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    simp only [decide_eq_true_eq]
    change ¬(160 : ℝ) + 8 * (k.val : ℝ) ≤ 128
    linarith
  have hBefore : resting.time < (1599 / 10 : ℝ) := by change c.final.time < _; rw [c.date]; norm_num
  have hReady : ∀ j, ReadyCoordinates resting j := by
    intro j
    exact ⟨(c.ready j).ready,(c.ready j).charge,(c.ready j).auxiliary⟩
  have hFuture : ∀ d ∈ resting.pending, (1599 / 10 : ℝ) < d.due := by
    intro d hd
    rw [hPending] at hd
    contradiction
  let flow : Flow θ resting (quietAt resting (1599 / 10)) := quietFlow resting hBefore
    (fun j => (hReady j).ready) (fun j p => ((hReady j).auxiliary p).1) c.raw_none
    (fun j => by linarith [(hReady j).charge.2])
    (fun j p => by linarith [((hReady j).auxiliary p).2.2]) (fun d hd => (hFuture d hd).le)
  let wait : Execution θ (fun _ _ => []) resting (quietAt resting (1599 / 10)) :=
    .cons (.flow flow) (.nil _)
  let execution := cut.append wait
  have waitCovered : wait.SectionCovered := by
    constructor
    · intro i p
      exact ⟨wait.errorCover_of_inactive i p ⟨Or.inl (by rw [((hReady i).auxiliary p).1]; decide), trivial⟩⟩
    · intro i p
      exact ⟨wait.markCover_of_inactive i p ⟨Or.inr (hReady i).ready, trivial⟩⟩
  obtain ⟨_,hComplete⟩ := quiet_complete_exists (θ := θ) (route := fun _ _ => []) resting hBefore
    (fun j => (hReady j).ready) (fun j p => ((hReady j).auxiliary p).1) c.raw_none
    (fun j => by linarith [(hReady j).charge.2])
    (fun j p => by linarith [((hReady j).auxiliary p).2.2]) hFuture
  have hFinalReady := quietAt_ready_coordinates resting 0 (hReady 0) hBefore.le
  refine ⟨{
    final := quietAt resting (1599 / 10), execution := execution, date := rfl
    covered := cutCovered.append waitCovered
    contacts_transversal := (Execution.contactsTransversal_append cut wait).mpr ⟨hCutTransversal, trivial⟩
    prepared := ⟨hFinalReady.ready,hFinalReady.charge,outcome.prepared.recovery,hFinalReady.auxiliary⟩
    charge := ?_, raw_none := c.raw_none, pending := hPending
    gain_target := outcome.gain_target, gain_other := outcome.gain_other
    recovery := outcome.recovery_gain, emission_count := ?_, deliveries := ?_
    physical := execution.physical_invariant hb (hborn.physical_invariant hb)
    raw_valid := execution.raw_valid hborn.raw_valid, complete := hComplete
  }⟩
  · change relax (1 / 2) (1 / 10) (c.final.x 0 .q) c.final.time (1599 / 10) = 1 / 10
    rw [c.charge]
    simp [relax]
  · change ((cut.append wait).emissionTimes 0).length = 12
    rw [Execution.emissionTimes_append]
    have hw : wait.emissionTimes 0 = [] := by simp [wait,Execution.emissionTimes,Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero]
    rw [hw,List.append_nil]
    change ((cut.ledger.emissions.filter (fun e => e.1 = 0)).map Prod.snd).length = 12
    rw [hLedger]
    exact outcome.emissions
  · change (cut.append wait).deliveries = _
    rw [Execution.deliveries_append]
    have hw : wait.deliveries = [] := rfl
    rw [hw,List.append_nil,hDelivered,c.deliveries]

end KernelR.Hybrid
