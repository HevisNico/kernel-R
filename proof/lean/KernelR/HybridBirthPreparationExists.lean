import KernelR.HybridBirthPrepared40
import KernelR.HybridBirthSourceTrain
import KernelR.HybridPreparedLearnedTrainExistence

namespace KernelR.Hybrid

/-- The initial sixteen-source preparation is exhibited by its actual
birth execution. The second source train remains queued. -/
structure ConstructedBirthPreparation (θ : Fin 1 → Parameters) (born : Snapshot 1) where
  at40 : BirthPrepared40 θ born
  final : Snapshot 1
  suffix : Execution θ (fun _ _ => []) at40.final final
  suffix_contacts_transversal : suffix.ContactsTransversal
  date : final.time = 128
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j p, final.raw j p = none
  pending : final.pending = sourceTrain 0 0 160 8 16
  deliveries_suffix : suffix.deliveries = sourceTrain 0 0 48 8 10
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete_suffix : CompleteThrough suffix 128

noncomputable def ConstructedBirthPreparation.execution {θ born}
    (c : ConstructedBirthPreparation θ born) : Execution θ (fun _ _ => []) born c.final :=
  c.at40.execution.append c.suffix

theorem ConstructedBirthPreparation.contacts_transversal {θ born}
    (c : ConstructedBirthPreparation θ born) : c.execution.ContactsTransversal := by
  rw [ConstructedBirthPreparation.execution, Execution.contactsTransversal_append]
  exact ⟨c.at40.contacts_transversal, c.suffix_contacts_transversal⟩

theorem ConstructedBirthPreparation.deliveries {θ born} (c : ConstructedBirthPreparation θ born) :
    c.execution.deliveries = sourceTrain 0 0 0 8 16 := by
  simp only [ConstructedBirthPreparation.execution,Execution.deliveries_append,
    c.at40.deliveries,c.deliveries_suffix]
  norm_num [sourceTrain,List.ofFn_succ]

theorem ConstructedBirthPreparation.complete {θ born} (c : ConstructedBirthPreparation θ born) :
    CompleteThrough c.execution 128 := c.complete_suffix

/-- The existing analytical preparation theorem is applied only after its
reaching execution and calendar have been physically constructed. -/
theorem ConstructedBirthPreparation.outcome {θ ε born}
    (c : ConstructedBirthPreparation θ born) (hb : PhysicalBox θ ε) :
    Nonempty (BirthSourceTrain c.execution 0 0) := by
  exact c.execution.birth_low_train c.at40.mark.first.weak.birth hb 0 0 (by decide)
    c.at40.mark.initial_aux c.deliveries (by rw [c.date])

theorem BirthPrepared40.preparation_exists {θ ε born} (c : BirthPrepared40 θ born)
    (hb : PhysicalBox θ ε) : Nonempty (ConstructedBirthPreparation θ born) := by
  have hs : ∀ j, PreparedSection c.final j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact c.prepared
  have hg : 9 / 5 ≤ Real.exp (c.final.x 0 (.z 0)) ∧ Real.exp (c.final.x 0 (.z 0)) ≤ 2 := by
    have hz := ((c.mark.first.weak.birth.2.2 0).2.2.2.2 (0 : Port)).1
    simp only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] at hz
    apply learned_gain_bounds
    · rw [c.gain_target]; linarith [hz.1]
    · rw [c.gain_target]; linarith [hz.2]
  have hr : c.final.raw 0 0 = some c.final.time := by rw [c.date]; exact c.raw_active
  have hqueue : c.final.pending = sourceTrain 0 0 (c.final.time + 8) 8 10 ++ sourceTrain 0 0 160 8 16 := by
    rw [c.date]
    norm_num
    exact c.pending
  obtain ⟨train⟩ := prepared_learned_train_exists hb c.final 10 (sourceTrain 0 0 160 8 16)
    c.physical c.raw_valid hs hg hr c.raw_other hqueue (by
      intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      rw [c.date]
      dsimp
      have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
      linarith)
  have htime : train.final.time < (128 : ℝ) := by rw [train.date,c.date]; norm_num
  have hmain : ∀ j, train.final.main j = .ready := fun j => (train.ready j).ready
  have haux : ∀ j p, train.final.aux j p = .ready := fun j p => ((train.ready j).auxiliary p).1
  have hq : ∀ j, train.final.x j .q < 1 := fun j => by linarith [(train.ready j).charge.2]
  have hm : ∀ j p, train.final.x j (.m p) < 1 := fun j p => by linarith [((train.ready j).auxiliary p).2.2]
  have hfuture : ∀ d ∈ train.final.pending, (128 : ℝ) < d.due := by
    intro d hd
    rw [train.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    dsimp
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    linarith
  let flow : Flow θ train.final (quietAt train.final 128) :=
    quietFlow train.final htime hmain haux train.raw_none hq hm (fun d hd => (hfuture d hd).le)
  let quiet : Execution θ (fun _ _ => []) train.final (quietAt train.final 128) :=
    .cons (.flow flow) (.nil _)
  let suffix := train.execution.append quiet
  obtain ⟨_,hcomplete⟩ := quiet_complete_exists (θ := θ) (route := fun _ _ => [])
    train.final htime hmain haux train.raw_none hq hm hfuture
  refine ⟨{
    at40 := c
    final := quietAt train.final 128
    suffix := suffix
    suffix_contacts_transversal := by
      exact (Execution.contactsTransversal_append train.execution quiet).mpr
        ⟨train.contacts_transversal, trivial⟩
    date := rfl
    ready := fun j => quietAt_ready_coordinates train.final j (train.ready j) htime.le
    charge := ?_
    raw_none := train.raw_none
    pending := train.pending
    deliveries_suffix := ?_
    physical := suffix.physical_invariant hb c.physical
    raw_valid := suffix.raw_valid c.raw_valid
    complete_suffix := hcomplete
  }⟩
  · simp [quietAt,quietValues,train.charge,relax]
  · simp only [suffix,Execution.deliveries_append,train.deliveries,quiet,
      Execution.deliveries,Move.deliveries,List.append_nil]
    rw [c.date]
    norm_num

/-- Actual first-train existence from the original birth assumptions, with
no supplied reaching execution, pulse word, count, dose or firing calendar. -/
theorem birth_protocol_preparation_exists {θ ε born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    ∃ c : ConstructedBirthPreparation θ born, Nonempty (BirthSourceTrain c.execution 0 0) := by
  obtain ⟨first⟩ := birth_protocol_prepared40_exists hborn hb ha hqueue
  obtain ⟨c⟩ := first.preparation_exists hb
  exact ⟨c,c.outcome hb⟩

end KernelR.Hybrid
