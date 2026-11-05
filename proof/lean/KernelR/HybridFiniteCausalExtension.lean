import KernelR.HybridFiniteCausalChain

/-! A strong inductive extension retains the exact old stage and actual new
head. These equalities allow the next packet invariant to refer to the actual
returned stage, rather than an existentially unrelated signal witness. -/
namespace KernelR.Hybrid

structure FiniteCausalExtension {d : FiniteCausalChainData} {T : ℝ} {n : ℕ}
    (stage : FiniteCausalChainStage d T n)
    (head : FiniteCausalCell (d.headParameters n) stage.nextSource T) where
  next : FiniteCausalChainStage d T (n+1)
  weave : CausalHeadWeave stage.execution head.execution
    ((d.source n).pending.map Delivery.succ) (d.contacts n)
  execution_eq : HEq next.execution weave.execution
  final_state : next.final=stage.final.prependQueued head.final weave.pending
  head_times : next.execution.emissionTimes 0=head.execution.emissionTimes 0
  tail_times : ∀ i, next.execution.emissionTimes i.succ=stage.execution.emissionTimes i
  head_values : next.final.x 0=head.final.x 0
  tail_values : ∀ i, next.final.x i.succ=stage.final.x i
  contacts_transversal : stage.execution.ContactsTransversal →
    head.execution.ContactsTransversal → next.execution.ContactsTransversal
  tail_sections : ∀ kind i p first last count,
    SectionRun kind i p stage.execution first last count →
      SectionRun kind i.succ p next.execution first last count
  head_sections : ∀ kind p first last count,
    SectionRun kind 0 p head.execution first last count →
      SectionRun kind 0 p next.execution first last count

/-- Construct the actual next stage with an explicit bridge to both physical
input traces. This is stronger than a bare existential stage constructor. -/
theorem finite_causal_extension_exists {d : FiniteCausalChainData} {T : ℝ} {n : ℕ}
    (stage : FiniteCausalChainStage d T n)
    (head : FiniteCausalCell (d.headParameters n) stage.nextSource T) {ε}
    (hb : PhysicalBox (d.parameters (n+1)) ε)
    (hf : PhysicalInvariant (d.parameters (n+1)) (d.source (n+1)))
    (hv : RawValid (d.source (n+1))) :
    Nonempty (FiniteCausalExtension stage head) := by
  have hstart : (d.source n).time=stage.nextSource.time :=
    (d.source_clock n).trans (d.common_clock n).symm
  have hqueue : stage.nextSource.pending=stage.execution.headInputQueue (d.contacts n) := rfl
  have hbalance := HeadQueueBalance.initial stage.execution stage.nextSource (d.contacts n) hqueue
  obtain ⟨weave⟩ := stage.execution.prepend_causal_result head.execution hstart
    (stage.complete.1.trans head.complete.1.symm) (d.contacts n) (d.strict_contacts n)
    ((d.source n).pending.map Delivery.succ) hbalance
  have hsource : (d.source n).prependQueued stage.nextSource
      ((d.source n).pending.map Delivery.succ)=d.source (n+1) := rfl
  let execution := weave.execution.cast_source hsource.symm
  have hledger : execution.ledger=weave.execution.ledger := weave.execution.cast_source_ledger hsource.symm
  have htimes (i : Fin (n+1+1)) : execution.emissionTimes i=weave.execution.emissionTimes i := by
    simp only [Execution.emissionTimes,hledger]
  let cells : (i : Fin (n+1+1)) → Σ source, FiniteCausalCell (d.parameters (n+1) i) source T :=
    Fin.cases ⟨stage.nextSource,head⟩ stage.cells
  let next : FiniteCausalChainStage d T (n+1) := {
    final:=stage.final.prependQueued head.final weave.pending,execution:=execution
    complete:=by simpa only [CompleteThrough,FiniteCausalChainData.route] using weave.complete stage.complete head.complete
    ready:=by
      intro i
      cases i using Fin.cases with
      | zero => exact ⟨head.ready.ready,head.ready.charge,head.ready.auxiliary⟩
      | succ i => exact ⟨(stage.ready i).ready,(stage.ready i).charge,(stage.ready i).auxiliary⟩
    charge:=by
      intro i
      cases i using Fin.cases with
      | zero => exact head.charge
      | succ i => exact stage.charge i
    raw_none:=by
      intro i q
      cases i using Fin.cases with
      | zero => exact head.raw_none q
      | succ i => exact stage.raw_none i q
    pending:=weave.pending_empty stage.pending head.pending
    physical:=execution.physical_invariant hb hf,raw_valid:=execution.raw_valid hv
    cells:=cells
    section_runs:=by
      intro kind i p first last count localRun
      apply SectionRun.cast_source (same := hsource.symm)
      cases i using Fin.cases with
      | zero => exact weave.head_sections kind p first last count localRun
      | succ i =>
        exact weave.tail_sections kind i p first last count
          (stage.section_runs kind i p first last count localRun)
    contacts_transversal:=by
      intro localContacts
      apply (weave.execution.contactsTransversal_cast_source hsource.symm).2
      exact weave.contacts_transversal
        (stage.contacts_transversal (fun i => localContacts i.succ)) (localContacts 0)
    emission_times:=by
      intro i
      cases i using Fin.cases with
      | zero => exact (htimes 0).trans weave.head_emission_times
      | succ i => exact (htimes i.succ).trans ((weave.tail_emission_times i).trans (stage.emission_times i))
    cell_values:=by
      intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact stage.cell_values i
  }
  exact ⟨{
    next:=next,weave:=weave,execution_eq:=HEq.rfl,final_state:=rfl
    head_times:=(htimes 0).trans weave.head_emission_times
    tail_times:=fun i => (htimes i.succ).trans (weave.tail_emission_times i)
    head_values:=rfl,tail_values:=fun _ => rfl
    tail_sections:=by
      intro kind i p first last count run
      exact (weave.tail_sections kind i p first last count run).cast_source hsource.symm
    head_sections:=by
      intro kind p first last count run
      exact (weave.head_sections kind p first last count run).cast_source hsource.symm
    contacts_transversal:=by
      intro tailContacts headContacts
      exact (weave.execution.contactsTransversal_cast_source hsource.symm).2
        (weave.contacts_transversal tailContacts headContacts)
  }⟩

namespace FiniteCausalExtension
variable {d T n} {stage : FiniteCausalChainStage d T n}
  {head : FiniteCausalCell (d.headParameters n) stage.nextSource T}
  (extension : FiniteCausalExtension stage head)

theorem head_energy_actual : extension.next.final.x 0 .energy=head.final.x 0 .energy :=
  congrFun extension.head_values .energy

theorem tail_energy_actual (i : Fin (n+1)) : extension.next.final.x i.succ .energy=stage.final.x i .energy :=
  congrFun (extension.tail_values i) .energy

end FiniteCausalExtension
end KernelR.Hybrid
