import KernelR.HybridCausalHeadSignals
import KernelR.HybridPhysicalInvariant
import KernelR.HybridInputs
import KernelR.HybridContactTransversalityFrame

/-! Inductive finite feed-forward construction on a common physical horizon.

The leaf is the only externally queued source. Each next one-cell response is
constructed against the preceding *actual* emission ledger. Its queue is an
analysis queue: the global queue receives those wires only at actual FIREs.
The induction below constructs a real execution for every finite depth from a
local response constructor. It does not assert that arbitrary contacts admit
such responses, nor introduce dimension-changing births. -/
namespace KernelR.Hybrid

theorem SectionRun.cast_source {n θ route s v u kind i p first last count}
    {e : @Execution n θ route s u} (run : SectionRun kind i p e first last count)
    (same : v = s) : SectionRun kind i p (e.cast_source same) first last count := by
  cases same
  exact run


/-- Fixed physical coordinates, parameters, and strictly delayed contacts.
The newly added cell is index zero; every previous index moves by `Fin.succ`. -/
structure FiniteCausalChainData where
  leafParameters : Parameters
  leafSource : Snapshot 1
  headParameters : ℕ → Parameters
  headSource : ℕ → Snapshot 1
  common_clock : ∀ n, (headSource n).time=leafSource.time
  contacts : (n : ℕ) → HeadRoutes (n+1)
  strict_contacts : ∀ n, StrictHeadRoutes (contacts n)

namespace FiniteCausalChainData

noncomputable def parameters (d : FiniteCausalChainData) : (n : ℕ) → Fin (n+1) → Parameters
  | 0 => fun _ => d.leafParameters
  | n+1 => prependParameters (fun _ : Fin 1 => d.headParameters n) (d.parameters n)

noncomputable def route (d : FiniteCausalChainData) : (n : ℕ) → Router (n+1)
  | 0 => fun _ _ => []
  | n+1 => prependRouted (d.route n) (d.contacts n)

/-- The physical source queue is only the shifted original external queue. -/
noncomputable def source (d : FiniteCausalChainData) : (n : ℕ) → Snapshot (n+1)
  | 0 => d.leafSource
  | n+1 => (d.source n).prependQueued (d.headSource n) ((d.source n).pending.map Delivery.succ)

def liftLeafDelivery : (n : ℕ) → Delivery 1 → Delivery (n+1)
  | 0,token => token
  | n+1,token => (liftLeafDelivery n token).succ

theorem source_clock (d : FiniteCausalChainData) (n : ℕ) :
    (d.source n).time=d.leafSource.time := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem source_pending (d : FiniteCausalChainData) (n : ℕ) :
    (d.source n).pending=d.leafSource.pending.map (liftLeafDelivery n) := by
  induction n with
  | zero => simp [source,liftLeafDelivery]
  | succ n ih =>
    change (d.source n).pending.map Delivery.succ=_
    rw [ih,List.map_map]
    rfl

theorem leaf_destination (n : ℕ) (token : Delivery 1) :
    (liftLeafDelivery n token).cell=Fin.last n := by
  induction n with
  | zero => change token.cell=(0:Fin 1); exact Subsingleton.elim _ _
  | succ n ih => exact congrArg Fin.succ ih

theorem source_external_only (d : FiniteCausalChainData) (n : ℕ) (token : Delivery (n+1))
    (ht : token∈(d.source n).pending) : token.cell=Fin.last n := by
  rw [d.source_pending n] at ht
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp ht
  exact leaf_destination n original

theorem source_queue_length (d : FiniteCausalChainData) (n : ℕ) :
    (d.source n).pending.length=d.leafSource.pending.length := by
  rw [d.source_pending n,List.length_map]

end FiniteCausalChainData

/-- A real one-cell response; no global reaching execution is supplied. -/
structure FiniteCausalCell (parameter : Parameters) (source : Snapshot 1) (T : ℝ) where
  final : Snapshot 1
  execution : Execution (fun _ : Fin 1 => parameter) (fun _ _ => []) source final
  complete : CompleteThrough execution T
  ready : ReadyCoordinates final 0
  charge : final.x 0 .q=1/10
  raw_none : ∀ q, final.raw 0 q=none
  pending : final.pending=[]

/-- A constructed stage retains all physical local traces and their exact
ordered FIRE calendars, not merely a guessed global schedule. -/
structure FiniteCausalChainStage (d : FiniteCausalChainData) (T : ℝ) (n : ℕ) where
  final : Snapshot (n+1)
  execution : Execution (d.parameters n) (d.route n) (d.source n) final
  complete : CompleteThrough execution T
  ready : ∀ i, ReadyCoordinates final i
  charge : ∀ i, final.x i .q=1/10
  raw_none : ∀ i q, final.raw i q=none
  pending : final.pending=[]
  physical : PhysicalInvariant (d.parameters n) final
  raw_valid : RawValid final
  cells : (i : Fin (n+1)) → Σ source, FiniteCausalCell (d.parameters n i) source T
  emission_times : ∀ i, execution.emissionTimes i=(cells i).2.execution.emissionTimes 0
  cell_values : ∀ i, final.x i=(cells i).2.final.x 0
  contacts_transversal : (∀ i, (cells i).2.execution.ContactsTransversal) →
    execution.ContactsTransversal
  section_runs : ∀ kind i p first last count,
    SectionRun kind 0 p (cells i).2.execution first last count →
      SectionRun kind i p execution first last count

namespace FiniteCausalChainStage
variable {d : FiniteCausalChainData} {T : ℝ} {n : ℕ}

theorem energy_actual (stage : FiniteCausalChainStage d T n) (i : Fin (n+1)) :
    stage.final.x i .energy=(stage.cells i).2.final.x 0 .energy :=
  congrFun (stage.cell_values i) .energy

/-- Every additional physical response sees the exact inputs extracted from
this stage's actual ledger. This operation never inserts them globally. -/
noncomputable def nextSource (stage : FiniteCausalChainStage d T n) : Snapshot 1 :=
  (d.headSource n).requeue (stage.execution.headInputQueue (d.contacts n))

/-- One inductive extension, constructed by the causal weaver. The head's
initial queue is fixed by the old actual ledger, rather than postulated as an
operational global queue. -/
theorem extend_exists (stage : FiniteCausalChainStage d T n)
    (head : FiniteCausalCell (d.headParameters n) stage.nextSource T) {ε}
    (hb : PhysicalBox (d.parameters (n+1)) ε)
    (hf : PhysicalInvariant (d.parameters (n+1)) (d.source (n+1)))
    (hv : RawValid (d.source (n+1))) :
    Nonempty (FiniteCausalChainStage d T (n+1)) := by
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
  refine ⟨{
    final:=stage.final.prependQueued head.final weave.pending,execution:=execution
    complete:=?_,ready:=?_,charge:=?_,raw_none:=?_
    pending:=weave.pending_empty stage.pending head.pending
    physical:=execution.physical_invariant hb hf,raw_valid:=execution.raw_valid hv
    cells:=cells,emission_times:=?_,cell_values:=?_
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
  }⟩
  · simpa only [CompleteThrough,FiniteCausalChainData.route] using weave.complete stage.complete head.complete
  · intro i
    cases i using Fin.cases with
    | zero => exact ⟨head.ready.ready,head.ready.charge,head.ready.auxiliary⟩
    | succ i => exact ⟨(stage.ready i).ready,(stage.ready i).charge,(stage.ready i).auxiliary⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact head.charge
    | succ i => exact stage.charge i
  · intro i q
    cases i using Fin.cases with
    | zero => exact head.raw_none q
    | succ i => exact stage.raw_none i q
  · intro i
    cases i using Fin.cases with
    | zero => exact (htimes 0).trans weave.head_emission_times
    | succ i => exact (htimes i.succ).trans ((weave.tail_emission_times i).trans (stage.emission_times i))
  · intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact stage.cell_values i

end FiniteCausalChainStage

/-- Genuine induction over every finite depth. The only response premise is
an executable one-cell constructor against each preceding actual stage.
Instantiating it from packet/band lemmas is a separate physical obligation;
no global reaching or preloaded-wire premise occurs here. -/
theorem finite_causal_chain_exists (d : FiniteCausalChainData) (T : ℝ) {ε}
    (leaf : FiniteCausalCell d.leafParameters d.leafSource T)
    (hb : ∀ n, PhysicalBox (d.parameters n) ε)
    (hf : ∀ n, PhysicalInvariant (d.parameters n) (d.source n))
    (hv : ∀ n, RawValid (d.source n))
    (constructHead : ∀ n (stage : FiniteCausalChainStage d T n),
      Nonempty (FiniteCausalCell (d.headParameters n) stage.nextSource T)) :
    ∀ n, Nonempty (FiniteCausalChainStage d T n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨{
      final:=leaf.final,execution:=leaf.execution,complete:=leaf.complete
      ready:=?_,charge:=?_,raw_none:=?_,pending:=leaf.pending
      physical:=leaf.execution.physical_invariant (hb 0) (hf 0)
      raw_valid:=leaf.execution.raw_valid (hv 0)
      cells:=fun _ => ⟨d.leafSource,leaf⟩,emission_times:=?_,cell_values:=?_
      contacts_transversal:=fun localContacts => localContacts 0
      section_runs:=by
        intro kind i p first last count localRun
        fin_cases i
        exact localRun
    }⟩
    · intro i; fin_cases i; exact leaf.ready
    · intro i; fin_cases i; exact leaf.charge
    · intro i q; fin_cases i; exact leaf.raw_none q
    · intro i; fin_cases i; rfl
    · intro i; fin_cases i; rfl
  | succ n ih =>
    obtain ⟨stage⟩ := ih
    obtain ⟨head⟩ := constructHead n stage
    exact stage.extend_exists head (hb (n+1)) (hf (n+1)) (hv (n+1))

end KernelR.Hybrid
