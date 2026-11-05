import KernelR.HybridFiniteChainLowPreparation
import KernelR.HybridPortPermutation
import KernelR.HybridContactPortTransport
import KernelR.HybridDoseCountingTransport

/-! Prepare the relay's own low port two from its own original birth and
sixteen real direct sources. Port transport retains the complete physical
execution, including its energy path and actual deliveries. No future relay
contact or source is inserted during preparation. -/
namespace KernelR.Hybrid

private noncomputable def relay_restore_execution {θ θ' : Fin 1 → Parameters} {s s' u}
    (e : Execution θ' (fun _ _ => []) s' u) (hp : θ'=θ) (hs : s=s') :
    Execution θ (fun _ _ => []) s u := by cases hp; cases hs; exact e

private theorem relay_restore_ledger {θ θ' : Fin 1 → Parameters} {s s' u}
    (e : Execution θ' (fun _ _ => []) s' u) (hp : θ'=θ) (hs : s=s') :
    (relay_restore_execution e hp hs).ledger=e.ledger := by cases hp; cases hs; rfl

private theorem relay_restore_deliveries {θ θ' : Fin 1 → Parameters} {s s' u}
    (e : Execution θ' (fun _ _ => []) s' u) (hp : θ'=θ) (hs : s=s') :
    (relay_restore_execution e hp hs).deliveries=e.deliveries := by cases hp; cases hs; rfl

private theorem relay_restore_times {θ θ' : Fin 1 → Parameters} {s s' u}
    (e : Execution θ' (fun _ _ => []) s' u) (hp : θ'=θ) (hs : s=s') (i : Fin 1) :
    (relay_restore_execution e hp hs).emissionTimes i=e.emissionTimes i := by cases hp; cases hs; rfl

private theorem relay_restore_complete {θ θ' : Fin 1 → Parameters} {s s' u T}
    (e : Execution θ' (fun _ _ => []) s' u) (hp : θ'=θ) (hs : s=s') (hc : CompleteThrough e T) :
    CompleteThrough (relay_restore_execution e hp hs) T := by cases hp; cases hs; exact hc

private theorem relay_restore_transversal {θ θ' : Fin 1 → Parameters} {s s' u}
    (e : Execution θ' (fun _ _ => []) s' u) (hp : θ'=θ) (hs : s=s')
    (positive : e.ContactsTransversal) :
    (relay_restore_execution e hp hs).ContactsTransversal := by
  cases hp
  cases hs
  exact positive

private theorem relay_restore_covered {θ θ' : Fin 1 → Parameters} {s s' u}
    (e : Execution θ' (fun _ _ => []) s' u) (hp : θ'=θ) (hs : s=s')
    (covered : e.SectionCovered) :
    (relay_restore_execution e hp hs).SectionCovered := by
  cases hp
  cases hs
  exact covered

structure FiniteChainRelayPreparation (θ : Fin 1 → Parameters) (born : Snapshot 1) where
  low : FiniteChainLowPreparation (permuteParameters θ swapLowPorts) (born.permutePorts swapLowPorts)
  final : Snapshot 1
  final_state : final=low.final.permutePorts swapLowPorts.symm
  execution : Execution θ (fun _ _ => []) born final
  covered : execution.SectionCovered
  contacts_transversal : execution.ContactsTransversal
  date : final.time=1599/10
  prepared : PreparedSection final 0
  charge : final.x 0 .q=1/10
  raw_none : ∀ j p, final.raw j p=none
  pending : final.pending=[]
  gain_target : final.x 0 (.z 2)=born.x 0 (.z 2)+9/5
  gain_other : ∀ p, p≠2 → final.x 0 (.z p)=born.x 0 (.z p)
  recovery : final.x 0 .b=born.x 0 .b+1/10
  emission_times : ∀ i, execution.emissionTimes i=low.execution.emissionTimes i
  emission_count : (execution.emissionTimes 0).length=12
  deliveries : execution.deliveries=sourceTrain 0 2 0 8 16
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (1599/10)

/-- A relay starts with only its sixteen actual port-two teaching sources.
Both fabrication parameters and birth values remain the original cell's own. -/
theorem finite_chain_relay_preparation_exists {θ ε born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p=.ready)
    (hqueue : born.pending=sourceTrain 0 2 0 8 16) :
    Nonempty (FiniteChainRelayPreparation θ born) := by
  have hqueueLow : (born.permutePorts swapLowPorts).pending=sourceTrain 0 0 0 8 16 := by
    change born.pending.map (fun d => d.permutePorts swapLowPorts)=_
    rw [hqueue,sourceTrain_permutePorts]
    simp only [swapLowPorts_symm,swapLowPorts_two]
  obtain ⟨low⟩ := finite_chain_low_preparation_exists hborn.swapLowPorts (hb.permutePorts swapLowPorts)
    (fun p => ha (swapLowPorts p)) hqueueLow
  let transported := low.execution.permutePorts swapLowPorts.symm
  have hp : permuteParameters (permuteParameters θ swapLowPorts) swapLowPorts.symm=θ :=
    permuteParameters_inverse θ swapLowPorts
  have hs : born=(born.permutePorts swapLowPorts).permutePorts swapLowPorts.symm :=
    (Snapshot.permutePorts_inverse born swapLowPorts).symm
  let execution := relay_restore_execution transported hp hs
  have transportedCovered : transported.SectionCovered := by
    constructor
    · intro i p
      obtain ⟨cover⟩ := low.covered.1 i (swapLowPorts.symm p)
      simpa only [Equiv.symm_symm, Equiv.apply_symm_apply, transported] using
        cover.permutePorts_exists swapLowPorts.symm
    · intro i p
      obtain ⟨cover⟩ := low.covered.2 i (swapLowPorts.symm p)
      simpa only [Equiv.symm_symm, Equiv.apply_symm_apply, transported] using
        cover.permutePorts_exists swapLowPorts.symm
  have hTimes (i : Fin 1) : execution.emissionTimes i=low.execution.emissionTimes i :=
    (relay_restore_times transported hp hs i).trans (low.execution.permutePorts_emissionTimes swapLowPorts.symm i)
  have hDeliveries : execution.deliveries=sourceTrain 0 2 0 8 16 := by
    rw [relay_restore_deliveries,low.execution.permutePorts_deliveries,low.deliveries,sourceTrain_permutePorts]
    simp only [Equiv.symm_symm,swapLowPorts_zero]
  refine ⟨{
    low:=low,final:=low.final.permutePorts swapLowPorts.symm,final_state:=rfl,execution:=execution
    covered:=relay_restore_covered transported hp hs transportedCovered
    contacts_transversal:=relay_restore_transversal transported hp hs
      (low.execution.contactsTransversal_permutePorts swapLowPorts.symm low.contacts_transversal)
    date:=low.date,prepared:=low.prepared.permutePorts swapLowPorts.symm,charge:=low.charge
    raw_none:=?_,pending:=?_,gain_target:=?_,gain_other:=?_,recovery:=low.recovery
    emission_times:=hTimes,emission_count:=(congrArg List.length (hTimes 0)).trans low.emission_count
    deliveries:=hDeliveries,physical:=execution.physical_invariant hb (hborn.physical_invariant hb)
    raw_valid:=execution.raw_valid hborn.raw_valid
    complete:=relay_restore_complete transported hp hs (low.complete.permutePorts swapLowPorts.symm)
  }⟩
  · intro j p
    exact low.raw_none j (swapLowPorts.symm p)
  · change low.final.pending.map (fun d => d.permutePorts swapLowPorts.symm)=[]
    rw [low.pending,List.map_nil]
  · simpa only [Snapshot.permutePorts_z,swapLowPorts_symm,swapLowPorts_two,swapLowPorts_zero] using low.gain_target
  · intro p hp2
    have hother : swapLowPorts.symm p≠0 := by
      intro h
      have he := congrArg swapLowPorts h
      simp only [Equiv.apply_symm_apply,swapLowPorts_zero] at he
      exact hp2 he
    simpa only [Snapshot.permutePorts_z,Equiv.apply_symm_apply] using low.gain_other (swapLowPorts.symm p) hother

namespace FiniteChainRelayPreparation
variable {θ born} (r : FiniteChainRelayPreparation θ born)

theorem ready : ReadyCoordinates r.final 0 := r.prepared.ready_coordinates

/-- Port renaming leaves the actual physical energy endpoint unchanged. -/
theorem energy_actual : r.final.x 0 .energy=r.low.final.x 0 .energy := by
  rw [r.final_state]
  rfl

end FiniteChainRelayPreparation
end KernelR.Hybrid
