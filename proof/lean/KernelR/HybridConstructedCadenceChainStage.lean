import KernelR.HybridFiniteCausalChain
import KernelR.HybridCadenceChainEnvelope
import KernelR.Chain.Induction
import KernelR.HybridCompleteSectionCovers

/-! A finite physical cadence stage with its actual root packet, uniform
clock envelope, exact per-cell FIRE counts and own memory increments. This
record states the construction target; it is not a supplied dynamical law. -/
namespace KernelR.Hybrid

/-- Physical indices put the root at zero and the leaf last. -/
def cadenceActivePort (depth : ℕ) (i : Fin (depth+1)) : Port :=
  if i.val=depth then 0 else 2

theorem cadence_active_port_leaf (depth : ℕ) : cadenceActivePort depth (Fin.last depth)=0 := by
  simp [cadenceActivePort]

theorem cadence_active_port_head (depth : ℕ) : cadenceActivePort (depth+1) 0=2 := by
  simp [cadenceActivePort]

theorem cadence_active_port_tail (depth : ℕ) (i : Fin (depth+1)) :
    cadenceActivePort (depth+1) i.succ=cadenceActivePort depth i := by
  simp [cadenceActivePort]

structure ConstructedCadenceChainStage (d : FiniteCausalChainData)
    (K : ℕ) (T : ℝ) (depth m L : ℕ) (J : ℝ) where
  stage : FiniteCausalChainStage d T depth
  contacts_transversal : stage.execution.ContactsTransversal
  section_covered :
    (∀ i p, stage.final.x i (.z p) < Real.log ((d.parameters depth i).cap p)) →
    (∀ i, stage.final.x i .b < 11 / 10) → stage.execution.SectionCovered
  packet : KernelR.Chain.Packet m L J
  calendar : stage.execution.emissionTimes 0=
    List.ofFn (fun i : Fin (m+L) => packet.actual i.val)
  envelope : CadencePacketEnvelope packet 160 K depth
  counts : ∀ i : Fin (depth+1), (stage.execution.emissionTimes i).length=
    K-5-2*(depth-i.val)
  gain_target : ∀ i : Fin (depth+1), stage.final.x i (.z (cadenceActivePort depth i))=
    (d.source depth).x i (.z (cadenceActivePort depth i))+
      (if i.val=depth then (12/5 : ℝ) else 3/5)
  gain_other : ∀ (i : Fin (depth+1)) (p : Port), p≠cadenceActivePort depth i →
    stage.final.x i (.z p)=(d.source depth).x i (.z p)
  recovery : ∀ i : Fin (depth+1), stage.final.x i .b=(d.source depth).x i .b+1/5

namespace ConstructedCadenceChainStage
variable {d : FiniteCausalChainData} {K : ℕ} {T : ℝ} {depth m L : ℕ} {J : ℝ}
  (c : ConstructedCadenceChainStage d K T depth m L J)
include c

theorem root_emission_count : (c.stage.execution.emissionTimes 0).length=K-5-2*depth := by
  simpa only [Fin.val_zero,Nat.sub_zero] using c.counts 0

theorem packet_count : m+L=K-5-2*depth := by
  have h := c.root_emission_count
  rw [c.calendar,List.length_ofFn] at h
  exact h

theorem root_terminal : c.stage.final.time=T ∧ c.stage.final.pending=[] :=
  ⟨c.stage.complete.1,c.stage.pending⟩

theorem actual_energy (i : Fin (depth+1)) :
    c.stage.final.x i .energy=(c.stage.cells i).2.final.x 0 .energy := c.stage.energy_actual i

end ConstructedCadenceChainStage
end KernelR.Hybrid
