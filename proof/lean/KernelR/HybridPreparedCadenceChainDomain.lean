import KernelR.HybridConstructedCadenceChainStage
import KernelR.HybridCadenceLeafKEnvelope
import KernelR.HybridLocalCadenceBudgetReceiverPacket
import KernelR.HybridFiniteCausalExtension

/-! Static prepared domains for the constructed finite cadence. No execution,
output date, dose word or CellLaw is a field of these assumptions. -/
namespace KernelR.Hybrid

noncomputable def cadenceChainTerminal (n K : ℕ) : ℝ :=
  finiteCadenceTerminal 160 (n+1) K

structure PreparedCadenceChainDomain (d : FiniteCausalChainData) (ε : ℝ) (n K : ℕ)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ) : Prop where
  source_clock : d.leafSource.time=1599/10
  budget : 4*(n+1)+12≤K
  sigma_nonneg : ∀ j, 0≤sigma j
  jitter_budget : KernelR.Chain.pathJitter sigma n≤3/20
  centre_bounds : ∀ j, j<n → (3/10 : ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j
  error_bounds : ∀ j, j<n → ∀ time, -sigma j≤delay j time-centre j ∧ delay j time-centre j≤sigma j
  contacts : ∀ j, j<n → d.contacts j=
    finiteCadenceHeadContact 0 2 160 (cadenceChainTerminal n K+1) (delay j)
  parameter_box : ∀ j, j≤n → PhysicalBox (d.parameters j) ε
  source_physical : ∀ j, j≤n → PhysicalInvariant (d.parameters j) (d.source j)
  source_raw_valid : ∀ j, j≤n → RawValid (d.source j)
  leaf_prepared : PreparedSection d.leafSource 0
  leaf_charge : d.leafSource.x 0 .q=1/10
  leaf_raw : ∀ p, d.leafSource.raw 0 p=none
  leaf_gain : Real.log (3/10)-1/100000≤d.leafSource.x 0 (.z 0) ∧
    d.leafSource.x 0 (.z 0)≤Real.log (3/10)+1/100000
  leaf_queue : d.leafSource.pending=sourceTrain 0 0 160 4 K
  head_box : ∀ j, j<n → PhysicalBox (fun _ : Fin 1 => d.headParameters j) ε
  head_physical : ∀ j, j<n → PhysicalInvariant (fun _ : Fin 1 => d.headParameters j) (d.headSource j)
  head_raw_valid : ∀ j, j<n → RawValid (d.headSource j)
  head_prepared : ∀ j, j<n → PreparedSection (d.headSource j) 0
  head_charge : ∀ j, j<n → (d.headSource j).x 0 .q=1/10
  head_raw : ∀ j, j<n → ∀ p, (d.headSource j).raw 0 p=none
  head_gain : ∀ j, j<n →
    Real.log (3/10)+9/5-1/100000≤(d.headSource j).x 0 (.z 2) ∧
      (d.headSource j).x 0 (.z 2)≤Real.log (3/10)+9/5+1/100000
  head_queue : ∀ j, j<n → (d.headSource j).pending=[]

namespace PreparedCadenceChainDomain
variable {d : FiniteCausalChainData} {ε : ℝ} {n K : ℕ}
  {sigma centre : ℕ → ℝ} {delay : ℕ → ℝ → ℝ}
  (domain : PreparedCadenceChainDomain d ε n K sigma centre delay)
include domain

theorem delay_bounds (j : ℕ) (hj : j<n) (time : ℝ) :
    (3/10 : ℝ)≤delay j time ∧ delay j time≤2/5 := by
  have hc := domain.centre_bounds j hj
  have he := domain.error_bounds j hj time
  constructor <;> linarith [hc.1,hc.2,he.1,he.2]

theorem head_clock (j : ℕ) : (d.headSource j).time=1599/10 :=
  (d.common_clock j).trans domain.source_clock

theorem external_source_count (j : ℕ) : (d.source j).pending.length=K := by
  rw [d.source_queue_length,domain.leaf_queue]
  simp [sourceTrain]

theorem leaf_exists :
    Nonempty (ConstructedCadenceLeafK (fun _ : Fin 1 => d.leafParameters) d.leafSource
      0 160 K (cadenceChainTerminal n K)) := by
  have hK : 9≤K := by have h := domain.budget; omega
  apply constructed_cadence_leaf_k_exists (domain.parameter_box 0 (by omega)) d.leafSource
    0 160 K (cadenceChainTerminal n K) hK
    (domain.source_physical 0 (by omega)) (domain.source_raw_valid 0 (by omega))
    domain.leaf_prepared domain.leaf_charge domain.leaf_raw domain.leaf_gain
    domain.leaf_prepared.recovery domain.leaf_queue
  · rw [domain.source_clock]; norm_num
  · exact finite_cadence_terminal_after_leaf (by omega)

/-- The base packet comes from the complete actual arbitrary-K leaf. -/
theorem base_exists : Nonempty (ConstructedCadenceChainStage d K
    (cadenceChainTerminal n K) 0 3 (K-8) 0) := by
  obtain ⟨leaf⟩ := domain.leaf_exists
  let stage : FiniteCausalChainStage d (cadenceChainTerminal n K) 0 := {
    final:=leaf.final, execution:=leaf.execution, complete:=leaf.complete
    ready:=leaf.ready, charge:=by intro i; fin_cases i; exact leaf.charge
    raw_none:=leaf.raw_none, pending:=leaf.pending, physical:=leaf.physical, raw_valid:=leaf.raw_valid
    cells:=fun _ => ⟨d.leafSource,leaf.finiteCell⟩
    contacts_transversal:=fun _ => leaf.contacts_transversal
    section_runs:=by
      intro kind i p first last count localRun
      fin_cases i
      exact localRun
    emission_times:=by
      intro i
      have hi : i=0 := by fin_cases i; rfl
      subst i
      exact leaf.finite_cell_calendar.symm
    cell_values:=by intro i; fin_cases i; rfl
  }
  refine ⟨{
    stage:=stage, packet:=leaf.packet, calendar:=leaf.packet_calendar
    contacts_transversal:=leaf.contacts_transversal
    envelope:=?_, counts:=?_, gain_target:=?_, gain_other:=?_, recovery:=?_
  }⟩
  · constructor
    · exact fun i => (leaf.packet_actual_bounds i).1
    · intro i
      simpa only [Nat.cast_zero,mul_zero,add_zero] using (leaf.packet_actual_bounds i).2
  · intro i
    have hi : i=0 := by fin_cases i; rfl
    subst i
    change (leaf.execution.emissionTimes 0).length=K-5-2*(0-0)
    simpa only [Nat.sub_self,mul_zero,Nat.sub_zero] using leaf.emission_count
  · intro i
    have hi : i=0 := by fin_cases i; rfl
    subst i
    change leaf.final.x 0 (.z 0)=d.leafSource.x 0 (.z 0)+12/5
    exact leaf.gain_target
  · intro i p hp
    have hi : i=0 := by fin_cases i; rfl
    subst i
    exact leaf.gain_other p hp
  · intro i
    have hi : i=0 := by fin_cases i; rfl
    subst i
    exact leaf.recovery

end PreparedCadenceChainDomain
end KernelR.Hybrid
