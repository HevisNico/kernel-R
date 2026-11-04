import KernelR.HybridPreparedCadenceChainConstruction

/-! A physical cadence extension retaining the exact ordered emission list of
all preceding cells. These equalities carry prescribed wire indices through
later physical weaving; no uniqueness or deterministic-execution claim is used. -/
namespace KernelR.Hybrid
namespace PreparedCadenceChainDomain
variable {d : FiniteCausalChainData} {ε : ℝ} {n K : ℕ}
  {sigma centre : ℕ → ℝ} {delay : ℕ → ℝ → ℝ}
  (domain : PreparedCadenceChainDomain d ε n K sigma centre delay)
include domain

theorem strong_step_exists {j m L : ℕ} {J : ℝ} (hj : j<n) (hL : 5≤L)
    (hJ : J+sigma j≤3/20)
    (old : ConstructedCadenceChainStage d K (cadenceChainTerminal n K) j m L J) :
    ∃ next : ConstructedCadenceChainStage d K (cadenceChainTerminal n K)
      (j+1) (m+2) (L-4) (J+sigma j),
      ∀ i : Fin (j+1), next.stage.execution.emissionTimes i.succ=old.stage.execution.emissionTimes i := by
  let incoming := old.packet.sampleWireDelay (delay j) (centre j) (sigma j)
    (domain.sigma_nonneg j) (domain.error_bounds j hj)
  let source := old.stage.nextSource
  have hf : PhysicalInvariant (fun _ : Fin 1 => d.headParameters j) source := by
    have h := domain.head_physical j hj
    exact ⟨h.region,h.gain_cap,h.recovery_cap,h.reserve⟩
  have hv : RawValid source := domain.head_raw_valid j hj
  have hs : PreparedSection source 0 := by
    have h := domain.head_prepared j hj
    exact ⟨h.ready,h.charge,h.recovery,h.auxiliary⟩
  have hqueue : source.pending=List.ofFn (fun i : Fin (m+L) =>
      (⟨0,2,incoming.actual i.val⟩ : Delivery 1)) := by
    change old.stage.execution.headInputQueue (d.contacts j)=_
    rw [domain.contacts j hj]
    exact finite_cadence_head_queue_packet old.stage.execution 0 2 old.packet
      160 (cadenceChainTerminal n K+1) (delay j) (centre j) (sigma j)
      (domain.sigma_nonneg j) (domain.error_bounds j hj) old.calendar
      (fun i => old.envelope.gate (by omega : j<n+1) i)
  have hm : 1≤m := old.packet.prefix_pos
  have hfirst : source.time< incoming.actual 0 := by
    let i : Fin (m+L) := ⟨0,by omega⟩
    have h := (old.envelope.sampled_wire_bounds (delay j) (centre j) (sigma j)
      (domain.sigma_nonneg j) (domain.error_bounds j hj) (domain.delay_bounds j hj) i).1
    change (d.headSource j).time< incoming.actual 0
    rw [domain.head_clock j]
    change (160 : ℝ)+3/10≤ incoming.actual 0 at h
    linarith
  have hterminal : incoming.actual (m+L-1)+19/5≤cadenceChainTerminal n K := by
    let i : Fin (m+L) := ⟨m+L-1,by omega⟩
    exact old.envelope.received_terminal (by omega : j<n+1) (delay j) (centre j)
      (sigma j) (domain.sigma_nonneg j) (domain.error_bounds j hj) (domain.delay_bounds j hj) i
  obtain ⟨receiver⟩ := local_cadence_budget_receiver_exists (domain.head_box j hj)
    source 2 incoming (cadenceChainTerminal n K) hJ hL hf hv hs
    (domain.head_charge j hj) (domain.head_raw j hj) (domain.head_gain j hj)
    hqueue hfirst (by linarith [hterminal])
  let head : FiniteCausalCell (d.headParameters j) source (cadenceChainTerminal n K) := {
    final:=receiver.final,execution:=receiver.execution,complete:=receiver.complete
    ready:=receiver.ready 0,charge:=receiver.charge,raw_none:=receiver.raw_none 0,pending:=receiver.pending
  }
  obtain ⟨extension⟩ := finite_causal_extension_exists old.stage head
    (domain.parameter_box (j+1) (by omega))
    (domain.source_physical (j+1) (by omega)) (domain.source_raw_valid (j+1) (by omega))
  refine ⟨{
    stage:=extension.next,packet:=receiver.outputPacket
    contacts_transversal:=extension.contacts_transversal old.contacts_transversal receiver.contacts_transversal
    calendar:=extension.head_times.trans receiver.output_packet_calendar
    envelope:=?_,counts:=?_,gain_target:=?_,gain_other:=?_,recovery:=?_
  },?_⟩
  · exact old.envelope.propagate (delay j) (centre j) (sigma j) (domain.sigma_nonneg j)
      (domain.error_bounds j hj) (domain.delay_bounds j hj) receiver.tail_size
      receiver.lowLatency receiver.firstHighLatency receiver.restHighLatency receiver.low_latency_bounds
      receiver.first_high_latency_bounds receiver.rest_high_latency_bounds receiver.high_latency_order
  · intro i
    cases i using Fin.cases with
    | zero =>
      rw [extension.head_times]
      change (receiver.execution.emissionTimes 0).length=K-5-2*((j+1)-0)
      rw [receiver.emission_count]
      have h := old.packet_count
      omega
    | succ i =>
      rw [extension.tail_times]
      simpa only [Fin.val_succ,Nat.add_sub_add_right] using old.counts i
  · intro i
    cases i using Fin.cases with
    | zero =>
      rw [cadence_active_port_head,extension.head_values]
      change receiver.final.x 0 (.z 2)=(d.headSource j).x 0 (.z 2)+3/5
      exact receiver.gain_target
    | succ i =>
      rw [cadence_active_port_tail,extension.tail_values]
      change old.stage.final.x i (.z (cadenceActivePort j i))=
        (d.source j).x i (.z (cadenceActivePort j i))+
          (if i.val+1=j+1 then (12/5 : ℝ) else 3/5)
      simpa only [Nat.add_right_cancel_iff] using old.gain_target i
  · intro i p hp
    cases i using Fin.cases with
    | zero =>
      rw [cadence_active_port_head] at hp
      rw [extension.head_values]
      change receiver.final.x 0 (.z p)=(d.headSource j).x 0 (.z p)
      exact receiver.gain_other p hp
    | succ i =>
      rw [cadence_active_port_tail] at hp
      rw [extension.tail_values]
      exact old.gain_other i p hp
  · intro i
    cases i using Fin.cases with
    | zero =>
      rw [extension.head_values]
      change receiver.final.x 0 .b=(d.headSource j).x 0 .b+1/5
      exact receiver.recovery_gain
    | succ i =>
      rw [extension.tail_values]
      exact old.recovery i

  · exact extension.tail_times

end PreparedCadenceChainDomain
end KernelR.Hybrid
