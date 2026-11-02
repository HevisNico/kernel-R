import KernelR.HybridBirthCadenceLocalC
import KernelR.Chain.Packets
import KernelR.HybridContact

/-! The autonomous C execution supplies a leaf packet through its actual
emission ledger. The wire transform below labels tokens due from those real
emissions; it does not insert tokens into a global pending queue. -/
namespace KernelR.Hybrid
namespace ConstructedCadenceLocalC
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward} (full : ConstructedCadenceLocalC c)
include full

omit full in
private theorem three_dose_log_bounds :
    Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ c.localCSource.x 0 (.z 0) ∧
      c.localCSource.x 0 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
  rw [c.local_c_source_gain]
  have h := newbornC.gain 0
  simp only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] at h
  constructor <;> linarith [h.1,h.2]

omit full in
theorem leaf_first_window (_full : ConstructedCadenceLocalC c) :
    (652 : ℝ) + 2 / 5 < c.wave.cadence.wire.fire.final.time ∧
      c.wave.cadence.wire.fire.final.time < 652 + 9 / 10 := by
  have hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤
      c.wave.cadence.warmup.localWarmup.final.x 0 (.z 0) ∧
      c.wave.cadence.warmup.localWarmup.final.x 0 (.z 0) ≤
        Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    have hgOwn : c.wave.cadence.warmup.localWarmup.final.x 0 (.z 0) =
        c.wave.cadence.warmup.start.sC.x 0 (.z 0) + 9 / 5 :=
      c.wave.cadence.warmup.localWarmup.gain_target
    rw [hgOwn]
    constructor <;> linarith [c.wave.cadence.warmup.start.c_gain_low.1,
      c.wave.cadence.warmup.start.c_gain_low.2]
  have h := c.wave.cadence.wire.fire.cadence_residual_window
    c.wave.cadence.warmup.localWarmup.coordinates (cadence_three_dose_gain_bounds hz).2
  have ht : c.wave.cadence.warmup.localWarmup.final.time = 652 :=
    c.wave.cadence.warmup.localWarmup.date
  simpa only [ht] using h

theorem leaf_second_latency : full.tail.second.fire.latency =
    restLatency (Real.exp (c.localCSource.x 0 (.z 0))) := by
  have hg := cadence_three_dose_gain_bounds ((three_dose_log_bounds (c := c)))
  apply restLatency_unique ⟨hg.1,by linarith [hg.2]⟩
  · exact ⟨by linarith [full.tail.second.fire.early],full.tail.second.fire.deadline.le⟩
  · have hq : c.localCSource.x 0 .q = 1 / 10 := c.mark.localSource.charge
    simpa only [hq,readyPulse,add_sub_cancel_left,sub_zero]
      using full.tail.second.fire.response_root

theorem leaf_second_window :
    (660 : ℝ) + 13 / 20 < full.tail.second.fire.final.time ∧
      full.tail.second.fire.final.time < 660 + 33 / 50 := by
  rw [full.tail.second.fire.date,c.local_c_source_date,full.leaf_second_latency]
  have h := restLatency_three_doses_bounds (three_dose_log_bounds (c := c)).1 (three_dose_log_bounds (c := c)).2
  constructor <;> linarith [h.1,h.2]

theorem leaf_high_source_date : full.tail.source668.final.time = 668 := by
  rw [full.tail.source668.date,full.tail.second.date,c.local_c_source_date]
  norm_num

theorem leaf_high_gain_own : full.tail.source668.final.x 0 (.z 0) =
    newbornC.x (.z 0) + 12 / 5 := by
  rw [full.tail.source668.gain_target,full.tail.second.gains,c.local_c_source_gain]
  ring

theorem leaf_high_gain_bounds :
    16 / 5 ≤ Real.exp (full.tail.source668.final.x 0 (.z 0)) ∧
      Real.exp (full.tail.source668.final.x 0 (.z 0)) ≤ 7 / 2 := by
  apply full.tail.source668.high_gain_bounds
  rw [full.tail.second.gains]
  exact (three_dose_log_bounds (c := c))

theorem leaf_high_first_window :
    (668 : ℝ) + 4 / 25 < full.tail.high.first.final.time ∧
      full.tail.high.first.final.time < 668 + 13 / 50 := by
  simpa only [full.leaf_high_source_date] using full.tail.high.first.window

/-- Exact-rest latency belongs to C's own four-dose gain. -/
noncomputable def leafRestLatency : ℝ :=
  highRestLatency (Real.exp (full.tail.source668.final.x 0 (.z 0)))

theorem leaf_rest_upper : full.leafRestLatency < 13 / 50 :=
  highRestLatency_lt_twenty_six full.leaf_high_gain_bounds

/-- Three actual prefix FIREs, followed by seventeen actual exact-rest FIREs. -/
noncomputable def leafPacket : KernelR.Chain.Packet 3 17 0 where
  slowDate i := if i = 0 then c.wave.cadence.wire.fire.final.time
    else if i = 1 then full.tail.second.fire.final.time else full.tail.high.first.final.time
  settle := 4 + full.leafRestLatency - full.tail.high.first.latency
  phase _ := 0
  prefix_pos := by norm_num
  tail_pos := by norm_num
  jitter_nonneg := by norm_num
  prefix_gap i hi := by
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl <;> norm_num <;> constructor <;>
      linarith [full.leaf_first_window.1,full.leaf_first_window.2,
        full.leaf_second_window.1,full.leaf_second_window.2,
        full.leaf_high_first_window.1,full.leaf_high_first_window.2]
  settle_bounds := by
    have hle := full.tail.high.first_latency_le_rest
    change full.tail.high.first.latency ≤ full.leafRestLatency at hle
    constructor <;> linarith [full.leaf_rest_upper,full.tail.high.first.early]
  phase_bounds _ := by norm_num

@[simp] theorem leaf_packet_actual_zero : full.leafPacket.actual 0 = c.wave.cadence.wire.fire.final.time := by
  norm_num [KernelR.Chain.Packet.actual,KernelR.Chain.Packet.ideal,leafPacket]

@[simp] theorem leaf_packet_actual_one : full.leafPacket.actual 1 = full.tail.second.fire.final.time := by
  norm_num [KernelR.Chain.Packet.actual,KernelR.Chain.Packet.ideal,leafPacket]

@[simp] theorem leaf_packet_actual_two : full.leafPacket.actual 2 = full.tail.high.first.final.time := by
  norm_num [KernelR.Chain.Packet.actual,KernelR.Chain.Packet.ideal,leafPacket]

theorem leaf_packet_actual_tail (k : ℕ) :
    full.leafPacket.actual (k + 3) = 672 + 4 * (k : ℝ) + full.leafRestLatency := by
  have hnot : ¬k + 3 < 3 := by omega
  simp only [KernelR.Chain.Packet.actual,KernelR.Chain.Packet.ideal,hnot,ite_false,
    leafPacket,Nat.reduceSub,show ¬(2 : ℕ) = 0 by decide,show ¬(2 : ℕ) = 1 by decide,
    Nat.add_sub_cancel,add_zero]
  rw [full.tail.high.first.date,full.leaf_high_source_date]
  ring

/-- The packet calendar is a conclusion about the complete actual C ledger. -/
theorem leaf_packet_calendar : full.execution.emissionTimes 0 =
    List.ofFn (fun i : Fin 20 => full.leafPacket.actual i.val) := by
  rw [full.calendar,full.tail.high.calendar,full.leaf_high_source_date,
    show (668 : ℝ) + 4 = 672 by norm_num]
  simp only [sourceTrain,List.map_ofFn]
  have hTail :
      List.ofFn (fun k : Fin 17 => full.leafPacket.actual (k.val + 1 + 1 + 1)) =
      List.ofFn (fun k : Fin 17 => (672 : ℝ) + 4 * (k.val : ℝ) + full.leafRestLatency) := by
    apply congrArg List.ofFn
    funext k
    simpa only [Nat.add_assoc] using full.leaf_packet_actual_tail k.val
  conv_rhs => rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ]
  simp only [Fin.val_zero,Fin.val_succ,full.leaf_packet_actual_zero,
    full.leaf_packet_actual_one,full.leaf_packet_actual_two,hTail]
  rfl

/-- A contact carrying C's real FIREs to B. The gate includes all twenty FIREs. -/
def leafContact (wireDelay : ℝ → ℝ) : Contact 3 := ⟨2,1,2,640,740,wireDelay⟩

theorem leaf_packet_dates_in_contact (i : Fin 20) :
    (640 : ℝ) ≤ full.leafPacket.actual i.val ∧ full.leafPacket.actual i.val < 740 := by
  by_cases h0 : i.val = 0
  · rw [h0,full.leaf_packet_actual_zero]
    constructor <;> linarith [full.leaf_first_window.1,full.leaf_first_window.2]
  by_cases h1 : i.val = 1
  · rw [h1,full.leaf_packet_actual_one]
    constructor <;> linarith [full.leaf_second_window.1,full.leaf_second_window.2]
  by_cases h2 : i.val = 2
  · rw [h2,full.leaf_packet_actual_two]
    constructor <;> linarith [full.leaf_high_first_window.1,full.leaf_high_first_window.2]
  have hi : 3 ≤ i.val := by omega
  have hk : i.val - 3 + 3 = i.val := by omega
  rw [←hk,full.leaf_packet_actual_tail]
  have hnonneg : (0 : ℝ) ≤ (i.val - 3 : ℕ) := Nat.cast_nonneg _
  have hu : ((i.val - 3 : ℕ) : ℝ) ≤ 16 := by exact_mod_cast (show i.val - 3 ≤ 16 by omega)
  have hlo : 4 / 25 < full.leafRestLatency :=
    full.tail.high.first.early.trans_le full.tail.high.first_latency_le_rest
  constructor <;> linarith [full.leaf_rest_upper]

/-- Delay errors label the real signal times; there is no resampling. -/
noncomputable def leafWireError (wireDelay : ℝ → ℝ) (i : ℕ) : ℝ :=
  wireDelay (full.leafPacket.actual i) - 7 / 20

theorem leaf_wire_error_bounds (wireDelay : ℝ → ℝ)
    (hd : ∀ t, (3 / 10 : ℝ) ≤ wireDelay t ∧ wireDelay t ≤ 2 / 5) (i : ℕ) :
    -(1 / 20 : ℝ) ≤ full.leafWireError wireDelay i ∧
      full.leafWireError wireDelay i ≤ 1 / 20 := by
  dsimp [leafWireError]
  constructor <;> linarith [(hd (full.leafPacket.actual i)).1,(hd (full.leafPacket.actual i)).2]

noncomputable def receivedLeafPacket (wireDelay : ℝ → ℝ)
    (hd : ∀ t, (3 / 10 : ℝ) ≤ wireDelay t ∧ wireDelay t ≤ 2 / 5) :
    KernelR.Chain.Packet 3 17 (1 / 20) := by
  let wired := full.leafPacket.wire (7 / 20) (1 / 20) (by norm_num)
    (full.leafWireError wireDelay) (full.leaf_wire_error_bounds wireDelay hd)
  exact {
    slowDate := wired.slowDate, settle := wired.settle, phase := wired.phase
    prefix_pos := wired.prefix_pos, tail_pos := wired.tail_pos
    jitter_nonneg := by norm_num
    prefix_gap := wired.prefix_gap, settle_bounds := wired.settle_bounds
    phase_bounds := by simpa only [zero_add] using wired.phase_bounds
  }

theorem received_leaf_actual (wireDelay : ℝ → ℝ)
    (hd : ∀ t, (3 / 10 : ℝ) ≤ wireDelay t ∧ wireDelay t ≤ 2 / 5) (i : ℕ) :
    (full.receivedLeafPacket wireDelay hd).actual i =
      full.leafPacket.actual i + wireDelay (full.leafPacket.actual i) := by
  change (full.leafPacket.wire (7 / 20) (1 / 20) (by norm_num)
    (full.leafWireError wireDelay) (full.leaf_wire_error_bounds wireDelay hd)).actual i = _
  rw [KernelR.Chain.wire_actual]
  dsimp [leafWireError]
  ring

/-- Tokens are extracted from the actual local emission ledger. This is not
an assertion that a surrounding global execution has yet consumed them. -/
noncomputable def leafTokens (wireDelay : ℝ → ℝ) : List (Delivery 3) :=
  (full.execution.emissionTimes 0).map (leafContact wireDelay).token

theorem leaf_tokens_received_calendar (wireDelay : ℝ → ℝ)
    (hd : ∀ t, (3 / 10 : ℝ) ≤ wireDelay t ∧ wireDelay t ≤ 2 / 5) :
    full.leafTokens wireDelay = List.ofFn (fun i : Fin 20 =>
      (⟨1,2,(full.receivedLeafPacket wireDelay hd).actual i.val⟩ : Delivery 3)) := by
  rw [leafTokens,full.leaf_packet_calendar,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [full.received_leaf_actual wireDelay hd]
  rfl

theorem leaf_token_provenance (wireDelay : ℝ → ℝ) (d : Delivery 3)
    (hd : d ∈ full.leafTokens wireDelay) :
    ∃ time, time ∈ full.execution.emissionTimes 0 ∧
      d = (leafContact wireDelay).token time := by
  obtain ⟨time,ht,he⟩ := List.mem_map.mp hd
  exact ⟨time,ht,he.symm⟩

/-- A future global weaver preserving this derived C calendar issues exactly
these tokens, provided its actual routing agrees with the physical contact. -/
theorem issued_leaf_tokens {θG : Fin 3 → Parameters} {route s u}
    (e : Execution θG route s u) (wireDelay : ℝ → ℝ)
    (hc : e.emissionTimes 2 = full.execution.emissionTimes 0)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = (1 : Fin 3)) =
        (leafContact wireDelay).route event.1 event.2) :
    e.issuedTo 1 = full.leafTokens wireDelay := by
  change e.issuedTo (leafContact wireDelay).target = _
  rw [e.issuedTo_contact (leafContact wireDelay) hwire]
  change ((e.emissionTimes 2).filter (fun t => (640 : ℝ) ≤ t ∧ t < 740)).map _ = _
  rw [hc]
  have hgate : ∀ time ∈ full.execution.emissionTimes 0, (640 : ℝ) ≤ time ∧ time < 740 := by
    intro time ht
    rw [full.leaf_packet_calendar] at ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact full.leaf_packet_dates_in_contact i
  rw [List.filter_eq_self.mpr (by simpa using hgate)]
  rfl

end ConstructedCadenceLocalC
end KernelR.Hybrid
