import KernelR.HybridCadenceWeakWarmupK
import KernelR.HybridCadenceLeafFirstMarkK
import KernelR.HybridLocalCadenceTailK
import KernelR.HybridPreparedFirstSource
import KernelR.Chain.Packets

/-! A complete physical leaf for an arbitrary finite period-four source
budget. The prepared initial state, source tokens and fabrication bounds are
the data; every subsequent FIRE, arrival and packet date is constructed. -/
namespace KernelR.Hybrid

-- Opaque observer formulas keep dependent snapshot aliases out of append
-- matching, while the actual four physical executions remain unchanged.
private theorem leaf_four_emission_times {n θ route s a b c u t₀ t₁ t₂ t₃}
    (e₀ : @Execution n θ route s a) (e₁ : Execution θ route a b)
    (e₂ : Execution θ route b c) (e₃ : Execution θ route c u) (i : Fin n)
    (h₀ : e₀.emissionTimes i = t₀) (h₁ : e₁.emissionTimes i = t₁)
    (h₂ : e₂.emissionTimes i = t₂) (h₃ : e₃.emissionTimes i = t₃) :
    (e₀.append (e₁.append (e₂.append e₃))).emissionTimes i =
      t₀ ++ (t₁ ++ (t₂ ++ t₃)) := by
  rw [Execution.emissionTimes_append,Execution.emissionTimes_append,Execution.emissionTimes_append,
    h₀,h₁,h₂,h₃]

private theorem leaf_four_deliveries {n θ route s a b c u t₀ t₁ t₂ t₃}
    (e₀ : @Execution n θ route s a) (e₁ : Execution θ route a b)
    (e₂ : Execution θ route b c) (e₃ : Execution θ route c u)
    (h₀ : e₀.deliveries = t₀) (h₁ : e₁.deliveries = t₁)
    (h₂ : e₂.deliveries = t₂) (h₃ : e₃.deliveries = t₃) :
    (e₀.append (e₁.append (e₂.append e₃))).deliveries =
      t₀ ++ (t₁ ++ (t₂ ++ t₃)) := by
  rw [Execution.deliveries_append,Execution.deliveries_append,Execution.deliveries_append,h₀,h₁,h₂,h₃]

structure ConstructedCadenceLeafK (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (start : ℝ) (K : ℕ) (terminal : ℝ) where
  budget : 9 ≤ K
  firstSource : PreparedFirstSource θ s p start (sourceTrain 0 p (start + 4) 4 (K - 1))
  warmup : ConstructedCadenceWeakWarmupK θ (fun _ _ => []) firstSource.final p K
  firstMark : ConstructedCadenceLeafFirstMarkK warmup
  tail : LocalCadenceTailK θ firstMark.final p (K - 8) terminal
  execution : Execution θ (fun _ _ => []) s tail.final
  reconstruct : execution = firstSource.execution.append
    (warmup.execution.append (firstMark.execution.append tail.execution))
  warmup_date : warmup.final.time = start + 12
  mark_date : firstMark.final.time = start + 20
  first_window : start + 12 + 2 / 5 < firstMark.fire.final.time ∧
    firstMark.fire.final.time < start + 12 + 9 / 10
  second_window : start + 20 + 13 / 20 < tail.second.fire.final.time ∧
    tail.second.fire.final.time < start + 20 + 33 / 50
  high_source_date : tail.sourceHigh.final.time = start + 28
  high_first_window : start + 28 + 4 / 25 < tail.high.first.final.time ∧
    tail.high.first.final.time < start + 28 + 13 / 50
  high_gain_bounds : 16 / 5 ≤ Real.exp (tail.sourceHigh.final.x 0 (.z p)) ∧
    Real.exp (tail.sourceHigh.final.x 0 (.z p)) ≤ 7 / 2
  date : tail.final.time = terminal
  ready : ∀ j, ReadyCoordinates tail.final j
  charge : tail.final.x 0 .q = 1 / 10
  raw_none : ∀ j q, tail.final.raw j q = none
  pending : tail.final.pending = []
  gain_target : tail.final.x 0 (.z p) = s.x 0 (.z p) + 12 / 5
  gain_other : ∀ q, q ≠ p → tail.final.x 0 (.z q) = s.x 0 (.z q)
  recovery : tail.final.x 0 .b = s.x 0 .b + 1 / 5
  emission_count : (execution.emissionTimes 0).length = K - 5
  calendar : execution.emissionTimes 0 = firstMark.fire.final.time :: tail.execution.emissionTimes 0
  deliveries : execution.deliveries = sourceTrain 0 p start 4 K
  physical : PhysicalInvariant θ tail.final
  raw_valid : RawValid tail.final
  complete : CompleteThrough execution terminal

noncomputable abbrev ConstructedCadenceLeafK.final {θ s p start K terminal}
    (c : ConstructedCadenceLeafK θ s p start K terminal) : Snapshot 1 := c.tail.final

/-- A real finite physical leaf, without a reaching-execution premise or
an asserted output calendar. Only its K actual source occurrences are given. -/
theorem constructed_cadence_leaf_k_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (start : ℝ) (K : ℕ) (terminal : ℝ) (hK : 9 ≤ K)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : PreparedSection s 0)
    (hq : s.x 0 .q = 1 / 10) (hr : ∀ q, s.raw 0 q = none)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 1 / 100000)
    (hB : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (hqueue : s.pending = sourceTrain 0 p start 4 K) (hstart : s.time < start)
    (hterminal : start + 4 * (K : ℝ) < terminal) :
    Nonempty (ConstructedCadenceLeafK θ s p start K terminal) := by
  have hHead : s.pending = ⟨0,p,start⟩ :: sourceTrain 0 p (start + 4) 4 (K - 1) := by
    rw [hqueue]
    conv_lhs => rw [show K = (K - 1) + 1 by omega]
    rw [sourceTrain_succ]
  have hLater : ∀ d ∈ sourceTrain (0 : Fin 1) p (start + 4) 4 (K - 1), start < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change start < start + 4 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨first⟩ := prepared_first_source_exists hb s p start _ hf hv hs hq hr hHead hstart hLater
  have hFirstQueue : first.final.pending = sourceTrain 0 p (first.final.time + 4) 4 (K - 1) := by
    rw [first.date]
    exact first.pending
  have hFirstGain : Real.log (3 / 10) - 1 / 100000 ≤ first.final.x 0 (.z p) ∧
      first.final.x 0 (.z p) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [first.gains]
    exact hz
  have hFirstB : 17999 / 100000 ≤ first.final.x 0 .b ∧ first.final.x 0 .b ≤ 18001 / 100000 := by
    rw [first.recovery]
    exact hB
  obtain ⟨warm⟩ := constructed_cadence_weak_warmup_k_exists hb first.final p K (by omega)
    first.physical first.raw_valid first.prepared first.charge hFirstGain.2
    (by rw [first.date]; exact first.raw_active) first.raw_other hFirstQueue
  obtain ⟨mark⟩ := constructed_cadence_leaf_first_mark_k_exists hb warm (by omega) hFirstGain hFirstB
  have hWarmDate : warm.sourceThird.final.time = start + 12 := by
    have h : warm.sourceThird.final.time = first.final.time + 12 := warm.date
    linarith [first.date]
  have hMarkDate : mark.mark.final.time = start + 20 := by
    have h : mark.mark.final.time = first.final.time + 20 := mark.date
    linarith [first.date]
  have hMarkGain : mark.mark.final.x 0 (.z p) = s.x 0 (.z p) + 9 / 5 := by
    have h : mark.mark.final.x 0 (.z p) = first.final.x 0 (.z p) + 9 / 5 := mark.gain_target
    rw [first.gains] at h
    exact h
  have hMarkZ : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ mark.mark.final.x 0 (.z p) ∧
      mark.mark.final.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [hMarkGain]
    constructor <;> linarith [hz.1,hz.2]
  have hMarkCharge : mark.mark.final.x 0 .q = 1 / 10 := mark.charge
  have hMarkCoords : CadenceReadyCoordinates mark.mark.final 0 (3 / 10) := by
    refine ⟨(mark.ready 0).ready,⟨(mark.ready 0).charge.1,?_⟩,(mark.ready 0).auxiliary⟩
    rw [hMarkCharge]
    norm_num
  have hMarkQueue : mark.mark.final.pending = sourceTrain 0 p (mark.mark.final.time + 4) 4 ((K - 8) + 2) := by
    have h : mark.mark.final.pending = sourceTrain 0 p (first.final.time + 24) 4 (K - 6) := mark.pending
    apply h.trans
    exact congrArg₂ (fun date count => sourceTrain (0 : Fin 1) p date 4 count)
      (by linarith [first.date,hMarkDate]) (by omega)
  have hEnd : mark.mark.final.time + 12 + 4 * ((K - 8 : ℕ) : ℝ) < terminal := by
    have hNat : K - 8 + 8 = K := by omega
    have hCast : ((K - 8 : ℕ) : ℝ) + 8 = (K : ℝ) := by exact_mod_cast hNat
    rw [hMarkDate]
    linarith [hterminal]
  obtain ⟨tail⟩ := local_cadence_tail_k_exists hb mark.mark.final p (K - 8) terminal (by omega)
    mark.physical mark.raw_valid hMarkCoords hMarkCharge hMarkZ mark.recovery_band
    mark.raw_active mark.raw_other hMarkQueue hEnd
  let trace := first.execution.append (warm.execution.append (mark.execution.append tail.execution))
  have hCal : trace.emissionTimes 0 = mark.fire.final.time :: tail.execution.emissionTimes 0 := by
    have hFirst : first.execution.emissionTimes 0 = [] := by simp [Execution.emissionTimes,first.emissions]
    have hWarm : warm.execution.emissionTimes 0 = [] := by simp [Execution.emissionTimes,warm.emissions]
    have hMark : mark.execution.emissionTimes 0 = [mark.fire.final.time] := by
      simp [Execution.emissionTimes,mark.emissions]
    exact leaf_four_emission_times first.execution warm.execution mark.execution tail.execution 0
      hFirst hWarm hMark (rfl : tail.execution.emissionTimes 0 = tail.execution.emissionTimes 0)
  have hFirstWindow : start + 12 + 2 / 5 < mark.fire.final.time ∧
      mark.fire.final.time < start + 12 + 9 / 10 := by
    have hzW : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ warm.sourceThird.final.x 0 (.z p) ∧
        warm.sourceThird.final.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
      have h : warm.sourceThird.final.x 0 (.z p) = first.final.x 0 (.z p) + 9 / 5 := warm.gain_target
      rw [h,first.gains]
      constructor <;> linarith [hz.1,hz.2]
    have h : warm.sourceThird.final.time + 2 / 5 < mark.fire.final.time ∧
        mark.fire.final.time < warm.sourceThird.final.time + 9 / 10 :=
      mark.fire.cadence_residual_window warm.coordinates (cadence_three_dose_gain_bounds hzW).2
    constructor <;> linarith [h.1,h.2,hWarmDate]
  have hSecondWindow : start + 20 + 13 / 20 < tail.second.fire.final.time ∧
      tail.second.fire.final.time < start + 20 + 33 / 50 := by
    have h := tail.second_fire_window hMarkCharge hMarkZ
    constructor <;> linarith [h.1,h.2,hMarkDate]
  have hHighDate : tail.sourceHigh.final.time = start + 28 := by
    rw [tail.source_high_date,hMarkDate]
    ring
  have hHighWindow : start + 28 + 4 / 25 < tail.high.first.final.time ∧
      tail.high.first.final.time < start + 28 + 13 / 50 := by
    have h := tail.high_first_window
    constructor <;> linarith [h.1,h.2,hMarkDate]
  have hHighGain : 16 / 5 ≤ Real.exp (tail.sourceHigh.final.x 0 (.z p)) ∧
      Real.exp (tail.sourceHigh.final.x 0 (.z p)) ≤ 7 / 2 := by
    apply tail.sourceHigh.high_gain_bounds
    rw [tail.second.gains]
    exact hMarkZ
  have hDel : trace.deliveries = sourceTrain 0 p start 4 K := by
    have hWarmDel : warm.execution.deliveries =
        [⟨0,p,start + 4⟩,⟨0,p,start + 8⟩,⟨0,p,start + 12⟩] := by
      have h := warm.deliveries
      exact h.trans (by rw [first.date])
    have hMarkDel : mark.execution.deliveries = [⟨0,p,start + 16⟩,⟨0,p,start + 20⟩] := by
      have h := mark.deliveries
      exact h.trans (by rw [first.date])
    apply (leaf_four_deliveries first.execution warm.execution mark.execution tail.execution
      first.deliveries hWarmDel hMarkDel tail.deliveries).trans
    rw [hMarkDate,
      show start + 20 + 4 = start + 24 by ring,show (K - 8) + 2 = K - 6 by omega]
    conv_rhs => rw [show K = (K - 6) + 6 by omega]
    simp only [sourceTrain_succ,List.cons_append,List.nil_append]
    ring_nf
  refine ⟨{
    budget := hK, firstSource := first, warmup := warm, firstMark := mark, tail := tail
    execution := trace, reconstruct := rfl, warmup_date := hWarmDate, mark_date := hMarkDate
    first_window := hFirstWindow, second_window := hSecondWindow, high_source_date := hHighDate
    high_first_window := hHighWindow, high_gain_bounds := hHighGain
    date := tail.date, ready := tail.ready, charge := tail.charge, raw_none := tail.raw_none
    pending := tail.pending, gain_target := ?_, gain_other := ?_, recovery := ?_
    emission_count := ?_, calendar := hCal, deliveries := hDel
    physical := tail.physical, raw_valid := tail.raw_valid, complete := tail.complete
  }⟩
  · rw [tail.gain_target,hMarkGain]
    ring
  · intro q hq
    rw [tail.gain_other q hq]
    have h : mark.mark.final.x 0 (.z q) = first.final.x 0 (.z q) := mark.gain_other q hq
    exact h.trans (first.gains q)
  · rw [tail.recovery_gain]
    have h : mark.mark.final.x 0 .b = first.final.x 0 .b + 1 / 10 := mark.recovery_own
    rw [h,first.recovery]
    ring
  · rw [hCal,List.length_cons,tail.emission_count]
    omega

namespace ConstructedCadenceLeafK
variable {θ s p start K terminal} (c : ConstructedCadenceLeafK θ s p start K terminal)

noncomputable def restLatency : ℝ := highRestLatency (Real.exp (c.tail.sourceHigh.final.x 0 (.z p)))

theorem rest_latency_upper : c.restLatency < 13 / 50 :=
  highRestLatency_lt_twenty_six c.high_gain_bounds

/-- Its prefix dates and settling interval are the actual first three FIREs.
Only later exact-rest inputs share the proved same-cell scalar root. -/
noncomputable def packet : KernelR.Chain.Packet 3 (K - 8) 0 where
  slowDate i := if i = 0 then c.firstMark.fire.final.time
    else if i = 1 then c.tail.second.fire.final.time else c.tail.high.first.final.time
  settle := 4 + c.restLatency - c.tail.high.first.latency
  phase _ := 0
  prefix_pos := by norm_num
  tail_pos := by have h := c.budget; omega
  jitter_nonneg := by norm_num
  prefix_gap i hi := by
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl <;> norm_num <;> constructor <;>
      linarith [c.first_window.1,c.first_window.2,c.second_window.1,c.second_window.2,
        c.high_first_window.1,c.high_first_window.2]
  settle_bounds := by
    have hle := c.tail.high_first_latency_le_rest
    change c.tail.high.first.latency ≤ c.restLatency at hle
    constructor <;> linarith [c.rest_latency_upper,c.tail.high.first.early]
  phase_bounds _ := by norm_num

@[simp] theorem packet_actual_zero : c.packet.actual 0 = c.firstMark.fire.final.time := by
  norm_num [KernelR.Chain.Packet.actual,KernelR.Chain.Packet.ideal,packet]

@[simp] theorem packet_actual_one : c.packet.actual 1 = c.tail.second.fire.final.time := by
  norm_num [KernelR.Chain.Packet.actual,KernelR.Chain.Packet.ideal,packet]

@[simp] theorem packet_actual_two : c.packet.actual 2 = c.tail.high.first.final.time := by
  norm_num [KernelR.Chain.Packet.actual,KernelR.Chain.Packet.ideal,packet]

theorem packet_actual_tail (k : ℕ) :
    c.packet.actual (k + 3) = start + 32 + 4 * (k : ℝ) + c.restLatency := by
  have hnot : ¬k + 3 < 3 := by omega
  simp only [KernelR.Chain.Packet.actual,KernelR.Chain.Packet.ideal,hnot,ite_false,packet,
    Nat.reduceSub,show ¬(2 : ℕ) = 0 by decide,show ¬(2 : ℕ) = 1 by decide,
    Nat.add_sub_cancel,add_zero]
  rw [c.tail.high.first.date]
  change c.tail.sourceHigh.final.time + c.tail.high.first.latency +
    (4 + c.restLatency - c.tail.high.first.latency) + 4 * (k : ℝ) = _
  rw [c.high_source_date]
  ring

/-- The complete actual emission list realizes the packet; this calendar is
a conclusion of the physical construction, never a supplied output premise. -/
theorem packet_calendar : c.execution.emissionTimes 0 =
    List.ofFn (fun i : Fin (3 + (K - 8)) => c.packet.actual i.val) := by
  rw [c.calendar,c.tail.calendar_exact]
  have hTail :
      (sourceTrain (0 : Fin 1) p (c.firstMark.final.time + 12) 4 (K - 8)).map
        (fun d => d.due + highRestLatency (Real.exp (c.tail.sourceHigh.final.x 0 (.z p)))) =
      List.ofFn (fun i : Fin (K - 8) => c.packet.actual (i.val + 1 + 1 + 1)) := by
    simp only [sourceTrain,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rw [show i.val + 1 + 1 + 1 = i.val + 3 by omega,c.packet_actual_tail]
    change c.firstMark.final.time + 12 + 4 * (i.val : ℝ) + c.restLatency = _
    linarith [c.mark_date]
  rw [hTail]
  have hDim : 3 + (K - 8) = (K - 8) + 3 := by omega
  rw [hDim]
  conv_rhs => rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ]
  simp only [Fin.val_zero,Fin.val_succ,c.packet_actual_zero,c.packet_actual_one,c.packet_actual_two]

end ConstructedCadenceLeafK
end KernelR.Hybrid
