import KernelR.HybridSensor
import KernelR.HybridPulseTransversality
/-! Construct the first physical scalar crossing, independently of any Execution. -/
namespace KernelR.Hybrid
open Set

/-- A continuous response which starts below a threshold and ends above it has
a first contact, with strict preguard throughout the half-open preceding span.
Global monotonicity, transversality and an existing execution are unnecessary. -/
theorem scalar_first_crossing {f : ℝ → ℝ} {start deadline level : ℝ}
    (hf : Continuous f) (ht : start < deadline)
    (hlo : f start < level) (hhi : level < f deadline) :
    ∃ root : ℝ, start < root ∧ root < deadline ∧ f root = level ∧
      ∀ t ∈ Ico start root, f t < level := by
  obtain ⟨w,hw,hvalue⟩ := intermediate_value_Icc ht.le hf.continuousOn ⟨hlo.le,hhi.le⟩
  have hcompact : IsCompact (Icc start deadline ∩ f ⁻¹' {level}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  have hnonempty : (Icc start deadline ∩ f ⁻¹' {level}).Nonempty := by
    exact ⟨w,hw,by simpa only [Set.mem_preimage,Set.mem_singleton_iff] using hvalue⟩
  obtain ⟨root,hroot⟩ := hcompact.exists_isLeast hnonempty
  have hmem : root ∈ Icc start deadline := hroot.1.1
  have hvalue : f root = level := hroot.1.2
  have hstart : start < root := by
    by_contra hn
    have heq : root = start := le_antisymm (le_of_not_gt hn) hmem.1
    rw [heq] at hvalue
    linarith
  have hend : root < deadline := by
    by_contra hn
    have heq : root = deadline := le_antisymm hmem.2 (le_of_not_gt hn)
    rw [heq] at hvalue
    linarith
  refine ⟨root,hstart,hend,hvalue,?_⟩
  intro t ht
  by_contra hn
  obtain ⟨earlier,hearlier,hcross⟩ := intermediate_value_Icc ht.1 hf.continuousOn
    ⟨hlo.le,le_of_not_gt hn⟩
  have hleast : root ≤ earlier := hroot.2 ⟨⟨hearlier.1,hearlier.2.trans (ht.2.le.trans hmem.2)⟩,hcross⟩
  linarith [hearlier.2,ht.2]

/-- Threshold-one specialization in time relative to the input origin. -/
theorem scalar_first_one_crossing {f : ℝ → ℝ} {horizon : ℝ}
    (hf : Continuous f) (ht : 0 < horizon) (hlo : f 0 < 1) (hhi : 1 < f horizon) :
    ∃ root : ℝ, 0 < root ∧ root < horizon ∧ f root = 1 ∧
      ∀ t ∈ Ico 0 root, f t < 1 :=
  scalar_first_crossing hf ht hlo hhi

/-- A real sensor response starting in its birth/rest band has a first MARK
threshold in (.01,.025), and its READY guard holds strictly at every prior
point. This theorem supplies a path cutoff, not an extracted observed event. -/
theorem auxPulse_first_sensor_crossing {initial amplitude start : ℝ}
    (hl : 1 / 40 - 1 / 100000 ≤ initial) (hu : initial ≤ 1 / 40 + 1 / 100000)
    (ha : 31 ≤ amplitude) (hb : amplitude ≤ 60) :
    ∃ latency : ℝ, 1 / 100 < latency ∧ latency < 1 / 40 ∧
      auxPulse initial amplitude start (start + latency) = 1 ∧
      ∀ t ∈ Ico start (start + latency), auxPulse initial amplitude start t < 1 := by
  have hc : Continuous (fun t : ℝ => auxPulse initial amplitude start (start + t)) := by
    unfold auxPulse readyPulse response
    fun_prop
  have hzero : auxPulse initial amplitude start (start + 0) < 1 := by
    rw [add_zero,auxPulse_initial]
    linarith
  obtain ⟨latency,hpos,hend,hroot,hprior⟩ := scalar_first_one_crossing hc
    (by norm_num : (0 : ℝ) < 1 / 40) hzero (auxPulse_above_at_deadline hl ha)
  have hearly : 1 / 100 < latency := by
    by_contra hn
    have h := auxPulse_below_before_early hu hb (by linarith : start ≤ start + latency)
      (by linarith : start + latency ≤ start + 1 / 100)
    rw [hroot] at h
    exact (lt_irrefl (1 : ℝ)) h
  refine ⟨latency,hearly,hend,hroot,?_⟩
  intro t ht
  have h := hprior (t - start) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  simpa only [show start + (t - start) = t by ring] using h

/-- The sensor contact is transverse for the same rest band and gain bounds.
The pulse derivative equation turns the strict deadline into a positive slope. -/
theorem auxPulse_first_sensor_crossing_transversal {initial amplitude start : ℝ}
    (hl : 1 / 40 - 1 / 100000 ≤ initial) (hu : initial ≤ 1 / 40 + 1 / 100000)
    (ha : 31 ≤ amplitude) (hb : amplitude ≤ 60) :
    ∃ latency : ℝ, 1 / 100 < latency ∧ latency < 1 / 40 ∧
      auxPulse initial amplitude start (start + latency) = 1 ∧
      (∀ t ∈ Ico start (start + latency), auxPulse initial amplitude start t < 1) ∧
      0 < deriv (auxPulse initial amplitude start) (start + latency) := by
  obtain ⟨latency, early, deadline, root, prior⟩ :=
    auxPulse_first_sensor_crossing hl hu ha hb (start := start)
  refine ⟨latency, early, deadline, root, prior, ?_⟩
  apply auxPulse_transversal_of_later_value (by linarith : 0 ≤ amplitude)
    (show start + latency < start + 1 / 40 by linarith)
  rw [root]
  exact auxPulse_above_at_deadline hl ha

/-- Every own physical input gain in the fabrication box supports the cutoff;
no threshold root or execution is assumed as input. -/
theorem PhysicalBox.first_sensor_crossing {n θ ε} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) {initial start : ℝ}
    (hl : 1 / 40 - 1 / 100000 ≤ initial) (hu : initial ≤ 1 / 40 + 1 / 100000) :
    ∃ latency : ℝ, 1 / 100 < latency ∧ latency < 1 / 40 ∧
      auxPulse initial ((θ i).inputGain p) start (start + latency) = 1 ∧
      ∀ t ∈ Ico start (start + latency), auxPulse initial ((θ i).inputGain p) start t < 1 :=
  auxPulse_first_sensor_crossing hl hu (hb.input_gain_lower i p) (hb.coarse_upper i p).2.2.2.2

/-- The fabrication box also supplies the transverse sensor contact. -/
theorem PhysicalBox.first_sensor_crossing_transversal {n θ ε}
    (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) {initial start : ℝ}
    (hl : 1 / 40 - 1 / 100000 ≤ initial) (hu : initial ≤ 1 / 40 + 1 / 100000) :
    ∃ latency : ℝ, 1 / 100 < latency ∧ latency < 1 / 40 ∧
      auxPulse initial ((θ i).inputGain p) start (start + latency) = 1 ∧
      (∀ t ∈ Ico start (start + latency),
        auxPulse initial ((θ i).inputGain p) start t < 1) ∧
      0 < deriv (auxPulse initial ((θ i).inputGain p) start) (start + latency) :=
  auxPulse_first_sensor_crossing_transversal hl hu
    (hb.input_gain_lower i p) (hb.coarse_upper i p).2.2.2.2

#print axioms auxPulse_first_sensor_crossing_transversal
#print axioms PhysicalBox.first_sensor_crossing_transversal

end KernelR.Hybrid
