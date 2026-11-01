import KernelR.HybridCadenceHighTrain
import KernelR.HybridPulseRoot
/-! A high-gain resting reference and actual cadence output calendars. -/
namespace KernelR.Hybrid
open Set

/-- High gains have their own resting root before .3; the older resting
reference with a (.3,.9) domain does not describe these physical inputs. -/
theorem high_rest_latency_exists {G : ℝ} (hg : 16 / 5 ≤ G ∧ G ≤ 7 / 2) :
    ∃ t : ℝ, 1 / 10 < t ∧ t < 3 / 10 ∧ readyPulse (1 / 10) G 0 t = 1 := by
  have hlo : readyPulse (1 / 10) G 0 (1 / 10) < 1 :=
    readyPulse_high_gain_not_early (by norm_num) hg.2 (by norm_num) (by norm_num)
  have hhi : 1 < readyPulse (1 / 10) G 0 (3 / 10) := by
    simpa only [zero_add] using readyPulse_high_gain_by_deadline (start := (0 : ℝ)) (by norm_num) hg.1
  have hc : ContinuousOn (readyPulse (1 / 10) G 0) (Icc (1 / 10) (3 / 10)) := by
    unfold readyPulse response
    fun_prop
  obtain ⟨t,ht,hroot⟩ := intermediate_value_Icc (by norm_num : (1 / 10 : ℝ) ≤ 3 / 10) hc ⟨hlo.le,hhi.le⟩
  refine ⟨t,?_,?_,hroot⟩
  · by_contra h
    have heq : t = 1 / 10 := le_antisymm (le_of_not_gt h) ht.1
    rw [heq] at hroot
    linarith
  · by_contra h
    have heq : t = 3 / 10 := le_antisymm ht.2 (le_of_not_gt h)
    rw [heq] at hroot
    linarith

noncomputable def highRestLatency (G : ℝ) : ℝ :=
  Classical.epsilon (fun t : ℝ => 1 / 10 < t ∧ t < 3 / 10 ∧ readyPulse (1 / 10) G 0 t = 1)

theorem highRestLatency_spec {G : ℝ} (hg : 16 / 5 ≤ G ∧ G ≤ 7 / 2) :
    1 / 10 < highRestLatency G ∧ highRestLatency G < 3 / 10 ∧
      readyPulse (1 / 10) G 0 (highRestLatency G) = 1 :=
  Classical.epsilon_spec (high_rest_latency_exists hg)

theorem highRestLatency_unique {G t : ℝ} (hg : 16 / 5 ≤ G ∧ G ≤ 7 / 2)
    (ht : t ∈ Icc 0 (9 / 10)) (hroot : readyPulse (1 / 10) G 0 t = 1) : t = highRestLatency G := by
  have hspec := highRestLatency_spec hg
  exact readyPulse_root_unique (start := (0 : ℝ)) (by norm_num : (1 / 10 : ℝ) ≤ 7 / 50)
    (by linarith [hg.1]) (by simpa only [zero_add] using ht)
    ⟨by linarith [hspec.1],by linarith [hspec.2.1]⟩ hroot hspec.2.2

/-- The actual firing from exact rest agrees with this own-gain root. -/
theorem HighGainTrigger.high_rest_date {n θ route s u i p} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) (cycle : SensorCycle e i p)
    (hq : s.x i .q = 1 / 10)
    (hg : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    tr.beforeFire.time = s.time + highRestLatency (Real.exp (s.x i (.z p))) := by
  have hroot := tr.firing_equation cycle hr ho hno
  rw [hq] at hroot
  have hshift : readyPulse (1 / 10) (Real.exp (s.x i (.z p))) 0 (tr.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 1 / 10 < tr.beforeFire.time := by
    simpa only [tr.entry.time_unchanged] using tr.early
  have hhi : tr.beforeFire.time < s.time + 9 / 10 := by
    simpa only [tr.entry.time_unchanged] using tr.deadline
  have h := highRestLatency_unique hg ⟨by linarith,by linarith⟩ hshift
  linarith

/-- Nonnegative residual charge can advance the first high-gain firing.
It is retained as its actual distinct date, rather than replaced by rest. -/
theorem HighGainTrigger.latency_le_high_rest {n θ route s u i p} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) (cycle : SensorCycle e i p)
    (hq : 1 / 10 ≤ s.x i .q)
    (hg : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    tr.beforeFire.time - s.time ≤ highRestLatency (Real.exp (s.x i (.z p))) := by
  have hroot := tr.firing_equation cycle hr ho hno
  have hshift : readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) 0 (tr.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 1 / 10 < tr.beforeFire.time := by
    simpa only [tr.entry.time_unchanged] using tr.early
  have hhi : tr.beforeFire.time < s.time + 9 / 10 := by
    simpa only [tr.entry.time_unchanged] using tr.deadline
  have hspec := highRestLatency_spec hg
  exact first_firing_le_rest_reference (start := (0 : ℝ)) hq (by linarith [hg.1])
    ⟨by linarith,by linarith⟩ ⟨by linarith [hspec.1],by linarith [hspec.2.1]⟩ hshift hspec.2.2

theorem CadenceLearnedPulse.emission_at_high_rest {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : CadenceLearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (ha : s.aux i p = .ready) (hx : RestBand (s.x i (.m p)))
    (hq : s.x i .q = 1 / 10)
    (hg : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 419 / 300 ≤ u.time) :
    e.emissionTimes i = [s.time + highRestLatency (Real.exp (s.x i (.z p)))] := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  rw [pulse.emissions,pulse.trigger.high_rest_date cycle hq hg hr ho hno]

theorem CadenceLearnedPulse.high_residual_calendar {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : CadenceLearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (ha : s.aux i p = .ready) (hx : RestBand (s.x i (.m p)))
    (hq : 1 / 10 ≤ s.x i .q)
    (hg : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 419 / 300 ≤ u.time) :
    ∃ first : ℝ, 1 / 10 < first ∧ first < 3 / 10 ∧
      first ≤ highRestLatency (Real.exp (s.x i (.z p))) ∧ e.emissionTimes i = [s.time + first] := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  let first := pulse.trigger.beforeFire.time - s.time
  have hlo : s.time + 1 / 10 < pulse.trigger.beforeFire.time := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.early
  have hle := pulse.trigger.latency_le_high_rest cycle hq hg hr ho hno
  have hspec := highRestLatency_spec hg
  refine ⟨first,by dsimp [first]; linarith,by dsimp [first]; linarith [hspec.2.1],hle,?_⟩
  rw [pulse.emissions]
  congr 1
  dsimp [first]
  ring

/-- Exact-rest high-gain inputs have one common physical latency. Every
receiving-cell arrival and all other-cell traffic remain in the execution. -/
theorem cadence_high_calendar_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : ∀ (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (_hf : PhysicalInvariant θ s) (_hv : RawValid s) (_hm : s.main i = .ready)
    (_hq : s.x i .q = 1 / 10)
    (_hgain : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (_hbrecovery : 37999 / 100000 ≤ s.x i .b)
    (_ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (_hspace : (s.time :: times).Pairwise (fun t v => t + 19 / 5 ≤ v))
    (_hquiet : ∀ t ∈ s.time :: times, t + 19 / 5 ≤ u.time),
    e.emissionTimes i = (s.time :: times).map (fun t => t + highRestLatency (Real.exp (s.x i (.z p)))) := by
  intro times
  induction times with
  | nil =>
    intro s u e hf hv hm hq hgain hbrecovery ha hr ho hcalendar hspace hquiet
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.high_gain_pulse_of_valid hb hf.region hv i p hm (by rw [hq]; norm_num) hgain
      ⟨hbrecovery,hf.recovery_cap i⟩ ha hr ho hn (hquiet s.time (by simp))
    simpa only [List.map_cons,List.map_nil] using pulse.emission_at_high_rest hb hf.region p (ha p).1 (ha p).2
      hq hgain hr ho hn (by linarith [hquiet s.time (by simp)])
  | cons next times ih =>
    intro s u e hf hv hm hq hgain hbrecovery ha hr ho hcalendar hspace hquiet
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: times.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hgap : s.time + 19 / 5 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.high_gain_pulse_of_valid hb hf.region hv i p hm (by rw [hq]; norm_num) hgain
      ⟨hbrecovery,hf.recovery_cap i⟩ ha hr ho cut.no_arrivals_before (by rw [cut.date.1]; exact hgap)
    have hem := pulse.emission_at_high_rest hb hf.region p (ha p).1 (ha p).2 hq hgain hr ho
      cut.no_arrivals_before (by rw [cut.date.1]; linarith)
    have hmnext : cut.afterArrival.main i = .ready := by rw [cut.modes_after.1]; exact pulse.ready
    have hqnext : cut.afterArrival.x i .q = 1 / 10 := by rw [cut.entry.physical_continuous,pulse.charge_rest]
    have hx : cut.afterArrival.x i (.z p) = s.x i (.z p) := by rw [cut.entry.physical_continuous,pulse.gain_preserved p]
    have hgainnext : 16 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 7 / 2 := by rw [hx]; exact hgain
    have hbnext : 37999 / 100000 ≤ cut.afterArrival.x i .b := by
      rw [cut.entry.physical_continuous,pulse.recovery_preserved]; exact hbrecovery
    have hanext : ∀ q, cut.afterArrival.aux i q = .ready ∧ RestBand (cut.afterArrival.x i (.m q)) := by
      intro q
      rw [cut.modes_after.2,cut.entry.physical_continuous]
      exact pulse.auxiliary q
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: times).Pairwise (fun t v => t + 19 / 5 ≤ v) := by
      rw [cut.date.2]; exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: times, t + 19 / 5 ≤ u.time := by
      rw [cut.date.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have htail := ih cut.rest (advanced.physical_invariant hb hf) (advanced.raw_valid hv)
      hmnext hqnext hgainnext hbnext hanext hrnext honext cut.later hspaceNext hquietNext
    rw [hx,cut.date.2] at htail
    rw [cut.emissions,hem,htail]
    rfl

/-- The first actual residual latency is kept separately; only subsequent
exact-rest inputs use the common high-gain response root. -/
theorem cadence_high_residual_calendar_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main i = .ready)
    (hq : 1 / 10 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 2)
    (hgain : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hbrecovery : 37999 / 100000 ≤ s.x i .b)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: times).Pairwise (fun t v => t + 19 / 5 ≤ v))
    (hquiet : ∀ t ∈ s.time :: times, t + 19 / 5 ≤ u.time) :
    ∃ first : ℝ, 1 / 10 < first ∧ first < 3 / 10 ∧
      first ≤ highRestLatency (Real.exp (s.x i (.z p))) ∧
      e.emissionTimes i = (s.time + first) :: times.map (fun t => t + highRestLatency (Real.exp (s.x i (.z p)))) := by
  cases times with
  | nil =>
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.high_gain_pulse_of_valid hb hf.region hv i p hm
      ⟨by linarith [hq.1],hq.2⟩ hgain ⟨hbrecovery,hf.recovery_cap i⟩ ha hr ho hn (hquiet s.time (by simp))
    obtain ⟨first,hlo,hhi,hle,hem⟩ := pulse.high_residual_calendar hb hf.region p (ha p).1 (ha p).2
      hq.1 hgain hr ho hn (by linarith [hquiet s.time (by simp)])
    exact ⟨first,hlo,hhi,hle,by simpa only [List.map_nil] using hem⟩
  | cons next tail =>
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: tail.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hgap : s.time + 19 / 5 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.high_gain_pulse_of_valid hb hf.region hv i p hm
      ⟨by linarith [hq.1],hq.2⟩ hgain ⟨hbrecovery,hf.recovery_cap i⟩ ha hr ho cut.no_arrivals_before
      (by rw [cut.date.1]; exact hgap)
    obtain ⟨first,hlo,hhi,hle,hem⟩ := pulse.high_residual_calendar hb hf.region p (ha p).1 (ha p).2
      hq.1 hgain hr ho cut.no_arrivals_before (by rw [cut.date.1]; linarith)
    have hmnext : cut.afterArrival.main i = .ready := by rw [cut.modes_after.1]; exact pulse.ready
    have hqnext : cut.afterArrival.x i .q = 1 / 10 := by rw [cut.entry.physical_continuous,pulse.charge_rest]
    have hx : cut.afterArrival.x i (.z p) = s.x i (.z p) := by rw [cut.entry.physical_continuous,pulse.gain_preserved p]
    have hgainnext : 16 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 7 / 2 := by rw [hx]; exact hgain
    have hbnext : 37999 / 100000 ≤ cut.afterArrival.x i .b := by
      rw [cut.entry.physical_continuous,pulse.recovery_preserved]; exact hbrecovery
    have hanext : ∀ q, cut.afterArrival.aux i q = .ready ∧ RestBand (cut.afterArrival.x i (.m q)) := by
      intro q
      rw [cut.modes_after.2,cut.entry.physical_continuous]
      exact pulse.auxiliary q
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: tail).Pairwise (fun t v => t + 19 / 5 ≤ v) := by
      rw [cut.date.2]; exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: tail, t + 19 / 5 ≤ u.time := by
      rw [cut.date.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have htail := cadence_high_calendar_of_valid hb i p tail cut.rest (advanced.physical_invariant hb hf)
      (advanced.raw_valid hv) hmnext hqnext hgainnext hbnext hanext hrnext honext cut.later hspaceNext hquietNext
    rw [hx,cut.date.2] at htail
    refine ⟨first,hlo,hhi,hle,?_⟩
    rw [cut.emissions,hem,htail]
    rfl

end KernelR.Hybrid
