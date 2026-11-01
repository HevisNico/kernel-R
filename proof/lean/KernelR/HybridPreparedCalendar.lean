import KernelR.HybridCellPreparedTrain
import KernelR.HybridPulseRoot
/-! Common physical latency for prepared inputs at exact resting charge. -/
namespace KernelR.Hybrid
open Set

/-- A rest-started learned response has a real root in the actual firing bracket. -/
theorem rest_latency_exists {G : ℝ} (hg : 9 / 5 ≤ G ∧ G ≤ 12 / 5) :
    ∃ t : ℝ, 3 / 10 < t ∧ t < 9 / 10 ∧ readyPulse (1 / 10) G 0 t = 1 := by
  have hlo : readyPulse (1 / 10) G 0 (3 / 10) < 1 :=
    readyPulse_mid_gain_not_early (by norm_num) hg.2 (by norm_num) (by norm_num)
  have hhi : 1 < readyPulse (1 / 10) G 0 (9 / 10) := by
    simpa only [zero_add] using readyPulse_emission_by_deadline (start := (0 : ℝ)) (by norm_num) hg.1
  have hc : ContinuousOn (readyPulse (1 / 10) G 0) (Icc (3 / 10) (9 / 10)) := by
    unfold readyPulse response
    fun_prop
  obtain ⟨t,ht,hroot⟩ := intermediate_value_Icc (by norm_num : (3 / 10 : ℝ) ≤ 9 / 10) hc ⟨hlo.le,hhi.le⟩
  refine ⟨t,?_,?_,hroot⟩
  · by_contra h
    have heq : t = 3 / 10 := le_antisymm (le_of_not_gt h) ht.1
    rw [heq] at hroot
    linarith
  · by_contra h
    have heq : t = 9 / 10 := le_antisymm ht.2 (le_of_not_gt h)
    rw [heq] at hroot
    linarith

/-- A canonical mathematical latency, selected from the real threshold equation.
It is only used below under the proved learned-gain bounds. -/
noncomputable def restLatency (G : ℝ) : ℝ :=
  Classical.epsilon (fun t : ℝ => 3 / 10 < t ∧ t < 9 / 10 ∧ readyPulse (1 / 10) G 0 t = 1)

theorem restLatency_spec {G : ℝ} (hg : 9 / 5 ≤ G ∧ G ≤ 12 / 5) :
    3 / 10 < restLatency G ∧ restLatency G < 9 / 10 ∧ readyPulse (1 / 10) G 0 (restLatency G) = 1 :=
  Classical.epsilon_spec (rest_latency_exists hg)

theorem restLatency_unique {G t : ℝ} (hg : 9 / 5 ≤ G ∧ G ≤ 12 / 5)
    (ht : t ∈ Icc 0 (9 / 10)) (hroot : readyPulse (1 / 10) G 0 t = 1) : t = restLatency G := by
  have hspec := restLatency_spec hg
  exact readyPulse_root_unique (start := (0 : ℝ)) (by norm_num : (1 / 10 : ℝ) ≤ 7 / 50) hg.1
    (by simpa only [zero_add] using ht) ⟨by linarith [hspec.1],by linarith [hspec.2.1]⟩ hroot hspec.2.2

/-- An actual learned pulse starting at rest emits at its unique response root. -/
theorem LearnedPulse.emission_at_rest {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : LearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) :
    e.emissionTimes i = [s.time + restLatency (Real.exp (s.x i (.z p)))] := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  have hroot := pulse.trigger.firing_equation cycle hr ho hno
  rw [hq] at hroot
  have hshift : readyPulse (1 / 10) (Real.exp (s.x i (.z p))) 0
      (pulse.trigger.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 3 / 10 < pulse.trigger.beforeFire.time := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.early
  have hhi : pulse.trigger.beforeFire.time < s.time + 9 / 10 := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.deadline
  have heq := restLatency_unique hg
    (t := pulse.trigger.beforeFire.time - s.time) ⟨by linarith,by linarith⟩ hshift
  rw [pulse.emissions]
  congr 1
  linarith

/-- All actual emissions in a separated rest-started prepared train share one
physical latency. Other-cell traffic remains in the supplied execution. -/
theorem prepared_cell_calendar_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : ∀ (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (_hi : UpperRegion s) (_hv : RawValid s) (_hs : PreparedSection s i)
    (_hq : s.x i .q = 1 / 10)
    (_hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (_hspace : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (_hquiet : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time),
    e.emissionTimes i = (s.time :: times).map (fun t => t + restLatency (Real.exp (s.x i (.z p)))) := by
  intro times
  induction times with
  | nil =>
    intro s u e hi hv hs hq hz hr ho hcalendar hspace hquiet
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.learned_mid_pulse_of_valid hb hi hv i p hs hz hr ho hn (hquiet s.time (by simp))
    simpa only [List.map_cons,List.map_nil] using pulse.emission_at_rest hb hi p hs hq hz hr ho hn (hquiet s.time (by simp))
  | cons next times ih =>
    intro s u e hi hv hs hq hz hr ho hcalendar hspace hquiet
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: times.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hdate := cut.date
    have hgap : s.time + 15 / 2 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.learned_mid_pulse_of_valid hb hi hv i p hs hz hr ho
      cut.no_arrivals_before (by rw [hdate.1]; exact hgap)
    have hem := pulse.emission_at_rest hb hi p hs hq hz hr ho cut.no_arrivals_before
      (by rw [hdate.1]; exact hgap)
    have hnext := cut.prepared pulse.prepared
    have hx : cut.afterArrival.x i (.z p) = s.x i (.z p) := by
      rw [cut.entry.physical_continuous,pulse.gain_preserved p]
    have hqnext : cut.afterArrival.x i .q = 1 / 10 := by
      rw [cut.entry.physical_continuous,pulse.charge_rest]
    have hznext : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by rw [hx]; exact hz
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
      rw [hdate.2]
      exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: times, t + 15 / 2 ≤ u.time := by
      rw [hdate.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have htail := ih cut.rest (advanced.upper_region hb hi) (advanced.raw_valid hv) hnext hqnext hznext
      hrnext honext cut.later hspaceNext hquietNext
    rw [hx,hdate.2] at htail
    rw [cut.emissions,hem,htail]
    rfl

end KernelR.Hybrid
