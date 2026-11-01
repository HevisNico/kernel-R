import KernelR.HybridFirstWiredArrival
import KernelR.HybridNewbornWeakCycle
import KernelR.HybridResidualLatency

/-! The newborn's first actual wire input has a genuine weak continuation.
A strict interior prefix at 168 is retained without asserting a READY state. -/
namespace KernelR.Hybrid

/-- No emitting or delivering move can alter even the list order of a queue. -/
theorem Execution.pending_eq_of_no_events {n θ route s u} (e : @Execution n θ route s u)
    (he : e.ledger.emissions = []) (hd : e.deliveries = []) : u.pending = s.pending := by
  induction e with
  | nil => rfl
  | @cons s v u move rest ih =>
    change move.ledger.emissions ++ rest.ledger.emissions = [] at he
    change move.deliveries ++ rest.deliveries = [] at hd
    obtain ⟨hem,her⟩ := List.append_eq_nil_iff.mp he
    obtain ⟨hdm,hdr⟩ := List.append_eq_nil_iff.mp hd
    rw [ih her hdr]
    cases move with
    | flow f => exact f.queue_fixed
    | jump j => cases j <;> simp_all [Move.ledger,Move.deliveries,Jump.ledger,Jump.deliveries,
        Ledger.zero,setMain,setAux,setRaw]

namespace FirstWiredArrival
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  (r : FirstWiredArrival b)

noncomputable def receiverLocal : Snapshot 1 := r.final.cellProjection 1
  (sourceTrain 0 2 320 8 16 ++ sourceTrain 0 2 480 8 16)

theorem receiver_local_physical : PhysicalInvariant (fun _ : Fin 1 => fresh) r.receiverLocal := by
  have hθ : extendParameters θ fresh (1 : Fin 2) = fresh := rfl
  refine ⟨fun j => r.receipt.physical.region 1,?_,
    fun j => r.receipt.physical.recovery_cap 1,fun j => r.receipt.physical.reserve 1⟩
  intro j p
  change r.final.x 1 (.z p) ≤ Real.log (fresh.cap p)
  have h := r.receipt.physical.gain_cap 1 p
  change r.final.x 1 (.z p) ≤ Real.log ((extendParameters θ fresh 1).cap p) at h
  rwa [hθ] at h

theorem receiver_local_raw_valid : RawValid r.receiverLocal :=
  fun _ p o h => r.receipt.raw_valid 1 p o h

theorem receiver_local_ready : ∀ j, ReadyCoordinates r.receiverLocal j :=
  fun _ => ⟨r.receipt.receiver_ready.ready,r.receipt.receiver_ready.charge,r.receipt.receiver_ready.auxiliary⟩

theorem receiver_local_charge : r.receiverLocal.x 0 .q ≤ 10001 / 100000 := by
  change r.final.x 1 .q ≤ _
  linarith [r.receiver_charge.2]

theorem receiver_local_log_gain : r.receiverLocal.x 0 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000 := by
  change r.final.x 1 (.z 1) ≤ _
  rw [r.receiver_gain]
  have hz := (newborn.gain (1 : Port)).2
  simp only [nominalGain,ite_true] at hz
  linarith

theorem receiver_local_gain : Real.exp (r.receiverLocal.x 0 (.z 1)) ≤ 4 / 3 := by
  apply fast_nominal_raw_gain_upper
  linarith [r.receiver_local_log_gain]

theorem receiver_local_raw : r.receiverLocal.raw 0 1 = some r.receiverLocal.time := r.raw_receiver

theorem receiver_local_raw_other : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ 1 → r.receiverLocal.raw j p = none := by
  intro j p h
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact r.receipt.raw_other p (by simpa using h)

theorem receiver_local_future
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    ∀ d ∈ r.receiverLocal.pending, r.receiverLocal.time + 31 / 4 ≤ d.due := by
  intro d hd
  change d ∈ sourceTrain 0 2 320 8 16 ++ sourceTrain 0 2 480 8 16 at hd
  rcases List.mem_append.mp hd with hd | hd <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd <;>
    change r.final.time + 31 / 4 ≤ _ + 8 * (k.val : ℝ) <;>
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val,(r.date_bounds hdelay).2]

/-- The actual sender section and the newborn projection reproduce the full
received state with the original global queue; local queues are not inserted. -/
theorem receiver_product_initial :
    r.cut.state.product r.receiverLocal constructedBBirthQueue = r.final := by
  have ht : r.cut.state.time = r.final.time := r.receipt.date.symm
  have hx : r.cut.state.x 0 = r.final.x 0 := r.receipt.sender_values.symm
  have hm : r.cut.state.main 0 = r.final.main 0 := r.receipt.sender_main.symm
  have ha : r.cut.state.aux 0 = r.final.aux 0 := by
    funext p
    exact (r.receipt.sender_aux p).symm
  have hr : r.cut.state.raw 0 = r.final.raw 0 := by
    funext p
    exact (r.receipt.sender_raw p).symm
  have hQ : constructedBBirthQueue = r.final.pending := r.pending.symm
  have extensionality {n} (s u : Snapshot n) (ht : s.time = u.time) (hx : s.x = u.x)
      (hm : s.main = u.main) (ha : s.aux = u.aux) (hr : s.raw = u.raw)
      (hp : s.pending = u.pending) : s = u := by
    cases s
    cases u
    simp_all only
  apply extensionality
  · exact ht
  · funext j
    by_cases hj : j = 0
    · subst j; exact hx
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; exact hm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; exact ha
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; exact hr
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · exact hQ

end FirstWiredArrival

structure FirstReceiverWeak {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (r : FirstWiredArrival b) where
  weak : WeakInputCycle (fun _ : Fin 1 => fresh) (fun _ _ => []) r.receiverLocal 0 1
  cut168 : weak.execution.BeforeFlowCut 168
  cut_emissions : cut168.cut.ledger.emissions = []
  cut_deliveries : cut168.cut.deliveries = []
  cut_physical : PhysicalInvariant (fun _ : Fin 1 => fresh) cut168.state
  cut_raw_valid : RawValid cut168.state
  cut_pending : cut168.state.pending = r.receiverLocal.pending

theorem first_receiver_weak_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (r : FirstWiredArrival b)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (FirstReceiverWeak r) := by
  obtain ⟨weak⟩ := narrow_weak_input_cycle_exists (route := fun _ _ => []) r.receiverLocal hb.extend_new
    r.receiver_local_physical r.receiver_local_raw_valid 0 1 r.receiver_local_ready
    r.receiver_local_charge r.receiver_local_gain r.receiver_local_log_gain
    r.receiver_local_raw r.receiver_local_raw_other (r.receiver_local_future hdelay)
  obtain ⟨cut⟩ := weak.execution.before_flow_cut_exists 168
    (by change r.final.time ≤ (168 : ℝ); linarith [(r.date_bounds hdelay).2])
    (by rw [weak.date]; change (168 : ℝ) < r.final.time + 15 / 2; linarith [(r.date_bounds hdelay).1])
  have he : cut.cut.ledger.emissions = [] := by
    have h : cut.cut.ledger.emissions ++ cut.rest.ledger.emissions = [] :=
      cut.emissions.symm.trans weak.emissions
    exact (List.append_eq_nil_iff.mp h).1
  have hd : cut.cut.deliveries = [] := by
    have h : cut.cut.deliveries ++ cut.rest.deliveries = [] := cut.deliveries.symm.trans weak.deliveries
    exact (List.append_eq_nil_iff.mp h).1
  exact ⟨⟨weak,cut,he,hd,cut.cut.physical_invariant hb.extend_new r.receiver_local_physical,
    cut.cut.raw_valid r.receiver_local_raw_valid,cut.cut.pending_eq_of_no_events he hd⟩⟩

namespace FirstReceiverWeak
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} (w : FirstReceiverWeak r)

noncomputable def «local» (_w : FirstReceiverWeak r) : Snapshot 1 := r.receiverLocal

noncomputable def continuation : Execution (fun _ : Fin 1 => fresh) (fun _ _ => []) w.cut168.state w.weak.final :=
  .cons (.flow w.cut168.flow) w.cut168.rest

theorem complete : CompleteThrough w.cut168.cut 168 := w.cut168.complete

theorem before_guards : BeforeGuards w.cut168.state w.cut168.state.x := w.cut168.before_guards

theorem continuation_emissions : w.continuation.ledger.emissions = [] := by
  have h : w.cut168.cut.ledger.emissions ++ w.cut168.rest.ledger.emissions = [] :=
    w.cut168.emissions.symm.trans w.weak.emissions
  exact (List.append_eq_nil_iff.mp h).2

theorem continuation_deliveries : w.continuation.deliveries = [] := by
  have h : w.cut168.cut.deliveries ++ w.cut168.rest.deliveries = [] :=
    w.cut168.deliveries.symm.trans w.weak.deliveries
  exact (List.append_eq_nil_iff.mp h).2

/-- The cut's own empty emission trace keeps its main mode READY. This uses
only this actual prefix, rather than the later weak endpoint. -/
theorem cut_main_states : w.cut168.cut.AllStates (fun v => v.main 0 = .ready) :=
  w.cut168.cut.ready_states_of_no_emissions 0 (r.receiver_local_ready 0).ready
    (by simp [Execution.emissionTimes,w.cut_emissions])

theorem cut_main_ready : w.cut168.state.main 0 = .ready :=
  w.cut168.cut.allStates_final w.cut_main_states

theorem cut_mark_zero (p : Port) : w.cut168.cut.ledger.mark 0 p = 0 :=
  w.cut168.cut.mark_zero_ready 0 p (w.cut168.cut.allStates_main_flows 0 .ready w.cut_main_states)

theorem cut_recovery : w.cut168.state.x 0 .b = r.receiverLocal.x 0 .b :=
  w.cut168.cut.recovery_constant_ready 0 (w.cut168.cut.allStates_main_flows 0 .ready w.cut_main_states)

theorem cut_no_arrival (p : Port) : NoArrivalAt w.cut168.cut 0 p := by
  simp [NoArrivalAt,w.cut_deliveries]

/-- The 419/300 sensor deadline lies strictly before 168 for every admitted
wire jitter; a complete actual sensor cycle is already present in this cut. -/
theorem cut_sensor_cycle {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (SensorCycle w.cut168.cut 0 1) := by
  apply w.cut168.cut.sensor_cycle hb.extend_new r.receiver_local_physical.region 0 1
    ((r.receiver_local_ready 0).auxiliary 1).1 r.receiver_local_raw
    ((r.receiver_local_ready 0).auxiliary 1).2
  rw [w.cut168.date]
  change r.final.time + 419 / 300 ≤ (168 : ℝ)
  linarith [(r.date_bounds hdelay).2]

theorem cut_error_and_gain {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    w.cut168.cut.ledger.error 0 1 = 3 / 5 ∧
      w.cut168.state.x 0 (.z 1) = r.receiverLocal.x 0 (.z 1) + 3 / 5 := by
  obtain ⟨cycle⟩ := w.cut_sensor_cycle hb hdelay
  have hh : r.receiverLocal.x 0 (.z 1) + 3 / 5 < Real.log (fresh.cap 1) := by
    linarith [r.receiver_local_log_gain,hb.extend_new.fast_nominal_headroom 0 1]
  exact cycle.total_error_of_invariant hb.extend_new r.receiver_local_physical
    r.receiver_local_raw_valid w.cut_main_states hh r.receiver_local_raw (w.cut_no_arrival 1)

theorem cut_error_dose {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    w.cut168.cut.ledger.error 0 1 = 3 / 5 := (w.cut_error_and_gain hb hdelay).1

theorem cut_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    w.cut168.state.x 0 (.z 1) = r.receiverLocal.x 0 (.z 1) + 3 / 5 :=
  (w.cut_error_and_gain hb hdelay).2

theorem cut_sensor_rest {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    w.cut168.state.aux 0 1 = .ready ∧ w.cut168.state.x 0 (.m 1) = 1 / 40 := by
  obtain ⟨cycle⟩ := w.cut_sensor_cycle hb hdelay
  exact cycle.final_rest r.receiver_local_raw_valid r.receiver_local_raw (w.cut_no_arrival 1)

theorem cut_other_aux (p : Port) (hp : p ≠ 1) :
    (w.cut168.state.aux 0 p = .ready ∧ RestBand (w.cut168.state.x 0 (.m p))) ∧
      w.cut168.state.x 0 (.z p) = r.receiverLocal.x 0 (.z p) :=
  w.cut168.cut.aux_no_input_rest_band 0 p ((r.receiver_local_ready 0).auxiliary p).1
    ((r.receiver_local_ready 0).auxiliary p).2 (r.receiver_local_raw_other 0 p (Or.inr hp))
    (w.cut_no_arrival p)

theorem cut_aux_rest {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) (p : Port) :
    w.cut168.state.aux 0 p = .ready ∧ RestBand (w.cut168.state.x 0 (.m p)) := by
  by_cases hp : p = 1
  · subst p
    have hs := w.cut_sensor_rest hb hdelay
    exact ⟨hs.1,by rw [hs.2]; norm_num [RestBand]⟩
  · exact (w.cut_other_aux p hp).1

end FirstReceiverWeak
end KernelR.Hybrid
