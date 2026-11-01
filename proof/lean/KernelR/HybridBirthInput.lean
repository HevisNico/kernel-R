import KernelR.HybridPreparedTrain
/-! Select the first actual source delivery from a READY birth, including legal time-zero interleavings. -/
namespace KernelR.Hybrid
open Set

theorem Execution.ready_without_input_band {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .ready) (hq : s.x i .q ≤ 7 / 50)
    (hr : ∀ p, s.raw i p = none) (hno : ∀ p, NoArrivalAt e i p) :
    e.AllStates (fun v => v.main i = .ready) := by
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
    have hraw : ∀ p, segment.RawAbsent i p := fun p =>
      (segment.raw_absent_of_no_arrival i p (hr p) (hp.no_arrival i p (hno p))).2
    have hsol := segment.ready_no_current_solution i (segment.allStates_main_flows i .ready hstates) hraw
    have hg := exit.ready_main_departure i hv hw
    have hd := decay_upper (show s.x i .q - 1 / 10 ≤ (1 / 25 : ℝ) by linarith)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) (sub_nonneg.mpr segment.time_monotone)
    rw [hg.1] at hsol
    linarith

theorem BirthState.ready_coordinates {n s} (hborn : @BirthState n s) (i : Fin n)
    (ha : ∀ p, s.aux i p = .ready) : ReadyCoordinates s i := by
  have hi := hborn.2.2 i
  refine ⟨hi.1,⟨hi.2.1.1,by linarith [hi.2.1.2]⟩,?_⟩
  intro p
  refine ⟨ha p,?_⟩
  rcases (hi.2.2.2.2 p).2 with h | h
  · exact h.2
  · have hbad := ha p
    rw [h.1] at hbad
    contradiction

structure BirthInput {n θ route born u} (e : @Execution n θ route born u)
    (i : Fin n) (p : Port) (count : ℕ) where
  cut : DeliveryStep e ⟨i,p,0⟩ (sourceTrain i p 8 8 count)
  coordinates : ReadyCoordinates cut.afterArrival i
  recovery : 7999 / 100000 ≤ cut.afterArrival.x i .b ∧ cut.afterArrival.x i .b ≤ 8001 / 100000
  gain_preserved : ∀ q, cut.afterArrival.x i (.z q) = born.x i (.z q)
  emissions_before : cut.span.emissionTimes i = []
  raw_active : cut.afterArrival.raw i p = some cut.afterArrival.time
  raw_other : ∀ q, q ≠ p → cut.afterArrival.raw i q = none
  date : cut.afterArrival.time = 0

/-- A zero-time source arrival preserves the actual READY birth coordinates;
legal interleavings before its delivery are selected, not prescribed. -/
theorem Execution.birth_input {n θ route born u} (e : @Execution n θ route born u)
    (hborn : BirthState born) (i : Fin n) (p : Port) (count : ℕ)
    (ha : ∀ q, born.aux i q = .ready)
    (hd : e.deliveries = sourceTrain i p 0 8 (count + 1)) : Nonempty (BirthInput e i p count) := by
  have hd' : e.deliveries = ⟨i,p,0⟩ :: sourceTrain i p 8 8 count := by
    simpa only [sourceTrain_succ,zero_add] using hd
  obtain ⟨cut⟩ := e.first_delivery _ _ hd'
  have hc := hborn.ready_coordinates i ha
  have htime : cut.beforeArrival.time = born.time := by
    rw [hborn.1]
    exact cut.date.1
  have hx := cut.span.zero_duration_continuous htime
  have hmain := cut.span.ready_without_input_band i hc.ready hc.charge.2
    (hborn.2.1 i) (cut.no_arrivals_before i)
  have haux : ∀ q, cut.beforeArrival.aux i q = .ready := by
    intro q
    exact cut.span.allStates_final (cut.span.aux_ready_without_input_band i q (ha q)
      (hc.auxiliary q).2.2 (hborn.2.1 i q) (cut.no_arrivals_before i q))
  have hbefore : ReadyCoordinates cut.beforeArrival i :=
    ⟨cut.span.allStates_final hmain,by rw [hx]; exact hc.charge,
      fun q => ⟨haux q,by rw [hx]; exact (hc.auxiliary q).2⟩⟩
  have hb : 7999 / 100000 ≤ cut.afterArrival.x i .b ∧ cut.afterArrival.x i .b ≤ 8001 / 100000 := by
    rw [cut.entry.physical_continuous,hx]
    constructor <;> linarith [(hborn.2.2 i).2.2.1.1,(hborn.2.2 i).2.2.1.2]
  refine ⟨⟨cut,cut.ready_coordinates i hbefore,hb,?_,cut.span.no_emissions_of_ready_states i hmain,
    cut.raw_after,?_,cut.date.2⟩⟩
  · intro q
    rw [cut.entry.physical_continuous,hx]
  · intro q hq
    rw [cut.raw_other i q (Or.inr hq)]
    exact (cut.span.raw_absent_of_no_arrival i q (hborn.2.1 i q) (cut.no_arrivals_before i q)).1

theorem Execution.birth_source_input {n θ route born u} (e : @Execution n θ route born u)
    (hborn : BirthState born) (i : Fin n) (p : Port) (count : ℕ) (T : ℝ)
    (ha : ∀ q, born.aux i q = .ready) (hc : CompleteThrough e T)
    (hq : born.pending = sourceTrain i p 0 8 (count + 1))
    (hT : 8 * (count + 1 : ℕ) ≤ T) (hr : ∀ i t, route i t = []) : Nonempty (BirthInput e i p count) := by
  apply e.birth_input hborn i p count ha
  exact e.source_train_deliveries i p 0 8 (count + 1) T hc hq (by norm_num) (by simpa using hT) hr

end KernelR.Hybrid
