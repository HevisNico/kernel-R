import KernelR.HybridPulseSection
import KernelR.HybridPreparedTrain
/-! Resting states through terminal-date deliveries and zero-time interleavings. -/
namespace KernelR.Hybrid

/-- A zero-duration trace cannot fire away from its READY threshold. -/
theorem Execution.zero_duration_ready_main {n θ route s u} (e : @Execution n θ route s u)
    (ht : u.time = s.time) (i : Fin n) (hm : s.main i = .ready) (hq : s.x i .q ≠ 1) :
    e.AllStates (fun v => v.main i = .ready) := by
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hm with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hupper : v.time ≤ u.time := by
      have h := rest.time_monotone
      rw [exit.time_unchanged] at h
      exact h
    have hx := segment.zero_duration_continuous (by linarith [segment.time_monotone])
    have hg := (exit.ready_main_departure i hv hw).1
    rw [hx] at hg
    exact False.elim (hq hg)

/-- The sensor threshold likewise cannot be reached by zero-time jumps. -/
theorem Execution.zero_duration_ready_aux {n θ route s u} (e : @Execution n θ route s u)
    (ht : u.time = s.time) (i : Fin n) (p : Port) (hm : s.aux i p = .ready)
    (hq : s.x i (.m p) ≠ 1) : e.AllStates (fun v => v.aux i p = .ready) := by
  rcases e.first_state_change (fun v => v.aux i p) .ready
    (fun f => congrFun (congrFun f.aux_fixed i) p) hm with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hupper : v.time ≤ u.time := by
      have h := rest.time_monotone
      rw [exit.time_unchanged] at h
      exact h
    have hx := segment.zero_duration_continuous (by linarith [segment.time_monotone])
    have hg := (exit.ready_aux_departure i p hv hw).1
    rw [hx] at hg
    exact False.elim (hq hg)

/-- Any raw input introduced only at the terminal date is absent or fresh
there. This allows pending and already-delivered boundary sources alike. -/
theorem Execution.raw_none_or_terminal {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hr : s.raw i p = none)
    (hdates : ∀ d ∈ e.deliveries, d.due = u.time) :
    u.raw i p = none ∨ u.raw i p = some u.time := by
  cases hu : u.raw i p with
  | none => exact Or.inl rfl
  | some origin =>
    rcases e.raw_origin_provenance i p origin hu with h | ⟨d,hd,_,_,ht⟩
    · rw [hr] at h
      contradiction
    · exact Or.inr (congrArg some (ht.symm.trans (hdates d hd)))

structure IdlePrepared {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  gain_preserved : ∀ p, u.x i (.z p) = s.x i (.z p)
  recovery_preserved : u.x i .b = s.x i .b
  emissions : e.emissionTimes i = []

/-- The prepared resting charge is exact throughout an input-free interval. -/
theorem Execution.idle_prepared {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hr : ∀ p, s.raw i p = none) (hno : ∀ p, NoArrivalAt e i p) : Nonempty (IdlePrepared e i) := by
  have hm := e.ready_without_input i hs.ready (by rw [hq]) hr hno
  have hflows := e.allStates_main_flows i .ready hm
  have hsol := e.ready_no_current_solution i hflows
    (fun p => (e.raw_absent_of_no_arrival i p (hr p) (hno p)).2)
  have hrest : u.x i .q = 1 / 10 := by simpa only [hq,sub_self,zero_mul,add_zero] using hsol
  have haux := fun p => e.aux_no_input_rest_band i p (hs.auxiliary p).1
    (hs.auxiliary p).2 (hr p) (hno p)
  have hb := e.recovery_constant_ready i hflows
  exact ⟨⟨⟨e.allStates_final hm,by rw [hrest]; norm_num,
    by rw [hb]; exact hs.recovery,fun p => (haux p).1⟩,
    hrest,fun p => (haux p).2,hb,e.no_emissions_of_ready_states i hm⟩⟩

/-- Terminal-date arrivals change raw inputs but provide no elapsed time in
which to change prepared coordinates, modes or output counts. -/
theorem Execution.idle_prepared_boundary {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hr : ∀ p, s.raw i p = none) (hdates : ∀ d ∈ e.deliveries, d.due = u.time) :
    Nonempty (IdlePrepared e i) := by
  cases he : e.deliveries with
  | nil =>
    exact e.idle_prepared i hs hq hr (fun p => by simp [NoArrivalAt,he])
  | cons d ds =>
    obtain ⟨cut⟩ := e.first_delivery d ds he
    have hdate := hdates d (by rw [he]; simp)
    obtain ⟨idle⟩ := cut.span.idle_prepared i hs hq hr (cut.no_arrivals_before i)
    have hafter : cut.afterArrival.time = u.time := cut.date.2.trans hdate
    have hx : u.x = cut.beforeArrival.x := by
      rw [cut.rest.zero_duration_continuous hafter.symm,cut.entry.physical_continuous]
    have hm : cut.afterArrival.main i = .ready := by rw [cut.modes_after.1]; exact idle.prepared.ready
    have ha : ∀ p, cut.afterArrival.aux i p = .ready := by
      intro p
      rw [cut.modes_after.2]
      exact (idle.prepared.auxiliary p).1
    have hmain := cut.rest.zero_duration_ready_main hafter.symm i hm (by
      rw [cut.entry.physical_continuous,idle.charge_rest]; norm_num)
    have haux : ∀ p, cut.rest.AllStates (fun v => v.aux i p = .ready) := by
      intro p
      apply cut.rest.zero_duration_ready_aux hafter.symm i p (ha p)
      rw [cut.entry.physical_continuous]
      have hb := (idle.prepared.auxiliary p).2.2
      intro h
      rw [h] at hb
      norm_num at hb
    have hem : e.emissionTimes i = [] := by
      have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
      apply e.no_emissions_of_split cut.span cut.entry cut.rest cut.reconstruct i idle.emissions
        (by rw [cut.entry.no_emissions_of_delivery d hd]; rfl)
      exact cut.rest.no_emissions_of_ready_states i hmain
    refine ⟨⟨⟨cut.rest.allStates_final hmain,?_,?_,?_⟩,?_,?_,?_,hem⟩⟩
    · rw [hx]; exact idle.prepared.charge
    · rw [hx]; exact idle.prepared.recovery
    · intro p
      exact ⟨cut.rest.allStates_final (haux p),by rw [hx]; exact (idle.prepared.auxiliary p).2⟩
    · rw [hx]; exact idle.charge_rest
    · intro p
      rw [hx]; exact idle.gain_preserved p
    · rw [hx]; exact idle.recovery_preserved

end KernelR.Hybrid
