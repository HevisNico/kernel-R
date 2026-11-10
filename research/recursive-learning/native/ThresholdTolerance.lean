import KernelR.HybridCadenceHighFireExistence

/-! A one-shot readout with an uncertain, fixed main FIRE threshold.
The cell starts just after admission of one canonical pulse. The original
MARK and SILENT transitions are used; the experiment ends at the first
FIRE or at the read deadline. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- Both inputs use the same cell. The arrival port is the task input. -/
def tolerancePort (high : Bool) : Port := if high then 1 else 0

/-- Ready at rest, with precisely the selected canonical pulse admitted. -/
noncomputable def toleranceStartOn (time : ℝ) (gains : Port → ℝ) (port : Port) : Snapshot 1 where
  time := time
  x := fun _ c => match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z p => gains p
    | .b => 2 / 25
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ p => if p = port then some time else none
  pending := []

private theorem early_bound {G time t : ℝ} (upper : G ≤ 12 / 5)
    (start : time ≤ t) (stop : t ≤ time + 3 / 10) :
    readyPulse (1 / 10) G time t ≤ 47 / 50 := by
  have nonneg := response_nonnegative (show 0 ≤ t - time by linarith)
  have responseBound := response_mid_early_upper (t := t - time) (by linarith) (by linarith)
  have gainBound := mul_le_mul_of_nonneg_right upper nonneg
  have bound := mul_le_mul_of_nonneg_left responseBound (by norm_num : (0 : ℝ) ≤ 12 / 5)
  simp only [readyPulse, sub_self, zero_mul, add_zero]
  linarith

private theorem strong_deadline {G time : ℝ} (lower : 2 ≤ G) :
    (21 / 20 : ℝ) < readyPulse (1 / 10) G time (time + 9 / 10) := by
  have h := mul_le_mul_of_nonneg_right lower
    (response_nonnegative (by norm_num : (0 : ℝ) ≤ 9 / 10))
  have bound := response_emission_deadline
  simp only [readyPulse, sub_self, zero_mul, add_zero, add_sub_cancel_left]
  linarith

private def auxiliaryGuards (s : Snapshot 1) (values : Values 1) : Prop :=
  ∀ i p, match s.aux i p with
    | .ready => values i (.m p) < 1
    | .mark => 4 / 5 < values i (.m p)
    | .silent => 1 / 10 < values i (.m p)
    | .error => 1 / 40 < values i (.m p)

/-- The original mode-fixed R path, cut at the chosen stop. The sole
changed interior guard is the upper READY guard for the main charge. -/
structure TolerantLeg (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    (origin level stop : ℝ) where
  positive : s.time < stop
  live : origin ≤ s.time ∧ stop < origin + 1
  empty : s.pending = []
  integral :
    let path := readyProtectedValues θ s 0 p .silent (some origin)
    ∀ t ∈ Icc s.time stop, ∀ i c,
      path t i c = s.x i c + ∫ v in s.time..t, field θ s (path v) v i c
  continuous :
    ∀ i c, Continuous (fun t => readyProtectedValues θ s 0 p .silent (some origin) t i c)
  integrable :
    let path := readyProtectedValues θ s 0 p .silent (some origin)
    ∀ i c, IntervalIntegrable (fun t => field θ s (path t) t i c) volume s.time stop
  main_guard : ∀ t ∈ Ico s.time stop,
    readyProtectedValues θ s 0 p .silent (some origin) t 0 .q < level
  aux_guards : ∀ t ∈ Icc s.time stop,
    auxiliaryGuards s (readyProtectedValues θ s 0 p .silent (some origin) t)

/-- The actual snapshot after pulse admission, with the sensors in the
rest band used by the MARK proof. Energy and recovery are supplied by
the snapshot's physical invariant. -/
structure ReadoutReady (s : Snapshot 1) (p : Port) : Prop where
  main : ∀ i, s.main i = .ready
  charge : s.x 0 .q = 1 / 10
  aux : ∀ i q, s.aux i q = .ready
  rest : ∀ i q, RestBand (s.x i (.m q))
  raw : s.raw 0 p = some s.time
  otherRaw : ∀ i q, i ≠ 0 ∨ q ≠ p → s.raw i q = none
  empty : s.pending = []

/-- A one-shot decision prefix. The original MARK and SILENT flows
also satisfy the perturbed READY guard. On a positive output the terminal
event is a transverse FIRE at the perturbed level. The resulting mode
change is the ordinary R update from READY to FAST. -/
structure TolerantSnapshotDecision (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (port : Port) (high : Bool) (level : ℝ) where
  physical_start : PhysicalInvariant θ s
  mark : FirstInputMark θ s 0 port
  silent : FirstInputSilent mark
  before_mark : ∀ t ∈ Ico s.time (s.time + mark.latency), mark.flow.path t 0 .q < level
  before_silent : ∀ t ∈ Ico mark.final.time silent.final.time, silent.flow.path t 0 .q < level
  stop : ℝ
  leg : TolerantLeg θ silent.final port s.time level stop
  scalar_guard : ∀ t ∈ Ico s.time stop,
    readyPulse (1 / 10) (Real.exp (s.x 0 (.z port))) s.time t < level
  charge : (readyProtectedEnd θ silent.final 0 port .silent (some s.time) stop).x 0 .q =
    readyPulse (1 / 10) (Real.exp (s.x 0 (.z port))) s.time stop
  outcome :
    let endpoint := readyProtectedEnd θ silent.final 0 port .silent (some s.time) stop
    if high then
      s.time + 3 / 10 < stop ∧ stop < s.time + 9 / 10 ∧ endpoint.x 0 .q = level ∧
        0 < field θ endpoint endpoint.x stop 0 .q
    else stop = s.time + 9 / 10 ∧ endpoint.x 0 .q < level

noncomputable def TolerantSnapshotDecision.final {θ s port high level}
    (run : TolerantSnapshotDecision θ s port high level) : Snapshot 1 :=
  let endpoint := readyProtectedEnd θ run.silent.final 0 port .silent (some s.time) run.stop
  if high then setMain endpoint 0 .fast else endpoint

abbrev TolerantPortDecision (θ : Fin 1 → Parameters) (time : ℝ) (gains : Port → ℝ)
    (port : Port) (high : Bool) (level : ℝ) :=
  TolerantSnapshotDecision θ (toleranceStartOn time gains port) port high level

noncomputable abbrev TolerantPortDecision.final {θ time gains port high level}
    (run : TolerantPortDecision θ time gains port high level) : Snapshot 1 :=
  TolerantSnapshotDecision.final run

theorem tolerant_snapshot_readout {θ ε s port high level}
    (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (ready : ReadoutReady s port)
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (gain : if high then
      2 ≤ Real.exp (s.x 0 (.z port)) ∧ Real.exp (s.x 0 (.z port)) ≤ 12 / 5
      else Real.exp (s.x 0 (.z port)) ≤ 6 / 5) :
    Nonempty (TolerantSnapshotDecision θ s port high level) := by
  let p := port
  let time := s.time
  let G := Real.exp (s.x 0 (.z p))
  let q := readyPulse (1 / 10) G time
  have amplitude : G ≤ 12 / 5 := by
    cases high
    · simp only [Bool.false_eq_true, ite_false] at gain
      dsimp [G, p]
      linarith
    · exact gain.2
  have hEarly : ∀ t, time ≤ t → t ≤ time + 3 / 10 → q t < level :=
    fun t ht hu => (early_bound amplitude ht hu).trans_lt (by linarith [threshold.1])
  have earlyStock : ∀ t, s.time ≤ t → t ≤ s.time + 1 / 10 →
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t < 1 := by
    intro t ht hu
    rw [ready.charge]
    change q t < 1
    exact (early_bound amplitude ht (by linarith)).trans_lt (by norm_num)
  have active := ready.raw
  have otherRaw := ready.otherRaw
  have mainBelow (i : Fin 1) : s.x i .q < 1 := by
    rw [Subsingleton.elim i 0, ready.charge]
    norm_num
  have auxBelow (i : Fin 1) (q : Port) : s.x i (.m q) < 1 := by
    have h := (ready.rest i q).2
    linarith
  obtain ⟨f⟩ := first_input_mark_of_response_margin_until_exists s box 0 p
    ready.main ready.aux active otherRaw mainBelow auxBelow earlyStock (ready.rest 0 p) (by simp [ready.empty])
  obtain ⟨g⟩ := f.first_silent_of_response_margin_until_exists box earlyStock (by simp [ready.empty])
  have firstBelow : ∀ t ∈ Ico time (time + f.latency), f.flow.path t 0 .q < level := by
    intro t ht
    have he := f.flow.ready_single_pulse_solution 0 p s.time (ready.main 0) active
      (fun port h => otherRaw 0 port (Or.inr h)) (by rw [ready.aux]; decide) t ⟨ht.1, ht.2.le⟩
    rw [he, ready.charge]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    change readyPulse (1 / 10) G time t < level
    exact hEarly t ht.1 (by linarith [ht.2, f.deadline])
  have secondBelow : ∀ t ∈ Ico f.final.time g.final.time, g.flow.path t 0 .q < level := by
    intro t ht
    have ha : f.final.aux 0 p = .mark := by simp [FirstInputMark.final, setAux]
    have he := g.flow.ready_single_pulse_solution 0 p s.time (f.main_ready 0) f.raw_active
      (fun port h => f.raw_other 0 port (Or.inr h)) (by rw [ha]; decide) t ⟨ht.1, ht.2.le⟩
    rw [he]
    have restart := f.protected_response_restart t
    change readyPulse (f.final.x 0 .q)
      (Real.exp (f.final.x 0 (.z p)) * Real.exp (-a * (f.final.time - s.time))) f.final.time t = readyPulse (s.x 0 .q) G time t at restart
    rw [ready.charge] at restart
    rw [restart]
    have start : time + f.latency ≤ t := ht.1
    have stop : t < f.silentDate := ht.2
    have sensorDeadline : f.silentDate < time + 1 / 20 := g.deadline
    exact hEarly t (by linarith [f.early]) (by linarith)
  have gAfter : time ≤ g.final.time := by
    have h := g.flow.positive
    change time + f.latency < g.final.time at h
    linarith [f.early]
  have gBefore : g.final.time < time + 1 / 20 := g.deadline
  have chosen : ∃ stop : ℝ,
      g.final.time < stop ∧ stop ≤ time + 9 / 10 ∧
      (∀ t ∈ Ico time stop, q t < level) ∧
      (if high then time + 3 / 10 < stop ∧ stop < time + 9 / 10 ∧ q stop = level ∧ 0 < deriv q stop
        else stop = time + 9 / 10 ∧ q stop < level) := by
    cases high
    · have bound : G ≤ 6 / 5 := gain
      have below (t : ℝ) (ht : time ≤ t) : q t < level := by
        have h := readyPulse_uniform_bound (initial := (1 / 10 : ℝ)) (amplitude := G)
          (Q := 1 / 10) (G := 6 / 5) le_rfl le_rfl bound (by norm_num) ht
        change q t ≤ _ at h
        linarith [threshold.1]
      exact ⟨time + 9 / 10, by linarith, le_rfl, fun t ht => below t ht.1, rfl,
        below _ (by linarith)⟩
    · have strong : 2 ≤ G := gain.1
      have above : level < q (time + 9 / 10) := threshold.2.trans_lt (strong_deadline strong)
      have continuous : Continuous q :=
        continuous_iff_continuousAt.mpr (fun t => (readyPulse_derivative _ _ _ t).continuousAt)
      obtain ⟨stop, start, deadline, hit, prior⟩ := scalar_first_crossing continuous
        (show time < time + 9 / 10 by linarith) (hEarly time le_rfl (by linarith)) above
      have late : time + 3 / 10 < stop := by
        by_contra h
        exact (ne_of_lt (hEarly stop start.le (le_of_not_gt h))) hit
      have slope : 0 < deriv q stop := readyPulse_transversal_of_later_value
        (by linarith : 0 ≤ G) deadline (by change q stop < q (time + 9 / 10); rw [hit]; exact above)
      exact ⟨stop, by linarith, deadline.le, prior, late, deadline, hit, slope⟩
  obtain ⟨stop, later, limit, prior, answer⟩ := chosen
  let path := readyProtectedValues θ g.final 0 p .silent (some time)
  have live : stop < time + 1 := by linarith
  have qPath (t : ℝ) : path t 0 .q = q t := by
    simp only [path, readyProtectedValues, protectedRawAmplitude, ite_true]
    rw [g.response_restart t, ready.charge]
  have rhs (t : ℝ) (ht : t ∈ Icc g.final.time stop) (i : Fin 1) (c : Coord) :
      field θ g.final (path t) t i c = readyProtectedRhs θ g.final 0 p .silent (some time) t i c :=
    readyProtected_field g.final 0 p .silent (some time) (Or.inr rfl)
      g.main_ready g.aux_silent g.aux_other g.raw_active g.raw_other t ht.1
      (fun origin h => by obtain rfl := Option.some.inj h; exact ⟨gAfter, ht.2.trans_lt live⟩) i c
  have sensor (t : ℝ) (ht : t ∈ Icc g.final.time stop) : auxiliaryGuards g.final (path t) := by
    intro i port
    by_cases h : i = 0 ∧ port = p
    · rcases h with ⟨rfl, rfl⟩
      rw [g.aux_silent]
      change 1 / 10 < path t 0 (.m p)
      simp only [path, readyProtectedValues, protectedReadyRate, and_self, ite_true]
      rw [g.sensor_charge]
      have hp := (box.rates_positive 0 p).2.1
      have decay := silent_full_decay_end (start := g.final.time) (ne_of_gt hp)
      rw [← decay]
      apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) (by norm_num)
      have last := (g.errorDate_bounds box).1
      change time + 99 / 100 < g.final.time + Real.log 8 / (θ 0).ls p at last
      have earlier : t < g.final.time + Real.log 8 / (θ 0).ls p := by linarith [ht.2]
      nlinarith [mul_pos hp (sub_pos.mpr earlier)]
    · have other : i ≠ 0 ∨ port ≠ p := by tauto
      rw [g.aux_other i port other]
      change (if i = 0 ∧ port = p then _ else _) < 1
      rw [ite_eq_right h]
      exact relax_lt (by norm_num) ht.1 (g.aux_below i port other) (by norm_num)
  have physicalLeg : TolerantLeg θ g.final p time level stop := by
    refine ⟨later, ⟨gAfter, live⟩, g.queue_preserved.trans ready.empty, ?_, ?_, ?_, ?_, sensor⟩
    · dsimp only
      intro t ht i c
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun v _ => readyProtectedValues_derivative (θ := θ) g.final 0 p .silent (some time) v i c)
        ((readyProtectedRhs_continuous (θ := θ) g.final 0 p .silent (some time) i c).intervalIntegrable g.final.time t)
      rw [readyProtectedValues_initial] at h
      have integralEq : (∫ v in g.final.time..t, field θ g.final (path v) v i c) =
          ∫ v in g.final.time..t, readyProtectedRhs θ g.final 0 p .silent (some time) v i c := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.1
        intro v hv
        exact rhs v ⟨hv.1.le, hv.2.le.trans ht.2⟩ i c
      change path t i c = _
      rw [integralEq, h]
      ring
    · intro i c
      exact continuous_iff_continuousAt.mpr fun t =>
        (readyProtectedValues_derivative (θ := θ) g.final 0 p .silent (some time) t i c).continuousAt
    · dsimp only
      intro i c
      apply ((readyProtectedRhs_continuous (θ := θ) g.final 0 p .silent (some time) i c).intervalIntegrable _ _).congr_uIoo
      intro t ht
      rw [uIoo_of_lt later] at ht
      exact (rhs t ⟨ht.1.le, ht.2.le⟩ i c).symm
    · intro t ht
      change path t 0 .q < level
      rw [qPath]
      exact prior t ⟨gAfter.trans ht.1, ht.2⟩
  refine ⟨⟨physical, f, g, firstBelow, secondBelow, stop, physicalLeg, prior, qPath stop, ?_⟩⟩
  cases high
  · exact ⟨answer.1, (qPath stop).trans_lt answer.2⟩
  · obtain ⟨early, late, hit, slope⟩ := answer
    refine ⟨early, late, (qPath stop).trans hit, ?_⟩
    change 0 < field θ g.final (path stop) stop 0 .q
    rw [rhs stop ⟨later.le, le_rfl⟩]
    have derivative := (readyProtectedValues_derivative (θ := θ) g.final 0 p .silent (some time) stop 0 .q).deriv
    rw [show (fun t => path t 0 .q) = q from funext qPath] at derivative
    exact derivative ▸ slope

/-- The stop is determined by the first crossing or the quiet deadline.
This compares certificates for the same one-shot task, including its
fixed realized threshold and gain. -/
theorem TolerantSnapshotDecision.stop_unique {θ s port high level}
    (a b : TolerantSnapshotDecision θ s port high level) : a.stop = b.stop := by
  cases high
  · exact a.outcome.1.trans b.outcome.1.symm
  · apply le_antisymm
    · by_contra h
      have below := a.scalar_guard b.stop ⟨by linarith [b.outcome.1], lt_of_not_ge h⟩
      have hit := b.charge.symm.trans b.outcome.2.2.1
      exact (ne_of_lt below) hit
    · by_contra h
      have below := b.scalar_guard a.stop ⟨by linarith [a.outcome.1], lt_of_not_ge h⟩
      have hit := a.charge.symm.trans a.outcome.2.2.1
      exact (ne_of_lt below) hit

theorem TolerantPortDecision.stop_unique {θ time gains port high level}
    (a b : TolerantPortDecision θ time gains port high level) : a.stop = b.stop :=
  TolerantSnapshotDecision.stop_unique a b

/-- The classifier of the original two-port experiment. -/
abbrev TolerantDecision (θ : Fin 1 → Parameters) (time : ℝ) (gains : Port → ℝ)
    (high : Bool) (level : ℝ) := TolerantPortDecision θ time gains (tolerancePort high) high level

noncomputable abbrev toleranceStart (time : ℝ) (gains : Port → ℝ) (high : Bool) :=
  toleranceStartOn time gains (tolerancePort high)

/-- Read a specified physical port. The output bit is certified from its
gain band, so the same port can be tested at two different gain states. -/
theorem tolerant_port_readout {θ ε time gains port high level} (box : @PhysicalBox 1 θ ε)
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (gain : if high then 2 ≤ Real.exp (gains port) ∧ Real.exp (gains port) ≤ 12 / 5
      else Real.exp (gains port) ≤ 6 / 5)
    (other : ∀ p, p ≠ port → Real.exp (gains p) ≤ 18 / 5) :
    Nonempty (TolerantPortDecision θ time gains port high level) := by
  apply tolerant_snapshot_readout box (physical := ?_) (ready := ?_) threshold gain
  swap
  · refine ⟨fun _ => rfl, rfl, fun _ _ => rfl, ?_, ?_, ?_, rfl⟩
    · intro i p
      norm_num [RestBand, toleranceStartOn]
    · simp [toleranceStartOn]
    · intro i p h
      have eq : i = 0 := Subsingleton.elim _ _
      simp [eq, toleranceStartOn] at h ⊢
      exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    norm_num [toleranceStartOn, auxUpper]
  · intro i p
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have cap : (18 / 5 : ℝ) ≤ (θ 0).cap p := by
      have h := (box.2 0 p).1.1
      change 4 * (1 - ε) ≤ (θ 0).cap p at h
      linarith [box.epsilon_bounds.2]
    change gains p ≤ Real.log ((θ 0).cap p)
    apply Real.exp_le_exp.mp
    rw [Real.exp_log (box.cap_positive 0 p)]
    apply le_trans ?_ cap
    by_cases eq : p = port
    · subst p
      cases high
      · exact (show Real.exp (gains port) ≤ 6 / 5 from gain).trans (by norm_num)
      · exact (show Real.exp (gains port) ≤ 12 / 5 from gain.2).trans (by norm_num)
    · exact other p eq
  · intro i
    norm_num [toleranceStartOn]
  · intro i
    norm_num [toleranceStartOn]

/-- Distinguish which of the two ports received one canonical input pulse. -/
theorem tolerant_two_port_readout {θ ε time gains level} (box : @PhysicalBox 1 θ ε)
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (weak : Real.exp (gains 0) ≤ 6 / 5)
    (strong : 2 ≤ Real.exp (gains 1) ∧ Real.exp (gains 1) ≤ 12 / 5)
    (unused : Real.exp (gains 2) ≤ 18 / 5) :
    ∀ high, Nonempty (TolerantDecision θ time gains high level) := by
  intro high
  apply tolerant_port_readout box threshold
  · cases high
    · exact weak
    · exact strong
  · intro p hp
    cases high <;> fin_cases p <;> simp [tolerancePort] at hp ⊢
    · exact strong.2.trans (by norm_num)
    · exact unused
    · exact weak.trans (by norm_num)
    · exact unused

/-- At level one the entire prefix, including the output event, is
an execution in the original kernel. -/
noncomputable def TolerantSnapshotDecision.nominalExecution {θ s port high}
    (run : TolerantSnapshotDecision θ s port high 1) :
    Execution θ (fun _ _ => []) s run.final := by
  let p := port
  let sensor := run.silent
  let last := readyProtectedEnd θ sensor.final 0 p .silent (some s.time) run.stop
  let flow : Flow θ sensor.final last :=
    readyProtectedFlow sensor.final 0 p .silent (some s.time) run.leg.positive (Or.inr rfl)
      sensor.main_ready sensor.aux_silent sensor.aux_other sensor.raw_active sensor.raw_other
      (fun o h => by
        obtain rfl := Option.some.inj h
        exact ⟨run.leg.live.1, run.leg.live.2.le⟩)
      sensor.main_below sensor.aux_below
      (fun t ht => by
        have h := run.leg.main_guard t ht
        simpa only [readyProtectedValues, protectedRawAmplitude, ite_true] using h)
      (fun t ht => by
        have h := run.leg.aux_guards t ⟨ht.1, ht.2.le⟩ 0 p
        rw [sensor.aux_silent] at h
        change (1 / 10 : ℝ) < readyProtectedValues θ sensor.final 0 p .silent (some s.time) t 0 (.m p) at h
        simpa only [readyProtectedValues, protectedReadyRate, and_self, ite_true, reduceCtorEq, ite_false] using h)
      (fun d hd => by rw [run.leg.empty] at hd; exact (List.not_mem_nil hd).elim)
  let before := (sensor.execution (fun _ _ => [])).append (.cons (.flow flow) (.nil _))
  cases high
  · exact before
  · have fire : Jump (fun _ _ => []) last run.final := by
      simpa [TolerantSnapshotDecision.final, last, setMain] using
        (Jump.fire (route := fun _ _ => []) last 0 (sensor.main_ready 0) run.outcome.2.2.1)
    exact before.append (.cons (.jump fire) (.nil _))

noncomputable abbrev TolerantPortDecision.nominalExecution {θ time gains port high}
    (run : TolerantPortDecision θ time gains port high 1) :
    Execution θ (fun _ _ => []) (toleranceStartOn time gains port) run.final :=
  TolerantSnapshotDecision.nominalExecution run

namespace TolerantDecision

noncomputable abbrev final {θ time gains high level}
    (run : TolerantDecision θ time gains high level) : Snapshot 1 :=
  TolerantPortDecision.final run

theorem stop_unique {θ time gains high level}
    (a b : TolerantDecision θ time gains high level) : a.stop = b.stop :=
  TolerantPortDecision.stop_unique a b

noncomputable abbrev nominalExecution {θ time gains high}
    (run : TolerantDecision θ time gains high 1) :
    Execution θ (fun _ _ => []) (toleranceStart time gains high) run.final :=
  TolerantPortDecision.nominalExecution run

end TolerantDecision

end RecursiveLearning.Native
