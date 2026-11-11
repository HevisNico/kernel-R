import Driven

/-! A read of several trained ports at once. The pulses arrive at the
same instant, the cell fires once, and it returns to rest with no gain
changed. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- The thresholds of the cell that do not depend on the pulsed port. -/
structure CellConfig (θ : Fin 1 → Parameters) (level : ℝ) : Prop where
  fire : (θ 0).thresholds.fire = level
  fastEnd : (θ 0).thresholds.fastEnd = 1 / 4
  reopen : (θ 0).thresholds.reopen = 1 / 10
  mark : ∀ q, (θ 0).thresholds.mark q = 1
  silent : ∀ q, (θ 0).thresholds.silent q = 4 / 5
  ordered : ∀ q, 0 < (θ 0).thresholds.auxReady q ∧
    (θ 0).thresholds.auxReady q ≤ (θ 0).thresholds.error q ∧ (θ 0).thresholds.error q < 1

theorem PortConfig.cell {θ : Fin 1 → Parameters} {p upper lower level}
    (c : PortConfig θ p upper lower level) : CellConfig θ level :=
  ⟨c.fire, c.fastEnd, c.reopen, c.mark, c.silent, c.ordered⟩

theorem cell_threshold_bounds {θ : Fin 1 → Parameters} {level : ℝ} (config : CellConfig θ level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20) : ParameterThresholdBounds θ := by
  constructor
  · intro i
    rw [Subsingleton.elim i 0, config.fire]
    linarith [fire.2]
  · intro i
    rw [Subsingleton.elim i 0, config.fastEnd]
    norm_num
  · intro i
    rw [Subsingleton.elim i 0, config.fastEnd, config.fire]
    linarith [fire.1]
  · intro i
    rw [Subsingleton.elim i 0, config.reopen]
    norm_num
  · intro i q
    rw [Subsingleton.elim i 0, config.mark]
    norm_num
  · intro i q
    rw [Subsingleton.elim i 0, config.silent]
    norm_num
  · intro i q
    rw [Subsingleton.elim i 0]
    linarith [(config.ordered q).1, (config.ordered q).2.1]
  · intro i q
    rw [Subsingleton.elim i 0]
    exact (config.ordered q).1.le

theorem cell_guards_rest {θ : Fin 1 → Parameters} {level : ℝ} (config : CellConfig θ level)
    {s : Snapshot 1} {x : Values 1} (main : s.main 0 = .ready) (charge : x 0 .q < level)
    (aux : ∀ q, s.aux 0 q = .ready) (sensors : ∀ q, x 0 (.m q) < 1) :
    ThresholdGuards (fun i => (θ i).thresholds) s x := by
  constructor
  · intro i
    rw [Subsingleton.elim i 0]
    simpa [main, config.fire] using charge
  · intro i q
    rw [Subsingleton.elim i 0]
    simpa [aux q, config.mark] using sensors q

/-- An execution of the single cell from `s` to `u` whose FIRE events
are exactly the listed ones, with their dates. -/
def Emits (θ : Fin 1 → Parameters) (s u : Snapshot 1) (events : List (Fin 1 × ℝ)) : Prop :=
  ∃ e : ParameterExecution θ (fun _ _ => []) s u, e.emissions = events

theorem Runs.emits {θ : Fin 1 → Parameters} {s u : Snapshot 1} (h : Runs θ s u 0) :
    Emits θ s u [] := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, List.length_eq_zero_iff.mp he⟩

theorem Emits.append {θ : Fin 1 → Parameters} {s u v : Snapshot 1} {l l' : List (Fin 1 × ℝ)}
    (first : Emits θ s u l) (second : Emits θ u v l') : Emits θ s v (l ++ l') := by
  obtain ⟨e, he⟩ := first
  obtain ⟨f, hf⟩ := second
  exact ⟨e.append f, by rw [execution_emissions_append, he, hf]⟩

theorem Emits.jump {θ : Fin 1 → Parameters} {s u : Snapshot 1}
    (j : ParameterJump θ (fun _ _ => []) s u) : Emits θ s u j.emissions :=
  ⟨.cons (.jump j) (.nil _), by simp [ParameterExecution.emissions]⟩

/-- A sensor at the FIRE: idle at rest, or SILENT under a pulse that
started at `o`, no earlier than `D`, on a port whose ERROR entry
threshold is low. `S` is the date at which it entered SILENT. -/
def FiredPort (θ : Fin 1 → Parameters) (e : Snapshot 1) (D : ℝ) (q : Port) : Prop :=
  (e.aux 0 q = .ready ∧ e.raw 0 q = none ∧ RestBand (e.x 0 (.m q))) ∨
  (e.aux 0 q = .silent ∧
    7 / 100 ≤ (θ 0).thresholds.error q ∧ (θ 0).thresholds.error q ≤ 2 / 25 ∧
    1 / 200 ≤ (θ 0).thresholds.auxReady q ∧
    (θ 0).thresholds.auxReady q < (θ 0).thresholds.error q ∧
    ∃ o S, e.raw 0 q = some o ∧ D ≤ o ∧ o ≤ S ∧ S < D + 1 / 2 ∧ o ≤ e.time ∧ e.time ≤ o + 1 ∧
      e.x 0 (.m q) = (4 / 5) * Real.exp (-(θ 0).ls q * (e.time - S)))

/-- The FIRE and the return to rest, with any number of SILENT sensors.
The cell is READY with its main charge at the FIRE level. It fires once,
goes through its refractory period while the busy sensors complete their
cycle, and ends at rest with every gain unchanged. -/
theorem fire_rest_exists {θ ε} {e : Snapshot 1} {level rest D : ℝ} (box : @PhysicalBox 1 θ ε)
    (cell : CellConfig θ level) (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (inv : ParameterPhysicalInvariant θ e) (main : e.main 0 = .ready)
    (charge : e.x 0 .q = level) (recovery : 7 / 100 ≤ e.x 0 .b ∧ e.x 0 .b ≤ 1 / 10)
    (date : D ≤ e.time ∧ e.time ≤ D + 1) (ports : ∀ q, FiredPort θ e D q)
    (wait : D + 22 ≤ rest) (pending : ∀ d ∈ e.pending, rest ≤ d.due) :
    ∃ u, Emits θ e u [(0, e.time)] ∧ RestState θ u ∧ u.time = rest ∧ u.pending = e.pending ∧
      (∀ q, u.x 0 (.z q) = e.x 0 (.z q)) ∧ u.x 0 .b = e.x 0 .b ∧ u.x 0 .q = 1 / 10 := by
  let fired : Snapshot 1 := { (setMain e 0 .fast) with
    pending := e.pending ++ (fun (_ : Fin 1) (_ : ℝ) => ([] : List (Delivery 1))) 0 e.time }
  let fireJump : ParameterJump θ (fun _ _ => []) e fired :=
    .fire e 0 main (by rw [cell.fire]; exact charge)
  have firedMain : fired.main 0 = .fast := by simp [fired, setMain]
  have firedPending : ∀ v ∈ fired.pending, v ∈ e.pending := by
    intro v hv
    have hv' : v ∈ e.pending ++ ([] : List (Delivery 1)) := hv
    simpa using hv'
  -- A busy sensor is above its ERROR entry threshold and reopens after its pulse.
  have busy (q : Port) (hs : e.aux 0 q = .silent) :
      (∃ o, e.raw 0 q = some o ∧ o ≤ e.time ∧ e.time ≤ o + 1 ∧ o + 1 < sensorReady θ fired q) ∧
      (θ 0).thresholds.error q ≤ e.x 0 (.m q) ∧ sensorReady θ fired q < D + 5 / 2 ∧
      1 / 200 ≤ (θ 0).thresholds.auxReady q ∧ (θ 0).thresholds.auxReady q < 2 / 25 := by
    rcases ports q with ⟨hr, _, _⟩ | ⟨_, lo, hi, floor, below, o, S, raw, s₀, s₁, s₂, s₃, s₄, value⟩
    · rw [hr] at hs; cases hs
    · have rp : 0 < (θ 0).ls q := (box.rates_positive 0 q).2.1
      obtain ⟨long, short⟩ := low_entry_silent_duration box q ⟨lo, hi⟩
      have long' : 1 < decayTime (4 / 5) ((θ 0).thresholds.error q) ((θ 0).ls q) := long
      have short' : decayTime (4 / 5) ((θ 0).thresholds.error q) ((θ 0).ls q) ≤ 31 / 20 := short
      have errT := error_duration_bound box q ⟨floor, below, hi⟩
      have epos : 0 < (θ 0).thresholds.error q := by linarith
      have shift : decayTime (e.x 0 (.m q)) ((θ 0).thresholds.error q) ((θ 0).ls q) =
          decayTime (4 / 5) ((θ 0).thresholds.error q) ((θ 0).ls q) - (e.time - S) := by
        rw [value]
        exact decayTime_shift (by norm_num) epos rp _
      have readyEq : sensorReady θ fired q =
          S + decayTime (4 / 5) ((θ 0).thresholds.error q) ((θ 0).ls q) +
            decayTime ((θ 0).thresholds.error q) ((θ 0).thresholds.auxReady q) ((θ 0).le q) := by
        rw [sensorReady_silent (s := fired) hs, sensorNext_silent (s := fired) hs]
        show e.time + decayTime (e.x 0 (.m q)) _ _ + _ = _
        rw [shift]
        ring
      refine ⟨⟨o, raw, s₃, s₄, by rw [readyEq]; linarith [errT.1]⟩, ?_, ?_, floor, by linarith⟩
      · rw [value]
        exact (decay_above (by norm_num) epos rp (by linarith [date.2])).le
      · rw [readyEq]; linarith [errT.2]
  have idle (q : Port) (hr : e.aux 0 q = .ready) : e.raw 0 q = none ∧ RestBand (e.x 0 (.m q)) := by
    rcases ports q with ⟨_, raw, band⟩ | ⟨hs, _⟩
    · exact ⟨raw, band⟩
    · rw [hs] at hr; cases hr
  have modes (q : Port) : e.aux 0 q = .ready ∨ e.aux 0 q = .silent := by
    rcases ports q with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have sched : Scheduled θ fired := {
    refractory := ⟨by rw [firedMain]; decide,
      fun q => by
        show e.aux 0 q ≠ .mark
        rcases modes q with h | h <;> rw [h] <;> decide,
      fun q hr => (idle q hr).1⟩
    main_levels := by rw [cell.reopen, cell.fastEnd]; norm_num
    levels := fun q => ⟨(cell.ordered q).1, (cell.ordered q).2.1, (cell.ordered q).2.2,
      (cell.mark q).ge⟩
    recovery := by
      show 0 < e.x 0 .b
      linarith [recovery.1]
    fast := fun _ => by
      rw [cell.fastEnd]
      show 1 / 4 ≤ e.x 0 .q
      rw [charge]
      linarith [fire.1]
    slow := fun h => by rw [firedMain] at h; cases h
    ready := fun q hr => lt_of_le_of_lt (idle q hr).2.2 (by norm_num)
    silent := fun q hs => (busy q hs).2.1
    error := fun q hr => by
      have hr' : e.aux 0 q = .error := hr
      rcases modes q with h | h <;> rw [h] at hr' <;> cases hr'
    raw := fun q o h => by
      have h' : e.raw 0 q = some o := h
      rcases modes q with hm | hm
      · rw [(idle q hm).1] at h'; cases h'
      · obtain ⟨o', raw, lo, hi, _⟩ := (busy q hm).1
        rw [raw] at h'
        obtain rfl := Option.some.inj h'
        exact ⟨lo, hi⟩ }
  have fastT := fast_duration_bound fire
  have slowT := slow_duration_bound recovery
  have reopenEq : mainReopen θ fired =
      e.time + decayTime level (1 / 4) a + decayTime (1 / 4) (1 / 10) (e.x 0 .b) := by
    rw [mainReopen_fast firedMain, mainNext_fast firedMain, cell.fastEnd, cell.reopen]
    show e.time + decayTime (e.x 0 .q) _ _ + _ = _
    rw [charge]
    rfl
  have ord : Ordered θ fired := {
    sensor := fun q hq => by
      have hs : e.aux 0 q = .silent := (modes q).resolve_left hq
      rw [reopenEq]
      linarith [(busy q hs).2.2.1, fastT.1, slowT.1, date.1]
    raw := fun q o h => by
      have h' : e.raw 0 q = some o := h
      rcases modes q with hm | hm
      · rw [(idle q hm).1] at h'; cases h'
      · obtain ⟨o', raw, lo, hi, after⟩ := (busy q hm).1
        rw [raw] at h'
        obtain rfl := Option.some.inj h'
        rw [reopenEq]
        exact ⟨by linarith [fastT.1, slowT.1], after⟩
    pending := fun v hv => by
      rw [reopenEq]
      have h := pending v (firedPending v hv)
      linarith [fastT.2, slowT.2, date.2] }
  obtain ⟨u₁, run, fin⟩ := refractory_run_exists box fired sched ord
  have time₁ : u₁.time = mainReopen θ fired := fin.time
  have charge₁ : u₁.x 0 .q = 1 / 10 := fin.charge.trans cell.reopen
  have reopenLate : mainReopen θ fired < rest := by
    rw [reopenEq]
    linarith [fastT.2, slowT.2, date.2]
  have firedBefore : fired.time ≤ mainReopen θ fired :=
    (sched.dates box).1.trans (sched.dates box).2.1
  have sensor₁ (q : Port) : u₁.x 0 (.m q) < 1 := by
    rw [fin.sensors q]
    rcases modes q with hm | hm
    · rw [restSensor_ready (s := fired) hm]
      exact lt_of_le_of_lt (relax_restBand firedBefore (idle q hm).2).2 (by norm_num)
    · rw [restSensor_busy (s := fired) (show fired.aux 0 q ≠ .ready by
        show e.aux 0 q ≠ .ready; rw [hm]; decide)]
      exact relax_lt_one (ord.sensor q (by show e.aux 0 q ≠ .ready; rw [hm]; decide)).le
        (by linarith [(busy q hm).2.2.2.2])
  let u := quietAt u₁ rest
  have stopRest : u₁.time < rest := by rw [time₁]; exact reopenLate
  have waitFlow : ParameterFlow θ u₁ u := {
    toFlowDynamics := quietDynamics u₁ stopRest
      (fun i => by rw [Subsingleton.elim i 0]; exact fin.main)
      (fun i q => by rw [Subsingleton.elim i 0]; exact fin.aux q)
      (fun i q => by rw [Subsingleton.elim i 0]; exact fin.raw q)
      (fun v hv => pending v (firedPending v (fin.queue ▸ hv)))
    guards := by
      intro t ht
      have ht₁ : u₁.time ≤ t := ht.1
      apply cell_guards_rest cell fin.main _ fin.aux
      · intro q
        exact relax_lt_one ht₁ (sensor₁ q)
      · change relax (1 / 2) (1 / 10) (u₁.x 0 .q) u₁.time t < level
        rw [charge₁]
        have flat : relax (1 / 2) (1 / 10) (1 / 10) u₁.time t = 1 / 10 := by simp [relax]
        rw [flat]
        linarith [fire.1] }
  have uCharge : u.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (u₁.x 0 .q) u₁.time rest = 1 / 10
    rw [charge₁]
    simp [relax]
  have uSensors (q : Port) : RestBand (u.x 0 (.m q)) := by
    change RestBand (relax (1 / 2) (1 / 40) (u₁.x 0 (.m q)) u₁.time rest)
    rw [fin.sensors q, time₁]
    rcases modes q with hm | hm
    · rw [restSensor_ready (s := fired) hm, relax_relax]
      exact relax_restBand (show e.time ≤ rest by linarith [date.2]) (idle q hm).2
    · have ne : fired.aux 0 q ≠ .ready := by show e.aux 0 q ≠ .ready; rw [hm]; decide
      obtain ⟨_, _, early, floor, ceil⟩ := busy q hm
      rw [restSensor_busy (s := fired) ne, relax_relax]
      have longWait : Real.exp (-(1 / 2) * (rest - sensorReady θ fired q)) ≤ 1 / 9500 :=
        (Real.exp_le_exp.mpr (by linarith)).trans exp_neg_long_wait
      have pos := Real.exp_pos (-(1 / 2) * (rest - sensorReady θ fired q))
      have hi := mul_le_mul (show (θ 0).thresholds.auxReady q - 1 / 40 ≤ 11 / 200 by linarith)
        longWait pos.le (by norm_num)
      have lo := mul_le_mul (show 1 / 40 - (θ 0).thresholds.auxReady q ≤ 11 / 200 by linarith)
        longWait pos.le (by norm_num)
      refine ⟨?_, ?_⟩ <;> dsimp only [relax] <;> linarith
  have counted : Emits θ e u [(0, e.time)] :=
    (Emits.jump fireJump).append (run.append (Runs.flow waitFlow)).emits
  obtain ⟨whole, _⟩ := id counted
  have final := ParameterExecution.physical_invariant whole (cell_threshold_bounds cell fire) box inv
  have uB : u.x 0 .b = e.x 0 .b := fin.recovery
  have uGains (q : Port) : u.x 0 (.z q) = e.x 0 (.z q) := fin.gains q
  refine ⟨u, counted, ⟨fin.main, fin.aux, fin.raw, ⟨uCharge.ge, uCharge.le.trans (by norm_num)⟩,
    uSensors, ?_, final.reserve 0, ?_⟩, rfl, ?_, uGains, uB, uCharge⟩
  · rw [uB]
    exact ⟨by linarith [recovery.1], by linarith [recovery.2]⟩
  · intro q
    rw [uGains q]
    exact inv.gain 0 q
  · show u₁.pending = e.pending
    rw [fin.queue]
    show e.pending ++ ([] : List (Delivery 1)) = e.pending
    simp

theorem readyPulse_add (initial g₁ g₂ start t : ℝ) :
    readyPulse initial (g₁ + g₂) start t =
      readyPulse initial g₁ start t + g₂ * response (t - start) := by
  unfold readyPulse
  ring

/-- The main charge under a pulse at gain `g₁` from `D₁` and a pulse at
gain `g₂` from `D₂`, after `D₂`. -/
noncomputable def jointCharge (q₀ g₁ g₂ D₁ D₂ t : ℝ) : ℝ :=
  readyPulse q₀ g₁ D₁ t + g₂ * response (t - D₂)

/-- A read of two ports as an execution. The pulse on the second port
arrives up to a quarter of a unit after the first. If the first pulse
alone stays below the FIRE level until the second arrives, and the two
together reach it later than 1/20 after the second, the cell fires
exactly once, at the first contact, and returns to rest with every gain
and the recovery rate unchanged. -/
theorem staggered_read_exists {θ ε p₁ p₂ u₁ l₁ u₂ l₂ level rest D₂} {s : Snapshot 1}
    {later : List (Delivery 1)} (box : @PhysicalBox 1 θ ε) (distinct : p₁ ≠ p₂)
    (config₁ : PortConfig θ p₁ u₁ l₁ level) (config₂ : PortConfig θ p₂ u₂ l₂ level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry₁ : 7 / 100 ≤ u₁ ∧ u₁ ≤ 2 / 25) (exit₁ : 1 / 200 ≤ l₁ ∧ l₁ < u₁)
    (entry₂ : 7 / 100 ≤ u₂ ∧ u₂ ≤ 2 / 25) (exit₂ : 1 / 200 ≤ l₂ ∧ l₂ < u₂)
    (state : RestState θ s) (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending =
      (⟨0, p₁, s.time⟩ : Delivery 1) :: (⟨0, p₂, D₂⟩ : Delivery 1) :: later)
    (order : s.time ≤ D₂ ∧ D₂ ≤ s.time + 1 / 4)
    (wait : s.time + 22 ≤ rest) (laterDue : ∀ d ∈ later, rest ≤ d.due)
    (alone : ∀ t ∈ Ico s.time D₂,
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p₁))) s.time t < level)
    (quiet : ∀ t ∈ Icc D₂ (D₂ + 1 / 20), jointCharge (s.x 0 .q) (Real.exp (s.x 0 (.z p₁)))
      (Real.exp (s.x 0 (.z p₂))) s.time D₂ t < level)
    (fires : ∃ t ∈ Icc D₂ (s.time + 1), level ≤ jointCharge (s.x 0 .q)
      (Real.exp (s.x 0 (.z p₁))) (Real.exp (s.x 0 (.z p₂))) s.time D₂ t) :
    ∃ u tf, Emits θ s u [(0, tf)] ∧ D₂ + 1 / 20 < tf ∧ tf ≤ s.time + 1 ∧
      jointCharge (s.x 0 .q) (Real.exp (s.x 0 (.z p₁))) (Real.exp (s.x 0 (.z p₂)))
        s.time D₂ tf = level ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = later ∧
      (∀ q, u.x 0 (.z q) = s.x 0 (.z q)) ∧ u.x 0 .b = s.x 0 .b ∧ u.x 0 .q = 1 / 10 := by
  let G₁ := Real.exp (s.x 0 (.z p₁))
  let G₂ := Real.exp (s.x 0 (.z p₂))
  let joint := fun t => jointCharge (s.x 0 .q) G₁ G₂ s.time D₂ t
  have jointCont : Continuous joint := by
    dsimp only [joint, jointCharge, readyPulse, response]
    fun_prop
  obtain ⟨t₁, ht₁, high⟩ := fires
  obtain ⟨tf, after, before, hit, first⟩ := first_hit jointCont ht₁.1
    (quiet D₂ ⟨le_rfl, by linarith⟩) high
  have late : D₂ + 1 / 20 < tf := by
    by_contra h
    have bound := quiet tf ⟨after.le, not_lt.mp h⟩
    have same : joint tf = level := hit
    have bound' : joint tf < level := bound
    linarith
  have tfLe : tf ≤ s.time + 1 := before.trans ht₁.2
  let K := s.time + 1
  -- The first admission.
  let a₁ : Snapshot 1 := { (setRaw s 0 p₁ (some s.time)) with
    pending := [] ++ ((⟨0, p₂, D₂⟩ : Delivery 1) :: later) }
  let jump₁ : ParameterJump θ (fun _ _ => []) s a₁ :=
    .arrive s ⟨0, p₁, s.time⟩ [] ((⟨0, p₂, D₂⟩ : Delivery 1) :: later) queue rfl (state.raw p₁)
  have raw₁ : a₁.raw 0 p₁ = some s.time := by simp [a₁, setRaw]
  have rawRest (q : Port) (h : q ≠ p₁) : a₁.raw 0 q = none :=
    (raw_update_other s 0 p₁ (some s.time) 0 q (Or.inr h)).trans (state.raw q)
  have aux₁ (q : Port) : a₁.aux 0 q = .ready := state.aux q
  have live₁ (q : Port) (h : a₁.raw 0 q ≠ none) : q = p₁ := by
    by_contra hn
    exact h (rawRest q hn)
  have scale₁ : rawScale a₁ p₁ = 1 := by
    show rawInputScale (a₁.raw 0 p₁) s.time = 1
    rw [raw₁]
    simp [rawInputScale]
  have amplitude₁ : drivenAmplitude a₁ = G₁ := by
    unfold drivenAmplitude
    rw [Finset.sum_eq_single p₁ (fun q _ hq => by rw [rawScale_none (rawRest q hq), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), scale₁, mul_one]
    rfl
  -- The planned MARK dates.
  obtain ⟨lat₁, early₁, quick₁, root₁, prior₁⟩ := box.first_sensor_crossing 0 p₁
    (state.sensors p₁).1 (state.sensors p₁).2 (start := s.time)
  let m₂ := relax (1 / 2) (1 / 40) (s.x 0 (.m p₂)) s.time D₂
  have band₂ : RestBand m₂ := relax_restBand order.1 (state.sensors p₂)
  obtain ⟨lat₂, early₂, quick₂, root₂, prior₂⟩ := box.first_sensor_crossing 0 p₂
    band₂.1 band₂.2 (start := D₂)
  let M : Port → ℝ := fun q => if q = p₁ then s.time + lat₁ else D₂ + lat₂
  have M₁ : M p₁ = s.time + lat₁ := by simp [M]
  have M₂ : M p₂ = D₂ + lat₂ := by simp [M, Ne.symm distinct]
  have markSpan (q : Port) : 0 ≤ decayTime 1 (4 / 5) ((θ 0).lm q) ∧
      decayTime 1 (4 / 5) ((θ 0).lm q) ≤ 1 / 45 := by
    have form : decayTime 1 (4 / 5) ((θ 0).lm q) = Real.log (5 / 4) / (θ 0).lm q := by
      unfold decayTime
      norm_num
    rw [form]
    exact ⟨(box.aux_durations_positive 0 q).1.le, box.mark_duration_upper 0 q⟩
  have errBand (q : Port) (hq : q = p₁ ∨ q = p₂) :
      7 / 100 ≤ (θ 0).thresholds.error q ∧ (θ 0).thresholds.error q ≤ 2 / 25 ∧
      1 / 200 ≤ (θ 0).thresholds.auxReady q ∧
      (θ 0).thresholds.auxReady q < (θ 0).thresholds.error q := by
    rcases hq with rfl | rfl
    · rw [config₁.error, config₁.auxReady]
      exact ⟨entry₁.1, entry₁.2, exit₁.1, exit₁.2⟩
    · rw [config₂.error, config₂.auxReady]
      exact ⟨entry₂.1, entry₂.2, exit₂.1, exit₂.2⟩
  have aboveK (q : Port) (hq : q = p₁ ∨ q = p₂) (S : ℝ) (hS : s.time ≤ S) :
      (θ 0).thresholds.error q < (4 / 5) * Real.exp (-(θ 0).ls q * (K - S)) := by
    obtain ⟨lo, hi, _, _⟩ := errBand q hq
    have long : 1 < decayTime (4 / 5) ((θ 0).thresholds.error q) ((θ 0).ls q) :=
      (low_entry_silent_duration box q ⟨lo, hi⟩).1
    apply decay_above (by norm_num) (by linarith) (box.rates_positive 0 q).2.1
    show s.time + 1 - S < _
    linarith
  have sensor₁ (t : ℝ) : drivenSensor θ a₁ p₁ t =
      auxPulse (s.x 0 (.m p₁)) ((θ 0).inputGain p₁) s.time t := by
    rw [drivenSensor_ready (aux₁ p₁), scale₁, mul_one]
    rfl
  have plan₁ : Plan θ a₁ M D₂ K level := {
    driven := ⟨state.main, fun q => by rw [aux₁ q]; decide⟩
    time := order.1
    horizon := by show D₂ ≤ s.time + 1; linarith [order.2]
    fire := config₁.fire
    mark := config₁.mark
    silent := config₁.silent
    charge := fun t ht => by
      rw [amplitude₁]
      exact alone t ht
    raw := fun q o h => by
      rw [live₁ q (by rw [h]; simp), raw₁] at h
      obtain rfl := Option.some.inj h
      exact ⟨le_rfl, by linarith [order.2]⟩
    pending := fun d hd => by
      have hd' : d ∈ (⟨0, p₂, D₂⟩ : Delivery 1) :: later := by simpa [a₁] using hd
      rcases List.mem_cons.mp hd' with rfl | h
      · exact le_rfl
      · have due := laterDue d h
        linarith [order.2]
    quiet := fun q _ _ => lt_of_le_of_lt (state.sensors q).2 (by norm_num)
    ready := fun q _ hr => by
      obtain rfl := live₁ q hr
      rw [M₁]
      exact ⟨by show s.time ≤ s.time + lat₁; linarith,
        fun t ht => by rw [sensor₁]; exact prior₁ t ht, by rw [sensor₁]; exact root₁⟩
    marked := fun q hm => by rw [aux₁ q] at hm; cases hm
    silenced := fun q hm => by rw [aux₁ q] at hm; cases hm
    above := fun q hb => by
      have hq : q = p₁ := by
        rcases hb with h | h
        · exact absurd (aux₁ q) h
        · exact live₁ q h
      subst hq
      rw [silentEnd_ready (aux₁ q), M₁]
      exact aboveK q (Or.inl rfl) _ (by linarith [(markSpan q).1]) }
  have complete₁ : Complete θ a₁ M (s.time + 1 / 20) :=
    ⟨fun q _ hr => by
      obtain rfl := live₁ q hr
      rw [M₁]
      linarith [(markSpan q).2],
     fun q hm => by rw [aux₁ q] at hm; cases hm⟩
  obtain ⟨c, run₁, dateC, planC, sameC, keepC⟩ := driven_until_exists box M D₂ K level a₁ plan₁
  have completeC := keepC _ complete₁
  have busy₁ : Busy a₁ p₁ := Or.inr (by rw [raw₁]; simp)
  have idle₁ (q : Port) (h : q ≠ p₁) : ¬ Busy a₁ q := by
    intro hb
    rcases hb with hb | hb
    · exact hb (aux₁ q)
    · exact h (live₁ q hb)
  have rawC (q : Port) : c.raw 0 q = a₁.raw 0 q := by rw [sameC.raw]
  have auxC (q : Port) (h : q ≠ p₁) : c.aux 0 q = .ready := by
    by_contra hn
    exact idle₁ q h ((sameC.busy q).mp (Or.inl hn))
  have sensorC (q : Port) (h : q ≠ p₁) (t : ℝ) :
      drivenSensor θ c q t = relax (1 / 2) (1 / 40) (s.x 0 (.m q)) s.time t := by
    rw [sameC.idle q (idle₁ q h) t, drivenSensor_ready (aux₁ q), rawScale_none (rawRest q h),
      mul_zero, auxPulse_zero_eq_relax]
    rfl
  have valueC₂ : c.x 0 (.m p₂) = m₂ := by
    rw [← drivenSensor_initial θ c p₂, sensorC p₂ (Ne.symm distinct), dateC]
  have chargeC : c.x 0 .q = readyPulse (s.x 0 .q) G₁ s.time D₂ := by
    have h := sameC.charge c.time
    rw [readyPulse_initial, amplitude₁, dateC] at h
    exact h
  -- The second admission.
  have free : c.raw 0 p₂ = none := (rawC p₂).trans (rawRest p₂ (Ne.symm distinct))
  have queueC : c.pending = [] ++ ((⟨0, p₂, D₂⟩ : Delivery 1) :: later) := sameC.queue
  let a₂ : Snapshot 1 := { (setRaw c 0 p₂ (some c.time)) with pending := [] ++ later }
  let jump₂ : ParameterJump θ (fun _ _ => []) c a₂ :=
    .arrive c ⟨0, p₂, D₂⟩ [] later queueC dateC.symm free
  have raw₂ : a₂.raw 0 p₂ = some D₂ := by
    simp [a₂, setRaw]
    exact dateC
  have rawOther (q : Port) (h : q ≠ p₂) : a₂.raw 0 q = c.raw 0 q :=
    raw_update_other c 0 p₂ (some c.time) 0 q (Or.inr h)
  have sensorOther (q : Port) (h : q ≠ p₂) : drivenSensor θ a₂ q = drivenSensor θ c q :=
    drivenSensor_congr rfl rfl (rawOther q h) rfl
  have endOther (q : Port) (T : ℝ) : silentEnd θ a₂ M q T = silentEnd θ c M q T :=
    silentEnd_congr rfl rfl rfl T
  have scale₂ : rawScale a₂ p₂ = 1 := by
    show rawInputScale (a₂.raw 0 p₂) c.time = 1
    rw [raw₂, dateC]
    simp [rawInputScale]
  have scale₂₁ : rawScale a₂ p₁ = Real.exp (-a * (D₂ - s.time)) := by
    show rawInputScale (a₂.raw 0 p₁) c.time = _
    rw [rawOther p₁ distinct, rawC, raw₁, dateC]
    rfl
  have amplitude₂ : drivenAmplitude a₂ = G₁ * Real.exp (-a * (D₂ - s.time)) + G₂ := by
    unfold drivenAmplitude
    rw [Finset.sum_eq_add p₁ p₂ distinct
      (fun q _ hq => by
        rw [rawScale_none ((rawOther q hq.2).trans ((rawC q).trans (rawRest q hq.1))), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h),
      scale₂₁, scale₂, mul_one]
    show Real.exp (c.x 0 (.z p₁)) * _ + Real.exp (c.x 0 (.z p₂)) = _
    rw [sameC.gains p₁, sameC.gains p₂]
    rfl
  have chargeFn (t : ℝ) :
      readyPulse (a₂.x 0 .q) (drivenAmplitude a₂) a₂.time t = joint t := by
    rw [amplitude₂]
    show readyPulse (c.x 0 .q) _ c.time t = _
    rw [chargeC, dateC, readyPulse_add, readyPulse_restart]
    rfl
  have aux₂ : a₂.aux 0 p₂ = .ready := auxC p₂ (Ne.symm distinct)
  have sensor₂ (t : ℝ) : drivenSensor θ a₂ p₂ t =
      auxPulse m₂ ((θ 0).inputGain p₂) D₂ t := by
    rw [drivenSensor_ready aux₂, scale₂, mul_one]
    show auxPulse (c.x 0 (.m p₂)) _ c.time t = _
    rw [valueC₂, dateC]
  have busyOther (q : Port) (h : q ≠ p₂) (hb : Busy a₂ q) : Busy c q := by
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (by rw [← rawOther q h]; exact hb)
  have plan₂ : Plan θ a₂ M tf K level := {
    driven := ⟨planC.driven.main, planC.driven.no_error⟩
    time := by show c.time ≤ tf; rw [dateC]; exact after.le
    horizon := tfLe
    fire := config₁.fire
    mark := config₁.mark
    silent := config₁.silent
    charge := fun t ht => by
      rw [chargeFn]
      have lo : c.time ≤ t := ht.1
      rw [dateC] at lo
      exact first t ⟨lo, ht.2⟩
    raw := fun q o h => by
      by_cases hq : q = p₂
      · subst q
        rw [raw₂] at h
        obtain rfl := Option.some.inj h
        exact ⟨by show D₂ ≤ c.time; rw [dateC], by linarith [order.1]⟩
      · rw [rawOther q hq, rawC] at h
        have hq₁ := live₁ q (by rw [h]; simp)
        subst hq₁
        rw [raw₁] at h
        obtain rfl := Option.some.inj h
        exact ⟨by show s.time ≤ c.time; rw [dateC]; exact order.1, tfLe⟩
    pending := fun d hd => by
      have due := laterDue d (by simpa [a₂] using hd)
      linarith
    quiet := fun q hm hr => by
      have hq : q ≠ p₂ := fun h => by rw [h, raw₂] at hr; cases hr
      exact planC.quiet q hm (by rw [← rawOther q hq]; exact hr)
    ready := fun q hm hr => by
      by_cases hq : q = p₂
      · subst q
        rw [M₂]
        refine ⟨by show c.time ≤ D₂ + lat₂; rw [dateC]; linarith, fun t ht => ?_, ?_⟩
        · rw [sensor₂]
          have lo : c.time ≤ t := ht.1
          rw [dateC] at lo
          exact prior₂ t ⟨lo, ht.2⟩
        · rw [sensor₂]
          exact root₂
      · rw [sensorOther q hq]
        exact planC.ready q hm (by rw [← rawOther q hq]; exact hr)
    marked := planC.marked
    silenced := planC.silenced
    above := fun q hb => by
      by_cases hq : q = p₂
      · subst q
        rw [silentEnd_ready aux₂, M₂]
        exact aboveK p₂ (Or.inr rfl) _ (by linarith [order.1, (markSpan p₂).1])
      · rw [endOther]
        exact planC.above q (busyOther q hq hb) }
  have complete₂ : Complete θ a₂ M tf :=
    ⟨fun q hm hr => by
      by_cases hq : q = p₂
      · subst q
        rw [M₂]
        linarith [(markSpan p₂).2]
      · have h := completeC.ready q hm (by rw [← rawOther q hq]; exact hr)
        linarith [order.1],
     fun q hm => by
      have h := completeC.marked q hm
      exact h.trans (by linarith [order.1])⟩
  obtain ⟨e, run₂, fin⟩ := driven_run_exists box M tf K level a₂ plan₂ complete₂
  have pre : Runs θ s e 0 :=
    (Runs.jump jump₁ rfl).append (run₁.append ((Runs.jump jump₂ rfl).append run₂))
  obtain ⟨preExec, _⟩ := id pre
  have inv := ParameterExecution.physical_invariant preExec
    (cell_threshold_bounds config₁.cell fire) box state.physical
  have eCharge : e.x 0 .q = level := by
    rw [fin.charge, chargeFn]
    exact hit
  have ports : ∀ q, FiredPort θ e s.time q := by
    intro q
    by_cases h₂ : q = p₂
    · subst q
      obtain ⟨mode, value⟩ := fin.busy p₂ (Or.inr (by rw [raw₂]; simp))
      obtain ⟨lo, hi, floor, below⟩ := errBand p₂ (Or.inr rfl)
      refine Or.inr ⟨mode, lo, hi, floor, below, D₂, M p₂ + decayTime 1 (4 / 5) ((θ 0).lm p₂),
        by rw [fin.raw]; exact raw₂, order.1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [M₂]; linarith [(markSpan p₂).1]
      · rw [M₂]; linarith [(markSpan p₂).2, order.2]
      · rw [fin.time]; exact after.le
      · rw [fin.time]; linarith [order.1]
      · rw [value, silentEnd_ready aux₂, fin.time]
    · by_cases h₁ : q = p₁
      · subst q
        have busyC : Busy c p₁ := (sameC.busy p₁).mpr busy₁
        have busyA : Busy a₂ p₁ := by
          rcases busyC with hb | hb
          · exact Or.inl hb
          · exact Or.inr (by rw [rawOther p₁ h₂]; exact hb)
        obtain ⟨mode, value⟩ := fin.busy p₁ busyA
        obtain ⟨lo, hi, floor, below⟩ := errBand p₁ (Or.inl rfl)
        refine Or.inr ⟨mode, lo, hi, floor, below, s.time,
          M p₁ + decayTime 1 (4 / 5) ((θ 0).lm p₁),
          by rw [fin.raw, rawOther p₁ h₂, rawC]; exact raw₁, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
        · rw [M₁]; linarith [(markSpan p₁).1]
        · rw [M₁]; linarith [(markSpan p₁).2]
        · rw [fin.time]; linarith [order.1]
        · rw [fin.time]; exact tfLe
        · rw [value, endOther, sameC.ends p₁ busy₁, silentEnd_ready (aux₁ p₁), fin.time]
      · have idleA : ¬ Busy a₂ q := by
          intro hb
          exact idle₁ q h₁ ((sameC.busy q).mp (busyOther q h₂ hb))
        obtain ⟨mode, value⟩ := fin.idle q idleA
        refine Or.inl ⟨mode,
          by rw [fin.raw, rawOther q h₂, rawC]; exact rawRest q h₁, ?_⟩
        rw [value, sensorOther q h₂, sensorC q h₁]
        exact relax_restBand (by linarith [order.1]) (state.sensors q)
  obtain ⟨u, tail, rested, date, pend, gains, b, charge⟩ :=
    fire_rest_exists (D := s.time) (rest := rest) box config₁.cell fire inv fin.main eCharge
      (by rw [fin.recovery]; show 7 / 100 ≤ c.x 0 .b ∧ c.x 0 .b ≤ 1 / 10
          rw [sameC.recovery]; exact recovery)
      (by rw [fin.time]; exact ⟨by linarith [order.1], tfLe⟩) ports wait
      (by
        intro d hd
        rw [fin.queue] at hd
        exact laterDue d (by simpa [a₂] using hd))
  refine ⟨u, tf, ?_, late, tfLe, hit, rested, date, ?_, ?_, ?_, charge⟩
  · have whole := pre.emits.append tail
    rw [fin.time] at whole
    simpa using whole
  · rw [pend, fin.queue]
    simp [a₂]
  · intro q
    rw [gains q, fin.gains q]
    exact sameC.gains q
  · rw [b, fin.recovery]
    exact sameC.recovery

theorem readyPulse_rest (gain start t : ℝ) :
    readyPulse (1 / 10) gain start t = 1 / 10 + gain * response (t - start) := by
  rw [readyPulse_shift, readyPulse_at_rest]

/-- The read of two ports after stop-learning training, as an execution.
Each gain fires alone from the exact rest charge, and one dose below it
was silent, with doses of at most 1/20. The second read pulse arrives up
to a quarter of a unit after the first. The cell fires exactly once,
later than 0.239 units after the first pulse and no later than 0.256
units after the second, whatever the two gains and the FIRE level. Every
complete run fires at that same date. -/
theorem stopped_staggered_read {θ ε p₁ p₂ u₁ l₁ u₂ l₂ level rest D₂} {s : Snapshot 1}
    {later : List (Delivery 1)} (box : @PhysicalBox 1 θ ε) (distinct : p₁ ≠ p₂)
    (config₁ : PortConfig θ p₁ u₁ l₁ level) (config₂ : PortConfig θ p₂ u₂ l₂ level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry₁ : 7 / 100 ≤ u₁ ∧ u₁ ≤ 2 / 25) (exit₁ : 1 / 200 ≤ l₁ ∧ l₁ < u₁)
    (entry₂ : 7 / 100 ≤ u₂ ∧ u₂ ≤ 2 / 25) (exit₂ : 1 / 200 ≤ l₂ ∧ l₂ < u₂)
    (dose₁ : 8 * (u₁ - l₁) ≤ 1 / 20) (dose₂ : 8 * (u₂ - l₂) ≤ 1 / 20)
    (state : RestState θ s) (rested : s.x 0 .q = 1 / 10)
    (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending =
      (⟨0, p₁, s.time⟩ : Delivery 1) :: (⟨0, p₂, D₂⟩ : Delivery 1) :: later)
    (order : s.time ≤ D₂ ∧ D₂ ≤ s.time + 1 / 4)
    (wait : s.time + 22 ≤ rest) (laterDue : ∀ d ∈ later, rest ≤ d.due)
    (fires₁ : PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₁))) level)
    (fires₂ : PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₂))) level)
    (silent₁ : ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
      ¬ PulseFires c (Real.exp (s.x 0 (.z p₁) - 8 * (u₁ - l₁))) level)
    (silent₂ : ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
      ¬ PulseFires c (Real.exp (s.x 0 (.z p₂) - 8 * (u₂ - l₂))) level) :
    ∃ u tf, Emits θ s u [(0, tf)] ∧ s.time + 239 / 1000 < tf ∧ tf ≤ D₂ + 32 / 125 ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = later ∧
      (∀ q, u.x 0 (.z q) = s.x 0 (.z q)) ∧ u.x 0 .b = s.x 0 .b ∧ u.x 0 .q = 1 / 10 ∧
      (later = [] → ∀ (v : Snapshot 1) (other : ParameterExecution θ (fun _ _ => []) s v),
        ParameterCompleteThrough other rest →
        u.ObservationalEq v ∧ other.emissionTimes 0 = [tf]) := by
  have hPos := response_one_pos
  have hLow := response_one_lower
  have step : (19 / 20 : ℝ) ≤ Real.exp (-(1 / 20 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 20 : ℝ))]
  have unit : (209 / 400 : ℝ) ≤ Real.exp (-(1 / 20 : ℝ)) * response 1 := by
    have h := mul_le_mul step hLow (by norm_num) (Real.exp_pos _).le
    linarith
  -- Scalar facts for one port.
  have port (z d : ℝ) (dose : d ≤ 1 / 20)
      (fires : PulseFires (1 / 10) (Real.exp z) level)
      (silent : ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
        ¬ PulseFires c (Real.exp (z - d)) level) :
      level ≤ 1 / 10 + Real.exp z * response 1 ∧
      1 / 10 + Real.exp z * (Real.exp (-(1 / 20 : ℝ)) * response 1) < level := by
    obtain ⟨τ, hτ, reach⟩ := fires
    rw [readyPulse_at_rest] at reach
    have rise := response_strictMono_pulse.monotoneOn hτ
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) hτ.2
    have grow := mul_le_mul_of_nonneg_left rise (Real.exp_pos z).le
    obtain ⟨c, hc, _, quiet⟩ := silent
    have below : 1 / 10 + Real.exp (z - d) * response 1 < level := by
      by_contra h
      exact quiet (pulseFires_of_peak hc (not_lt.mp h))
    rw [sub_eq_add_neg, Real.exp_add] at below
    have decay : Real.exp (-(1 / 20 : ℝ)) ≤ Real.exp (-d) := Real.exp_le_exp.mpr (by linarith)
    have weaker : Real.exp z * (Real.exp (-(1 / 20 : ℝ)) * response 1) ≤
        Real.exp z * Real.exp (-d) * response 1 := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left decay (Real.exp_pos z).le) hPos.le
    exact ⟨by linarith, by linarith⟩
  obtain ⟨peak₁, low₁⟩ := port _ _ dose₁ fires₁ silent₁
  obtain ⟨peak₂, low₂⟩ := port _ _ dose₂ fires₂ silent₂
  let G₁ := Real.exp (s.x 0 (.z p₁))
  let G₂ := Real.exp (s.x 0 (.z p₂))
  have g₁ : 0 < G₁ := Real.exp_pos _
  have g₂ : 0 < G₂ := Real.exp_pos _
  have pk₁ : level ≤ 1 / 10 + G₁ * response 1 := peak₁
  have pk₂ : level ≤ 1 / 10 + G₂ * response 1 := peak₂
  have lw₁ : 1 / 10 + G₁ * (Real.exp (-(1 / 20 : ℝ)) * response 1) < level := low₁
  have lw₂ : 1 / 10 + G₂ * (Real.exp (-(1 / 20 : ℝ)) * response 1) < level := low₂
  have cap₁ : G₁ * (209 / 400) < level - 1 / 10 := by
    have h := mul_le_mul_of_nonneg_left unit g₁.le
    linarith
  have cap₂ : G₂ * (209 / 400) < level - 1 / 10 := by
    have h := mul_le_mul_of_nonneg_left unit g₂.le
    linarith
  have slope (x : ℝ) (h₀ : 0 ≤ x) : response x ≤ (7 / 5) * x := by
    have h := response_upper h₀
    have k := mul_le_mul_of_nonneg_right a_coarse_bounds.2.le h₀
    linarith
  have alone : ∀ t ∈ Ico s.time D₂, readyPulse (s.x 0 .q) G₁ s.time t < level := by
    intro t ht
    rw [rested, readyPulse_rest]
    have span : (7 / 5 : ℝ) * (t - s.time) ≤ 7 / 20 := by linarith [ht.2, order.2]
    have h := mul_le_mul_of_nonneg_left
      ((slope (t - s.time) (by linarith [ht.1])).trans span) g₁.le
    linarith
  have quiet : ∀ t ∈ Icc D₂ (D₂ + 1 / 20), jointCharge (s.x 0 .q) G₁ G₂ s.time D₂ t < level := by
    intro t ht
    unfold jointCharge
    rw [rested, readyPulse_rest]
    have span₁ : (7 / 5 : ℝ) * (t - s.time) ≤ 21 / 50 := by linarith [ht.2, order.2]
    have span₂ : (7 / 5 : ℝ) * (t - D₂) ≤ 7 / 100 := by linarith [ht.2]
    have h₁ := mul_le_mul_of_nonneg_left
      ((slope (t - s.time) (by linarith [ht.1, order.1])).trans span₁) g₁.le
    have h₂ := mul_le_mul_of_nonneg_left
      ((slope (t - D₂) (by linarith [ht.1])).trans span₂) g₂.le
    linarith
  have mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : response x ≤ response y :=
    response_strictMono_pulse.monotoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy
  have fires : ∃ t ∈ Icc D₂ (s.time + 1), level ≤ jointCharge (s.x 0 .q) G₁ G₂ s.time D₂ t := by
    refine ⟨D₂ + 32 / 125, ⟨by linarith, by linarith [order.2]⟩, ?_⟩
    unfold jointCharge
    rw [rested, readyPulse_rest, add_sub_cancel_left]
    have later₁ := mono (x := 32 / 125) (y := D₂ + 32 / 125 - s.time) (by norm_num)
      (by linarith [order.1]) (by linarith [order.2])
    have half := window_half.2
    have a₁ := mul_le_mul_of_nonneg_left (half.trans later₁) g₁.le
    have a₂ := mul_le_mul_of_nonneg_left half g₂.le
    show level ≤ 1 / 10 + G₁ * response (D₂ + 32 / 125 - s.time) + G₂ * response (32 / 125)
    linarith
  obtain ⟨u, tf, emits, late, tfLe, hit, restedEnd, date, pend, gains, b, charge⟩ :=
    staggered_read_exists box distinct config₁ config₂ fire entry₁ exit₁ entry₂ exit₂ state
      recovery queue order wait laterDue alone quiet fires
  unfold jointCharge at hit
  rw [rested, readyPulse_rest] at hit
  have hit' : 1 / 10 + G₁ * response (tf - s.time) + G₂ * response (tf - D₂) = level := hit
  have τpos : 0 ≤ tf - D₂ := by linarith
  have τle : tf - D₂ ≤ tf - s.time := by linarith [order.1]
  have τ₁le : tf - s.time ≤ 1 := by linarith
  have between := mono τpos τle τ₁le
  have sumPos : 0 < G₁ + G₂ := add_pos g₁ g₂
  have upper : response (tf - D₂) ≤ 1 / 2 * response 1 := by
    have h₁ := mul_le_mul_of_nonneg_left between g₁.le
    have total : (G₁ + G₂) * response (tf - D₂) ≤ (G₁ + G₂) * (1 / 2 * response 1) := by
      linarith
    exact le_of_mul_le_mul_left total sumPos
  have lower : 1 / 2 * (Real.exp (-(1 / 20 : ℝ)) * response 1) < response (tf - s.time) := by
    have h₂ := mul_le_mul_of_nonneg_left between g₂.le
    have total : (G₁ + G₂) * (1 / 2 * (Real.exp (-(1 / 20 : ℝ)) * response 1)) <
        (G₁ + G₂) * response (tf - s.time) := by
      linarith
    exact lt_of_mul_lt_mul_left total sumPos.le
  have afterFirst : s.time + 239 / 1000 < tf := by
    have lowBound : response (239 / 1000) < response (tf - s.time) :=
      lt_of_le_of_lt (by linarith [window_half.1]) lower
    have h := (response_strictMono_pulse.lt_iff_lt
      (show (239 / 1000 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, by norm_num⟩)
      ⟨τpos.trans τle, τ₁le⟩).mp lowBound
    linarith
  have beforeSecond : tf ≤ D₂ + 32 / 125 := by
    have h := (response_strictMono_pulse.le_iff_le ⟨τpos, τle.trans τ₁le⟩
      (show (32 / 125 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, by norm_num⟩)).mp
      (upper.trans window_half.2)
    linarith
  refine ⟨u, tf, emits, afterFirst, beforeSecond, restedEnd, date, pend, gains, b, charge, ?_⟩
  intro none v other complete
  obtain ⟨e, he⟩ := emits
  have bounds := cell_threshold_bounds config₁.cell fire
  have done : ParameterCompleteThrough e rest :=
    date ▸ restedEnd.complete config₁ fire.1 e (pend.trans none)
  refine ⟨(ParameterExecution.observational_unique box bounds e other state.physical done
    complete).1, ?_⟩
  rw [← ParameterExecution.emissionTimes_unique e other box bounds state.physical done complete 0]
  simp [ParameterExecution.emissionTimes, he]

/-- A FIRE of an execution happens no later than its end. -/
theorem emissionTimes_le {n θ route} {s u : Snapshot n} (e : ParameterExecution θ route s u)
    (i : Fin n) : ∀ t ∈ e.emissionTimes i, t ≤ u.time := by
  induction e with
  | nil => intro t ht; simp [ParameterExecution.emissionTimes, ParameterExecution.emissions] at ht
  | cons m rest ih =>
    intro t ht
    unfold ParameterExecution.emissionTimes at ht ih
    simp only [ParameterExecution.emissions_cons, List.filter_append, List.map_append,
      List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨event, mem, rfl⟩ := List.mem_map.mp ht
      rw [m.emission_time event (List.mem_filter.mp mem).1]
      exact m.time_monotone.trans rest.time_monotone
    · exact ih t ht

theorem emissionTimes_append {θ : Fin 1 → Parameters} {s u v : Snapshot 1}
    (e : ParameterExecution θ (fun _ _ => []) s u) (f : ParameterExecution θ (fun _ _ => []) u v) :
    (e.append f).emissionTimes 0 = e.emissionTimes 0 ++ f.emissionTimes 0 := by
  simp [ParameterExecution.emissionTimes, execution_emissions_append]

/-- Training and read in one execution. Two ports of a rested cell start
from gains that do not fire. Each is trained by its own train of pulses,
with a dose of at most 1/20, until it stops by itself. One pulse on each
port then reads the cell, the second up to a quarter of a unit after the
first. The read FIRE comes later than 0.239 units after the first read
pulse and no later than 0.256 units after the second, whatever the start
gains and the FIRE level. Every complete run has the same FIRE dates and
the same end. -/
theorem trained_read_exists {θ ε p₁ p₂ u₁ l₁ u₂ l₂ level}
    {dates₁ dates₂ : List ℝ} {s : Snapshot 1} {middle read₁ read₂ rest : ℝ}
    (box : @PhysicalBox 1 θ ε) (distinct : p₁ ≠ p₂)
    (config₁ : PortConfig θ p₁ u₁ l₁ level) (config₂ : PortConfig θ p₂ u₂ l₂ level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry₁ : 7 / 100 ≤ u₁ ∧ u₁ ≤ 2 / 25) (exit₁ : 1 / 200 ≤ l₁ ∧ l₁ < u₁)
    (entry₂ : 7 / 100 ≤ u₂ ∧ u₂ ≤ 2 / 25) (exit₂ : 1 / 200 ≤ l₂ ∧ l₂ < u₂)
    (dose₁ : 8 * (u₁ - l₁) ≤ 1 / 20) (dose₂ : 8 * (u₂ - l₂) ≤ 1 / 20)
    (state : RestState θ s) (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending = (⟨0, p₁, s.time⟩ : Delivery 1) ::
      (dates₁.map (fun D => (⟨0, p₁, D⟩ : Delivery 1)) ++
        (⟨0, p₂, middle⟩ : Delivery 1) ::
          (dates₂.map (fun D => (⟨0, p₂, D⟩ : Delivery 1)) ++
            [(⟨0, p₁, read₁⟩ : Delivery 1), (⟨0, p₂, read₂⟩ : Delivery 1)])))
    (spaced₁ : Spaced s.time dates₁ middle) (spaced₂ : Spaced middle dates₂ read₁)
    (order : read₁ ≤ read₂ ∧ read₂ ≤ read₁ + 1 / 4) (wait : read₁ + 22 ≤ rest)
    (below₁ : ¬ PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₁))) level)
    (below₂ : ¬ PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₂))) level)
    (r₁ r₂ : ℕ)
    (reach₁ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₁) + r₁ * (8 * (u₁ - l₁))) * response 1)
    (reach₂ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₂) + r₂ * (8 * (u₂ - l₂))) * response 1)
    (enough₁ : 2 * r₁ + 2 ≤ dates₁.length + 1) (enough₂ : 2 * r₂ + 2 ≤ dates₂.length + 1) :
    ∃ (u : Snapshot 1) (tf : ℝ) (training : List ℝ),
      read₁ + 239 / 1000 < tf ∧ tf ≤ read₂ + 32 / 125 ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) s u,
        e.emissionTimes 0 = training ++ [tf]) ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = [] ∧
      (∃ k : ℕ, k ≤ dates₁.length + 1 ∧ u.x 0 (.z p₁) = s.x 0 (.z p₁) + k * (8 * (u₁ - l₁))) ∧
      (∃ k : ℕ, k ≤ dates₂.length + 1 ∧ u.x 0 (.z p₂) = s.x 0 (.z p₂) + k * (8 * (u₂ - l₂))) ∧
      (∀ (v : Snapshot 1) (other : ParameterExecution θ (fun _ _ => []) s v),
        ParameterCompleteThrough other rest →
        u.ObservationalEq v ∧ other.emissionTimes 0 = training ++ [tf]) ∧
      ∀ t ∈ training, t ≤ read₁ := by
  obtain ⟨m, f, ⟨e₁, _⟩, rested, date, pend, charge, b, _, gain₁, gain₂, fires₁, fires₂, last₁,
      last₂, _⟩ :=
    two_port_training_exists
      (tail := [(⟨0, p₁, read₁⟩ : Delivery 1), (⟨0, p₂, read₂⟩ : Delivery 1)])
      box distinct config₁ config₂ fire entry₁ exit₁ entry₂ exit₂ state recovery queue spaced₁
      spaced₂ (by
        intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact le_rfl
        · exact order.1)
      r₁ r₂ reach₁ reach₂ enough₁ enough₂
  have silent₁ := last₁.resolve_left (fun same => below₁ (same ▸ fires₁))
  have silent₂ := last₂.resolve_left (fun same => below₂ (same ▸ fires₂))
  obtain ⟨u, tf, ⟨e₂, emitted⟩, afterFirst, beforeSecond, restedEnd, dateEnd, pendEnd, gains,
      _, _, _⟩ :=
    stopped_staggered_read (later := []) (rest := rest) (D₂ := read₂) box distinct config₁
      config₂ fire entry₁ exit₁ entry₂ exit₂ dose₁ dose₂ rested charge
      (by rw [b]; exact recovery) (by rw [pend, date]) (by rw [date]; exact order)
      (by rw [date]; exact wait) (by intro d hd; cases hd) fires₁ fires₂ silent₁ silent₂
  have times : (e₁.append e₂).emissionTimes 0 = e₁.emissionTimes 0 ++ [tf] := by
    rw [emissionTimes_append]
    congr 1
    simp [ParameterExecution.emissionTimes, emitted]
  rw [date] at afterFirst
  have early : ∀ t ∈ e₁.emissionTimes 0, t ≤ read₁ := by
    intro t ht
    rw [← date]
    exact emissionTimes_le e₁ 0 t ht
  refine ⟨u, tf, e₁.emissionTimes 0, afterFirst, beforeSecond, ⟨e₁.append e₂, times⟩,
    restedEnd, dateEnd, pendEnd, ?_, ?_, ?_, early⟩
  · obtain ⟨k, hk, e⟩ := gain₁
    exact ⟨k, hk, by rw [gains, e]⟩
  · obtain ⟨k, hk, e⟩ := gain₂
    exact ⟨k, hk, by rw [gains, e]⟩
  · intro v other complete
    have bounds := cell_threshold_bounds config₁.cell fire
    have done : ParameterCompleteThrough (e₁.append e₂) rest :=
      dateEnd ▸ restedEnd.complete config₁ fire.1 (e₁.append e₂) pendEnd
    refine ⟨(ParameterExecution.observational_unique box bounds (e₁.append e₂) other
      state.physical done complete).1, ?_⟩
    rw [← ParameterExecution.emissionTimes_unique (e₁.append e₂) other box bounds state.physical
      done complete 0, times]

end RecursiveLearning.Native
