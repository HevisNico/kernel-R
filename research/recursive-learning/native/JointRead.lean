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
started at `D`, on a port whose ERROR entry threshold is low. -/
def FiredPort (θ : Fin 1 → Parameters) (e : Snapshot 1) (D : ℝ) (q : Port) : Prop :=
  (e.aux 0 q = .ready ∧ e.raw 0 q = none ∧ RestBand (e.x 0 (.m q))) ∨
  (e.aux 0 q = .silent ∧ e.raw 0 q = some D ∧
    7 / 100 ≤ (θ 0).thresholds.error q ∧ (θ 0).thresholds.error q ≤ 2 / 25 ∧
    1 / 200 ≤ (θ 0).thresholds.auxReady q ∧
    (θ 0).thresholds.auxReady q < (θ 0).thresholds.error q ∧
    ∃ S, D ≤ S ∧ S < D + 1 / 20 ∧
      e.x 0 (.m q) = (4 / 5) * Real.exp (-(θ 0).ls q * (e.time - S)))

/-- The FIRE and the return to rest, with any number of SILENT sensors.
The cell is READY with its main charge at the FIRE level. It fires once,
goes through its refractory period while the busy sensors complete their
cycle, and ends at rest with every gain unchanged. -/
theorem fire_rest_exists {θ ε} {e : Snapshot 1} {level rest D : ℝ} (box : @PhysicalBox 1 θ ε)
    (cell : CellConfig θ level) (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (inv : ParameterPhysicalInvariant θ e) (main : e.main 0 = .ready)
    (charge : e.x 0 .q = level) (recovery : 7 / 100 ≤ e.x 0 .b ∧ e.x 0 .b ≤ 1 / 10)
    (date : D + 1 / 20 ≤ e.time ∧ e.time ≤ D + 1) (ports : ∀ q, FiredPort θ e D q)
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
  -- A busy sensor is above its ERROR entry threshold and reopens between D + 1 and D + 2.
  have busy (q : Port) (hs : e.aux 0 q = .silent) :
      e.raw 0 q = some D ∧ (θ 0).thresholds.error q ≤ e.x 0 (.m q) ∧
      D + 1 < sensorReady θ fired q ∧ sensorReady θ fired q < D + 2 ∧
      1 / 200 ≤ (θ 0).thresholds.auxReady q ∧ (θ 0).thresholds.auxReady q < 2 / 25 := by
    rcases ports q with ⟨hr, _, _⟩ | ⟨_, raw, lo, hi, floor, below, S, s₀, s₁, value⟩
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
      refine ⟨raw, ?_, ?_, ?_, floor, by linarith⟩
      · rw [value]
        exact (decay_above (by norm_num) epos rp (by linarith [date.2])).le
      · rw [readyEq]; linarith [errT.1]
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
      · rw [(busy q hm).1] at h'
        obtain rfl := Option.some.inj h'
        exact ⟨by show D ≤ e.time; linarith [date.1], date.2⟩ }
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
      linarith [(busy q hs).2.2.2.1, fastT.1, slowT.1, date.1]
    raw := fun q o h => by
      have h' : e.raw 0 q = some o := h
      rcases modes q with hm | hm
      · rw [(idle q hm).1] at h'; cases h'
      · rw [(busy q hm).1] at h'
        obtain rfl := Option.some.inj h'
        rw [reopenEq]
        exact ⟨by linarith [fastT.1, slowT.1, date.1], (busy q hm).2.2.1⟩
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
        (by linarith [(busy q hm).2.2.2.2.2])
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
      obtain ⟨_, _, _, early, floor, ceil⟩ := busy q hm
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

/-- A read of two ports at the same instant, as an execution. Each port
has its own low ERROR thresholds. If the two pulses together bring the
main charge of the rested cell to the FIRE level, the cell fires exactly
once, at the first contact, and returns to rest with every gain and the
recovery rate unchanged. The latency is the first-contact time of the
scalar read equation at the sum of the two gains. -/
theorem joint_read_exists {θ ε p₁ p₂ u₁ l₁ u₂ l₂ level rest} {s : Snapshot 1}
    {later : List (Delivery 1)} (box : @PhysicalBox 1 θ ε) (distinct : p₁ ≠ p₂)
    (config₁ : PortConfig θ p₁ u₁ l₁ level) (config₂ : PortConfig θ p₂ u₂ l₂ level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry₁ : 7 / 100 ≤ u₁ ∧ u₁ ≤ 2 / 25) (exit₁ : 1 / 200 ≤ l₁ ∧ l₁ < u₁)
    (entry₂ : 7 / 100 ≤ u₂ ∧ u₂ ≤ 2 / 25) (exit₂ : 1 / 200 ≤ l₂ ∧ l₂ < u₂)
    (state : RestState θ s) (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending =
      (⟨0, p₁, s.time⟩ : Delivery 1) :: (⟨0, p₂, s.time⟩ : Delivery 1) :: later)
    (wait : s.time + 22 ≤ rest) (laterDue : ∀ d ∈ later, rest ≤ d.due)
    (sum : Real.exp (s.x 0 (.z p₁)) + Real.exp (s.x 0 (.z p₂)) ≤ 7)
    (fires : PulseFires (s.x 0 .q)
      (Real.exp (s.x 0 (.z p₁)) + Real.exp (s.x 0 (.z p₂))) level) :
    ∃ u latency, Emits θ s u [(0, s.time + latency)] ∧
      FirstPulseReport (s.x 0 .q) (Real.exp (s.x 0 (.z p₁)) + Real.exp (s.x 0 (.z p₂)))
        level latency ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = later ∧
      (∀ q, u.x 0 (.z q) = s.x 0 (.z q)) ∧ u.x 0 .b = s.x 0 .b ∧ u.x 0 .q = 1 / 10 := by
  let G := Real.exp (s.x 0 (.z p₁)) + Real.exp (s.x 0 (.z p₂))
  have Gpos : 0 ≤ G := add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  let pulse := fun t => readyPulse (s.x 0 .q) G s.time t
  have pulseCont : Continuous pulse := by
    dsimp only [pulse, readyPulse, response]
    fun_prop
  -- The first contact with the FIRE level, after both sensors are SILENT.
  have early : ∀ t, s.time ≤ t → t ≤ s.time + 1 / 20 → pulse t ≤ 3 / 5 := by
    intro t h₀ h₁
    have resp := response_upper (sub_nonneg.mpr h₀)
    have respPos := response_nonnegative (sub_nonneg.mpr h₀)
    have small : response (t - s.time) ≤ 7 / 100 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr a_coarse_bounds.2.le) (sub_nonneg.mpr h₀),
        a_coarse_bounds.1]
    have drive := mul_le_mul (show G ≤ 7 from sum) small respPos (by norm_num)
    have decay := decay_upper (show s.x 0 .q - 1 / 10 ≤ 1 / 10000 by linarith [state.charge.2])
      (by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (sub_nonneg.mpr h₀)
    dsimp only [pulse, readyPulse]
    linarith
  obtain ⟨t₁, ht₁, high⟩ := (pulseFires_iff (start := s.time)).mpr fires
  have startLow : pulse s.time < level :=
    lt_of_le_of_lt (early s.time le_rfl (by linarith)) (by linarith [fire.1])
  obtain ⟨tf, after, before, hit, first⟩ := first_hit pulseCont ht₁.1 startLow high
  have late : s.time + 1 / 20 < tf := by
    by_contra h
    have bound := early tf after.le (not_lt.mp h)
    rw [hit] at bound
    linarith [fire.1]
  have tfLe : tf ≤ s.time + 1 := before.trans ht₁.2
  -- The two admissions.
  let a₁ : Snapshot 1 := { (setRaw s 0 p₁ (some s.time)) with
    pending := [] ++ ((⟨0, p₂, s.time⟩ : Delivery 1) :: later) }
  let jump₁ : ParameterJump θ (fun _ _ => []) s a₁ :=
    .arrive s ⟨0, p₁, s.time⟩ [] ((⟨0, p₂, s.time⟩ : Delivery 1) :: later) queue rfl (state.raw p₁)
  have free : a₁.raw 0 p₂ = none :=
    (raw_update_other s 0 p₁ (some s.time) 0 p₂ (Or.inr (Ne.symm distinct))).trans (state.raw p₂)
  let a₂ : Snapshot 1 := { (setRaw a₁ 0 p₂ (some a₁.time)) with pending := [] ++ later }
  let jump₂ : ParameterJump θ (fun _ _ => []) a₁ a₂ :=
    .arrive a₁ ⟨0, p₂, s.time⟩ [] later rfl rfl free
  have raw₂ : a₂.raw 0 p₂ = some s.time := by
    simp [a₂, setRaw]
    rfl
  have rawOther (q : Port) (h : q ≠ p₂) : a₂.raw 0 q = a₁.raw 0 q :=
    raw_update_other a₁ 0 p₂ (some a₁.time) 0 q (Or.inr h)
  have raw₁ : a₂.raw 0 p₁ = some s.time := by
    rw [rawOther p₁ distinct]
    simp [a₁, setRaw]
  have raw₃ (q : Port) (h₁ : q ≠ p₁) (h₂ : q ≠ p₂) : a₂.raw 0 q = none := by
    rw [rawOther q h₂]
    exact (raw_update_other s 0 p₁ (some s.time) 0 q (Or.inr h₁)).trans (state.raw q)
  have live (q : Port) (hq : q = p₁ ∨ q = p₂) : a₂.raw 0 q = some s.time := by
    rcases hq with rfl | rfl
    · exact raw₁
    · exact raw₂
  have scale (q : Port) (hq : q = p₁ ∨ q = p₂) : rawScale a₂ q = 1 := by
    show rawInputScale (a₂.raw 0 q) s.time = 1
    rw [live q hq]
    simp [rawInputScale]
  have amplitude : drivenAmplitude a₂ = G := by
    unfold drivenAmplitude
    rw [Finset.sum_eq_add p₁ p₂ distinct
      (fun q _ hq => by rw [rawScale_none (raw₃ q hq.1 hq.2), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h),
      scale p₁ (Or.inl rfl), scale p₂ (Or.inr rfl), mul_one, mul_one]
    rfl
  have auxA (q : Port) : a₂.aux 0 q = .ready := state.aux q
  -- The planned MARK dates.
  have cross (q : Port) := box.first_sensor_crossing 0 q (state.sensors q).1 (state.sensors q).2
    (start := s.time)
  choose lat hlat using cross
  let M : Port → ℝ := fun q => s.time + lat q
  have sensorEq (q : Port) (hq : q = p₁ ∨ q = p₂) (t : ℝ) :
      drivenSensor θ a₂ q t = auxPulse (s.x 0 (.m q)) ((θ 0).inputGain q) s.time t := by
    rw [drivenSensor_ready (auxA q), scale q hq, mul_one]
    rfl
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
  have pulsed (q : Port) (h : a₂.raw 0 q ≠ none) : q = p₁ ∨ q = p₂ := by
    by_contra hn
    have hn' := not_or.mp hn
    exact h (raw₃ q hn'.1 hn'.2)
  have aboveAt (q : Port) (hq : q = p₁ ∨ q = p₂) : (θ 0).thresholds.error q <
      (4 / 5) * Real.exp (-(θ 0).ls q * (tf - (M q + decayTime 1 (4 / 5) ((θ 0).lm q)))) := by
    obtain ⟨lo, hi, _, _⟩ := errBand q hq
    have long : 1 < decayTime (4 / 5) ((θ 0).thresholds.error q) ((θ 0).ls q) :=
      (low_entry_silent_duration box q ⟨lo, hi⟩).1
    apply decay_above (by norm_num) (by linarith) (box.rates_positive 0 q).2.1
    have h := (hlat q).1
    linarith [(markSpan q).1]
  have plan : Plan θ a₂ M tf level := {
    driven := ⟨state.main, fun q => by rw [auxA q]; decide⟩
    time := after.le
    fire := config₁.fire
    mark := config₁.mark
    silent := config₁.silent
    charge := fun t ht => by
      rw [amplitude]
      exact first t ht
    raw := fun q o h => by
      rw [live q (pulsed q (by rw [h]; simp))] at h
      obtain rfl := Option.some.inj h
      exact ⟨le_rfl, tfLe⟩
    pending := fun d hd => by
      have h := laterDue d (by simpa [a₂] using hd)
      linarith
    quiet := fun q _ _ => lt_of_le_of_lt (state.sensors q).2 (by norm_num)
    ready := fun q _ hr => by
      have hq := pulsed q hr
      obtain ⟨_, quick, root, prior⟩ := hlat q
      refine ⟨by show s.time ≤ s.time + lat q; linarith [(hlat q).1], ?_, fun t ht => ?_, ?_⟩
      · show s.time + lat q + _ < tf
        linarith [(markSpan q).2]
      · rw [sensorEq q hq]
        exact prior t ht
      · rw [sensorEq q hq]
        exact root
    marked := fun q hm => by rw [auxA q] at hm; cases hm
    silenced := fun q hm => by rw [auxA q] at hm; cases hm
    above := fun q hb => by
      have hq : q = p₁ ∨ q = p₂ := by
        rcases hb with h | h
        · exact absurd (auxA q) h
        · exact pulsed q h
      rw [silentEnd_ready (auxA q)]
      exact aboveAt q hq }
  obtain ⟨e, run, fin⟩ := driven_run_exists box M tf level a₂ plan
  have pre : Runs θ s e 0 := (Runs.jump jump₁ rfl).append ((Runs.jump jump₂ rfl).append run)
  obtain ⟨preExec, _⟩ := id pre
  have inv := ParameterExecution.physical_invariant preExec
    (cell_threshold_bounds config₁.cell fire) box state.physical
  have eCharge : e.x 0 .q = level := by
    rw [fin.charge, amplitude]
    exact hit
  have busyOf (q : Port) (hq : q = p₁ ∨ q = p₂) : Busy a₂ q :=
    Or.inr (by rw [live q hq]; simp)
  have ports : ∀ q, FiredPort θ e s.time q := by
    intro q
    by_cases hq : q = p₁ ∨ q = p₂
    · obtain ⟨mode, value⟩ := fin.busy q (busyOf q hq)
      obtain ⟨lo, hi, floor, below⟩ := errBand q hq
      refine Or.inr ⟨mode, by rw [fin.raw]; exact live q hq, lo, hi, floor, below,
        M q + decayTime 1 (4 / 5) ((θ 0).lm q), ?_, ?_, ?_⟩
      · show s.time ≤ s.time + lat q + _
        linarith [(hlat q).1, (markSpan q).1]
      · show s.time + lat q + _ < s.time + 1 / 20
        linarith [(hlat q).2.1, (markSpan q).2]
      · rw [value, silentEnd_ready (auxA q), fin.time]
    · have hq := not_or.mp hq
      have idle : ¬ Busy a₂ q := by
        intro hb
        rcases hb with h | h
        · exact h (auxA q)
        · exact h (raw₃ q hq.1 hq.2)
      obtain ⟨mode, value⟩ := fin.idle q idle
      refine Or.inl ⟨mode, by rw [fin.raw]; exact raw₃ q hq.1 hq.2, ?_⟩
      rw [value, drivenSensor_ready (auxA q), rawScale_none (raw₃ q hq.1 hq.2), mul_zero,
        auxPulse_zero_eq_relax]
      exact relax_restBand after.le (state.sensors q)
  obtain ⟨u, tail, rested, date, pend, gains, b, charge⟩ :=
    fire_rest_exists (D := s.time) (rest := rest) box config₁.cell fire inv fin.main eCharge
      (by rw [fin.recovery]; exact recovery) (by rw [fin.time]; exact ⟨late.le, tfLe⟩) ports wait
      (by
        intro d hd
        rw [fin.queue] at hd
        exact laterDue d (by simpa [a₂] using hd))
  refine ⟨u, tf - s.time, ?_, ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩, rested, date, ?_,
    fun q => (gains q).trans (fin.gains q), b.trans fin.recovery, charge⟩
  · have whole := pre.emits.append tail
    rw [fin.time] at whole
    simpa using whole
  · rw [← readyPulse_shift]
    exact hit
  · intro t ht
    have h := first (s.time + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp only [pulse] at h
    rwa [readyPulse_shift, add_sub_cancel_left] at h
  · rw [pend, fin.queue]
    simp [a₂]

/-- The read of two ports after stop-learning training, as an execution.
Each gain fires alone from the exact rest charge, and one dose below it
was silent, with doses of at most 1/20. The joint read fires exactly
once, between 0.239 and 0.256 units after the pulses, whatever the two
gains and the FIRE level. Every complete run fires at that same date. -/
theorem stopped_joint_read {θ ε p₁ p₂ u₁ l₁ u₂ l₂ level rest} {s : Snapshot 1}
    {later : List (Delivery 1)} (box : @PhysicalBox 1 θ ε) (distinct : p₁ ≠ p₂)
    (config₁ : PortConfig θ p₁ u₁ l₁ level) (config₂ : PortConfig θ p₂ u₂ l₂ level)
    (fire : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (entry₁ : 7 / 100 ≤ u₁ ∧ u₁ ≤ 2 / 25) (exit₁ : 1 / 200 ≤ l₁ ∧ l₁ < u₁)
    (entry₂ : 7 / 100 ≤ u₂ ∧ u₂ ≤ 2 / 25) (exit₂ : 1 / 200 ≤ l₂ ∧ l₂ < u₂)
    (dose₁ : 8 * (u₁ - l₁) ≤ 1 / 20) (dose₂ : 8 * (u₂ - l₂) ≤ 1 / 20)
    (state : RestState θ s) (rested : s.x 0 .q = 1 / 10)
    (recovery : 7 / 100 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 1 / 10)
    (queue : s.pending =
      (⟨0, p₁, s.time⟩ : Delivery 1) :: (⟨0, p₂, s.time⟩ : Delivery 1) :: later)
    (wait : s.time + 22 ≤ rest) (laterDue : ∀ d ∈ later, rest ≤ d.due)
    (fires₁ : PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₁))) level)
    (fires₂ : PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₂))) level)
    (silent₁ : ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
      ¬ PulseFires c (Real.exp (s.x 0 (.z p₁) - 8 * (u₁ - l₁))) level)
    (silent₂ : ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
      ¬ PulseFires c (Real.exp (s.x 0 (.z p₂) - 8 * (u₂ - l₂))) level) :
    ∃ u latency, Emits θ s u [(0, s.time + latency)] ∧
      latency ∈ Ioc (239 / 1000 : ℝ) (32 / 125) ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = later ∧
      (∀ q, u.x 0 (.z q) = s.x 0 (.z q)) ∧ u.x 0 .b = s.x 0 .b ∧ u.x 0 .q = 1 / 10 ∧
      (later = [] → ∀ (v : Snapshot 1) (other : ParameterExecution θ (fun _ _ => []) s v),
        ParameterCompleteThrough other rest →
        u.ObservationalEq v ∧ other.emissionTimes 0 = [s.time + latency]) := by
  have hPos := response_one_pos
  have hLow := response_one_lower
  have step : (19 / 20 : ℝ) ≤ Real.exp (-(1 / 20 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 20 : ℝ))]
  -- Scalar facts for one port.
  have port (z d : ℝ) (dose : d ≤ 1 / 20)
      (fires : PulseFires (1 / 10) (Real.exp z) level)
      (silent : ∃ c, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 ∧
        ¬ PulseFires c (Real.exp (z - d)) level) :
      level ≤ 1 / 10 + Real.exp z * response 1 ∧
      1 / 10 + Real.exp z * Real.exp (-(1 / 20 : ℝ)) * response 1 < level ∧
      Real.exp z ≤ 2 := by
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
    have weaker : Real.exp z * Real.exp (-(1 / 20 : ℝ)) * response 1 ≤
        Real.exp z * Real.exp (-d) * response 1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left decay (Real.exp_pos z).le) hPos.le
    refine ⟨by linarith, by linarith, ?_⟩
    have floor : Real.exp z * (19 / 20) * (11 / 20) ≤
        Real.exp z * Real.exp (-(1 / 20 : ℝ)) * response 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left step (Real.exp_pos z).le) hLow (by norm_num)
        (mul_nonneg (Real.exp_pos z).le (Real.exp_pos _).le)
    nlinarith [Real.exp_pos z]
  obtain ⟨peak₁, low₁, cap₁⟩ := port _ _ dose₁ fires₁ silent₁
  obtain ⟨peak₂, low₂, cap₂⟩ := port _ _ dose₂ fires₂ silent₂
  let G := Real.exp (s.x 0 (.z p₁)) + Real.exp (s.x 0 (.z p₂))
  have Gpos : 0 < G := add_pos (Real.exp_pos _) (Real.exp_pos _)
  have joint : PulseFires (s.x 0 .q) G level := by
    apply pulseFires_of_peak (by rw [rested])
    have extra := mul_nonneg (Real.exp_pos (s.x 0 (.z p₂))).le hPos.le
    show level ≤ 1 / 10 + (Real.exp (s.x 0 (.z p₁)) + Real.exp (s.x 0 (.z p₂))) * response 1
    linarith
  obtain ⟨u, latency, emits, report, restedEnd, date, pend, gains, b, charge⟩ :=
    joint_read_exists box distinct config₁ config₂ fire entry₁ exit₁ entry₂ exit₂ state recovery
      queue wait laterDue (by linarith) joint
  rw [rested] at report
  have window := stopped_read_response_residual (gain := G) (c := 1 / 2) (fire := level)
    (d := 1 / 20) (δ := 0) (x := 1 / 20) (qFire := 1 / 10) (qSilent := 1 / 10)
    (qRead := 1 / 10) (tFire := 1) (t := latency) (by norm_num) Gpos (by linarith [fire.1])
    ⟨le_rfl, by norm_num⟩ le_rfl ⟨le_rfl, by norm_num⟩ le_rfl ⟨by norm_num, le_rfl⟩
    (by
      rw [readyPulse_at_rest]
      show level ≤ 1 / 10 + 1 / 2 *
        (Real.exp (s.x 0 (.z p₁)) + Real.exp (s.x 0 (.z p₂))) * response 1
      linarith)
    (by
      rw [readyPulse_at_rest]
      show 1 / 10 + 1 / 2 * ((Real.exp (s.x 0 (.z p₁)) + Real.exp (s.x 0 (.z p₂))) *
        Real.exp (-(1 / 20 : ℝ))) * response 1 < level
      linarith)
    report
  have gap : 0 < level - 1 / 10 := by linarith [fire.1]
  have lower : 1 / 2 * Real.exp (-(1 / 20 : ℝ)) * response 1 < response latency := by
    have h := window.1
    rw [sub_zero] at h
    exact lt_of_mul_lt_mul_right h gap.le
  have upper : response latency ≤ 1 / 2 * response 1 := by
    have h := window.2
    rw [sub_zero] at h
    exact le_of_mul_le_mul_right h gap
  have inside : latency ∈ Ioc (239 / 1000 : ℝ) (32 / 125) :=
    ⟨(response_strictMono_pulse.lt_iff_lt ⟨by norm_num, by norm_num⟩ report.live).mp
        (window_half.1.trans_lt lower),
      (response_strictMono_pulse.le_iff_le report.live ⟨by norm_num, by norm_num⟩).mp
        (upper.trans window_half.2)⟩
  refine ⟨u, latency, emits, inside, restedEnd, date, pend, gains, b, charge, ?_⟩
  intro none v other complete
  obtain ⟨e, he⟩ := emits
  have bounds := cell_threshold_bounds config₁.cell fire
  have done : ParameterCompleteThrough e rest :=
    date ▸ restedEnd.complete config₁ fire.1 e (pend.trans none)
  refine ⟨(ParameterExecution.observational_unique box bounds e other state.physical done
    complete).1, ?_⟩
  rw [← ParameterExecution.emissionTimes_unique e other box bounds state.physical done complete 0]
  simp [ParameterExecution.emissionTimes, he]

theorem emissionTimes_append {θ : Fin 1 → Parameters} {s u v : Snapshot 1}
    (e : ParameterExecution θ (fun _ _ => []) s u) (f : ParameterExecution θ (fun _ _ => []) u v) :
    (e.append f).emissionTimes 0 = e.emissionTimes 0 ++ f.emissionTimes 0 := by
  simp [ParameterExecution.emissionTimes, execution_emissions_append]

/-- Training and read in one execution. Two ports of a rested cell start
from gains that do not fire. Each is trained by its own train of pulses,
with a dose of at most 1/20, until it stops by itself. One pulse on each
port then reads the cell. The read FIRE comes between 0.239 and 0.256
units after the read pulses, whatever the start gains and the FIRE
level. Every complete run has the same FIRE dates and the same end. -/
theorem trained_read_exists {θ ε p₁ p₂ u₁ l₁ u₂ l₂ level}
    {dates₁ dates₂ : List ℝ} {s : Snapshot 1} {middle readDate rest : ℝ}
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
            [(⟨0, p₁, readDate⟩ : Delivery 1), (⟨0, p₂, readDate⟩ : Delivery 1)])))
    (spaced₁ : Spaced s.time dates₁ middle) (spaced₂ : Spaced middle dates₂ readDate)
    (wait : readDate + 22 ≤ rest)
    (below₁ : ¬ PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₁))) level)
    (below₂ : ¬ PulseFires (1 / 10) (Real.exp (s.x 0 (.z p₂))) level)
    (r₁ r₂ : ℕ)
    (reach₁ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₁) + r₁ * (8 * (u₁ - l₁))) * response 1)
    (reach₂ : level ≤ 1 / 10 + Real.exp (s.x 0 (.z p₂) + r₂ * (8 * (u₂ - l₂))) * response 1)
    (enough₁ : 2 * r₁ + 2 ≤ dates₁.length + 1) (enough₂ : 2 * r₂ + 2 ≤ dates₂.length + 1) :
    ∃ (u : Snapshot 1) (latency : ℝ) (training : List ℝ),
      latency ∈ Ioc (239 / 1000 : ℝ) (32 / 125) ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) s u,
        e.emissionTimes 0 = training ++ [readDate + latency]) ∧
      RestState θ u ∧ u.time = rest ∧ u.pending = [] ∧
      (∃ k : ℕ, k ≤ dates₁.length + 1 ∧ u.x 0 (.z p₁) = s.x 0 (.z p₁) + k * (8 * (u₁ - l₁))) ∧
      (∃ k : ℕ, k ≤ dates₂.length + 1 ∧ u.x 0 (.z p₂) = s.x 0 (.z p₂) + k * (8 * (u₂ - l₂))) ∧
      ∀ (v : Snapshot 1) (other : ParameterExecution θ (fun _ _ => []) s v),
        ParameterCompleteThrough other rest →
        u.ObservationalEq v ∧ other.emissionTimes 0 = training ++ [readDate + latency] := by
  obtain ⟨m, f, ⟨e₁, _⟩, rested, date, pend, charge, b, _, gain₁, gain₂, fires₁, fires₂, last₁,
      last₂, _⟩ :=
    two_port_training_exists
      (tail := [(⟨0, p₁, readDate⟩ : Delivery 1), (⟨0, p₂, readDate⟩ : Delivery 1)])
      box distinct config₁ config₂ fire entry₁ exit₁ entry₂ exit₂ state recovery queue spaced₁
      spaced₂ (by
        intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> exact le_rfl)
      r₁ r₂ reach₁ reach₂ enough₁ enough₂
  have silent₁ := last₁.resolve_left (fun same => below₁ (same ▸ fires₁))
  have silent₂ := last₂.resolve_left (fun same => below₂ (same ▸ fires₂))
  obtain ⟨u, latency, ⟨e₂, emitted⟩, inside, restedEnd, dateEnd, pendEnd, gains, _, _, _⟩ :=
    stopped_joint_read (later := []) (rest := rest) box distinct config₁ config₂ fire entry₁
      exit₁ entry₂ exit₂ dose₁ dose₂ rested charge (by rw [b]; exact recovery)
      (by rw [pend, date]) (by rw [date]; exact wait) (by intro d hd; cases hd)
      fires₁ fires₂ silent₁ silent₂
  have times : (e₁.append e₂).emissionTimes 0 = e₁.emissionTimes 0 ++ [readDate + latency] := by
    rw [emissionTimes_append]
    congr 1
    simp [ParameterExecution.emissionTimes, emitted, date]
  refine ⟨u, latency, e₁.emissionTimes 0, inside, ⟨e₁.append e₂, times⟩, restedEnd, dateEnd,
    pendEnd, ?_, ?_, ?_⟩
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
