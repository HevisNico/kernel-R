import SelfCertifyingLearning.Budget

/-! Executable interval hysteresis. The monitor reads reports only; true
parameter values occur solely in the soundness/accounting specification. -/
namespace SelfCertifyingLearning.Renewal

structure Interval where
  lo : Nat
  hi : Nat
  ordered : lo ≤ hi
  deriving DecidableEq, Repr

def Interval.Contains (report : Interval) (value : Nat) : Prop :=
  report.lo ≤ value ∧ value ≤ report.hi

/-- Bounded-error scalar measurement, including saturation of the lower
endpoint at zero for the nonnegative parameter (not for signed reserve). -/
def measurement (value radius : Nat) : Interval :=
  ⟨value - radius, value + radius, by omega⟩

/-- Renewing a report does not by itself invalidate the search memory.
A reopening needs separation of the entire uncertainty intervals. -/
def Separated (granularity : Nat) (anchor next : Interval) : Prop :=
  anchor.hi + granularity ≤ next.lo ∨ next.hi + granularity ≤ anchor.lo

instance (g : Nat) (a b : Interval) : Decidable (Separated g a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

def review (g : Nat) (anchor next : Interval) : Interval × Bool :=
  if Separated g anchor next then (next, true) else (anchor, false)

def reopenings (g : Nat) (anchor : Interval) : List Interval → Nat
  | [] => 0
  | next :: rest =>
    if Separated g anchor next then 1 + reopenings g next rest
    else reopenings g anchor rest

/-- Absolute distance, in the same integer ticks as the observations. -/
def distance (a b : Nat) : Nat := (a - b) + (b - a)

theorem measurement_honest (value radius truth : Nat)
    (noise : distance value truth ≤ radius) : (measurement value radius).Contains truth := by
  unfold distance at noise
  unfold measurement Interval.Contains
  dsimp only
  omega

theorem distance_self (a : Nat) : distance a a = 0 := by simp [distance]

theorem distance_triangle (a b c : Nat) :
    distance a c ≤ distance a b + distance b c := by unfold distance; omega

theorem separated_cost {g a b x y} (first : Interval.Contains a x)
    (second : Interval.Contains b y) (apart : Separated g a b) :
    g ≤ distance x y := by
  unfold Interval.Contains at first second
  unfold Separated at apart
  unfold distance
  omega

/-- The monitor is not merely protected against false alarms: movement
larger than granularity plus both report widths is detected on this visit. -/
theorem detects_resolvable_change {g a b x y}
    (first : Interval.Contains a x) (second : Interval.Contains b y)
    (movement : g + (a.hi - a.lo) + (b.hi - b.lo) ≤ distance x y) :
    review g a b = (b, true) := by
  have apart : Separated g a b := by
    have ha := a.ordered
    have hb := b.ordered
    unfold Interval.Contains at first second
    unfold distance at movement
    unfold Separated
    omega
  simp [review, apart]

/-- The simulator/proof supplies truth; review and reopenings never read it. -/
structure Sample where
  report : Interval
  truth : Nat
  honest : report.Contains truth

def variation (previous : Nat) : List Sample → Nat
  | [] => 0
  | sample :: rest => distance previous sample.truth + variation sample.truth rest

/-- Ghost ledger: sample-to-sample variation is injected once; a genuine
reopening spends at least g ticks. A renewal is an idle event. -/
def events (g : Nat) (anchor : Interval) (previous : Nat) : List Sample → List Event
  | [] => []
  | sample :: rest =>
    .disturbance (distance previous sample.truth) ::
      if Separated g anchor sample.report then
        .correction :: events g sample.report sample.truth rest
      else .idle :: events g anchor sample.truth rest

theorem events_corrections (g anchor previous samples) :
    corrections (events g anchor previous samples) =
      reopenings g anchor (samples.map Sample.report) := by
  induction samples generalizing anchor previous with
  | nil => rfl
  | cons sample rest ih =>
    simp only [events, List.map_cons, reopenings]
    split <;> simp [corrections, ih]

theorem events_injected (g anchor previous samples) :
    injected (events g anchor previous samples) = variation previous samples := by
  induction samples generalizing anchor previous with
  | nil => rfl
  | cons sample rest ih =>
    simp only [events, variation]
    split <;> simp [injected, ih]

/-- The charge is derived from honest interval separation and the triangle
inequality, not assumed as an extra transition contract. The anchor's true
value is frozen until a reopening, so adjacent epochs cannot reuse drift. -/
theorem charged_execution (g : Nat) (anchor : Interval) (anchorTruth previous credit : Nat)
    (honest : anchor.Contains anchorTruth) (covered : distance anchorTruth previous ≤ credit)
    (samples : List Sample) : ∃ final, Run g credit (events g anchor previous samples) final := by
  induction samples generalizing anchor anchorTruth previous credit with
  | nil => exact ⟨credit, .nil credit⟩
  | cons sample rest ih =>
    have travel := distance_triangle anchorTruth previous sample.truth
    by_cases apart : Separated g anchor sample.report
    · have charge := separated_cost honest sample.honest apart
      obtain ⟨final, tail⟩ := ih sample.report sample.truth sample.truth 0 sample.honest
        (by simp [distance])
      refine ⟨final, ?_⟩
      simp only [events, ite_eq_left apart]
      exact .disturbance (Nat.le_refl _) (.correction (by omega) tail)
    · obtain ⟨final, tail⟩ := ih anchor anchorTruth sample.truth
        (credit + distance previous sample.truth) honest (by omega)
      refine ⟨final, ?_⟩
      simp only [events, ite_eq_right apart]
      exact .disturbance (Nat.le_refl _) (.idle (Nat.le_refl _) tail)

/-- Any finite sequence of honest reports: the monitor's reopen count is
bounded by actual sampled variation, including arbitrary report widths. -/
theorem reopening_bound (g : Nat) (initial : Sample) (samples : List Sample) :
    g * reopenings g initial.report (samples.map Sample.report) ≤
      variation initial.truth samples := by
  obtain ⟨final, run⟩ := charged_execution g initial.report initial.truth initial.truth 0
    initial.honest (by simp [distance]) samples
  have bound := run.correction_bound
  rw [events_corrections, events_injected] at bound
  simpa using bound

theorem no_reopen_of_overlap {g a b value} (positive : 0 < g)
    (first : Interval.Contains a value) (second : Interval.Contains b value) :
    review g a b = (a, false) := by
  have no : ¬ Separated g a b := by
    intro apart
    have := separated_cost first second apart
    simp [distance] at this
    omega
  simp [review, no]

/-- Even changing noisy reports cannot reopen in a constant honest world. -/
theorem constant_world_no_reopen (g : Nat) (positive : 0 < g)
    (anchor : Interval) (value : Nat) (first : anchor.Contains value)
    (reports : List Interval) (honest : ∀ report ∈ reports, report.Contains value) :
    reopenings g anchor reports = 0 := by
  induction reports with
  | nil => rfl
  | cons report rest ih =>
    have second := honest report (by simp)
    have no : ¬ Separated g anchor report := by
      intro apart
      have := separated_cost first second apart
      simp [distance] at this
      omega
    simp only [reopenings, ite_eq_right no]
    exact ih (by intro r hr; exact honest r (by simp [hr]))

/-- Positive granularity is necessary: identical exact reports otherwise
trigger a reopening. This is a control, not a supported configuration. -/
theorem zero_granularity_reopens :
    review 0 ⟨5, 5, by decide⟩ ⟨5, 5, by decide⟩ = (⟨5, 5, by decide⟩, true) := by decide

end SelfCertifyingLearning.Renewal
