import Std

/-! A conditional deterministic safety contract. No theorem here certifies a
SPICE netlist or infers a uniform physical envelope from sampled trajectories.
Integer units are chosen by a later physical refinement, rounding outwards. -/
namespace Sky130Supervisor

structure Bounds where
  S : Int
  H : Int
  Dmin : Int
  Dmax : Int
  linearCapacity : Int
  semanticCapacity : Int
  epsilon : Int
  deriving Repr

def capacity (b : Bounds) : Int := min b.linearCapacity b.semanticCapacity

def WellFormed (b : Bounds) : Prop :=
  0 ≤ b.S ∧ 0 ≤ b.H ∧ 0 ≤ b.epsilon ∧ b.H ≤ b.Dmin ∧
  b.Dmin ≤ b.Dmax ∧
  b.S + 2*b.H + 2*b.epsilon + b.Dmax ≤ capacity b

def Ready (b : Bounds) (lower : Int) : Prop := b.S + b.H ≤ lower
instance (b : Bounds) (lower : Int) : Decidable (Ready b lower) := inferInstanceAs (Decidable (_ ≤ _))

structure State where
  reserve : Int
  carry : Int
  deriving Repr

def Invariant (b : Bounds) (s : State) : Prop :=
  Ready b s.carry ∧ s.carry ≤ s.reserve ∧ s.reserve ≤ capacity b

inductive Action where
  | wait | maintenance | refuse
  deriving Repr, DecidableEq

def lower (b : Bounds) (s : State) (report : Int) : Int :=
  max (report-b.epsilon) s.carry

def upper (b : Bounds) (report : Int) : Int := min (report+b.epsilon) (capacity b)

def choose (b : Bounds) (lo hi : Int) : Action :=
  if Ready b lo ∧ lo ≤ hi then
    if hi+b.Dmax ≤ capacity b then .maintenance
    else if b.S+2*b.H ≤ lo then .wait else .refuse
  else .refuse

def Certified (b : Bounds) (lo hi : Int) (a : Action) : Prop :=
  Ready b lo ∧ lo ≤ hi ∧ match a with
  | .wait => b.S+2*b.H ≤ lo
  | .maintenance => hi+b.Dmax ≤ capacity b
  | .refuse => False

/-- Returned lower carry uses Dmin; the overflow guard uses Dmax. -/
def nextCarry (b : Bounds) (lo : Int) : Action → Int
  | .wait => lo-b.H
  | .maintenance => lo-b.H+b.Dmin
  | .refuse => 0

def post (reserve loss dose : Int) : Action → Int
  | .wait => reserve-loss
  | .maintenance => reserve-loss+dose
  | .refuse => reserve

/-- One period has one mandatory service before the possible maintenance dose.
`reserve-loss` is the conservative floor before that dose; the physical bridge
must enclose all cumulative loss before every required service by the same H. -/
def preService (reserve loss : Int) : Int := reserve-loss

def step (b : Bounds) (s : State) (report loss dose : Int) : State :=
  let lo := lower b s report
  let a := choose b lo (upper b report)
  ⟨post s.reserve loss dose a, nextCarry b lo a⟩

theorem capacity_respects_both (b : Bounds) :
    capacity b ≤ b.linearCapacity ∧ capacity b ≤ b.semanticCapacity := by
  simp only [capacity]; omega

theorem observation_encloses (b : Bounds) (s : State) (report : Int)
    (inv : Invariant b s) (sensor : -b.epsilon ≤ report-s.reserve ∧ report-s.reserve ≤ b.epsilon) :
    lower b s report ≤ s.reserve ∧ s.reserve ≤ upper b report ∧
    upper b report-lower b s report ≤ 2*b.epsilon ∧ Ready b (lower b s report) := by
  rcases inv with ⟨ready, carry, cap⟩
  unfold lower upper Ready at *
  omega

theorem choose_certified (b : Bounds) (lo hi : Int)
    (wf : WellFormed b) (ready : Ready b lo) (ordered : lo ≤ hi)
    (width : hi-lo ≤ 2*b.epsilon) : Certified b lo hi (choose b lo hi) := by
  rcases wf with ⟨_, _, _, _, _, room⟩
  unfold choose
  rw [ite_eq_left ⟨ready, ordered⟩]
  split
  · exact ⟨ready, ordered, by assumption⟩
  · rename_i noRoom
    have enough : b.S+2*b.H ≤ lo := by omega
    rw [ite_eq_left enough]
    exact ⟨ready, ordered, enough⟩

theorem certified_not_refuse (b : Bounds) (lo hi : Int) (a : Action)
    (cert : Certified b lo hi a) : a ≠ .refuse := by
  cases a <;> simp_all [Certified]

theorem maintenance_guard_is_mandatory (b : Bounds) (lo hi : Int)
    (selected : choose b lo hi = .maintenance) : hi+b.Dmax ≤ capacity b := by
  unfold choose at selected
  split at selected
  · split at selected
    · assumption
    · split at selected <;> contradiction
  · contradiction

theorem maintenance_no_overflow (b : Bounds) (actual hi loss dose : Int)
    (enclosed : actual ≤ hi) (lossNonnegative : 0 ≤ loss) (doseUpper : dose ≤ b.Dmax)
    (guard : hi+b.Dmax ≤ capacity b) : actual-loss+dose ≤ capacity b := by omega

theorem segment_safe (b : Bounds) (s : State) (lo hi loss dose : Int) (a : Action)
    (wf : WellFormed b) (inv : Invariant b s) (enclosed : lo ≤ s.reserve ∧ s.reserve ≤ hi)
    (lossBound : 0 ≤ loss ∧ loss ≤ b.H) (doseBound : b.Dmin ≤ dose ∧ dose ≤ b.Dmax)
    (cert : Certified b lo hi a) :
    b.S ≤ preService s.reserve loss ∧
    Invariant b ⟨post s.reserve loss dose a, nextCarry b lo a⟩ := by
  rcases wf with ⟨_, hnonneg, _, restores, _, _⟩
  rcases inv with ⟨_, _, cap⟩
  rcases cert with ⟨ready, _, actionGuard⟩
  cases a <;> simp only [preService, post, nextCarry, Invariant, Ready] at *
  · omega
  · omega

theorem step_safe (b : Bounds) (s : State) (report loss dose : Int)
    (wf : WellFormed b) (inv : Invariant b s)
    (sensor : -b.epsilon ≤ report-s.reserve ∧ report-s.reserve ≤ b.epsilon)
    (lossBound : 0 ≤ loss ∧ loss ≤ b.H) (doseBound : b.Dmin ≤ dose ∧ dose ≤ b.Dmax) :
    b.S ≤ preService s.reserve loss ∧ Invariant b (step b s report loss dose) := by
  obtain ⟨lo, hi, width, ready⟩ := observation_encloses b s report inv sensor
  have ordered : lower b s report ≤ upper b report := by omega
  have cert := choose_certified b (lower b s report) (upper b report) wf ready ordered width
  exact segment_safe b s _ _ loss dose _ wf inv ⟨lo, hi⟩ lossBound doseBound cert

structure World where
  loss : Nat → Int
  dose : Nat → Int
  error : Nat → Int

/-- Deterministic physical/sensor enclosure, not supplied by finite simulations. -/
def Enclosed (b : Bounds) (w : World) : Prop := ∀ n,
  (0 ≤ w.loss n ∧ w.loss n ≤ b.H) ∧
  (b.Dmin ≤ w.dose n ∧ w.dose n ≤ b.Dmax) ∧
  (-b.epsilon ≤ w.error n ∧ w.error n ≤ b.epsilon)

def run (b : Bounds) (w : World) (entry : State) : Nat → State
  | 0 => entry
  | n+1 => let s := run b w entry n
           step b s (s.reserve+w.error n) (w.loss n) (w.dose n)

theorem run_invariant (b : Bounds) (w : World) (entry : State)
    (wf : WellFormed b) (environment : Enclosed b w) (start : Invariant b entry) :
    ∀ n, Invariant b (run b w entry n) := by
  intro n; induction n with
  | zero => exact start
  | succ n ih =>
    obtain ⟨loss, dose, error⟩ := environment n
    have obs : -b.epsilon ≤ (run b w entry n).reserve+w.error n-(run b w entry n).reserve ∧
        (run b w entry n).reserve+w.error n-(run b w entry n).reserve ≤ b.epsilon := by omega
    exact (step_safe b _ _ _ _ wf ih obs loss dose).2

theorem every_service_safe (b : Bounds) (w : World) (entry : State)
    (wf : WellFormed b) (environment : Enclosed b w) (start : Invariant b entry) (n : Nat) :
    b.S ≤ preService (run b w entry n).reserve (w.loss n) := by
  have inv := run_invariant b w entry wf environment start n
  obtain ⟨loss, dose, error⟩ := environment n
  have obs : -b.epsilon ≤ (run b w entry n).reserve+w.error n-(run b w entry n).reserve ∧
      (run b w entry n).reserve+w.error n-(run b w entry n).reserve ≤ b.epsilon := by omega
  exact (step_safe b _ _ _ _ wf inv obs loss dose).1

theorem every_boundary_respects_semantic_capacity (b : Bounds) (w : World) (entry : State)
    (wf : WellFormed b) (environment : Enclosed b w) (start : Invariant b entry) (n : Nat) :
    (run b w entry n).reserve ≤ b.semanticCapacity := by
  have inv := run_invariant b w entry wf environment start n
  have cap := capacity_respects_both b
  unfold Invariant at inv
  omega

theorem no_refusal_in_enclosed_domain (b : Bounds) (w : World) (entry : State)
    (wf : WellFormed b) (environment : Enclosed b w) (start : Invariant b entry) (n : Nat) :
    let s := run b w entry n
    choose b (lower b s (s.reserve+w.error n)) (upper b (s.reserve+w.error n)) ≠ .refuse := by
  have inv := run_invariant b w entry wf environment start n
  obtain ⟨_, _, error⟩ := environment n
  have obs : -b.epsilon ≤ (run b w entry n).reserve+w.error n-(run b w entry n).reserve ∧
      (run b w entry n).reserve+w.error n-(run b w entry n).reserve ≤ b.epsilon := by omega
  obtain ⟨lo, hi, width, ready⟩ := observation_encloses b _ _ inv obs
  exact certified_not_refuse b _ _ _ (choose_certified b _ _ wf ready (by omega) width)

/-- No SPICE behavior is inferred by this interface. Its service implication
must be justified separately for the new calendar, observation/state map,
recovery status, and semantic capacity. It covers all periods, not only probes. -/
structure PhysicalRefinement (b : Bounds) (w : World) (entry : State) where
  serviceSucceeded : Nat → Prop
  timingReady : Nat → Prop
  recovery : ∀ n, timingReady n
  service_of_margin : ∀ n, timingReady n →
    b.S ≤ preService (run b w entry n).reserve (w.loss n) →
    (run b w entry n).reserve ≤ b.semanticCapacity → serviceSucceeded n

theorem refined_zero_failed_services (b : Bounds) (w : World) (entry : State)
    (wf : WellFormed b) (environment : Enclosed b w) (start : Invariant b entry)
    (bridge : PhysicalRefinement b w entry) : ∀ n, bridge.serviceSucceeded n := by
  intro n
  have inv := run_invariant b w entry wf environment start n
  have cap := capacity_respects_both b
  exact bridge.service_of_margin n (bridge.recovery n)
    (every_service_safe b w entry wf environment start n) (by unfold Invariant at inv; omega)

inductive PreparationEvent where
  | maintenance | observation
  deriving Repr, DecidableEq

def preparationMaintenance : List PreparationEvent → Nat
  | [] => 0
  | .maintenance :: rest => 1+preparationMaintenance rest
  | .observation :: rest => preparationMaintenance rest

def preparationObservations : List PreparationEvent → Nat
  | [] => 0
  | .maintenance :: rest => preparationObservations rest
  | .observation :: rest => 1+preparationObservations rest

def preparationCost (maintenancePrice observationPrice : Nat) : List PreparationEvent → Nat
  | [] => 0
  | .maintenance :: rest => maintenancePrice+preparationCost maintenancePrice observationPrice rest
  | .observation :: rest => observationPrice+preparationCost maintenancePrice observationPrice rest

theorem preparation_cost_exact (events : List PreparationEvent) (cm co : Nat) :
    preparationCost cm co events = preparationMaintenance events*cm+preparationObservations events*co := by
  induction events with
  | nil => simp [preparationCost, preparationMaintenance, preparationObservations]
  | cons event rest ih =>
    cases event <;> simp only [preparationCost, preparationMaintenance, preparationObservations,
      Nat.add_mul, Nat.one_mul] at * <;> omega

theorem preparation_cost_length_bound (events : List PreparationEvent) (cm co : Nat) :
    preparationCost cm co events ≤ events.length*(cm+co) := by
  induction events with
  | nil => simp [preparationCost]
  | cons event rest ih =>
    cases event <;> simp only [preparationCost, List.length_cons, Nat.add_mul, Nat.one_mul] at * <;> omega

theorem preparation_budget (events : List PreparationEvent) (cm co budget : Nat)
    (bounded : events.length ≤ budget) : preparationCost cm co events ≤ budget*(cm+co) := by
  have cost := preparation_cost_length_bound events cm co
  have length := Nat.mul_le_mul_right (cm+co) bounded
  omega

/-- A validated maintenance in preparation advances reserve by at least Dmin-H.
This is conditional on actuation and loss bounds, not a proof of startup timing. -/
theorem preparation_progress (b : Bounds) (x loss dose : Int)
    (lossBound : loss ≤ b.H) (doseBound : b.Dmin ≤ dose) :
    b.Dmin-b.H ≤ post x loss dose .maintenance-x := by
  simp only [post]; omega

/-- Chronological preparation: observations do not move reserve; every
clock-only dose requires a sound upper observation and the same Dmax guard.
No service success is required during this charged, pre-contract phase. -/
inductive PreparationTrace (b : Bounds) : Int → Int → List PreparationEvent → Prop where
  | nil (x : Int) : PreparationTrace b x x []
  | observation {initial x : Int} {events : List PreparationEvent}
      (history : PreparationTrace b initial x events) (report : Int)
      (sensor : -b.epsilon ≤ report-x ∧ report-x ≤ b.epsilon) :
      PreparationTrace b initial x (events ++ [.observation])
  | maintenance {initial x : Int} {events : List PreparationEvent}
      (history : PreparationTrace b initial x events) (report loss dose : Int)
      (sensor : -b.epsilon ≤ report-x ∧ report-x ≤ b.epsilon)
      (lossBound : 0 ≤ loss ∧ loss ≤ b.H)
      (doseBound : b.Dmin ≤ dose ∧ dose ≤ b.Dmax)
      (room : report+b.epsilon+b.Dmax ≤ capacity b) :
      PreparationTrace b initial (x-loss+dose) (events ++ [.maintenance])

theorem guarded_preparation_step (b : Bounds) (x report loss dose : Int)
    (sensor : -b.epsilon ≤ report-x ∧ report-x ≤ b.epsilon)
    (lossBound : 0 ≤ loss ∧ loss ≤ b.H)
    (doseBound : b.Dmin ≤ dose ∧ dose ≤ b.Dmax)
    (guard : report+b.epsilon+b.Dmax ≤ capacity b) :
    x+b.Dmin-b.H ≤ x-loss+dose ∧ x-loss+dose ≤ capacity b := by omega

theorem preparation_trace_respects_capacity (b : Bounds) (initial final : Int)
    (events : List PreparationEvent) (start : initial ≤ capacity b)
    (trace : PreparationTrace b initial final events) : final ≤ capacity b := by
  induction trace with
  | nil => exact start
  | observation history report sensor ih => exact ih
  | maintenance history report loss dose sensor lossBound doseBound room ih =>
    exact (guarded_preparation_step b _ report loss dose sensor lossBound doseBound room).2

/-- A fresh interval certificate is required at the end of preparation. -/
structure EntryCertificate (b : Bounds) where
  initial : Int
  actual : Int
  report : Int
  preparation : List PreparationEvent
  initialFits : initial ≤ capacity b
  preparationValid : PreparationTrace b initial actual preparation
  sensor : -b.epsilon ≤ report-actual ∧ report-actual ≤ b.epsilon
  lowerReady : Ready b (report-b.epsilon)
  upperFits : report+b.epsilon ≤ capacity b

def EntryCertificate.state {b : Bounds} (entry : EntryCertificate b) : State :=
  ⟨entry.actual, entry.report-b.epsilon⟩

theorem entry_certificate_valid (b : Bounds) (entry : EntryCertificate b) :
    Invariant b entry.state := by
  change Ready b (entry.report-b.epsilon) ∧ entry.report-b.epsilon ≤ entry.actual ∧ entry.actual ≤ capacity b
  have h := entry.sensor
  have cap := entry.upperFits
  exact ⟨entry.lowerReady, by omega, by omega⟩

theorem certified_preparation_respects_capacity (b : Bounds) (entry : EntryCertificate b) :
    entry.actual ≤ capacity b := by
  exact preparation_trace_respects_capacity b entry.initial entry.actual entry.preparation
    entry.initialFits entry.preparationValid

inductive Phase where
  | preparation | guaranteedService
  deriving DecidableEq, Repr

structure Record where
  phase : Phase
  fired : Bool
  deriving Repr

def serviceFailure (r : Record) : Bool := r.phase == .guaranteedService && !r.fired

theorem preparation_silence_is_not_a_service (fired : Bool) :
    serviceFailure ⟨.preparation, fired⟩ = false := by simp [serviceFailure]

def chargedCost (maintenancePrice observationPrice servicePrice : Nat)
    (prepMaintenance prepObservations maintenance observations services : Nat) : Nat :=
  (prepMaintenance+maintenance)*maintenancePrice +
  (prepObservations+observations)*observationPrice + services*servicePrice

theorem preparation_cost_is_charged (pm po m o n cm co cs : Nat) :
    chargedCost cm co cs pm po m o n =
    pm*cm+po*co+chargedCost cm co cs 0 0 m o n := by
  simp [chargedCost, Nat.add_mul]; omega

theorem finite_cost_budget (pm po m o n cm co cs : Nat)
    (maintenance : m ≤ n) (observations : o ≤ n+1) :
    chargedCost cm co cs pm po m o n ≤
    pm*cm+po*co+n*cm+(n+1)*co+n*cs := by
  have hm := Nat.mul_le_mul_right cm maintenance
  have ho := Nat.mul_le_mul_right co observations
  simp only [chargedCost, Nat.add_mul, Nat.one_mul] at *
  omega

def actionAt (b : Bounds) (w : World) (entry : State) (n : Nat) : Action :=
  let s := run b w entry n
  choose b (lower b s (s.reserve+w.error n)) (upper b (s.reserve+w.error n))

def maintenanceCount (b : Bounds) (w : World) (entry : State) : Nat → Nat
  | 0 => 0
  | n+1 => maintenanceCount b w entry n + if actionAt b w entry n = .maintenance then 1 else 0

theorem maintenance_count_bounded (b : Bounds) (w : World) (entry : State) :
    ∀ n, maintenanceCount b w entry n ≤ n := by
  intro n; induction n with
  | zero => simp [maintenanceCount]
  | succ n ih =>
    simp only [maintenanceCount]
    split <;> omega

def totalRunCost (b : Bounds) (w : World) (entry : EntryCertificate b) (n cm co cs : Nat) : Nat :=
  preparationCost cm co entry.preparation + maintenanceCount b w entry.state n*cm + (n+1)*co+n*cs

theorem total_run_cost_contains_preparation (b : Bounds) (w : World) (entry : EntryCertificate b) (n cm co cs : Nat) :
    preparationCost cm co entry.preparation ≤ totalRunCost b w entry n cm co cs := by
  unfold totalRunCost
  omega

theorem actual_run_cost_bounded (b : Bounds) (w : World) (entry : EntryCertificate b) (n cm co cs : Nat) :
    totalRunCost b w entry n cm co cs ≤
    preparationCost cm co entry.preparation + n*cm+(n+1)*co+n*cs := by
  have h := Nat.mul_le_mul_right cm (maintenance_count_bounded b w entry.state n)
  unfold totalRunCost
  omega

theorem certified_entry_run_safe (b : Bounds) (w : World) (entry : EntryCertificate b)
    (wf : WellFormed b) (environment : Enclosed b w) :
    ∀ n, b.S ≤ preService (run b w entry.state n).reserve (w.loss n) := by
  exact every_service_safe b w entry.state wf environment (entry_certificate_valid b entry)

/-- All rejections are about observed loss and have no Gaussian hard-bound claim. -/
theorem measured_loss_violation_sound (b : Bounds) (actual report errorBound : Int)
    (error : report-actual ≤ errorBound) (violation : b.H < report-errorBound) : b.H < actual := by omega

/-- Optional observed-loss monitor. A voltage-only implementation must first
justify the error/window of this accumulated-loss report; H is not read from
an injected simulator parameter. -/
def monitoredChoice (b : Bounds) (lo hi lossReport lossError : Int) : Action :=
  if b.H < lossReport-lossError then .refuse else choose b lo hi

theorem observed_violation_refuses (b : Bounds) (lo hi report errorBound : Int)
    (violation : b.H < report-errorBound) : monitoredChoice b lo hi report errorBound = .refuse := by
  simp [monitoredChoice, violation]

theorem no_false_alarm_inside_boundary (b : Bounds) (lo hi actual report errorBound : Int)
    (within : actual ≤ b.H) (error : report-actual ≤ errorBound) :
    monitoredChoice b lo hi report errorBound = choose b lo hi := by
  have noViolation : ¬ b.H < report-errorBound := by omega
  simp [monitoredChoice, noViolation]

end Sky130Supervisor
