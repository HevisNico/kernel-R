import KernelR.Hybrid

/-! Threshold-dependent execution, with the same integral dynamics and
snapshot updates as the nominal protocol proofs. The realized parameter
vector is fixed across every jump and every segment. -/
namespace KernelR.Hybrid

structure ParameterFlow {n} (θ : Fin n → Parameters) (s u : Snapshot n)
    extends FlowDynamics θ s u where
  guards : ∀ t ∈ Set.Ico s.time u.time,
    ThresholdGuards (fun i => (θ i).thresholds) s (path t)

inductive ParameterJump {n} (θ : Fin n → Parameters) (route : Router n) : Snapshot n → Snapshot n → Type
  | fire (s : Snapshot n) (i : Fin n) (mode : s.main i = .ready) (guard : s.x i .q = (θ i).thresholds.fire) :
      ParameterJump θ route s { (setMain s i .fast) with pending := s.pending ++ route i s.time }
  | fastEnd (s : Snapshot n) (i : Fin n) (mode : s.main i = .fast)
      (guard : s.x i .q = (θ i).thresholds.fastEnd) : ParameterJump θ route s (setMain s i .slow)
  | reopen (s : Snapshot n) (i : Fin n) (mode : s.main i = .slow)
      (guard : s.x i .q = (θ i).thresholds.reopen) : ParameterJump θ route s (setMain s i .ready)
  | mark (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .ready)
      (guard : s.x i (.m p) = (θ i).thresholds.mark p) : ParameterJump θ route s (setAux s i p .mark)
  | silent (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .mark)
      (guard : s.x i (.m p) = (θ i).thresholds.silent p) : ParameterJump θ route s (setAux s i p .silent)
  | error (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .silent)
      (guard : s.x i (.m p) = (θ i).thresholds.error p) : ParameterJump θ route s (setAux s i p .error)
  | auxReady (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .error)
      (guard : s.x i (.m p) = (θ i).thresholds.auxReady p) : ParameterJump θ route s (setAux s i p .ready)
  | arrive (s : Snapshot n) (d : Delivery n) (before after : List (Delivery n))
      (queue : s.pending = before ++ d :: after) (due : d.due = s.time)
      (free : s.raw d.cell d.port = none) :
      ParameterJump θ route s { (setRaw s d.cell d.port (some s.time)) with pending := before ++ after }
  | rawEnd (s : Snapshot n) (i : Fin n) (p : Port) (origin : ℝ)
      (active : s.raw i p = some origin) (due : s.time = origin + 1) :
      ParameterJump θ route s (setRaw s i p none)

inductive ParameterMove {n} (θ : Fin n → Parameters) (route : Router n)
    (s u : Snapshot n) : Type
  | flow : ParameterFlow θ s u → ParameterMove θ route s u
  | jump : ParameterJump θ route s u → ParameterMove θ route s u

inductive ParameterExecution {n} (θ : Fin n → Parameters) (route : Router n) :
    Snapshot n → Snapshot n → Type
  | nil (s) : ParameterExecution θ route s s
  | cons {s u v} : ParameterMove θ route s u → ParameterExecution θ route u v →
      ParameterExecution θ route s v

/-- The original protocol thresholds are a fixed instance of the parameters. -/
def NominalThresholds {n} (θ : Fin n → Parameters) : Prop :=
  ∀ i, (θ i).thresholds = Thresholds.nominal

/-- Terminal urgency uses the same realized thresholds as the moves. -/
def ParameterCompleteThrough {n θ route s u}
    (_e : @ParameterExecution n θ route s u) (T : ℝ) : Prop :=
  u.time = T ∧ (∀ v, IsEmpty (ParameterJump θ route u v)) ∧ ∀ d ∈ u.pending, T < d.due

def ParameterExecution.append {n θ route s u v}
    (e : @ParameterExecution n θ route s u) (f : ParameterExecution θ route u v) :
    ParameterExecution θ route s v :=
  match e with
  | .nil _ => f
  | .cons m r => .cons m (r.append f)

theorem nominal_guard_iff {n θ} (nominal : @NominalThresholds n θ) (s : Snapshot n) (x : Values n) :
    ThresholdGuards (fun i => (θ i).thresholds) s x ↔ BeforeGuards s x := by
  rw [show (fun i => (θ i).thresholds) = (fun _ => Thresholds.nominal) from funext nominal]
  rfl

def ParameterJump.emissions {n θ route s u} (j : @ParameterJump n θ route s u) :
    List (Fin n × ℝ) := by
  cases j with
  | fire i _ _ => exact [(i, s.time)]
  | _ => exact []

def ParameterExecution.emissions {n θ route s u} : @ParameterExecution n θ route s u → List (Fin n × ℝ)
  | .nil _ => []
  | .cons (.flow _) rest => rest.emissions
  | .cons (.jump j) rest => j.emissions ++ rest.emissions

def ParameterExecution.emissionTimes {n θ route s u}
    (e : @ParameterExecution n θ route s u) (i : Fin n) : List ℝ :=
  (e.emissions.filter (fun event => event.1 = i)).map Prod.snd

def Flow.toParameter {n θ s u} (f : @Flow n θ s u) (nominal : NominalThresholds θ) :
    ParameterFlow θ s u where
  toFlowDynamics := f.toFlowDynamics
  guards := by
    intro t ht
    exact (nominal_guard_iff nominal s _).2 (f.guards t ht)

def ParameterFlow.toNominal {n θ s u} (f : @ParameterFlow n θ s u)
    (nominal : NominalThresholds θ) : Flow θ s u where
  toFlowDynamics := f.toFlowDynamics
  guards := by
    intro t ht
    exact (nominal_guard_iff nominal s _).1 (f.guards t ht)

def Jump.toParameter {n θ route s u} (j : @Jump n route s u)
    (nominal : NominalThresholds θ) : ParameterJump θ route s u := by
  cases j with
  | fire i m g => exact .fire _ i m (by simpa [nominal i] using g)
  | fastEnd i m g => exact .fastEnd _ i m (by simpa [nominal i] using g)
  | reopen i m g => exact .reopen _ i m (by simpa [nominal i] using g)
  | mark i p m g => exact .mark _ i p m (by simpa [nominal i] using g)
  | silent i p m g => exact .silent _ i p m (by simpa [nominal i] using g)
  | error i p m g => exact .error _ i p m (by simpa [nominal i] using g)
  | auxReady i p m g => exact .auxReady _ i p m (by simpa [nominal i] using g)
  | arrive d b a q t f => exact .arrive _ d b a q t f
  | rawEnd i p o a d => exact .rawEnd _ i p o a d

def ParameterJump.toNominal {n θ route s u} (j : @ParameterJump n θ route s u)
    (nominal : NominalThresholds θ) : Jump route s u := by
  cases j with
  | fire i m g => exact .fire _ i m (by simpa [nominal i] using g)
  | fastEnd i m g => exact .fastEnd _ i m (by simpa [nominal i] using g)
  | reopen i m g => exact .reopen _ i m (by simpa [nominal i] using g)
  | mark i p m g => exact .mark _ i p m (by simpa [nominal i] using g)
  | silent i p m g => exact .silent _ i p m (by simpa [nominal i] using g)
  | error i p m g => exact .error _ i p m (by simpa [nominal i] using g)
  | auxReady i p m g => exact .auxReady _ i p m (by simpa [nominal i] using g)
  | arrive d b a q t f => exact .arrive _ d b a q t f
  | rawEnd i p o a d => exact .rawEnd _ i p o a d

def Execution.toParameter {n θ route s u} (e : @Execution n θ route s u)
    (nominal : NominalThresholds θ) : ParameterExecution θ route s u :=
  match e with
  | .nil s => .nil s
  | .cons (.flow f) rest => .cons (.flow (f.toParameter nominal)) (rest.toParameter nominal)
  | .cons (.jump j) rest => .cons (.jump (j.toParameter nominal)) (rest.toParameter nominal)

def ParameterExecution.toNominal {n θ route s u} (e : @ParameterExecution n θ route s u)
    (nominal : NominalThresholds θ) : Execution θ route s u :=
  match e with
  | .nil s => .nil s
  | .cons (.flow f) rest => .cons (.flow (f.toNominal nominal)) (rest.toNominal nominal)
  | .cons (.jump j) rest => .cons (.jump (j.toNominal nominal)) (rest.toNominal nominal)

theorem ParameterExecution.complete_nominal_iff {n θ route s u T}
    (e : @ParameterExecution n θ route s u) (nominal : NominalThresholds θ) :
    ParameterCompleteThrough e T ↔ CompleteThrough (e.toNominal nominal) T := by
  constructor
  · rintro ⟨time, h, due⟩
    exact ⟨time, fun v => ⟨fun j => (h v).false (j.toParameter nominal)⟩, due⟩
  · rintro ⟨time, h, due⟩
    exact ⟨time, fun v => ⟨fun j => (h v).false (j.toNominal nominal)⟩, due⟩

/-- A strict snapshot with no due delivery or expiry has no enabled jump. -/
theorem Snapshot.no_parameter_jump {n θ route} (s : Snapshot n)
    (h : ThresholdGuards (fun i => (θ i).thresholds) s s.x)
    (pending : ∀ d ∈ s.pending, s.time < d.due)
    (raw : ∀ i p o, s.raw i p = some o → s.time < o + 1)
    (v : Snapshot n) : IsEmpty (ParameterJump θ route s v) := by
  constructor
  intro j
  cases j with
  | fire i m q | fastEnd i m q | reopen i m q =>
    have hq := h.1 i
    rw [m, q] at hq
    exact (lt_irrefl _) hq
  | mark i p m q | silent i p m q | error i p m q | auxReady i p m q =>
    have hq := h.2 i p
    rw [m, q] at hq
    exact (lt_irrefl _) hq
  | arrive d b a q t free =>
    have hd : d ∈ s.pending := by simp [q]
    linarith [pending d hd]
  | rawEnd i p o a t =>
    linarith [raw i p o a]

/-- No fixed realized guard, delivery or expiry may be bypassed by time. -/
theorem ParameterFlow.no_initial_jump {n θ route s u} (f : @ParameterFlow n θ s u)
    (v : Snapshot n) : IsEmpty (ParameterJump θ route s v) := by
  have h := f.guards s.time ⟨le_rfl, f.positive⟩
  rw [f.initial] at h
  exact s.no_parameter_jump h
    (fun d hd => f.positive.trans_le (f.pending_urgent d hd))
    (fun i p o ho => f.positive.trans_le (f.raw_support i p o ho).2) v

/-- Expiry and ERROR entry at the same date commute exactly, including
at the same port. Neither move changes the other's guard. -/
theorem ParameterJump.error_expiry_commute {n θ route} {s : Snapshot n}
    (i j : Fin n) (p q : Port) (origin : ℝ)
    (mode : s.aux i p = .silent) (contact : s.x i (.m p) = (θ i).thresholds.error p)
    (active : s.raw j q = some origin) (due : s.time = origin + 1) :
    Nonempty (ParameterJump θ route (setAux s i p .error)
      (setRaw (setAux s i p .error) j q none)) ∧
    Nonempty (ParameterJump θ route (setRaw s j q none)
      (setRaw (setAux s i p .error) j q none)) := by
  exact ⟨⟨.rawEnd _ j q origin active due⟩, ⟨.error _ i p mode contact⟩⟩

end KernelR.Hybrid
