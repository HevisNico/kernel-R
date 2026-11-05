import KernelR.Family.Constants
import KernelR.HybridSnapshotObservational

/-! Parametric native first-contact semantics. The state types and queue
operations are those of the original kernel; all fixed dynamics/guard constants
are explicit inputs. No latency, event count, or output schedule is assumed. -/
namespace KernelR.Family
open KernelR.Hybrid MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def pulse (c : Constants) (origin t : ℝ) : ℝ :=
  if origin ≤ t ∧ t < origin + c.pulseWidth then
    c.a * Real.exp (-c.a * (t-origin)) else 0

noncomputable def current {n} (c : Constants) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  match s.raw i p with
  | none => 0
  | some origin => pulse c origin t

noncomputable def errorAct {n} (c : Constants) (θ : Fin n → Parameters)
    (s : Snapshot n) (x : Values n) (i : Fin n) (p : Port) : ℝ :=
  if s.aux i p = .error ∧ s.main i = .ready ∧ 0 < x i .energy ∧
      x i (.z p) < Real.log ((θ i).cap p) then
    c.gainFactor * (θ i).le p * x i (.m p) else 0

noncomputable def markAct {n} (c : Constants) (θ : Fin n → Parameters)
    (s : Snapshot n) (x : Values n) (i : Fin n) (p : Port) : ℝ :=
  if s.aux i p = .mark ∧ s.main i ≠ .ready ∧ 0 < x i .energy ∧
      x i .b < c.recoveryCap then
    c.recoveryFactor * (θ i).lm p * x i (.m p) else 0

noncomputable def drive {n} (c : Constants) (s : Snapshot n)
    (x : Values n) (i : Fin n) (t : ℝ) : ℝ :=
  ∑ p : Port, Real.exp (x i (.z p)) * current c s i p t

noncomputable def work {n} (c : Constants) (θ : Fin n → Parameters)
    (s : Snapshot n) (x : Values n) (i : Fin n) (t : ℝ) : ℝ :=
  (match s.main i with
   | .ready => drive c s x i t
   | .fast => c.a * x i .q
   | .slow => c.slowWork) +
  (∑ p : Port, if s.aux i p = .ready then
      (θ i).inputGain p * current c s i p t
    else auxDrain (θ i) (s.aux i p) p (x i (.m p))) +
  (∑ p : Port, errorAct c θ s x i p) + ∑ p : Port, markAct c θ s x i p

noncomputable def field {n} (c : Constants) (θ : Fin n → Parameters)
    (s : Snapshot n) (x : Values n) (t : ℝ) (i : Fin n) : Coord → ℝ
  | .q => match s.main i with
    | .ready => c.kappa * (c.rest-x i .q) + drive c s x i t
    | .fast => -c.a * x i .q
    | .slow => -x i .b * x i .q
  | .m p => if s.aux i p = .ready then
      c.kappa * (c.auxRest-x i (.m p)) + (θ i).inputGain p * current c s i p t
    else -auxDrain (θ i) (s.aux i p) p (x i (.m p))
  | .z p => errorAct c θ s x i p
  | .b => ∑ p : Port, markAct c θ s x i p
  | .energy => c.energyRate * (c.energyTarget-x i .energy) - work c θ s x i t

def BeforeGuards {n} (c : Constants) (s : Snapshot n) (x : Values n) : Prop :=
  (∀ i, match s.main i with
    | .ready => x i .q < c.threshold
    | .fast => c.fastExit < x i .q
    | .slow => c.rest < x i .q) ∧
  (∀ i p, match s.aux i p with
    | .ready => x i (.m p) < c.auxThreshold
    | .mark => c.markExit < x i (.m p)
    | .silent => c.errorLevel < x i (.m p)
    | .error => c.auxRest < x i (.m p))

structure Flow {n} (c : Constants) (θ : Fin n → Parameters) (s u : Snapshot n) where
  positive : s.time < u.time
  path : ℝ → Values n
  initial : path s.time = s.x
  final : path u.time = u.x
  main_fixed : u.main = s.main
  aux_fixed : u.aux = s.aux
  raw_fixed : u.raw = s.raw
  queue_fixed : u.pending = s.pending
  continuous : ∀ i k, ContinuousOn (fun t => path t i k) (Set.Icc s.time u.time)
  integrable : ∀ i k, IntervalIntegrable (fun t => field c θ s (path t) t i k)
    volume s.time u.time
  mark_integrable : ∀ i p, IntervalIntegrable (fun t => markAct c θ s (path t) i p)
    volume s.time u.time
  integral_eq : ∀ t ∈ Set.Icc s.time u.time, ∀ i k,
    path t i k = s.x i k + ∫ v in s.time..t, field c θ s (path v) v i k
  guards : ∀ t ∈ Set.Ico s.time u.time, BeforeGuards c s (path t)
  raw_support : ∀ i p origin, s.raw i p = some origin →
    origin ≤ s.time ∧ u.time ≤ origin+c.pulseWidth
  pending_urgent : ∀ d ∈ s.pending, u.time ≤ d.due

/-- Explicit physical domain for flow uniqueness. It does not assume equality,
uniqueness, a formula for any trajectory, or protocol-specific numerical bounds. -/
def Flow.Safe {n c θ s u} (f : @Flow n c θ s u) : Prop :=
  ∀ t ∈ Set.Icc s.time u.time, ∀ i,
    0 < f.path t i .energy ∧ 0 ≤ f.path t i .b ∧ ∀ p, 0 ≤ f.path t i (.m p)

inductive Jump {n} (c : Constants) (route : Router n) : Snapshot n → Snapshot n → Type
  | fire (s : Snapshot n) (i : Fin n) (mode : s.main i = .ready)
      (guard : s.x i .q = c.threshold) :
      Jump c route s { (setMain s i .fast) with pending := s.pending ++ route i s.time }
  | fastEnd (s : Snapshot n) (i : Fin n) (mode : s.main i = .fast)
      (guard : s.x i .q = c.fastExit) : Jump c route s (setMain s i .slow)
  | reopen (s : Snapshot n) (i : Fin n) (mode : s.main i = .slow)
      (guard : s.x i .q = c.rest) : Jump c route s (setMain s i .ready)
  | mark (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .ready)
      (guard : s.x i (.m p) = c.auxThreshold) : Jump c route s (setAux s i p .mark)
  | silent (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .mark)
      (guard : s.x i (.m p) = c.markExit) : Jump c route s (setAux s i p .silent)
  | error (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .silent)
      (guard : s.x i (.m p) = c.errorLevel) : Jump c route s (setAux s i p .error)
  | auxReady (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .error)
      (guard : s.x i (.m p) = c.auxRest) : Jump c route s (setAux s i p .ready)
  | arrive (s : Snapshot n) (d : Delivery n) (before after : List (Delivery n))
      (queue : s.pending = before ++ d :: after) (due : d.due = s.time)
      (free : s.raw d.cell d.port = none) :
      Jump c route s { (setRaw s d.cell d.port (some s.time)) with pending := before ++ after }
  | rawEnd (s : Snapshot n) (i : Fin n) (p : Port) (origin : ℝ)
      (active : s.raw i p = some origin) (due : s.time = origin+c.pulseWidth) :
      Jump c route s (setRaw s i p none)

theorem Jump.physical_continuous {n c route s u} (j : @Jump n c route s u) : u.x=s.x := by
  cases j <;> rfl

theorem Jump.time_unchanged {n c route s u} (j : @Jump n c route s u) : u.time=s.time := by
  cases j <;> rfl

inductive Move {n} (c : Constants) (θ : Fin n → Parameters) (route : Router n)
    (s u : Snapshot n) : Type
  | flow : Flow c θ s u → Move c θ route s u
  | jump : Jump c route s u → Move c θ route s u

inductive Execution {n} (c : Constants) (θ : Fin n → Parameters) (route : Router n) :
    Snapshot n → Snapshot n → Type
  | nil (s) : Execution c θ route s s
  | cons {s u v} : Move c θ route s u → Execution c θ route u v → Execution c θ route s v

def Execution.append {n c θ route s u v} :
    @Execution n c θ route s u → Execution c θ route u v → Execution c θ route s v
  | .nil _, rest => rest
  | .cons move tail, rest => .cons move (tail.append rest)

def CompleteThrough {n c θ route s u} (_e : @Execution n c θ route s u) (T : ℝ) : Prop :=
  u.time=T ∧ (∀ v, IsEmpty (Jump c route u v)) ∧ ∀ d ∈ u.pending, T<d.due

end KernelR.Family
