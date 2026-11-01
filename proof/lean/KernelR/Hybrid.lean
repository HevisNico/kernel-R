import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Pulses-only operational semantics. No pulse-case words or dose counters occur
in the admissibility relation. Existence for the certified protocol is not yet
proved. Time-zero jump interleavings have no prescribed priority. -/
namespace KernelR.Hybrid
open MeasureTheory
attribute [local instance] Classical.propDecidable
abbrev Port := Fin 3
inductive MainMode where
  | ready | fast | slow
  deriving DecidableEq
inductive AuxMode where
  | ready | mark | silent | error
  deriving DecidableEq
inductive Coord where
  | q | m (p : Port) | z (p : Port) | b | energy
  deriving DecidableEq
abbrev Values (n : ℕ) := Fin n → Coord → ℝ
structure Parameters where
  cap : Port → ℝ
  lm : Port → ℝ
  ls : Port → ℝ
  le : Port → ℝ
  inputGain : Port → ℝ
structure Delivery (n : ℕ) where
  cell : Fin n
  port : Port
  due : ℝ
structure Snapshot (n : ℕ) where
  time : ℝ
  x : Values n
  main : Fin n → MainMode
  aux : Fin n → Port → AuxMode
  raw : Fin n → Port → Option ℝ
  pending : List (Delivery n)
abbrev Router (n : ℕ) := Fin n → ℝ → List (Delivery n)
/-- Delay causality is a separate condition on the supplied wiring. -/
def CausalRouter {n} (route : Router n) : Prop :=
  ∀ i t d, d ∈ route i t → t ≤ d.due
noncomputable def a : ℝ := Real.log 4
noncomputable def pulse (origin t : ℝ) : ℝ :=
  if origin ≤ t ∧ t < origin + 1 then a * Real.exp (-a * (t - origin)) else 0
noncomputable def current {n} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  match s.raw i p with
  | none => 0
  | some origin => pulse origin t
noncomputable def errorAct {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (i : Fin n) (p : Port) : ℝ :=
  if s.aux i p = .error ∧ s.main i = .ready ∧ 0 < x i .energy ∧
      x i (.z p) < Real.log ((θ i).cap p) then
    8 * (θ i).le p * x i (.m p) else 0
noncomputable def markAct {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (i : Fin n) (p : Port) : ℝ :=
  if s.aux i p = .mark ∧ s.main i ≠ .ready ∧ 0 < x i .energy ∧ x i .b < 11 / 10 then
    (1 / 2) * (θ i).lm p * x i (.m p) else 0
noncomputable def auxDrain (θ : Parameters) (mode : AuxMode) (p : Port) (m : ℝ) : ℝ :=
  match mode with
  | .ready => 0
  | .mark => θ.lm p * m
  | .silent => θ.ls p * m
  | .error => θ.le p * m
noncomputable def drive {n} (s : Snapshot n) (x : Values n) (i : Fin n) (t : ℝ) : ℝ :=
  ∑ p : Port, Real.exp (x i (.z p)) * current s i p t
noncomputable def work {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (i : Fin n) (t : ℝ) : ℝ :=
  (match s.main i with
   | .ready => drive s x i t
   | .fast => a * x i .q
   | .slow => 11 / 10) +
  (∑ p : Port, if s.aux i p = .ready then (θ i).inputGain p * current s i p t
    else auxDrain (θ i) (s.aux i p) p (x i (.m p))) +
  (∑ p : Port, errorAct θ s x i p) + ∑ p : Port, markAct θ s x i p
noncomputable def field {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (t : ℝ) (i : Fin n) : Coord → ℝ
  | .q => match s.main i with
    | .ready => (1 / 2) * (1 / 10 - x i .q) + drive s x i t
    | .fast => -a * x i .q
    | .slow => -x i .b * x i .q
  | .m p => if s.aux i p = .ready then
      (1 / 2) * (1 / 40 - x i (.m p)) + (θ i).inputGain p * current s i p t
    else -auxDrain (θ i) (s.aux i p) p (x i (.m p))
  | .z p => errorAct θ s x i p
  | .b => ∑ p : Port, markAct θ s x i p
  | .energy => 10 * (100 - x i .energy) - work θ s x i t

/-- Independent fixed fabrication boxes; no equality between cells or ports. -/
noncomputable def response (t : ℝ) : ℝ :=
  a / (a - 1 / 2) * (Real.exp (-(1 / 2) * t) - Real.exp (-a * t))
def InRelativeBox (ε nominal value : ℝ) : Prop :=
  nominal * (1 - ε) ≤ value ∧ value ≤ nominal * (1 + ε)
def PhysicalBox {n} (θ : Fin n → Parameters) (ε : ℝ) : Prop :=
  (ε = 3 / 1000 ∨ ε = 1 / 10) ∧ ∀ i p,
    InRelativeBox ε 4 ((θ i).cap p) ∧
    InRelativeBox ε (Real.log (5 / 4) / (1 / 50)) ((θ i).lm p) ∧
    InRelativeBox ε (Real.log 8 / (53 / 50)) ((θ i).ls p) ∧
    InRelativeBox ε (a / (3 / 20)) ((θ i).le p) ∧
    InRelativeBox ε ((1 - 1 / 40) / response (1 / 50)) ((θ i).inputGain p)
noncomputable def nominalGain (p : Port) : ℝ := if p = 1 then 6 / 5 else 3 / 10
/-- Common birth at zero. The caller must separately fix the pending source
queue to the supplied protocol, so no unlisted delayed source can be hidden. -/
def BirthState {n} (s : Snapshot n) : Prop :=
  s.time = 0 ∧ (∀ i p, s.raw i p = none) ∧ ∀ i,
    s.main i = .ready ∧
    (1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 10 + 1 / 100000) ∧
    (2 / 25 - 1 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 2 / 25 + 1 / 100000) ∧
    (50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100) ∧ ∀ p,
    (Real.log (nominalGain p) - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (nominalGain p) + 1 / 100000) ∧
    ((s.aux i p = .ready ∧ 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧
        s.x i (.m p) ≤ 1 / 40 + 1 / 100000) ∨
     (s.aux i p = .error ∧ 1 / 40 ≤ s.x i (.m p) ∧
        s.x i (.m p) ≤ 1 / 40 + 1 / 100000))

/-- Strict interior guards: reaching a section cannot be passed in the old mode. -/
def BeforeGuards {n} (s : Snapshot n) (x : Values n) : Prop :=
  (∀ i, match s.main i with
    | .ready => x i .q < 1
    | .fast => 1 / 4 < x i .q
    | .slow => 1 / 10 < x i .q) ∧
  (∀ i p, match s.aux i p with
    | .ready => x i (.m p) < 1
    | .mark => 4 / 5 < x i (.m p)
    | .silent => 1 / 10 < x i (.m p)
    | .error => 1 / 40 < x i (.m p))

/-- Integral ODEs apply to every prefix of a positive-duration flow. -/
structure Flow {n} (θ : Fin n → Parameters) (s u : Snapshot n) where
  positive : s.time < u.time
  path : ℝ → Values n
  initial : path s.time = s.x
  final : path u.time = u.x
  main_fixed : u.main = s.main
  aux_fixed : u.aux = s.aux
  raw_fixed : u.raw = s.raw
  queue_fixed : u.pending = s.pending
  continuous : ∀ i c, ContinuousOn (fun t => path t i c) (Set.Icc s.time u.time)
  integrable : ∀ i c, IntervalIntegrable (fun t => field θ s (path t) t i c)
    volume s.time u.time
  mark_integrable : ∀ i p, IntervalIntegrable (fun t => markAct θ s (path t) i p)
    volume s.time u.time
  integral_eq : ∀ t ∈ Set.Icc s.time u.time, ∀ i c,
    path t i c = s.x i c + ∫ v in s.time..t, field θ s (path v) v i c
  guards : ∀ t ∈ Set.Ico s.time u.time, BeforeGuards s (path t)
  raw_support : ∀ i p origin, s.raw i p = some origin →
    origin ≤ s.time ∧ u.time ≤ origin + 1
  pending_urgent : ∀ d ∈ s.pending, u.time ≤ d.due

/-- All state updates below preserve physical coordinates and time. -/
def setMain {n} (s : Snapshot n) (i : Fin n) (mode : MainMode) : Snapshot n :=
  { s with main := Function.update s.main i mode }
def setAux {n} (s : Snapshot n) (i : Fin n) (p : Port) (mode : AuxMode) : Snapshot n :=
  { s with aux := Function.update s.aux i (Function.update (s.aux i) p mode) }
def setRaw {n} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ) : Snapshot n :=
  { s with raw := Function.update s.raw i (Function.update (s.raw i) p origin) }
inductive Jump {n} (route : Router n) : Snapshot n → Snapshot n → Type
  | fire (s : Snapshot n) (i : Fin n) (mode : s.main i = .ready) (guard : s.x i .q = 1) :
      Jump route s { (setMain s i .fast) with pending := s.pending ++ route i s.time }
  | fastEnd (s : Snapshot n) (i : Fin n) (mode : s.main i = .fast)
      (guard : s.x i .q = 1 / 4) : Jump route s (setMain s i .slow)
  | reopen (s : Snapshot n) (i : Fin n) (mode : s.main i = .slow)
      (guard : s.x i .q = 1 / 10) : Jump route s (setMain s i .ready)
  | mark (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .ready)
      (guard : s.x i (.m p) = 1) : Jump route s (setAux s i p .mark)
  | silent (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .mark)
      (guard : s.x i (.m p) = 4 / 5) : Jump route s (setAux s i p .silent)
  | error (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .silent)
      (guard : s.x i (.m p) = 1 / 10) : Jump route s (setAux s i p .error)
  | auxReady (s : Snapshot n) (i : Fin n) (p : Port) (mode : s.aux i p = .error)
      (guard : s.x i (.m p) = 1 / 40) : Jump route s (setAux s i p .ready)
  | arrive (s : Snapshot n) (d : Delivery n) (before after : List (Delivery n))
      (queue : s.pending = before ++ d :: after) (due : d.due = s.time)
      (free : s.raw d.cell d.port = none) :
      Jump route s { (setRaw s d.cell d.port (some s.time)) with pending := before ++ after }
  | rawEnd (s : Snapshot n) (i : Fin n) (p : Port) (origin : ℝ)
      (active : s.raw i p = some origin) (due : s.time = origin + 1) :
      Jump route s (setRaw s i p none)
inductive Move {n} (θ : Fin n → Parameters) (route : Router n)
    (s u : Snapshot n) : Type
  | flow : Flow θ s u → Move θ route s u
  | jump : Jump route s u → Move θ route s u
inductive Execution {n} (θ : Fin n → Parameters) (route : Router n) :
    Snapshot n → Snapshot n → Type
  | nil (s) : Execution θ route s s
  | cons {s u v} : Move θ route s u → Execution θ route u v → Execution θ route s v
/-- Terminal saturation includes guards and deliveries exactly at the horizon.
This defines a target class, not an existence or non-Zeno theorem. -/
def CompleteThrough {n θ route s u} (_e : @Execution n θ route s u) (T : ℝ) : Prop :=
  u.time = T ∧ (∀ v, IsEmpty (Jump route u v)) ∧ ∀ d ∈ u.pending, T < d.due
end KernelR.Hybrid
