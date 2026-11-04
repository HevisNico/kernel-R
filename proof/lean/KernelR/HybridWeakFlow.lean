import KernelR.Hybrid

/-! Integral flows whose READY upper guards permit a threshold touch.
All other guards, raw-support bounds and queue urgency are unchanged. -/
namespace KernelR.Hybrid
open MeasureTheory

def WeakBeforeGuards {n} (s : Snapshot n) (x : Values n) : Prop :=
  (∀ i, match s.main i with
    | .ready => x i .q ≤ 1
    | .fast => 1 / 4 < x i .q
    | .slow => 1 / 10 < x i .q) ∧
  (∀ i p, match s.aux i p with
    | .ready => x i (.m p) ≤ 1
    | .mark => 4 / 5 < x i (.m p)
    | .silent => 1 / 10 < x i (.m p)
    | .error => 1 / 40 < x i (.m p))

theorem BeforeGuards.toWeak {n s x} (guards : @BeforeGuards n s x) :
    WeakBeforeGuards s x := by
  constructor
  · intro i
    have h := guards.1 i
    cases mode : s.main i <;> simp_all
    exact h.le
  · intro i p
    have h := guards.2 i p
    cases mode : s.aux i p <;> simp_all
    exact h.le

structure WeakFlow {n} (θ : Fin n → Parameters) (s u : Snapshot n) where
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
  guards : ∀ t ∈ Set.Ico s.time u.time, WeakBeforeGuards s (path t)
  raw_support : ∀ i p origin, s.raw i p = some origin →
    origin ≤ s.time ∧ u.time ≤ origin + 1
  pending_urgent : ∀ d ∈ s.pending, u.time ≤ d.due

def Flow.toWeak {n θ s u} (flow : @Flow n θ s u) : WeakFlow θ s u where
  positive := flow.positive
  path := flow.path
  initial := flow.initial
  final := flow.final
  main_fixed := flow.main_fixed
  aux_fixed := flow.aux_fixed
  raw_fixed := flow.raw_fixed
  queue_fixed := flow.queue_fixed
  continuous := flow.continuous
  integrable := flow.integrable
  mark_integrable := flow.mark_integrable
  integral_eq := flow.integral_eq
  guards := fun t ht => (flow.guards t ht).toWeak
  raw_support := flow.raw_support
  pending_urgent := flow.pending_urgent

end KernelR.Hybrid
