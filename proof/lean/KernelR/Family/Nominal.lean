import KernelR.Family.Model

/-! Exact bridge to the existing operational kernel. Coordinates, modes,
raw origins, queues and flow paths are unchanged. This is not merely an
agreement of terminal numerical values. -/
namespace KernelR.Family
open KernelR.Hybrid

@[simp] theorem pulse_nominal (origin t : ℝ) :
    pulse nominal origin t = Hybrid.pulse origin t := rfl

@[simp] theorem current_nominal {n} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    current nominal s i p t = Hybrid.current s i p t := rfl

@[simp] theorem errorAct_nominal {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (i : Fin n) (p : Port) :
    errorAct nominal θ s x i p = Hybrid.errorAct θ s x i p := rfl

@[simp] theorem markAct_nominal {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (i : Fin n) (p : Port) :
    markAct nominal θ s x i p = Hybrid.markAct θ s x i p := rfl

@[simp] theorem field_nominal {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (t : ℝ) (i : Fin n) (k : Coord) :
    field nominal θ s x t i k = Hybrid.field θ s x t i k := rfl

@[simp] theorem beforeGuards_nominal {n} (s : Snapshot n) (x : Values n) :
    BeforeGuards nominal s x ↔ Hybrid.BeforeGuards s x := Iff.rfl

def Flow.toNative {n θ s u} (f : @Flow n nominal θ s u) : Hybrid.Flow θ s u :=
  { positive := f.positive, path := f.path, initial := f.initial, final := f.final,
    main_fixed := f.main_fixed, aux_fixed := f.aux_fixed, raw_fixed := f.raw_fixed,
    queue_fixed := f.queue_fixed, continuous := f.continuous, integrable := f.integrable,
    mark_integrable := f.mark_integrable, integral_eq := f.integral_eq,
    guards := f.guards, raw_support := f.raw_support, pending_urgent := f.pending_urgent }

def Flow.ofNative {n θ s u} (f : @Hybrid.Flow n θ s u) : Flow nominal θ s u :=
  { positive := f.positive, path := f.path, initial := f.initial, final := f.final,
    main_fixed := f.main_fixed, aux_fixed := f.aux_fixed, raw_fixed := f.raw_fixed,
    queue_fixed := f.queue_fixed, continuous := f.continuous, integrable := f.integrable,
    mark_integrable := f.mark_integrable, integral_eq := f.integral_eq,
    guards := f.guards, raw_support := f.raw_support, pending_urgent := f.pending_urgent }

def Jump.toNative {n route s u} (j : @Jump n nominal route s u) : Hybrid.Jump route s u := by
  cases j with
  | fire i mode guard => exact .fire _ i mode guard
  | fastEnd i mode guard => exact .fastEnd _ i mode guard
  | reopen i mode guard => exact .reopen _ i mode guard
  | mark i p mode guard => exact .mark _ i p mode guard
  | silent i p mode guard => exact .silent _ i p mode guard
  | error i p mode guard => exact .error _ i p mode guard
  | auxReady i p mode guard => exact .auxReady _ i p mode guard
  | arrive d before after queue due free => exact .arrive _ d before after queue due free
  | rawEnd i p origin active due => exact .rawEnd _ i p origin active due

def Jump.ofNative {n route s u} (j : @Hybrid.Jump n route s u) : Jump nominal route s u := by
  cases j with
  | fire i mode guard => exact .fire _ i mode guard
  | fastEnd i mode guard => exact .fastEnd _ i mode guard
  | reopen i mode guard => exact .reopen _ i mode guard
  | mark i p mode guard => exact .mark _ i p mode guard
  | silent i p mode guard => exact .silent _ i p mode guard
  | error i p mode guard => exact .error _ i p mode guard
  | auxReady i p mode guard => exact .auxReady _ i p mode guard
  | arrive d before after queue due free => exact .arrive _ d before after queue due free
  | rawEnd i p origin active due => exact .rawEnd _ i p origin active due

def Move.toNative {n θ route s u} : @Move n nominal θ route s u → Hybrid.Move θ route s u
  | .flow f => .flow f.toNative
  | .jump j => .jump j.toNative

def Move.ofNative {n θ route s u} : @Hybrid.Move n θ route s u → Move nominal θ route s u
  | .flow f => .flow (Flow.ofNative f)
  | .jump j => .jump (Jump.ofNative j)

def Execution.toNative {n θ route s u} :
    @Execution n nominal θ route s u → Hybrid.Execution θ route s u
  | .nil s => .nil s
  | .cons move rest => .cons move.toNative rest.toNative

def Execution.ofNative {n θ route s u} :
    @Hybrid.Execution n θ route s u → Execution nominal θ route s u
  | .nil s => .nil s
  | .cons move rest => .cons (Move.ofNative move) (Execution.ofNative rest)

theorem Flow.toNative_path {n θ s u} (f : @Flow n nominal θ s u) :
    f.toNative.path = f.path := rfl

theorem execution_exists_iff {n θ route s u} :
    Nonempty (@Execution n nominal θ route s u) ↔ Nonempty (Hybrid.Execution θ route s u) :=
  ⟨fun ⟨e⟩ => ⟨e.toNative⟩, fun ⟨e⟩ => ⟨Execution.ofNative e⟩⟩

theorem completeThrough_iff {n θ route s u} (e : @Execution n nominal θ route s u) (T : ℝ) :
    CompleteThrough e T ↔ Hybrid.CompleteThrough e.toNative T := by
  constructor
  · rintro ⟨date, jumps, pending⟩
    exact ⟨date, fun v => ⟨fun j => (jumps v).false (Jump.ofNative j)⟩, pending⟩
  · rintro ⟨date, jumps, pending⟩
    exact ⟨date, fun v => ⟨fun j => (jumps v).false j.toNative⟩, pending⟩

end KernelR.Family
