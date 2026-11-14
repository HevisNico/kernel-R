import AutonomousFeedback

/-!
# The guarded model of the SKY130 circuit network, gain only

An instance of the guarded model of `../../network-stability/AutonomousFeedback.lean` for two circuit
cells joined by a forward and a return edge. Phase 1, exploratory.

The circuit cell has no recovery memory and no MARK: the only stored coordinates are the gains of its
ports. There are four: the source port and the return port of cell A, the forward port and the source
port of cell B. A pulse on a port is a probe. Its read law is the circuit's own, in units where one
dose of that port is `d`:

    score = - gap + d * (writes of that port),      FIRE iff 0 ≤ score + error,

where `gap` is the measured distance of the port's preset to its service threshold. A silent read
writes one dose. A FIRE of a routed source enqueues one pulse on the wire port of the other cell.
What the model does not carry — the help of a recent pulse, the noise of the read, the error of the
measures — is in `error`, bounded below by `lo` and above by `hi`.

The file proves nothing new about the model: it builds the certificate that
`AutonomousFeedback.certified_feedback` asks for, for every number of sources and every gap, and
states its conclusion for this network. The margins along the nominal run remain a hypothesis: they
are numbers, checked instance by instance.
-/

namespace NetworkStability.CircuitNetwork

open AutonomousFeedback
open RoutedCalendar (HasRoom)

/-- The four stored gains. -/
abbrev sourceOfA : Fin 4 := 0
abbrev returnOnA : Fin 4 := 1
abbrev forwardOnB : Fin 4 := 2
abbrev sourceOfB : Fin 4 := 3

/-- A pulse. A source is external; `routed` says whether its date is inside the gate of its edge. -/
inductive Probe where
  | sourceA (routed : Bool)
  | sourceB (routed : Bool)
  | forward
  | back
  deriving DecidableEq, Repr

def port : Probe → Fin 4
  | .sourceA _ => sourceOfA
  | .sourceB _ => sourceOfB
  | .forward => forwardOnB
  | .back => returnOnA

def route : Probe → List Probe
  | .sourceA true => [.forward]
  | .sourceB true => [.back]
  | _ => []

/-- The circuit network as a guarded model: no drive term, one bias per port. -/
def circuit (gap : Fin 4 → Int) : Model 4 Probe where
  cell := port
  bias := fun p => - gap (port p)
  drive := fun _ => 0
  route := route

/-- The sources of a calendar, in an order that keeps the dates of each port: `a0` sources of A before
its gate and `a1` inside it, then `b0` sources of B before its gate and `b1` inside it. Wire pulses
are not in the seed: they exist only if their source fires. -/
def calendar (a0 a1 b0 b1 : Nat) : List Probe :=
  List.replicate a0 (.sourceA false) ++ List.replicate a1 (.sourceA true) ++
    List.replicate b0 (.sourceB false) ++ List.replicate b1 (.sourceB true)

/-- A source inside a gate pays for itself and for the wire pulse it may cause. -/
def weight : Probe → Nat
  | .sourceA true => 2
  | .sourceB true => 2
  | _ => 1

def reserve (i : Fin 4) (p : Probe) : Nat :=
  (if port p = i then 1 else 0) +
    match p with
    | .sourceA true => if i = forwardOnB then 1 else 0
    | .sourceB true => if i = returnOnA then 1 else 0
    | _ => 0

theorem mass_replicate (w : Probe → Nat) (n : Nat) (p : Probe) :
    mass w (List.replicate n p) = n * w p := by
  induction n with
  | zero => simp [mass]
  | succ n ih =>
    simp only [mass, List.replicate_succ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.succ_mul, Nat.add_comm]

theorem mass_calendar (w : Probe → Nat) (a0 a1 b0 b1 : Nat) :
    mass w (calendar a0 a1 b0 b1) =
      a0 * w (.sourceA false) + a1 * w (.sourceA true) + b0 * w (.sourceB false) + b1 * w (.sourceB true) := by
  simp only [calendar, mass_append, mass_replicate]

/-- At most `a0 + a1 + b0 + b1` writes on any port, and the queue is empty after
`4 * (a0 + 2 * a1 + b0 + 2 * b1)` steps whatever the errors. -/
def certificate (gap : Fin 4 → Int) (a0 a1 b0 b1 : Nat) :
    Certificate (a0 + a1 + b0 + b1) (a0 + 2 * a1 + b0 + 2 * b1) 1 (circuit gap) (calendar a0 a1 b0 b1) where
  weight := weight
  reserve := reserve
  eta_pos := Nat.one_pos
  scalar := by
    intro p
    cases p with
    | sourceA r => cases r <;> simp [circuit, route, weight, mass]
    | sourceB r => cases r <;> simp [circuit, route, weight, mass]
    | forward => simp [circuit, route, weight, mass]
    | back => simp [circuit, route, weight, mass]
  local_route := by
    intro p i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    cases p with
    | sourceA r =>
      cases r <;> rcases cases with h | h | h | h <;> subst h <;>
        simp (config := { decide := true }) [circuit, route, reserve, port, mass]
    | sourceB r =>
      cases r <;> rcases cases with h | h | h | h <;> subst h <;>
        simp (config := { decide := true }) [circuit, route, reserve, port, mass]
    | forward => simp [circuit, route, mass]
    | back => simp [circuit, route, mass]
  local_write := by
    intro p
    cases p with
    | sourceA r => cases r <;> simp [circuit, reserve, port]
    | sourceB r => cases r <;> simp [circuit, reserve, port]
    | forward => simp [circuit, reserve, port]
    | back => simp [circuit, reserve, port]
  seed_weight := by
    rw [mass_calendar]
    simp only [weight]
    omega
  seed_reserve := by
    intro i
    rw [mass_calendar]
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with h | h | h | h <;> subst h <;>
      simp (config := { decide := true }) [reserve] <;> omega

/-- The network theorem for this circuit network, in its certified form. If the errors of the reads
stay inside `[lo, hi]` and every read of the nominal run has room for them, then the run with errors
is the nominal run: same decisions, same routed pulses, same writes; the queue is empty at the end
and stays so; and at every step, with or without room, no port has more than `Q` writes and no
stored value reaches the rail. -/
theorem circuit_certified (gap : Fin 4 → Int) (a0 a1 b0 b1 d B rail : Nat)
    (base : Fin 4 → Nat) (hbase : ∀ i, base i ≤ B)
    (headroom : B + d * (a0 + a1 + b0 + b1) < rail)
    (lo hi error : Nat → Int) (within : ∀ k, lo k ≤ error k ∧ error k ≤ hi k)
    (margins : NominalMargins (circuit gap) d lo hi ((a0 + 2 * a1 + b0 + 2 * b1) * 4)
      (start 4 (calendar a0 a1 b0 b1))) :
    let steps := (a0 + 2 * a1 + b0 + 2 * b1) * 4
    let terminal := run (circuit gap) d error steps (start 4 (calendar a0 a1 b0 b1))
    terminal.pending = [] ∧
      terminal = run (circuit gap) d (fun _ => 0) steps (start 4 (calendar a0 a1 b0 b1)) ∧
      (∀ n, run (circuit gap) d error n terminal = terminal) ∧
      ∀ n, let s := run (circuit gap) d error n (start 4 (calendar a0 a1 b0 b1))
        RoutedCalendar.total ⟨s.writes, []⟩ ≤ (a0 + a1 + b0 + b1) * 4 ∧
        ∀ i, s.writes i ≤ a0 + a1 + b0 + b1 ∧ base i ≤ base i + d * s.writes i ∧
          base i + d * s.writes i < rail :=
  certified_feedback (a0 + a1 + b0 + b1) d B rail (a0 + 2 * a1 + b0 + 2 * b1) 1
    (circuit gap) (calendar a0 a1 b0 b1) (certificate gap a0 a1 b0 b1) base hbase headroom
    lo hi error within margins

/-! ## Budgets given per port

`NominalMargins` takes its bounds per step. The measures give them per port: each port has its own
noise, its own help from a recent pulse, its own dose. `PortMargins` checks every read of the nominal
run against the bounds of the port it reads, and `nominal_of_port` turns it into `NominalMargins`. -/

def PortMargins (M : Model N P) (d : Nat) (lo hi : Fin N → Int) : Nat → State N P → Prop
  | 0, _ => True
  | n + 1, s =>
    match s.pending with
    | [] => True
    | p :: _ =>
      HasRoom (score M d s p) (lo (M.cell p)) (hi (M.cell p)) ∧ PortMargins M d lo hi n (step M d 0 s)

/-- The bound of the port that the nominal run from `s0` reads at step `k`. -/
def stepBound (M : Model N P) (d : Nat) (s0 : State N P) (b : Fin N → Int) (k : Nat) : Int :=
  match (run M d (fun _ => 0) (k - s0.log.length) s0).pending with
  | [] => 0
  | p :: _ => b (M.cell p)

theorem run_zero_succ (M : Model N P) (d j : Nat) (s : State N P) :
    run M d (fun _ => 0) (j + 1) s = step M d 0 (run M d (fun _ => 0) j s) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    show run M d (fun _ => 0) (j + 1) (step M d 0 s) = _
    rw [ih]
    rfl

theorem step_log_length (M : Model N P) (d : Nat) (e : Int) (s : State N P) (p : P) (tail : List P)
    (h : s.pending = p :: tail) : (step M d e s).log.length = s.log.length + 1 := by
  simp [step, h]

theorem nominal_of_port (M : Model N P) (d : Nat) (lo hi : Fin N → Int) (s0 : State N P) :
    ∀ n j, ((run M d (fun _ => 0) j s0).pending = [] ∨
        (run M d (fun _ => 0) j s0).log.length = s0.log.length + j) →
      PortMargins M d lo hi n (run M d (fun _ => 0) j s0) →
      NominalMargins M d (stepBound M d s0 lo) (stepBound M d s0 hi) n (run M d (fun _ => 0) j s0) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro j inv pm
    have next := run_zero_succ M d j s0
    generalize ht : run M d (fun _ => 0) j s0 = t at inv pm next ⊢
    cases hp : t.pending with
    | nil => simp [NominalMargins, hp]
    | cons p tail =>
      have len : t.log.length = s0.log.length + j := by
        rcases inv with h | h
        · rw [hp] at h; cases h
        · exact h
      simp only [PortMargins, hp] at pm
      simp only [NominalMargins, hp]
      have head : (run M d (fun _ => 0) (t.log.length - s0.log.length) s0).pending = p :: tail := by
        rw [len, Nat.add_sub_cancel_left, ht]
        exact hp
      have blo : stepBound M d s0 lo t.log.length = lo (M.cell p) := by simp only [stepBound, head]
      have bhi : stepBound M d s0 hi t.log.length = hi (M.cell p) := by simp only [stepBound, head]
      rw [blo, bhi]
      refine ⟨pm.1, ?_⟩
      rw [← next]
      apply ih (j + 1)
      · right
        rw [next, step_log_length M d 0 t p tail hp, len]
        omega
      · rw [next]
        exact pm.2

/-- The network theorem for this circuit network with one budget per port. The error of a read must
lie in the budget of the port read at that step of the nominal run, which under the conclusion is
the port actually read. -/
theorem circuit_predicted (gap : Fin 4 → Int) (a0 a1 b0 b1 d B rail : Nat)
    (base : Fin 4 → Nat) (hbase : ∀ i, base i ≤ B)
    (headroom : B + d * (a0 + a1 + b0 + b1) < rail)
    (lo hi : Fin 4 → Int) (error : Nat → Int)
    (within : ∀ k, stepBound (circuit gap) d (start 4 (calendar a0 a1 b0 b1)) lo k ≤ error k ∧
      error k ≤ stepBound (circuit gap) d (start 4 (calendar a0 a1 b0 b1)) hi k)
    (margins : PortMargins (circuit gap) d lo hi ((a0 + 2 * a1 + b0 + 2 * b1) * 4)
      (start 4 (calendar a0 a1 b0 b1))) :
    let steps := (a0 + 2 * a1 + b0 + 2 * b1) * 4
    let terminal := run (circuit gap) d error steps (start 4 (calendar a0 a1 b0 b1))
    terminal.pending = [] ∧
      terminal = run (circuit gap) d (fun _ => 0) steps (start 4 (calendar a0 a1 b0 b1)) ∧
      (∀ n, run (circuit gap) d error n terminal = terminal) ∧
      ∀ n, let s := run (circuit gap) d error n (start 4 (calendar a0 a1 b0 b1))
        RoutedCalendar.total ⟨s.writes, []⟩ ≤ (a0 + a1 + b0 + b1) * 4 ∧
        ∀ i, s.writes i ≤ a0 + a1 + b0 + b1 ∧ base i ≤ base i + d * s.writes i ∧
          base i + d * s.writes i < rail :=
  circuit_certified gap a0 a1 b0 b1 d B rail base hbase headroom _ _ error within
    (nominal_of_port (circuit gap) d lo hi (start 4 (calendar a0 a1 b0 b1)) _ 0 (Or.inr rfl) margins)

/-- The margins are a finite check on numbers. -/
def decNominal {N : Nat} {P : Type} (M : Model N P) (d : Nat) (lo hi : Nat → Int) :
    (n : Nat) → (s : State N P) → Decidable (NominalMargins M d lo hi n s)
  | 0, _ => isTrue trivial
  | n + 1, s =>
    match h : s.pending with
    | [] => isTrue (by simp [NominalMargins, h])
    | p :: _ =>
      have room : Decidable (HasRoom (score M d s p) (lo s.log.length) (hi s.log.length)) := by
        unfold HasRoom
        exact inferInstance
      have rest := decNominal M d lo hi n (step M d 0 s)
      decidable_of_iff (HasRoom (score M d s p) (lo s.log.length) (hi s.log.length) ∧
        NominalMargins M d lo hi n (step M d 0 s)) (by simp [NominalMargins, h])

instance {N : Nat} {P : Type} (M : Model N P) (d : Nat) (lo hi : Nat → Int) (n : Nat) (s : State N P) :
    Decidable (NominalMargins M d lo hi n s) := decNominal M d lo hi n s

def decPort {N : Nat} {P : Type} (M : Model N P) (d : Nat) (lo hi : Fin N → Int) :
    (n : Nat) → (s : State N P) → Decidable (PortMargins M d lo hi n s)
  | 0, _ => isTrue trivial
  | n + 1, s =>
    match h : s.pending with
    | [] => isTrue (by simp [PortMargins, h])
    | p :: _ =>
      have room : Decidable (HasRoom (score M d s p) (lo (M.cell p)) (hi (M.cell p))) := by
        unfold HasRoom
        exact inferInstance
      have rest := decPort M d lo hi n (step M d 0 s)
      decidable_of_iff (HasRoom (score M d s p) (lo (M.cell p)) (hi (M.cell p)) ∧
        PortMargins M d lo hi n (step M d 0 s)) (by simp [PortMargins, h])

instance {N : Nat} {P : Type} (M : Model N P) (d : Nat) (lo hi : Fin N → Int) (n : Nat) (s : State N P) :
    Decidable (PortMargins M d lo hi n s) := decPort M d lo hi n s

/-! ## The nominal cell of phase 0, on the calendar of phase 1

One dose is 100 000 units. The measured gap of each port of the nominal cell is 3.59378 doses. The
error budget used here is +0.26 and -0.23 dose. Eight sources before each gate and ten inside. -/

def nominalGap : Fin 4 → Int := fun _ => 359378

def nominalRun : State 4 Probe :=
  run (circuit nominalGap) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))

/-- Every port ends with four writes, and nothing is left to do. -/
example : nominalRun.pending = [] ∧ ∀ i, nominalRun.writes i = 4 := by decide +kernel

/-- Ten FIRE on the source port of A after its four silences, six on the forward port of B. -/
example : (nominalRun.log.filter fun r => r.2 && r.1 == Probe.sourceA true).length = 10 ∧
    (nominalRun.log.filter fun r => r.2 && r.1 == Probe.forward).length = 6 ∧
    (nominalRun.log.filter fun r => r.2 && r.1 == Probe.back).length = 6 := by decide +kernel

/-- Every read of the nominal run has room for the error budget. -/
example : NominalMargins (circuit nominalGap) 100000 (fun _ => -23000) (fun _ => 26000) 224
    (start 4 (calendar 8 10 8 10)) := by decide +kernel

/-- The same with one budget per port. -/
example : PortMargins (circuit nominalGap) 100000 (fun _ => -23000) (fun _ => 26000) 224
    (start 4 (calendar 8 10 8 10)) := by decide +kernel

/-- A larger positive error has no room at the fourth read of a port: 0.59378 dose is all there is. -/
example : ¬ NominalMargins (circuit nominalGap) 100000 (fun _ => -23000) (fun _ => 60000) 224
    (start 4 (calendar 8 10 8 10)) := by decide +kernel

end NetworkStability.CircuitNetwork
