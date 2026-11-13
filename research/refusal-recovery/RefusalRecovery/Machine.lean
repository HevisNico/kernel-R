import SelfCertifyingLearning.OfferFactory

namespace RefusalRecovery
open SelfCertifyingLearning

structure Hardware where
  service : Nat
  dose : Nat
  capacity : Nat
  maxWait : Nat
  phaseLimit : Nat
  sensorError : Nat
  deriving DecidableEq, Repr

structure State where
  generation : Nat
  now : Nat
  pending : Bool
  deriving DecidableEq, Repr

def enter (previousGeneration now : Nat) (pending : Bool) : State :=
  ⟨previousGeneration + 1, now, pending⟩

def following (s : State) : State := ⟨s.generation, s.now + 1, true⟩

structure Reading where
  time : Nat
  report : Int
  delivered : Bool
  deriving DecidableEq, Repr

def before (h : Hardware) (r : Reading) : Int := r.report - (h.sensorError : Int)

def after (h : Hardware) (r : Reading) : Int :=
  if r.delivered then min (h.capacity : Int) (before h r + (h.dose : Int))
  else before h r

def fresh (s : State) (r : Reading) : Bool :=
  decide (r.time = s.now ∧ r.delivered = s.pending)

def sampledSafe (h : Hardware) (s : State) (reading : Option Reading) : Bool :=
  match reading with
  | none => false
  | some r => fresh s r && decide ((h.service : Int) ≤ before h r)

structure Permit where
  generation : Nat
  issued : Nat
  expires : Nat
  bound : Nat
  decisions : Nat
  deriving DecidableEq, Repr

def config (h : Hardware) (p : Permit) : Repair.Config :=
  ⟨h.service, p.bound, 1, h.dose, h.capacity, h.maxWait⟩

def entry (h : Hardware) (r : Reading) : Nat := (after h r).toNat

def phaseSpan (h : Hardware) (r : Reading) (p : Permit) : Nat :=
  ClosedLoop.clock (config h p) p.decisions (entry h r)

def Admissible (h : Hardware) (s : State) (r : Reading) (p : Permit) : Prop :=
  fresh s r = true ∧ p.generation = s.generation ∧ p.issued = s.now ∧
  0 ≤ after h r ∧ (config h p).Valid ∧ (config h p).Ready (entry h r) ∧
  0 < p.decisions ∧ p.decisions ≤ h.phaseLimit ∧
  s.now + phaseSpan h r p ≤ p.expires

instance (h s r p) : Decidable (Admissible h s r p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def authorized (h : Hardware) (s : State) (r : Reading) (p : Permit) : Bool :=
  decide (Admissible h s r p)

inductive Action where
  | repair
  | resume (permit : Permit)
  | exhausted
  | fault
  deriving DecidableEq, Repr

def fallback : Nat → Action
  | 0 => .exhausted
  | _ + 1 => .repair

def choose (h : Hardware) (s : State) (fuel : Nat)
    (reading : Option Reading) (permit : Option Permit) : Action :=
  match reading with
  | none => .fault
  | some r =>
    if fresh s r then
      match permit with
      | some p => if authorized h s r p then .resume p else fallback fuel
      | none => fallback fuel
    else .fault

structure Frame where
  time : Nat
  sampledSafe : Bool
  action : Action
  deriving DecidableEq, Repr

def visit (h : Hardware) (s : State) (fuel : Nat)
    (reading : Option Reading) (permit : Option Permit) : Frame :=
  ⟨s.now, sampledSafe h s reading, choose h s fuel reading permit⟩

abbrev Input := State → Option Reading × Option Permit

def run (h : Hardware) (input : Input) : Nat → State → List Frame
  | 0, s => [visit h s 0 (input s).1 (input s).2]
  | n + 1, s =>
    let frame := visit h s (n + 1) (input s).1 (input s).2
    frame :: if frame.action = .repair then run h input n (following s) else []

def writes (frames : List Frame) : Nat :=
  (frames.filter fun f => f.action == .repair).length

def cost (probePrice writePrice : Nat) (frames : List Frame) : Nat :=
  probePrice * frames.length + writePrice * writes frames

theorem sampled_sound {h s r pre} (honest : before h r ≤ pre)
    (claimed : sampledSafe h s (some r) = true) : (h.service : Int) ≤ pre := by
  simp only [sampledSafe, Bool.and_eq_true, decide_eq_true_eq] at claimed
  omega

theorem no_missing_claim (h s) : sampledSafe h s none = false := rfl

theorem no_stale_claim (h s r) (stale : r.time ≠ s.now) :
    sampledSafe h s (some r) = false := by simp [sampledSafe, fresh, stale]

theorem post_lower_sound {h r pre post} (honest : before h r ≤ pre)
    (delivery : if r.delivered then min (h.capacity : Int) (pre + (h.dose : Int)) ≤ post
      else pre ≤ post) : after h r ≤ post := by
  unfold after
  split <;> split at delivery <;> simp_all <;> omega

theorem zero_no_repair (h s reading permit) : choose h s 0 reading permit ≠ .repair := by
  cases reading with
  | none => simp [choose]
  | some r =>
    simp only [choose]
    split
    · cases permit with
      | none => simp [fallback]
      | some p =>
        by_cases accepted : authorized h s r p = true
        · simp [accepted]
        · simp [accepted, fallback]
    · simp

theorem resume_admissible {h s fuel reading permit p}
    (resumed : choose h s fuel reading permit = .resume p) :
    ∃ r, reading = some r ∧ permit = some p ∧ Admissible h s r p := by
  cases reading with
  | none => simp [choose] at resumed
  | some r =>
    simp only [choose] at resumed
    split at resumed
    · cases permit with
      | none => cases fuel <;> simp [fallback] at resumed
      | some q =>
        simp only at resumed
        split at resumed
        next good =>
          have eq := Action.resume.inj resumed
          subst q
          exact ⟨r, rfl, rfl, of_decide_eq_true good⟩
        next => cases fuel <;> simp [fallback] at resumed
    · contradiction

theorem repair_fresh {h s fuel reading permit}
    (repair : choose h s fuel reading permit = .repair) :
    ∃ r, reading = some r ∧ fresh s r = true := by
  cases reading with
  | none => simp [choose] at repair
  | some r =>
    by_cases ok : fresh s r = true
    · exact ⟨r, rfl, ok⟩
    · simp [choose, ok] at repair

theorem repair_positive {h s fuel reading permit}
    (repair : choose h s fuel reading permit = .repair) : 0 < fuel := by
  cases fuel with
  | zero => exact False.elim (zero_no_repair h s reading permit repair)
  | succ n => omega

theorem next_probe (s : State) :
    (following s).now = s.now + 1 ∧ (following s).pending = true ∧
    (following s).generation = s.generation := ⟨rfl, rfl, rfl⟩

theorem run_bounds (h input n s) :
    (run h input n s).length ≤ n + 1 ∧ writes (run h input n s) ≤ n := by
  induction n generalizing s with
  | zero =>
    have noWrite := zero_no_repair h s (input s).1 (input s).2
    simp [run, writes, visit, noWrite]
  | succ n ih =>
    have tail := ih (following s)
    simp only [run]
    split
    next repair => simp_all [writes, visit]
    next stopped => simp_all [writes, visit]

theorem cost_bound (h input n s probePrice writePrice) :
    cost probePrice writePrice (run h input n s) ≤
      probePrice * (n + 1) + writePrice * n := by
  have bounds := run_bounds h input n s
  exact Nat.add_le_add (Nat.mul_le_mul_left _ bounds.1) (Nat.mul_le_mul_left _ bounds.2)

theorem cumulative_cost_bound (priorCost h input n s probePrice writePrice) :
    priorCost + cost probePrice writePrice (run h input n s) ≤
      priorCost + probePrice * (n + 1) + writePrice * n := by
  have bound := cost_bound h input n s probePrice writePrice
  omega

def Honest (h : Hardware) (input : Input) (truth : Nat → Int) : Prop :=
  ∀ s r, (input s).1 = some r → fresh s r = true → before h r ≤ truth s.now

theorem visit_claim_sound {h s n input truth} (honest : Honest h input truth)
    (claim : (visit h s n (input s).1 (input s).2).sampledSafe = true) :
    (h.service : Int) ≤ truth s.now := by
  cases obs : (input s).1 with
  | none => simp [visit, obs, sampledSafe] at claim
  | some r =>
    change sampledSafe h s (input s).1 = true at claim
    rw [obs] at claim
    have parts : fresh s r = true ∧ decide ((h.service : Int) ≤ before h r) = true := by
      simpa only [sampledSafe, Bool.and_eq_true] using claim
    have fresh := parts.1
    exact sampled_sound (honest s r obs fresh) claim

theorem run_claims_sound (h input n s truth) (honest : Honest h input truth) :
    ∀ frame ∈ run h input n s, frame.sampledSafe = true → (h.service : Int) ≤ truth frame.time := by
  induction n generalizing s with
  | zero =>
    intro frame member claim
    simp only [run, List.mem_singleton] at member
    subst frame
    exact visit_claim_sound honest claim
  | succ n ih =>
    intro frame member claim
    simp only [run, List.mem_cons] at member
    rcases member with first | later
    · subst frame; exact visit_claim_sound honest claim
    · split at later
      · exact ih (following s) frame later claim
      · simp at later

theorem resumed_service {h s r p} (admitted : Admissible h s r p)
    (state : Nat → Int) (observed : after h r ≤ state 0)
    (physics : ClosedLoop.Realizes (config h p) p.decisions (entry h r) state) :
    SafeUntil state h.service (phaseSpan h r p) ∧
    (ClosedLoop.final (config h p) p.decisions (entry h r) : Int) ≤ state (phaseSpan h r p) := by
  have nonnegative := admitted.2.2.2.1
  have valid := admitted.2.2.2.2.1
  have ready := admitted.2.2.2.2.2.1
  apply ClosedLoop.execution_safe valid p.decisions ready state _ physics
  unfold entry
  omega

theorem resumed_dates {h s r p} (admitted : Admissible h s r p)
    {k : Nat} (within : k ≤ phaseSpan h r p) :
    p.issued ≤ s.now + k ∧ s.now + k ≤ p.expires := by
  have issued := admitted.2.2.1
  have covers := admitted.2.2.2.2.2.2.2.2
  omega

theorem resumed_from_physics {h s r p} (admitted : Admissible h s r p)
    (state : Nat → Int) (rate : Nat → Nat) (observed : after h r ≤ state 0)
    (rates : ∀ k, k ≤ phaseSpan h r p → rate k ≤ p.bound)
    (flow : ∀ k, k < phaseSpan h r p → state k - (rate (k + 1) : Int) ≤ state (k + 1))
    (delivery : OfferFactory.Delivers (config h p) p.decisions (entry h r) rate state) :
    SafeUntil state h.service (phaseSpan h r p) :=
  (resumed_service admitted state observed
    (OfferFactory.realizes_from_physics (config h p) p.decisions (entry h r)
      rate state rates flow delivery)).1

theorem resumed_write_bound {h s r p} (admitted : Admissible h s r p) :
    ClosedLoop.writes (ClosedLoop.trace (config h p) p.decisions (entry h r)) ≤ h.phaseLimit := by
  have valid := admitted.2.2.2.2.1
  have ready := admitted.2.2.2.2.2.1
  have bounded := admitted.2.2.2.2.2.2.2.1
  have counts := ClosedLoop.trace_counts valid p.decisions ready
  omega

theorem no_finite_prefix_future_bound (past : Nat → Nat) (n bound : Nat) :
    ∃ alternative : Nat → Nat,
      (∀ t, t ≤ n → alternative t = past t) ∧ bound < alternative (n + 1) := by
  refine ⟨fun t => if t ≤ n then past t else bound + 1, ?_, ?_⟩
  · intro t ht; simp [ht]
  · have later : ¬ n + 1 ≤ n := by omega
    simp [later]

end RefusalRecovery
