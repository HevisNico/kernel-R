import RefusalRecovery.Machine

namespace RefusalRecovery.Runtime
open SelfCertifyingLearning

def hardware : Hardware := ⟨100, 220, 660, 40, 8, 2⟩

def activeReady (h : Hardware) (s : State) (r : Reading) (p : Permit)
    (remaining rateLower : Nat) : Prop :=
  fresh s r = true ∧ p.generation = s.generation ∧ p.issued ≤ s.now ∧
  0 ≤ after h r ∧ (config h p).Valid ∧ (config h p).Ready (entry h r) ∧
  0 < remaining ∧ remaining ≤ p.decisions ∧ p.decisions ≤ h.phaseLimit ∧
  rateLower ≤ p.bound

instance (h s r p remaining rateLower) : Decidable (activeReady h s r p remaining rateLower) :=
  inferInstanceAs (Decidable (_ ∧ _))

def activeChoose (h : Hardware) (s : State) (r : Reading) (p : Permit)
    (remaining rateLower : Nat) : ClosedLoop.Action :=
  let a := ClosedLoop.choose (config h p) (entry h r)
  if activeReady h s r p remaining rateLower ∧
      s.now + ClosedLoop.duration (config h p) a ≤ p.expires then a else .refuse

theorem active_choice_safe {h s r p remaining rateLower a}
    (chosen : activeChoose h s r p remaining rateLower = a) (notRefused : a ≠ .refuse)
    (state : Nat → Int) (observed : after h r ≤ state 0)
    (dynamics : ClosedLoop.Dynamics (config h p) state a) :
    SafeUntil state h.service (ClosedLoop.duration (config h p) a) ∧
    (ClosedLoop.next (config h p) (entry h r) a : Int) ≤
      state (ClosedLoop.duration (config h p) a) := by
  simp only [activeChoose] at chosen
  split at chosen
  next good =>
    subst a
    have nonnegative := good.1.2.2.2.1
    apply ClosedLoop.action_safe good.1.2.2.2.2.1 good.1.2.2.2.2.2.1 state _ dynamics
    unfold entry
    omega
  next => exact False.elim (notRefused chosen.symm)

theorem demonstrated_violation_refuses (h s r p remaining rateLower)
    (violation : p.bound < rateLower) : activeChoose h s r p remaining rateLower = .refuse := by
  simp only [activeChoose]
  split
  next good => have bound := good.1.2.2.2.2.2.2.2.2.2; omega
  next => rfl

theorem active_dates {h s r p remaining rateLower a}
    (chosen : activeChoose h s r p remaining rateLower = a) (notRefused : a ≠ .refuse) :
    0 < ClosedLoop.duration (config h p) a ∧
    p.issued ≤ s.now ∧ s.now + ClosedLoop.duration (config h p) a ≤ p.expires := by
  simp only [activeChoose] at chosen
  split at chosen
  next good =>
    subst a
    exact ⟨ClosedLoop.action_progress good.1.2.2.2.2.1 good.1.2.2.2.2.2.1,
      good.1.2.2.1, good.2⟩
  next => exact False.elim (notRefused chosen.symm)

def response (line : String) : String :=
  match (line.splitOn " ").mapM String.toInt? with
  | some [mode, gen, now, pending, fuel, time, report, delivered, pg, issued, expires, bound, count, rate] =>
    if (mode ≠ 0 ∧ mode ≠ 1) ∨ gen < 0 ∨ now < 0 ∨ pending < 0 ∨ pending > 1 ∨
        fuel < 0 ∨ time < 0 ∨ delivered < 0 ∨ delivered > 1 ∨ pg < -1 ∨ issued < 0 ∨
        expires < 0 ∨ bound < 0 ∨ count < 0 ∨ rate < 0 then "ERROR numeric domain" else
    let s : State := ⟨gen.toNat, now.toNat, pending = 1⟩
    let r : Reading := ⟨time.toNat, report, delivered = 1⟩
    let p : Permit := ⟨pg.toNat, issued.toNat, expires.toNat, bound.toNat, count.toNat⟩
    let safe := if sampledSafe hardware s (some r) then 1 else 0
    let lower := after hardware r
    if mode = 0 then
      let a := choose hardware s fuel.toNat (some r) (if pg = -1 then none else some p)
      let kind := match a with
        | .repair => "repair"
        | .resume _ => "resume"
        | .exhausted => "exhausted"
        | .fault => "fault"
      s!"{kind} {lower} {safe} {if a = .repair then 1 else 0}"
    else if pg < 0 then "ERROR missing active permit" else
      let a := activeChoose hardware s r p fuel.toNat (rate.toNat - 1)
      let kind := match a with
        | .wait _ => "wait"
        | .write => "write"
        | .refuse => "refuse"
      s!"{kind} {lower} {safe} {ClosedLoop.duration (config hardware p) a}"
  | _ => "ERROR field count or integer"

end RefusalRecovery.Runtime
