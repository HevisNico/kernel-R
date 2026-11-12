import SelfCertifyingLearning.Epochs

/-! Calendar-time composition of admitted phases. Static eligibility does
not prove a future physical envelope; Realizes is the explicit plant premise. -/
namespace SelfCertifyingLearning.EpochSafety
open Repair ClosedLoop Epochs

def SafeBetween (state : Nat → Int) (service start stop : Nat) : Prop :=
  ∀ t, start ≤ t → t ≤ stop → (service : Int) ≤ state t

def Realizes (state : Nat → Int) : Plan → Prop
  | .complete _ | .blocked _ => True
  | .phase cursor offer tail =>
    ClosedLoop.Realizes offer.config offer.decisions (entry cursor offer)
      (fun t => state (cursor.now + t)) ∧ Realizes state tail

theorem phase_dates {policy cursor offer} (admitted : Admissible policy cursor offer)
    {offset : Nat} (within : offset ≤ span cursor offer) :
    offer.issued ≤ cursor.now + offset ∧ cursor.now + offset ≤ offer.expires := by
  have begins := admitted.issued
  have ends := admitted.covers
  omega

theorem endpoint_ready {policy cursor offer} (admitted : Admissible policy cursor offer) :
    offer.config.Ready (endpoint cursor offer) :=
  final_ready admitted.valid offer.decisions admitted.ready

theorem endpoint_service {policy cursor offer} (admitted : Admissible policy cursor offer) :
    policy.service ≤ (advance cursor offer).lower := by
  have floor := (endpoint_ready admitted).1
  simp only [advance]
  rw [← admitted.sameService]
  unfold Config.guard at floor
  omega

theorem handoff_preserved {policy cursor plan} (valid : WellFormed policy cursor plan)
    (initial : policy.handoff ≤ cursor.lower) : policy.handoff ≤ plan.finish.lower := by
  induction valid with
  | complete => exact initial
  | blocked => exact initial
  | phase admitted rest ih => exact ih admitted.preserves

theorem phase_safe {policy cursor offer} (admitted : Admissible policy cursor offer)
    (state : Nat → Int) (observed : (cursor.lower : Int) ≤ state cursor.now)
    (realizes : ClosedLoop.Realizes offer.config offer.decisions (entry cursor offer)
      (fun t => state (cursor.now + t))) :
    SafeUntil (fun t => state (cursor.now + t)) policy.service (span cursor offer) ∧
    ((advance cursor offer).lower : Int) ≤ state (advance cursor offer).now := by
  have entryBound : (entry cursor offer : Int) ≤ state (cursor.now + 0) := by
    simp only [Nat.add_zero]
    unfold entry
    omega
  have safe := execution_safe admitted.valid offer.decisions admitted.ready
    (fun t => state (cursor.now + t)) entryBound realizes
  rw [admitted.sameService] at safe
  exact safe

/-- No interval between successful phases is left uncovered. Refusal stops
this theorem at the current boundary; it promises nothing after that time. -/
theorem composed_safe {policy cursor plan} (valid : WellFormed policy cursor plan)
    (state : Nat → Int) (initial : policy.service ≤ cursor.lower)
    (observed : (cursor.lower : Int) ≤ state cursor.now) (realizes : Realizes state plan) :
    SafeBetween state policy.service cursor.now plan.finish.now ∧
    (plan.finish.lower : Int) ≤ state plan.finish.now := by
  induction valid with
  | complete cursor =>
    refine ⟨?_, observed⟩
    intro t lo hi
    simp only [Plan.finish] at hi
    have : t = cursor.now := by omega
    subst t
    omega
  | blocked cursor =>
    refine ⟨?_, observed⟩
    intro t lo hi
    simp only [Plan.finish] at hi
    have : t = cursor.now := by omega
    subst t
    omega
  | @phase cursor offer tail admitted rest ih =>
    have segment := phase_safe admitted state observed realizes.1
    have following := ih (endpoint_service admitted) segment.2 realizes.2
    refine ⟨?_, following.2⟩
    intro t lo hi
    by_cases early : t ≤ (advance cursor offer).now
    · have offset : t - cursor.now ≤ span cursor offer := by simp only [advance] at early; omega
      have bound := segment.1 (t - cursor.now) offset
      have same : cursor.now + (t - cursor.now) = t := by omega
      simpa only [same] using bound
    · exact following.1 t (by omega) hi

/-- An already expired offer cannot be revived by choosing a shorter phase. -/
theorem expired_refused (policy cursor offer) (expired : offer.expires < cursor.now) :
    eligible policy cursor offer = false := by
  cases result : eligible policy cursor offer with
  | false => rfl
  | true =>
    have admitted := (eligible_iff _ _ _).mp result
    have covers := admitted.covers
    omega

/-- The same service requirement is enforced across every selected phase;
weakening a specification cannot make an inadmissible offer acceptable. -/
theorem changed_service_refused (policy cursor offer)
    (different : offer.config.service ≠ policy.service) : eligible policy cursor offer = false := by
  cases result : eligible policy cursor offer with
  | false => rfl
  | true => exact False.elim (different ((eligible_iff _ _ _).mp result).sameService)

end SelfCertifyingLearning.EpochSafety
