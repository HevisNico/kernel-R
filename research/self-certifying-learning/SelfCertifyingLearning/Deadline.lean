import Std

/-! A discrete observation contract. The true reserve is signed; its lower
enclosure and cumulative-loss envelope must hold between observations too. -/
namespace SelfCertifyingLearning

def SafeUntil (state : Nat → Int) (reserve : Nat) (deadline : Nat) : Prop :=
  ∀ k, k ≤ deadline → (reserve : Int) ≤ state k

/-- The endpoint budget implies safety at every intermediate discrete time.
It does not establish the envelope from sampled data. -/
theorem safe_until_deadline (state : Nat → Int) (loss : Nat → Nat)
    (initial reserve deadline : Nat)
    (enclosure : ∀ k, k ≤ deadline → (initial : Int) - (loss k : Int) ≤ state k)
    (lossBound : ∀ k, k ≤ deadline → loss k ≤ loss deadline)
    (budget : loss deadline + reserve ≤ initial) : SafeUntil state reserve deadline := by
  intro k hk
  have := enclosure k hk
  have := lossBound k hk
  omega

/-- Constant rate is a special case of an envelope, valid only when its
inequality holds throughout the planned interval. -/
theorem constant_rate_deadline (state : Nat → Int) (initial reserve rate deadline : Nat)
    (enclosure : ∀ k, k ≤ deadline → (initial : Int) - (rate * k : Nat) ≤ state k)
    (budget : rate * deadline + reserve ≤ initial) : SafeUntil state reserve deadline := by
  apply safe_until_deadline state (fun k => rate * k) initial reserve deadline enclosure
  · intro k hk
    exact Nat.mul_le_mul_left rate hk
  · exact budget

/-- An upper level cannot extend the deadline of the certificate it consumes. -/
theorem SafeUntil.restrict {state reserve deadline} (safe : SafeUntil state reserve deadline)
    {earlier : Nat} (within : earlier ≤ deadline) : SafeUntil state reserve earlier := by
  intro k hk
  exact safe k (Nat.le_trans hk within)

structure TimedCertificate (State : Type) where
  issued : Nat
  expires : Nat
  ordered : issued ≤ expires
  valid : State → Prop

def TimedCertificate.Usable {State} (cert : TimedCertificate State)
    (now : Nat) (state : State) : Prop :=
  cert.issued ≤ now ∧ now ≤ cert.expires ∧ cert.valid state

/-- Proofs retain their meaning; using them requires the current context.
Usable is a proposition, not an implemented detector of validity. -/
structure Decision {State : Type} (cert : TimedCertificate State) where
  conclusion : State → Prop
  justified : ∀ state, cert.valid state → conclusion state

theorem Decision.apply {State} {cert : TimedCertificate State} (decision : Decision cert)
    {now state} (usable : cert.Usable now state) : decision.conclusion state :=
  decision.justified state usable.2.2

theorem expired_not_usable {State} (cert : TimedCertificate State) {now state}
    (expired : cert.expires < now) : ¬ cert.Usable now state := by
  intro usable
  have := usable.2.1
  omega

/-- Abstract information limit: a sound observation-only checker cannot
accept a shared observation when one compatible world is unsafe. -/
theorem indistinguishable_cannot_accept {World Observation : Type}
    (observe : World → Observation) (safe : World → Prop) (check : Observation → Bool)
    (sound : ∀ world, check (observe world) = true → safe world)
    (first second : World) (same : observe first = observe second) (bad : ¬ safe second) :
    check (observe first) ≠ true := by
  intro accepted
  exact bad (sound second (same ▸ accepted))

end SelfCertifyingLearning
