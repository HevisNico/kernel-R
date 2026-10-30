import KernelR.Chain.Induction

/-! Explicit refinement interface from actual streams to packet witnesses.
No local law is an axiom: callers must supply proofs from their execution
semantics. The repository does not yet supply that hybrid-semantics proof. -/
namespace KernelR.Chain

def HasPacket (stream : ℕ → ℝ) (m L : ℕ) (J : ℝ) : Prop :=
  ∃ p : Packet m L J, ∀ i, i < m + L → stream i = p.actual i

structure RelayWitness {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (outgoing : ℕ → ℝ) where
  low firstHigh restHigh : ℝ
  low_bounds : 65 / 100 ≤ low ∧ low ≤ 66 / 100
  first_bounds : 20 / 100 ≤ firstHigh ∧ firstHigh ≤ 25 / 100
  rest_bounds : 24 / 100 ≤ restHigh ∧ restHigh ≤ 25 / 100
  ordered : firstHigh ≤ restHigh
  realizes : ∀ i, i < (m + 2) + (L - 4) →
    outgoing i = (p.relay hL low firstHigh restHigh
      low_bounds first_bounds rest_bounds ordered).actual i

def RelayLaw (incoming outgoing : ℕ → ℝ) : Prop :=
  ∀ m L J (p : Packet m L J) (hL : 5 ≤ L), J ≤ 3 / 20 →
    (∀ i, i < m + L → incoming i = p.actual i) →
    Nonempty (RelayWitness p hL outgoing)

theorem wire_hasPacket {stream : ℕ → ℝ} {m L J}
    (hp : HasPacket stream m L J) (d σ : ℝ) (hσ : 0 ≤ σ)
    (e : ℕ → ℝ) (he : ∀ i, -σ ≤ e i ∧ e i ≤ σ) :
    HasPacket (fun i => stream i + d + e i) m L (J + σ) := by
  rcases hp with ⟨p, hp⟩
  refine ⟨p.wire d σ hσ e he, ?_⟩
  intro i hi
  rw [wire_actual, hp i hi]

theorem relay_hasPacket {incoming outgoing : ℕ → ℝ} {m L J}
    (hp : HasPacket incoming m L J) (hL : 5 ≤ L) (hJ : J ≤ 3 / 20)
    (law : RelayLaw incoming outgoing) :
    HasPacket outgoing (m + 2) (L - 4) J := by
  rcases hp with ⟨p, hp⟩
  obtain ⟨w⟩ := law m L J p hL hJ hp
  exact ⟨p.relay hL w.low w.firstHigh w.restHigh
    w.low_bounds w.first_bounds w.rest_bounds w.ordered, w.realizes⟩

/-- Physical stream composition with explicit wire errors and local relay laws.
The theorem permits different local latencies at every cell and adversarial errors. -/
theorem realized_chain
    (output : ℕ → ℕ → ℝ) (delay σ : ℕ → ℝ) (error : ℕ → ℕ → ℝ)
    (N K : ℕ) (hN : 0 < N) (hK : 4 * N + 12 ≤ K)
    (hσ : ∀ j, 0 ≤ σ j)
    (he : ∀ j i, -σ j ≤ error j i ∧ error j i ≤ σ j)
    (budget : pathJitter σ (N - 1) ≤ 3 / 20)
    (leaf : HasPacket (output 0) 3 (K - 8) 0)
    (localLaws : ∀ j, j + 1 < N →
      RelayLaw (fun i => output j i + delay j + error j i) (output (j + 1))) :
    ∀ j, j < N →
      HasPacket (output j) (prefixLength j) (tailLength K j) (pathJitter σ j) := by
  apply compose_every_finite_chain
    (fun j m L J => HasPacket (output j) m L J) σ N K hN hK hσ budget leaf
  intro j m L J hj hL hJ hp
  exact relay_hasPacket (wire_hasPacket hp (delay j) (σ j) (hσ j) (error j) (he j))
    hL hJ (localLaws j hj)

end KernelR.Chain
