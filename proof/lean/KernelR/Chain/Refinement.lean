import KernelR.Chain.Induction

/-! Explicit refinement interface from finite physical streams to packet witnesses.
No local law is an axiom: callers must supply proofs from their execution
semantics. The repository does not yet supply that hybrid-semantics proof. -/
namespace KernelR.Chain

/-- A finite event stream; time values at indices >= count are irrelevant padding. -/
structure Signal where
  count : ℕ
  time : ℕ → ℝ

noncomputable def Signal.wire (s : Signal) (delay : ℝ) (error : ℕ → ℝ) : Signal :=
  ⟨s.count, fun i => s.time i + delay + error i⟩

/-- The count equality excludes both missing and additional output events. -/
def HasPacket (stream : Signal) (m L : ℕ) (J : ℝ) : Prop :=
  stream.count = m + L ∧
    ∃ p : Packet m L J, ∀ i, i < m + L → stream.time i = p.actual i

structure RelayWitness {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (outgoing : Signal) where
  low : ℝ
  firstHigh : ℝ
  restHigh : ℝ
  low_bounds : 65 / 100 ≤ low ∧ low ≤ 66 / 100
  first_bounds : 20 / 100 ≤ firstHigh ∧ firstHigh ≤ 25 / 100
  rest_bounds : 24 / 100 ≤ restHigh ∧ restHigh ≤ 25 / 100
  ordered : firstHigh ≤ restHigh
  count_exact : outgoing.count = (m + 2) + (L - 4)
  realizes : ∀ i, i < (m + 2) + (L - 4) →
    outgoing.time i = (p.relay hL low firstHigh restHigh
      low_bounds first_bounds rest_bounds ordered).actual i

def RelayLaw (incoming outgoing : Signal) : Prop :=
  ∀ m L J (p : Packet m L J) (hL : 5 ≤ L), J ≤ 3 / 20 →
    incoming.count = m + L →
    (∀ i, i < m + L → incoming.time i = p.actual i) →
    Nonempty (RelayWitness p hL outgoing)

theorem wire_hasPacket {stream : Signal} {m L J}
    (hp : HasPacket stream m L J) (d σ : ℝ) (hσ : 0 ≤ σ)
    (e : ℕ → ℝ) (he : ∀ i, -σ ≤ e i ∧ e i ≤ σ) :
    HasPacket (stream.wire d e) m L (J + σ) := by
  rcases hp with ⟨hc, p, hp⟩
  refine ⟨hc, p.wire d σ hσ e he, ?_⟩
  intro i hi
  change stream.time i + d + e i = _
  rw [wire_actual, hp i hi]

theorem relay_hasPacket {incoming outgoing : Signal} {m L J}
    (hp : HasPacket incoming m L J) (hL : 5 ≤ L) (hJ : J ≤ 3 / 20)
    (law : RelayLaw incoming outgoing) :
    HasPacket outgoing (m + 2) (L - 4) J := by
  rcases hp with ⟨hc, p, hp⟩
  obtain ⟨w⟩ := law m L J p hL hJ hc hp
  exact ⟨w.count_exact, p.relay hL w.low w.firstHigh w.restHigh
    w.low_bounds w.first_bounds w.rest_bounds w.ordered, w.realizes⟩

/-- Finite physical-stream composition with explicit wire errors and local laws.
Every cell may have different latencies, and errors may be adversarial. -/
theorem realized_chain
    (output : ℕ → Signal) (delay σ : ℕ → ℝ) (error : ℕ → ℕ → ℝ)
    (N K : ℕ) (hN : 0 < N) (hK : 4 * N + 12 ≤ K)
    (hσ : ∀ j, 0 ≤ σ j)
    (he : ∀ j i, -σ j ≤ error j i ∧ error j i ≤ σ j)
    (budget : pathJitter σ (N - 1) ≤ 3 / 20)
    (leaf : HasPacket (output 0) 3 (K - 8) 0)
    (localLaws : ∀ j, j + 1 < N →
      RelayLaw ((output j).wire (delay j) (error j)) (output (j + 1))) :
    ∀ j, j < N →
      HasPacket (output j) (prefixLength j) (tailLength K j) (pathJitter σ j) := by
  apply compose_every_finite_chain
    (fun j m L J => HasPacket (output j) m L J) σ N K hN hK hσ budget leaf
  intro j m L J hj hL hJ hp
  exact relay_hasPacket (wire_hasPacket hp (delay j) (σ j) (hσ j) (error j) (he j))
    hL hJ (localLaws j hj)

theorem realized_node_count {output : ℕ → Signal} {N K j : ℕ}
    (hK : 4 * N + 12 ≤ K) (hj : j < N) {J : ℝ}
    (hp : HasPacket (output j) (prefixLength j) (tailLength K j) J) :
    (output j).count = K - 5 - 2 * j :=
  hp.1.trans (node_outputs hK hj)

theorem realized_total_count {output : ℕ → Signal} {N K : ℕ}
    (hK : 4 * N + 12 ≤ K) (J : ℕ → ℝ)
    (hp : ∀ j, j < N → HasPacket (output j) (prefixLength j) (tailLength K j) (J j)) :
    (Finset.range N).sum (fun j => (output j).count) = N * (K - N - 4) := by
  calc
    (Finset.range N).sum (fun j => (output j).count) =
        (Finset.range N).sum (fun j => prefixLength j + tailLength K j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hp j (Finset.mem_range.mp hj)).1
    _ = N * (K - N - 4) := total_emissions_sum hK

end KernelR.Chain
