import KernelR.Robust.Packets

/-! Universal slow-chain composition. Local execution laws are explicit inputs;
the result concerns exact finite streams, including absence of extra outputs. -/
namespace KernelR.Robust
open KernelR.Chain (Signal pathJitter pathJitter_mono)

def HasPacket (s : Signal) (L : ℕ) (T J : ℝ) : Prop :=
  s.count = L ∧ ∃ p : Packet L T J, ∀ i, i < L → s.time i = p.actual i

structure CellWitness (incoming outgoing : Signal) (δ : ℝ) where
  reference : ℝ
  latency : ℕ → ℝ
  first : latency 0 ≤ reference + δ
  regular : ∀ i, i ≠ 0 → -δ ≤ latency i - reference ∧ latency i - reference ≤ δ
  count_exact : outgoing.count = incoming.count - 3
  realizes : ∀ i, i < outgoing.count → outgoing.time i = incoming.time (i+3) + latency i

/-- The local physical refinement must prove silence, existence, uniqueness,
latency and the absence of spontaneous outputs from a prepared section. -/
def CellLaw (incoming outgoing : Signal) (δ : ℝ) : Prop :=
  ∀ L T J, 4 ≤ L → 15 / 2 + 2 * J ≤ T →
    HasPacket incoming L T J → Nonempty (CellWitness incoming outgoing δ)

theorem cell_hasPacket {incoming outgoing : Signal} {L T J δ}
    (hp : HasPacket incoming L T J) (hδ : 0 ≤ δ)
    (w : CellWitness incoming outgoing δ) : HasPacket outgoing (L-3) T (J+δ) := by
  rcases hp with ⟨hc, p, hp⟩
  have hout : outgoing.count = L-3 := by rw [w.count_exact, hc]
  refine ⟨hout, p.cell w.reference δ hδ w.latency w.first w.regular, ?_⟩
  intro i hi
  rw [Packet.cell_actual, w.realizes i (by omega), hp (i+3) (by omega)]

theorem wire_hasPacket {s : Signal} {L T J}
    (hp : HasPacket s L T J) (d σ : ℝ) (hσ : 0 ≤ σ)
    (e : ℕ → ℝ) (he : ∀ i, -σ ≤ e i ∧ e i ≤ σ) :
    HasPacket (s.wire d e) L T (J+σ) := by
  rcases hp with ⟨hc, p, hp⟩
  refine ⟨hc, p.wire d σ hσ e he, ?_⟩
  intro i hi
  change s.time i + d + e i = _
  rw [Packet.wire_actual, hp i hi]

noncomputable def periodicSource (K : ℕ) (origin T : ℝ) : Signal :=
  ⟨K, fun i => origin + T * i⟩

theorem source_hasPacket (K : ℕ) (origin T : ℝ) :
    HasPacket (periodicSource K origin T) K T 0 := by
  refine ⟨rfl, ⟨origin, 0, fun _ => 0, le_rfl, le_rfl, ?_⟩, ?_⟩
  · intro i; constructor <;> norm_num
  · intro i hi
    simp [periodicSource, Packet.actual]

theorem remaining_step (K j : ℕ) : K - 3 * (j+1) = (K-3*j)-3 := by omega

/-- Input j has accumulated errors of cells and wires strictly before j.
Only N-1 such increments enter the sufficient input-period condition. -/
theorem realized_chain
    (incoming outgoing : ℕ → Signal) (δ σ delay : ℕ → ℝ)
    (error : ℕ → ℕ → ℝ) (N K : ℕ) (T : ℝ)
    (hK : 3*N+1 ≤ K) (hδ : ∀ j, 0 ≤ δ j) (hσ : ∀ j, 0 ≤ σ j)
    (he : ∀ j i, -σ j ≤ error j i ∧ error j i ≤ σ j)
    (period : 15/2 + 2 * pathJitter (fun j => δ j + σ j) (N-1) ≤ T)
    (source : HasPacket (incoming 0) K T 0)
    (wires : ∀ j, j+1 < N → incoming (j+1) = (outgoing j).wire (delay j) (error j))
    (laws : ∀ j, j < N → CellLaw (incoming j) (outgoing j) (δ j)) :
    ∀ j, j < N →
      HasPacket (incoming j) (K-3*j) T (pathJitter (fun i => δ i+σ i) j) ∧
      HasPacket (outgoing j) (K-3*(j+1)) T (pathJitter (fun i => δ i+σ i) j + δ j) := by
  have hβ : ∀ j, 0 ≤ δ j + σ j := fun j => add_nonneg (hδ j) (hσ j)
  have produce : ∀ j, j < N →
      HasPacket (incoming j) (K-3*j) T (pathJitter (fun i => δ i+σ i) j) →
      HasPacket (outgoing j) (K-3*(j+1)) T (pathJitter (fun i => δ i+σ i) j + δ j) := by
    intro j hj hp
    have hL : 4 ≤ K-3*j := by omega
    have hm := pathJitter_mono _ hβ (show j ≤ N-1 by omega)
    have hperiod : 15/2 + 2 * pathJitter (fun i => δ i+σ i) j ≤ T := by linarith
    obtain ⟨w⟩ := laws j hj (K-3*j) T _ hL hperiod hp
    simpa only [remaining_step] using cell_hasPacket hp (hδ j) w
  intro j
  induction j with
  | zero =>
    intro hj
    have hp : HasPacket (incoming 0) (K-3*0) T (pathJitter (fun i => δ i+σ i) 0) := by
      simpa [pathJitter] using source
    exact ⟨hp, produce 0 hj hp⟩
  | succ j ih =>
    intro hj
    have prev := (ih (by omega)).2
    have hp := wire_hasPacket prev (delay j) (σ j) (hσ j) (error j) (he j)
    have next : HasPacket (incoming (j+1)) (K-3*(j+1)) T
        (pathJitter (fun i => δ i+σ i) (j+1)) := by
      rw [wires j hj]
      simpa only [pathJitter, add_assoc] using hp
    exact ⟨next, produce (j+1) hj next⟩

theorem root_count {s : Signal} {N K : ℕ} {T J : ℝ} (hN : 0 < N)
    (hp : HasPacket s (K-3*((N-1)+1)) T J) : s.count = K-3*N := by
  have hn : N-1+1 = N := by omega
  simpa only [hn] using hp.1

theorem eight_root_outputs (N : ℕ) : (3*N+8)-3*N = 8 := by omega

def traffic (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => traffic K n + (K-3*(n+1))

theorem traffic_closed_form {N K : ℕ} (hK : 3*N ≤ K) :
    2 * traffic K N + 3*N*(N+1) = 2*N*K := by
  induction N with
  | zero => simp [traffic]
  | succ n ih =>
    have hprev := ih (by omega)
    have hsub : K-3*(n+1)+3*(n+1) = K := by omega
    simp only [traffic]
    nlinarith

theorem traffic_sum (K N : ℕ) :
    traffic K N = (Finset.range N).sum (fun j => K-3*(j+1)) := by
  induction N with
  | zero => simp [traffic]
  | succ n ih => simp [traffic, Finset.sum_range_succ, ih]

theorem realized_total_count {output : ℕ → Signal} {N K : ℕ} {T : ℝ}
    (J : ℕ → ℝ)
    (hp : ∀ j, j < N → HasPacket (output j) (K-3*(j+1)) T (J j)) :
    (Finset.range N).sum (fun j => (output j).count) = traffic K N := by
  rw [traffic_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (hp j (Finset.mem_range.mp hj)).1

theorem fixed_delays_noiseless_period (N : ℕ) :
    15/2 + 2 * pathJitter (fun _ => (0:ℝ)+0) (N-1) = 15/2 := by
  rw [KernelR.Chain.constant_jitter]
  ring

theorem thirty_two_cells_period_eight :
    15/2 + 2 * pathJitter (fun _ => (187/25000:ℝ)+0) (32-1) ≤ 8 := by
  rw [KernelR.Chain.constant_jitter]
  norm_num

end KernelR.Robust
