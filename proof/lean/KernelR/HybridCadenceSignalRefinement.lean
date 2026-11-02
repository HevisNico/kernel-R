import KernelR.HybridLocalCadenceReceiverPacket
import KernelR.Chain.Refinement

/-! Exact finite-signal refinement for constructed cadence receivers. The
wide residual-high timing bounds come from their actual threshold paths.
Composition below requires a real local receiver at each link; it does not
assert a universal local law or construct a coupled arbitrary-size network. -/
namespace KernelR.Chain

/-- Unlike HasPacket, this relation retains the particular physical packet. -/
def RealizesPacket {m L J} (stream : Signal) (packet : Packet m L J) : Prop :=
  stream.count = m + L ∧ ∀ i, i < m + L → stream.time i = packet.actual i

theorem RealizesPacket.hasPacket {m L J stream} {packet : Packet m L J}
    (h : RealizesPacket stream packet) : HasPacket stream m L J := ⟨h.1,packet,h.2⟩

theorem RealizesPacket.wire {m L J stream} {packet : Packet m L J}
    (h : RealizesPacket stream packet) (d σ : ℝ) (hσ : 0 ≤ σ)
    (error : ℕ → ℝ) (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) :
    RealizesPacket (stream.wire d error) (packet.wire d σ hσ error he) := by
  refine ⟨h.1,?_⟩
  intro i hi
  change stream.time i + d + error i = _
  rw [wire_actual,h.2 i hi]

/-- A local refinement for a given incoming packet and a given physical
outgoing signal. The broader high bounds are the ones proved by dynamics. -/
structure CadenceRelayWitness {m L J} (packet : Packet m L J) (hL : 5 ≤ L)
    (outgoing : Signal) where
  low : ℝ
  firstHigh : ℝ
  restHigh : ℝ
  low_bounds : 65 / 100 ≤ low ∧ low ≤ 66 / 100
  first_bounds : 4 / 25 ≤ firstHigh ∧ firstHigh ≤ 13 / 50
  rest_bounds : 4 / 25 ≤ restHigh ∧ restHigh ≤ 13 / 50
  ordered : firstHigh ≤ restHigh
  realizes : RealizesPacket outgoing (packet.relayCadence hL low firstHigh restHigh
    low_bounds first_bounds rest_bounds ordered)

theorem CadenceRelayWitness.hasPacket {m L J packet hL outgoing}
    (w : @CadenceRelayWitness m L J packet hL outgoing) :
    HasPacket outgoing (m + 2) (L - 4) J := w.realizes.hasPacket

/-- Finite list padding carries no events beyond the exact length. -/
noncomputable def dateSignal (dates : List ℝ) : Signal :=
  ⟨dates.length,fun i => dates[i]?.getD 0⟩

theorem dateSignal_realizes {m L J} (packet : Packet m L J) :
    RealizesPacket (dateSignal (List.ofFn (fun i : Fin (m + L) => packet.actual i.val))) packet := by
  constructor
  · simp [dateSignal]
  · intro i hi
    simp [dateSignal,List.getElem?_ofFn,hi]

end KernelR.Chain

namespace KernelR.Hybrid

/-- No new stream is postulated: the list comes from actual FIRE jumps. -/
theorem Execution.signal_realizes_calendar {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) {m L J}
    (packet : KernelR.Chain.Packet m L J)
    (hcalendar : e.emissionTimes i = List.ofFn (fun k : Fin (m + L) => packet.actual k.val)) :
    KernelR.Chain.RealizesPacket (e.signal i) packet := by
  constructor
  · change (e.emissionTimes i).length = _
    rw [hcalendar,List.length_ofFn]
  · intro k hk
    change (e.emissionTimes i)[k]?.getD 0 = _
    rw [hcalendar]
    simp [hk]

namespace LocalCadenceReceiver
variable {θ s p m L J} {packet : KernelR.Chain.Packet m L J} {terminal}
  (r : LocalCadenceReceiver θ s p packet terminal)

noncomputable abbrev outputSignal : KernelR.Chain.Signal := r.execution.signal 0

noncomputable def inputSignal : KernelR.Chain.Signal :=
  KernelR.Chain.dateSignal (r.execution.deliveries.map Delivery.due)

theorem input_signal_realizes : KernelR.Chain.RealizesPacket r.inputSignal packet := by
  unfold inputSignal
  rw [r.deliveries,List.map_ofFn]
  exact KernelR.Chain.dateSignal_realizes packet

theorem output_signal_realizes : KernelR.Chain.RealizesPacket r.outputSignal r.outputPacket :=
  r.execution.signal_realizes_calendar 0 r.outputPacket r.output_packet_calendar

/-- The witness uses the same actual low root, residual-high FIRE and own
high exact-rest root retained by the receiver construction. -/
noncomputable def signal_witness : KernelR.Chain.CadenceRelayWitness packet r.tail_size r.outputSignal where
  low := r.lowLatency
  firstHigh := r.firstHighLatency
  restHigh := r.restHighLatency
  low_bounds := r.low_latency_bounds
  first_bounds := r.first_high_latency_bounds
  rest_bounds := r.rest_high_latency_bounds
  ordered := r.high_latency_order
  realizes := r.output_signal_realizes

/-- Wire comparison concerns valid event indices; padding is irrelevant. -/
theorem input_signal_wire_dates {m₀ L₀ J₀} (previous : KernelR.Chain.Signal)
    (previousPacket : KernelR.Chain.Packet m₀ L₀ J₀)
    (hprevious : KernelR.Chain.RealizesPacket previous previousPacket)
    (d σ : ℝ) (hσ : 0 ≤ σ) (error : ℕ → ℝ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ)
    (hpacket : HEq packet (previousPacket.wire d σ hσ error he))
    (hshape : m = m₀ ∧ L = L₀ ∧ J = J₀ + σ) :
    r.inputSignal.count = previous.count ∧
      ∀ i,i < previous.count → r.inputSignal.time i = previous.time i + d + error i := by
  rcases hshape with ⟨rfl,rfl,rfl⟩
  have hp : packet = previousPacket.wire d σ hσ error he := eq_of_heq hpacket
  have hr := r.input_signal_realizes
  refine ⟨hr.1.trans hprevious.1.symm,?_⟩
  intro i hi
  have hk : i < m + L := by rwa [hprevious.1] at hi
  calc
    r.inputSignal.time i = packet.actual i := hr.2 i hk
    _ = (previousPacket.wire d σ hσ error he).actual i := congrArg (fun q => q.actual i) hp
    _ = previousPacket.actual i + d + error i := KernelR.Chain.wire_actual _ _ _ _ _ _ _
    _ = previous.time i + d + error i := by rw [hprevious.2 i hk]

end LocalCadenceReceiver

/-- One real receiver of the exact wired packet supplied by its predecessor.
Source preparation is present in receiver.initial_prepared; it is not claimed
for arbitrary cells or derived merely from the packet contract. -/
structure CadencePhysicalLink {m L J} (packet : KernelR.Chain.Packet m L J) where
  sigma : ℝ
  sigma_nonneg : 0 ≤ sigma
  delay : ℝ
  error : ℕ → ℝ
  error_bounds : ∀ i,-sigma ≤ error i ∧ error i ≤ sigma
  parameters : Fin 1 → Parameters
  source : Snapshot 1
  port : Port
  terminal : ℝ
  receiver : LocalCadenceReceiver parameters source port
    (packet.wire delay sigma sigma_nonneg error error_bounds) terminal

namespace CadencePhysicalLink
variable {m L J} {packet : KernelR.Chain.Packet m L J} (link : CadencePhysicalLink packet)

/-- Package an already-constructed receiver without assuming any further
physical preparation or changing its input packet. -/
noncomputable def of_receiver (sigma : ℝ) (hσ : 0 ≤ sigma) (delay : ℝ)
    (error : ℕ → ℝ) (he : ∀ i,-sigma ≤ error i ∧ error i ≤ sigma)
    {θ : Fin 1 → Parameters} {source : Snapshot 1} {port : Port} {terminal : ℝ}
    (receiver : LocalCadenceReceiver θ source port (packet.wire delay sigma hσ error he) terminal) :
    CadencePhysicalLink packet where
  sigma := sigma
  sigma_nonneg := hσ
  delay := delay
  error := error
  error_bounds := he
  parameters := θ
  source := source
  port := port
  terminal := terminal
  receiver := receiver

noncomputable abbrev outputPacket := link.receiver.outputPacket
noncomputable abbrev outputSignal := link.receiver.outputSignal

theorem output_realizes : KernelR.Chain.RealizesPacket link.outputSignal link.outputPacket :=
  link.receiver.output_signal_realizes

theorem wire_dates (previous : KernelR.Chain.Signal)
    (hprevious : KernelR.Chain.RealizesPacket previous packet) :
    link.receiver.inputSignal.count = previous.count ∧
      ∀ i,i < previous.count → link.receiver.inputSignal.time i =
        previous.time i + link.delay + link.error i :=
  link.receiver.input_signal_wire_dates previous packet hprevious link.delay link.sigma
    link.sigma_nonneg link.error link.error_bounds HEq.rfl ⟨rfl,rfl,rfl⟩

end CadencePhysicalLink

/-- A dependent path. Its next packet is the actual output packet of its
preceding receiver, rather than an independently assumed calendar. -/
inductive CadenceReceiverPath : {m L : ℕ} → {J : ℝ} → KernelR.Chain.Packet m L J → ℕ → Type where
  | nil {m L J} (packet : KernelR.Chain.Packet m L J) : CadenceReceiverPath packet 0
  | cons {m L J} {packet : KernelR.Chain.Packet m L J} {n : ℕ}
      (link : CadencePhysicalLink packet) (rest : CadenceReceiverPath link.outputPacket n) :
      CadenceReceiverPath packet (n + 1)

namespace CadenceReceiverPath
variable {m L J} {packet : KernelR.Chain.Packet m L J} {n : ℕ}

noncomputable def signals {m L : ℕ} {J : ℝ} {packet : KernelR.Chain.Packet m L J} {n : ℕ}
    (path : CadenceReceiverPath packet n)
    (leaf : KernelR.Chain.Signal) (i : ℕ) : KernelR.Chain.Signal :=
  match path,i with
  | _,0 => leaf
  | .nil _,_ + 1 => ⟨0,fun _ => 0⟩
  | .cons link rest,j + 1 => rest.signals link.outputSignal j

noncomputable def jitterSchedule {m L : ℕ} {J : ℝ} {packet : KernelR.Chain.Packet m L J} {n : ℕ}
    (path : CadenceReceiverPath packet n) (i : ℕ) : ℝ :=
  match path,i with
  | .nil _,_ => 0
  | .cons link _,0 => link.sigma
  | .cons _ rest,j + 1 => rest.jitterSchedule j

theorem jitter_nonneg (path : CadenceReceiverPath packet n) : ∀ i,0 ≤ path.jitterSchedule i := by
  induction path with
  | nil => intro i; exact le_rfl
  | cons link rest ih =>
    intro i
    cases i with
    | zero => exact link.sigma_nonneg
    | succ i => exact ih i

theorem jitter_head {m L J} {packet : KernelR.Chain.Packet m L J} {n}
    (link : CadencePhysicalLink packet) (rest : CadenceReceiverPath link.outputPacket n) (i : ℕ) :
    KernelR.Chain.pathJitter (jitterSchedule (.cons link rest)) (i + 1) =
      link.sigma + KernelR.Chain.pathJitter rest.jitterSchedule i := by
  induction i with
  | zero => simp [KernelR.Chain.pathJitter,jitterSchedule]
  | succ i ih =>
    rw [KernelR.Chain.pathJitter,ih,KernelR.Chain.pathJitter]
    change (link.sigma + _) + rest.jitterSchedule i = _
    ring

/-- Every node is a finite actual signal. This is conditional on the supplied
physical receiver path and does not assert a global network execution. -/
theorem signals_hasPacket (path : CadenceReceiverPath packet n) (leaf : KernelR.Chain.Signal)
    (hleaf : KernelR.Chain.RealizesPacket leaf packet) :
    ∀ i,i ≤ n → KernelR.Chain.HasPacket (path.signals leaf i)
      (m + 2 * i) (L - 4 * i) (J + KernelR.Chain.pathJitter path.jitterSchedule i) := by
  induction path generalizing leaf with
  | nil packet =>
    intro i hi
    have hz : i = 0 := by omega
    subst i
    simpa [signals,KernelR.Chain.pathJitter] using hleaf.hasPacket
  | @cons m L J packet n link rest ih =>
    intro i hi
    cases i with
    | zero => simpa [signals,KernelR.Chain.pathJitter] using hleaf.hasPacket
    | succ i =>
      have h := ih link.outputSignal link.output_realizes i (by omega)
      have hm : (m + 2) + 2 * i = m + 2 * (i + 1) := by omega
      have hL : (L - 4) - 4 * i = L - 4 * (i + 1) := by omega
      simpa only [signals,hm,hL,jitter_head,add_assoc] using h

theorem node_budget (path : CadenceReceiverPath packet n)
    (hbudget : J + KernelR.Chain.pathJitter path.jitterSchedule n ≤ 1 / 10)
    (i : ℕ) (hi : i ≤ n) :
    J + KernelR.Chain.pathJitter path.jitterSchedule i ≤ 1 / 10 := by
  have hmono := KernelR.Chain.pathJitter_mono path.jitterSchedule path.jitter_nonneg hi
  linarith

/-- Arbitrary finite depth under the current one-tenth budget. The only
physical existence premise is a dependent path of already-proved receivers. -/
theorem realized_chain {K N : ℕ} (hN : 0 < N)
    {leafPacket : KernelR.Chain.Packet 3 (K - 8) 0}
    (path : CadenceReceiverPath leafPacket (N - 1)) (leaf : KernelR.Chain.Signal)
    (hleaf : KernelR.Chain.RealizesPacket leaf leafPacket)
    (hbudget : KernelR.Chain.pathJitter path.jitterSchedule (N - 1) ≤ 1 / 10) :
    ∀ i,i < N → KernelR.Chain.HasPacket (path.signals leaf i)
      (KernelR.Chain.prefixLength i) (KernelR.Chain.tailLength K i)
      (KernelR.Chain.pathJitter path.jitterSchedule i) ∧
      KernelR.Chain.pathJitter path.jitterSchedule i ≤ 1 / 10 := by
  intro i hi
  have h := path.signals_hasPacket leaf hleaf i (by omega)
  refine ⟨?_,?_⟩
  · simpa only [KernelR.Chain.prefixLength,KernelR.Chain.tailLength,zero_add] using h
  · simpa only [zero_add] using path.node_budget (by simpa only [zero_add] using hbudget) i (by omega)

/-- The usual node and total counts now follow from concrete local receiver
witnesses, without a universal RelayLaw premise. -/
theorem realized_counts {K N : ℕ} (hN : 0 < N) (hK : 4 * N + 12 ≤ K)
    {leafPacket : KernelR.Chain.Packet 3 (K - 8) 0}
    (path : CadenceReceiverPath leafPacket (N - 1)) (leaf : KernelR.Chain.Signal)
    (hleaf : KernelR.Chain.RealizesPacket leaf leafPacket)
    (hbudget : KernelR.Chain.pathJitter path.jitterSchedule (N - 1) ≤ 1 / 10) :
    (∀ i,i < N → (path.signals leaf i).count = K - 5 - 2 * i) ∧
      (Finset.range N).sum (fun i => (path.signals leaf i).count) = N * (K - N - 4) := by
  have hpackets := path.realized_chain hN leaf hleaf hbudget
  constructor
  · intro i hi
    exact KernelR.Chain.realized_node_count hK hi (hpackets i hi).1
  · exact KernelR.Chain.realized_total_count hK
      (KernelR.Chain.pathJitter path.jitterSchedule) (fun i hi => (hpackets i hi).1)

theorem realized_root_count {K N : ℕ} (hN : 0 < N) (hK : 4 * N + 12 ≤ K)
    {leafPacket : KernelR.Chain.Packet 3 (K - 8) 0}
    (path : CadenceReceiverPath leafPacket (N - 1)) (leaf : KernelR.Chain.Signal)
    (hleaf : KernelR.Chain.RealizesPacket leaf leafPacket)
    (hbudget : KernelR.Chain.pathJitter path.jitterSchedule (N - 1) ≤ 1 / 10) :
    (path.signals leaf (N - 1)).count = K - 2 * N - 3 := by
  have h := (path.realized_chain hN leaf hleaf hbudget (N - 1) (by omega)).1
  exact h.1.trans (KernelR.Chain.root_outputs hN hK)

end CadenceReceiverPath
end KernelR.Hybrid
