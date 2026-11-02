import KernelR.HybridFiniteCadenceContact
import KernelR.HybridCadencePacketRelay

/-! A uniform envelope for actual physical packet dates. Its propagation
keeps the full wire errors and the directly proved broad relay latencies. -/
namespace KernelR.Hybrid

noncomputable def finiteCadenceTerminal (start : ℝ) (N K : ℕ) : ℝ :=
  start+4*((K-1 : ℕ) : ℝ)+(11/10)*((N-1 : ℕ) : ℝ)+8

structure CadencePacketEnvelope {m L J} (packet : KernelR.Chain.Packet m L J)
    (start : ℝ) (K depth : ℕ) : Prop where
  lower : ∀ i : Fin (m+L), start≤packet.actual i.val
  upper : ∀ i : Fin (m+L), packet.actual i.val≤
    start+4*((K-1 : ℕ) : ℝ)+(11/10)*(depth : ℝ)+9/10

namespace CadencePacketEnvelope
variable {m L J start K depth} {packet : KernelR.Chain.Packet m L J}
  (env : CadencePacketEnvelope packet start K depth)
include env

theorem sampled_wire_bounds (delay : ℝ → ℝ) (centre sigma : ℝ) (hsigma : 0≤sigma)
    (herr : ∀ time, -sigma≤delay time-centre ∧ delay time-centre≤sigma)
    (hd : ∀ time, (3/10 : ℝ)≤delay time ∧ delay time≤2/5) (i : Fin (m+L)) :
    start+3/10≤(packet.sampleWireDelay delay centre sigma hsigma herr).actual i.val ∧
    (packet.sampleWireDelay delay centre sigma hsigma herr).actual i.val≤
      start+4*((K-1 : ℕ) : ℝ)+(11/10)*(depth : ℝ)+13/10 := by
  rw [KernelR.Chain.Packet.sample_wire_delay_actual]
  constructor <;> linarith [env.lower i,env.upper i,(hd (packet.actual i.val)).1,(hd (packet.actual i.val)).2]

theorem propagate (delay : ℝ → ℝ) (centre sigma : ℝ) (hsigma : 0≤sigma)
    (herr : ∀ time, -sigma≤delay time-centre ∧ delay time-centre≤sigma)
    (hd : ∀ time, (3/10 : ℝ)≤delay time ∧ delay time≤2/5)
    (hL : 5≤L) (low firstHigh restHigh : ℝ)
    (hlow : 65/100≤low ∧ low≤66/100)
    (hfirst : 4/25≤firstHigh ∧ firstHigh≤13/50)
    (hrest : 4/25≤restHigh ∧ restHigh≤13/50)
    (horder : firstHigh≤restHigh) :
    CadencePacketEnvelope
      ((packet.sampleWireDelay delay centre sigma hsigma herr).relayCadence hL
        low firstHigh restHigh hlow hfirst hrest horder) start K (depth+1) := by
  constructor
  · intro i
    obtain ⟨k,latency,hlo,hhi,hdate⟩ := KernelR.Chain.relay_cadence_input_origin
      (packet.sampleWireDelay delay centre sigma hsigma herr) hL low firstHigh restHigh
      hlow hfirst hrest horder i
    rw [hdate]
    linarith [(env.sampled_wire_bounds delay centre sigma hsigma herr hd k).1]
  · intro i
    obtain ⟨k,latency,hlo,hhi,hdate⟩ := KernelR.Chain.relay_cadence_input_origin
      (packet.sampleWireDelay delay centre sigma hsigma herr) hL low firstHigh restHigh
      hlow hfirst hrest horder i
    rw [hdate]
    have h := (env.sampled_wire_bounds delay centre sigma hsigma herr hd k).2
    push_cast
    linarith

theorem gate {N : ℕ} (hdepth : depth<N) (i : Fin (m+L)) :
    start≤packet.actual i.val ∧ packet.actual i.val<finiteCadenceTerminal start N K+1 := by
  have hn : (depth : ℝ)≤((N-1 : ℕ) : ℝ) := by exact_mod_cast (show depth≤N-1 by omega)
  exact ⟨env.lower i,by dsimp [finiteCadenceTerminal]; linarith [env.upper i]⟩

theorem received_terminal {N : ℕ} (hdepth : depth<N)
    (delay : ℝ → ℝ) (centre sigma : ℝ) (hsigma : 0≤sigma)
    (herr : ∀ time, -sigma≤delay time-centre ∧ delay time-centre≤sigma)
    (hd : ∀ time, (3/10 : ℝ)≤delay time ∧ delay time≤2/5) (i : Fin (m+L)) :
    (packet.sampleWireDelay delay centre sigma hsigma herr).actual i.val+19/5≤
      finiteCadenceTerminal start N K := by
  have hn : (depth : ℝ)≤((N-1 : ℕ) : ℝ) := by exact_mod_cast (show depth≤N-1 by omega)
  dsimp [finiteCadenceTerminal]
  linarith [(env.sampled_wire_bounds delay centre sigma hsigma herr hd i).2]

end CadencePacketEnvelope

theorem finite_cadence_terminal_after_leaf {start : ℝ} {N K : ℕ}
    (hK : 1≤K) : start+4*(K : ℝ)<finiteCadenceTerminal start N K := by
  have hk : ((K-1 : ℕ) : ℝ)=(K : ℝ)-1 := by rw [Nat.cast_sub hK]; norm_num
  have hn : (0 : ℝ)≤((N-1 : ℕ) : ℝ) := Nat.cast_nonneg _
  dsimp [finiteCadenceTerminal]
  rw [hk]
  linarith

end KernelR.Hybrid
