import KernelR.HybridCausalHeadSignals
import KernelR.HybridFiniteCadencePacketGaps

/-! Finite-chain contacts sample delay functions at actual FIRE dates. The
receiver analysis queue is derived from the real tail ledger. No such queue
is inserted into the operational global source state. -/
namespace KernelR.Hybrid
attribute [local instance] Classical.propDecidable

noncomputable def finiteCadenceHeadContact {n} (child : Fin n) (port : Port)
    (opens closes : ℝ) (delay : ℝ → ℝ) : HeadRoutes n :=
  fun i time => if i=child ∧ opens≤time ∧ time<closes then
    [⟨0,port,time+delay time⟩] else []

theorem finite_cadence_head_contact_strict {n} (child : Fin n) (port : Port)
    (opens closes : ℝ) (delay : ℝ → ℝ) (hd : ∀ time, 0<delay time) :
    StrictHeadRoutes (finiteCadenceHeadContact child port opens closes delay) := by
  intro i time d h
  simp only [finiteCadenceHeadContact] at h
  split_ifs at h with hg
  · have he : d=(⟨0,port,time+delay time⟩ : Delivery 1) := List.mem_singleton.mp h
    subst d
    change time<time+delay time
    linarith [hd time]
  · contradiction

theorem finite_cadence_head_contact_before_open {n} (child : Fin n) (port : Port)
    (opens closes : ℝ) (delay : ℝ → ℝ) (i : Fin n) {time : ℝ} (ht : time<opens) :
    finiteCadenceHeadContact child port opens closes delay i time=[] := by
  simp [finiteCadenceHeadContact,show ¬opens≤time by linarith]

theorem finite_cadence_head_input_queue {n θ route s u}
    (e : @Execution n θ route s u) (child : Fin n) (port : Port)
    (opens closes : ℝ) (delay : ℝ → ℝ)
    (hgate : ∀ time∈e.emissionTimes child, opens≤time ∧ time<closes) :
    e.headInputQueue (finiteCadenceHeadContact child port opens closes delay)=
      (e.emissionTimes child).map (fun time => (⟨0,port,time+delay time⟩ : Delivery 1)) := by
  have hGate : ∀ ev∈e.ledger.emissions, ev.1=child → opens≤ev.2 ∧ ev.2<closes := by
    intro ev hev hi
    apply hgate
    apply List.mem_map.mpr
    refine ⟨ev,?_,rfl⟩
    exact List.mem_filter.mpr ⟨hev,by simpa only [decide_eq_true_eq] using hi⟩
  have aux : ∀ events : List (Fin n×ℝ),
      (∀ ev∈events, ev.1=child → opens≤ev.2 ∧ ev.2<closes) →
      events.flatMap (fun ev => finiteCadenceHeadContact child port opens closes delay ev.1 ev.2)=
        ((events.filter (fun ev => ev.1=child)).map Prod.snd).map
          (fun time => (⟨0,port,time+delay time⟩ : Delivery 1)) := by
    intro events
    induction events with
    | nil => intro _; rfl
    | cons ev rest ih =>
      intro h
      have hrest : ∀ event∈rest, event.1=child → opens≤event.2 ∧ event.2<closes :=
        fun event hevent => h event (by simp [hevent])
      rw [List.flatMap_cons,ih hrest]
      by_cases hi : ev.1=child
      · have hg := h ev (by simp) hi
        have hc : finiteCadenceHeadContact child port opens closes delay ev.1 ev.2=
            [⟨0,port,ev.2+delay ev.2⟩] := ite_eq_left ⟨hi,hg⟩
        rw [hc]
        simp [hi]
      · have hc : finiteCadenceHeadContact child port opens closes delay ev.1 ev.2=[] :=
          ite_eq_right (fun hg => hi hg.1)
        rw [hc]
        simp [hi]
  exact aux e.ledger.emissions hGate

/-- Every link is closed before the common fast-phase opening. -/
noncomputable def finiteCadenceRouter (delay : ℕ → ℝ → ℝ) (opens closes : ℝ) :
    (n : ℕ) → Router (n+1)
  | 0 => fun _ _ => []
  | n+1 => prependRouted (finiteCadenceRouter delay opens closes n)
      (finiteCadenceHeadContact 0 2 opens closes (delay n))

theorem finite_cadence_router_before_open (delay : ℕ → ℝ → ℝ) (opens closes : ℝ)
    (n : ℕ) (i : Fin (n+1)) {time : ℝ} (ht : time<opens) :
    finiteCadenceRouter delay opens closes n i time=[] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change (finiteCadenceRouter delay opens closes n i time).map Delivery.succ ++
        (finiteCadenceHeadContact 0 2 opens closes (delay n) i time).map Delivery.head=[]
      rw [ih i,finite_cadence_head_contact_before_open _ _ _ _ _ _ ht]
      rfl

end KernelR.Hybrid

namespace KernelR.Chain

/-- Padding samples are bounded as well; only finite packet dates are physical
occurrences, and none is retimed by this proof witness. -/
noncomputable def Packet.sampleWireDelay {m L J} (p : Packet m L J)
    (delay : ℝ → ℝ) (centre sigma : ℝ) (hsigma : 0≤sigma)
    (herr : ∀ time, -sigma≤delay time-centre ∧ delay time-centre≤sigma) :
    Packet m L (J+sigma) :=
  p.wire centre sigma hsigma (fun i => delay (p.actual i)-centre)
    (fun i => herr (p.actual i))

theorem Packet.sample_wire_delay_actual {m L J} (p : Packet m L J)
    (delay : ℝ → ℝ) (centre sigma : ℝ) (hsigma : 0≤sigma)
    (herr : ∀ time, -sigma≤delay time-centre ∧ delay time-centre≤sigma) (i : ℕ) :
    (p.sampleWireDelay delay centre sigma hsigma herr).actual i=p.actual i+delay (p.actual i) := by
  rw [Packet.sampleWireDelay,wire_actual]
  ring

end KernelR.Chain

namespace KernelR.Hybrid

theorem finite_cadence_head_queue_packet {n θ route s u m L J}
    (e : @Execution n θ route s u) (child : Fin n) (port : Port)
    (packet : KernelR.Chain.Packet m L J) (opens closes : ℝ) (delay : ℝ → ℝ)
    (centre sigma : ℝ) (hsigma : 0≤sigma)
    (herr : ∀ time, -sigma≤delay time-centre ∧ delay time-centre≤sigma)
    (hcalendar : e.emissionTimes child=List.ofFn (fun i : Fin (m+L) => packet.actual i.val))
    (hgate : ∀ i : Fin (m+L), opens≤packet.actual i.val ∧ packet.actual i.val<closes) :
    e.headInputQueue (finiteCadenceHeadContact child port opens closes delay)=
      List.ofFn (fun i : Fin (m+L) =>
        (⟨0,port,(packet.sampleWireDelay delay centre sigma hsigma herr).actual i.val⟩ : Delivery 1)) := by
  have hg : ∀ time∈e.emissionTimes child, opens≤time ∧ time<closes := by
    intro time ht
    rw [hcalendar] at ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact hgate i
  rw [finite_cadence_head_input_queue e child port opens closes delay hg,hcalendar,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,KernelR.Chain.Packet.sample_wire_delay_actual]

end KernelR.Hybrid
