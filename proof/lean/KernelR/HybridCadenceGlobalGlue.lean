import KernelR.HybridConstructedCadenceBC
import KernelR.HybridCadenceRouter

/-! Reconstruct the original three-cell teaching boundary and its exact
cadence router when A is prepended to the actual B/C execution. The receiver's
derived analysis queue is never inserted into the operational source state. -/
namespace KernelR.Hybrid

noncomputable def cadenceAContacts (wireDelay : ℝ → ℝ) : HeadRoutes 2 :=
  fun i time => if i=0 ∧ (640 : ℝ)≤time ∧ time<780 then
    [⟨0,2,time+wireDelay time⟩] else []

noncomputable def cadenceGlobalRouter (forward backward : ℝ → ℝ) : Router 3 :=
  prependRouted (cadenceBCRouter forward) (cadenceAContacts backward)

theorem cadence_a_contacts_strict (wireDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10 : ℝ)≤wireDelay time ∧ wireDelay time≤2/5) :
    StrictHeadRoutes (cadenceAContacts wireDelay) := by
  intro i time d h
  simp only [cadenceAContacts] at h
  split_ifs at h with hg
  · have he : d=(⟨0,2,time+wireDelay time⟩ : Delivery 1) := List.mem_singleton.mp h
    subst d
    change time<time+wireDelay time
    linarith [(hd time).1]
  · contradiction

theorem cadence_global_router_eq (forward backward : ℝ → ℝ) :
    cadenceGlobalRouter forward backward=cadenceRouter forward backward := by
  classical
  funext i time
  refine Fin.cases ?_ (fun j => ?_) i
  · change []=cadenceRouter forward backward 0 time
    simp [cadenceRouter,cadenceForwardContact,cadenceReturnContact,Contact.route]
  · refine Fin.cases ?_ (fun k => ?_) j
    · change (cadenceAContacts backward 0 time).map (Delivery.head (n:=2))=
        cadenceRouter forward backward 1 time
      by_cases hg : (640 : ℝ)≤time ∧ time<780 <;>
        simp [cadenceAContacts,cadenceRouter,cadenceForwardContact,cadenceReturnContact,
          Contact.route,Contact.token,Delivery.head,hg]
    · have hk : k=0 := Subsingleton.elim _ _
      subst k
      change ((cadenceBCContacts forward 0 time).map (Delivery.head (n:=1))).map Delivery.succ ++
          (cadenceAContacts backward 1 time).map (Delivery.head (n:=2))=
        cadenceRouter forward backward 2 time
      by_cases hg : (640 : ℝ)≤time ∧ time<780 <;>
        simp [cadenceBCContacts,cadenceAContacts,cadenceRouter,cadenceForwardContact,cadenceReturnContact,
          Contact.route,Contact.token,Delivery.head,Delivery.succ,hg]

theorem cadence_global_parameters (θ : Fin 1 → Parameters) (freshB freshC : Parameters) :
    prependParameters θ (cadenceBCParameters freshB freshC)=
      extendParameters (extendParameters θ freshB) freshC := by
  funext i
  fin_cases i <;> rfl

noncomputable def cadenceAReceiverSource
    {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (packet : KernelR.Chain.Packet 5 13 (1/10)) : Snapshot 1 :=
  {c.wave.cadence.teaching.final.autonomousView 0 with
    pending:=List.ofFn (fun i : Fin 18 => (⟨0,2,packet.actual i.val⟩ : Delivery 1))}

theorem cadence_a_receiver_source_date
    {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (packet : KernelR.Chain.Packet 5 13 (1/10)) :
    (cadenceAReceiverSource c packet).time=6399/10 := c.wave.cadence.teaching.date

private theorem cadence_glue_snapshot_ext {n} (s u : Snapshot n)
    (ht : s.time=u.time) (hx : s.x=u.x) (hm : s.main=u.main)
    (ha : s.aux=u.aux) (hr : s.raw=u.raw) (hp : s.pending=u.pending) : s=u := by
  cases s
  cases u
  simp_all only

theorem cadence_global_source_eq
    {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward}
    (bc : ConstructedBCadence c) (packet : KernelR.Chain.Packet 5 13 (1/10)) :
    bc.source.prependQueued (cadenceAReceiverSource c packet) (bc.source.pending.map Delivery.succ)=
      c.wave.cadence.teaching.final := by
  apply cadence_glue_snapshot_ext
  · exact bc.source_date.trans c.wave.cadence.teaching.date.symm
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact bc.source_x j
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact bc.source_main j
  · funext i q
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact bc.source_aux j q
  · funext i q
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact bc.source_raw j q
  · change bc.source.pending.map Delivery.succ=c.wave.cadence.teaching.final.pending
    rw [bc.source_pending,c.wave.cadence.teaching.pending]
    simp only [sourceTrain,List.map_ofFn]
    rfl

/-- Only genuine B FIREs in the contact window contribute A analysis inputs.
The emitted times are obtained from the actual B/C execution ledger. -/
theorem cadence_a_head_input_queue {θ route s u}
    (e : @Execution 2 θ route s u) (wireDelay : ℝ → ℝ)
    (hgate : ∀ time∈e.emissionTimes 0, (640 : ℝ)≤time ∧ time<780) :
    e.headInputQueue (cadenceAContacts wireDelay)=
      (e.emissionTimes 0).map (fun time => (⟨0,2,time+wireDelay time⟩ : Delivery 1)) := by
  classical
  have hGate : ∀ ev∈e.ledger.emissions, ev.1=0 → (640 : ℝ)≤ev.2 ∧ ev.2<780 := by
    intro ev hev hi
    apply hgate
    apply List.mem_map.mpr
    refine ⟨ev,?_,rfl⟩
    exact List.mem_filter.mpr ⟨hev,by simpa only [decide_eq_true_eq] using hi⟩
  have aux : ∀ events : List (Fin 2×ℝ),
      (∀ ev∈events, ev.1=0 → (640 : ℝ)≤ev.2 ∧ ev.2<780) →
      events.flatMap (fun ev => cadenceAContacts wireDelay ev.1 ev.2)=
        ((events.filter (fun ev => ev.1=0)).map Prod.snd).map
          (fun time => (⟨0,2,time+wireDelay time⟩ : Delivery 1)) := by
    intro events
    induction events with
    | nil => intro _; rfl
    | cons ev rest ih =>
      intro h
      have hrest : ∀ event∈rest, event.1=0 → (640 : ℝ)≤event.2 ∧ event.2<780 :=
        fun event hevent => h event (by simp [hevent])
      rw [List.flatMap_cons,ih hrest]
      by_cases hi : ev.1=0
      · have hg := h ev (by simp) hi
        have hc : cadenceAContacts wireDelay ev.1 ev.2=[⟨0,2,ev.2+wireDelay ev.2⟩] :=
          ite_eq_left ⟨hi,hg⟩
        rw [hc]
        simp [hi]
      · have hc : cadenceAContacts wireDelay ev.1 ev.2=[] := ite_eq_right (fun hg => hi hg.1)
        rw [hc]
        simp [hi]
  exact aux e.ledger.emissions hGate

namespace CadenceGlobalGlue

theorem params_eq (θ : Fin 1 → Parameters) (freshB freshC : Parameters) :
    prependParameters θ (cadenceBCParameters freshB freshC)=
      extendParameters (extendParameters θ freshB) freshC :=
  cadence_global_parameters θ freshB freshC

theorem router_eq (forward backward : ℝ → ℝ) :
    cadenceGlobalRouter forward backward=cadenceRouter forward backward :=
  cadence_global_router_eq forward backward

theorem source_reconstruct
    {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward}
    (bc : ConstructedBCadence c) (packet : KernelR.Chain.Packet 5 13 (1/10)) :
    bc.source.prependQueued (cadenceAReceiverSource c packet) (bc.source.pending.map Delivery.succ)=
      c.wave.cadence.teaching.final := cadence_global_source_eq bc packet

theorem head_input_queue
    {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward}
    (bc : ConstructedBCadence c) (wireDelay : ℝ → ℝ)
    (hgate : ∀ time∈bc.execution.emissionTimes 0, (640 : ℝ)≤time ∧ time<780) :
    bc.execution.headInputQueue (cadenceAContacts wireDelay)=
      (bc.execution.emissionTimes 0).map (fun time => (⟨0,2,time+wireDelay time⟩ : Delivery 1)) :=
  cadence_a_head_input_queue bc.execution wireDelay hgate

end CadenceGlobalGlue

end KernelR.Hybrid
