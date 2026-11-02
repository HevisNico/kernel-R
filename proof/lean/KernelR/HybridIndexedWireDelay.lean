import KernelR.HybridFiniteCadencePacketGaps
import KernelR.HybridCausalHeadQueue

/-! A finite sequence of per-emission wire errors is implemented by one native
real-time delay function. The function is bounded at every real time, including
those absent from the emission list. Packet correspondence is proved only
against the actual execution ledger supplied by its physical constructor. -/
namespace KernelR.Hybrid

/-- The absent-time index is the list length, so a bound on all error indices
also controls this native delay away from all actual emissions. -/
noncomputable def indexedWireDelay (dates : List ℝ) (center : ℝ)
    (error : ℕ → ℝ) (time : ℝ) : ℝ := by
  classical
  exact center + error (dates.idxOf time)

theorem indexedWireDelay_at (dates : List ℝ) (center : ℝ) (error : ℕ → ℝ)
    (hn : dates.Nodup) (i : ℕ) (hi : i < dates.length) :
    indexedWireDelay dates center error dates[i] = center + error i := by
  classical
  simp only [indexedWireDelay,hn.idxOf_getElem i hi]

theorem indexedWireDelay_absent (dates : List ℝ) (center : ℝ) (error : ℕ → ℝ)
    (time : ℝ) (ht : time ∉ dates) :
    indexedWireDelay dates center error time = center + error dates.length := by
  classical
  simp only [indexedWireDelay,List.idxOf_eq_length ht]

theorem indexedWireDelay_bounds (dates : List ℝ) (center σ : ℝ) (error : ℕ → ℝ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) (time : ℝ) :
    center - σ ≤ indexedWireDelay dates center error time ∧
      indexedWireDelay dates center error time ≤ center + σ := by
  classical
  have h := he (dates.idxOf time)
  unfold indexedWireDelay
  constructor <;> linarith [h.1,h.2]

theorem indexedWireDelay_physical_bounds (dates : List ℝ) (center σ : ℝ) (error : ℕ → ℝ)
    (hc : 3 / 10 + σ ≤ center ∧ center ≤ 2 / 5 - σ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) (time : ℝ) :
    3 / 10 ≤ indexedWireDelay dates center error time ∧
      indexedWireDelay dates center error time ≤ 2 / 5 := by
  have h := indexedWireDelay_bounds dates center σ error he time
  constructor <;> linarith [hc.1,hc.2,h.1,h.2]

/-- Real tokens for a single newly attached receiving cell. -/
noncomputable def indexedHeadContact {n} (source : Fin n) (port : Port)
    (delay : ℝ → ℝ) : HeadRoutes n := fun i time =>
  if i=source then [⟨0,port,time + delay time⟩] else []

theorem indexedHeadContact_strict {n} (source : Fin n) (port : Port) (delay : ℝ → ℝ)
    (hdelay : ∀ time,0 < delay time) : StrictHeadRoutes (indexedHeadContact source port delay) := by
  intro i time token ht
  unfold indexedHeadContact at ht
  split_ifs at ht with hi
  · simp only [List.mem_singleton] at ht
    subst token
    change time < time + delay time
    linarith [hdelay time]
  · contradiction

/-- The contact queue is extracted from actual FIREs, including their order. -/
theorem Execution.headInputQueue_indexedContact {n θ route s u}
    (e : @Execution n θ route s u) (source : Fin n) (port : Port) (delay : ℝ → ℝ) :
    e.headInputQueue (indexedHeadContact source port delay) =
      (e.emissionTimes source).map (fun time => (⟨0,port,time + delay time⟩ : Delivery 1)) := by
  have h : ∀ events : List (Fin n × ℝ),
      events.flatMap (fun event => indexedHeadContact source port delay event.1 event.2) =
      ((events.filter (fun event => event.1=source)).map Prod.snd).map
        (fun time => (⟨0,port,time + delay time⟩ : Delivery 1)) := by
    intro events
    induction events with
    | nil => rfl
    | cons event events ih =>
      rcases event with ⟨i,time⟩
      rw [List.flatMap_cons,ih]
      by_cases hi : i=source <;> simp [indexedHeadContact,hi]
  exact h e.ledger.emissions

/-- The defining list is the real emission ledger, rather than an independent
future output calendar or a preloaded global wire queue. -/
noncomputable def Execution.indexedWireDelay {n θ route s u}
    (e : @Execution n θ route s u) (source : Fin n) (center : ℝ) (error : ℕ → ℝ) : ℝ → ℝ :=
  KernelR.Hybrid.indexedWireDelay (e.emissionTimes source) center error

theorem Execution.indexedWireDelay_at {n θ route s u}
    (e : @Execution n θ route s u) (source : Fin n) (center : ℝ) (error : ℕ → ℝ)
    (hn : (e.emissionTimes source).Nodup) (i : ℕ) (hi : i < (e.emissionTimes source).length) :
    e.indexedWireDelay source center error (e.emissionTimes source)[i] = center + error i :=
  KernelR.Hybrid.indexedWireDelay_at _ center error hn i hi

theorem Execution.indexedWireDelay_physical_bounds {n θ route s u}
    (e : @Execution n θ route s u) (source : Fin n) (center σ : ℝ) (error : ℕ → ℝ)
    (hc : 3 / 10 + σ ≤ center ∧ center ≤ 2 / 5 - σ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) (time : ℝ) :
    3 / 10 ≤ e.indexedWireDelay source center error time ∧
      e.indexedWireDelay source center error time ≤ 2 / 5 :=
  KernelR.Hybrid.indexedWireDelay_physical_bounds _ center σ error hc he time

/-- Every exact finite packet has distinct actual dates under the full written
budget. This is a timing fact, not an extension of the receiver's budget. -/
theorem packet_dates_nodup {m L J} (packet : KernelR.Chain.Packet m L J) (hJ : J ≤ 3 / 20) :
    (List.ofFn (fun i : Fin (m + L) => packet.actual i.val)).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j he
  exact Fin.ext ((packet.full_budget_strict_mono hJ).injective he)

theorem indexedWireDelay_packet_at {m L J} (packet : KernelR.Chain.Packet m L J)
    (hJ : J ≤ 3 / 20) (center : ℝ) (error : ℕ → ℝ) (i : Fin (m + L)) :
    indexedWireDelay (List.ofFn (fun k : Fin (m + L) => packet.actual k.val)) center error
      (packet.actual i.val) = center + error i.val := by
  have h := indexedWireDelay_at _ center error (packet_dates_nodup packet hJ) i.val
    (by simpa only [List.length_ofFn] using i.isLt)
  simpa only [List.getElem_ofFn] using h

/-- The packet wire's per-index jitter is realized by one ordinary real-time
router delay on the actual dates, with no signal retiming. -/
theorem indexedWireDelay_wire_actual {m L J} (packet : KernelR.Chain.Packet m L J)
    (hJ : J ≤ 3 / 20) (center σ : ℝ) (hσ : 0 ≤ σ) (error : ℕ → ℝ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) (i : Fin (m + L)) :
    (packet.wire center σ hσ error he).actual i.val = packet.actual i.val +
      indexedWireDelay (List.ofFn (fun k : Fin (m + L) => packet.actual k.val)) center error (packet.actual i.val) := by
  rw [KernelR.Chain.wire_actual,indexedWireDelay_packet_at packet hJ]
  ring

/-- Consume a packet refinement already proved by a physical execution's
constructor. The chosen native delay always indexes that actual ledger. -/
theorem Execution.indexedWireDelay_packet_at {n θ route s u m L J}
    (e : @Execution n θ route s u) (source : Fin n) (packet : KernelR.Chain.Packet m L J)
    (hcalendar : e.emissionTimes source=List.ofFn (fun k : Fin (m + L) => packet.actual k.val))
    (hJ : J ≤ 3 / 20) (center : ℝ) (error : ℕ → ℝ) (i : Fin (m + L)) :
    e.indexedWireDelay source center error (packet.actual i.val)=center + error i.val := by
  unfold Execution.indexedWireDelay
  rw [hcalendar]
  exact KernelR.Hybrid.indexedWireDelay_packet_at packet hJ center error i

theorem Execution.indexedWireDelay_wire_actual {n θ route s u m L J}
    (e : @Execution n θ route s u) (source : Fin n) (packet : KernelR.Chain.Packet m L J)
    (hcalendar : e.emissionTimes source=List.ofFn (fun k : Fin (m + L) => packet.actual k.val))
    (hJ : J ≤ 3 / 20) (center σ : ℝ) (hσ : 0 ≤ σ) (error : ℕ → ℝ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) (i : Fin (m + L)) :
    (packet.wire center σ hσ error he).actual i.val=
      packet.actual i.val+e.indexedWireDelay source center error (packet.actual i.val) := by
  rw [KernelR.Chain.wire_actual,e.indexedWireDelay_packet_at source packet hcalendar hJ]
  ring

/-- The actual contact queue is exactly the receiver's wired packet source
list. The surrounding weaver still issues each token at its actual FIRE. -/
theorem Execution.indexedWire_head_tokens {n θ route s u m L J}
    (e : @Execution n θ route s u) (source : Fin n) (port : Port)
    (packet : KernelR.Chain.Packet m L J)
    (hcalendar : e.emissionTimes source=List.ofFn (fun k : Fin (m + L) => packet.actual k.val))
    (hJ : J ≤ 3 / 20) (center σ : ℝ) (hσ : 0 ≤ σ) (error : ℕ → ℝ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) :
    e.headInputQueue (indexedHeadContact source port (e.indexedWireDelay source center error)) =
      List.ofFn (fun i : Fin (m + L) =>
        (⟨0,port,(packet.wire center σ hσ error he).actual i.val⟩ : Delivery 1)) := by
  rw [e.headInputQueue_indexedContact,hcalendar,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [e.indexedWireDelay_wire_actual source packet hcalendar hJ center σ hσ error he i]
  rfl

end KernelR.Hybrid
