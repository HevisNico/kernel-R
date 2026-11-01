import KernelR.HybridContact
import KernelR.HybridPreparedCalendar
import KernelR.HybridCellDueSources
/-! Wire deliveries derived from a physical prepared sender, retaining fresh jitter. -/
namespace KernelR.Hybrid
open Set

/-- A real prepared sender's input calendar determines every actual wire input.
Its output calendar is derived from the ODE, rather than assumed. -/
theorem prepared_contact_calendar_of_valid {n θ ε route s u} (hb : @PhysicalBox n θ ε)
    (c : Contact n) (p : Port) (times : List ℝ) (e : Execution θ route s u)
    (hi : UpperRegion s) (hv : RawValid s) (hs : PreparedSection s c.source)
    (hq : s.x c.source .q = 1 / 10)
    (hz : 9 / 5 ≤ Real.exp (s.x c.source (.z p)) ∧ Real.exp (s.x c.source (.z p)) ≤ 12 / 5)
    (hr : s.raw c.source p = some s.time) (ho : ∀ q, q ≠ p → s.raw c.source q = none)
    (hcalendar : e.cellDeliveries c.source = times.map (fun t => ⟨c.source,p,t⟩))
    (hspace : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (hquiet : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time)
    (hf : PendingFuture u)
    (hfuture : ∀ d ∈ s.pending, d.cell = c.target → u.time < d.due)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2)
    (hgate : ∀ t ∈ s.time :: times, c.opens ≤ t + 3 / 10 ∧ t + 9 / 10 ≤ c.closes)
    (hdelay : ∀ t, 3 / 10 ≤ c.delay t ∧ c.delay t ≤ 2 / 5) :
    e.cellDeliveries c.target = (s.time :: times).map
      (fun t => c.token (t + restLatency (Real.exp (s.x c.source (.z p))))) := by
  have houtputs := prepared_cell_calendar_of_valid hb c.source p times e hi hv hs hq hz hr ho
    hcalendar hspace hquiet
  let latency := restLatency (Real.exp (s.x c.source (.z p)))
  have hlat : 3 / 10 < latency ∧ latency < 9 / 10 := ⟨(restLatency_spec hz).1,(restLatency_spec hz).2.1⟩
  have hselected : (e.emissionTimes c.source).filter (fun t => c.opens ≤ t ∧ t < c.closes) =
      (s.time :: times).map (fun t => t + latency) := by
    rw [houtputs]
    apply List.filter_eq_self.mpr
    intro t ht
    obtain ⟨input,hm,rfl⟩ := List.mem_map.mp ht
    exact decide_eq_true ⟨by linarith [(hgate input hm).1],by linarith [(hgate input hm).2]⟩
  have hdue : ∀ t ∈ e.emissionTimes c.source, c.opens ≤ t → t < c.closes → (c.token t).due < u.time := by
    intro t ht _ _
    rw [houtputs] at ht
    obtain ⟨input,hm,rfl⟩ := List.mem_map.mp ht
    dsimp [Contact.token]
    have hd := (hdelay (input + latency)).2
    have hh := hquiet input hm
    change input + latency + c.delay (input + latency) < u.time
    linarith
  have horder : (((e.emissionTimes c.source).filter (fun t => c.opens ≤ t ∧ t < c.closes)).map c.token).Pairwise
      (fun d f => d.due ≤ f.due) := by
    rw [hselected,List.map_map]
    apply List.pairwise_map.mpr
    apply hspace.imp
    intro t v hgap
    change t + latency + c.delay (t + latency) ≤ v + latency + c.delay (v + latency)
    linarith [(hdelay (t + latency)).2,(hdelay (v + latency)).1]
  rw [e.contact_deliveries c hf hfuture hwire hdue horder,hselected,List.map_map]
  rfl

/-- Common sender latency cancels, but the two fresh wire delays remain. -/
theorem Contact.period_eight_gap {n} (c : Contact n) (t latency : ℝ)
    (hd₁ : 3 / 10 ≤ c.delay (t + latency) ∧ c.delay (t + latency) ≤ 2 / 5)
    (hd₂ : 3 / 10 ≤ c.delay (t + 8 + latency) ∧ c.delay (t + 8 + latency) ≤ 2 / 5) :
    79 / 10 ≤ (c.token (t + 8 + latency)).due - (c.token (t + latency)).due ∧
      (c.token (t + 8 + latency)).due - (c.token (t + latency)).due ≤ 81 / 10 := by
  dsimp [token]
  constructor <;> linarith [hd₁.1,hd₁.2,hd₂.1,hd₂.2]

/-- The first A-to-B contact in the written two-cell protocol. -/
def teachingContact (delay : ℝ → ℝ) : Contact 2 :=
  ⟨0,1,1,160,310,delay⟩

/-- The sixteen actual prepared A inputs give exactly sixteen B deliveries.
The A receiving calendar remains a premise here; neither A outputs nor B
arrivals are assumed. B's direct sources at 320 or later remain in the queue. -/
theorem Execution.teaching_contact_calendar {θ ε route s u} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (hs : PreparedSection s 0) (hq : s.x 0 .q = 1 / 10)
    (hz : 9 / 5 ≤ Real.exp (s.x 0 (.z 0)) ∧ Real.exp (s.x 0 (.z 0)) ≤ 12 / 5)
    (hr : s.raw 0 0 = some s.time) (ho : ∀ q, q ≠ 0 → s.raw 0 q = none)
    (hcalendar : e.cellDeliveries 0 = sourceTrain 0 0 168 8 15)
    (ht : s.time = 160) (hu : u.time = 3199 / 10) (hf : PendingFuture u)
    (hfuture : ∀ d ∈ s.pending, d.cell = 1 → 320 ≤ d.due)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = 1) = (teachingContact delay).route event.1 event.2) :
    e.cellDeliveries 1 = List.ofFn (fun k : Fin 16 =>
      (teachingContact delay).token (160 + 8 * k.val + restLatency (Real.exp (s.x 0 (.z 0))))) := by
  let times : List ℝ := List.ofFn (fun k : Fin 15 => (168 : ℝ) + 8 * (k.val : ℝ))
  have htimes : (160 : ℝ) :: times = List.ofFn (fun k : Fin 16 => (160 : ℝ) + 8 * (k.val : ℝ)) := by
    have h := congrArg (List.map Delivery.due) (sourceTrain_succ (0 : Fin 2) 0 160 8 15)
    simpa only [sourceTrain,times,List.map_ofFn,Function.comp_def,List.map_cons,
      show (160 : ℝ) + 8 = 168 by norm_num] using h.symm
  have hcal : e.cellDeliveries 0 = times.map (fun t => ⟨0,0,t⟩) := by
    simpa only [times,sourceTrain,List.map_ofFn,Function.comp_def] using hcalendar
  have hspace : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
    rw [ht,htimes]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    linarith
  have hbound : ∀ t ∈ s.time :: times, 160 ≤ t ∧ t ≤ 280 := by
    intro t hm
    rw [ht,htimes] at hm
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hm
    have hlo : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    have hhi : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
    constructor <;> linarith
  have hquiet : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time := by
    intro t hm
    rw [hu]
    linarith [(hbound t hm).2]
  have hfuture' : ∀ d ∈ s.pending, d.cell = (teachingContact delay).target → u.time < d.due := by
    intro d hd hc
    rw [hu]
    linarith [hfuture d hd hc]
  have hgate : ∀ t ∈ s.time :: times,
      (teachingContact delay).opens ≤ t + 3 / 10 ∧ t + 9 / 10 ≤ (teachingContact delay).closes := by
    intro t hm
    have ht' := hbound t hm
    dsimp [teachingContact]
    constructor <;> linarith [ht'.1,ht'.2]
  have h := prepared_contact_calendar_of_valid hb (teachingContact delay) 0 times e hi hv hs hq hz hr ho
    hcal hspace hquiet hf hfuture' hwire hgate hdelay
  change e.cellDeliveries 1 = (s.time :: times).map (fun t =>
    (teachingContact delay).token (t + restLatency (Real.exp (s.x 0 (.z 0))))) at h
  rw [ht,htimes,List.map_ofFn] at h
  exact h

/-- Once source 160 is active, its fifteen successors can be obtained from the
actual pending queue. No receiving calendar or output count is assumed. -/
theorem Execution.teaching_contact_sources {θ ε route s u} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (hs : PreparedSection s 0) (hq : s.x 0 .q = 1 / 10)
    (hz : 9 / 5 ≤ Real.exp (s.x 0 (.z 0)) ∧ Real.exp (s.x 0 (.z 0)) ≤ 12 / 5)
    (hr : s.raw 0 0 = some s.time) (ho : ∀ q, q ≠ 0 → s.raw 0 q = none)
    (hqueue : (s.pending.filter (fun d => d.cell = 0)).Perm (sourceTrain 0 0 168 8 15))
    (hclosed : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ 0)
    (ht : s.time = 160) (hu : u.time = 3199 / 10) (hf : PendingFuture u)
    (hfuture : ∀ d ∈ s.pending, d.cell = 1 → 320 ≤ d.due)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = 1) = (teachingContact delay).route event.1 event.2) :
    e.cellDeliveries 1 = List.ofFn (fun k : Fin 16 =>
      (teachingContact delay).token (160 + 8 * k.val + restLatency (Real.exp (s.x 0 (.z 0))))) := by
  have hcal : e.cellDeliveries 0 = sourceTrain 0 0 168 8 15 := by
    apply e.cell_deliveries_due_prefix_exact 0 0 (sourceTrain 0 0 168 8 15) []
      (by simpa only [List.append_nil] using hqueue) ?_ (by simp) hf hclosed ?_ ?_
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      have hk : (k.val : ℝ) ≤ 14 := by exact_mod_cast (show k.val ≤ 14 by omega)
      rw [hu]
      change 168 + 8 * (k.val : ℝ) < 3199 / 10
      linarith
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨rfl,rfl⟩
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
      change 168 + 8 * (k.val : ℝ) ≤ 168 + 8 * (l.val : ℝ)
      linarith
  exact e.teaching_contact_calendar hb hi hv hs hq hz hr ho hcal ht hu hf hfuture delay hdelay hwire

/-- Every teaching token is strictly between 160.6 and 281.3, using only the
proved real latency bracket and its own independent wire delay. -/
theorem teachingContact.date_bounds {G : ℝ} (hg : 9 / 5 ≤ G ∧ G ≤ 12 / 5)
    (delay : ℝ → ℝ) (hd : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) (k : Fin 16) :
    803 / 5 < ((teachingContact delay).token (160 + 8 * k.val + restLatency G)).due ∧
      ((teachingContact delay).token (160 + 8 * k.val + restLatency G)).due < 2813 / 10 := by
  have hs := restLatency_spec hg
  have hklo : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hkhi : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
  have hdelay := hd (160 + 8 * k.val + restLatency G)
  dsimp [Contact.token,teachingContact]
  constructor <;> linarith [hs.1,hs.2.1,hdelay.1,hdelay.2]

end KernelR.Hybrid
