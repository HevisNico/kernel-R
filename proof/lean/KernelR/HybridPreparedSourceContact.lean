import KernelR.HybridPreparedContact
/-! Sixteen physical period-eight inputs and their routed contact at any date. -/
namespace KernelR.Hybrid
open Set

/-- The sender's physical pulse train and the target's actual routed input list.
The first source is already active; all fifteen successors come from the queue. -/
structure PreparedSourceContact {n θ route s u} (e : @Execution n θ route s u)
    (c : Contact n) (p : Port) (start : ℝ) where
  sender : PreparedTrain e c.source 16
  calendar : e.cellDeliveries c.target = List.ofFn (fun k : Fin 16 =>
    c.token (start + 8 * k.val + restLatency (Real.exp (s.x c.source (.z p)))))

/-- A period-eight physical sender has sixteen routed outputs. Its actual
receiving calendar is supplied here, but neither its outputs nor target inputs
are supplied. No extra cell's events or future source tokens are discarded. -/
theorem Execution.prepared_source_contact_of_calendar {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (c : Contact n) (p : Port) (start : ℝ)
    (hs : PreparedSection s c.source) (hq : s.x c.source .q = 1 / 10)
    (hz : 9 / 5 ≤ Real.exp (s.x c.source (.z p)) ∧ Real.exp (s.x c.source (.z p)) ≤ 12 / 5)
    (hr : s.raw c.source p = some s.time) (ho : ∀ q, q ≠ p → s.raw c.source q = none)
    (hcalendar : e.cellDeliveries c.source = sourceTrain c.source p (start + 8) 8 15)
    (ht : s.time = start) (hu : start + 129 ≤ u.time) (hf : PendingFuture u)
    (hfuture : ∀ d ∈ s.pending, d.cell = c.target → u.time < d.due)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2)
    (hgate : c.opens ≤ start + 3 / 10 ∧ start + 120 + 9 / 10 ≤ c.closes)
    (hdelay : ∀ t, 3 / 10 ≤ c.delay t ∧ c.delay t ≤ 2 / 5) :
    Nonempty (PreparedSourceContact e c p start) := by
  let times : List ℝ := List.ofFn (fun k : Fin 15 => start + 8 + 8 * (k.val : ℝ))
  have htimes : start :: times = List.ofFn (fun k : Fin 16 => start + 8 * (k.val : ℝ)) := by
    have h := congrArg (List.map Delivery.due) (sourceTrain_succ c.source p start 8 15)
    simpa only [sourceTrain,times,List.map_ofFn,Function.comp_def,List.map_cons] using h.symm
  have hcal : e.cellDeliveries c.source = times.map (fun t => ⟨c.source,p,t⟩) := by
    simpa only [times,sourceTrain,List.map_ofFn,Function.comp_def] using hcalendar
  have hspace : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
    rw [ht,htimes]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    linarith
  have hbound : ∀ t ∈ s.time :: times, start ≤ t ∧ t ≤ start + 120 := by
    intro t hm
    rw [ht,htimes] at hm
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hm
    have hlo : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    have hhi : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
    constructor <;> linarith
  have hquiet : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time := by
    intro t hm
    linarith [(hbound t hm).2]
  have hgate' : ∀ t ∈ s.time :: times,
      c.opens ≤ t + 3 / 10 ∧ t + 9 / 10 ≤ c.closes := by
    intro t hm
    have ht' := hbound t hm
    constructor <;> linarith [ht'.1,ht'.2,hgate.1,hgate.2]
  have hcontact := prepared_contact_calendar_of_valid hb c p times e hi hv hs hq hz hr ho
    hcal hspace hquiet hf hfuture hwire hgate' hdelay
  rw [ht,htimes,List.map_ofFn] at hcontact
  obtain ⟨train⟩ := prepared_cell_train_of_valid hb c.source p times e hi hv hs hz hr ho hcal hspace hquiet
  have hcount : times.length + 1 = 16 := by simp only [times,List.length_ofFn]
  have train' : PreparedTrain e c.source 16 := hcount ▸ train
  exact ⟨⟨train',hcontact⟩⟩

/-- Actual pending sources determine the sender calendar. Later sources at the
sender, all other-cell traffic, and all later target sources remain present.
Only the routing projection of this contact and actual no-incoming events at
the sender are fixed. Completeness through the terminal date is not assumed. -/
theorem Execution.prepared_source_contact {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (c : Contact n) (p : Port) (start : ℝ)
    (hs : PreparedSection s c.source) (hq : s.x c.source .q = 1 / 10)
    (hz : 9 / 5 ≤ Real.exp (s.x c.source (.z p)) ∧ Real.exp (s.x c.source (.z p)) ≤ 12 / 5)
    (hr : s.raw c.source p = some s.time) (ho : ∀ q, q ≠ p → s.raw c.source q = none)
    (later : List (Delivery n))
    (hqueue : (s.pending.filter (fun d => d.cell = c.source)).Perm
      (sourceTrain c.source p (start + 8) 8 15 ++ later))
    (hlater : ∀ d ∈ later, u.time < d.due)
    (hclosed : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ c.source)
    (ht : s.time = start) (hu : start + 129 ≤ u.time) (hf : PendingFuture u)
    (hfuture : ∀ d ∈ s.pending, d.cell = c.target → u.time < d.due)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2)
    (hgate : c.opens ≤ start + 3 / 10 ∧ start + 120 + 9 / 10 ≤ c.closes)
    (hdelay : ∀ t, 3 / 10 ≤ c.delay t ∧ c.delay t ≤ 2 / 5) :
    Nonempty (PreparedSourceContact e c p start) := by
  have hcal : e.cellDeliveries c.source = sourceTrain c.source p (start + 8) 8 15 := by
    apply e.cell_deliveries_due_prefix_exact c.source p (sourceTrain c.source p (start + 8) 8 15) later
      hqueue ?_ hlater hf hclosed ?_ ?_
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      have hk : (k.val : ℝ) ≤ 14 := by exact_mod_cast (show k.val ≤ 14 by omega)
      change start + 8 + 8 * (k.val : ℝ) < u.time
      linarith
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨rfl,rfl⟩
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
      change start + 8 + 8 * (k.val : ℝ) ≤ start + 8 + 8 * (l.val : ℝ)
      linarith
  exact e.prepared_source_contact_of_calendar hb hi hv c p start hs hq hz hr ho
    hcal ht hu hf hfuture hwire hgate hdelay

/-- The terminal queue invariant follows from its initial version and causal
wiring; this wrapper keeps that common use explicit. -/
theorem Execution.prepared_source_contact_of_causal {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (c : Contact n) (p : Port) (start : ℝ)
    (hs : PreparedSection s c.source) (hq : s.x c.source .q = 1 / 10)
    (hz : 9 / 5 ≤ Real.exp (s.x c.source (.z p)) ∧ Real.exp (s.x c.source (.z p)) ≤ 12 / 5)
    (hr : s.raw c.source p = some s.time) (ho : ∀ q, q ≠ p → s.raw c.source q = none)
    (later : List (Delivery n))
    (hqueue : (s.pending.filter (fun d => d.cell = c.source)).Perm
      (sourceTrain c.source p (start + 8) 8 15 ++ later))
    (hlater : ∀ d ∈ later, u.time < d.due)
    (hclosed : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ c.source)
    (ht : s.time = start) (hu : start + 129 ≤ u.time)
    (hcausal : CausalRouter route) (hpf : PendingFuture s)
    (hfuture : ∀ d ∈ s.pending, d.cell = c.target → u.time < d.due)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2)
    (hgate : c.opens ≤ start + 3 / 10 ∧ start + 120 + 9 / 10 ≤ c.closes)
    (hdelay : ∀ t, 3 / 10 ≤ c.delay t ∧ c.delay t ≤ 2 / 5) :
    Nonempty (PreparedSourceContact e c p start) :=
  e.prepared_source_contact hb hi hv c p start hs hq hz hr ho later hqueue hlater hclosed ht hu
    (e.pending_future hcausal hpf) hfuture hwire hgate hdelay

/-- Dates retain each fresh wire delay, at any origin and contact. -/
theorem Contact.sixteen_source_date_bounds {n} (c : Contact n) (start : ℝ)
    {G : ℝ} (hg : 9 / 5 ≤ G ∧ G ≤ 12 / 5)
    (hd : ∀ t, 3 / 10 ≤ c.delay t ∧ c.delay t ≤ 2 / 5) (k : Fin 16) :
    start + 3 / 5 < (c.token (start + 8 * k.val + restLatency G)).due ∧
      (c.token (start + 8 * k.val + restLatency G)).due < start + 1213 / 10 := by
  have hs := restLatency_spec hg
  have hklo : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hkhi : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
  have hdelay := hd (start + 8 * k.val + restLatency G)
  dsimp [Contact.token]
  constructor <;> linarith [hs.1,hs.2.1,hdelay.1,hdelay.2]

end KernelR.Hybrid
