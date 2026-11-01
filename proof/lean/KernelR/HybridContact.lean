import KernelR.HybridRoutedInputs
import KernelR.HybridEventBudget
/-! A gated physical contact and its tokens extracted from actual emissions. -/
namespace KernelR.Hybrid
attribute [local instance] Classical.propDecidable

structure Contact (n : ℕ) where
  source : Fin n
  target : Fin n
  port : Port
  opens : ℝ
  closes : ℝ
  delay : ℝ → ℝ

def Contact.token {n} (c : Contact n) (t : ℝ) : Delivery n := ⟨c.target,c.port,t + c.delay t⟩

noncomputable def Contact.route {n} (c : Contact n) : Router n := fun i t =>
  if i = c.source ∧ c.opens ≤ t ∧ t < c.closes then [c.token t] else []

theorem Contact.causal {n} (c : Contact n) (hd : ∀ t, 0 ≤ c.delay t) : CausalRouter c.route := by
  intro i t d hm
  by_cases h : i = c.source ∧ c.opens ≤ t ∧ t < c.closes
  · simp only [route,ite_eq_left h,List.mem_singleton] at hm
    subst d
    dsimp [token]
    linarith [hd t]
  · simp only [route,ite_eq_right h,List.not_mem_nil] at hm

theorem Contact.fanout {n} (c : Contact n) : FanoutBound c.route 1 := by
  intro i t
  unfold route
  split_ifs <;> simp

/-- Other contacts may target other cells. Only this receiving cell's routing
projection is fixed, and only at emissions present in the supplied execution. -/
theorem Execution.issuedTo_contact {n θ route s u} (e : @Execution n θ route s u)
    (c : Contact n)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2) :
    e.issuedTo c.target = ((e.emissionTimes c.source).filter
      (fun t => c.opens ≤ t ∧ t < c.closes)).map c.token := by
  have hfilter : ∀ events : List (Fin n × ℝ),
      (∀ event ∈ events, (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2) →
      (events.flatMap (fun event => route event.1 event.2)).filter (fun d => d.cell = c.target) =
        events.flatMap (fun event => c.route event.1 event.2) := by
    intro events
    induction events with
    | nil => simp
    | cons event events ih =>
      intro hw
      simp only [List.flatMap_cons,List.filter_append,hw event (by simp),
        ih (fun event he => hw event (List.mem_cons_of_mem _ he))]
  have hlist : ∀ events : List (Fin n × ℝ),
      events.flatMap (fun event => c.route event.1 event.2) =
      (((events.filter (fun event => event.1 = c.source)).map Prod.snd).filter
        (fun t => c.opens ≤ t ∧ t < c.closes)).map c.token := by
    intro events
    induction events with
    | nil => simp
    | cons event events ih =>
      rcases event with ⟨i,t⟩
      rw [List.flatMap_cons,ih]
      by_cases hc : i = c.source
      · by_cases ht : c.opens ≤ t ∧ t < c.closes
        · simp [Contact.route,hc,ht]
        · simp [Contact.route,hc,ht]
      · simp [Contact.route,hc]
  exact (hfilter e.ledger.emissions hwire).trans (hlist e.ledger.emissions)

/-- A complete actual receiving list is obtained from the real emission ledger,
with no assumed pulse-case word or arrival calendar. Later external sources
and other-cell traffic remain present. -/
theorem Execution.contact_deliveries {n θ route s u} (e : @Execution n θ route s u)
    (c : Contact n) (hf : PendingFuture u)
    (hs : ∀ d ∈ s.pending, d.cell = c.target → u.time < d.due)
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2)
    (hdue : ∀ t ∈ e.emissionTimes c.source, c.opens ≤ t → t < c.closes → (c.token t).due < u.time)
    (horder : (((e.emissionTimes c.source).filter
      (fun t => c.opens ≤ t ∧ t < c.closes)).map c.token).Pairwise (fun d f => d.due ≤ f.due)) :
    e.cellDeliveries c.target = ((e.emissionTimes c.source).filter
      (fun t => c.opens ≤ t ∧ t < c.closes)).map c.token := by
  have hissued := e.issuedTo_contact c hwire
  have hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2,
      d.cell = c.target → d.due < u.time := by
    intro event he d hd hc
    have hm : d ∈ (route event.1 event.2).filter (fun d => d.cell = c.target) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hd,hc⟩
    rw [hwire event he] at hm
    unfold Contact.route at hm
    split_ifs at hm with h
    · simp only [List.mem_singleton] at hm
      subst d
      have ht : event.2 ∈ e.emissionTimes c.source := by
        apply List.mem_map.mpr
        exact ⟨event,by simp [List.mem_filter,he,h.1],rfl⟩
      exact hdue event.2 ht h.2.1 h.2.2
    · contradiction
  rw [← hissued]
  apply e.cell_routed_exact c.target c.port hf hs hr
  · intro d hd
    rw [hissued] at hd
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hd
    rfl
  · rw [hissued]
    exact horder

end KernelR.Hybrid
