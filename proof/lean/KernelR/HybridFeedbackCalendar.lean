import KernelR.HybridEntryRouter
import KernelR.HybridRestingInput
import KernelR.HybridBoundaryIdle
/-! The real return-wire calendar retains its first residual-charge latency. -/
namespace KernelR.Hybrid

/-- Quiet waiting preserves exact resting charge before the next source. -/
theorem CellDeliveryStep.prepared_rest_input {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hr : ∀ p, s.raw i p = none) : PreparedSection cut.afterArrival i ∧ cut.afterArrival.x i .q = 1 / 10 := by
  obtain ⟨idle⟩ := cut.span.idle_prepared i hs hq hr cut.no_arrivals_before
  exact ⟨cut.prepared idle.prepared,by rw [cut.entry.physical_continuous]; exact idle.charge_rest⟩

/-- The first return pulse has its own latency; later prepared pulses share
the same-gain resting reference. All fresh wire delays are retained. -/
def feedbackArrivalDates (first rest : ℝ) (delay : ℝ → ℝ) : List ℝ :=
  (344 + first + delay (344 + first)) :: List.ofFn (fun k : Fin 12 =>
    352 + 8 * (k.val : ℝ) + rest + delay (352 + 8 * (k.val : ℝ) + rest))

theorem feedbackArrivalDates.length (first rest : ℝ) (delay : ℝ → ℝ) :
    (feedbackArrivalDates first rest delay).length = 13 := by simp [feedbackArrivalDates]

/-- Positive residual can advance only the first sender firing, so the first
wire gap is no shorter than the ordinary period-eight jittered gap. -/
theorem feedbackArrivalDates.spaced {first rest : ℝ} (hfirst : first ≤ rest)
    (delay : ℝ → ℝ) (hd : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) :
    (feedbackArrivalDates first rest delay).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro v hv
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hv
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    linarith [(hd (344 + first)).2,(hd (352 + 8 * (k.val : ℝ) + rest)).1]
  · apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    linarith [(hd (352 + 8 * (k.val : ℝ) + rest)).2,(hd (352 + 8 * (l.val : ℝ) + rest)).1]

theorem feedbackArrivalDates.bounds {first rest : ℝ}
    (hfirst : 3 / 10 < first ∧ first < 9 / 10) (hrest : 3 / 10 < rest ∧ rest < 9 / 10)
    (delay : ℝ → ℝ) (hd : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) :
    ∀ t ∈ feedbackArrivalDates first rest delay, 1723 / 5 < t ∧ t < 4413 / 10 := by
  intro t ht
  rcases List.mem_cons.mp ht with ht | ht
  · subst t
    constructor <;> linarith [(hd (344 + first)).1,(hd (344 + first)).2,hfirst.1,hfirst.2]
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
    have hklo : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    have hkhi : (k.val : ℝ) ≤ 11 := by exact_mod_cast (show k.val ≤ 11 by omega)
    constructor <;> linarith [(hd (352 + 8 * (k.val : ℝ) + rest)).1,
      (hd (352 + 8 * (k.val : ℝ) + rest)).2,hrest.1,hrest.2]

/-- After its half-open forward gate closes, the entry router contains only
the declared return contact. -/
theorem reciprocalEntryRouter.after_forward (forward backward : ℝ → ℝ) (i : Fin 2)
    {t : ℝ} (ht : 310 ≤ t) :
    reciprocalEntryRouter forward backward i t = (feedbackContact backward).route i t := by
  classical
  have hf : (teachingContact forward).route i t = [] := by
    unfold Contact.route
    split_ifs with h
    · have hg : t < (310 : ℝ) := h.2.2
      linarith
    · rfl
  simp only [reciprocalEntryRouter,hf,List.nil_append]

theorem reciprocalEntryRouter.closed_to_b (forward backward : ℝ → ℝ) (i : Fin 2)
    {t : ℝ} (ht : 310 ≤ t) : ∀ d ∈ reciprocalEntryRouter forward backward i t, d.cell ≠ 1 := by
  intro d hd
  rw [reciprocalEntryRouter.after_forward forward backward i ht] at hd
  have hc : d.cell = (0 : Fin 2) := (feedbackContact backward).route_target hd
  rw [hc]
  decide

theorem reciprocalEntryRouter.to_a (forward backward : ℝ → ℝ) (i : Fin 2)
    {t : ℝ} (ht : 310 ≤ t) :
    (reciprocalEntryRouter forward backward i t).filter (fun d => d.cell = 0) =
      (feedbackContact backward).route i t := by
  rw [reciprocalEntryRouter.after_forward forward backward i ht]
  exact (feedbackContact backward).filter_target i t

def feedbackSendDates (first rest : ℝ) : List ℝ :=
  (344 + first) :: List.ofFn (fun k : Fin 12 => 352 + 8 * (k.val : ℝ) + rest)

theorem feedbackArrivalDates.map_send (first rest : ℝ) (delay : ℝ → ℝ) :
    feedbackArrivalDates first rest delay = (feedbackSendDates first rest).map (fun t => t + delay t) := by
  simp only [feedbackArrivalDates,feedbackSendDates,List.map_cons,List.map_ofFn,Function.comp_def]

theorem feedbackSendDates.bounds {first rest : ℝ}
    (hfirst : 3 / 10 < first ∧ first < 9 / 10) (hrest : 3 / 10 < rest ∧ rest < 9 / 10) :
    ∀ t ∈ feedbackSendDates first rest, 3443 / 10 < t ∧ t < 4409 / 10 := by
  intro t ht
  rcases List.mem_cons.mp ht with ht | ht
  · subst t
    constructor <;> linarith [hfirst.1,hfirst.2]
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
    have hklo : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    have hkhi : (k.val : ℝ) ≤ 11 := by exact_mod_cast (show k.val ≤ 11 by omega)
    constructor <;> linarith [hrest.1,hrest.2]

/-- Exact return-wire arrivals are extracted from the sender's actual output
list, keeping its first residual latency and every independent wire delay. -/
theorem Execution.feedback_contact_deliveries {θ route s u} (e : @Execution 2 θ route s u)
    (first rest : ℝ) (hfirst : 3 / 10 < first ∧ first < 9 / 10)
    (hrest : 3 / 10 < rest ∧ rest < 9 / 10) (hle : first ≤ rest)
    (houtputs : e.emissionTimes 1 = feedbackSendDates first rest)
    (delay : ℝ → ℝ) (hd : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hu : u.time = 4599 / 10) (hf : PendingFuture u)
    (hempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = 0) = (feedbackContact delay).route event.1 event.2) :
    e.cellDeliveries 0 = (feedbackArrivalDates first rest delay).map (fun t => ⟨0,2,t⟩) := by
  have hselected : (e.emissionTimes 1).filter (fun t => (320 : ℝ) ≤ t ∧ t < 470) = feedbackSendDates first rest := by
    rw [houtputs]
    apply List.filter_eq_self.mpr
    intro t ht
    have hb := feedbackSendDates.bounds hfirst hrest t ht
    exact decide_eq_true ⟨by linarith [hb.1],by linarith [hb.2]⟩
  have hfuture : ∀ d ∈ s.pending, d.cell = (feedbackContact delay).target → u.time < d.due := by
    intro d hd hc
    change d.cell = (0 : Fin 2) at hc
    have hm : d ∈ s.pending.filter (fun d => d.cell = 0) := by
      simpa only [List.mem_filter,decide_eq_true_eq] using And.intro hd hc
    rw [hempty] at hm
    contradiction
  have hdue : ∀ t ∈ e.emissionTimes 1, (320 : ℝ) ≤ t → t < 470 →
      ((feedbackContact delay).token t).due < u.time := by
    intro t ht _ _
    rw [houtputs] at ht
    have hb := (feedbackSendDates.bounds hfirst hrest t ht).2
    change t + delay t < u.time
    rw [hu]
    linarith [(hd t).2]
  have horder : (((e.emissionTimes 1).filter (fun t => (320 : ℝ) ≤ t ∧ t < 470)).map
      (feedbackContact delay).token).Pairwise (fun d f => d.due ≤ f.due) := by
    rw [hselected]
    apply List.pairwise_map.mpr
    have hs := feedbackArrivalDates.spaced hle delay hd
    rw [feedbackArrivalDates.map_send] at hs
    have hm := List.pairwise_map.mp hs
    exact hm.imp (fun {t v} h => by change t + delay t ≤ v + delay v; linarith)
  have h := e.contact_deliveries (feedbackContact delay) hf hfuture hwire hdue horder
  change e.cellDeliveries 0 = ((e.emissionTimes 1).filter (fun t => (320 : ℝ) ≤ t ∧ t < 470)).map
    (feedbackContact delay).token at h
  rw [hselected] at h
  simpa only [feedbackArrivalDates,feedbackSendDates,Contact.token,feedbackContact,List.map_cons,
    List.map_ofFn,Function.comp_def] using h

end KernelR.Hybrid
