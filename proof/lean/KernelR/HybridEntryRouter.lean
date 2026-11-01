import KernelR.HybridPreparedContact
/-! The declared two-cell contact windows, with independent per-emission delays. -/
namespace KernelR.Hybrid

/-- The return contact is closed throughout the A-to-B teaching epoch. -/
def feedbackContact (delay : ℝ → ℝ) : Contact 2 := ⟨1,0,2,320,470,delay⟩

noncomputable def reciprocalEntryRouter (forward backward : ℝ → ℝ) : Router 2 := fun i t =>
  (teachingContact forward).route i t ++ (feedbackContact backward).route i t

theorem Contact.route_target {n} (c : Contact n) {i t d} (hd : d ∈ c.route i t) : d.cell = c.target := by
  classical
  unfold Contact.route at hd
  split_ifs at hd
  · simp only [List.mem_singleton] at hd
    subst d
    rfl
  · contradiction

theorem Contact.filter_target {n} (c : Contact n) (i : Fin n) (t : ℝ) :
    (c.route i t).filter (fun d => d.cell = c.target) = c.route i t := by
  classical
  apply List.filter_eq_self.mpr
  intro d hd
  exact decide_eq_true (c.route_target hd)

theorem reciprocalEntryRouter.causal (forward backward : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ forward t) (hb : ∀ t, 0 ≤ backward t) :
    CausalRouter (reciprocalEntryRouter forward backward) := by
  intro i t d hd
  rcases List.mem_append.mp hd with h | h
  · exact (teachingContact forward).causal hf i t d h
  · exact (feedbackContact backward).causal hb i t d h

theorem reciprocalEntryRouter.before_reverse (forward backward : ℝ → ℝ) (i : Fin 2)
    {t : ℝ} (ht : t < 320) :
    reciprocalEntryRouter forward backward i t = (teachingContact forward).route i t := by
  classical
  have hr : (feedbackContact backward).route i t = [] := by
    unfold Contact.route
    split_ifs with h
    · have hg : (320 : ℝ) ≤ t := h.2.1
      linarith
    · rfl
  simp only [reciprocalEntryRouter,hr,List.append_nil]

theorem reciprocalEntryRouter.closed_to_a (forward backward : ℝ → ℝ) (i : Fin 2)
    {t : ℝ} (ht : t < 320) : ∀ d ∈ reciprocalEntryRouter forward backward i t, d.cell ≠ 0 := by
  intro d hd
  rw [reciprocalEntryRouter.before_reverse forward backward i ht] at hd
  have hc : d.cell = (1 : Fin 2) := (teachingContact forward).route_target hd
  rw [hc]
  decide

theorem reciprocalEntryRouter.to_b (forward backward : ℝ → ℝ) (i : Fin 2)
    {t : ℝ} (ht : t < 320) :
    (reciprocalEntryRouter forward backward i t).filter (fun d => d.cell = 1) =
      (teachingContact forward).route i t := by
  rw [reciprocalEntryRouter.before_reverse forward backward i ht]
  exact (teachingContact forward).filter_target i t

end KernelR.Hybrid
