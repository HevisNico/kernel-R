import KernelR.HybridEntryRouter
/-! The B-to-C contact after the actual third-cell birth. -/
namespace KernelR.Hybrid

def cTeachingContact (delay : ℝ → ℝ) : Contact 3 := ⟨1,2,1,480,630,delay⟩

noncomputable def cTeachingRouter (delay : ℝ → ℝ) : Router 3 :=
  (cTeachingContact delay).route

theorem cTeachingRouter.causal (delay : ℝ → ℝ) (hd : ∀ t, 0 ≤ delay t) :
    CausalRouter (cTeachingRouter delay) := (cTeachingContact delay).causal hd

theorem cTeachingRouter.closed_to_a (delay : ℝ → ℝ) (i : Fin 3) (t : ℝ) :
    ∀ d ∈ cTeachingRouter delay i t, d.cell ≠ 0 := by
  intro d hd
  have hc : d.cell = (2 : Fin 3) := (cTeachingContact delay).route_target hd
  rw [hc]
  decide

theorem cTeachingRouter.closed_to_b (delay : ℝ → ℝ) (i : Fin 3) (t : ℝ) :
    ∀ d ∈ cTeachingRouter delay i t, d.cell ≠ 1 := by
  intro d hd
  have hc : d.cell = (2 : Fin 3) := (cTeachingContact delay).route_target hd
  rw [hc]
  decide

theorem cTeachingRouter.to_c (delay : ℝ → ℝ) (i : Fin 3) (t : ℝ) :
    (cTeachingRouter delay i t).filter (fun d => d.cell = 2) =
      (cTeachingContact delay).route i t := (cTeachingContact delay).filter_target i t

theorem cTeachingContact.date_bounds {G : ℝ} (hG : 9 / 5 ≤ G ∧ G ≤ 12 / 5)
    (delay : ℝ → ℝ) (hd : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) (k : Fin 16) :
    4806 / 10 < ((cTeachingContact delay).token (480 + 8 * k.val + restLatency G)).due ∧
      ((cTeachingContact delay).token (480 + 8 * k.val + restLatency G)).due < 6013 / 10 := by
  have hl := restLatency_spec hG
  have hklo : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hkhi : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
  have hdelay := hd (480 + 8 * k.val + restLatency G)
  dsimp [Contact.token,cTeachingContact]
  constructor <;> linarith [hl.1,hl.2.1,hdelay.1,hdelay.2]

end KernelR.Hybrid
