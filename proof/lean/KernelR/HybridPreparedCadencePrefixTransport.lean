import KernelR.HybridFiniteChainPreparedData
import KernelR.HybridCadenceStageTransport

/-! Changing an unused future wire leaves the existing physical stage's
parameters, initial source and whole prefix router exactly unchanged. -/
namespace KernelR.Hybrid
namespace FiniteChainFamilyPreparation
variable {n : ℕ} {θ : Fin (n+1)→Parameters} {bornCells : Fin (n+1)→Snapshot 1} {K : ℕ}
  (f : FiniteChainFamilyPreparation θ bornCells K)
  {delay delay' : ℕ→ℝ→ℝ} {T : ℝ}
  {hd : ∀ j, j<n → ∀ t, 0<delay j t}
  {hd' : ∀ j, j<n → ∀ t, 0<delay' j t}

theorem cadence_parameters_delay_eq (j : ℕ) :
    (f.cadenceData delay T hd).parameters j=(f.cadenceData delay' T hd').parameters j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change prependParameters _ ((f.cadenceData delay T hd).parameters j)=
      prependParameters _ ((f.cadenceData delay' T hd').parameters j)
    rw [ih]
    rfl

theorem cadence_source_delay_eq (j : ℕ) :
    (f.cadenceData delay T hd).source j=(f.cadenceData delay' T hd').source j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change ((f.cadenceData delay T hd).source j).prependQueued _
        (((f.cadenceData delay T hd).source j).pending.map Delivery.succ)=
      ((f.cadenceData delay' T hd').source j).prependQueued _
        (((f.cadenceData delay' T hd').source j).pending.map Delivery.succ)
    rw [ih]
    rfl

theorem cadence_route_prefix_eq (j : ℕ) (hj : j≤n)
    (heq : ∀ k, k<j → delay k=delay' k) :
    (f.cadenceData delay T hd).route j=(f.cadenceData delay' T hd').route j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change prependRouted ((f.cadenceData delay T hd).route j) ((f.cadenceData delay T hd).contacts j)=
      prependRouted ((f.cadenceData delay' T hd').route j) ((f.cadenceData delay' T hd').contacts j)
    rw [ih (by omega) (fun k hk => heq k (by omega))]
    have hc : (f.cadenceData delay T hd).contacts j=
        finiteCadenceHeadContact (0 : Fin (j+1)) 2 160 (T+1) (delay j) :=
      FiniteChainPreparedData.contacts (s:=f.final) (θ:=θ) (T:=T) (hd:=hd) j (by omega)
    have hc' : (f.cadenceData delay' T hd').contacts j=
        finiteCadenceHeadContact (0 : Fin (j+1)) 2 160 (T+1) (delay' j) :=
      FiniteChainPreparedData.contacts (s:=f.final) (θ:=θ) (T:=T) (hd:=hd') j (by omega)
    rw [hc,hc',heq j (by omega)]

end FiniteChainFamilyPreparation
end KernelR.Hybrid
