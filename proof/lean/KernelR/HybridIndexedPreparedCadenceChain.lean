import KernelR.HybridPreparedCadencePrefixTransport
import KernelR.HybridStrongCadenceChainStep
import KernelR.HybridIndexedWireDelay

/-! Prescribed per-emission errors are realized by feed-forward physical
construction. Each new delay indexes the already constructed sender's FAST
ledger. Every later weave retains that exact ordered ledger. -/
namespace KernelR.Hybrid

/-- In a depth-d root-first suffix, wire k leaves cell d-k. Its parent is
cell d-k-1. In particular the newly added wire leaves cell one. -/
def indexedCadenceSender (depth wire : ℕ) (hwire : wire<depth) : Fin (depth+1) :=
  ⟨depth-wire,by omega⟩

theorem indexedCadenceSender_new (j : ℕ) :
    indexedCadenceSender (j+1) j (by omega)=(0 : Fin (j+1)).succ := by
  apply Fin.ext
  simp only [indexedCadenceSender,Fin.val_succ,Fin.val_zero]
  omega

theorem indexedCadenceSender_succ {j k : ℕ} (hk : k<j) :
    indexedCadenceSender (j+1) k (by omega)=(indexedCadenceSender j k hk).succ := by
  apply Fin.ext
  simp only [indexedCadenceSender,Fin.val_succ]
  omega

structure IndexedPreparedCadenceChainStage {n : ℕ} {θ : Fin (n+1)→Parameters}
    {bornCells : Fin (n+1)→Snapshot 1} {K : ℕ}
    (f : FiniteChainFamilyPreparation θ bornCells K)
    (sigma centre : ℕ→ℝ) (error : ℕ→ℕ→ℝ) (depth : ℕ) where
  delay : ℕ→ℝ→ℝ
  error_bounds : ∀ j, j<n → ∀ t, -sigma j≤delay j t-centre j ∧ delay j t-centre j≤sigma j
  positive : ∀ j, j<n → ∀ t, 0<delay j t
  cadence : ConstructedCadenceChainStage
    (f.cadenceData delay (cadenceChainTerminal n K) positive)
    K (cadenceChainTerminal n K) depth (KernelR.Chain.prefixLength depth)
    (KernelR.Chain.tailLength K depth) (KernelR.Chain.pathJitter sigma depth)
  realizes : ∀ (j : ℕ) (hj : j<depth) (i : ℕ)
    (hi : i<(cadence.stage.execution.emissionTimes (indexedCadenceSender depth j hj)).length),
    delay j (cadence.stage.execution.emissionTimes (indexedCadenceSender depth j hj))[i]=
      centre j+error j i

namespace FiniteChainFamilyPreparation
variable {n : ℕ} {θ : Fin (n+1)→Parameters} {bornCells : Fin (n+1)→Snapshot 1} {K : ℕ}
  (f : FiniteChainFamilyPreparation θ bornCells K)

theorem indexed_cadence_stage_exists {ε} (hb : PhysicalBox θ ε)
    (sigma centre : ℕ→ℝ) (error : ℕ→ℕ→ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ i, -sigma j≤error j i ∧ error j i≤sigma j) :
    ∀ depth, depth≤n → Nonempty (IndexedPreparedCadenceChainStage f sigma centre error depth) := by
  have positive_of_bounds (delay : ℕ→ℝ→ℝ)
      (herr : ∀ j, j<n → ∀ t, -sigma j≤delay j t-centre j ∧ delay j t-centre j≤sigma j) :
      ∀ j, j<n → ∀ t, 0<delay j t := by
    intro j hj t
    linarith [(hcentre j hj).1,(herr j hj t).1]
  intro depth
  induction depth with
  | zero =>
    intro _
    let delay : ℕ→ℝ→ℝ := fun j _ => centre j+error j 0
    have herr : ∀ j, j<n → ∀ t, -sigma j≤delay j t-centre j ∧ delay j t-centre j≤sigma j := by
      intro j hj t
      dsimp only [delay]
      constructor <;> linarith [(herror j hj 0).1,(herror j hj 0).2]
    let hd := positive_of_bounds delay herr
    have domain := f.cadence_domain (hd:=hd) hb sigma centre hK hsigma hbudget hcentre herr
    obtain ⟨base⟩ := domain.base_exists
    refine ⟨{delay:=delay,error_bounds:=herr,positive:=hd,cadence:=base,realizes:=?_}⟩
    intro j hj
    omega
  | succ depth ih =>
    intro hdepth
    obtain ⟨old⟩ := ih (by omega)
    have hj : depth<n := by omega
    have holdJ : KernelR.Chain.pathJitter sigma depth≤3/20 :=
      (KernelR.Chain.pathJitter_mono sigma hsigma (by omega : depth≤n)).trans hbudget
    have hnextJ : KernelR.Chain.pathJitter sigma depth+sigma depth≤3/20 := by
      exact (KernelR.Chain.pathJitter_mono sigma hsigma (by omega : depth+1≤n)).trans hbudget
    let chosen := old.cadence.stage.execution.indexedWireDelay 0 (centre depth) (error depth)
    let delay := Function.update old.delay depth chosen
    have hchosen (t : ℝ) : -sigma depth≤chosen t-centre depth ∧ chosen t-centre depth≤sigma depth := by
      have h : centre depth-sigma depth≤chosen t ∧ chosen t≤centre depth+sigma depth :=
        indexedWireDelay_bounds (old.cadence.stage.execution.emissionTimes 0)
          (centre depth) (sigma depth) (error depth) (herror depth hj) t
      constructor <;> linarith [h.1,h.2]
    have herr : ∀ j, j<n → ∀ t, -sigma j≤delay j t-centre j ∧ delay j t-centre j≤sigma j := by
      intro j hj' t
      by_cases heq : j=depth
      · subst j
        simpa only [delay,Function.update_self] using hchosen t
      · simpa only [delay,Function.update_of_ne heq] using old.error_bounds j hj' t
    let hd := positive_of_bounds delay herr
    let oldData := f.cadenceData old.delay (cadenceChainTerminal n K) old.positive
    let newData := f.cadenceData delay (cadenceChainTerminal n K) hd
    have hp : oldData.parameters depth=newData.parameters depth := f.cadence_parameters_delay_eq depth
    have hs : oldData.source depth=newData.source depth := f.cadence_source_delay_eq depth
    have hr : oldData.route depth=newData.route depth := by
      apply f.cadence_route_prefix_eq depth (by omega)
      intro j hlt
      simp only [delay,Function.update_of_ne (show j≠depth by omega)]
    let previous := old.cadence.transport hp hr hs
    have domain := f.cadence_domain (hd:=hd) hb sigma centre hK hsigma hbudget hcentre herr
    have hL : 5≤KernelR.Chain.tailLength K depth := by
      have h := KernelR.Chain.tail_budget (by omega : 0<n+1) hK (by omega : depth<n+1)
      omega
    obtain ⟨rawNext,htail⟩ := domain.strong_step_exists hj hL hnextJ previous
    let next := rawNext.reindex (KernelR.Chain.prefix_step depth).symm
      (KernelR.Chain.tail_step K depth).symm (show KernelR.Chain.pathJitter sigma depth+sigma depth=
        KernelR.Chain.pathJitter sigma (depth+1) from rfl)
    have htimes (i : Fin (depth+1)) : next.stage.execution.emissionTimes i.succ=
        old.cadence.stage.execution.emissionTimes i :=
      (congrArg (fun s => s.execution.emissionTimes i.succ) (rawNext.reindex_stage _ _ _)).trans
        ((htail i).trans (old.cadence.transport_times hp hr hs i))
    have hn : (old.cadence.stage.execution.emissionTimes 0).Nodup := by
      rw [old.cadence.calendar]
      exact packet_dates_nodup old.cadence.packet holdJ
    have hrealizes : ∀ (j : ℕ) (hj' : j<depth+1) (i : ℕ)
        (hi : i<(next.stage.execution.emissionTimes (indexedCadenceSender (depth+1) j hj')).length),
        delay j (next.stage.execution.emissionTimes (indexedCadenceSender (depth+1) j hj'))[i]=
          centre j+error j i := by
      intro j hj' i hi
      by_cases heq : j=depth
      · subst j
        have hlist : next.stage.execution.emissionTimes (indexedCadenceSender (depth+1) depth hj')=
            old.cadence.stage.execution.emissionTimes 0 := by
          rw [indexedCadenceSender_new,htimes 0]
        have hi' : i<(old.cadence.stage.execution.emissionTimes 0).length := by
          simpa only [hlist] using hi
        have h := old.cadence.stage.execution.indexedWireDelay_at 0 (centre depth) (error depth) hn i hi'
        simpa only [hlist,delay,Function.update_self] using h
      · have hlt : j<depth := by omega
        have hlist : next.stage.execution.emissionTimes (indexedCadenceSender (depth+1) j hj')=
            old.cadence.stage.execution.emissionTimes (indexedCadenceSender depth j hlt) := by
          rw [indexedCadenceSender_succ hlt,htimes]
        have hi' : i<(old.cadence.stage.execution.emissionTimes (indexedCadenceSender depth j hlt)).length := by
          simpa only [hlist] using hi
        simpa only [hlist,delay,Function.update_of_ne heq] using old.realizes j hlt i hi'
    exact ⟨{delay:=delay,error_bounds:=herr,positive:=hd,cadence:=next,realizes:=hrealizes}⟩

end FiniteChainFamilyPreparation
end KernelR.Hybrid
