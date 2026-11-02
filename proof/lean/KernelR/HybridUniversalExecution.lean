import KernelR.HybridExecutionUniqueness
import KernelR.HybridJumpStripping
import KernelR.HybridJumpLocalDiamond

/-! Every complete finite operational execution has the same physical endpoint
and ordered per-cell FIRE lists. The result is derived from physical integral
uniqueness and legal jump confluence, with no event-priority or trace premise. -/
namespace KernelR.Hybrid

/-- Any enabled jump can be cancelled from any complete finite execution. -/
theorem Execution.strip_initial_jump {n θ route s u a T}
    (e : @Execution n θ route s u) (hc : CompleteThrough e T)
    (j : Jump route s a) :
    ∃ b, ∃ tail : Execution θ route a b,
      u.ObservationalEq b ∧ CompleteThrough tail T ∧
      (j.ledger.emissions++tail.ledger.emissions).Perm e.ledger.emissions ∧
      tail.moveCount+1=e.moveCount :=
  e.strip_initial_jump_of_diamond
    (fun j k => labelled_diamond_of_diamond θ j k (j.local_diamond k)) hc j

/-- Arbitrary finite complete traces agree observationally. The global FIRE
list is compared up to simultaneous interleaving; each cell's list is exact. -/
theorem Execution.observational_unique {n θ ε route s u v T}
    (e : @Execution n θ route s u) (f : Execution θ route s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (he : CompleteThrough e T) (hf : CompleteThrough f T) :
    u.ObservationalEq v ∧ e.ledger.emissions.Perm f.ledger.emissions :=
  Execution.observational_unique_of_strip hb
    (fun e hc j => e.strip_initial_jump hc j) e f hs he hf

/-- Each physical cell's ordered actual FIRE dates are independent of legal
flow subdivision, zero-time event order and pending-list presentation. -/
theorem Execution.emissionTimes_unique {n θ ε route s u v T}
    (e : @Execution n θ route s u) (f : Execution θ route s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (he : CompleteThrough e T) (hf : CompleteThrough f T) (i : Fin n) :
    e.emissionTimes i=f.emissionTimes i := by
  have hp := (e.observational_unique f hb hs he hf).2
  exact List.Perm.eq_of_pairwise (le:=fun a b : ℝ => a≤b)
    (fun _ _ _ _ h h' => le_antisymm h h')
    (e.emissionTimes_chronological i) (f.emissionTimes_chronological i)
    ((hp.filter _).map _)

#print axioms Execution.observational_unique
#print axioms Execution.emissionTimes_unique

end KernelR.Hybrid
