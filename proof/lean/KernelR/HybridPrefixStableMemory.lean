import KernelR.HybridFlowCuts
import KernelR.HybridInvariants

/-! A real prefix of a memory-preserving execution preserves the same own
memory. Both inequalities come from the prefix and its retained continuation. -/
namespace KernelR.Hybrid

theorem Execution.IsPrefix.gain_eq_of_final {n θ ε route s u v}
    {e : @Execution n θ route s u} {cut : Execution θ route s v}
    (hcut : e.IsPrefix cut) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (he : u.x i (.z p) = s.x i (.z p)) : v.x i (.z p) = s.x i (.z p) := by
  obtain ⟨remaining⟩ := hcut.continuation
  exact le_antisymm ((remaining.tail.gain_nondecreasing hb i p).trans_eq he)
    (cut.gain_nondecreasing hb i p)

theorem Execution.IsPrefix.recovery_eq_of_final {n θ ε route s u v}
    {e : @Execution n θ route s u} {cut : Execution θ route s v}
    (hcut : e.IsPrefix cut) (hb : PhysicalBox θ ε) (i : Fin n)
    (he : u.x i .b = s.x i .b) : v.x i .b = s.x i .b := by
  obtain ⟨remaining⟩ := hcut.continuation
  exact le_antisymm ((remaining.tail.recovery_nondecreasing hb i).trans_eq he)
    (cut.recovery_nondecreasing hb i)

end KernelR.Hybrid
