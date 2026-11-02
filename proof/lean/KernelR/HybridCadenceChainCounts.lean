import KernelR.HybridConstructedCadenceChainStage

/-! Counts of actual finite physical cadence ledgers. Reversing physical
indices identifies the leaf-to-root count formula with the proved finite
chain sum. No output count or reaching execution is assumed in these sums. -/
namespace KernelR.Hybrid

private theorem emission_list_sum_cells {n : ℕ} (events : List (Fin n × ℝ)) :
    (∑ i : Fin n, (events.filter (fun event => event.1 = i)).length) = events.length := by
  classical
  induction events with
  | nil => simp
  | cons event events ih =>
    have hStep (i : Fin n) : ((event :: events).filter (fun ev => ev.1 = i)).length =
        (if event.1 = i then 1 else 0) + (events.filter (fun ev => ev.1 = i)).length := by
      by_cases h : event.1 = i <;> simp [h,Nat.add_comm]
    have hSingle : (∑ i : Fin n, if event.1 = i then (1 : ℕ) else 0) = 1 := by simp
    calc
      _ = ∑ i : Fin n, ((if event.1 = i then 1 else 0) +
          (events.filter (fun ev => ev.1 = i)).length) := Finset.sum_congr rfl (fun i _ => hStep i)
      _ = (∑ i : Fin n, if event.1 = i then 1 else 0) +
          ∑ i : Fin n, (events.filter (fun ev => ev.1 = i)).length := Finset.sum_add_distrib
      _ = 1 + events.length := by rw [hSingle,ih]
      _ = (event :: events).length := by simp [Nat.add_comm]

/-- Each actual emission has exactly one finite cell label. -/
theorem Execution.emission_count_eq_sum_cells {n θ route s u} (e : @Execution n θ route s u) :
    e.ledger.emissions.length = ∑ i : Fin n, (e.emissionTimes i).length := by
  symm
  simpa only [Execution.emissionTimes,List.length_map] using emission_list_sum_cells e.ledger.emissions

namespace ConstructedCadenceChainStage
variable {d : FiniteCausalChainData} {K : ℕ} {T : ℝ} {depth m L : ℕ} {J : ℝ}
  (c : ConstructedCadenceChainStage d K T depth m L J)
include c

/-- Physical root-first indices are reversed before applying the finite
chain arithmetic theorem. Every summand is a real cell's emitted stream. -/
theorem actual_emission_sum (hK : 4 * (depth + 1) + 12 ≤ K) :
    (∑ i : Fin (depth + 1), (c.stage.execution.emissionTimes i).length) =
      (depth + 1) * (K - (depth + 1) - 4) := by
  let f : Fin (depth + 1) → ℕ := fun i => K - 5 - 2 * i.val
  calc
    _ = ∑ i : Fin (depth + 1), f (Fin.revPerm i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [c.counts i]
      dsimp only [f]
      have hrev : (Fin.revPerm i).val = depth - i.val := by
        simp only [Fin.revPerm_apply,Fin.val_rev]
        omega
      rw [hrev]
    _ = ∑ i : Fin (depth + 1), f i := Equiv.sum_comp Fin.revPerm f
    _ = (Finset.range (depth + 1)).sum (fun j => K - 5 - 2 * j) :=
      Fin.sum_univ_eq_sum_range (fun j => K - 5 - 2 * j) (depth + 1)
    _ = (Finset.range (depth + 1)).sum
        (fun j => KernelR.Chain.prefixLength j + KernelR.Chain.tailLength K j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (KernelR.Chain.node_outputs hK (Finset.mem_range.mp hj)).symm
    _ = _ := KernelR.Chain.total_emissions_sum hK

theorem actual_emission_count (hK : 4 * (depth + 1) + 12 ≤ K) :
    c.stage.execution.ledger.emissions.length = (depth + 1) * (K - (depth + 1) - 4) :=
  c.stage.execution.emission_count_eq_sum_cells.trans (c.actual_emission_sum hK)

theorem root_emission_count_nodes : (c.stage.execution.emissionTimes 0).length =
    K - 2 * (depth + 1) - 3 := by
  rw [c.root_emission_count]
  omega

theorem canonical_tail_length (hK : 4 * (depth + 1) + 12 ≤ K)
    (hm : m = KernelR.Chain.prefixLength depth) : L = KernelR.Chain.tailLength K depth := by
  have h := c.packet_count
  dsimp only [KernelR.Chain.prefixLength] at hm
  dsimp only [KernelR.Chain.tailLength]
  omega

theorem canonical_tail_min (hK : 4 * (depth + 1) + 12 ≤ K)
    (hm : m = KernelR.Chain.prefixLength depth) : 8 ≤ L := by
  rw [c.canonical_tail_length hK hm]
  exact KernelR.Chain.tail_budget (by omega : 0 < depth + 1) hK (by omega : depth < depth + 1)

/-- Combine this actual cadence ledger with an actual preparatory execution
whose count has already been proved. The exact ledger concatenation retains
all earlier preparation FIREs rather than hiding them in a reset state. -/
theorem birth_emission_count {θP routeP sP uP θG routeG sG uG}
    (preparation : @Execution (depth + 1) θP routeP sP uP)
    (whole : @Execution (depth + 1) θG routeG sG uG)
    (hPreparation : preparation.ledger.emissions.length = 12 * depth + 14)
    (hLedger : whole.ledger = preparation.ledger.add c.stage.execution.ledger)
    (hK : 4 * (depth + 1) + 12 ≤ K) :
    whole.ledger.emissions.length = (depth + 1) * (K - (depth + 1) + 8) + 2 := by
  rw [hLedger]
  change (preparation.ledger.emissions ++ c.stage.execution.ledger.emissions).length = _
  rw [List.length_append,hPreparation,c.actual_emission_count hK]
  have hSub : K - (depth + 1) + 8 = (K - (depth + 1) - 4) + 12 := by omega
  rw [hSub]
  ring

end ConstructedCadenceChainStage
end KernelR.Hybrid
