import KernelR.HybridIndependentHeadProduct
import KernelR.HybridFiniteCausalChain

/-! Independent finite preparation from actual one-cell paths. Every cell has
its own source coordinates, parameters, external input queue and genuine FIRE
ledger. The construction combines all external sources; it assumes no neutral
path, global reaching execution, or copied birth state. -/
namespace KernelR.Hybrid

/-- Recursive ordered queue union: the head's actual sources, then all tail
sources, with their exact receiving-cell indices transported. -/
noncomputable def independentFamilySource : {n : ℕ} →
    (Fin (n+1) → Snapshot 1) → Snapshot (n+1)
  | 0,sources => sources 0
  | n+1,sources =>
    let tail := independentFamilySource (fun i : Fin (n+1) => sources i.succ)
    tail.prependQueued (sources 0) (independentHeadQueue tail (sources 0))

theorem independent_family_source_clock {n : ℕ} (sources : Fin (n+1) → Snapshot 1)
    (S : ℝ) (hclock : ∀ i, (sources i).time=S) :
    (independentFamilySource sources).time=S := by
  induction n with
  | zero => exact hclock 0
  | succ n ih => exact ih (fun i => sources i.succ) (fun i => hclock i.succ)

theorem independent_family_source_values {n : ℕ} (sources : Fin (n+1) → Snapshot 1)
    (i : Fin (n+1)) : (independentFamilySource sources).x i=(sources i).x 0 := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih (fun i => sources i.succ) i

theorem independent_family_source_queue_succ {n : ℕ} (sources : Fin (n+1+1) → Snapshot 1) :
    (independentFamilySource sources).pending=
      (sources 0).pending.map (Delivery.head (n:=n+1)) ++
      (independentFamilySource (fun i : Fin (n+1) => sources i.succ)).pending.map Delivery.succ := rfl

theorem independent_family_source_queue_length {n : ℕ} (sources : Fin (n+1) → Snapshot 1) :
    (independentFamilySource sources).pending.length=∑ i, (sources i).pending.length := by
  induction n with
  | zero =>
    change (sources 0).pending.length=∑ i : Fin 1, (sources i).pending.length
    simp only [Fin.sum_univ_one]
  | succ n ih =>
    change ((sources 0).pending.map (Delivery.head (n:=n+1)) ++
      (independentFamilySource (fun i : Fin (n+1) => sources i.succ)).pending.map Delivery.succ).length=_
    rw [List.length_append,List.length_map,List.length_map,ih]
    conv_rhs => rw [Fin.sum_univ_succ]

/-- A real global family, with every cell's exact physical endpoint and
ordered FIRE stream tied to its given local preparation. -/
structure IndependentFiniteFamily {n : ℕ} (θ : Fin (n+1) → Parameters)
    (sources : Fin (n+1) → Snapshot 1) (T : ℝ)
    (runs : (i : Fin (n+1)) → FiniteCausalCell (θ i) (sources i) T) where
  final : Snapshot (n+1)
  execution : Execution θ (fun _ _ => []) (independentFamilySource sources) final
  complete : CompleteThrough execution T
  pending : final.pending=[]
  ready : ∀ i, ReadyCoordinates final i
  charge : ∀ i, final.x i .q=1/10
  raw_none : ∀ i q, final.raw i q=none
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  final_values : ∀ i, final.x i=(runs i).final.x 0
  final_main : ∀ i, final.main i=(runs i).final.main 0
  final_aux : ∀ i q, final.aux i q=(runs i).final.aux 0 q
  final_raw : ∀ i q, final.raw i q=(runs i).final.raw 0 q
  emission_times : ∀ i, execution.emissionTimes i=(runs i).execution.emissionTimes 0
  emission_count : execution.ledger.emissions.length=∑ i, (runs i).execution.ledger.emissions.length
  delivery_count : execution.deliveries.length=∑ i, (runs i).execution.deliveries.length

private noncomputable def independent_family_cast_parameters {n θ θ' route s u}
    (e : @Execution n θ route s u) (hp : θ=θ') : Execution θ' route s u := hp ▸ e

private theorem independent_family_parameters_ledger {n θ θ' route s u}
    (e : @Execution n θ route s u) (hp : θ=θ') :
    (independent_family_cast_parameters e hp).ledger=e.ledger := by cases hp; rfl

private theorem independent_family_parameters_deliveries {n θ θ' route s u}
    (e : @Execution n θ route s u) (hp : θ=θ') :
    (independent_family_cast_parameters e hp).deliveries=e.deliveries := by cases hp; rfl

private theorem independent_family_parameters_times {n θ θ' route s u}
    (e : @Execution n θ route s u) (hp : θ=θ') (i : Fin n) :
    (independent_family_cast_parameters e hp).emissionTimes i=e.emissionTimes i := by cases hp; rfl

private noncomputable def independent_family_cast_router {n θ route route' s u}
    (e : @Execution n θ route s u) (hr : route=route') : Execution θ route' s u := hr ▸ e

private theorem independent_family_router_ledger {n θ route route' s u}
    (e : @Execution n θ route s u) (hr : route=route') :
    (independent_family_cast_router e hr).ledger=e.ledger := by cases hr; rfl

private theorem independent_family_router_deliveries {n θ route route' s u}
    (e : @Execution n θ route s u) (hr : route=route') :
    (independent_family_cast_router e hr).deliveries=e.deliveries := by cases hr; rfl

private theorem independent_family_router_complete {n θ route route' s u T}
    (e : @Execution n θ route s u) (hr : route=route') (hc : CompleteThrough e T) :
    CompleteThrough (independent_family_cast_router e hr) T := by cases hr; exact hc

/-- Combine independently constructed physical preparations at a common clock
and horizon. This induction permits actual input arrivals and FIREs in every
cell. Physical premises concern only the already-constructed local endpoints. -/
theorem independent_finite_family_exists (n : ℕ)
    (θ : Fin (n+1) → Parameters) (sources : Fin (n+1) → Snapshot 1) (S T : ℝ)
    (hclock : ∀ i, (sources i).time=S)
    (runs : (i : Fin (n+1)) → FiniteCausalCell (θ i) (sources i) T)
    (hf : ∀ i, PhysicalInvariant (fun _ : Fin 1 => θ i) (runs i).final)
    (hv : ∀ i, RawValid (runs i).final) :
    Nonempty (IndependentFiniteFamily θ sources T runs) := by
  induction n with
  | zero =>
    have hp : (fun _ : Fin 1 => θ 0)=θ := by funext i; fin_cases i; rfl
    let execution := independent_family_cast_parameters (runs 0).execution hp
    have hledger : execution.ledger=(runs 0).execution.ledger := independent_family_parameters_ledger (runs 0).execution hp
    have hdel : execution.deliveries=(runs 0).execution.deliveries := independent_family_parameters_deliveries (runs 0).execution hp
    refine ⟨{
      final:=(runs 0).final,execution:=execution,complete:=?_,pending:=(runs 0).pending
      ready:=?_,charge:=?_,raw_none:=?_,physical:=?_,raw_valid:=hv 0
      final_values:=?_,final_main:=?_,final_aux:=?_,final_raw:=?_,emission_times:=?_
      emission_count:=?_,delivery_count:=?_
    }⟩
    · simpa only [CompleteThrough] using (runs 0).complete
    · intro i; fin_cases i; exact (runs 0).ready
    · intro i; fin_cases i; exact (runs 0).charge
    · intro i q; fin_cases i; exact (runs 0).raw_none q
    · simpa only [hp] using hf 0
    · intro i; fin_cases i; rfl
    · intro i; fin_cases i; rfl
    · intro i q; fin_cases i; rfl
    · intro i q; fin_cases i; rfl
    · intro i; fin_cases i; exact independent_family_parameters_times (runs 0).execution hp 0
    · change execution.ledger.emissions.length=∑ i : Fin 1, (runs i).execution.ledger.emissions.length
      rw [hledger,Fin.sum_univ_one]
    · change execution.deliveries.length=∑ i : Fin 1, (runs i).execution.deliveries.length
      rw [hdel,Fin.sum_univ_one]
  | succ n ih =>
    obtain ⟨tail⟩ := ih (fun i => θ i.succ) (fun i => sources i.succ)
      (fun i => hclock i.succ) (fun i => runs i.succ) (fun i => hf i.succ) (fun i => hv i.succ)
    have hstart : (independentFamilySource (fun i : Fin (n+1) => sources i.succ)).time=(sources 0).time :=
      (independent_family_source_clock _ S (fun i => hclock i.succ)).trans (hclock 0).symm
    obtain ⟨product⟩ := tail.execution.prepend_independent_exists (runs 0).execution hstart
      (tail.complete.1.trans (runs 0).complete.1.symm)
    have hp : prependParameters (fun _ : Fin 1 => θ 0) (fun i : Fin (n+1) => θ i.succ)=θ := by
      funext i
      cases i using Fin.cases <;> rfl
    have hr : prependRouted (fun (_ : Fin (n+1)) (_ : ℝ) => []) (fun _ _ => [])=
        (fun (_ : Fin (n+1+1)) (_ : ℝ) => []) := by
      funext i time
      cases i using Fin.cases <;> rfl
    let e0 := independent_family_cast_parameters product.execution hp
    let execution := independent_family_cast_router e0 hr
    have hledger : execution.ledger=product.execution.ledger :=
      (independent_family_router_ledger e0 hr).trans (independent_family_parameters_ledger product.execution hp)
    have hdel : execution.deliveries=product.execution.deliveries :=
      (independent_family_router_deliveries e0 hr).trans (independent_family_parameters_deliveries product.execution hp)
    have htimes (i : Fin (n+1+1)) : execution.emissionTimes i=product.execution.emissionTimes i := by
      simp only [Execution.emissionTimes,hledger]
    have hcomplete : CompleteThrough e0 T := by
      simpa only [CompleteThrough] using product.complete tail.complete (runs 0).complete
    refine ⟨{
      final:=tail.final.prependQueued (runs 0).final product.pending,execution:=execution
      complete:=independent_family_router_complete e0 hr hcomplete
      pending:=product.pending_empty tail.pending (runs 0).pending
      ready:=product.ready tail.ready (runs 0).ready,charge:=?_,raw_none:=?_
      physical:=?_,raw_valid:=product.raw_valid (tail.complete.1.trans (runs 0).complete.1.symm) tail.raw_valid (hv 0)
      final_values:=?_,final_main:=?_,final_aux:=?_,final_raw:=?_,emission_times:=?_
      emission_count:=?_,delivery_count:=?_
    }⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact (runs 0).charge
      | succ i => exact tail.charge i
    · intro i q
      cases i using Fin.cases with
      | zero => exact (runs 0).raw_none q
      | succ i => exact tail.raw_none i q
    · simpa only [hp] using product.physical tail.physical (hf 0)
    · intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact tail.final_values i
    · intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact tail.final_main i
    · intro i q
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact tail.final_aux i q
    · intro i q
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact tail.final_raw i q
    · intro i
      cases i using Fin.cases with
      | zero => exact (htimes 0).trans product.head_emission_times
      | succ i => exact (htimes i.succ).trans ((product.tail_emission_times i).trans (tail.emission_times i))
    · apply Eq.trans (congrArg (fun l : Ledger (n+1+1) => l.emissions.length) hledger)
      apply Eq.trans product.emission_count
      rw [tail.emission_count]
      conv_rhs => rw [Fin.sum_univ_succ]
      omega
    · apply Eq.trans (congrArg List.length hdel)
      apply Eq.trans product.delivery_count
      rw [tail.delivery_count]
      conv_rhs => rw [Fin.sum_univ_succ]
      omega

namespace IndependentFiniteFamily
variable {n θ sources T runs} (family : @IndependentFiniteFamily n θ sources T runs)

theorem date : family.final.time=T := family.complete.1

theorem energy_actual (i : Fin (n+1)) : family.final.x i .energy=(runs i).final.x 0 .energy :=
  congrFun (family.final_values i) .energy

end IndependentFiniteFamily
end KernelR.Hybrid
