import KernelR.HybridFiniteChainRelayPreparation
import KernelR.HybridFiniteChainLeafPreparation
import KernelR.HybridIndependentFiniteFamily
import KernelR.HybridLocalFutureFrame

/-! Common-birth preparation of a finite independent family. Each relay is
trained at its own port two, and the last cell at its own nominal fast port
one. The leaf's future port-zero program is carried along the entire global
physical execution, starting at the common birth, rather than inserted at the
preparation endpoint. -/
namespace KernelR.Hybrid
attribute [local instance] Classical.propDecidable

def finiteChainPreparationPort (n : ℕ) (i : Fin (n+1)) : Port := if i=Fin.last n then 1 else 2

noncomputable def finiteChainPreparationDose (n : ℕ) (i : Fin (n+1)) : ℝ := if i=Fin.last n then 3/5 else 9/5

def finiteChainPreparationCount (n : ℕ) (i : Fin (n+1)) : ℕ := if i=Fin.last n then 14 else 12

structure FiniteChainPreparationCell (parameter : Parameters) (born : Snapshot 1)
    (port : Port) (dose : ℝ) (count : ℕ) where
  run : FiniteCausalCell parameter born (1599/10)
  prepared : PreparedSection run.final 0
  gain_target : run.final.x 0 (.z port)=born.x 0 (.z port)+dose
  gain_other : ∀ q, q≠port → run.final.x 0 (.z q)=born.x 0 (.z q)
  recovery : run.final.x 0 .b=born.x 0 .b+1/10
  emission_count : (run.execution.emissionTimes 0).length=count
  deliveries : run.execution.deliveries=sourceTrain 0 port 0 8 16
  physical : PhysicalInvariant (fun _ : Fin 1 => parameter) run.final
  raw_valid : RawValid run.final

noncomputable def familyPreparationBornSource {n : ℕ}
    (bornCells : Fin (n+1) → Snapshot 1) (K : ℕ) : Snapshot (n+1) :=
  appendPending (independentFamilySource bornCells) (sourceTrain (Fin.last n) 0 160 4 K)

private theorem family_source_main {n : ℕ} (sources : Fin (n+1) → Snapshot 1) (i : Fin (n+1)) :
    (independentFamilySource sources).main i=(sources i).main 0 := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih (fun i => sources i.succ) i

private theorem family_source_aux {n : ℕ} (sources : Fin (n+1) → Snapshot 1) (i : Fin (n+1)) (q : Port) :
    (independentFamilySource sources).aux i q=(sources i).aux 0 q := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih (fun i => sources i.succ) i

private theorem family_source_raw {n : ℕ} (sources : Fin (n+1) → Snapshot 1) (i : Fin (n+1)) (q : Port) :
    (independentFamilySource sources).raw i q=(sources i).raw 0 q := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih (fun i => sources i.succ) i

structure FiniteChainFamilyPreparation {n : ℕ} (θ : Fin (n+1) → Parameters)
    (bornCells : Fin (n+1) → Snapshot 1) (K : ℕ) where
  initial_birth : ∀ i, BirthState (bornCells i)
  locals : (i : Fin (n+1)) → FiniteChainPreparationCell (θ i) (bornCells i)
    (finiteChainPreparationPort n i) (finiteChainPreparationDose n i) (finiteChainPreparationCount n i)
  family : IndependentFiniteFamily θ bornCells (1599/10) (fun i => (locals i).run)
  source_birth : BirthState (familyPreparationBornSource bornCells K)
  final : Snapshot (n+1)
  final_state : final=appendPending family.final (sourceTrain (Fin.last n) 0 160 4 K)
  execution : Execution θ (fun _ _ => []) (familyPreparationBornSource bornCells K) final
  ledger : execution.ledger=family.execution.ledger
  deliveries : execution.deliveries=family.execution.deliveries
  date : final.time=1599/10
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q=1/10
  raw_none : ∀ i q, final.raw i q=none
  pending : final.pending=sourceTrain (Fin.last n) 0 160 4 K
  gain_target : ∀ i, final.x i (.z (finiteChainPreparationPort n i))=
    (bornCells i).x 0 (.z (finiteChainPreparationPort n i))+finiteChainPreparationDose n i
  gain_other : ∀ i q, q≠finiteChainPreparationPort n i → final.x i (.z q)=(bornCells i).x 0 (.z q)
  recovery : ∀ i, final.x i .b=(bornCells i).x 0 .b+1/10
  emission_times : ∀ i, execution.emissionTimes i=(locals i).run.execution.emissionTimes 0
  emission_count_per_cell : ∀ i, (execution.emissionTimes i).length=finiteChainPreparationCount n i
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (1599/10)

/-- All cells are independently born at zero. The only finite teaching input
premises are their sixteen real direct sources; the leaf's later K sources
are present from time zero in the resulting physical global source queue. -/
theorem finite_chain_family_preparation_exists {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε)
    (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16) :
    Nonempty (FiniteChainFamilyPreparation θ bornCells K) := by
  have hlocal : ∀ i : Fin (n+1), Nonempty (FiniteChainPreparationCell (θ i) (bornCells i)
      (finiteChainPreparationPort n i) (finiteChainPreparationDose n i) (finiteChainPreparationCount n i)) := by
    intro i
    have hbox : PhysicalBox (fun _ : Fin 1 => θ i) ε := ⟨hb.1,fun _ q => hb.2 i q⟩
    by_cases hi : i=Fin.last n
    · have hq : (bornCells i).pending=sourceTrain 0 1 0 8 16++[] := by
        simpa only [finiteChainPreparationPort,hi,ite_true,List.append_nil] using hqueue i
      obtain ⟨leaf⟩ := finite_chain_leaf_preparation_exists (hborn i) hbox (ha i) [] hq
        (by intro d hd; contradiction)
      refine ⟨{
        run:={
          final:=leaf.final
          execution:=leaf.execution
          complete:=leaf.complete
          ready:=leaf.prepared.ready_coordinates
          charge:=leaf.charge
          raw_none:=leaf.raw_none 0
          pending:=leaf.pending
        }
        prepared:=leaf.prepared,gain_target:=?_,gain_other:=?_,recovery:=leaf.recovery
        emission_count:=?_,deliveries:=?_,physical:=leaf.physical,raw_valid:=leaf.raw_valid
      }⟩
      · simpa only [finiteChainPreparationPort,finiteChainPreparationDose,hi,ite_true] using leaf.gain_target
      · simpa only [finiteChainPreparationPort,hi,ite_true] using leaf.gain_other
      · simpa only [finiteChainPreparationCount,hi,ite_true] using leaf.emission_count
      · simpa only [finiteChainPreparationPort,hi,ite_true] using leaf.deliveries
    · have hq : (bornCells i).pending=sourceTrain 0 2 0 8 16 := by
        simpa only [finiteChainPreparationPort,hi,ite_false] using hqueue i
      obtain ⟨relay⟩ := finite_chain_relay_preparation_exists (hborn i) hbox (ha i) hq
      refine ⟨{
        run:={
          final:=relay.final
          execution:=relay.execution
          complete:=relay.complete
          ready:=relay.prepared.ready_coordinates
          charge:=relay.charge
          raw_none:=relay.raw_none 0
          pending:=relay.pending
        }
        prepared:=relay.prepared,gain_target:=?_,gain_other:=?_,recovery:=relay.recovery
        emission_count:=?_,deliveries:=?_,physical:=relay.physical,raw_valid:=relay.raw_valid
      }⟩
      · simpa only [finiteChainPreparationPort,finiteChainPreparationDose,hi,ite_false] using relay.gain_target
      · simpa only [finiteChainPreparationPort,hi,ite_false] using relay.gain_other
      · simpa only [finiteChainPreparationCount,hi,ite_false] using relay.emission_count
      · simpa only [finiteChainPreparationPort,hi,ite_false] using relay.deliveries
  let locals := fun i => Classical.choice (hlocal i)
  obtain ⟨family⟩ := independent_finite_family_exists n θ bornCells 0 (1599/10) (fun i => (hborn i).1)
    (fun i => (locals i).run) (fun i => (locals i).physical) (fun i => (locals i).raw_valid)
  let future := sourceTrain (Fin.last n) 0 160 4 K
  have hfuture : ∀ d∈future, (1599/10:ℝ)<d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change (1599/10:ℝ)<160+4*(k.val:ℝ)
    nlinarith [Nat.cast_nonneg (α:=ℝ) k.val]
  obtain ⟨execution,hLedger,hDelivered⟩ := family.execution.appendFuture_emptyRoute future
    (fun d hd => by rw [family.date]; exact (hfuture d hd).le)
  let final := appendPending family.final future
  have hPrepared : ∀ i, PreparedSection final i := by
    intro i
    have h := (locals i).prepared
    refine ⟨(family.ready i).ready,(family.ready i).charge,?_,(family.ready i).auxiliary⟩
    change family.final.x i .b∈Set.Icc (17999/100000) (18001/100000)
    rw [family.final_values i]
    exact h.recovery
  have hSourceBirth : BirthState (familyPreparationBornSource bornCells K) := by
    refine ⟨independent_family_source_clock bornCells 0 (fun i => (hborn i).1),?_,?_⟩
    · intro i q
      change (independentFamilySource bornCells).raw i q=none
      rw [family_source_raw]
      exact (hborn i).2.1 0 q
    · intro i
      have h := (hborn i).2.2 0
      simp only [familyPreparationBornSource,appendPending]
      rw [family_source_main,independent_family_source_values]
      refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
      intro q
      rw [family_source_aux]
      exact h.2.2.2.2 q
  have hPending : final.pending=future := by change family.final.pending++future=future; rw [family.pending,List.nil_append]
  have hTimes (i : Fin (n+1)) : execution.emissionTimes i=(locals i).run.execution.emissionTimes 0 := by
    change ((execution.ledger.emissions.filter (fun ev => ev.1=i)).map Prod.snd)=_
    rw [hLedger]
    exact family.emission_times i
  refine ⟨{
    initial_birth:=hborn,locals:=locals,family:=family,source_birth:=hSourceBirth,final:=final,final_state:=rfl,execution:=execution
    ledger:=hLedger,deliveries:=hDelivered,date:=family.date,prepared:=hPrepared,charge:=family.charge
    raw_none:=family.raw_none,pending:=hPending,gain_target:=?_,gain_other:=?_,recovery:=?_
    emission_times:=hTimes,emission_count_per_cell:=?_,physical:=⟨family.physical.region,family.physical.gain_cap,family.physical.recovery_cap,family.physical.reserve⟩,
    raw_valid:=family.raw_valid
    complete:=⟨family.date,?_,?_⟩
  }⟩
  · intro i; change family.final.x i _=_; rw [family.final_values]; exact (locals i).gain_target
  · intro i q hq; change family.final.x i _=_; rw [family.final_values]; exact (locals i).gain_other q hq
  · intro i; change family.final.x i .b=_; rw [family.final_values]; exact (locals i).recovery
  · intro i; exact (congrArg List.length (hTimes i)).trans (locals i).emission_count
  · exact ready_no_jump final (fun i => (hPrepared i).ready) (fun i q => ((hPrepared i).auxiliary q).1)
      family.raw_none (fun i => by change family.final.x i .q<1; rw [family.charge]; norm_num)
      (fun i q => by linarith [((hPrepared i).auxiliary q).2.2])
      (fun d hd => by
        rw [hPending] at hd
        change family.final.time<d.due
        rw [family.date]
        exact hfuture d hd)
  · intro d hd; rw [hPending] at hd; exact hfuture d hd

namespace FiniteChainFamilyPreparation
variable {n θ bornCells K} (f : @FiniteChainFamilyPreparation n θ bornCells K)

noncomputable abbrev source (_f : @FiniteChainFamilyPreparation n θ bornCells K) : Snapshot (n+1) := familyPreparationBornSource bornCells K

theorem source_values (i : Fin (n+1)) : f.source.x i=(bornCells i).x 0 :=
  independent_family_source_values bornCells i

theorem source_pending : f.source.pending=(independentFamilySource bornCells).pending++sourceTrain (Fin.last n) 0 160 4 K := rfl

theorem total_emission_count : f.execution.ledger.emissions.length=12*n+14 := by
  have hlocal (i : Fin (n+1)) : (f.locals i).run.execution.ledger.emissions.length=
      finiteChainPreparationCount n i := by
    have ht : (f.locals i).run.execution.emissionTimes 0=
        (f.locals i).run.execution.ledger.emissions.map Prod.snd := by
      rw [Execution.emissionTimes,List.filter_eq_self.mpr]
      intro ev _
      simp only [decide_eq_true_eq]
      exact Subsingleton.elim _ _
    have hc := (f.locals i).emission_count
    rw [ht,List.length_map] at hc
    exact hc
  rw [f.ledger,f.family.emission_count]
  calc
    _ = ∑ i : Fin (n+1), finiteChainPreparationCount n i := Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = ∑ i : Fin (n+1), (12+(if i=Fin.last n then 2 else 0) : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i=Fin.last n <;> simp [finiteChainPreparationCount,hi]
    _ = 12*n+14 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp
      omega

theorem ready (i : Fin (n+1)) : ReadyCoordinates f.final i := (f.prepared i).ready_coordinates

end FiniteChainFamilyPreparation
end KernelR.Hybrid
