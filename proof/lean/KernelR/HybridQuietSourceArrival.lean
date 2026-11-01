import KernelR.HybridQuietFlowExistence
import KernelR.HybridSilentReturn
import KernelR.HybridPhysicalInvariant
import KernelR.HybridGuardNoJump
/-! Construct quiet waiting and the next exact head delivery, retaining residues and queue order. -/
namespace KernelR.Hybrid
open Set

theorem relax_mem_Icc {rate target initial start t lower upper : ℝ}
    (hr : 0 ≤ rate) (ht : start ≤ t) (hi : initial ∈ Icc lower upper) (hb : target ∈ Icc lower upper) :
    relax rate target initial start t ∈ Icc lower upper := by
  have he : 0 ≤ Real.exp (-rate * (t - start)) := (Real.exp_pos _).le
  have hu : Real.exp (-rate * (t - start)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hlo := add_le_add (mul_le_mul_of_nonneg_right hi.1 he)
    (mul_le_mul_of_nonneg_right hb.1 (sub_nonneg.mpr hu))
  have hhi := add_le_add (mul_le_mul_of_nonneg_right hi.2 he)
    (mul_le_mul_of_nonneg_right hb.2 (sub_nonneg.mpr hu))
  dsimp only [relax]
  constructor <;> nlinarith

theorem quietAt_ready_coordinates {n} (s : Snapshot n) (i : Fin n) (hs : ReadyCoordinates s i)
    {T : ℝ} (ht : s.time ≤ T) : ReadyCoordinates (quietAt s T) i := by
  refine ⟨hs.ready,?_,?_⟩
  · exact relax_mem_Icc (by norm_num) ht hs.charge (by constructor <;> norm_num)
  · intro p
    refine ⟨(hs.auxiliary p).1,?_⟩
    exact relax_mem_Icc (by norm_num) ht (hs.auxiliary p).2 (by constructor <;> norm_num)

noncomputable def quietSourceAfter {n} (s : Snapshot n) (d : Delivery n) (later : List (Delivery n)) : Snapshot n :=
  { (setRaw (quietAt s d.due) d.cell d.port (some d.due)) with pending := later }

structure QuietSourceArrival {n} (θ : Fin n → Parameters) (route : Router n)
    (s : Snapshot n) (d : Delivery n) (later : List (Delivery n)) where
  final : Snapshot n
  execution : Execution θ route s final
  date : final.time = d.due
  deliveries : execution.deliveries = [d]
  pending : final.pending = later
  ready : ∀ j, ReadyCoordinates final j
  values : final.x = quietValues s d.due
  gain_preserved : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery_preserved : ∀ j, final.x j .b = s.x j .b
  raw_active : final.raw d.cell d.port = some final.time
  raw_other : ∀ j q, j ≠ d.cell ∨ q ≠ d.port → final.raw j q = none
  emissions : execution.ledger.emissions = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- The exact head token is delivered after a constructed waiting flow. Every
later token remains, even if another is due at the same clock time. -/
theorem quiet_source_arrival_exists {n θ ε route} (hb : @PhysicalBox n θ ε)
    (s : Snapshot n) (d : Delivery n) (later : List (Delivery n))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : ∀ j, ReadyCoordinates s j)
    (hr : ∀ j q, s.raw j q = none) (ht : s.time < d.due)
    (hqueue : s.pending = d :: later) (hmin : ∀ f ∈ later, d.due ≤ f.due) :
    Nonempty (QuietSourceArrival θ route s d later) := by
  have hfuture : ∀ f ∈ s.pending, d.due ≤ f.due := by
    intro f hf
    rw [hqueue] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact le_rfl
    · exact hmin f hf
  let flow := quietFlow (θ := θ) s ht (fun j => (hs j).ready) (fun j q => ((hs j).auxiliary q).1) hr
    (fun j => by linarith [(hs j).charge.2])
    (fun j q => by linarith [((hs j).auxiliary q).2.2]) hfuture
  let v := quietAt s d.due
  let u := quietSourceAfter s d later
  let jump : Jump route v u := .arrive v d [] later hqueue rfl (hr d.cell d.port)
  let e : Execution θ route s u := .cons (.flow flow) (.cons (.jump jump) (.nil _))
  refine ⟨{
    final := u
    execution := e
    date := rfl
    deliveries := rfl
    pending := rfl
    ready := fun j => by
      have h := quietAt_ready_coordinates s j (hs j) ht.le
      exact ⟨h.ready,h.charge,h.auxiliary⟩
    values := rfl
    gain_preserved := fun _ _ => rfl
    recovery_preserved := fun _ => rfl
    raw_active := ?_
    raw_other := ?_
    emissions := rfl
    physical := e.physical_invariant hb hf
    raw_valid := e.raw_valid hv
  }⟩
  · simp [u,quietSourceAfter,setRaw,quietAt]
  · intro j q h
    rcases h with hj | hq
    · simp [u,quietSourceAfter,setRaw,quietAt,hj,hr]
    · by_cases hj : j = d.cell
      · subst j
        simp [u,quietSourceAfter,setRaw,quietAt,hq,hr]
      · simp [u,quietSourceAfter,setRaw,quietAt,hj,hr]

/-- Saturation at the arrival clock is justified only after the head delivery
has actually been consumed, and only if all remaining tokens are later. -/
theorem QuietSourceArrival.complete {n θ route s d later}
    (c : @QuietSourceArrival n θ route s d later)
    (hf : ∀ f ∈ later, d.due < f.due) : CompleteThrough c.execution d.due := by
  refine ⟨c.date,?_,?_⟩
  · intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro j
        have hs := c.ready j
        simpa only [hs.ready] using (show c.final.x j .q < 1 by linarith [hs.charge.2])
      · intro j q
        have hs := (c.ready j).auxiliary q
        simpa only [hs.1] using (show c.final.x j (.m q) < 1 by linarith [hs.2.2])
    · intro j q origin hraw
      by_cases h : j = d.cell ∧ q = d.port
      · rcases h with ⟨rfl,rfl⟩
        have heq : origin = c.final.time := Option.some.inj (hraw.symm.trans c.raw_active)
        rw [heq]
        linarith
      · rw [c.raw_other j q (by tauto)] at hraw
        contradiction
    · intro f hm
      rw [c.pending] at hm
      rw [c.date]
      exact hf f hm
  · intro f hm
    rw [c.pending] at hm
    exact hf f hm

end KernelR.Hybrid
