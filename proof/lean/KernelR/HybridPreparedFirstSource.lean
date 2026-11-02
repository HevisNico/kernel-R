import KernelR.HybridShortLearnedNextSource

/-! A prepared one-cell receiver waits along its own quiet physical path,
then consumes the first declared input token at its actual date. -/
namespace KernelR.Hybrid

structure PreparedFirstSource (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (H : ℝ) (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  date : final.time = H
  values : final.x = (quietAt s H).x
  prepared : PreparedSection final 0
  charge : final.x 0 .q = 1 / 10
  raw_active : final.raw 0 p = some H
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = later
  gains : ∀ q, final.x 0 (.z q) = s.x 0 (.z q)
  recovery : final.x 0 .b = s.x 0 .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,p,H⟩]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution H

theorem prepared_first_source_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (H : ℝ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : PreparedSection s 0)
    (hq : s.x 0 .q = 1 / 10) (hr : ∀ q, s.raw 0 q = none)
    (hqueue : s.pending = ⟨0,p,H⟩ :: later) (hgap : s.time < H)
    (hLater : ∀ d ∈ later, H < d.due) : Nonempty (PreparedFirstSource θ s p H later) := by
  have hFuture : ∀ d ∈ s.pending, H ≤ d.due := by
    intro d hd
    rw [hqueue] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_rfl
    · exact (hLater d hd).le
  let flow := quietFlow (θ := θ) s hgap
    (fun j => by have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hs.ready)
    (fun j q => by have hj : j = 0 := Subsingleton.elim _ _; subst j; exact (hs.auxiliary q).1)
    (fun j q => by have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hr q)
    (fun j => by have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [hs.charge.2])
    (fun j q => by have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hs.auxiliary q).2.2]) hFuture
  let before : Snapshot 1 := quietAt s H
  let final : Snapshot 1 := {setRaw before 0 p (some H) with pending := later}
  let arrival : Jump (fun _ _ => []) before final :=
    .arrive before ⟨0,p,H⟩ [] later hqueue rfl (hr p)
  let execution : Execution θ (fun _ _ => []) s final :=
    .cons (.flow flow) (.cons (.jump arrival) (.nil _))
  have hReady : ReadyCoordinates before 0 := quietAt_ready_coordinates s 0 hs.ready_coordinates hgap.le
  have hPrepared : PreparedSection final 0 :=
    ⟨hReady.ready,hReady.charge,hs.recovery,hReady.auxiliary⟩
  have hCharge : final.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (s.x 0 .q) s.time H = _
    rw [hq]
    simp [relax]
  have hActive : final.raw 0 p = some H := by simp [final,setRaw]
  have hOther : ∀ q, q ≠ p → final.raw 0 q = none := by
    intro q hq
    simpa [final,before,quietAt,setRaw,hq] using hr q
  have hPending : ∀ d ∈ final.pending, final.time < d.due := hLater
  have hGuard : BeforeGuards final final.x := by
    constructor
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [hPrepared.ready,hCharge]
      norm_num
    · intro i q
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [(hPrepared.auxiliary q).1]
      linarith [(hPrepared.auxiliary q).2.2]
  have hComplete : CompleteThrough execution H := by
    refine ⟨rfl,?_,hPending⟩
    intro u
    apply hGuard.no_jump
    · intro i q origin hraw
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      by_cases hq : q = p
      · subst q
        have ho : origin = H := Option.some.inj (hraw.symm.trans hActive)
        rw [ho]
        change H < H + 1
        linarith
      · rw [hOther q hq] at hraw
        contradiction
    · exact hPending
  exact ⟨{
    final := final, execution := execution, date := rfl, values := rfl
    prepared := hPrepared, charge := hCharge, raw_active := hActive, raw_other := hOther
    pending := rfl, gains := fun _ => rfl, recovery := rfl, emissions := rfl, deliveries := rfl
    physical := execution.physical_invariant hb hf, raw_valid := execution.raw_valid hv, complete := hComplete
  }⟩

end KernelR.Hybrid
