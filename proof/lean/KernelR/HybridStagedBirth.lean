import KernelR.HybridSilentReturn
import KernelR.HybridPhysicalInvariant

/-! A dimension-changing birth event preserves existing cells and introduces
one fresh READY cell, with an explicit new-cell source queue. -/
namespace KernelR.Hybrid
open Set

/-- Fresh READY coordinate data; the surrounding birth event fixes its date. -/
structure Newborn where
  x : Coord → ℝ
  charge : 1 / 10 - 1 / 100000 ≤ x .q ∧ x .q ≤ 1 / 10 + 1 / 100000
  recovery : 2 / 25 - 1 / 100000 ≤ x .b ∧ x .b ≤ 2 / 25 + 1 / 100000
  reserve : 50 ≤ x .energy ∧ x .energy ≤ 100
  gain : ∀ p, Real.log (nominalGain p) - 1 / 100000 ≤ x (.z p) ∧
    x (.z p) ≤ Real.log (nominalGain p) + 1 / 100000
  sensor : ∀ p, RestBand (x (.m p))

noncomputable def Newborn.nominal : Newborn where
  x := fun c => match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z p => Real.log (nominalGain p)
    | .b => 2 / 25
    | .energy => 100
  charge := by norm_num
  recovery := by norm_num
  reserve := by norm_num
  gain := by intro p; constructor <;> linarith
  sensor := by intro p; norm_num [RestBand]

def Newborn.snapshot (newborn : Newborn) : Snapshot 1 where
  time := 0
  x := fun _ => newborn.x
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := []

theorem Newborn.birth_state (newborn : Newborn) : BirthState newborn.snapshot := by
  refine ⟨rfl,fun _ _ => rfl,fun _ => ⟨rfl,newborn.charge,newborn.recovery,newborn.reserve,?_⟩⟩
  intro p
  exact ⟨newborn.gain p,Or.inl ⟨rfl,(newborn.sensor p).1,(newborn.sensor p).2⟩⟩

theorem Newborn.nominal_birth_state : BirthState Newborn.nominal.snapshot :=
  Newborn.nominal.birth_state

def liftDelivery {n} (d : Delivery n) : Delivery (n + 1) := ⟨d.cell.castSucc,d.port,d.due⟩

def extendParameters {n} (old : Fin n → Parameters) (fresh : Parameters) : Fin (n + 1) → Parameters :=
  Fin.lastCases fresh old

def addNewborn {n} (s : Snapshot n) (newborn : Newborn)
    (sources : List (Delivery (n + 1))) : Snapshot (n + 1) where
  time := s.time
  x := Fin.lastCases newborn.x s.x
  main := Fin.lastCases .ready s.main
  aux := Fin.lastCases (fun _ => .ready) s.aux
  raw := Fin.lastCases (fun _ => none) s.raw
  pending := s.pending.map liftDelivery ++ sources

theorem PhysicalBox.extend_old {n θ fresh ε}
    (hb : @PhysicalBox (n + 1) (extendParameters θ fresh) ε) : PhysicalBox θ ε := by
  refine ⟨hb.1,?_⟩
  intro i p
  simpa only [extendParameters,Fin.lastCases_castSucc] using hb.2 i.castSucc p

theorem PhysicalBox.extend_new {n θ fresh ε}
    (hb : @PhysicalBox (n + 1) (extendParameters θ fresh) ε) :
    PhysicalBox (fun _ : Fin 1 => fresh) ε := by
  refine ⟨hb.1,?_⟩
  intro i p
  simpa only [extendParameters,Fin.lastCases_last] using hb.2 (Fin.last n) p

theorem addNewborn_physical_invariant {n θ fresh ε s} (newborn : Newborn)
    (sources : List (Delivery (n + 1)))
    (hb : @PhysicalBox (n + 1) (extendParameters θ fresh) ε) (hs : PhysicalInvariant θ s) :
    PhysicalInvariant (extendParameters θ fresh) (addNewborn s newborn sources) := by
  have hnew := newborn.birth_state.physical_invariant hb.extend_new
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [addNewborn,Fin.lastCases_last,Newborn.snapshot] using hnew.region 0
    · simpa only [addNewborn,Fin.lastCases_castSucc] using hs.region j
  · intro i p
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [addNewborn,extendParameters,Fin.lastCases_last,Newborn.snapshot] using hnew.gain_cap 0 p
    · simpa only [addNewborn,extendParameters,Fin.lastCases_castSucc] using hs.gain_cap j p
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [addNewborn,Fin.lastCases_last,Newborn.snapshot] using hnew.recovery_cap 0
    · simpa only [addNewborn,Fin.lastCases_castSucc] using hs.recovery_cap j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [addNewborn,Fin.lastCases_last,Newborn.snapshot] using hnew.reserve 0
    · simpa only [addNewborn,Fin.lastCases_castSucc] using hs.reserve j

theorem addNewborn_raw_valid {n s} (newborn : Newborn) (sources : List (Delivery (n + 1)))
    (hs : @RawValid n s) : RawValid (addNewborn s newborn sources) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro p origin hr
    simp only [addNewborn,Fin.lastCases_last] at hr
    contradiction
  · intro p origin hr
    simp only [addNewborn,Fin.lastCases_castSucc] at hr
    exact hs j p origin hr

/-- Birth appends one cell. Added source tokens target that cell and are not past due. -/
structure BirthStep {n} (s : Snapshot n) (u : Snapshot (n + 1)) where
  newborn : Newborn
  sources : List (Delivery (n + 1))
  source_cell : ∀ d ∈ sources, d.cell = Fin.last n
  source_future : ∀ d ∈ sources, s.time ≤ d.due
  state : u = addNewborn s newborn sources

theorem birth_step_exists {n s} (newborn : Newborn) (sources : List (Delivery (n + 1)))
    (hcell : ∀ d ∈ sources, d.cell = Fin.last n)
    (hfuture : ∀ d ∈ sources, s.time ≤ d.due) :
    Nonempty (BirthStep s (addNewborn s newborn sources)) :=
  ⟨⟨newborn,sources,hcell,hfuture,rfl⟩⟩

theorem BirthStep.time_unchanged {n s u} (birth : @BirthStep n s u) : u.time = s.time := by
  rw [birth.state]
  rfl

theorem BirthStep.old_coordinates {n s u} (birth : @BirthStep n s u) (i : Fin n) :
    u.x i.castSucc = s.x i := by
  rw [birth.state]
  simp only [addNewborn,Fin.lastCases_castSucc]

theorem BirthStep.old_modes {n s u} (birth : @BirthStep n s u) (i : Fin n) :
    u.main i.castSucc = s.main i ∧ u.aux i.castSucc = s.aux i := by
  rw [birth.state]
  simp only [addNewborn,Fin.lastCases_castSucc,and_self]

theorem BirthStep.old_raw {n s u} (birth : @BirthStep n s u) (i : Fin n) : u.raw i.castSucc = s.raw i := by
  rw [birth.state]
  simp only [addNewborn,Fin.lastCases_castSucc]

theorem BirthStep.pending {n s u} (birth : @BirthStep n s u) :
    u.pending = s.pending.map liftDelivery ++ birth.sources :=
  congrArg Snapshot.pending birth.state

theorem BirthStep.pending_future {n s u} (birth : @BirthStep n s u) (hs : PendingFuture s) : PendingFuture u := by
  intro d hd
  rw [birth.pending] at hd
  rw [birth.time_unchanged]
  rcases List.mem_append.mp hd with h | h
  · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp h
    exact hs old hold
  · exact birth.source_future d h

theorem BirthStep.old_pending_exact {n s u} (birth : @BirthStep n s u) :
    u.pending.filter (fun d => d.cell ≠ Fin.last n) = s.pending.map liftDelivery := by
  classical
  have hold : (s.pending.map liftDelivery).filter (fun d => d.cell ≠ Fin.last n) = s.pending.map liftDelivery := by
    apply List.filter_eq_self.mpr
    intro d hd
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hd
    simp [liftDelivery,ne_of_lt old.cell.castSucc_lt_last]
  have hnew : birth.sources.filter (fun d => d.cell ≠ Fin.last n) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have hm : d ∈ birth.sources ∧ d.cell ≠ Fin.last n := by
      simpa only [List.mem_filter,decide_eq_true_eq] using hd
    exact hm.2 (birth.source_cell d hm.1)
  rw [birth.pending,List.filter_append,hold,hnew,List.append_nil]

theorem BirthStep.new_coordinates {n s u} (birth : @BirthStep n s u) :
    u.x (Fin.last n) = birth.newborn.x := by
  simpa only [addNewborn,Fin.lastCases_last] using
    congrArg (fun v : Snapshot (n + 1) => v.x (Fin.last n)) birth.state

theorem BirthStep.new_ready {n s u} (birth : @BirthStep n s u) : ReadyCoordinates u (Fin.last n) := by
  have hmain : u.main (Fin.last n) = .ready := by rw [birth.state]; simp [addNewborn]
  have haux : ∀ p, u.aux (Fin.last n) p = .ready := by rw [birth.state]; simp [addNewborn]
  refine ⟨hmain,?_,fun p => ⟨haux p,?_⟩⟩
  · rw [birth.new_coordinates]
    exact ⟨birth.newborn.charge.1,by linarith [birth.newborn.charge.2]⟩
  · rw [birth.new_coordinates]
    exact birth.newborn.sensor p

theorem BirthStep.new_raw {n s u} (birth : @BirthStep n s u) : ∀ p, u.raw (Fin.last n) p = none := by
  rw [birth.state]
  simp [addNewborn]

theorem BirthStep.old_prepared {n s u} (birth : @BirthStep n s u) (i : Fin n)
    (hs : PreparedSection s i) : PreparedSection u i.castSucc := by
  have hx := birth.old_coordinates i
  have hm := birth.old_modes i
  exact ⟨by rw [hm.1]; exact hs.ready,
    by rw [hx]; exact hs.charge,by rw [hx]; exact hs.recovery,
    by rw [hm.2,hx]; exact hs.auxiliary⟩

theorem BirthStep.old_ready_coordinates {n s u} (birth : @BirthStep n s u) (i : Fin n)
    (hs : ReadyCoordinates s i) : ReadyCoordinates u i.castSucc := by
  have hx := birth.old_coordinates i
  have hm := birth.old_modes i
  exact ⟨by rw [hm.1]; exact hs.ready,by rw [hx]; exact hs.charge,
    by rw [hm.2,hx]; exact hs.auxiliary⟩

theorem BirthStep.new_recovery {n s u} (birth : @BirthStep n s u) :
    7999 / 100000 ≤ u.x (Fin.last n) .b ∧ u.x (Fin.last n) .b ≤ 8001 / 100000 := by
  rw [birth.new_coordinates]
  constructor <;> linarith [birth.newborn.recovery.1,birth.newborn.recovery.2]

theorem BirthStep.new_gain {n s u} (birth : @BirthStep n s u) (p : Port) :
    Real.log (nominalGain p) - 1 / 100000 ≤ u.x (Fin.last n) (.z p) ∧
    u.x (Fin.last n) (.z p) ≤ Real.log (nominalGain p) + 1 / 100000 := by
  rw [birth.new_coordinates]
  exact birth.newborn.gain p

theorem BirthStep.physical_invariant {n θ fresh ε s u} (birth : @BirthStep n s u)
    (hb : PhysicalBox (extendParameters θ fresh) ε) (hs : PhysicalInvariant θ s) :
    PhysicalInvariant (extendParameters θ fresh) u := by
  rw [birth.state]
  exact addNewborn_physical_invariant birth.newborn birth.sources hb hs

theorem BirthStep.raw_valid {n s u} (birth : @BirthStep n s u) (hs : RawValid s) : RawValid u := by
  rw [birth.state]
  exact addNewborn_raw_valid birth.newborn birth.sources hs

/-- Two physical phases joined by a birth event that changes the number of cells. -/
structure StagedExecution {n} (θ : Fin n → Parameters) (fresh : Parameters)
    (routeBefore : Router n) (routeAfter : Router (n + 1)) (s : Snapshot n) (u : Snapshot (n + 1)) where
  beforeBirth : Snapshot n
  afterBirth : Snapshot (n + 1)
  before : Execution θ routeBefore s beforeBirth
  birth : BirthStep beforeBirth afterBirth
  after : Execution (extendParameters θ fresh) routeAfter afterBirth u

theorem StagedExecution.physical_invariant {n θ fresh ε routeBefore routeAfter s u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u)
    (hb : PhysicalBox (extendParameters θ fresh) ε) (hs : PhysicalInvariant θ s) :
    PhysicalInvariant (extendParameters θ fresh) u :=
  e.after.physical_invariant hb (e.birth.physical_invariant hb (e.before.physical_invariant hb.extend_old hs))

theorem StagedExecution.raw_valid {n θ fresh routeBefore routeAfter s u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u) (hs : RawValid s) : RawValid u :=
  e.after.raw_valid (e.birth.raw_valid (e.before.raw_valid hs))

theorem StagedExecution.pending_future {n θ fresh routeBefore routeAfter s u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u)
    (hbefore : CausalRouter routeBefore) (hafter : CausalRouter routeAfter) (hs : PendingFuture s) :
    PendingFuture u :=
  e.after.pending_future hafter (e.birth.pending_future (e.before.pending_future hbefore hs))

theorem StagedExecution.time_bounds {n θ fresh routeBefore routeAfter s u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u) :
    s.time ≤ e.beforeBirth.time ∧ e.beforeBirth.time = e.afterBirth.time ∧ e.afterBirth.time ≤ u.time :=
  ⟨e.before.time_monotone,e.birth.time_unchanged.symm,e.after.time_monotone⟩

theorem StagedExecution.old_gain_balance {n θ fresh routeBefore routeAfter s u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u) (i : Fin n) (p : Port) :
    u.x i.castSucc (.z p) = s.x i (.z p) + e.before.ledger.error i p + e.after.ledger.error i.castSucc p := by
  rw [e.after.gain_balance,e.birth.old_coordinates,e.before.gain_balance]

theorem StagedExecution.old_recovery_balance {n θ fresh routeBefore routeAfter s u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u) (i : Fin n) :
    u.x i.castSucc .b = s.x i .b + e.before.ledger.recovery i + e.after.ledger.recovery i.castSucc := by
  rw [e.after.recovery_balance,e.birth.old_coordinates,e.before.recovery_balance]

theorem StagedExecution.new_gain_balance {n θ fresh routeBefore routeAfter s u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u) (p : Port) :
    u.x (Fin.last n) (.z p) = e.birth.newborn.x (.z p) + e.after.ledger.error (Fin.last n) p := by
  rw [e.after.gain_balance,e.birth.new_coordinates]

theorem StagedExecution.new_recovery_balance {n θ fresh routeBefore routeAfter s u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u) :
    u.x (Fin.last n) .b = e.birth.newborn.x .b + e.after.ledger.recovery (Fin.last n) := by
  rw [e.after.recovery_balance,e.birth.new_coordinates]

end KernelR.Hybrid
