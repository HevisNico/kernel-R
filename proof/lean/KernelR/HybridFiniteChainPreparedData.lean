import KernelR.HybridFiniteCausalChain
import KernelR.HybridFiniteCadenceContact
import KernelR.HybridAutonomousCellProjection
import KernelR.HybridFiniteChainFamilyPreparation
import KernelR.HybridPreparedCadenceChainDomain

/-! The finite source family is indexed root first and leaf last. The causal
construction starts at the original leaf and adds its real ancestors. These
maps retain physical coordinates and the original external leaf queue; they
introduce no reaching-execution or reset premise. -/
namespace KernelR.Hybrid

/-- A depth-j suffix contains original indices n-j,...,n, in the same order. -/
def finiteChainSuffixIndex (n j : ℕ) (hj : j≤n) (i : Fin (j+1)) : Fin (n+1) :=
  ⟨n-j+i.val,by omega⟩

/-- Before adding head j, its original position is n-1-j. Out of range the
actual original root is a harmless unused default. -/
def finiteChainHeadIndex (n j : ℕ) : Fin (n+1) := ⟨n-(j+1),by omega⟩

@[simp] theorem finiteChainSuffixIndex_leaf (n : ℕ) (i : Fin 1) :
    finiteChainSuffixIndex n 0 (Nat.zero_le n) i=Fin.last n := by
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  apply Fin.ext
  simp [finiteChainSuffixIndex]

@[simp] theorem finiteChainSuffixIndex_head (n j : ℕ) (hj : j+1≤n) :
    finiteChainSuffixIndex n (j+1) hj 0=finiteChainHeadIndex n j := by
  apply Fin.ext
  simp [finiteChainSuffixIndex,finiteChainHeadIndex]

@[simp] theorem finiteChainSuffixIndex_succ (n j : ℕ) (hj : j+1≤n) (i : Fin (j+1)) :
    finiteChainSuffixIndex n (j+1) hj i.succ=finiteChainSuffixIndex n j (by omega) i := by
  apply Fin.ext
  simp only [finiteChainSuffixIndex,Fin.val_succ]
  omega

@[simp] theorem finiteChainSuffixIndex_full (n : ℕ) (i : Fin (n+1)) :
    finiteChainSuffixIndex n n (Nat.le_refl n) i=i := by
  apply Fin.ext
  simp [finiteChainSuffixIndex]

/-- Only actual links below n are used. The total record's unused contacts
have a fixed positive default, adding no restriction to the physical links. -/
noncomputable def finiteChainPreparedDelay (n : ℕ) (delay : ℕ→ℝ→ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  if j<n then delay j t else 7/20

noncomputable def finiteChainPreparedData {n : ℕ} (θ : Fin (n+1)→Parameters)
    (s : Snapshot (n+1)) (delay : ℕ→ℝ→ℝ) (T : ℝ)
    (hd : ∀ j, j<n → ∀ t, 0<delay j t) : FiniteCausalChainData where
  leafParameters := θ (Fin.last n)
  leafSource := s.autonomousView (Fin.last n)
  headParameters := fun j => θ (finiteChainHeadIndex n j)
  headSource := fun j => (s.autonomousView (finiteChainHeadIndex n j)).requeue []
  common_clock := fun _ => rfl
  contacts := fun j => finiteCadenceHeadContact (0 : Fin (j+1)) 2 160 (T+1)
    (finiteChainPreparedDelay n delay j)
  strict_contacts := by
    intro j
    apply finite_cadence_head_contact_strict
    intro t
    dsimp [finiteChainPreparedDelay]
    split_ifs with hj
    · exact hd j hj t
    · norm_num

namespace FiniteChainPreparedData
variable {n : ℕ} {θ : Fin (n+1)→Parameters} {s : Snapshot (n+1)}
  {delay : ℕ→ℝ→ℝ} {T : ℝ} {hd : ∀ j, j<n → ∀ t, 0<delay j t}

@[simp] theorem contacts (j : ℕ) (hj : j<n) :
    (finiteChainPreparedData θ s delay T hd).contacts j=
      finiteCadenceHeadContact (0 : Fin (j+1)) 2 160 (T+1) (delay j) := by
  change finiteCadenceHeadContact 0 2 160 (T+1) (finiteChainPreparedDelay n delay j)=_
  have hdelay : finiteChainPreparedDelay n delay j=delay j := by
    funext t
    simp only [finiteChainPreparedDelay,ite_eq_left_iff]
    exact fun h => (h hj).elim
  rw [hdelay]

/-- Every recursive parameter row is the corresponding original row. -/
theorem parameters_suffix : ∀ j (hj : j≤n) (i : Fin (j+1)),
    (finiteChainPreparedData θ s delay T hd).parameters j i=
      θ (finiteChainSuffixIndex n j hj i) := by
  intro j
  induction j with
  | zero =>
    intro hj i
    simp only [FiniteCausalChainData.parameters,finiteChainPreparedData,finiteChainSuffixIndex_leaf]
  | succ j ih =>
    intro hj i
    cases i using Fin.cases with
    | zero =>
      change θ (finiteChainHeadIndex n j)=_
      rw [finiteChainSuffixIndex_head]
    | succ i =>
      change (finiteChainPreparedData θ s delay T hd).parameters j i=_
      rw [finiteChainSuffixIndex_succ]
      exact ih (by omega) i

/-- The recursive snapshots retain all actual values, modes and RAW origins
of their original suffix, including the actual physical energy coordinate. -/
theorem source_coordinates : ∀ j (hj : j≤n) (i : Fin (j+1)),
    ((finiteChainPreparedData θ s delay T hd).source j).x i = s.x (finiteChainSuffixIndex n j hj i) ∧
    ((finiteChainPreparedData θ s delay T hd).source j).main i = s.main (finiteChainSuffixIndex n j hj i) ∧
    ((finiteChainPreparedData θ s delay T hd).source j).aux i = s.aux (finiteChainSuffixIndex n j hj i) ∧
    ((finiteChainPreparedData θ s delay T hd).source j).raw i = s.raw (finiteChainSuffixIndex n j hj i) := by
  intro j
  induction j with
  | zero =>
    intro hj i
    simp only [finiteChainSuffixIndex_leaf]
    exact ⟨rfl,rfl,rfl,rfl⟩
  | succ j ih =>
    intro hj i
    cases i using Fin.cases with
    | zero =>
      rw [finiteChainSuffixIndex_head]
      exact ⟨rfl,rfl,rfl,rfl⟩
    | succ i =>
      rw [finiteChainSuffixIndex_succ]
      exact ih (by omega) i

@[simp] theorem parameters_full :
    (finiteChainPreparedData θ s delay T hd).parameters n=θ := by
  funext i
  simpa only [finiteChainSuffixIndex_full] using parameters_suffix (s:=s) (hd:=hd) n (Nat.le_refl n) i

/-- Every suffix inherits the original independent fabrication box. -/
theorem physical_box {ε} (hb : PhysicalBox θ ε) (j : ℕ) (hj : j≤n) :
    PhysicalBox ((finiteChainPreparedData θ s delay T hd).parameters j) ε := by
  refine ⟨hb.1,?_⟩
  intro i p
  rw [parameters_suffix j hj i]
  exact hb.2 (finiteChainSuffixIndex n j hj i) p

/-- Current physical invariants pull back along exact suffix coordinates. -/
theorem physical (hf : PhysicalInvariant θ s) (j : ℕ) (hj : j≤n) :
    PhysicalInvariant ((finiteChainPreparedData θ s delay T hd).parameters j)
      ((finiteChainPreparedData θ s delay T hd).source j) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    obtain ⟨hx,hm,ha,hr⟩ := source_coordinates (hd:=hd) j hj i
    rw [hx,ha]
    exact hf.region _
  · intro i p
    obtain ⟨hx,hm,ha,hr⟩ := source_coordinates (hd:=hd) j hj i
    rw [hx,parameters_suffix j hj i]
    exact hf.gain_cap _ p
  · intro i
    obtain ⟨hx,hm,ha,hr⟩ := source_coordinates (hd:=hd) j hj i
    rw [hx]
    exact hf.recovery_cap _
  · intro i
    obtain ⟨hx,hm,ha,hr⟩ := source_coordinates (hd:=hd) j hj i
    rw [hx]
    exact hf.reserve _

/-- No RAW current is manufactured by coordinate projection. -/
theorem raw_none (hr : ∀ i p, s.raw i p=none) (j : ℕ) (hj : j≤n) :
    ∀ i p, ((finiteChainPreparedData θ s delay T hd).source j).raw i p=none := by
  intro i p
  rw [(source_coordinates (hd:=hd) j hj i).2.2.2]
  exact hr _ p

private theorem projected_source_train (i : Fin (n+1)) (p : Port) (start gap : ℝ) (K : ℕ) :
    cellQueue i (sourceTrain i p start gap K)=sourceTrain 0 p start gap K := by
  induction K generalizing start with
  | zero => rfl
  | succ K ih =>
    rw [sourceTrain_succ,sourceTrain_succ]
    simpa [cellQueue,Delivery.atCell] using
      congrArg (List.cons (⟨0,p,start⟩ : Delivery 1)) (ih (start+gap))


private theorem lift_leaf_delivery (j : ℕ) (p : Port) (due : ℝ) :
    FiniteCausalChainData.liftLeafDelivery j (⟨0,p,due⟩ : Delivery 1)=⟨Fin.last j,p,due⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [FiniteCausalChainData.liftLeafDelivery,ih]
    rfl

/-- The only operational pending tokens are the actual external leaf train. -/
theorem source_pending {K : ℕ} (hq : s.pending=sourceTrain (Fin.last n) 0 160 4 K) (j : ℕ) :
    ((finiteChainPreparedData θ s delay T hd).source j).pending=sourceTrain (Fin.last j) 0 160 4 K := by
  rw [FiniteCausalChainData.source_pending]
  change (cellQueue (Fin.last n) s.pending).map _=_
  rw [hq,projected_source_train]
  simp only [sourceTrain,List.map_ofFn,Function.comp_def,lift_leaf_delivery]

private theorem snapshot_eq {k : ℕ} {a b : Snapshot k}
    (ht : a.time=b.time) (hx : a.x=b.x) (hm : a.main=b.main)
    (ha : a.aux=b.aux) (hr : a.raw=b.raw) (hq : a.pending=b.pending) : a=b := by
  cases a
  cases b
  simp_all only

/-- Reassembling all original suffix coordinates recovers the exact actual
family snapshot, including its global external source queue. -/
theorem source_full {K : ℕ} (hq : s.pending=sourceTrain (Fin.last n) 0 160 4 K) :
    (finiteChainPreparedData θ s delay T hd).source n=s := by
  have hclock : ((finiteChainPreparedData θ s delay T hd).source n).time=s.time :=
    FiniteCausalChainData.source_clock _ n
  have hx : ((finiteChainPreparedData θ s delay T hd).source n).x=s.x := by
    funext i
    simpa only [finiteChainSuffixIndex_full] using (source_coordinates (hd:=hd) n (Nat.le_refl n) i).1
  have hm : ((finiteChainPreparedData θ s delay T hd).source n).main=s.main := by
    funext i
    simpa only [finiteChainSuffixIndex_full] using (source_coordinates (hd:=hd) n (Nat.le_refl n) i).2.1
  have ha : ((finiteChainPreparedData θ s delay T hd).source n).aux=s.aux := by
    funext i
    simpa only [finiteChainSuffixIndex_full] using (source_coordinates (hd:=hd) n (Nat.le_refl n) i).2.2.1
  have hr : ((finiteChainPreparedData θ s delay T hd).source n).raw=s.raw := by
    funext i
    simpa only [finiteChainSuffixIndex_full] using (source_coordinates (hd:=hd) n (Nat.le_refl n) i).2.2.2
  have hp : ((finiteChainPreparedData θ s delay T hd).source n).pending=s.pending :=
    (source_pending hq n).trans hq.symm
  exact snapshot_eq hclock hx hm ha hr hp

end FiniteChainPreparedData
end KernelR.Hybrid

namespace KernelR.Hybrid
namespace FiniteChainFamilyPreparation
variable {n : ℕ} {θ : Fin (n+1)→Parameters} {bornCells : Fin (n+1)→Snapshot 1} {K : ℕ}
  (f : FiniteChainFamilyPreparation θ bornCells K)

/-- The fast-phase data comes from the true common preparation endpoint. -/
noncomputable def cadenceData (delay : ℕ→ℝ→ℝ) (T : ℝ)
    (hd : ∀ j, j<n → ∀ t, 0<delay j t) : FiniteCausalChainData :=
  finiteChainPreparedData θ f.final delay T hd

variable {delay : ℕ→ℝ→ℝ} {T : ℝ} {hd : ∀ j, j<n → ∀ t, 0<delay j t}

@[simp] theorem cadence_parameters_full : (f.cadenceData delay T hd).parameters n=θ :=
  FiniteChainPreparedData.parameters_full

@[simp] theorem cadence_source_full : (f.cadenceData delay T hd).source n=f.final :=
  FiniteChainPreparedData.source_full f.pending

theorem cadence_parameters_suffix (j : ℕ) (hj : j≤n) (i : Fin (j+1)) :
    (f.cadenceData delay T hd).parameters j i=θ (finiteChainSuffixIndex n j hj i) :=
  FiniteChainPreparedData.parameters_suffix j hj i

theorem cadence_source_coordinates (j : ℕ) (hj : j≤n) (i : Fin (j+1)) :
    ((f.cadenceData delay T hd).source j).x i=f.final.x (finiteChainSuffixIndex n j hj i) ∧
    ((f.cadenceData delay T hd).source j).main i=f.final.main (finiteChainSuffixIndex n j hj i) ∧
    ((f.cadenceData delay T hd).source j).aux i=f.final.aux (finiteChainSuffixIndex n j hj i) ∧
    ((f.cadenceData delay T hd).source j).raw i=f.final.raw (finiteChainSuffixIndex n j hj i) :=
  FiniteChainPreparedData.source_coordinates j hj i

theorem cadence_box {ε} (hb : PhysicalBox θ ε) (j : ℕ) (hj : j≤n) :
    PhysicalBox ((f.cadenceData delay T hd).parameters j) ε :=
  FiniteChainPreparedData.physical_box hb j hj

theorem cadence_physical (j : ℕ) (hj : j≤n) :
    PhysicalInvariant ((f.cadenceData delay T hd).parameters j) ((f.cadenceData delay T hd).source j) :=
  FiniteChainPreparedData.physical f.physical j hj

theorem cadence_raw_none (j : ℕ) (hj : j≤n) :
    ∀ i p, ((f.cadenceData delay T hd).source j).raw i p=none :=
  FiniteChainPreparedData.raw_none f.raw_none j hj

theorem cadence_raw_valid (j : ℕ) (hj : j≤n) : RawValid ((f.cadenceData delay T hd).source j) := by
  intro i p origin hr
  rw [f.cadence_raw_none j hj i p] at hr
  contradiction

theorem cadence_source_date (j : ℕ) : ((f.cadenceData delay T hd).source j).time=1599/10 :=
  ((f.cadenceData delay T hd).source_clock j).trans f.date

theorem cadence_source_pending (j : ℕ) :
    ((f.cadenceData delay T hd).source j).pending=sourceTrain (Fin.last j) 0 160 4 K :=
  FiniteChainPreparedData.source_pending f.pending j

theorem cadence_leaf_date : (f.cadenceData delay T hd).leafSource.time=1599/10 := f.date

theorem cadence_leaf_prepared : PreparedSection (f.cadenceData delay T hd).leafSource 0 := by
  have h := f.prepared (Fin.last n)
  exact ⟨h.ready,h.charge,h.recovery,h.auxiliary⟩

theorem cadence_leaf_charge : (f.cadenceData delay T hd).leafSource.x 0 .q=1/10 := f.charge _

theorem cadence_leaf_raw : ∀ p, (f.cadenceData delay T hd).leafSource.raw 0 p=none := f.raw_none _

theorem cadence_leaf_pending : (f.cadenceData delay T hd).leafSource.pending=sourceTrain 0 0 160 4 K := by
  exact f.cadence_source_pending (delay:=delay) (T:=T) (hd:=hd) 0

theorem cadence_leaf_box {ε} (hb : PhysicalBox θ ε) :
    PhysicalBox (fun _ : Fin 1 => (f.cadenceData delay T hd).leafParameters) ε :=
  ⟨hb.1,fun _ p => hb.2 (Fin.last n) p⟩

theorem cadence_leaf_physical : PhysicalInvariant
    (fun _ : Fin 1 => (f.cadenceData delay T hd).leafParameters) (f.cadenceData delay T hd).leafSource :=
  Snapshot.autonomousView_physical f.physical (Fin.last n)

theorem cadence_leaf_raw_valid : RawValid (f.cadenceData delay T hd).leafSource :=
  Snapshot.autonomousView_raw_valid f.raw_valid (Fin.last n)

/-- The leaf's fast port remains its own low birth port after port1 teaching. -/
theorem cadence_leaf_gain_own :
    (f.cadenceData delay T hd).leafSource.x 0 (.z 0)=(bornCells (Fin.last n)).x 0 (.z 0) :=
  f.gain_other (Fin.last n) 0 (by simp [finiteChainPreparationPort])

theorem cadence_leaf_recovery_own :
    (f.cadenceData delay T hd).leafSource.x 0 .b=(bornCells (Fin.last n)).x 0 .b+1/10 := f.recovery _

theorem cadence_leaf_log_gain :
    Real.log (3/10)-1/100000 ≤ (f.cadenceData delay T hd).leafSource.x 0 (.z 0) ∧
    (f.cadenceData delay T hd).leafSource.x 0 (.z 0) ≤ Real.log (3/10)+1/100000 := by
  have hg := f.gain_other (Fin.last n) 0 (by simp [finiteChainPreparationPort])
  have hz := (((f.initial_birth (Fin.last n)).2.2 0).2.2.2.2 (0 : Port)).1
  change Real.log (3/10)-1/100000 ≤ f.final.x (Fin.last n) (.z 0) ∧
    f.final.x (Fin.last n) (.z 0) ≤ Real.log (3/10)+1/100000
  rw [hg]
  simpa only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] using hz

theorem cadence_leaf_recovery :
    17999/100000 ≤ (f.cadenceData delay T hd).leafSource.x 0 .b ∧
    (f.cadenceData delay T hd).leafSource.x 0 .b ≤ 18001/100000 :=
  (f.prepared (Fin.last n)).recovery

private theorem cadence_head_not_leaf (j : ℕ) (hj : j<n) : finiteChainHeadIndex n j≠Fin.last n := by
  intro h
  have hv := congrArg Fin.val h
  simp only [finiteChainHeadIndex,Fin.val_last] at hv
  omega

theorem cadence_head_parameters (j : ℕ) :
    (f.cadenceData delay T hd).headParameters j=θ (finiteChainHeadIndex n j) := rfl

theorem cadence_head_date (j : ℕ) : ((f.cadenceData delay T hd).headSource j).time = 1599/10 := f.date

theorem cadence_head_pending (j : ℕ) : ((f.cadenceData delay T hd).headSource j).pending=[] := rfl

theorem cadence_head_prepared (j : ℕ) : PreparedSection ((f.cadenceData delay T hd).headSource j) 0 := by
  have h := f.prepared (finiteChainHeadIndex n j)
  exact ⟨h.ready,h.charge,h.recovery,h.auxiliary⟩

theorem cadence_head_charge (j : ℕ) : ((f.cadenceData delay T hd).headSource j).x 0 .q=1/10 := f.charge _

theorem cadence_head_raw (j : ℕ) : ∀ p, ((f.cadenceData delay T hd).headSource j).raw 0 p=none := f.raw_none _

theorem cadence_head_box {ε} (hb : PhysicalBox θ ε) (j : ℕ) :
    PhysicalBox (fun _ : Fin 1 => (f.cadenceData delay T hd).headParameters j) ε :=
  ⟨hb.1,fun _ p => hb.2 (finiteChainHeadIndex n j) p⟩

theorem cadence_head_physical (j : ℕ) : PhysicalInvariant
    (fun _ : Fin 1 => (f.cadenceData delay T hd).headParameters j)
    ((f.cadenceData delay T hd).headSource j) := by
  have h := Snapshot.autonomousView_physical f.physical (finiteChainHeadIndex n j)
  exact ⟨h.region,h.gain_cap,h.recovery_cap,h.reserve⟩

theorem cadence_head_raw_valid (j : ℕ) : RawValid ((f.cadenceData delay T hd).headSource j) := by
  intro i p origin hr
  change f.final.raw (finiteChainHeadIndex n j) p=some origin at hr
  rw [f.raw_none] at hr
  contradiction

theorem cadence_head_gain_own (j : ℕ) (hj : j<n) :
    ((f.cadenceData delay T hd).headSource j).x 0 (.z 2)=
      (bornCells (finiteChainHeadIndex n j)).x 0 (.z 2)+9/5 := by
  change f.final.x (finiteChainHeadIndex n j) (.z 2)=_
  have hn := cadence_head_not_leaf j hj
  simpa only [finiteChainPreparationPort,finiteChainPreparationDose,ite_eq_right hn]
    using f.gain_target (finiteChainHeadIndex n j)

theorem cadence_head_recovery_own (j : ℕ) :
    ((f.cadenceData delay T hd).headSource j).x 0 .b=
      (bornCells (finiteChainHeadIndex n j)).x 0 .b+1/10 := f.recovery _

theorem cadence_head_log_gain (j : ℕ) (hj : j<n) :
    Real.log (3/10)+9/5-1/100000 ≤ ((f.cadenceData delay T hd).headSource j).x 0 (.z 2) ∧
    ((f.cadenceData delay T hd).headSource j).x 0 (.z 2) ≤ Real.log (3/10)+9/5+1/100000 := by
  have hn := cadence_head_not_leaf j hj
  have hg := f.gain_target (finiteChainHeadIndex n j)
  simp only [finiteChainPreparationPort,finiteChainPreparationDose,ite_eq_right hn] at hg
  have hz := (((f.initial_birth (finiteChainHeadIndex n j)).2.2 0).2.2.2.2 (2 : Port)).1
  simp only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] at hz
  change Real.log (3/10)+9/5-1/100000 ≤ f.final.x (finiteChainHeadIndex n j) (.z 2) ∧
    f.final.x (finiteChainHeadIndex n j) (.z 2) ≤ Real.log (3/10)+9/5+1/100000
  rw [hg]
  constructor <;> linarith [hz.1,hz.2]

theorem cadence_head_recovery (j : ℕ) :
    17999/100000 ≤ ((f.cadenceData delay T hd).headSource j).x 0 .b ∧
    ((f.cadenceData delay T hd).headSource j).x 0 .b ≤ 18001/100000 :=
  (f.prepared (finiteChainHeadIndex n j)).recovery


/-- The actual preparation discharges every physical part of the fast-phase
initial domain. The remaining assumptions are only source length and declared
wire geometry; no execution, calendar, dose or output count is supplied. -/
theorem cadence_domain {ε} (hb : PhysicalBox θ ε) (sigma centre : ℕ→ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10 : ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ time, -sigma j≤delay j time-centre j ∧ delay j time-centre j≤sigma j) :
    PreparedCadenceChainDomain (f.cadenceData delay (cadenceChainTerminal n K) hd) ε n K sigma centre delay := by
  let T := cadenceChainTerminal n K
  refine {
    source_clock := f.cadence_leaf_date (T:=T) (hd:=hd)
    budget := hK, sigma_nonneg := hsigma, jitter_budget := hbudget
    centre_bounds := hcentre, error_bounds := herror
    contacts := ?_
    parameter_box := fun j hj => f.cadence_box (T:=T) (hd:=hd) hb j hj
    source_physical := fun j hj => f.cadence_physical (T:=T) (hd:=hd) j hj
    source_raw_valid := fun j hj => f.cadence_raw_valid (T:=T) (hd:=hd) j hj
    leaf_prepared := f.cadence_leaf_prepared (T:=T) (hd:=hd)
    leaf_charge := f.cadence_leaf_charge (T:=T) (hd:=hd)
    leaf_raw := f.cadence_leaf_raw (T:=T) (hd:=hd)
    leaf_gain := f.cadence_leaf_log_gain (T:=T) (hd:=hd)
    leaf_queue := f.cadence_leaf_pending (T:=T) (hd:=hd)
    head_box := fun j _ => f.cadence_head_box (T:=T) (hd:=hd) hb j
    head_physical := fun j _ => f.cadence_head_physical (T:=T) (hd:=hd) j
    head_raw_valid := fun j _ => f.cadence_head_raw_valid (T:=T) (hd:=hd) j
    head_prepared := fun j _ => f.cadence_head_prepared (T:=T) (hd:=hd) j
    head_charge := fun j _ => f.cadence_head_charge (T:=T) (hd:=hd) j
    head_raw := fun j _ => f.cadence_head_raw (T:=T) (hd:=hd) j
    head_gain := fun j hj => f.cadence_head_log_gain (T:=T) (hd:=hd) j hj
    head_queue := fun j _ => f.cadence_head_pending (T:=T) (hd:=hd) j
  }
  intro j hj
  exact FiniteChainPreparedData.contacts (s:=f.final) (θ:=θ) (T:=T) (hd:=hd) j hj

end FiniteChainFamilyPreparation
end KernelR.Hybrid
