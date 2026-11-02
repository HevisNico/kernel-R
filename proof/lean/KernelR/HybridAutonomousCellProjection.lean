import KernelR.HybridStableMemory
import KernelR.HybridInputs
import KernelR.HybridPhysicalInvariant

/-! Extract an actual autonomous cell trace from a finite network execution.
The queue is filtered by destination, including actual external sources. All
selected ODE coordinates, modes, RAW origins and energy are retained. A FIRE
of another cell is skipped; an outgoing selected FIRE becomes a real local
FIRE with empty routing, never a manufactured external source. -/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- A token belongs to the projected queue exactly when it targets the cell. -/
def Delivery.atCell {n} (i : Fin n) (d : Delivery n) : Option (Delivery 1) :=
  if d.cell=i then some ⟨0,d.port,d.due⟩ else none

def cellQueue {n} (i : Fin n) (Q : List (Delivery n)) : List (Delivery 1) := Q.filterMap (Delivery.atCell i)

def cellEmissions {n} (i : Fin n) (events : List (Fin n×ℝ)) : List (Fin 1×ℝ) :=
  events.filterMap (fun ev => if ev.1=i then some (0,ev.2) else none)

/-- The one-cell queue is a projection of the actual global queue. -/
noncomputable def Snapshot.autonomousView {n} (s : Snapshot n) (i : Fin n) : Snapshot 1 where
  time:=s.time
  x:=fun _ => s.x i
  main:=fun _ => s.main i
  aux:=fun _ => s.aux i
  raw:=fun _ => s.raw i
  pending:=cellQueue i s.pending

def NoIncoming {n} (route : Router n) (i : Fin n) : Prop :=
  ∀ j time d, d∈route j time → d.cell≠i

@[simp] theorem cellQueue_nil {n} (i : Fin n) : cellQueue i []=[] := rfl

@[simp] theorem cellQueue_append {n} (i : Fin n) (Q R : List (Delivery n)) :
    cellQueue i (Q++R)=cellQueue i Q++cellQueue i R := by simp [cellQueue,List.filterMap_append]

@[simp] theorem cellEmissions_append {n} (i : Fin n) (Q R : List (Fin n×ℝ)) :
    cellEmissions i (Q++R)=cellEmissions i Q++cellEmissions i R := by
  simp [cellEmissions,List.filterMap_append]

theorem NoIncoming.cell_queue_empty {n route} {i : Fin n} (h : NoIncoming route i) (j : Fin n) (time : ℝ) :
    cellQueue i (route j time)=[] := by
  have aux : ∀ Q : List (Delivery n), (∀ d∈Q, d.cell≠i) → cellQueue i Q=[] := by
    intro Q
    induction Q with
    | nil => simp
    | cons d Q ih =>
      intro hQ
      have hd : d.cell≠i := hQ d (by simp)
      have ht := ih (fun x hx => hQ x (by simp [hx]))
      simpa [cellQueue,Delivery.atCell,hd] using ht
  exact aux _ (fun d hd => h j time d hd)

private theorem view_ext {a b : Snapshot 1}
    (ht : a.time=b.time) (hx : a.x=b.x) (hm : a.main=b.main)
    (ha : a.aux=b.aux) (hr : a.raw=b.raw) (hq : a.pending=b.pending) : a=b := by
  cases a; cases b; simp_all only

@[simp] theorem Snapshot.autonomousView_setMain_self {n} (s : Snapshot n) (i : Fin n) (mode : MainMode) :
    (setMain s i mode).autonomousView i=setMain (s.autonomousView i) 0 mode := by
  apply view_ext
  · rfl
  · rfl
  · funext j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp [Snapshot.autonomousView,setMain]
  · rfl
  · rfl
  · rfl

@[simp] theorem Snapshot.autonomousView_setMain_other {n} (s : Snapshot n) (i j : Fin n)
    (mode : MainMode) (h : j≠i) : (setMain s j mode).autonomousView i=s.autonomousView i := by
  apply view_ext
  · rfl
  · rfl
  · funext k
    simp [Snapshot.autonomousView,setMain,Ne.symm h]
  · rfl
  · rfl
  · rfl

@[simp] theorem Snapshot.autonomousView_setAux_self {n} (s : Snapshot n) (i : Fin n) (p : Port) (mode : AuxMode) :
    (setAux s i p mode).autonomousView i=setAux (s.autonomousView i) 0 p mode := by
  apply view_ext
  · rfl
  · rfl
  · rfl
  · funext j q
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp [Snapshot.autonomousView,setAux]
  · rfl
  · rfl

@[simp] theorem Snapshot.autonomousView_setAux_other {n} (s : Snapshot n) (i j : Fin n)
    (p : Port) (mode : AuxMode) (h : j≠i) : (setAux s j p mode).autonomousView i=s.autonomousView i := by
  apply view_ext
  · rfl
  · rfl
  · rfl
  · funext k q
    simp [Snapshot.autonomousView,setAux,Ne.symm h]
  · rfl
  · rfl

@[simp] theorem Snapshot.autonomousView_setRaw_self {n} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ) :
    (setRaw s i p origin).autonomousView i=setRaw (s.autonomousView i) 0 p origin := by
  apply view_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext j q
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp [Snapshot.autonomousView,setRaw]
  · rfl

@[simp] theorem Snapshot.autonomousView_setRaw_other {n} (s : Snapshot n) (i j : Fin n)
    (p : Port) (origin : Option ℝ) (h : j≠i) : (setRaw s j p origin).autonomousView i=s.autonomousView i := by
  apply view_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext k q
    simp [Snapshot.autonomousView,setRaw,Ne.symm h]
  · rfl

theorem Snapshot.autonomousView_pending {n} (s : Snapshot n) (i : Fin n) (Q : List (Delivery n)) :
    ({s with pending:=Q} : Snapshot n).autonomousView i={s.autonomousView i with pending:=cellQueue i Q} := rfl

/-- Projection is exact even for the energy equation and non-ready modes. -/
noncomputable def Flow.autonomousView {n θ s u} (f : @Flow n θ s u) (i : Fin n) :
    Flow (fun _ : Fin 1 => θ i) (s.autonomousView i) (u.autonomousView i) where
  positive:=f.positive
  path:=fun t _ => f.path t i
  initial:=by funext j c; exact congrFun (congrFun f.initial i) c
  final:=by funext j c; exact congrFun (congrFun f.final i) c
  main_fixed:=by funext j; exact congrFun f.main_fixed i
  aux_fixed:=by funext j q; exact congrFun (congrFun f.aux_fixed i) q
  raw_fixed:=by funext j q; exact congrFun (congrFun f.raw_fixed i) q
  queue_fixed:=by change cellQueue i u.pending=cellQueue i s.pending; rw [f.queue_fixed]
  continuous:=fun _ c => f.continuous i c
  integrable:=fun _ c => f.integrable i c
  mark_integrable:=fun _ p => f.mark_integrable i p
  integral_eq:=fun t ht _ c => f.integral_eq t ht i c
  guards:=fun t ht => ⟨fun _ => (f.guards t ht).1 i,fun _ p => (f.guards t ht).2 i p⟩
  raw_support:=fun _ p origin hr => f.raw_support i p origin hr
  pending_urgent:=by
    intro d hd
    obtain ⟨old,hold,heq⟩ := List.mem_filterMap.mp hd
    by_cases h : old.cell=i
    · simp only [Delivery.atCell,h,ite_true,Option.some.injEq] at heq
      subst d
      exact f.pending_urgent old hold
    · simp [Delivery.atCell,h] at heq

@[simp] theorem Flow.autonomousView_mark {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port) :
    (f.autonomousView i).ledger.mark 0 p=f.ledger.mark i p := rfl

/-- Endpoint transport retains the exact ledger and token history. -/
private theorem cast_view_target {θ : Fin 1 → Parameters} {s u v : Snapshot 1}
    (e : Execution θ (fun _ _ => []) s u) (h : u=v) :
    ∃ out : Execution θ (fun _ _ => []) s v,
      out.ledger.emissions=e.ledger.emissions ∧ out.deliveries=e.deliveries ∧
      ∀ p, out.ledger.mark 0 p=e.ledger.mark 0 p := by
  subst v
  exact ⟨e,rfl,rfl,fun _ => rfl⟩

private theorem jump_view_step {θ : Fin 1 → Parameters} {s u v : Snapshot 1}
    (j : Jump (fun _ _ => []) s u) (h : u=v) :
    ∃ out : Execution θ (fun _ _ => []) s v,
      out.ledger.emissions=j.ledger.emissions ∧ out.deliveries=j.deliveries ∧
      ∀ p, out.ledger.mark 0 p=0 := by
  obtain ⟨out,he,hd,hm⟩ := cast_view_target (.cons (.jump j) (.nil _)) h
  refine ⟨out,?_,?_,?_⟩
  · simpa only [Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,List.append_nil] using he
  · simpa only [Execution.deliveries,Move.deliveries,List.append_nil] using hd
  · intro p
    rw [hm]
    simp only [Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,j.mark_zero,add_zero]

private theorem skip_view_step {θ : Fin 1 → Parameters} {s v : Snapshot 1} (h : s=v) :
    ∃ out : Execution θ (fun _ _ => []) s v,
      out.ledger.emissions=[] ∧ out.deliveries=[] ∧ ∀ p, out.ledger.mark 0 p=0 := by
  obtain ⟨out,he,hd,hm⟩ := cast_view_target (.nil s) h
  exact ⟨out,he,hd,hm⟩

/-- Every selected operational jump remains an actual local jump. Other
cells' updates are skipped only when the exact projected state is unchanged. -/
theorem Jump.autonomous_cell_exists {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hNo : NoIncoming route i) (θ : Fin 1 → Parameters) :
    ∃ out : Execution θ (fun _ _ => []) (s.autonomousView i) (u.autonomousView i),
      out.ledger.emissions=cellEmissions i j.ledger.emissions ∧
      out.deliveries=cellQueue i j.deliveries ∧ ∀ p, out.ledger.mark 0 p=0 := by
  cases j with
  | fire k hm hq =>
    have hroute := hNo.cell_queue_empty k s.time
    by_cases hk : k=i
    · subst k
      let localJ := Jump.fire (route:=fun _ _ => []) (s.autonomousView i) 0 hm hq
      have target : ({setMain (s.autonomousView i) 0 .fast with
          pending:=(s.autonomousView i).pending++[]} : Snapshot 1)=
          ({setMain s i .fast with pending:=s.pending++route i s.time} : Snapshot n).autonomousView i := by
        apply view_ext
        · rfl
        · rfl
        · funext k
          have hk : k=(0:Fin 1) := Subsingleton.elim _ _
          subst k
          simp [Snapshot.autonomousView,setMain]
        · rfl
        · rfl
        · change cellQueue i s.pending++[]=cellQueue i (s.pending++route i s.time)
          rw [cellQueue_append,hroute,List.append_nil]
      obtain ⟨out,he,hd,hmark⟩ := jump_view_step (θ:=θ) localJ target
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions,Snapshot.autonomousView] using he
      · simpa [localJ,Jump.deliveries,cellQueue] using hd
    · have target : s.autonomousView i=
          ({setMain s k .fast with pending:=s.pending++route k s.time} : Snapshot n).autonomousView i := by
        apply view_ext
        · rfl
        · rfl
        · funext j
          simp [Snapshot.autonomousView,setMain,Ne.symm hk]
        · rfl
        · rfl
        · change cellQueue i s.pending=cellQueue i (s.pending++route k s.time)
          rw [cellQueue_append,hroute,List.append_nil]
      obtain ⟨out,he,hd,hmark⟩ := skip_view_step (θ:=θ) target
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions,hk] using he
      · simpa [Jump.deliveries,cellQueue] using hd
  | fastEnd k hm hq =>
    by_cases hk : k=i
    · subst k
      let localJ := Jump.fastEnd (route:=fun _ _ => []) (s.autonomousView i) 0 hm hq
      obtain ⟨out,he,hd,hmark⟩ := jump_view_step (θ:=θ) localJ
        (Snapshot.autonomousView_setMain_self s i .slow).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [localJ,Jump.deliveries,cellQueue] using hd
    · obtain ⟨out,he,hd,hmark⟩ := skip_view_step (θ:=θ)
        (Snapshot.autonomousView_setMain_other s i k .slow hk).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [Jump.deliveries,cellQueue] using hd
  | reopen k hm hq =>
    by_cases hk : k=i
    · subst k
      let localJ := Jump.reopen (route:=fun _ _ => []) (s.autonomousView i) 0 hm hq
      obtain ⟨out,he,hd,hmark⟩ := jump_view_step (θ:=θ) localJ
        (Snapshot.autonomousView_setMain_self s i .ready).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [localJ,Jump.deliveries,cellQueue] using hd
    · obtain ⟨out,he,hd,hmark⟩ := skip_view_step (θ:=θ)
        (Snapshot.autonomousView_setMain_other s i k .ready hk).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [Jump.deliveries,cellQueue] using hd
  | mark k p hm hq =>
    by_cases hk : k=i
    · subst k
      let localJ := Jump.mark (route:=fun _ _ => []) (s.autonomousView i) 0 p hm hq
      obtain ⟨out,he,hd,hmark⟩ := jump_view_step (θ:=θ) localJ
        (Snapshot.autonomousView_setAux_self s i p .mark).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [localJ,Jump.deliveries,cellQueue] using hd
    · obtain ⟨out,he,hd,hmark⟩ := skip_view_step (θ:=θ)
        (Snapshot.autonomousView_setAux_other s i k p .mark hk).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [Jump.deliveries,cellQueue] using hd
  | silent k p hm hq =>
    by_cases hk : k=i
    · subst k
      let localJ := Jump.silent (route:=fun _ _ => []) (s.autonomousView i) 0 p hm hq
      obtain ⟨out,he,hd,hmark⟩ := jump_view_step (θ:=θ) localJ
        (Snapshot.autonomousView_setAux_self s i p .silent).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [localJ,Jump.deliveries,cellQueue] using hd
    · obtain ⟨out,he,hd,hmark⟩ := skip_view_step (θ:=θ)
        (Snapshot.autonomousView_setAux_other s i k p .silent hk).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [Jump.deliveries,cellQueue] using hd
  | error k p hm hq =>
    by_cases hk : k=i
    · subst k
      let localJ := Jump.error (route:=fun _ _ => []) (s.autonomousView i) 0 p hm hq
      obtain ⟨out,he,hd,hmark⟩ := jump_view_step (θ:=θ) localJ
        (Snapshot.autonomousView_setAux_self s i p .error).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [localJ,Jump.deliveries,cellQueue] using hd
    · obtain ⟨out,he,hd,hmark⟩ := skip_view_step (θ:=θ)
        (Snapshot.autonomousView_setAux_other s i k p .error hk).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [Jump.deliveries,cellQueue] using hd
  | auxReady k p hm hq =>
    by_cases hk : k=i
    · subst k
      let localJ := Jump.auxReady (route:=fun _ _ => []) (s.autonomousView i) 0 p hm hq
      obtain ⟨out,he,hd,hmark⟩ := jump_view_step (θ:=θ) localJ
        (Snapshot.autonomousView_setAux_self s i p .ready).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [localJ,Jump.deliveries,cellQueue] using hd
    · obtain ⟨out,he,hd,hmark⟩ := skip_view_step (θ:=θ)
        (Snapshot.autonomousView_setAux_other s i k p .ready hk).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [Jump.deliveries,cellQueue] using hd
  | arrive d before after hqueue hdue hfree =>
    by_cases hd : d.cell=i
    · let localD : Delivery 1 := ⟨0,d.port,d.due⟩
      have hQ : (s.autonomousView i).pending=cellQueue i before++localD::cellQueue i after := by
        change cellQueue i s.pending=_
        rw [hqueue]
        simp [cellQueue,Delivery.atCell,hd,localD,List.filterMap_append]
      have hF : (s.autonomousView i).raw 0 d.port=none := by
        change s.raw i d.port=none
        rw [←hd]
        exact hfree
      let localJ := Jump.arrive (route:=fun _ _ => []) (s.autonomousView i) localD
        (cellQueue i before) (cellQueue i after) hQ hdue hF
      have target : ({setRaw (s.autonomousView i) 0 d.port (some s.time) with
          pending:=cellQueue i before++cellQueue i after} : Snapshot 1)=
          ({setRaw s d.cell d.port (some s.time) with pending:=before++after} : Snapshot n).autonomousView i := by
        apply view_ext
        · rfl
        · rfl
        · rfl
        · rfl
        · funext j q
          have hj : j=(0:Fin 1) := Subsingleton.elim _ _
          subst j
          simp [Snapshot.autonomousView,setRaw,hd]
        · exact (cellQueue_append i before after).symm
      obtain ⟨out,he,hdel,hmark⟩ := jump_view_step (θ:=θ) localJ target
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [localJ,Jump.deliveries,cellQueue,Delivery.atCell,hd,localD] using hdel
    · have target : s.autonomousView i=
          ({setRaw s d.cell d.port (some s.time) with pending:=before++after} : Snapshot n).autonomousView i := by
        apply view_ext
        · rfl
        · rfl
        · rfl
        · rfl
        · funext k q
          simp [Snapshot.autonomousView,setRaw,Ne.symm hd]
        · change cellQueue i s.pending=cellQueue i (before++after)
          rw [hqueue]
          simp [cellQueue,Delivery.atCell,hd,List.filterMap_append]
      obtain ⟨out,he,hdel,hmark⟩ := skip_view_step (θ:=θ) target
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [Jump.deliveries,cellQueue,Delivery.atCell,hd] using hdel
  | rawEnd k p origin hr ht =>
    by_cases hk : k=i
    · subst k
      let localJ := Jump.rawEnd (route:=fun _ _ => []) (s.autonomousView i) 0 p origin hr ht
      obtain ⟨out,he,hd,hmark⟩ := jump_view_step (θ:=θ) localJ
        (Snapshot.autonomousView_setRaw_self s i p none).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [localJ,Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [localJ,Jump.deliveries,cellQueue] using hd
    · obtain ⟨out,he,hd,hmark⟩ := skip_view_step (θ:=θ)
        (Snapshot.autonomousView_setRaw_other s i k p none hk).symm
      refine ⟨out,?_,?_,hmark⟩
      · simpa [Jump.ledger,Ledger.zero,cellEmissions] using he
      · simpa [Jump.deliveries,cellQueue] using hd

private theorem autonomous_execution_exists {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hNo : NoIncoming route i) :
    ∃ out : Execution (fun _ : Fin 1 => θ i) (fun _ _ => []) (s.autonomousView i) (u.autonomousView i),
      out.ledger.emissions=cellEmissions i e.ledger.emissions ∧
      out.deliveries=cellQueue i e.deliveries ∧
      ∀ p, out.ledger.mark 0 p=e.ledger.mark i p := by
  induction e with
  | nil s => exact ⟨.nil _,rfl,rfl,fun _ => rfl⟩
  | @cons s v u move rest ih =>
    obtain ⟨tail,heT,hdT,hmT⟩ := ih
    cases move with
    | flow f =>
      let head : Execution (fun _ : Fin 1 => θ i) (fun _ _ => []) (s.autonomousView i) (v.autonomousView i) :=
        .cons (.flow (f.autonomousView i)) (.nil _)
      let out := head.append tail
      refine ⟨out,?_,?_,?_⟩
      · simpa only [out,head,Execution.emissions_append,Execution.ledger,Move.ledger,
          Flow.ledger,Ledger.add,Ledger.zero,List.nil_append,List.append_nil,cellEmissions] using heT
      · simpa only [out,head,Execution.deliveries_append,Execution.deliveries,Move.deliveries,
          List.nil_append] using hdT
      · intro p
        rw [Execution.mark_append,hmT]
        simp only [head,Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,add_zero,Flow.autonomousView_mark]
    | jump j =>
      obtain ⟨head,heH,hdH,hmH⟩ := j.autonomous_cell_exists i hNo (fun _ => θ i)
      let out := head.append tail
      refine ⟨out,?_,?_,?_⟩
      · change (head.append tail).ledger.emissions=cellEmissions i (j.ledger.emissions++rest.ledger.emissions)
        rw [Execution.emissions_append,heH,heT,cellEmissions_append]
      · change (head.append tail).deliveries=cellQueue i (j.deliveries++rest.deliveries)
        rw [Execution.deliveries_append,hdH,hdT,cellQueue_append]
      · intro p
        change (head.append tail).ledger.mark 0 p=j.ledger.mark i p+rest.ledger.mark i p
        rw [Execution.mark_append,hmH,hmT,j.mark_zero,zero_add]

private theorem selected_emission_times {n} (i : Fin n) (events : List (Fin n×ℝ)) :
    ((cellEmissions i events).filter (fun ev => ev.1=0)).map Prod.snd=
      (events.filter (fun ev => ev.1=i)).map Prod.snd := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    rcases event with ⟨j,time⟩
    by_cases h : j=i
    · subst j
      simpa [cellEmissions] using congrArg (List.cons time) ih
    · simpa [cellEmissions,h] using ih

/-- The local operational trace and its exact selected physical observations. -/
structure AutonomousCellProjection {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  execution : Execution (fun _ : Fin 1 => θ i) (fun _ _ => []) (s.autonomousView i) (u.autonomousView i)
  emissions : execution.ledger.emissions=cellEmissions i e.ledger.emissions
  deliveries : execution.deliveries=cellQueue i e.deliveries
  mark : ∀ p, execution.ledger.mark 0 p=e.ledger.mark i p
  error : ∀ p, execution.ledger.error 0 p=e.ledger.error i p
  recovery : execution.ledger.recovery 0=e.ledger.recovery i
  emission_times : execution.emissionTimes 0=e.emissionTimes i

/-- No incoming routed contact is sufficient. External source occurrences
remain in the projected pending queue and are consumed by actual local jumps. -/
theorem Execution.autonomous_cell_exists {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hNo : NoIncoming route i) : Nonempty (AutonomousCellProjection e i) := by
  obtain ⟨out,he,hd,hm⟩ := autonomous_execution_exists e i hNo
  refine ⟨{
    execution:=out,emissions:=he,deliveries:=hd,mark:=hm,error:=?_,recovery:=?_,emission_times:=?_
  }⟩
  · intro p
    have hLocal := out.gain_balance 0 p
    have hGlobal := e.gain_balance i p
    change u.x i (.z p)=s.x i (.z p)+out.ledger.error 0 p at hLocal
    linarith
  · have hLocal := out.recovery_balance 0
    have hGlobal := e.recovery_balance i
    change u.x i .b=s.x i .b+out.ledger.recovery 0 at hLocal
    linarith
  · rw [Execution.emissionTimes,he]
    exact selected_emission_times i e.ledger.emissions

theorem Snapshot.autonomousView_physical {n θ s} (hf : @PhysicalInvariant n θ s) (i : Fin n) :
    PhysicalInvariant (fun _ : Fin 1 => θ i) (s.autonomousView i) :=
  ⟨fun _ => hf.region i,fun _ p => hf.gain_cap i p,fun _ => hf.recovery_cap i,fun _ => hf.reserve i⟩

theorem Snapshot.autonomousView_raw_valid {n s} (hv : @RawValid n s) (i : Fin n) :
    RawValid (s.autonomousView i) := fun _ p origin h => hv i p origin h

theorem autonomous_physical_box {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) :
    PhysicalBox (fun _ : Fin 1 => θ i) ε := ⟨hb.1,fun _ p => hb.2 i p⟩

end KernelR.Hybrid
