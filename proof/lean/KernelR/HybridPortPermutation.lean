import KernelR.HybridPhysicalInvariant
import KernelR.HybridInputs
import KernelR.HybridPulseSection
import KernelR.HybridSilentReturn
import KernelR.HybridArrivals

/-! Port relabeling transports whole isolated physical executions. New port p
reads old port σ p; an old queued token therefore moves to σ.symm p. All main
coordinates, clocks, FIRE dates and actual energy paths remain unchanged. -/
namespace KernelR.Hybrid
open Set MeasureTheory

@[simp] def Coord.permutePorts (σ : Equiv.Perm Port) : Coord → Coord
  | .q => .q
  | .m p => .m (σ p)
  | .z p => .z (σ p)
  | .b => .b
  | .energy => .energy

def Values.permutePorts {n} (x : Values n) (σ : Equiv.Perm Port) : Values n :=
  fun i c => x i (c.permutePorts σ)

def Parameters.permutePorts (θ : Parameters) (σ : Equiv.Perm Port) : Parameters where
  cap p := θ.cap (σ p)
  lm p := θ.lm (σ p)
  ls p := θ.ls (σ p)
  le p := θ.le (σ p)
  inputGain p := θ.inputGain (σ p)

def permuteParameters {n} (θ : Fin n → Parameters) (σ : Equiv.Perm Port) : Fin n → Parameters :=
  fun i => (θ i).permutePorts σ

def Delivery.permutePorts {n} (d : Delivery n) (σ : Equiv.Perm Port) : Delivery n :=
  ⟨d.cell,σ.symm d.port,d.due⟩

def Snapshot.permutePorts {n} (s : Snapshot n) (σ : Equiv.Perm Port) : Snapshot n where
  time := s.time
  x := s.x.permutePorts σ
  main := s.main
  aux i p := s.aux i (σ p)
  raw i p := s.raw i (σ p)
  pending := s.pending.map (fun d => d.permutePorts σ)

@[simp] theorem Snapshot.permutePorts_time {n} (s : Snapshot n) (σ : Equiv.Perm Port) :
    (s.permutePorts σ).time=s.time := rfl
@[simp] theorem Snapshot.permutePorts_main {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) :
    (s.permutePorts σ).main i=s.main i := rfl
@[simp] theorem Snapshot.permutePorts_q {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) :
    (s.permutePorts σ).x i .q=s.x i .q := rfl
@[simp] theorem Snapshot.permutePorts_b {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) :
    (s.permutePorts σ).x i .b=s.x i .b := rfl
@[simp] theorem Snapshot.permutePorts_energy {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) :
    (s.permutePorts σ).x i .energy=s.x i .energy := rfl
@[simp] theorem Snapshot.permutePorts_m {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    (s.permutePorts σ).x i (.m p)=s.x i (.m (σ p)) := rfl
@[simp] theorem Snapshot.permutePorts_z {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    (s.permutePorts σ).x i (.z p)=s.x i (.z (σ p)) := rfl
@[simp] theorem Snapshot.permutePorts_aux {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    (s.permutePorts σ).aux i p=s.aux i (σ p) := rfl
@[simp] theorem Snapshot.permutePorts_raw {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    (s.permutePorts σ).raw i p=s.raw i (σ p) := rfl

@[simp] theorem Coord.permutePorts_inverse (σ : Equiv.Perm Port) (c : Coord) :
    (c.permutePorts σ.symm).permutePorts σ = c := by cases c <;> simp

@[simp] theorem Values.permutePorts_inverse {n} (x : Values n) (σ : Equiv.Perm Port) :
    (x.permutePorts σ).permutePorts σ.symm = x := by
  funext i c
  cases c <;> simp [Values.permutePorts]

@[simp] theorem Delivery.permutePorts_inverse {n} (d : Delivery n) (σ : Equiv.Perm Port) :
    (d.permutePorts σ).permutePorts σ.symm = d := by
  cases d
  simp [Delivery.permutePorts]

private theorem port_snapshot_ext {n} {s u : Snapshot n}
    (ht : s.time=u.time) (hx : s.x=u.x) (hm : s.main=u.main)
    (ha : s.aux=u.aux) (hr : s.raw=u.raw) (hq : s.pending=u.pending) : s=u := by
  cases s; cases u; simp_all only

@[simp] theorem Snapshot.permutePorts_inverse {n} (s : Snapshot n) (σ : Equiv.Perm Port) :
    (s.permutePorts σ).permutePorts σ.symm = s := by
  apply port_snapshot_ext
  · rfl
  · exact Values.permutePorts_inverse s.x σ
  · rfl
  · funext i p; simp [Snapshot.permutePorts]
  · funext i p; simp [Snapshot.permutePorts]
  · simp [Snapshot.permutePorts,List.map_map,Function.comp_def]

@[simp] theorem Parameters.permutePorts_inverse (θ : Parameters) (σ : Equiv.Perm Port) :
    (θ.permutePorts σ).permutePorts σ.symm = θ := by
  cases θ
  simp [Parameters.permutePorts]

@[simp] theorem permuteParameters_inverse {n} (θ : Fin n → Parameters) (σ : Equiv.Perm Port) :
    permuteParameters (permuteParameters θ σ) σ.symm = θ := by
  funext i
  exact Parameters.permutePorts_inverse (θ i) σ

@[simp] theorem current_permutePorts {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) (p : Port) (t : ℝ) :
    current (s.permutePorts σ) i p t = current s i (σ p) t := rfl

@[simp] theorem errorAct_permutePorts {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    errorAct (permuteParameters θ σ) (s.permutePorts σ) (x.permutePorts σ) i p =
      errorAct θ s x i (σ p) := rfl

@[simp] theorem markAct_permutePorts {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    markAct (permuteParameters θ σ) (s.permutePorts σ) (x.permutePorts σ) i p =
      markAct θ s x i (σ p) := rfl

@[simp] theorem auxDrain_permutePorts (θ : Parameters) (mode : AuxMode)
    (σ : Equiv.Perm Port) (p : Port) (m : ℝ) :
    auxDrain (θ.permutePorts σ) mode p m = auxDrain θ mode (σ p) m := by
  cases mode <;> rfl

@[simp] theorem drive_permutePorts {n} (s : Snapshot n) (x : Values n)
    (σ : Equiv.Perm Port) (i : Fin n) (t : ℝ) :
    drive (s.permutePorts σ) (x.permutePorts σ) i t = drive s x i t := by
  change (∑ p : Port,Real.exp (x i (.z (σ p))) * current s i (σ p) t) = _
  exact Equiv.sum_comp σ (fun p => Real.exp (x i (.z p)) * current s i p t)

@[simp] theorem markSum_permutePorts {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (σ : Equiv.Perm Port) (i : Fin n) :
    (∑ p : Port,markAct (permuteParameters θ σ) (s.permutePorts σ) (x.permutePorts σ) i p) =
      ∑ p : Port,markAct θ s x i p := by
  simp only [markAct_permutePorts]
  exact Equiv.sum_comp σ (fun p => markAct θ s x i p)

@[simp] theorem errorSum_permutePorts {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (σ : Equiv.Perm Port) (i : Fin n) :
    (∑ p : Port,errorAct (permuteParameters θ σ) (s.permutePorts σ) (x.permutePorts σ) i p) =
      ∑ p : Port,errorAct θ s x i p := by
  simp only [errorAct_permutePorts]
  exact Equiv.sum_comp σ (fun p => errorAct θ s x i p)

@[simp] theorem auxWork_permutePorts {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (σ : Equiv.Perm Port) (i : Fin n) (t : ℝ) :
    (∑ p : Port,if (s.permutePorts σ).aux i p = .ready then
      ((permuteParameters θ σ) i).inputGain p * current (s.permutePorts σ) i p t
      else auxDrain ((permuteParameters θ σ) i) ((s.permutePorts σ).aux i p) p ((x.permutePorts σ) i (.m p))) =
    ∑ p : Port,if s.aux i p = .ready then (θ i).inputGain p * current s i p t
      else auxDrain (θ i) (s.aux i p) p (x i (.m p)) := by
  change (∑ p : Port,if s.aux i (σ p) = .ready then (θ i).inputGain (σ p) * current s i (σ p) t
    else auxDrain (θ i) (s.aux i (σ p)) (σ p) (x i (.m (σ p)))) = _
  exact Equiv.sum_comp σ (fun p => if s.aux i p = .ready then (θ i).inputGain p * current s i p t
    else auxDrain (θ i) (s.aux i p) p (x i (.m p)))

@[simp] theorem work_permutePorts {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (σ : Equiv.Perm Port) (i : Fin n) (t : ℝ) :
    work (permuteParameters θ σ) (s.permutePorts σ) (x.permutePorts σ) i t = work θ s x i t := by
  unfold work
  rw [auxWork_permutePorts,errorSum_permutePorts,markSum_permutePorts]
  cases h : s.main i <;>
    simp only [Snapshot.permutePorts_main,h,drive_permutePorts,Values.permutePorts,Coord.permutePorts]

/-- Includes the actual work/energy equation, not only threshold coordinates. -/
theorem field_permutePorts {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (x : Values n) (σ : Equiv.Perm Port) (t : ℝ) (i : Fin n) (c : Coord) :
    field (permuteParameters θ σ) (s.permutePorts σ) (x.permutePorts σ) t i c =
      field θ s x t i (c.permutePorts σ) := by
  cases c with
  | q => cases h : s.main i <;>
      simp only [field,Snapshot.permutePorts_main,h,Coord.permutePorts,drive_permutePorts,Values.permutePorts]
  | m p =>
      simp only [field,Coord.permutePorts,Snapshot.permutePorts_aux,Values.permutePorts,
        current_permutePorts]
      rfl
  | z p => exact errorAct_permutePorts θ s x σ i p
  | b => exact markSum_permutePorts θ s x σ i
  | energy => simp only [field,work_permutePorts,Values.permutePorts,Coord.permutePorts]

/-- Reuse the exact old path, with ports relabeled coordinate by coordinate. -/
noncomputable def Flow.permutePorts {n θ s u} (f : @Flow n θ s u) (σ : Equiv.Perm Port) :
    Flow (permuteParameters θ σ) (s.permutePorts σ) (u.permutePorts σ) where
  positive := f.positive
  path t := (f.path t).permutePorts σ
  initial := by change (f.path s.time).permutePorts σ = s.x.permutePorts σ; rw [f.initial]
  final := by change (f.path u.time).permutePorts σ = u.x.permutePorts σ; rw [f.final]
  main_fixed := f.main_fixed
  aux_fixed := by funext i p; exact congrFun (congrFun f.aux_fixed i) (σ p)
  raw_fixed := by funext i p; exact congrFun (congrFun f.raw_fixed i) (σ p)
  queue_fixed := by change u.pending.map _ = s.pending.map _; rw [f.queue_fixed]
  continuous := fun i c => f.continuous i (c.permutePorts σ)
  integrable := by intro i c; simpa only [field_permutePorts,Snapshot.permutePorts_time] using f.integrable i (c.permutePorts σ)
  mark_integrable := fun i p => f.mark_integrable i (σ p)
  integral_eq := by
    intro t ht i c
    simp only [field_permutePorts,Snapshot.permutePorts_time]
    change f.path t i (c.permutePorts σ) = s.x i (c.permutePorts σ) +
      ∫ v in s.time..t,field θ s (f.path v) v i (c.permutePorts σ)
    exact f.integral_eq t ht i (c.permutePorts σ)
  guards := fun t ht => ⟨(f.guards t ht).1,fun i p => (f.guards t ht).2 i (σ p)⟩
  raw_support := fun i p origin hr => f.raw_support i (σ p) origin hr
  pending_urgent := by
    intro d hd
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hd
    exact f.pending_urgent old hold

@[simp] theorem Flow.permutePorts_energy {n θ s u} (f : @Flow n θ s u)
    (σ : Equiv.Perm Port) (t : ℝ) (i : Fin n) :
    (f.permutePorts σ).path t i .energy = f.path t i .energy := rfl

@[simp] theorem Snapshot.permutePorts_pending {n} (s : Snapshot n) (Q : List (Delivery n))
    (σ : Equiv.Perm Port) :
    ({s with pending := Q} : Snapshot n).permutePorts σ =
      {s.permutePorts σ with pending := Q.map (fun d => d.permutePorts σ)} := rfl

@[simp] theorem Snapshot.permutePorts_setMain {n} (s : Snapshot n) (i : Fin n) (mode : MainMode)
    (σ : Equiv.Perm Port) :
    (setMain s i mode).permutePorts σ = setMain (s.permutePorts σ) i mode := by
  apply port_snapshot_ext <;> rfl

@[simp] theorem Snapshot.permutePorts_setAux {n} (s : Snapshot n) (i : Fin n) (p : Port)
    (mode : AuxMode) (σ : Equiv.Perm Port) :
    (setAux s i p mode).permutePorts σ = setAux (s.permutePorts σ) i (σ.symm p) mode := by
  apply port_snapshot_ext <;> try rfl
  funext j q
  by_cases hj : j=i <;> simp [Snapshot.permutePorts,setAux,Function.update_apply,hj,σ.eq_symm_apply]

@[simp] theorem Snapshot.permutePorts_setRaw {n} (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (σ : Equiv.Perm Port) :
    (setRaw s i p origin).permutePorts σ = setRaw (s.permutePorts σ) i (σ.symm p) origin := by
  apply port_snapshot_ext <;> try rfl
  funext j q
  by_cases hj : j=i <;> simp [Snapshot.permutePorts,setRaw,Function.update_apply,hj,σ.eq_symm_apply]

private noncomputable def jump_port_target {n s u v}
    (j : @Jump n (fun _ _ => []) s u) (h : u=v) : Jump (fun _ _ => []) s v := h ▸ j

private theorem jump_port_target_ledger {n s u v}
    (j : @Jump n (fun _ _ => []) s u) (h : u=v) : (jump_port_target j h).ledger=j.ledger := by
  subst v; rfl

private theorem jump_port_target_deliveries {n s u v}
    (j : @Jump n (fun _ _ => []) s u) (h : u=v) : (jump_port_target j h).deliveries=j.deliveries := by
  subst v; rfl

/-- Each physical jump remains a jump, including real arrivals and RAW expiry. -/
noncomputable def Jump.permutePorts {n s u} (j : @Jump n (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) : Jump (fun _ _ => []) (s.permutePorts σ) (u.permutePorts σ) := by
  cases j with
  | fire i hm hq =>
    apply jump_port_target (Jump.fire (route:=fun _ _ => []) (s.permutePorts σ) i hm hq)
    simp only [Snapshot.permutePorts_pending,Snapshot.permutePorts_setMain,List.map_append,List.map_nil]
    rfl
  | fastEnd i hm hq =>
    exact jump_port_target (Jump.fastEnd (s.permutePorts σ) i hm hq) (Snapshot.permutePorts_setMain s i .slow σ).symm
  | reopen i hm hq =>
    exact jump_port_target (Jump.reopen (s.permutePorts σ) i hm hq) (Snapshot.permutePorts_setMain s i .ready σ).symm
  | mark i p hm hx =>
    have hm' : (s.permutePorts σ).aux i (σ.symm p)=.ready := by simpa [Snapshot.permutePorts] using hm
    have hx' : (s.permutePorts σ).x i (.m (σ.symm p))=1 := by simpa [Snapshot.permutePorts,Values.permutePorts] using hx
    exact jump_port_target (Jump.mark (s.permutePorts σ) i (σ.symm p) hm' hx')
      (Snapshot.permutePorts_setAux s i p .mark σ).symm
  | silent i p hm hx =>
    have hm' : (s.permutePorts σ).aux i (σ.symm p)=.mark := by simpa [Snapshot.permutePorts] using hm
    have hx' : (s.permutePorts σ).x i (.m (σ.symm p))=4/5 := by simpa [Snapshot.permutePorts,Values.permutePorts] using hx
    exact jump_port_target (Jump.silent (s.permutePorts σ) i (σ.symm p) hm' hx')
      (Snapshot.permutePorts_setAux s i p .silent σ).symm
  | error i p hm hx =>
    have hm' : (s.permutePorts σ).aux i (σ.symm p)=.silent := by simpa [Snapshot.permutePorts] using hm
    have hx' : (s.permutePorts σ).x i (.m (σ.symm p))=1/10 := by simpa [Snapshot.permutePorts,Values.permutePorts] using hx
    exact jump_port_target (Jump.error (s.permutePorts σ) i (σ.symm p) hm' hx')
      (Snapshot.permutePorts_setAux s i p .error σ).symm
  | auxReady i p hm hx =>
    have hm' : (s.permutePorts σ).aux i (σ.symm p)=.error := by simpa [Snapshot.permutePorts] using hm
    have hx' : (s.permutePorts σ).x i (.m (σ.symm p))=1/40 := by simpa [Snapshot.permutePorts,Values.permutePorts] using hx
    exact jump_port_target (Jump.auxReady (s.permutePorts σ) i (σ.symm p) hm' hx')
      (Snapshot.permutePorts_setAux s i p .ready σ).symm
  | arrive d before after hqueue hdue hfree =>
    let token := d.permutePorts σ
    have hqueue' : (s.permutePorts σ).pending = before.map (fun d => d.permutePorts σ) ++
        token :: after.map (fun d => d.permutePorts σ) := by
      change s.pending.map _ = _
      rw [hqueue,List.map_append,List.map_cons]
    have hfree' : (s.permutePorts σ).raw token.cell token.port=none := by
      simpa [Snapshot.permutePorts,token,Delivery.permutePorts] using hfree
    apply jump_port_target (Jump.arrive (s.permutePorts σ) token
      (before.map (fun d => d.permutePorts σ)) (after.map (fun d => d.permutePorts σ)) hqueue' hdue hfree')
    simp only [Snapshot.permutePorts_pending,Snapshot.permutePorts_setRaw,List.map_append]
    rfl
  | rawEnd i p origin hr hdue =>
    have hr' : (s.permutePorts σ).raw i (σ.symm p)=some origin := by simpa [Snapshot.permutePorts] using hr
    exact jump_port_target (Jump.rawEnd (s.permutePorts σ) i (σ.symm p) origin hr' hdue)
      (Snapshot.permutePorts_setRaw s i p none σ).symm

noncomputable def Ledger.permutePorts {n} (L : Ledger n) (σ : Equiv.Perm Port) : Ledger n where
  error i p := L.error i (σ p)
  mark i p := L.mark i (σ p)
  recovery := L.recovery
  emissions := L.emissions
  issued := L.issued
  delivered := L.delivered

@[simp] theorem Ledger.permutePorts_zero {n} (σ : Equiv.Perm Port) :
    (Ledger.zero : Ledger n).permutePorts σ = Ledger.zero := rfl

@[simp] theorem Ledger.permutePorts_add {n} (L R : Ledger n) (σ : Equiv.Perm Port) :
    (L.add R).permutePorts σ = (L.permutePorts σ).add (R.permutePorts σ) := rfl

private theorem port_ledger_ext {n} {L R : Ledger n}
    (he : L.error=R.error) (hm : L.mark=R.mark) (hr : L.recovery=R.recovery)
    (hf : L.emissions=R.emissions) (hi : L.issued=R.issued) (hd : L.delivered=R.delivered) : L=R := by
  cases L; cases R; simp_all only

theorem Flow.permutePorts_ledger {n θ s u} (f : @Flow n θ s u) (σ : Equiv.Perm Port) :
    (f.permutePorts σ).ledger = f.ledger.permutePorts σ := by
  apply port_ledger_ext
  · funext i p
    simp only [Flow.ledger,Flow.permutePorts,Ledger.permutePorts,errorAct_permutePorts,Snapshot.permutePorts_time]
  · funext i p
    simp only [Flow.ledger,Flow.permutePorts,Ledger.permutePorts,markAct_permutePorts,Snapshot.permutePorts_time]
  · funext i
    change (∫ t in s.time..u.time,
      ∑ p : Port,markAct (permuteParameters θ σ) (s.permutePorts σ) ((f.path t).permutePorts σ) i p) = _
    simp only [markSum_permutePorts]
    rfl
  · rfl
  · rfl
  · rfl

theorem Jump.permutePorts_ledger {n s u} (j : @Jump n (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) : (j.permutePorts σ).ledger = j.ledger.permutePorts σ := by
  cases j <;> dsimp only [Jump.permutePorts]
  all_goals rw [jump_port_target_ledger]
  all_goals simp [Jump.ledger,Ledger.permutePorts,Ledger.zero,Snapshot.permutePorts]

theorem Jump.permutePorts_deliveries {n s u} (j : @Jump n (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) :
    (j.permutePorts σ).deliveries = j.deliveries.map (fun d => d.permutePorts σ) := by
  cases j <;> dsimp only [Jump.permutePorts]
  all_goals rw [jump_port_target_deliveries]
  all_goals simp [Jump.deliveries]

noncomputable def Move.permutePorts {n θ s u} (move : @Move n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) :
    Move (permuteParameters θ σ) (fun _ _ => []) (s.permutePorts σ) (u.permutePorts σ) :=
  match move with
  | .flow f => .flow (f.permutePorts σ)
  | .jump j => .jump (j.permutePorts σ)

theorem Move.permutePorts_ledger {n θ s u} (move : @Move n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) : (move.permutePorts σ).ledger = move.ledger.permutePorts σ := by
  cases move with
  | flow f => exact f.permutePorts_ledger σ
  | jump j => exact j.permutePorts_ledger σ

theorem Move.permutePorts_deliveries {n θ s u} (move : @Move n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) :
    (move.permutePorts σ).deliveries = move.deliveries.map (fun d => d.permutePorts σ) := by
  cases move with
  | flow f => rfl
  | jump j => exact j.permutePorts_deliveries σ

noncomputable def Execution.permutePorts {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u) (σ : Equiv.Perm Port) :
    Execution (permuteParameters θ σ) (fun _ _ => []) (s.permutePorts σ) (u.permutePorts σ) :=
  match e with
  | .nil s => .nil (s.permutePorts σ)
  | .cons move rest => .cons (move.permutePorts σ) (rest.permutePorts σ)

theorem Execution.permutePorts_ledger {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) : (e.permutePorts σ).ledger=e.ledger.permutePorts σ := by
  induction e with
  | nil s => rfl
  | cons move rest ih =>
    simp only [Execution.permutePorts,Execution.ledger,move.permutePorts_ledger,ih,Ledger.permutePorts_add]

theorem Execution.permutePorts_error {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    (e.permutePorts σ).ledger.error i p=e.ledger.error i (σ p) :=
  congrArg (fun L : Ledger n => L.error i p) (e.permutePorts_ledger σ)

theorem Execution.permutePorts_mark {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    (e.permutePorts σ).ledger.mark i p=e.ledger.mark i (σ p) :=
  congrArg (fun L : Ledger n => L.mark i p) (e.permutePorts_ledger σ)

theorem Execution.permutePorts_recovery {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) (i : Fin n) :
    (e.permutePorts σ).ledger.recovery i=e.ledger.recovery i :=
  by simpa only [Ledger.permutePorts] using congrArg (fun L : Ledger n => L.recovery i) (e.permutePorts_ledger σ)

theorem Execution.permutePorts_emissions {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) : (e.permutePorts σ).ledger.emissions=e.ledger.emissions :=
  by simpa only [Ledger.permutePorts] using congrArg Ledger.emissions (e.permutePorts_ledger σ)

theorem Execution.permutePorts_emissionTimes {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) (i : Fin n) : (e.permutePorts σ).emissionTimes i=e.emissionTimes i := by
  simp only [Execution.emissionTimes,e.permutePorts_emissions]

theorem Execution.permutePorts_deliveries {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) :
    (e.permutePorts σ).deliveries=e.deliveries.map (fun d => d.permutePorts σ) := by
  induction e with
  | nil s => rfl
  | cons move rest ih =>
    simp only [Execution.permutePorts,Execution.deliveries,move.permutePorts_deliveries,ih,List.map_append]

theorem CompleteThrough.permutePorts {n θ s u T} {e : @Execution n θ (fun _ _ => []) s u}
    (h : CompleteThrough e T) (σ : Equiv.Perm Port) : CompleteThrough (e.permutePorts σ) T := by
  refine ⟨h.1,?_,?_⟩
  · intro v
    constructor
    intro j
    have old := j.permutePorts σ.symm
    rw [Snapshot.permutePorts_inverse] at old
    exact (h.2.1 (v.permutePorts σ.symm)).false old
  · intro d hd
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hd
    exact h.2.2 old hold

/-- Fabrication parameters remain independent; every new port simply uses
its corresponding old fabrication interval. -/
theorem PhysicalBox.permutePorts {n θ ε} (hb : @PhysicalBox n θ ε) (σ : Equiv.Perm Port) :
    PhysicalBox (permuteParameters θ σ) ε := ⟨hb.1,fun i p => hb.2 i (σ p)⟩

theorem PhysicalInvariant.permutePorts {n θ s} (hf : @PhysicalInvariant n θ s) (σ : Equiv.Perm Port) :
    PhysicalInvariant (permuteParameters θ σ) (s.permutePorts σ) := by
  refine ⟨?_,fun i p => hf.gain_cap i (σ p),hf.recovery_cap,hf.reserve⟩
  intro i
  exact ⟨(hf.region i).1,(hf.region i).2.1,fun p => (hf.region i).2.2 (σ p)⟩

theorem RawValid.permutePorts {n s} (hv : @RawValid n s) (σ : Equiv.Perm Port) :
    RawValid (s.permutePorts σ) := fun i p origin hr => hv i (σ p) origin hr

theorem ReadyCoordinates.permutePorts {n s i} (hs : @ReadyCoordinates n s i) (σ : Equiv.Perm Port) :
    ReadyCoordinates (s.permutePorts σ) i :=
  ⟨hs.ready,hs.charge,fun p => hs.auxiliary (σ p)⟩

theorem PreparedSection.permutePorts {n s i} (hs : @PreparedSection n s i) (σ : Equiv.Perm Port) :
    PreparedSection (s.permutePorts σ) i :=
  ⟨hs.ready,hs.charge,hs.recovery,fun p => hs.auxiliary (σ p)⟩

theorem BirthState.permutePorts {n s} (hs : @BirthState n s) (σ : Equiv.Perm Port)
    (hnominal : ∀ p,nominalGain (σ p)=nominalGain p) : BirthState (s.permutePorts σ) := by
  refine ⟨hs.1,fun i p => hs.2.1 i (σ p),?_⟩
  intro i
  have h := hs.2.2 i
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
  intro p
  have hp := h.2.2.2.2 (σ p)
  simpa only [hnominal p,Snapshot.permutePorts_z,Snapshot.permutePorts_m,Snapshot.permutePorts_aux] using hp

/-- The two low nominal ports have identical birth bands; port one stays fixed. -/
def swapLowPorts : Equiv.Perm Port := Equiv.swap 0 2

@[simp] theorem swapLowPorts_zero : swapLowPorts 0=2 := by simp [swapLowPorts]
@[simp] theorem swapLowPorts_two : swapLowPorts 2=0 := by simp [swapLowPorts]
@[simp] theorem swapLowPorts_one : swapLowPorts 1=1 := by norm_num [swapLowPorts,Equiv.swap_apply_def]
@[simp] theorem swapLowPorts_symm : swapLowPorts.symm=swapLowPorts := Equiv.symm_swap _ _

theorem swapLowPorts_nominal (p : Port) : nominalGain (swapLowPorts p)=nominalGain p := by
  fin_cases p <;> norm_num [nominalGain]

theorem BirthState.swapLowPorts {n s} (hs : @BirthState n s) : BirthState (s.permutePorts swapLowPorts) :=
  hs.permutePorts KernelR.Hybrid.swapLowPorts swapLowPorts_nominal

@[simp] theorem sourceTrain_permutePorts {n} (i : Fin n) (p : Port) (S gap : ℝ) (count : ℕ)
    (σ : Equiv.Perm Port) :
    (sourceTrain i p S gap count).map (fun d => d.permutePorts σ) = sourceTrain i (σ.symm p) S gap count := by
  simp only [sourceTrain,List.map_ofFn]
  rfl

end KernelR.Hybrid
