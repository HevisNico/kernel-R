import KernelR.HybridParameterPhysical
import KernelR.HybridObservationalTransport

/-! Cuts and queue transport preserve the actual flow path, realized
guards, and FIRE labels. -/
namespace KernelR.Hybrid
open Set MeasureTheory

def ParameterMove.emissions {n θ route s u} : @ParameterMove n θ route s u → List (Fin n × ℝ)
  | .flow _ => []
  | .jump j => j.emissions

@[simp] theorem ParameterExecution.emissions_cons {n θ route s u v}
    (m : @ParameterMove n θ route s u) (e : ParameterExecution θ route u v) :
    (ParameterExecution.cons m e).emissions = m.emissions ++ e.emissions := by
  cases m <;> rfl

@[simp] def ParameterExecution.moveCount {n θ route s u} :
    @ParameterExecution n θ route s u → ℕ
  | .nil _ => 0
  | .cons _ rest => rest.moveCount + 1

/-- Re-present an actual flow with a permuted initial pending queue. -/
noncomputable def ParameterFlow.rebase_observational {n θ s u t} (f : @ParameterFlow n θ s u)
    (h : s.ObservationalEq t) : ParameterFlow θ t {u with pending:=t.pending} where
  positive := by simpa only [←h.time] using f.positive
  path := f.path
  initial := by simpa only [←h.time] using f.initial.trans h.values
  final := f.final
  main_fixed := f.main_fixed.trans h.main
  aux_fixed := f.aux_fixed.trans h.aux
  raw_fixed := f.raw_fixed.trans h.raw
  queue_fixed := rfl
  continuous := by simpa only [←h.time] using f.continuous
  integrable := by simpa only [←h.time,←h.field] using f.integrable
  mark_integrable := by
    simpa only [←h.time,markAct,←h.main,←h.aux] using f.mark_integrable
  integral_eq := by
    simpa only [←h.time,←h.values,←h.field] using f.integral_eq
  guards := by
    simpa only [←h.time,ThresholdGuards,←h.main,←h.aux] using f.guards
  raw_support := by
    simpa only [←h.raw,←h.time] using f.raw_support
  pending_urgent := by
    intro d hd
    exact f.pending_urgent d (h.pending.mem_iff.mpr hd)

/-- The re-presented flow ends in the same physical state. -/
theorem ParameterFlow.rebase_observational_final {n θ s u t} (f : @ParameterFlow n θ s u)
    (h : s.ObservationalEq t) : u.ObservationalEq {u with pending:=t.pending} := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (List.Perm.of_eq f.queue_fixed).trans h.pending

/-- Queue re-presentation preserves the actual jump constructor and FIRE label. -/
theorem ParameterJump.transport_observational_emissions {n θ route s u t} (j : @ParameterJump n θ route s u)
    (h : s.ObservationalEq t) :
    ∃ v, ∃ j' : ParameterJump θ route t v,
      u.ObservationalEq v ∧ j'.emissions=j.emissions := by
  rcases s with ⟨st,sx,sm,sa,sr,sq⟩
  rcases t with ⟨tt,tx,tm,ta,tr,tq⟩
  rcases h with ⟨ht,hx,hm,ha,hr,hq⟩
  dsimp at ht hx hm ha hr hq
  subst tt; subst tx; subst tm; subst ta; subst tr
  cases j with
  | fire i mode guard =>
    exact ⟨_,ParameterJump.fire _ i mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq.append_right _⟩,rfl⟩
  | fastEnd i mode guard =>
    exact ⟨_,ParameterJump.fastEnd _ i mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | reopen i mode guard =>
    exact ⟨_,ParameterJump.reopen _ i mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | mark i p mode guard =>
    exact ⟨_,ParameterJump.mark _ i p mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | silent i p mode guard =>
    exact ⟨_,ParameterJump.silent _ i p mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | error i p mode guard =>
    exact ⟨_,ParameterJump.error _ i p mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | auxReady i p mode guard =>
    exact ⟨_,ParameterJump.auxReady _ i p mode guard,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | rawEnd i p origin active due =>
    exact ⟨_,ParameterJump.rawEnd _ i p origin active due,⟨rfl,rfl,rfl,rfl,rfl,hq⟩,rfl⟩
  | arrive d before after queue due free =>
    change sq=before++d::after at queue
    have hd : d∈tq := hq.mem_iff.mp (by rw [queue]; simp)
    obtain ⟨before',after',hqueue'⟩ := List.mem_iff_append.mp hd
    refine ⟨_,ParameterJump.arrive _ d before' after' hqueue' due free,⟨rfl,rfl,rfl,rfl,rfl,?_⟩,rfl⟩
    rw [queue,hqueue'] at hq
    exact List.Perm.cons_inv ((List.perm_middle).symm.trans (hq.trans List.perm_middle))

/-- Every move transports without changing its FIRE labels. -/
theorem ParameterMove.transport_observational_emissions {n θ route s u t} (m : @ParameterMove n θ route s u)
    (h : s.ObservationalEq t) :
    ∃ v, ∃ m' : ParameterMove θ route t v,
      u.ObservationalEq v ∧ m'.emissions=m.emissions := by
  cases m with
  | flow f =>
    exact ⟨_,.flow (f.rebase_observational h),f.rebase_observational_final h,rfl⟩
  | jump j =>
    obtain ⟨v,j',hv,he⟩ := j.transport_observational_emissions h
    exact ⟨v,.jump j',hv,he⟩

/-- A complete finite trace can be re-presented from an observationally equal
snapshot, preserving the exact global FIRE list, hence each cell's list. -/
theorem ParameterExecution.transport_observational_emissions_count {n θ route s u t}
    (e : @ParameterExecution n θ route s u) (h : s.ObservationalEq t) :
    ∃ v, ∃ e' : ParameterExecution θ route t v,
      u.ObservationalEq v ∧ e'.emissions=e.emissions ∧
      e'.moveCount=e.moveCount := by
  induction e generalizing t with
  | nil s => exact ⟨t,.nil t,h,rfl,rfl⟩
  | cons move rest ih =>
    obtain ⟨mid,move',hm,hem⟩ := move.transport_observational_emissions h
    obtain ⟨v,rest',hv,her,hcount⟩ := ih hm
    refine ⟨v,.cons move' rest',hv,?_,?_⟩
    · simp only [ParameterExecution.emissions_cons,hem,her]
    · simp only [ParameterExecution.moveCount,hcount]

theorem parameterCompleteThrough_of_observational {n θ route s u t v T}
    (e : @ParameterExecution n θ route s u) (e' : ParameterExecution θ route t v)
    (h : u.ObservationalEq v) (hc : ParameterCompleteThrough e T) :
    ParameterCompleteThrough e' T := by
  refine ⟨h.time.symm.trans hc.1, ?_, fun d hd => hc.2.2 d (h.pending.mem_iff.mpr hd)⟩
  intro w
  constructor
  intro j
  obtain ⟨r, j', _, _⟩ := j.transport_observational_emissions h.symm
  exact (hc.2.1 r).false j'

theorem Snapshot.ObservationalEq.parameter_physical_invariant {n θ} {s t : Snapshot n}
    (h : s.ObservationalEq t) (hs : ParameterPhysicalInvariant θ s) :
    ParameterPhysicalInvariant θ t := by
  rcases hs with ⟨hq,hm,hz,hb,he⟩
  exact ⟨by simpa only [←h.values] using hq,
    by simpa only [←h.values] using hm, by simpa only [←h.values] using hz,
    by simpa only [←h.values] using hb, by simpa only [←h.values] using he⟩

/-- The remaining part of an existing positive flow, using the same path. -/
noncomputable def ParameterFlow.suffix {n θ s u} (f : @ParameterFlow n θ s u) {t : ℝ}
    (hstart : s.time ≤ t) (hend : t < u.time) : ParameterFlow θ (f.at t) u where
  positive := hend
  path := f.path
  initial := rfl
  final := f.final
  main_fixed := f.main_fixed
  aux_fixed := f.aux_fixed
  raw_fixed := f.raw_fixed
  queue_fixed := f.queue_fixed
  continuous := fun i c => (f.continuous i c).mono (Icc_subset_Icc hstart le_rfl)
  integrable := fun i c => (f.integrable i c).mono_set (by
    change uIcc t u.time ⊆ uIcc s.time u.time
    rw [uIcc_of_le hend.le,uIcc_of_le f.positive.le]
    exact Icc_subset_Icc hstart le_rfl)
  mark_integrable := fun i p => (f.mark_integrable i p).mono_set (by
    change uIcc t u.time ⊆ uIcc s.time u.time
    rw [uIcc_of_le hend.le,uIcc_of_le f.positive.le]
    exact Icc_subset_Icc hstart le_rfl)
  integral_eq := by
    intro v hv i c
    have hv₀ : v ∈ Icc s.time u.time := ⟨hstart.trans hv.1,hv.2⟩
    have ht₀ : t ∈ Icc s.time u.time := ⟨hstart,hend.le⟩
    have hi₁ : IntervalIntegrable (fun v => field θ s (f.path v) v i c) volume s.time t :=
      (f.integrable i c).mono_set (by
        rw [uIcc_of_le hstart,uIcc_of_le f.positive.le]
        exact Icc_subset_Icc le_rfl hend.le)
    have hi₂ : IntervalIntegrable (fun v => field θ s (f.path v) v i c) volume t v :=
      (f.integrable i c).mono_set (by
        rw [uIcc_of_le (show t ≤ v from hv.1),uIcc_of_le f.positive.le]
        exact Icc_subset_Icc hstart hv.2)
    have ha := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
    have ht := f.integral_eq t ht₀ i c
    have he := f.integral_eq v hv₀ i c
    change f.path v i c = f.path t i c + ∫ w in t..v, field θ s (f.path w) w i c
    linarith
  guards := fun v hv => f.guards v ⟨hstart.trans hv.1,hv.2⟩
  raw_support := fun i p origin hr =>
    ⟨(f.raw_support i p origin hr).1.trans hstart,(f.raw_support i p origin hr).2⟩
  pending_urgent := f.pending_urgent

theorem ParameterJump.emission_time {n θ route s u} (j : @ParameterJump n θ route s u)
    (event : Fin n × ℝ) (he : event ∈ j.emissions) : event.2 = s.time := by
  cases j <;> simp_all [ParameterJump.emissions]

theorem ParameterMove.emission_time {n θ route s u} (m : @ParameterMove n θ route s u)
    (event : Fin n × ℝ) (he : event ∈ m.emissions) : event.2 = s.time := by
  cases m with
  | flow f => simp [ParameterMove.emissions] at he
  | jump j => exact j.emission_time event he

theorem ParameterMove.time_monotone {n θ route s u} (m : @ParameterMove n θ route s u) :
    s.time ≤ u.time := by
  cases m with
  | flow f => exact f.positive.le
  | jump j => exact j.time_unchanged.ge

theorem ParameterExecution.time_monotone {n θ route s u}
    (e : @ParameterExecution n θ route s u) : s.time ≤ u.time := by
  induction e with
  | nil => exact le_rfl
  | cons m rest ih => exact m.time_monotone.trans ih

theorem ParameterExecution.emission_time_lower {n θ route s u}
    (e : @ParameterExecution n θ route s u) (event : Fin n × ℝ) (he : event ∈ e.emissions) :
    s.time ≤ event.2 := by
  induction e with
  | nil => simp [ParameterExecution.emissions] at he
  | cons step rest ih =>
    rw [ParameterExecution.emissions_cons, List.mem_append] at he
    rcases he with he | he
    · rw [step.emission_time event he]
    · exact step.time_monotone.trans (ih he)

theorem ParameterExecution.emissions_chronological {n θ route s u}
    (e : @ParameterExecution n θ route s u) :
    e.emissions.Pairwise (fun x y => x.2 ≤ y.2) := by
  induction e with
  | nil => simp [ParameterExecution.emissions]
  | cons step rest ih =>
    have hs : step.emissions.Pairwise (fun x y => x.2 ≤ y.2) := by
      cases step with
      | flow f => simp [ParameterMove.emissions]
      | jump j => cases j <;> simp [ParameterMove.emissions, ParameterJump.emissions]
    rw [ParameterExecution.emissions_cons]
    refine List.pairwise_append.mpr ⟨hs, ih, ?_⟩
    intro x hx y hy
    rw [step.emission_time x hx]
    exact step.time_monotone.trans (rest.emission_time_lower y hy)

theorem ParameterExecution.emissionTimes_chronological {n θ route s u}
    (e : @ParameterExecution n θ route s u) (i : Fin n) :
    (e.emissionTimes i).Pairwise (· ≤ ·) :=
  List.pairwise_map.mpr (e.emissions_chronological.filter _)

end KernelR.Hybrid
