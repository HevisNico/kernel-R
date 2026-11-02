import KernelR.Hybrid

/-! Observational equality for operational traces. Simultaneous independent
FIREs can permute the operational queue, so structural snapshot equality is
not the correct comparison relation. This file treats that presentation
choice without imposing an event priority. -/
namespace KernelR.Hybrid

/-- Equal physical snapshots, up to the list presentation of pending tokens. -/
structure Snapshot.ObservationalEq {n : ℕ} (s t : Snapshot n) : Prop where
  time : s.time=t.time
  values : s.x=t.x
  main : s.main=t.main
  aux : s.aux=t.aux
  raw : s.raw=t.raw
  pending : s.pending.Perm t.pending

namespace Snapshot.ObservationalEq

protected theorem refl {n} (s : Snapshot n) : s.ObservationalEq s :=
  ⟨rfl,rfl,rfl,rfl,rfl,List.Perm.refl _⟩

protected theorem symm {n} {s t : Snapshot n} (h : s.ObservationalEq t) :
    t.ObservationalEq s :=
  ⟨h.time.symm,h.values.symm,h.main.symm,h.aux.symm,h.raw.symm,h.pending.symm⟩

protected theorem trans {n} {s t u : Snapshot n} (h : s.ObservationalEq t)
    (g : t.ObservationalEq u) : s.ObservationalEq u :=
  ⟨h.time.trans g.time,h.values.trans g.values,h.main.trans g.main,
    h.aux.trans g.aux,h.raw.trans g.raw,h.pending.trans g.pending⟩

end Snapshot.ObservationalEq

/-- A pending-token permutation preserves the existence of each enabled jump,
with the same physical result and only a permuted residual queue. -/
theorem Jump.transport_observational {n route s u t} (j : @Jump n route s u)
    (h : s.ObservationalEq t) :
    ∃ v, Nonempty (Jump route t v) ∧ u.ObservationalEq v := by
  rcases s with ⟨st,sx,sm,sa,sr,sq⟩
  rcases t with ⟨tt,tx,tm,ta,tr,tq⟩
  rcases h with ⟨ht,hx,hm,ha,hr,hq⟩
  dsimp at ht hx hm ha hr hq
  subst tt; subst tx; subst tm; subst ta; subst tr
  cases j with
  | fire i mode guard =>
    refine ⟨_,⟨Jump.fire _ i mode guard⟩,?_⟩
    exact ⟨rfl,rfl,rfl,rfl,rfl,hq.append_right _⟩
  | fastEnd i mode guard =>
    exact ⟨_,⟨Jump.fastEnd _ i mode guard⟩,rfl,rfl,rfl,rfl,rfl,hq⟩
  | reopen i mode guard =>
    exact ⟨_,⟨Jump.reopen _ i mode guard⟩,rfl,rfl,rfl,rfl,rfl,hq⟩
  | mark i p mode guard =>
    exact ⟨_,⟨Jump.mark _ i p mode guard⟩,rfl,rfl,rfl,rfl,rfl,hq⟩
  | silent i p mode guard =>
    exact ⟨_,⟨Jump.silent _ i p mode guard⟩,rfl,rfl,rfl,rfl,rfl,hq⟩
  | error i p mode guard =>
    exact ⟨_,⟨Jump.error _ i p mode guard⟩,rfl,rfl,rfl,rfl,rfl,hq⟩
  | auxReady i p mode guard =>
    exact ⟨_,⟨Jump.auxReady _ i p mode guard⟩,rfl,rfl,rfl,rfl,rfl,hq⟩
  | rawEnd i p origin active due =>
    exact ⟨_,⟨Jump.rawEnd _ i p origin active due⟩,rfl,rfl,rfl,rfl,rfl,hq⟩
  | arrive d before after queue due free =>
    change sq=before++d::after at queue
    have hd : d∈tq := hq.mem_iff.mp (by rw [queue]; simp)
    obtain ⟨before',after',hqueue'⟩ := List.mem_iff_append.mp hd
    refine ⟨_,⟨Jump.arrive _ d before' after' hqueue' due free⟩,rfl,rfl,rfl,rfl,rfl,?_⟩
    rw [queue,hqueue'] at hq
    exact List.Perm.cons_inv ((List.perm_middle).symm.trans (hq.trans List.perm_middle))

/-- Saturation is invariant under an observational change of presentation. -/
theorem observational_no_jump {n route} {s t : Snapshot n}
    (h : s.ObservationalEq t) (hs : ∀ v, IsEmpty (Jump route s v)) :
    ∀ v, IsEmpty (Jump route t v) := by
  intro v
  exact ⟨fun j => by
    obtain ⟨w,⟨j'⟩,_⟩ := j.transport_observational h.symm
    exact (hs w).false j'⟩

end KernelR.Hybrid
