import KernelR.HybridSnapshotObservational
import KernelR.HybridRawJumpConfluence
import KernelR.HybridNeutralFutureFrame

namespace KernelR.Hybrid

/-- A jump not changing a main-mode address remains legal after an unrelated
main-mode write. This includes auxiliary and RAW events at the same cell. -/
theorem Jump.setMain_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (mode : MainMode) (h : u.main i=s.main i) :
    Nonempty (Jump route (setMain s i mode) (setMain u i mode)) := by
  cases j with
  | fire k hm hg =>
    have hk : k≠i := by intro he; subst k; simp [setMain,hm] at h
    have hm' : (setMain s i mode).main k=.ready := by simpa [setMain,hk] using hm
    have j := Jump.fire (route:=route) (setMain s i mode) k hm' hg
    exact ⟨by simpa only [setMain,Function.update_comm hk] using j⟩
  | fastEnd k hm hg =>
    have hk : k≠i := by intro he; subst k; simp [setMain,hm] at h
    have hm' : (setMain s i mode).main k=.fast := by simpa [setMain,hk] using hm
    have j := Jump.fastEnd (route:=route) (setMain s i mode) k hm' hg
    exact ⟨by simpa only [setMain,Function.update_comm hk] using j⟩
  | reopen k hm hg =>
    have hk : k≠i := by intro he; subst k; simp [setMain,hm] at h
    have hm' : (setMain s i mode).main k=.slow := by simpa [setMain,hk] using hm
    have j := Jump.reopen (route:=route) (setMain s i mode) k hm' hg
    exact ⟨by simpa only [setMain,Function.update_comm hk] using j⟩
  | mark k p hm hg => exact ⟨Jump.mark _ k p hm hg⟩
  | silent k p hm hg => exact ⟨Jump.silent _ k p hm hg⟩
  | error k p hm hg => exact ⟨Jump.error _ k p hm hg⟩
  | auxReady k p hm hg => exact ⟨Jump.auxReady _ k p hm hg⟩
  | rawEnd k p origin active due => exact ⟨Jump.rawEnd _ k p origin active due⟩
  | arrive d before after queue due free => exact ⟨Jump.arrive _ d before after queue due free⟩

private theorem setAux_comm {n} (s : Snapshot n) (i k : Fin n) (p q : Port)
    (v w : AuxMode) (h : i≠k ∨ p≠q) :
    setAux (setAux s i p v) k q w=setAux (setAux s k q w) i p v := by
  by_cases hik : i=k
  · subst k
    have hpq : p≠q := h.resolve_left (not_not_intro rfl)
    dsimp only [setAux]
    simp only [Function.update_self,Function.update_idem]
    congr 1
    exact congrArg (Function.update s.aux i) (Function.update_comm hpq v w (s.aux i))
  · dsimp only [setAux]
    simp only [Function.update_of_ne hik,Function.update_of_ne (Ne.symm hik)]
    congr 1
    exact Function.update_comm hik _ _ s.aux

private theorem setAux_other {n} (s : Snapshot n) (i k : Fin n) (p q : Port)
    (v : AuxMode) (h : i≠k ∨ p≠q) :
    (setAux s i p v).aux k q=s.aux k q := by
  by_cases hik : i=k
  · subst k
    have hpq : p≠q := h.resolve_left (not_not_intro rfl)
    simp [setAux,Ne.symm hpq]
  · simp [setAux,Ne.symm hik]

/-- A jump not changing an auxiliary-mode address remains legal after an
unrelated auxiliary-mode write. -/
theorem Jump.setAux_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (h : u.aux i p=s.aux i p) :
    Nonempty (Jump route (setAux s i p mode) (setAux u i p mode)) := by
  cases j with
  | fire k hm hg => exact ⟨Jump.fire _ k hm hg⟩
  | fastEnd k hm hg => exact ⟨Jump.fastEnd _ k hm hg⟩
  | reopen k hm hg => exact ⟨Jump.reopen _ k hm hg⟩
  | mark k q hm hg =>
    have hk : i≠k ∨ p≠q := by
      by_cases hik : i=k
      · right; intro hpq; subst k; subst q; simp [setAux,hm] at h
      · exact Or.inl hik
    have hm' : (setAux s i p mode).aux k q=.ready := by
      rw [setAux_other s i k p q mode hk]; exact hm
    have j := Jump.mark (route:=route) (setAux s i p mode) k q hm' hg
    exact ⟨by simpa only [setAux_comm s i k p q mode .mark hk] using j⟩
  | silent k q hm hg =>
    have hk : i≠k ∨ p≠q := by
      by_cases hik : i=k
      · right; intro hpq; subst k; subst q; simp [setAux,hm] at h
      · exact Or.inl hik
    have hm' : (setAux s i p mode).aux k q=.mark := by
      rw [setAux_other s i k p q mode hk]; exact hm
    have j := Jump.silent (route:=route) (setAux s i p mode) k q hm' hg
    exact ⟨by simpa only [setAux_comm s i k p q mode .silent hk] using j⟩
  | error k q hm hg =>
    have hk : i≠k ∨ p≠q := by
      by_cases hik : i=k
      · right; intro hpq; subst k; subst q; simp [setAux,hm] at h
      · exact Or.inl hik
    have hm' : (setAux s i p mode).aux k q=.silent := by
      rw [setAux_other s i k p q mode hk]; exact hm
    have j := Jump.error (route:=route) (setAux s i p mode) k q hm' hg
    exact ⟨by simpa only [setAux_comm s i k p q mode .error hk] using j⟩
  | auxReady k q hm hg =>
    have hk : i≠k ∨ p≠q := by
      by_cases hik : i=k
      · right; intro hpq; subst k; subst q; simp [setAux,hm] at h
      · exact Or.inl hik
    have hm' : (setAux s i p mode).aux k q=.error := by
      rw [setAux_other s i k p q mode hk]; exact hm
    have j := Jump.auxReady (route:=route) (setAux s i p mode) k q hm' hg
    exact ⟨by simpa only [setAux_comm s i k p q mode .ready hk] using j⟩
  | rawEnd k q origin active due => exact ⟨Jump.rawEnd _ k q origin active due⟩
  | arrive d before after queue due free => exact ⟨Jump.arrive _ d before after queue due free⟩


/-- Framing already queued tokens through one jump preserves its physical
result up to pending presentation, including an actual FIRE append. -/
theorem Jump.appendPending_observational {n route s u} (j : @Jump n route s u)
    (Q : List (Delivery n)) :
    ∃ v, Nonempty (Jump route (appendPending s Q) v) ∧
      v.ObservationalEq (appendPending u Q) := by
  by_cases he : j.ledger.emissions=[]
  · obtain ⟨j',_,_⟩ := j.appendFuture_neutral he Q
    exact ⟨_,⟨j'⟩,.refl _⟩
  · cases j with
    | fire i hm hg =>
      refine ⟨_,⟨Jump.fire (route:=route) (appendPending s Q) i hm hg⟩,
        rfl,rfl,rfl,rfl,rfl,?_⟩
      change ((s.pending++Q)++route i s.time).Perm ((s.pending++route i s.time)++Q)
      simpa only [List.append_assoc] using (List.perm_append_comm (l₁:=Q) (l₂:=route i s.time)).append_left s.pending
    | _ => simp [Jump.ledger,Ledger.zero] at he

/-- A FIRE commutes observationally with any simultaneous jump which leaves
its main-mode address alone. Its real issued tokens are retained. -/
theorem Jump.fire_diamond_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hm : s.main i=.ready) (hg : s.x i .q=1)
    (h : u.main i=s.main i) :
    JumpDiamond route ({setMain s i .fast with pending:=s.pending++route i s.time}) u := by
  obtain ⟨lift⟩ := j.setMain_of_unchanged i .fast h
  obtain ⟨v,⟨lift'⟩,hv⟩ := lift.appendPending_observational (route i s.time)
  have hm' : u.main i=.ready := h.trans hm
  have hg' : u.x i .q=1 := by simpa only [j.physical_continuous] using hg
  refine Or.inr ⟨v,_,⟨lift'⟩,⟨Jump.fire (route:=route) u i hm' hg'⟩,?_⟩
  simpa only [appendPending,setMain,j.time_unchanged] using hv

/-- The FAST exit commutes with an unrelated simultaneous jump. -/
theorem Jump.fastEnd_diamond_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hm : s.main i=.fast) (hg : s.x i .q=1/4)
    (h : u.main i=s.main i) : JumpDiamond route (setMain s i .slow) u := by
  obtain ⟨lift⟩ := j.setMain_of_unchanged i .slow h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨Jump.fastEnd (route:=route) u i (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

/-- The SLOW reopening commutes with an unrelated simultaneous jump. -/
theorem Jump.reopen_diamond_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hm : s.main i=.slow) (hg : s.x i .q=1/10)
    (h : u.main i=s.main i) : JumpDiamond route (setMain s i .ready) u := by
  obtain ⟨lift⟩ := j.setMain_of_unchanged i .ready h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨Jump.reopen (route:=route) u i (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

/-- The auxiliary READY-to-MARK transition commutes with a jump leaving its
auxiliary-mode address alone, including a simultaneous main FIRE. -/
theorem Jump.mark_diamond_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (hm : s.aux i p=.ready) (hg : s.x i (.m p)=1)
    (h : u.aux i p=s.aux i p) : JumpDiamond route (setAux s i p .mark) u := by
  obtain ⟨lift⟩ := j.setAux_of_unchanged i p .mark h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨Jump.mark (route:=route) u i p (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

theorem Jump.silent_diamond_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (hm : s.aux i p=.mark) (hg : s.x i (.m p)=4/5)
    (h : u.aux i p=s.aux i p) : JumpDiamond route (setAux s i p .silent) u := by
  obtain ⟨lift⟩ := j.setAux_of_unchanged i p .silent h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨Jump.silent (route:=route) u i p (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

theorem Jump.error_diamond_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (hm : s.aux i p=.silent) (hg : s.x i (.m p)=1/10)
    (h : u.aux i p=s.aux i p) : JumpDiamond route (setAux s i p .error) u := by
  obtain ⟨lift⟩ := j.setAux_of_unchanged i p .error h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨Jump.error (route:=route) u i p (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

theorem Jump.auxReady_diamond_of_unchanged {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (hm : s.aux i p=.error) (hg : s.x i (.m p)=1/40)
    (h : u.aux i p=s.aux i p) : JumpDiamond route (setAux s i p .ready) u := by
  obtain ⟨lift⟩ := j.setAux_of_unchanged i p .ready h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨Jump.auxReady (route:=route) u i p (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

end KernelR.Hybrid
