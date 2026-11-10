import KernelR.HybridParameterExecution
import KernelR.HybridRawJumpConfluence
import KernelR.HybridNeutralFutureFrame

/-! Local observational confluence for fixed realized thresholds.
The proof uses the same raw-address, queue, and mode-update commutations
as the nominal kernel. -/
namespace KernelR.Hybrid

theorem ParameterJump.physical_continuous {n θ route s u}
    (j : @ParameterJump n θ route s u) : u.x = s.x := by cases j <;> rfl

theorem ParameterJump.time_unchanged {n θ route s u}
    (j : @ParameterJump n θ route s u) : u.time = s.time := by cases j <;> rfl

def ParameterJumpDiamond {n} (θ : Fin n → Parameters) (route : Router n) (u v : Snapshot n) : Prop :=
  u.ObservationalEq v ∨ ∃ u' v', Nonempty (ParameterJump θ route u u') ∧
    Nonempty (ParameterJump θ route v v') ∧ u'.ObservationalEq v'

theorem parameter_rawEnd_rawEnd_diamond {n θ route} (s : Snapshot n)
    (i j : Fin n) (p q : Port) (o r : ℝ)
    (hi : s.raw i p=some o) (hj : s.raw j q=some r)
    (hti : s.time=o+1) (htj : s.time=r+1) :
    ParameterJumpDiamond θ route (setRaw s i p none) (setRaw s j q none) := by
  by_cases hc : i=j
  · subst j
    by_cases hp : p=q
    · subst q
      exact Or.inl (.refl _)
    · refine Or.inr ⟨_,_,⟨ParameterJump.rawEnd _ i q r ?_ htj⟩,
        ⟨ParameterJump.rawEnd _ i p o ?_ hti⟩,?_⟩
      · simpa only [setRaw_other s i i p q none (Or.inr hp)] using hj
      · simpa only [setRaw_other s i i q p none (Or.inr (Ne.symm hp))] using hi
      · rw [setRaw_commute s i i p q none none (Or.inr hp)]
        exact .refl _
  · refine Or.inr ⟨_,_,⟨ParameterJump.rawEnd _ j q r ?_ htj⟩,
      ⟨ParameterJump.rawEnd _ i p o ?_ hti⟩,?_⟩
    · simpa only [setRaw_other s i j p q none (Or.inl hc)] using hj
    · simpa only [setRaw_other s j i q p none (Or.inl (Ne.symm hc))] using hi
    · rw [setRaw_commute s i j p q none none (Or.inl hc)]
      exact .refl _

/-- An enabled delivery and an enabled expiry cannot share a RAW address.
Consequently their residual physical state is independent of jump order. -/
theorem parameter_arrive_rawEnd_diamond {n θ route} (s : Snapshot n) (d : Delivery n)
    (before after : List (Delivery n)) (hq : s.pending=before++d::after)
    (hd : d.due=s.time) (hf : s.raw d.cell d.port=none)
    (i : Fin n) (p : Port) (o : ℝ) (ha : s.raw i p=some o)
    (ht : s.time=o+1) :
    ParameterJumpDiamond θ route (s.afterArrival d before after) (setRaw s i p none) := by
  have hdiff : d.cell≠i ∨ d.port≠p := by
    by_cases hc : d.cell=i
    · right
      intro hp
      rw [hc,hp,ha] at hf
      contradiction
    · exact Or.inl hc
  refine Or.inr ⟨_,_,⟨ParameterJump.rawEnd _ i p o ?_ ht⟩,
    ⟨ParameterJump.arrive _ d before after hq hd ?_⟩,?_⟩
  · change (setRaw s d.cell d.port (some s.time)).raw i p=some o
    rw [setRaw_other s d.cell i d.port p (some s.time) hdiff]
    exact ha
  · rw [setRaw_other s i d.cell p d.port none (hdiff.elim
      (fun h => Or.inl (Ne.symm h)) (fun h => Or.inr (Ne.symm h)))]
    exact hf
  · refine ⟨rfl,rfl,rfl,rfl,?_,List.Perm.refl _⟩
    have h := congrArg Snapshot.raw (setRaw_commute s d.cell i d.port p
      (some s.time) none hdiff)
    exact h

/-- Two enabled deliveries either name the same due token (including duplicate
queue positions), or legally commute at independent RAW addresses. -/
theorem parameter_arrive_arrive_diamond {n θ route} (s : Snapshot n) (d e : Delivery n)
    (b₁ a₁ b₂ a₂ : List (Delivery n))
    (hq₁ : s.pending=b₁++d::a₁) (hq₂ : s.pending=b₂++e::a₂)
    (hd : d.due=s.time) (he : e.due=s.time)
    (hf₁ : s.raw d.cell d.port=none) (hf₂ : s.raw e.cell e.port=none) :
    ParameterJumpDiamond θ route (s.afterArrival d b₁ a₁) (s.afterArrival e b₂ a₂) := by
  have hA : s.pending.Perm (d::(b₁++a₁)) := by rw [hq₁]; exact List.perm_middle
  have hB : s.pending.Perm (e::(b₂++a₂)) := by rw [hq₂]; exact List.perm_middle
  by_cases hde : d=e
  · subst e
    exact Or.inl ⟨rfl,rfl,rfl,rfl,rfl,List.Perm.cons_inv (hA.symm.trans hB)⟩
  · have hdiff : d.cell≠e.cell ∨ d.port≠e.port := by
      by_cases hc : d.cell=e.cell
      · right
        intro hp
        exact hde (due_delivery_eq_of_address hd he hc hp)
      · exact Or.inl hc
    obtain ⟨ba,aa,bb,ab,hAA,hBB,hrest⟩ := queue_removal_diamond hA hB hde
    refine Or.inr ⟨_,_,⟨ParameterJump.arrive _ e ba aa hAA he ?_⟩,
      ⟨ParameterJump.arrive _ d bb ab hBB hd ?_⟩,?_⟩
    · change (setRaw s d.cell d.port (some s.time)).raw e.cell e.port=none
      rw [setRaw_other s d.cell e.cell d.port e.port (some s.time) hdiff]
      exact hf₂
    · change (setRaw s e.cell e.port (some s.time)).raw d.cell d.port=none
      rw [setRaw_other s e.cell d.cell e.port d.port (some s.time) (hdiff.elim
        (fun h => Or.inl (Ne.symm h)) (fun h => Or.inr (Ne.symm h)))]
      exact hf₁
    · refine ⟨rfl,rfl,rfl,rfl,?_,hrest⟩
      have h := congrArg Snapshot.raw (setRaw_commute s d.cell e.cell d.port e.port
        (some s.time) (some s.time) hdiff)
      simpa only [Snapshot.afterArrival,setRaw] using h



/-- A jump not changing a main-mode address remains legal after an unrelated
main-mode write. This includes auxiliary and RAW events at the same cell. -/
theorem ParameterJump.setMain_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (mode : MainMode) (h : u.main i=s.main i) :
    Nonempty (ParameterJump θ route (setMain s i mode) (setMain u i mode)) := by
  cases j with
  | fire k hm hg =>
    have hk : k≠i := by intro he; subst k; simp [setMain,hm] at h
    have hm' : (setMain s i mode).main k=.ready := by simpa [setMain,hk] using hm
    have j := ParameterJump.fire (route:=route) (setMain s i mode) k hm' hg
    exact ⟨by simpa only [setMain,Function.update_comm hk] using j⟩
  | fastEnd k hm hg =>
    have hk : k≠i := by intro he; subst k; simp [setMain,hm] at h
    have hm' : (setMain s i mode).main k=.fast := by simpa [setMain,hk] using hm
    have j := ParameterJump.fastEnd (route:=route) (setMain s i mode) k hm' hg
    exact ⟨by simpa only [setMain,Function.update_comm hk] using j⟩
  | reopen k hm hg =>
    have hk : k≠i := by intro he; subst k; simp [setMain,hm] at h
    have hm' : (setMain s i mode).main k=.slow := by simpa [setMain,hk] using hm
    have j := ParameterJump.reopen (route:=route) (setMain s i mode) k hm' hg
    exact ⟨by simpa only [setMain,Function.update_comm hk] using j⟩
  | mark k p hm hg => exact ⟨ParameterJump.mark _ k p hm hg⟩
  | silent k p hm hg => exact ⟨ParameterJump.silent _ k p hm hg⟩
  | error k p hm hg => exact ⟨ParameterJump.error _ k p hm hg⟩
  | auxReady k p hm hg => exact ⟨ParameterJump.auxReady _ k p hm hg⟩
  | rawEnd k p origin active due => exact ⟨ParameterJump.rawEnd _ k p origin active due⟩
  | arrive d before after queue due free => exact ⟨ParameterJump.arrive _ d before after queue due free⟩

private theorem parameter_setAux_comm {n} (s : Snapshot n) (i k : Fin n) (p q : Port)
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

private theorem parameter_setAux_other {n} (s : Snapshot n) (i k : Fin n) (p q : Port)
    (v : AuxMode) (h : i≠k ∨ p≠q) :
    (setAux s i p v).aux k q=s.aux k q := by
  by_cases hik : i=k
  · subst k
    have hpq : p≠q := h.resolve_left (not_not_intro rfl)
    simp [setAux,Ne.symm hpq]
  · simp [setAux,Ne.symm hik]

/-- A jump not changing an auxiliary-mode address remains legal after an
unrelated auxiliary-mode write. -/
theorem ParameterJump.setAux_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (h : u.aux i p=s.aux i p) :
    Nonempty (ParameterJump θ route (setAux s i p mode) (setAux u i p mode)) := by
  cases j with
  | fire k hm hg => exact ⟨ParameterJump.fire _ k hm hg⟩
  | fastEnd k hm hg => exact ⟨ParameterJump.fastEnd _ k hm hg⟩
  | reopen k hm hg => exact ⟨ParameterJump.reopen _ k hm hg⟩
  | mark k q hm hg =>
    have hk : i≠k ∨ p≠q := by
      by_cases hik : i=k
      · right; intro hpq; subst k; subst q; simp [setAux,hm] at h
      · exact Or.inl hik
    have hm' : (setAux s i p mode).aux k q=.ready := by
      rw [parameter_setAux_other s i k p q mode hk]; exact hm
    have j := ParameterJump.mark (route:=route) (setAux s i p mode) k q hm' hg
    exact ⟨by simpa only [parameter_setAux_comm s i k p q mode .mark hk] using j⟩
  | silent k q hm hg =>
    have hk : i≠k ∨ p≠q := by
      by_cases hik : i=k
      · right; intro hpq; subst k; subst q; simp [setAux,hm] at h
      · exact Or.inl hik
    have hm' : (setAux s i p mode).aux k q=.mark := by
      rw [parameter_setAux_other s i k p q mode hk]; exact hm
    have j := ParameterJump.silent (route:=route) (setAux s i p mode) k q hm' hg
    exact ⟨by simpa only [parameter_setAux_comm s i k p q mode .silent hk] using j⟩
  | error k q hm hg =>
    have hk : i≠k ∨ p≠q := by
      by_cases hik : i=k
      · right; intro hpq; subst k; subst q; simp [setAux,hm] at h
      · exact Or.inl hik
    have hm' : (setAux s i p mode).aux k q=.silent := by
      rw [parameter_setAux_other s i k p q mode hk]; exact hm
    have j := ParameterJump.error (route:=route) (setAux s i p mode) k q hm' hg
    exact ⟨by simpa only [parameter_setAux_comm s i k p q mode .error hk] using j⟩
  | auxReady k q hm hg =>
    have hk : i≠k ∨ p≠q := by
      by_cases hik : i=k
      · right; intro hpq; subst k; subst q; simp [setAux,hm] at h
      · exact Or.inl hik
    have hm' : (setAux s i p mode).aux k q=.error := by
      rw [parameter_setAux_other s i k p q mode hk]; exact hm
    have j := ParameterJump.auxReady (route:=route) (setAux s i p mode) k q hm' hg
    exact ⟨by simpa only [parameter_setAux_comm s i k p q mode .ready hk] using j⟩
  | rawEnd k q origin active due => exact ⟨ParameterJump.rawEnd _ k q origin active due⟩
  | arrive d before after queue due free => exact ⟨ParameterJump.arrive _ d before after queue due free⟩


/-- Framing already queued tokens through one jump preserves its physical
result up to pending presentation, including an actual FIRE append. -/
theorem ParameterJump.appendPending_observational {n θ route s u} (j : @ParameterJump n θ route s u)
    (Q : List (Delivery n)) :
    ∃ v, Nonempty (ParameterJump θ route (appendPending s Q) v) ∧
      v.ObservationalEq (appendPending u Q) := by
  cases j with
  | fire i hm hg =>
    refine ⟨_,⟨ParameterJump.fire (route:=route) (appendPending s Q) i hm hg⟩,
      rfl,rfl,rfl,rfl,rfl,?_⟩
    change ((s.pending++Q)++route i s.time).Perm ((s.pending++route i s.time)++Q)
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁:=Q) (l₂:=route i s.time)).append_left s.pending
  | fastEnd i hm hq => exact ⟨_, ⟨.fastEnd _ i hm hq⟩, .refl _⟩
  | reopen i hm hq => exact ⟨_, ⟨.reopen _ i hm hq⟩, .refl _⟩
  | mark i p hm hq => exact ⟨_, ⟨.mark _ i p hm hq⟩, .refl _⟩
  | silent i p hm hq => exact ⟨_, ⟨.silent _ i p hm hq⟩, .refl _⟩
  | error i p hm hq => exact ⟨_, ⟨.error _ i p hm hq⟩, .refl _⟩
  | auxReady i p hm hq => exact ⟨_, ⟨.auxReady _ i p hm hq⟩, .refl _⟩
  | rawEnd i p origin hr ht => exact ⟨_, ⟨.rawEnd _ i p origin hr ht⟩, .refl _⟩
  | arrive d before after hqueue hd hf =>
    have target : appendPending ({setRaw s d.cell d.port (some s.time) with pending := before ++ after} : Snapshot n) Q =
        {setRaw (appendPending s Q) d.cell d.port (some s.time) with pending := before ++ (after ++ Q)} := by
      simp only [appendPending,setRaw,List.append_assoc]
    rw [target]
    refine ⟨_,⟨.arrive _ d before (after ++ Q) ?_ hd hf⟩,.refl _⟩
    change s.pending ++ Q = before ++ d :: (after ++ Q)
    rw [hqueue,List.append_assoc,List.cons_append]

/-- A FIRE commutes observationally with any simultaneous jump which leaves
its main-mode address alone. Its real issued tokens are retained. -/
theorem ParameterJump.fire_diamond_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (hm : s.main i=.ready) (hg : s.x i .q=(θ i).thresholds.fire)
    (h : u.main i=s.main i) :
    ParameterJumpDiamond θ route ({setMain s i .fast with pending:=s.pending++route i s.time}) u := by
  obtain ⟨lift⟩ := j.setMain_of_unchanged i .fast h
  obtain ⟨v,⟨lift'⟩,hv⟩ := lift.appendPending_observational (route i s.time)
  have hm' : u.main i=.ready := h.trans hm
  have hg' : u.x i .q=(θ i).thresholds.fire := by simpa only [j.physical_continuous] using hg
  refine Or.inr ⟨v,_,⟨lift'⟩,⟨ParameterJump.fire (route:=route) u i hm' hg'⟩,?_⟩
  simpa only [appendPending,setMain,j.time_unchanged] using hv

/-- The FAST exit commutes with an unrelated simultaneous jump. -/
theorem ParameterJump.fastEnd_diamond_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (hm : s.main i=.fast) (hg : s.x i .q=(θ i).thresholds.fastEnd)
    (h : u.main i=s.main i) : ParameterJumpDiamond θ route (setMain s i .slow) u := by
  obtain ⟨lift⟩ := j.setMain_of_unchanged i .slow h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨ParameterJump.fastEnd (route:=route) u i (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

/-- The SLOW reopening commutes with an unrelated simultaneous jump. -/
theorem ParameterJump.reopen_diamond_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (hm : s.main i=.slow) (hg : s.x i .q=(θ i).thresholds.reopen)
    (h : u.main i=s.main i) : ParameterJumpDiamond θ route (setMain s i .ready) u := by
  obtain ⟨lift⟩ := j.setMain_of_unchanged i .ready h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨ParameterJump.reopen (route:=route) u i (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

/-- The auxiliary READY-to-MARK transition commutes with a jump leaving its
auxiliary-mode address alone, including a simultaneous main FIRE. -/
theorem ParameterJump.mark_diamond_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (hm : s.aux i p=.ready) (hg : s.x i (.m p)=(θ i).thresholds.mark p)
    (h : u.aux i p=s.aux i p) : ParameterJumpDiamond θ route (setAux s i p .mark) u := by
  obtain ⟨lift⟩ := j.setAux_of_unchanged i p .mark h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨ParameterJump.mark (route:=route) u i p (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

theorem ParameterJump.silent_diamond_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (hm : s.aux i p=.mark) (hg : s.x i (.m p)=(θ i).thresholds.silent p)
    (h : u.aux i p=s.aux i p) : ParameterJumpDiamond θ route (setAux s i p .silent) u := by
  obtain ⟨lift⟩ := j.setAux_of_unchanged i p .silent h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨ParameterJump.silent (route:=route) u i p (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

theorem ParameterJump.error_diamond_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (hm : s.aux i p=.silent) (hg : s.x i (.m p)=(θ i).thresholds.error p)
    (h : u.aux i p=s.aux i p) : ParameterJumpDiamond θ route (setAux s i p .error) u := by
  obtain ⟨lift⟩ := j.setAux_of_unchanged i p .error h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨ParameterJump.error (route:=route) u i p (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg

theorem ParameterJump.auxReady_diamond_of_unchanged {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (hm : s.aux i p=.error) (hg : s.x i (.m p)=(θ i).thresholds.auxReady p)
    (h : u.aux i p=s.aux i p) : ParameterJumpDiamond θ route (setAux s i p .ready) u := by
  obtain ⟨lift⟩ := j.setAux_of_unchanged i p .ready h
  refine Or.inr ⟨_,_,⟨lift⟩,⟨ParameterJump.auxReady (route:=route) u i p (h.trans hm) ?_⟩,.refl _⟩
  simpa only [j.physical_continuous] using hg



theorem ParameterJump.eq_fire_of_main_changed {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (hmode : s.main i=.ready) (hchange : u.main i≠s.main i) :
    u={ (setMain s i .fast) with pending:=s.pending++route i s.time } := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]

theorem ParameterJump.eq_fastEnd_of_main_changed {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (hmode : s.main i=.fast) (hchange : u.main i≠s.main i) :
    u=setMain s i .slow := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]

theorem ParameterJump.eq_reopen_of_main_changed {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (hmode : s.main i=.slow) (hchange : u.main i≠s.main i) :
    u=setMain s i .ready := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]

theorem ParameterJump.eq_mark_of_aux_changed {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (hmode : s.aux i p=.ready) (hchange : u.aux i p≠s.aux i p) :
    u=setAux s i p .mark := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem ParameterJump.eq_silent_of_aux_changed {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (hmode : s.aux i p=.mark) (hchange : u.aux i p≠s.aux i p) :
    u=setAux s i p .silent := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem ParameterJump.eq_error_of_aux_changed {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (hmode : s.aux i p=.silent) (hchange : u.aux i p≠s.aux i p) :
    u=setAux s i p .error := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem ParameterJump.eq_auxReady_of_aux_changed {n θ route s u} (j : @ParameterJump n θ route s u)
    (i : Fin n) (p : Port) (hmode : s.aux i p=.error) (hchange : u.aux i p≠s.aux i p) :
    u=setAux s i p .ready := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]



theorem ParameterJumpDiamond.symm {n θ route} {u v : Snapshot n}
    (h : @ParameterJumpDiamond n θ route u v) : ParameterJumpDiamond θ route v u := by
  rcases h with h | ⟨u',v',hu,hv,h⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨v',u',hv,hu,h.symm⟩

/-- Legal simultaneous operational choices commute up to token-list order.
The two branches may already agree, or each can take one further real jump
to physically identical observations with permutation-equivalent queues. -/
theorem ParameterJump.local_diamond {n θ route s a b} (j : @ParameterJump n θ route s a)
    (k : ParameterJump θ route s b) : ParameterJumpDiamond θ route a b := by
  cases j with
  | fire i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.fire_diamond_of_unchanged i hm hg h
    · rw [k.eq_fire_of_main_changed i hm h]
      exact Or.inl (.refl _)
  | fastEnd i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.fastEnd_diamond_of_unchanged i hm hg h
    · rw [k.eq_fastEnd_of_main_changed i hm h]
      exact Or.inl (.refl _)
  | reopen i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.reopen_diamond_of_unchanged i hm hg h
    · rw [k.eq_reopen_of_main_changed i hm h]
      exact Or.inl (.refl _)
  | mark i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.mark_diamond_of_unchanged i p hm hg h
    · rw [k.eq_mark_of_aux_changed i p hm h]
      exact Or.inl (.refl _)
  | silent i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.silent_diamond_of_unchanged i p hm hg h
    · rw [k.eq_silent_of_aux_changed i p hm h]
      exact Or.inl (.refl _)
  | error i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.error_diamond_of_unchanged i p hm hg h
    · rw [k.eq_error_of_aux_changed i p hm h]
      exact Or.inl (.refl _)
  | auxReady i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.auxReady_diamond_of_unchanged i p hm hg h
    · rw [k.eq_auxReady_of_aux_changed i p hm h]
      exact Or.inl (.refl _)
  | arrive d before after queue due free =>
    let ja := ParameterJump.arrive (θ:=θ) (route:=route) s d before after queue due free
    cases k with
    | fire i hm hg =>
      exact (ja.fire_diamond_of_unchanged i hm hg rfl).symm
    | fastEnd i hm hg =>
      exact (ja.fastEnd_diamond_of_unchanged i hm hg rfl).symm
    | reopen i hm hg =>
      exact (ja.reopen_diamond_of_unchanged i hm hg rfl).symm
    | mark i p hm hg =>
      exact (ja.mark_diamond_of_unchanged i p hm hg rfl).symm
    | silent i p hm hg =>
      exact (ja.silent_diamond_of_unchanged i p hm hg rfl).symm
    | error i p hm hg =>
      exact (ja.error_diamond_of_unchanged i p hm hg rfl).symm
    | auxReady i p hm hg =>
      exact (ja.auxReady_diamond_of_unchanged i p hm hg rfl).symm
    | arrive e before' after' queue' due' free' =>
      exact parameter_arrive_arrive_diamond s d e before after before' after'
        queue queue' due due' free free'
    | rawEnd i p o active expiry =>
      exact parameter_arrive_rawEnd_diamond s d before after queue due free i p o active expiry
  | rawEnd i p o active expiry =>
    let jr := ParameterJump.rawEnd (θ:=θ) (route:=route) s i p o active expiry
    cases k with
    | fire k hm hg =>
      exact (jr.fire_diamond_of_unchanged k hm hg rfl).symm
    | fastEnd k hm hg =>
      exact (jr.fastEnd_diamond_of_unchanged k hm hg rfl).symm
    | reopen k hm hg =>
      exact (jr.reopen_diamond_of_unchanged k hm hg rfl).symm
    | mark k q hm hg =>
      exact (jr.mark_diamond_of_unchanged k q hm hg rfl).symm
    | silent k q hm hg =>
      exact (jr.silent_diamond_of_unchanged k q hm hg rfl).symm
    | error k q hm hg =>
      exact (jr.error_diamond_of_unchanged k q hm hg rfl).symm
    | auxReady k q hm hg =>
      exact (jr.auxReady_diamond_of_unchanged k q hm hg rfl).symm
    | arrive d before after queue due free =>
      exact (parameter_arrive_rawEnd_diamond s d before after queue due free i p o active expiry).symm
    | rawEnd k q r active' expiry' =>
      exact parameter_rawEnd_rawEnd_diamond s i k p q o r active active' expiry expiry'


end KernelR.Hybrid
