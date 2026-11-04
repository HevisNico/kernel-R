import KernelR.HybridContactTransversalityTransport
import KernelR.HybridJumpLocalDiamond
import KernelR.HybridJumpStripping

/-! Directed simultaneous-event diamonds preserve the contact certificate of
one chosen reference branch. No certificate is required on the competing jump. -/
namespace KernelR.Hybrid

/-- At the instant of a legal jump, raw-current values can only increase.
An expiry already has zero current because pulse support is half-open. -/
theorem Jump.current_at_le {n route s u} (jump : @Jump n route s u)
    (i : Fin n) (p : Port) : current s i p s.time ≤ current u i p u.time := by
  cases jump with
  | arrive d before after queue due free =>
    by_cases hi : i = d.cell
    · subst i
      by_cases hp : p = d.port
      · subst p
        simp [current, setRaw, free, pulse]
        exact (a_coarse_bounds.1.le.trans' (by norm_num))
      · simp [current, setRaw, hp]
    · simp [current, setRaw, hi]
  | rawEnd k q origin active due =>
    by_cases hi : i = k
    · subst i
      by_cases hp : p = q
      · subst p
        simp [current, setRaw, active, pulse, due]
      · simp [current, setRaw, hp]
    · simp [current, setRaw, hi]
  | _ => exact le_rfl

/-- Preserving a READY main mode preserves or increases its instantaneous
field, including an arrival at that same cell. -/
theorem Jump.ready_field_le {n θ route s u} (jump : @Jump n route s u)
    (i : Fin n) (ready : s.main i = .ready) (unchanged : u.main i = s.main i) :
    field θ s s.x s.time i .q ≤ field θ u u.x u.time i .q := by
  simp only [field, ready, unchanged, jump.physical_continuous]
  apply add_le_add le_rfl
  unfold drive
  exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
    (jump.current_at_le i p) (Real.exp_pos _).le

/-- The auxiliary READY field has the same one-way stability. -/
theorem Jump.aux_ready_field_le {n θ ε route s u} (jump : @Jump n route s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (ready : s.aux i p = .ready) (unchanged : u.aux i p = s.aux i p) :
    field θ s s.x s.time i (.m p) ≤ field θ u u.x u.time i (.m p) := by
  simp only [field, ready, unchanged, jump.physical_continuous, ite_true]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (jump.current_at_le i p) (box.input_gain_positive i p).le)

/-- A directed diamond carries a positive contact on its reference branch
forward past the arbitrary competing initial jump. -/
def TransverseJumpDiamond {n} {θ : Fin n → Parameters} {route s a b}
    (jump : @Jump n route s a) (reference : Jump route s b) : Prop :=
  (a.ObservationalEq b ∧ jump.ledger.emissions.Perm reference.ledger.emissions) ∨
  ∃ a' b', ∃ residual : Jump route a a', ∃ competing : Jump route b b',
    a'.ObservationalEq b' ∧
    (jump.ledger.emissions ++ residual.ledger.emissions).Perm
      (reference.ledger.emissions ++ competing.ledger.emissions) ∧
    (reference.ContactTransversal θ → residual.ContactTransversal θ) ∧
    (jump.ContactTransversal θ → competing.ContactTransversal θ)

/-- Without a departure from READY, a contact obligation is vacuous. -/
theorem Jump.contactTransversal_of_modes_fixed {n θ route s u}
    (jump : @Jump n route s u) (main : u.main = s.main) (aux : u.aux = s.aux) :
    jump.ContactTransversal θ := by
  rw [jump.contactTransversal_iff_departures]
  simp [main, aux]

private theorem simultaneous_count {n} (l : List (Fin n × ℝ)) (T : ℝ)
    (h : ∀ e ∈ l, e.2=T) (i : Fin n) :
    l.count (i,T)=(l.filter (fun e => e.1=i)).length := by
  classical
  induction l with
  | nil => simp
  | cons e l ih =>
    rcases e with ⟨j,t⟩
    have ht : t=T := h (j,t) (by simp)
    subst t
    have hr : ∀ e ∈ l, e.2=T := fun e he => h e (by simp [he])
    by_cases hj : j=i
    · subst j
      simp [ih hr]
    · simp [hj,ih hr]

private theorem simultaneous_emissions_perm {n} {l r : List (Fin n × ℝ)} {T : ℝ}
    (hl : ∀ e ∈ l, e.2=T) (hr : ∀ e ∈ r, e.2=T)
    (hcount : ∀ i, (l.filter (fun e => e.1=i)).length=
      (r.filter (fun e => e.1=i)).length) : l.Perm r := by
  classical
  apply List.perm_iff_count.mpr
  rintro ⟨i,t⟩
  by_cases ht : t=T
  · subst t
    rw [simultaneous_count l T hl i,simultaneous_count r T hr i]
    exact hcount i
  · have hnl : (i,t)∉l := fun he => ht (hl _ he)
    have hnr : (i,t)∉r := fun he => ht (hr _ he)
    rw [List.count_eq_zero_of_not_mem hnl,List.count_eq_zero_of_not_mem hnr]

private theorem observational_fastPotential {n} {s t : Snapshot n}
    (h : s.ObservationalEq t) (i : Fin n) : fastPotential s i=fastPotential t i := by
  simp only [fastPotential,h.main,h.values]


private theorem directed_labels {n} (θ : Fin n → Parameters) {route s a b a' b'}
    (jump : @Jump n route s a) (reference : Jump route s b)
    (residual : Jump route a a') (competing : Jump route b b')
    (same : a'.ObservationalEq b') :
    (jump.ledger.emissions ++ residual.ledger.emissions).Perm
      (reference.ledger.emissions ++ competing.ledger.emissions) := by
  apply simultaneous_emissions_perm (T := s.time)
  · intro ev he
    rcases List.mem_append.mp he with he | he
    · exact (Move.jump (θ := θ) jump).emission_time ev he
    · exact ((Move.jump (θ := θ) residual).emission_time ev he).trans jump.time_unchanged
  · intro ev he
    rcases List.mem_append.mp he with he | he
    · exact (Move.jump (θ := θ) reference).emission_time ev he
    · exact ((Move.jump (θ := θ) competing).emission_time ev he).trans reference.time_unchanged
  · intro i
    have hj := jump.fast_potential_balance (θ := θ) i
    have hk := reference.fast_potential_balance (θ := θ) i
    have hj' := residual.fast_potential_balance (θ := θ) i
    have hk' := competing.fast_potential_balance (θ := θ) i
    have he := observational_fastPotential same i
    simp only [Move.fireCount, Move.ledger] at hj hk hj' hk'
    simp only [List.filter_append, List.length_append]
    exact_mod_cast (show
      (((jump.ledger.emissions.filter (fun ev => ev.1=i)).length +
        (residual.ledger.emissions.filter (fun ev => ev.1=i)).length : ℕ) : ℝ) =
      (((reference.ledger.emissions.filter (fun ev => ev.1=i)).length +
        (competing.ledger.emissions.filter (fun ev => ev.1=i)).length : ℕ) : ℝ) by
      push_cast
      linarith)

private theorem TransverseJumpDiamond.of_same {n θ route s a b}
    (jump : @Jump n route s a) (reference : Jump route s b)
    (same : a.ObservationalEq b) : TransverseJumpDiamond (θ := θ) jump reference := by
  left
  refine ⟨same, simultaneous_emissions_perm (T := s.time) ?_ ?_ ?_⟩
  · intro ev he; exact (Move.jump (θ := θ) jump).emission_time ev he
  · intro ev he; exact (Move.jump (θ := θ) reference).emission_time ev he
  · intro i
    have hj := jump.fast_potential_balance (θ := θ) i
    have hk := reference.fast_potential_balance (θ := θ) i
    have he := observational_fastPotential same i
    simp only [Move.fireCount, Move.ledger] at hj hk
    exact_mod_cast (show
      (((jump.ledger.emissions.filter (fun ev => ev.1=i)).length : ℕ) : ℝ) =
      (((reference.ledger.emissions.filter (fun ev => ev.1=i)).length : ℕ) : ℝ) by linarith)

private theorem TransverseJumpDiamond.of_residual {n θ route s a b a' b'}
    (jump : @Jump n route s a) (reference : Jump route s b)
    (residual : Jump route a a') (competing : Jump route b b')
    (same : a'.ObservationalEq b')
    (positive : reference.ContactTransversal θ → residual.ContactTransversal θ)
    (otherPositive : jump.ContactTransversal θ → competing.ContactTransversal θ) :
    TransverseJumpDiamond (θ := θ) jump reference :=
  Or.inr ⟨a', b', residual, competing, same,
    directed_labels θ jump reference residual competing same, positive, otherPositive⟩

/-- Reversing the two named branches retains both directed certificates. -/
theorem TransverseJumpDiamond.symm {n θ route s a b}
    {jump : @Jump n route s a} {reference : Jump route s b}
    (diamond : TransverseJumpDiamond (θ := θ) jump reference) :
    TransverseJumpDiamond (θ := θ) reference jump := by
  rcases diamond with ⟨same, labels⟩ | ⟨a', b', residual, competing, same, labels, hp, hq⟩
  · exact Or.inl ⟨same.symm, labels.symm⟩
  · exact Or.inr ⟨b', a', competing, residual, same.symm, labels.symm, hq, hp⟩

private theorem Jump.contactTransversal_setMain {n θ route s u}
    (jump : @Jump n route s u) (i : Fin n) (mode : MainMode)
    (_unchanged : u.main i = s.main i)
    (lift : Jump route (setMain s i mode) (setMain u i mode))
    (positive : jump.ContactTransversal θ) : lift.ContactTransversal θ := by
  rw [lift.contactTransversal_iff_departures]
  have hp := jump.contactTransversal_iff_departures.mp positive
  constructor
  · intro k ready changed
    have hki : k ≠ i := by
      intro h; subst k
      simp [setMain] at changed
    have ready' : s.main k = .ready := by simpa [setMain, hki] using ready
    have changed' : u.main k ≠ s.main k := by simpa [setMain, hki] using changed
    have heq : field θ (setMain s i mode) (setMain s i mode).x
        (setMain s i mode).time k .q = field θ s s.x s.time k .q := by
      simp [field, drive, current, setMain, hki]
    rw [heq]
    exact hp.1 k ready' changed'
  · intro k p ready changed
    change 0 < field θ s s.x s.time k (.m p)
    exact hp.2 k p ready changed

private theorem Jump.contactTransversal_setAux {n θ route s u}
    (jump : @Jump n route s u) (i : Fin n) (p : Port) (mode : AuxMode)
    (_unchanged : u.aux i p = s.aux i p)
    (lift : Jump route (setAux s i p mode) (setAux u i p mode))
    (positive : jump.ContactTransversal θ) : lift.ContactTransversal θ := by
  rw [lift.contactTransversal_iff_departures]
  have hp := jump.contactTransversal_iff_departures.mp positive
  constructor
  · intro k ready changed
    change 0 < field θ s s.x s.time k .q
    exact hp.1 k ready changed
  · intro k q ready changed
    have address : k ≠ i ∨ q ≠ p := by
      by_cases hk : k=i
      · right
        intro hq; subst k; subst q
        simp [setAux] at changed
      · exact Or.inl hk
    have other : ∀ (v : Snapshot n), (setAux v i p mode).aux k q = v.aux k q := by
      intro v
      rcases address with hk | hq
      · simp [setAux, hk]
      · by_cases hk : k=i
        · subst k; simp [setAux, hq]
        · simp [setAux, hk]
    have ready' : s.aux k q = .ready := by simpa only [other] using ready
    have changed' : u.aux k q ≠ s.aux k q := by simpa only [other] using changed
    have heq : field θ (setAux s i p mode) (setAux s i p mode).x
        (setAux s i p mode).time k (.m q) = field θ s s.x s.time k (.m q) := by
      simp only [field, other]
      rfl
    rw [heq]
    exact hp.2 k q ready' changed'

private theorem Jump.contactTransversal_appendPending {n θ route s u Q v}
    (jump : @Jump n route s u) (lift : Jump route (appendPending s Q) v)
    (same : v.ObservationalEq (appendPending u Q))
    (positive : jump.ContactTransversal θ) : lift.ContactTransversal θ := by
  rw [lift.contactTransversal_iff_departures]
  have heq : field θ (appendPending s Q) = field θ s := rfl
  rw [heq]
  simpa only [same.main, same.aux, appendPending] using
    jump.contactTransversal_iff_departures.mp positive

private theorem Jump.transverse_fire_diamond_of_unchanged {n θ route s u}
    (jump : @Jump n route s u) (i : Fin n)
    (ready : s.main i = .ready) (guard : s.x i .q = 1)
    (unchanged : u.main i = s.main i) :
    TransverseJumpDiamond (θ := θ) (Jump.fire s i ready guard) jump := by
  obtain ⟨lift⟩ := jump.setMain_of_unchanged i .fast unchanged
  obtain ⟨v, ⟨lift'⟩, same⟩ := lift.appendPending_observational (route i s.time)
  let competing := Jump.fire (route := route) u i (unchanged.trans ready)
    (by simpa only [jump.physical_continuous] using guard)
  apply TransverseJumpDiamond.of_residual _ _ lift' competing
  · simpa only [appendPending, setMain, jump.time_unchanged] using same
  · intro positive
    exact lift.contactTransversal_appendPending lift' same
      (jump.contactTransversal_setMain i .fast unchanged lift positive)
  · intro positive
    exact lt_of_lt_of_le positive (jump.ready_field_le i ready unchanged)

private theorem Jump.transverse_fastEnd_diamond_of_unchanged {n θ route s u}
    (jump : @Jump n route s u) (i : Fin n)
    (mode : s.main i = .fast) (guard : s.x i .q = 1/4)
    (unchanged : u.main i = s.main i) :
    TransverseJumpDiamond (θ := θ) (Jump.fastEnd s i mode guard) jump := by
  obtain ⟨lift⟩ := jump.setMain_of_unchanged i .slow unchanged
  let competing := Jump.fastEnd (route := route) u i (unchanged.trans mode)
    (by simpa only [jump.physical_continuous] using guard)
  exact TransverseJumpDiamond.of_residual _ _ lift competing (.refl _)
    (jump.contactTransversal_setMain i .slow unchanged lift) (fun _ => trivial)

private theorem Jump.transverse_reopen_diamond_of_unchanged {n θ route s u}
    (jump : @Jump n route s u) (i : Fin n)
    (mode : s.main i = .slow) (guard : s.x i .q = 1/10)
    (unchanged : u.main i = s.main i) :
    TransverseJumpDiamond (θ := θ) (Jump.reopen s i mode guard) jump := by
  obtain ⟨lift⟩ := jump.setMain_of_unchanged i .ready unchanged
  let competing := Jump.reopen (route := route) u i (unchanged.trans mode)
    (by simpa only [jump.physical_continuous] using guard)
  exact TransverseJumpDiamond.of_residual _ _ lift competing (.refl _)
    (jump.contactTransversal_setMain i .ready unchanged lift) (fun _ => trivial)

private theorem Jump.transverse_mark_diamond_of_unchanged {n θ ε route s u}
    (jump : @Jump n route s u) (box : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (mode : s.aux i p = .ready) (guard : s.x i (.m p) = 1)
    (unchanged : u.aux i p = s.aux i p) :
    TransverseJumpDiamond (θ := θ) (Jump.mark s i p mode guard) jump := by
  obtain ⟨lift⟩ := jump.setAux_of_unchanged i p .mark unchanged
  let competing := Jump.mark (route := route) u i p (unchanged.trans mode)
    (by simpa only [jump.physical_continuous] using guard)
  apply TransverseJumpDiamond.of_residual _ _ lift competing (.refl _)
  · exact jump.contactTransversal_setAux i p .mark unchanged lift
  · intro positive; exact lt_of_lt_of_le positive (jump.aux_ready_field_le box i p mode unchanged)

private theorem Jump.transverse_silent_diamond_of_unchanged {n θ route s u}
    (jump : @Jump n route s u) (i : Fin n) (p : Port)
    (mode : s.aux i p = .mark) (guard : s.x i (.m p) = 4/5)
    (unchanged : u.aux i p = s.aux i p) :
    TransverseJumpDiamond (θ := θ) (Jump.silent s i p mode guard) jump := by
  obtain ⟨lift⟩ := jump.setAux_of_unchanged i p .silent unchanged
  let competing := Jump.silent (route := route) u i p (unchanged.trans mode)
    (by simpa only [jump.physical_continuous] using guard)
  apply TransverseJumpDiamond.of_residual _ _ lift competing (.refl _)
  · exact jump.contactTransversal_setAux i p .silent unchanged lift
  · intro _; trivial

private theorem Jump.transverse_error_diamond_of_unchanged {n θ route s u}
    (jump : @Jump n route s u) (i : Fin n) (p : Port)
    (mode : s.aux i p = .silent) (guard : s.x i (.m p) = 1/10)
    (unchanged : u.aux i p = s.aux i p) :
    TransverseJumpDiamond (θ := θ) (Jump.error s i p mode guard) jump := by
  obtain ⟨lift⟩ := jump.setAux_of_unchanged i p .error unchanged
  let competing := Jump.error (route := route) u i p (unchanged.trans mode)
    (by simpa only [jump.physical_continuous] using guard)
  apply TransverseJumpDiamond.of_residual _ _ lift competing (.refl _)
  · exact jump.contactTransversal_setAux i p .error unchanged lift
  · intro _; trivial

private theorem Jump.transverse_auxReady_diamond_of_unchanged {n θ route s u}
    (jump : @Jump n route s u) (i : Fin n) (p : Port)
    (mode : s.aux i p = .error) (guard : s.x i (.m p) = 1/40)
    (unchanged : u.aux i p = s.aux i p) :
    TransverseJumpDiamond (θ := θ) (Jump.auxReady s i p mode guard) jump := by
  obtain ⟨lift⟩ := jump.setAux_of_unchanged i p .ready unchanged
  let competing := Jump.auxReady (route := route) u i p (unchanged.trans mode)
    (by simpa only [jump.physical_continuous] using guard)
  apply TransverseJumpDiamond.of_residual _ _ lift competing (.refl _)
  · exact jump.contactTransversal_setAux i p .ready unchanged lift
  · intro _; trivial

private theorem transverse_rawEnd_rawEnd {n θ route} (s : Snapshot n)
    (i j : Fin n) (p q : Port) (o r : ℝ)
    (hi : s.raw i p=some o) (hj : s.raw j q=some r)
    (hti : s.time=o+1) (htj : s.time=r+1) :
    TransverseJumpDiamond (θ := θ)
      (Jump.rawEnd (route := route) s i p o hi hti)
      (Jump.rawEnd (route := route) s j q r hj htj) := by
  by_cases hc : i=j
  · subst j
    by_cases hp : p=q
    · subst q
      exact TransverseJumpDiamond.of_same _ _ (.refl _)
    · apply TransverseJumpDiamond.of_residual _ _
        (Jump.rawEnd (route := route) (setRaw s i p none) i q r
          (by simpa only [setRaw_other s i i p q none (Or.inr hp)] using hj) htj)
        (Jump.rawEnd (route := route) (setRaw s i q none) i p o
          (by simpa only [setRaw_other s i i q p none (Or.inr (Ne.symm hp))] using hi) hti)
      · rw [setRaw_commute s i i p q none none (Or.inr hp)]
        exact .refl _
      · intro _; trivial
      · intro _; trivial
  · apply TransverseJumpDiamond.of_residual _ _
      (Jump.rawEnd (route := route) (setRaw s i p none) j q r
        (by simpa only [setRaw_other s i j p q none (Or.inl hc)] using hj) htj)
      (Jump.rawEnd (route := route) (setRaw s j q none) i p o
        (by simpa only [setRaw_other s j i q p none (Or.inl (Ne.symm hc))] using hi) hti)
    · rw [setRaw_commute s i j p q none none (Or.inl hc)]
      exact .refl _
    · intro _; trivial
    · intro _; trivial

private theorem transverse_arrive_rawEnd {n θ route} (s : Snapshot n) (d : Delivery n)
    (before after : List (Delivery n)) (hq : s.pending=before++d::after)
    (hd : d.due=s.time) (hf : s.raw d.cell d.port=none)
    (i : Fin n) (p : Port) (o : ℝ) (ha : s.raw i p=some o)
    (ht : s.time=o+1) :
    TransverseJumpDiamond (θ := θ)
      (Jump.arrive (route := route) s d before after hq hd hf)
      (Jump.rawEnd (route := route) s i p o ha ht) := by
  have hdiff : d.cell≠i ∨ d.port≠p := by
    by_cases hc : d.cell=i
    · right
      intro hp
      rw [hc,hp,ha] at hf
      contradiction
    · exact Or.inl hc
  apply TransverseJumpDiamond.of_residual _ _
    (Jump.rawEnd (route := route) (s.afterArrival d before after) i p o (by
      change (setRaw s d.cell d.port (some s.time)).raw i p=some o
      rw [setRaw_other s d.cell i d.port p (some s.time) hdiff]
      exact ha) ht)
    (Jump.arrive (route := route) (setRaw s i p none) d before after hq hd (by
      rw [setRaw_other s i d.cell p d.port none (hdiff.elim
        (fun h => Or.inl (Ne.symm h)) (fun h => Or.inr (Ne.symm h)))]
      exact hf))
  · refine ⟨rfl,rfl,rfl,rfl,?_,List.Perm.refl _⟩
    have h := congrArg Snapshot.raw (setRaw_commute s d.cell i d.port p
      (some s.time) none hdiff)
    simpa only [Snapshot.afterArrival, setRaw] using h
  · intro _; trivial
  · intro _; trivial

private theorem transverse_arrive_arrive {n θ route} (s : Snapshot n) (d e : Delivery n)
    (b₁ a₁ b₂ a₂ : List (Delivery n))
    (hq₁ : s.pending=b₁++d::a₁) (hq₂ : s.pending=b₂++e::a₂)
    (hd : d.due=s.time) (he : e.due=s.time)
    (hf₁ : s.raw d.cell d.port=none) (hf₂ : s.raw e.cell e.port=none) :
    TransverseJumpDiamond (θ := θ)
      (Jump.arrive (route := route) s d b₁ a₁ hq₁ hd hf₁)
      (Jump.arrive (route := route) s e b₂ a₂ hq₂ he hf₂) := by
  have hA : s.pending.Perm (d::(b₁++a₁)) := by rw [hq₁]; exact List.perm_middle
  have hB : s.pending.Perm (e::(b₂++a₂)) := by rw [hq₂]; exact List.perm_middle
  by_cases hde : d=e
  · subst e
    exact TransverseJumpDiamond.of_same _ _
      ⟨rfl,rfl,rfl,rfl,rfl,List.Perm.cons_inv (hA.symm.trans hB)⟩
  · have hdiff : d.cell≠e.cell ∨ d.port≠e.port := by
      by_cases hc : d.cell=e.cell
      · right
        intro hp
        exact hde (due_delivery_eq_of_address hd he hc hp)
      · exact Or.inl hc
    obtain ⟨ba,aa,bb,ab,hAA,hBB,hrest⟩ := queue_removal_diamond hA hB hde
    apply TransverseJumpDiamond.of_residual _ _
      (Jump.arrive (route := route) (s.afterArrival d b₁ a₁) e ba aa hAA he (by
        change (setRaw s d.cell d.port (some s.time)).raw e.cell e.port=none
        rw [setRaw_other s d.cell e.cell d.port e.port (some s.time) hdiff]
        exact hf₂))
      (Jump.arrive (route := route) (s.afterArrival e b₂ a₂) d bb ab hBB hd (by
        change (setRaw s e.cell e.port (some s.time)).raw d.cell d.port=none
        rw [setRaw_other s e.cell d.cell e.port d.port (some s.time) (hdiff.elim
          (fun h => Or.inl (Ne.symm h)) (fun h => Or.inr (Ne.symm h)))]
        exact hf₁))
    · refine ⟨rfl,rfl,rfl,rfl,?_,hrest⟩
      have h := congrArg Snapshot.raw (setRaw_commute s d.cell e.cell d.port e.port
        (some s.time) (some s.time) hdiff)
      simpa only [Snapshot.afterArrival,setRaw] using h
    · intro _; trivial
    · intro _; trivial

/-- Every simultaneous critical pair preserves the positive-contact
certificate of either selected branch, without imposing an event priority. -/
theorem Jump.transverse_local_diamond {n θ ε route s a b}
    (box : PhysicalBox θ ε) (j : @Jump n route s a)
    (k : Jump route s b) : TransverseJumpDiamond (θ := θ) j k := by
  cases j with
  | fire i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.transverse_fire_diamond_of_unchanged i hm hg h
    · apply TransverseJumpDiamond.of_same _ _
      rw [k.eq_fire_of_main_changed i hm h]
      exact .refl _
  | fastEnd i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.transverse_fastEnd_diamond_of_unchanged i hm hg h
    · apply TransverseJumpDiamond.of_same _ _
      rw [k.eq_fastEnd_of_main_changed i hm h]
      exact .refl _
  | reopen i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.transverse_reopen_diamond_of_unchanged i hm hg h
    · apply TransverseJumpDiamond.of_same _ _
      rw [k.eq_reopen_of_main_changed i hm h]
      exact .refl _
  | mark i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.transverse_mark_diamond_of_unchanged box i p hm hg h
    · apply TransverseJumpDiamond.of_same _ _
      rw [k.eq_mark_of_aux_changed i p hm h]
      exact .refl _
  | silent i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.transverse_silent_diamond_of_unchanged i p hm hg h
    · apply TransverseJumpDiamond.of_same _ _
      rw [k.eq_silent_of_aux_changed i p hm h]
      exact .refl _
  | error i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.transverse_error_diamond_of_unchanged i p hm hg h
    · apply TransverseJumpDiamond.of_same _ _
      rw [k.eq_error_of_aux_changed i p hm h]
      exact .refl _
  | auxReady i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.transverse_auxReady_diamond_of_unchanged i p hm hg h
    · apply TransverseJumpDiamond.of_same _ _
      rw [k.eq_auxReady_of_aux_changed i p hm h]
      exact .refl _
  | arrive d before after queue due free =>
    let ja := Jump.arrive (route:=route) s d before after queue due free
    cases k with
    | fire i hm hg =>
      exact (ja.transverse_fire_diamond_of_unchanged i hm hg rfl).symm
    | fastEnd i hm hg =>
      exact (ja.transverse_fastEnd_diamond_of_unchanged i hm hg rfl).symm
    | reopen i hm hg =>
      exact (ja.transverse_reopen_diamond_of_unchanged i hm hg rfl).symm
    | mark i p hm hg =>
      exact (ja.transverse_mark_diamond_of_unchanged box i p hm hg rfl).symm
    | silent i p hm hg =>
      exact (ja.transverse_silent_diamond_of_unchanged i p hm hg rfl).symm
    | error i p hm hg =>
      exact (ja.transverse_error_diamond_of_unchanged i p hm hg rfl).symm
    | auxReady i p hm hg =>
      exact (ja.transverse_auxReady_diamond_of_unchanged i p hm hg rfl).symm
    | arrive e before' after' queue' due' free' =>
      exact transverse_arrive_arrive s d e before after before' after'
        queue queue' due due' free free'
    | rawEnd i p o active expiry =>
      exact transverse_arrive_rawEnd s d before after queue due free i p o active expiry
  | rawEnd i p o active expiry =>
    let jr := Jump.rawEnd (route:=route) s i p o active expiry
    cases k with
    | fire k hm hg =>
      exact (jr.transverse_fire_diamond_of_unchanged k hm hg rfl).symm
    | fastEnd k hm hg =>
      exact (jr.transverse_fastEnd_diamond_of_unchanged k hm hg rfl).symm
    | reopen k hm hg =>
      exact (jr.transverse_reopen_diamond_of_unchanged k hm hg rfl).symm
    | mark k q hm hg =>
      exact (jr.transverse_mark_diamond_of_unchanged box k q hm hg rfl).symm
    | silent k q hm hg =>
      exact (jr.transverse_silent_diamond_of_unchanged k q hm hg rfl).symm
    | error k q hm hg =>
      exact (jr.transverse_error_diamond_of_unchanged k q hm hg rfl).symm
    | auxReady k q hm hg =>
      exact (jr.transverse_auxReady_diamond_of_unchanged k q hm hg rfl).symm
    | arrive d before after queue due free =>
      exact (transverse_arrive_rawEnd s d before after queue due free i p o active expiry).symm
    | rawEnd k q r active' expiry' =>
      exact transverse_rawEnd_rawEnd s i k p q o r active active' expiry expiry'


end KernelR.Hybrid
