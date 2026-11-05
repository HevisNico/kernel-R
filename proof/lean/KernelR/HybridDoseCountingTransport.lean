import KernelR.HybridDoseCounting
import KernelR.HybridPortPermutation
import KernelR.HybridEmissionRouterTransport

/-! Structural transport of complete-section covers. Port relabeling maps
every actual move, entry, exposed span and exit before counts are compared.
The memory or ledger identities are not used to invent a cover. -/
namespace KernelR.Hybrid

theorem Execution.permutePorts_append {n θ s v u}
    (first : @Execution n θ (fun _ _ => []) s v)
    (rest : Execution θ (fun _ _ => []) v u) (σ : Equiv.Perm Port) :
    (first.append rest).permutePorts σ =
      (first.permutePorts σ).append (rest.permutePorts σ) := by
  induction first with
  | nil => rfl
  | cons move tail ih => simp only [append, permutePorts, ih]

theorem Execution.allStates_permutePorts {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u) (σ : Equiv.Perm Port)
    (P : Snapshot n → Prop) (h : e.AllStates (fun v => P (v.permutePorts σ))) :
    (e.permutePorts σ).AllStates P := by
  induction e with
  | nil => exact h
  | cons move tail ih => exact ⟨h.1, ih h.2⟩

theorem Execution.errorExposed_permutePorts {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u) (σ : Equiv.Perm Port)
    (i : Fin n) (p : Port) (h : e.ErrorExposed i (σ p)) :
    (e.permutePorts σ).ErrorExposed i p := by
  induction e with
  | nil => trivial
  | cons move tail ih =>
    cases move with
    | flow f => exact ⟨h.1, ih h.2⟩
    | jump j => exact ih h

theorem Execution.markExposed_permutePorts {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u) (σ : Equiv.Perm Port)
    (i : Fin n) (p : Port) (h : e.MarkExposed i (σ p)) :
    (e.permutePorts σ).MarkExposed i p := by
  induction e with
  | nil => trivial
  | cons move tail ih =>
    cases move with
    | flow f => exact ⟨h.1, ih h.2⟩
    | jump j => exact ih h

theorem Move.errorInactive_permutePorts {n θ s u}
    (move : @Move n θ (fun _ _ => []) s u) (σ : Equiv.Perm Port)
    (i : Fin n) (p : Port) (h : move.ErrorInactive i (σ p)) :
    (move.permutePorts σ).ErrorInactive i p := by
  cases move <;> exact h

theorem Move.markInactive_permutePorts {n θ s u}
    (move : @Move n θ (fun _ _ => []) s u) (σ : Equiv.Perm Port)
    (i : Fin n) (p : Port) (h : move.MarkInactive i (σ p)) :
    (move.permutePorts σ).MarkInactive i p := by
  cases move <;> exact h

/-- Construct a cover of the relabeled execution by mapping its real sections. -/
theorem ErrorSectionCover.permutePorts_exists {n θ s u}
    {e : @Execution n θ (fun _ _ => []) s u} {i : Fin n} {p : Port}
    (cover : ErrorSectionCover i p e) (σ : Equiv.Perm Port) :
    Nonempty (ErrorSectionCover i (σ.symm p) (e.permutePorts σ)) := by
  induction cover with
  | nil s => exact ⟨.nil _⟩
  | inactive move rest physical tail ih =>
    obtain ⟨mapped⟩ := ih
    refine ⟨.inactive (move.permutePorts σ) (rest.permutePorts σ) ?_ mapped⟩
    apply move.errorInactive_permutePorts σ
    simpa only [Equiv.apply_symm_apply] using physical
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    obtain ⟨mapped⟩ := ih
    have hs : (span.permutePorts σ).AllStates
        (fun v => v.aux i (σ.symm p) = .error) := by
      apply span.allStates_permutePorts σ
      simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using phase
    have he : (span.permutePorts σ).ErrorExposed i (σ.symm p) := by
      apply span.errorExposed_permutePorts σ
      simpa only [Equiv.apply_symm_apply] using exposed
    simpa only [Execution.permutePorts, Execution.permutePorts_append, Move.permutePorts]
      using (Nonempty.intro (ErrorSectionCover.fullPhase
        (entry.permutePorts σ) (span.permutePorts σ) (exit.permutePorts σ)
        (rest.permutePorts σ)
        (by simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using before)
        (by simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using entered)
        (by simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using leaving)
        (by simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using after)
        hs he mapped))

/-- Construct a protected MARK cover under the same physical port relabeling. -/
theorem MarkSectionCover.permutePorts_exists {n θ s u}
    {e : @Execution n θ (fun _ _ => []) s u} {i : Fin n} {p : Port}
    (cover : MarkSectionCover i p e) (σ : Equiv.Perm Port) :
    Nonempty (MarkSectionCover i (σ.symm p) (e.permutePorts σ)) := by
  induction cover with
  | nil s => exact ⟨.nil _⟩
  | inactive move rest physical tail ih =>
    obtain ⟨mapped⟩ := ih
    refine ⟨.inactive (move.permutePorts σ) (rest.permutePorts σ) ?_ mapped⟩
    apply move.markInactive_permutePorts σ
    simpa only [Equiv.apply_symm_apply] using physical
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    obtain ⟨mapped⟩ := ih
    have hs : (span.permutePorts σ).AllStates
        (fun v => v.aux i (σ.symm p) = .mark) := by
      apply span.allStates_permutePorts σ
      simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using phase
    have he : (span.permutePorts σ).MarkExposed i (σ.symm p) := by
      apply span.markExposed_permutePorts σ
      simpa only [Equiv.apply_symm_apply] using exposed
    simpa only [Execution.permutePorts, Execution.permutePorts_append, Move.permutePorts]
      using (Nonempty.intro (MarkSectionCover.fullPhase
        (entry.permutePorts σ) (span.permutePorts σ) (exit.permutePorts σ)
        (rest.permutePorts σ)
        (by simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using before)
        (by simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using entered)
        (by simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using leaving)
        (by simpa only [Snapshot.permutePorts_aux, Equiv.apply_symm_apply] using after)
        hs he mapped))

theorem ErrorSectionCover.permutePorts_count {n θ s u}
    {e : @Execution n θ (fun _ _ => []) s u} {i : Fin n} {p : Port}
    (cover : ErrorSectionCover i p e) (σ : Equiv.Perm Port)
    (mapped : ErrorSectionCover i (σ.symm p) (e.permutePorts σ)) :
    mapped.count = cover.count := by
  have he := e.permutePorts_error σ i (σ.symm p)
  rw [mapped.ledger_eq] at he
  simp only [Equiv.apply_symm_apply] at he
  rw [cover.ledger_eq] at he
  have hc : (mapped.count : ℝ) = cover.count := by linarith
  exact_mod_cast hc

theorem MarkSectionCover.permutePorts_count {n θ s u}
    {e : @Execution n θ (fun _ _ => []) s u} {i : Fin n} {p : Port}
    (cover : MarkSectionCover i p e) (σ : Equiv.Perm Port)
    (mapped : MarkSectionCover i (σ.symm p) (e.permutePorts σ)) :
    mapped.count = cover.count := by
  have he := e.permutePorts_mark σ i (σ.symm p)
  rw [mapped.ledger_eq] at he
  simp only [Equiv.apply_symm_apply] at he
  rw [cover.ledger_eq] at he
  have hc : (mapped.count : ℝ) = cover.count := by linarith
  exact_mod_cast hc

/-- Exact-move router transport: flows retain their actual paths and jumps
retain both snapshots. This records substantially more than equal ledgers. -/
inductive Move.RouterCopy {n θ route route'} :
    {s u : Snapshot n} → Move θ route s u → Move θ route' s u → Prop
  | flow {s u} (f : Flow θ s u) : RouterCopy (.flow f) (.flow f)
  | jump {s u} (j : Jump route s u) (j' : Jump route' s u) :
      RouterCopy (.jump j) (.jump j')

inductive Execution.RouterCopy {n θ route route'} :
    {s u : Snapshot n} → Execution θ route s u → Execution θ route' s u → Prop
  | nil (s) : RouterCopy (.nil s) (.nil s)
  | cons {s v u} {move : Move θ route s v} {move' : Move θ route' s v}
      {rest : Execution θ route v u} {rest' : Execution θ route' v u}
      (step : Move.RouterCopy move move') (tail : RouterCopy rest rest') :
      RouterCopy (.cons move rest) (.cons move' rest')

theorem Execution.RouterCopy.split {n θ route route' s v u}
    (first : @Execution n θ route s v) (rest : Execution θ route v u)
    {whole : Execution θ route' s u} (copy : RouterCopy (first.append rest) whole) :
    ∃ first' : Execution θ route' s v, ∃ rest' : Execution θ route' v u,
      whole = first'.append rest' ∧ RouterCopy first first' ∧ RouterCopy rest rest' := by
  induction first with
  | nil => exact ⟨.nil _, whole, rfl, .nil _, copy⟩
  | cons move tail ih =>
    cases copy with
    | cons step tailCopy =>
      obtain ⟨initial, suffix, same, left, right⟩ := ih rest tailCopy
      exact ⟨.cons _ initial, suffix, by rw [same]; rfl, .cons step left, right⟩

theorem Execution.RouterCopy.allStates {n θ route route' s u}
    {e : @Execution n θ route s u} {e' : Execution θ route' s u}
    (copy : RouterCopy e e') (P : Snapshot n → Prop) (h : e.AllStates P) :
    e'.AllStates P := by
  induction copy with
  | nil => exact h
  | cons step tail ih => exact ⟨h.1, ih h.2⟩

theorem Execution.RouterCopy.errorExposed {n θ route route' s u}
    {e : @Execution n θ route s u} {e' : Execution θ route' s u}
    (copy : RouterCopy e e') (i : Fin n) (p : Port) (h : e.ErrorExposed i p) :
    e'.ErrorExposed i p := by
  induction copy with
  | nil => trivial
  | cons step tail ih =>
    cases step with
    | flow f => exact ⟨h.1, ih h.2⟩
    | jump j j' => exact ih h

theorem Execution.RouterCopy.markExposed {n θ route route' s u}
    {e : @Execution n θ route s u} {e' : Execution θ route' s u}
    (copy : RouterCopy e e') (i : Fin n) (p : Port) (h : e.MarkExposed i p) :
    e'.MarkExposed i p := by
  induction copy with
  | nil => trivial
  | cons step tail ih =>
    cases step with
    | flow f => exact ⟨h.1, ih h.2⟩
    | jump j j' => exact ih h

theorem ErrorSectionCover.routerCopy_exists {n θ route s u}
    {e : @Execution n θ route s u} {i : Fin n} {p : Port}
    (cover : ErrorSectionCover i p e) {route' : Router n}
    {e' : Execution θ route' s u} (copy : Execution.RouterCopy e e') :
    Nonempty (ErrorSectionCover i p e') := by
  induction cover generalizing route' with
  | nil s =>
    cases copy
    exact ⟨.nil _⟩
  | inactive move rest physical tail ih =>
    cases copy with
    | cons step tailCopy =>
      obtain ⟨mapped⟩ := ih tailCopy
      cases step with
      | flow f => exact ⟨.inactive (.flow f) _ physical mapped⟩
      | jump j j' => exact ⟨.inactive (.jump j') _ trivial mapped⟩
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    cases copy with
    | cons step suffixCopy =>
      cases step with
      | jump _ entry' =>
        obtain ⟨span', suffix', same, spanCopy, restCopy⟩ :=
          Execution.RouterCopy.split span (.cons (.jump exit) rest) suffixCopy
        cases same
        cases restCopy with
        | cons exitCopy tailCopy =>
          cases exitCopy with
          | jump _ exit' =>
            obtain ⟨mapped⟩ := ih tailCopy
            exact ⟨.fullPhase entry' span' exit' _ before entered leaving after
              (spanCopy.allStates _ phase) (spanCopy.errorExposed i p exposed) mapped⟩

theorem MarkSectionCover.routerCopy_exists {n θ route s u}
    {e : @Execution n θ route s u} {i : Fin n} {p : Port}
    (cover : MarkSectionCover i p e) {route' : Router n}
    {e' : Execution θ route' s u} (copy : Execution.RouterCopy e e') :
    Nonempty (MarkSectionCover i p e') := by
  induction cover generalizing route' with
  | nil s =>
    cases copy
    exact ⟨.nil _⟩
  | inactive move rest physical tail ih =>
    cases copy with
    | cons step tailCopy =>
      obtain ⟨mapped⟩ := ih tailCopy
      cases step with
      | flow f => exact ⟨.inactive (.flow f) _ physical mapped⟩
      | jump j j' => exact ⟨.inactive (.jump j') _ trivial mapped⟩
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    cases copy with
    | cons step suffixCopy =>
      cases step with
      | jump _ entry' =>
        obtain ⟨span', suffix', same, spanCopy, restCopy⟩ :=
          Execution.RouterCopy.split span (.cons (.jump exit) rest) suffixCopy
        cases same
        cases restCopy with
        | cons exitCopy tailCopy =>
          cases exitCopy with
          | jump _ exit' =>
            obtain ⟨mapped⟩ := ih tailCopy
            exact ⟨.fullPhase entry' span' exit' _ before entered leaving after
              (spanCopy.allStates _ phase) (spanCopy.markExposed i p exposed) mapped⟩

theorem Execution.RouterCopy.error_ledger {n θ route route' s u}
    {e : @Execution n θ route s u} {e' : Execution θ route' s u}
    (copy : RouterCopy e e') (i : Fin n) (p : Port) :
    e'.ledger.error i p = e.ledger.error i p := by
  induction copy with
  | nil => rfl
  | cons step tail ih =>
    cases step with
    | flow f =>
      change f.ledger.error i p + _ = f.ledger.error i p + _
      rw [ih]
    | jump j j' =>
      change j'.ledger.error i p + _ = j.ledger.error i p + _
      rw [j'.no_actuation.1 i p, j.no_actuation.1 i p, ih]

theorem Execution.RouterCopy.mark_ledger {n θ route route' s u}
    {e : @Execution n θ route s u} {e' : Execution θ route' s u}
    (copy : RouterCopy e e') (i : Fin n) (p : Port) :
    e'.ledger.mark i p = e.ledger.mark i p := by
  induction copy with
  | nil => rfl
  | cons step tail ih =>
    cases step with
    | flow f =>
      change f.ledger.mark i p + _ = f.ledger.mark i p + _
      rw [ih]
    | jump j j' =>
      change j'.ledger.mark i p + _ = j.ledger.mark i p + _
      rw [j'.no_mark_actuation i p, j.no_mark_actuation i p, ih]

theorem ErrorSectionCover.routerCopy_count {n θ route route' s u}
    {e : @Execution n θ route s u} {e' : Execution θ route' s u}
    {i : Fin n} {p : Port} (cover : ErrorSectionCover i p e)
    (copy : Execution.RouterCopy e e') (mapped : ErrorSectionCover i p e') :
    mapped.count = cover.count := by
  have he := copy.error_ledger i p
  rw [mapped.ledger_eq, cover.ledger_eq] at he
  have hc : (mapped.count : ℝ) = cover.count := by linarith
  exact_mod_cast hc

theorem MarkSectionCover.routerCopy_count {n θ route route' s u}
    {e : @Execution n θ route s u} {e' : Execution θ route' s u}
    {i : Fin n} {p : Port} (cover : MarkSectionCover i p e)
    (copy : Execution.RouterCopy e e') (mapped : MarkSectionCover i p e') :
    mapped.count = cover.count := by
  have he := copy.mark_ledger i p
  rw [mapped.ledger_eq, cover.ledger_eq] at he
  have hc : (mapped.count : ℝ) = cover.count := by linarith
  exact_mod_cast hc

/-- A legal router retargeting can retain the exact move correspondence. -/
theorem Execution.retarget_router_copy {n θ route s u}
    (e : @Execution n θ route s u) (newRoute : Router n)
    (routeMatches : ∀ event ∈ e.ledger.emissions,
      route event.1 event.2 = newRoute event.1 event.2) :
    ∃ lifted : Execution θ newRoute s u, RouterCopy e lifted ∧
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  induction e with
  | nil => exact ⟨.nil _, .nil _, rfl, rfl⟩
  | cons move rest ih =>
    obtain ⟨tail, tailCopy, ledger, deliveries⟩ :=
      ih (fun event member => routeMatches event (List.mem_append_right _ member))
    cases move with
    | flow f =>
      refine ⟨.cons (.flow f) tail, .cons (.flow f) tailCopy, ?_, ?_⟩
      · change f.ledger.add tail.ledger = f.ledger.add rest.ledger
        rw [ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [deliveries]
    | jump j =>
      obtain ⟨j', jumpLedger, jumpDeliveries⟩ := j.retarget_router newRoute
        (fun event member => routeMatches event (List.mem_append_left _ member))
      refine ⟨.cons (.jump j') tail, .cons (.jump j j') tailCopy, ?_, ?_⟩
      · change j'.ledger.add tail.ledger = j.ledger.add rest.ledger
        rw [jumpLedger, ledger]
      · change j'.deliveries ++ tail.deliveries = j.deliveries ++ rest.deliveries
        rw [jumpDeliveries, deliveries]

end KernelR.Hybrid
