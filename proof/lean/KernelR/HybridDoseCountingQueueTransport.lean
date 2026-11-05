import KernelR.HybridDoseCounting
import KernelR.HybridLocalFutureFrame
import KernelR.HybridLocalSourceRestriction

/-! Complete-section covers follow exact physical traces when only pending
queues change. The copy relation retains every move and each actual flow path;
no memory or dose equality is used to manufacture a cover. -/
namespace KernelR.Hybrid

/-- A state transformation which changes only the pending queue. -/
structure PhysicalRequeue (n : ℕ) where
  apply : Snapshot n → Snapshot n
  time : ∀ s, (apply s).time = s.time
  values : ∀ s, (apply s).x = s.x
  main : ∀ s, (apply s).main = s.main
  aux : ∀ s, (apply s).aux = s.aux
  raw : ∀ s, (apply s).raw = s.raw

inductive Move.RequeueCopy {n θ route route'} (F : PhysicalRequeue n) :
    {s u : Snapshot n} → Move θ route s u → Move θ route' (F.apply s) (F.apply u) → Prop
  | flow {s u} (f : Flow θ s u) (g : Flow θ (F.apply s) (F.apply u))
      (path : g.path = f.path) : RequeueCopy F (.flow f) (.flow g)
  | jump {s u} (j : Jump route s u) (j' : Jump route' (F.apply s) (F.apply u)) :
      RequeueCopy F (.jump j) (.jump j')

inductive Execution.RequeueCopy {n θ route route'} (F : PhysicalRequeue n) :
    {s u : Snapshot n} → Execution θ route s u →
      Execution θ route' (F.apply s) (F.apply u) → Prop
  | nil (s) : RequeueCopy F (.nil s) (.nil (F.apply s))
  | cons {s v u} {move : Move θ route s v}
      {move' : Move θ route' (F.apply s) (F.apply v)}
      {rest : Execution θ route v u} {rest' : Execution θ route' (F.apply v) (F.apply u)}
      (step : Move.RequeueCopy F move move') (tail : RequeueCopy F rest rest') :
      RequeueCopy F (.cons move rest) (.cons move' rest')

theorem Execution.RequeueCopy.split {n θ route route' s v u} {F : PhysicalRequeue n}
    (first : @Execution n θ route s v) (rest : Execution θ route v u)
    {whole : Execution θ route' (F.apply s) (F.apply u)}
    (copy : RequeueCopy F (first.append rest) whole) :
    ∃ first' : Execution θ route' (F.apply s) (F.apply v),
      ∃ rest' : Execution θ route' (F.apply v) (F.apply u),
      whole = first'.append rest' ∧ RequeueCopy F first first' ∧ RequeueCopy F rest rest' := by
  induction first with
  | nil => exact ⟨.nil _, whole, rfl, .nil _, copy⟩
  | cons move tail ih =>
    cases copy with
    | cons step tailCopy =>
      obtain ⟨initial, suffix, same, left, right⟩ := ih rest tailCopy
      exact ⟨.cons _ initial, suffix, by rw [same]; rfl, .cons step left, right⟩

theorem Execution.RequeueCopy.allStates {n θ route route' s u} {F : PhysicalRequeue n}
    {e : @Execution n θ route s u} {e' : Execution θ route' (F.apply s) (F.apply u)}
    (copy : RequeueCopy F e e') (P : Snapshot n → Prop)
    (h : e.AllStates (fun v => P (F.apply v))) : e'.AllStates P := by
  induction copy with
  | nil => exact h
  | cons step tail ih => exact ⟨h.1, ih h.2⟩

theorem Execution.RequeueCopy.errorExposed {n θ route route' s u} {F : PhysicalRequeue n}
    {e : @Execution n θ route s u} {e' : Execution θ route' (F.apply s) (F.apply u)}
    (copy : RequeueCopy F e e') (i : Fin n) (p : Port) (h : e.ErrorExposed i p) :
    e'.ErrorExposed i p := by
  induction copy with
  | nil => trivial
  | cons step tail ih =>
    cases step with
    | flow f g same =>
      exact ⟨by simpa only [ErrorOpen, F.aux, F.main, F.time, same] using h.1, ih h.2⟩
    | jump j j' => exact ih h

theorem Execution.RequeueCopy.markExposed {n θ route route' s u} {F : PhysicalRequeue n}
    {e : @Execution n θ route s u} {e' : Execution θ route' (F.apply s) (F.apply u)}
    (copy : RequeueCopy F e e') (i : Fin n) (p : Port) (h : e.MarkExposed i p) :
    e'.MarkExposed i p := by
  induction copy with
  | nil => trivial
  | cons step tail ih =>
    cases step with
    | flow f g same =>
      exact ⟨by simpa only [MarkOpen, F.aux, F.main, F.time, same] using h.1, ih h.2⟩
    | jump j j' => exact ih h

/-- Transport every real entry, exposed span and exit of an ERROR cover. -/
theorem ErrorSectionCover.requeueCopy_exists {n θ route s u}
    {e : @Execution n θ route s u} {i : Fin n} {p : Port}
    (cover : ErrorSectionCover i p e) {route' : Router n} {F : PhysicalRequeue n}
    {e' : Execution θ route' (F.apply s) (F.apply u)} (copy : Execution.RequeueCopy F e e') :
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
      | flow f g same =>
        refine ⟨.inactive (.flow g) _ ?_ mapped⟩
        simpa only [Move.ErrorInactive, F.aux, F.main] using physical
      | jump j j' => exact ⟨.inactive (.jump j') _ trivial mapped⟩
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    cases copy with
    | cons step suffixCopy =>
      cases step with
      | jump _ entry' =>
        obtain ⟨span', suffix', same, spanCopy, restCopy⟩ :=
          Execution.RequeueCopy.split span (.cons (.jump exit) rest) suffixCopy
        cases same
        cases restCopy with
        | cons exitCopy tailCopy =>
          cases exitCopy with
          | jump _ exit' =>
            obtain ⟨mapped⟩ := ih tailCopy
            refine ⟨.fullPhase entry' span' exit' _ ?_ ?_ ?_ ?_ ?_
              (spanCopy.errorExposed i p exposed) mapped⟩
            · simpa only [F.aux] using before
            · simpa only [F.aux] using entered
            · simpa only [F.aux] using leaving
            · simpa only [F.aux] using after
            · apply spanCopy.allStates
              simpa only [F.aux] using phase

/-- Independent port covers retain simultaneous and overlapping MARK sections. -/
theorem MarkSectionCover.requeueCopy_exists {n θ route s u}
    {e : @Execution n θ route s u} {i : Fin n} {p : Port}
    (cover : MarkSectionCover i p e) {route' : Router n} {F : PhysicalRequeue n}
    {e' : Execution θ route' (F.apply s) (F.apply u)} (copy : Execution.RequeueCopy F e e') :
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
      | flow f g same =>
        refine ⟨.inactive (.flow g) _ ?_ mapped⟩
        simpa only [Move.MarkInactive, F.aux, F.main] using physical
      | jump j j' => exact ⟨.inactive (.jump j') _ trivial mapped⟩
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    cases copy with
    | cons step suffixCopy =>
      cases step with
      | jump _ entry' =>
        obtain ⟨span', suffix', same, spanCopy, restCopy⟩ :=
          Execution.RequeueCopy.split span (.cons (.jump exit) rest) suffixCopy
        cases same
        cases restCopy with
        | cons exitCopy tailCopy =>
          cases exitCopy with
          | jump _ exit' =>
            obtain ⟨mapped⟩ := ih tailCopy
            refine ⟨.fullPhase entry' span' exit' _ ?_ ?_ ?_ ?_ ?_
              (spanCopy.markExposed i p exposed) mapped⟩
            · simpa only [F.aux] using before
            · simpa only [F.aux] using entered
            · simpa only [F.aux] using leaving
            · simpa only [F.aux] using after
            · apply spanCopy.allStates
              simpa only [F.aux] using phase

/-- Once the cover has been structurally transported, its count is unchanged. -/
theorem ErrorSectionCover.requeueCopy_count {n θ route route' s u} {F : PhysicalRequeue n}
    {e : @Execution n θ route s u} {e' : Execution θ route' (F.apply s) (F.apply u)}
    {i : Fin n} {p : Port} (cover : ErrorSectionCover i p e)
    (_copy : Execution.RequeueCopy F e e') (mapped : ErrorSectionCover i p e') :
    mapped.count = cover.count := by
  have h := e.gain_balance i p
  have h' := e'.gain_balance i p
  rw [cover.ledger_eq] at h
  rw [mapped.ledger_eq] at h'
  simp only [F.values] at h'
  have hc : (mapped.count : ℝ) = cover.count := by linarith
  exact_mod_cast hc

theorem Execution.RequeueCopy.mark_ledger {n θ route route' s u} {F : PhysicalRequeue n}
    {e : @Execution n θ route s u} {e' : Execution θ route' (F.apply s) (F.apply u)}
    (copy : RequeueCopy F e e') (i : Fin n) (p : Port) :
    e'.ledger.mark i p = e.ledger.mark i p := by
  induction copy with
  | nil => rfl
  | cons step tail ih =>
    cases step with
    | flow f g same =>
      have h : g.ledger.mark i p = f.ledger.mark i p := by
        simp only [Flow.ledger, F.time, same, markAct, F.aux, F.main]
      change g.ledger.mark i p + _ = f.ledger.mark i p + _
      rw [h, ih]
    | jump j j' =>
      change j'.ledger.mark i p + _ = j.ledger.mark i p + _
      rw [j'.no_mark_actuation i p, j.no_mark_actuation i p, ih]

theorem MarkSectionCover.requeueCopy_count {n θ route route' s u} {F : PhysicalRequeue n}
    {e : @Execution n θ route s u} {e' : Execution θ route' (F.apply s) (F.apply u)}
    {i : Fin n} {p : Port} (cover : MarkSectionCover i p e)
    (copy : Execution.RequeueCopy F e e') (mapped : MarkSectionCover i p e') :
    mapped.count = cover.count := by
  have he := copy.mark_ledger i p
  rw [mapped.ledger_eq, cover.ledger_eq] at he
  have hc : (mapped.count : ℝ) = cover.count := by linarith
  exact_mod_cast hc

noncomputable def appendPendingRequeue {n} (future : List (Delivery n)) : PhysicalRequeue n :=
  ⟨fun s => appendPending s future, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩

noncomputable def retainSourcesRequeue {n} (cutoff : ℝ) : PhysicalRequeue n :=
  ⟨retainSourcesThrough cutoff, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩

theorem Execution.appendFuture_emptyRoute_copy {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u) (future : List (Delivery n))
    (later : ∀ d ∈ future, u.time ≤ d.due) :
    ∃ lifted : Execution θ (fun _ _ => []) (appendPending s future) (appendPending u future),
      RequeueCopy (appendPendingRequeue future) e lifted ∧
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  induction e with
  | nil => exact ⟨.nil _, .nil _, rfl, rfl⟩
  | @cons s v u move rest ih =>
    obtain ⟨tail, tailCopy, ledger, deliveries⟩ := ih later
    cases move with
    | flow f =>
      let g := f.appendFuture future (fun d hd => rest.time_monotone.trans (later d hd))
      refine ⟨.cons (.flow g) tail, .cons (Move.RequeueCopy.flow (F := appendPendingRequeue future) f g rfl) tailCopy, ?_, ?_⟩
      · change g.ledger.add tail.ledger = f.ledger.add rest.ledger
        rw [ledger, f.appendFuture_ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [deliveries]
    | jump j =>
      obtain ⟨g, jumpLedger, jumpDeliveries⟩ := j.appendFuture_emptyRoute future
      refine ⟨.cons (.jump g) tail, .cons (Move.RequeueCopy.jump (F := appendPendingRequeue future) j g) tailCopy, ?_, ?_⟩
      · change g.ledger.add tail.ledger = j.ledger.add rest.ledger
        rw [jumpLedger, ledger]
      · change g.deliveries ++ tail.deliveries = j.deliveries ++ rest.deliveries
        rw [jumpDeliveries, deliveries]

theorem Execution.retainSourcesThrough_emptyRoute_copy {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u) (cutoff : ℝ) (before : u.time ≤ cutoff) :
    ∃ lifted : Execution θ (fun _ _ => [])
      (retainSourcesThrough cutoff s) (retainSourcesThrough cutoff u),
      RequeueCopy (retainSourcesRequeue cutoff) e lifted ∧
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  induction e with
  | nil => exact ⟨.nil _, .nil _, rfl, rfl⟩
  | @cons s v u move rest ih =>
    obtain ⟨tail, tailCopy, ledger, deliveries⟩ := ih before
    cases move with
    | flow f =>
      let g := f.retainSourcesThrough cutoff
      refine ⟨.cons (.flow g) tail, .cons (Move.RequeueCopy.flow (F := retainSourcesRequeue cutoff) f g rfl) tailCopy, ?_, ?_⟩
      · change g.ledger.add tail.ledger = f.ledger.add rest.ledger
        rw [ledger, f.retainSourcesThrough_ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [deliveries]
    | jump j =>
      have firstDate : s.time ≤ cutoff := by
        rw [← j.time_unchanged]
        exact rest.time_monotone.trans before
      obtain ⟨g, jumpLedger, jumpDeliveries⟩ := j.retainSourcesThrough_emptyRoute cutoff firstDate
      refine ⟨.cons (.jump g) tail, .cons (Move.RequeueCopy.jump (F := retainSourcesRequeue cutoff) j g) tailCopy, ?_, ?_⟩
      · change g.ledger.add tail.ledger = j.ledger.add rest.ledger
        rw [jumpLedger, ledger]
      · change g.deliveries ++ tail.deliveries = j.deliveries ++ rest.deliveries
        rw [jumpDeliveries, deliveries]

/-- One queue-framed witness retains all port covers simultaneously. -/
theorem Execution.appendFuture_section_covers {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u)
    (errors : ∀ i p, ErrorSectionCover i p e) (marks : ∀ i p, MarkSectionCover i p e)
    (future : List (Delivery n)) (later : ∀ d ∈ future, u.time ≤ d.due) :
    ∃ lifted : Execution θ (fun _ _ => []) (appendPending s future) (appendPending u future),
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries ∧
      (∀ i p, Nonempty (ErrorSectionCover i p lifted)) ∧
      (∀ i p, Nonempty (MarkSectionCover i p lifted)) := by
  obtain ⟨lifted, copy, ledger, deliveries⟩ := e.appendFuture_emptyRoute_copy future later
  exact ⟨lifted, ledger, deliveries, fun i p => (errors i p).requeueCopy_exists copy,
    fun i p => (marks i p).requeueCopy_exists copy⟩

/-- Source restriction retains all actual complete sections of its selected prefix. -/
theorem Execution.retainSourcesThrough_section_covers {n θ s u}
    (e : @Execution n θ (fun _ _ => []) s u)
    (errors : ∀ i p, ErrorSectionCover i p e) (marks : ∀ i p, MarkSectionCover i p e)
    (cutoff : ℝ) (before : u.time ≤ cutoff) :
    ∃ lifted : Execution θ (fun _ _ => [])
      (retainSourcesThrough cutoff s) (retainSourcesThrough cutoff u),
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries ∧
      (∀ i p, Nonempty (ErrorSectionCover i p lifted)) ∧
      (∀ i p, Nonempty (MarkSectionCover i p lifted)) := by
  obtain ⟨lifted, copy, ledger, deliveries⟩ := e.retainSourcesThrough_emptyRoute_copy cutoff before
  exact ⟨lifted, ledger, deliveries, fun i p => (errors i p).requeueCopy_exists copy,
    fun i p => (marks i p).requeueCopy_exists copy⟩

end KernelR.Hybrid
