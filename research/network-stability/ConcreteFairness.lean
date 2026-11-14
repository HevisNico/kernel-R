import FairMemory

namespace NetworkStability.AutonomousFeedback.Schedule

/-- A clean FIFO execution sampled after each dequeue. Its certified
counterpart has the same projected trajectory by the read-margin lemma. -/
def fifo (M : Model N P) (d : Nat) (seed : List P) : Execution M d seed where
  state n := run M d (fun _ => 0) n (start N seed)
  initial := rfl
  next := by
    intro n
    let s := run M d (fun _ => 0) n (start N seed)
    rw [run_add]
    change CertifiedTrace M d s (step M d 0 s)
    cases pending : s.pending with
    | nil =>
      have same : step M d 0 s = s := by simp [step, pending]
      rw [same]
      exact .nil _
    | cons p tail =>
      have same : { s with pending := p :: ([] ++ tail) } = s := by simp only [List.nil_append]; cases h : s; simp_all
      have room : RoutedCalendar.HasRoom (score M d s p) 0 0 := by
        unfold RoutedCalendar.HasRoom
        omega
      have tr := CertifiedTrace.cons [] tail p pending 0 0 0 (by decide) room
        (CertifiedTrace.nil (step M d 0 { s with pending := p :: ([] ++ tail) }))
      simpa only [same] using tr

private theorem clean_step (M : Model N P) (d : Nat) (s : State N P)
    (p : P) (rest : List P) (queue : s.pending = p :: rest) :
    project (step M d 0 s) = process M d (project s) p rest := by
  unfold project process step read emitted bump
  dsimp only
  simp only [queue]
  rfl

/-- Bounded residual paths for the strong diamond argument. -/
inductive BudgetPath (M : Model N P) (d : Nat) : Nat → Config N P → Config N P → Prop where
  | nil (n : Nat) (s : Config N P) : BudgetPath M d n s s
  | cons {n s t u} : Move M d s t → BudgetPath M d n t u → BudgetPath M d (n + 1) s u

theorem budget_transport {M : Model N P} {d n : Nat} {s t u : Config N P}
    (eq : Equivalent s t) (path : BudgetPath M d n s u) :
    ∃ v, BudgetPath M d n t v ∧ Equivalent u v := by
  induction path generalizing t with
  | nil n s => exact ⟨t, .nil n t, eq⟩
  | cons move _ ih =>
    obtain ⟨v, moved, same⟩ := move_transport M d eq move
    obtain ⟨last, tail, related⟩ := ih same
    exact ⟨last, .cons moved tail, related⟩

theorem path_has_budget {M : Model N P} {d : Nat} {s t : Config N P}
    (path : Path M d s t) : ∃ n, BudgetPath M d n s t := by
  induction path with
  | nil => exact ⟨0, .nil _ _⟩
  | cons move _ ih =>
    obtain ⟨n, budget⟩ := ih
    exact ⟨n + 1, .cons move budget⟩

private theorem budget_succ {M : Model N P} {d n : Nat} {s t : Config N P}
    (path : BudgetPath M d n s t) : BudgetPath M d (n + 1) s t := by
  induction path with
  | nil => exact .nil _ _
  | cons move _ ih => exact .cons move ih

private theorem strip_budget (M : Model N P) (d : Nat) (root : Config N P)
    (diamond : ∀ s, Path M d root s → Exclusive M s ∨ PairMargins M d s)
    {s a b : Config N P} (reach : Path M d root s) (step : Move M d s a)
    {n : Nat} (path : BudgetPath M d n s b) :
    ∃ u v, BudgetPath M d n a u ∧ (v = b ∨ Move M d b v) ∧ Equivalent u v := by
  induction path generalizing a with
  | nil n s => exact ⟨a, a, .nil n _, Or.inr step, ⟨List.Perm.refl _, rfl⟩⟩
  | @cons n t s' u next tail ih =>
    rcases local_diamond M d (diamond _ reach) step next with same | ⟨u', v', au, tv, related⟩
    · obtain ⟨last, moved, eq⟩ := budget_transport ⟨same.1.symm, same.2.symm⟩ tail
      exact ⟨last, _, budget_succ moved, Or.inl rfl, ⟨eq.1.symm, eq.2.symm⟩⟩
    · obtain ⟨last, finish, tailV, short, same⟩ :=
        ih (path_trans M d reach (.cons next (.nil _))) tv
      obtain ⟨endA, pathA, matchA⟩ := budget_transport ⟨related.1.symm, related.2.symm⟩ tailV
      exact ⟨endA, finish, .cons au pathA, short,
        ⟨matchA.1.symm.trans same.1, matchA.2.symm.trans same.2⟩⟩

/-- Commute a finite continuation past heads until FIFO serves its first
requested occurrence. The residual budget shrinks by one at that service. -/
private theorem catch_budget (M : Model N P) (d : Nat) (root : Config N P)
    (diamond : ∀ s, Path M d root s → Exclusive M s ∨ PairMargins M d s)
    (s : State N P) (reach : Path M d root (project s))
    (before : List P) (p : P) (after : List P) (queue : s.pending = before ++ p :: after)
    (n : Nat) (b : Config N P)
    (tail : BudgetPath M d n (process M d (project s) p (before ++ after)) b) :
    ∃ k u, BudgetPath M d n (project (run M d (fun _ => 0) k s)) u ∧
      ∀ i, b.writes i ≤ u.writes i := by
  induction before generalizing s after b with
  | nil =>
    refine ⟨1, b, ?_, fun _ => Nat.le_refl _⟩
    change BudgetPath M d n (project (step M d 0 s)) b
    rw [clean_step M d s p after queue]
    exact tail
  | cons q before ih =>
    let t := step M d 0 s
    let rest := before ++ after
    let ep := emitted M p (read M d (project s) p)
    let eq' := emitted M q (read M d (project s) q)
    let a := process M d (project s) p (q :: rest)
    let lifted := process M d (project t) p (before ++ (after ++ eq'))
    have mainEq : project t = process M d (project s) q (before ++ p :: after) :=
      clean_step M d s q _ queue
    have actual : Move M d (project s) (project t) := by
      rw [mainEq]
      exact .select _ _ _ (by change s.pending.Perm _; rw [queue]; exact List.Perm.refl _)
    by_cases same : p = q
    · subst q
      have related : Equivalent a (project t) := by
        rw [mainEq]
        exact process_equivalent M d rfl p List.perm_middle.symm
      obtain ⟨u, path, eq⟩ := budget_transport related tail
      exact ⟨1, u, path, fun i => Nat.le_of_eq (congrFun eq.2 i)⟩
    · let aNext := process M d a q (rest ++ ep)
      let bNext := process M d (process M d (project s) q (p :: rest)) p (rest ++ eq')
      have afterP : Move M d a aNext := .select _ _ _ (List.Perm.refl _)
      have tQueue : t.pending = before ++ p :: (after ++ eq') := by
        have eq := congrArg Config.pending mainEq
        change t.pending = (before ++ p :: after) ++ eq' at eq
        simpa only [List.append_assoc, List.cons_append] using eq
      have sPerm : (project s).pending.Perm (q :: p :: rest) := by
        change s.pending.Perm _
        rw [queue]
        exact List.perm_middle.cons q
      have memP : p ∈ (project s).pending := sPerm.mem_iff.mpr (by simp)
      have memQ : q ∈ (project s).pending := sPerm.mem_iff.mpr (by simp)
      have joined : Equivalent aNext bNext := by
        by_cases cells : M.cell p = M.cell q
        · rcases diamond _ reach with exclusive | margins
          · have nodup := ((sPerm.map M.cell).nodup_iff.mp exclusive)
            simp only [List.map_cons, cells] at nodup
            exact False.elim ((List.nodup_cons.mp nodup).1 (by simp))
          · exact two_occurrences_commute M d (project s) p q rest
              (read_after_room M d (project s) p q _ (margins p memP q memQ same cells))
              (read_after_room M d (project s) q p _ (margins q memQ p memP (Ne.symm same) cells.symm))
        · exact different_cells_commute M d (project s) p q rest cells
      have liftedEq : Equivalent lifted bNext := by
        apply process_equivalent M d
        · rw [mainEq]
          exact (process_equivalent M d rfl q List.perm_middle).2
        · exact List.Perm.of_eq (List.append_assoc _ _ _).symm
      have reachA : Path M d root a := path_trans M d reach
        (.cons (.select _ _ _ (by change s.pending.Perm _; rw [queue]; exact List.perm_middle)) (.nil _))
      obtain ⟨u, v, residual, short, uv⟩ := strip_budget M d root diamond reachA afterP tail
      obtain ⟨last, residual', ul⟩ := budget_transport
        ⟨joined.1.trans liftedEq.1.symm, joined.2.trans liftedEq.2.symm⟩ residual
      obtain ⟨k, finish, matched, counts⟩ :=
        ih t (path_trans M d reach (.cons actual (.nil _))) (after ++ eq') tQueue last residual'
      refine ⟨k + 1, finish, matched, fun i => ?_⟩
      have lower : b.writes i ≤ v.writes i := by
        rcases short with rfl | mv
        · exact Nat.le_refl _
        · exact move_writes_mono mv i
      exact Nat.le_trans lower (Nat.le_trans (Nat.le_of_eq (congrFun (uv.2.symm.trans ul.2) i)) (counts i))

theorem fifo_prefix (M : Model N P) (d : Nat) (s : State N P) (n : Nat) :
    Path M d (project s) (project (run M d (fun _ => 0) n s)) := by
  induction n generalizing s with
  | zero => exact .nil _
  | succ n ih =>
    cases queue : s.pending with
    | nil =>
      rw [run_empty M d _ _ s queue]
      exact .nil _
    | cons p tail =>
      rw [run]
      have pick : Move M d (project s) (project (step M d 0 s)) := by
        rw [clean_step M d s p tail queue]
        exact .select _ _ _ (by change s.pending.Perm _; rw [queue])
      exact .cons pick (ih _)

theorem fifo_dominates (M : Model N P) (d : Nat) (root : Config N P)
    (diamond : ∀ s, Path M d root s → Exclusive M s ∨ PairMargins M d s)
    (s : State N P) (reach : Path M d root (project s))
    {n : Nat} {b : Config N P} (path : BudgetPath M d n (project s) b) :
    ∃ k, ∀ i, b.writes i ≤ (run M d (fun _ => 0) k s).writes i := by
  induction n generalizing s b with
  | zero => cases path; exact ⟨0, fun _ => Nat.le_refl _⟩
  | succ n ih =>
    cases path with
    | nil => exact ⟨0, fun _ => Nat.le_refl _⟩
    | cons first tail =>
      cases first with
      | select p rest available =>
        have mem : p ∈ s.pending := available.mem_iff.mpr (by simp)
        obtain ⟨before, after, queue⟩ := List.append_of_mem mem
        have split : s.pending.Perm (p :: (before ++ after)) := by
          rw [queue]
          exact List.perm_middle
        have same := process_equivalent M d (s := project s) (t := project s) rfl p
          (available.symm.trans split).cons_inv
        obtain ⟨end', toEnd, endEq⟩ := budget_transport same tail
        obtain ⟨k, u, rem, lower⟩ :=
          catch_budget M d root diamond s reach before p after queue n end' toEnd
        obtain ⟨j, counts⟩ := ih _ (path_trans M d reach (fifo_prefix M d s k)) rem
        refine ⟨k + j, fun i => ?_⟩
        rw [run_add]
        exact Nat.le_trans (Nat.le_of_eq (congrFun endEq.2 i)) (Nat.le_trans (lower i) (counts i))

theorem fifo_write_fair (M : Model N P) (d : Nat) (seed : List P)
    (diamond : ∀ s, Path M d (seedConfig N seed) s → Exclusive M s ∨ PairMargins M d s) :
    WriteFair (fifo M d seed) := by
  intro k t path i
  obtain ⟨n, sized⟩ := path_has_budget path
  obtain ⟨j, writes⟩ := fifo_dominates M d _ diamond _ (reaches (fifo M d seed) k) sized
  refine ⟨k + j, Nat.le_add_right _ _, ?_⟩
  change t.writes i ≤ (run M d (fun _ => 0) (k + j) (start N seed)).writes i
  rw [run_add]
  exact writes i

/-- The concrete rule applies to noisy FIFO when every nominal prefix is
certified. Compare with the clean FIFO at both the starting cut and the catch. -/
theorem noisy_fifo_write_fair (M : Model N P) (d : Nat) (seed : List P)
    (diamond : ∀ s, Path M d (seedConfig N seed) s → Exclusive M s ∨ PairMargins M d s)
    (lo hi error : Nat → Int) (within : ∀ k, lo k ≤ error k ∧ error k ≤ hi k)
    (margins : ∀ n, NominalMargins M d lo hi n (start N seed))
    (k : Nat) (t : Config N P)
    (path : Path M d (project (run M d error k (start N seed))) t) :
    ∃ j, k ≤ j ∧ ∀ i, t.writes i ≤ (run M d error j (start N seed)).writes i := by
  have clean n := run_eq_of_margins M d lo hi error within n (start N seed) (margins n)
  rw [clean k] at path
  obtain ⟨n, sized⟩ := path_has_budget path
  obtain ⟨j, writes⟩ := fifo_dominates M d _ diamond _ (reaches (fifo M d seed) k) sized
  refine ⟨k + j, Nat.le_add_right _ _, ?_⟩
  rw [clean, run_add]
  exact writes

end NetworkStability.AutonomousFeedback.Schedule
