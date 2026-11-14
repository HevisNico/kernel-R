import ScheduleCounterexample

namespace NetworkStability.AutonomousFeedback.Schedule

/-- The data used by a zero-error transition. The chronological log is
observable, but it is not used as an input to a zero-error probe. -/
structure Config (N : Nat) (P : Type) where
  pending : List P
  writes : Fin N → Nat

def project (s : State N P) : Config N P := ⟨s.pending, s.writes⟩

def Equivalent (s t : Config N P) : Prop :=
  s.pending.Perm t.pending ∧ s.writes = t.writes

def read (M : Model N P) (d : Nat) (s : Config N P) (p : P) : Bool :=
  fires M d ⟨s.pending, s.writes, []⟩ p 0

def emitted (M : Model N P) (p : P) (fire : Bool) : List P :=
  if fire then M.route p else []

def bump (M : Model N P) (p : P) (fire : Bool) (w : Fin N → Nat) (i : Fin N) : Nat :=
  w i + if i = M.cell p ∧ fire = false then 1 else 0

def process (M : Model N P) (d : Nat) (s : Config N P) (p : P) (rest : List P) : Config N P :=
  let fire := read M d s p
  ⟨rest ++ emitted M p fire, bump M p fire s.writes⟩

/-- The scheduler can select any available occurrence. The queue order
abstracts the order of the remaining occurrences. -/
inductive Move (M : Model N P) (d : Nat) : Config N P → Config N P → Prop where
  | select (s : Config N P) (p : P) (rest : List P) (mem : s.pending.Perm (p :: rest)) :
      Move M d s (process M d s p rest)

inductive Path (M : Model N P) (d : Nat) : Config N P → Config N P → Prop where
  | nil (s : Config N P) : Path M d s s
  | cons {s t u} : Move M d s t → Path M d t u → Path M d s u

theorem select_projects (M : Model N P) (d : Nat) {s t : State N P}
    (step : ScheduleCounterexample.Select M d 0 s t) :
    Move M d (project s) (project t) := by
  cases step with
  | process before p after queue =>
    have mem : (project s).pending.Perm (p :: (before ++ after)) := by
      change s.pending.Perm _
      rw [queue]
      exact List.perm_middle
    exact Move.select _ _ _ mem

theorem trace_projects (M : Model N P) (d : Nat) {s t : State N P}
    (trace : ScheduleCounterexample.Trace M d 0 s t) :
    Path M d (project s) (project t) := by
  induction trace with
  | nil s => exact .nil _
  | cons step _ ih => exact .cons (select_projects M d step) ih

theorem read_eq (M : Model N P) (d : Nat) (p : P) (s t : Config N P)
    (same : s.writes (M.cell p) = t.writes (M.cell p)) :
    read M d s p = read M d t p := by
  unfold read fires score
  dsimp only
  simp only [same]

theorem process_equivalent (M : Model N P) (d : Nat) {s t : Config N P}
    (same : s.writes = t.writes) (p : P) {a b : List P} (rest : a.Perm b) :
    Equivalent (process M d s p a) (process M d t p b) := by
  have fire := read_eq M d p s t (congrFun same _)
  unfold Equivalent process
  dsimp only
  rw [fire, same]
  exact ⟨rest.append_right _, rfl⟩

theorem move_transport (M : Model N P) (d : Nat) {s t u : Config N P}
    (eq : Equivalent s t) (step : Move M d s u) :
    ∃ v, Move M d t v ∧ Equivalent u v := by
  cases step with
  | select p rest available =>
    exact ⟨_, .select t p rest (eq.1.symm.trans available),
      process_equivalent M d eq.2 p (List.Perm.refl _)⟩

theorem path_transport (M : Model N P) (d : Nat) {s t u : Config N P}
    (eq : Equivalent s t) (path : Path M d s u) :
    ∃ v, Path M d t v ∧ Equivalent u v := by
  induction path generalizing t with
  | nil s => exact ⟨t, .nil _, eq⟩
  | cons step _ ih =>
    obtain ⟨v, move, same⟩ := move_transport M d eq step
    obtain ⟨last, tail, join⟩ := ih same
    exact ⟨last, .cons move tail, join⟩

private theorem bump_commute (M : Model N P) (p q : P) (a b : Bool) (w : Fin N → Nat) :
    bump M q b (bump M p a w) = bump M p a (bump M q b w) := by
  funext i
  unfold bump
  omega

/-- Exact two-occurrence diamond at fixed decisions. The two appended route
lists may have opposite order, so the queue conclusion is a permutation. -/
theorem two_occurrences_commute (M : Model N P) (d : Nat)
    (s : Config N P) (p q : P) (rest : List P)
    (pStable : read M d (process M d s q (p :: rest)) p = read M d s p)
    (qStable : read M d (process M d s p (q :: rest)) q = read M d s q) :
    Equivalent
      (process M d (process M d s p (q :: rest)) q (rest ++ emitted M p (read M d s p)))
      (process M d (process M d s q (p :: rest)) p (rest ++ emitted M q (read M d s q))) := by
  unfold Equivalent
  simp only [process] at pStable qStable ⊢
  rw [pStable, qStable]
  constructor
  · simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := emitted M p (read M d s p))
        (l₂ := emitted M q (read M d s q))).append_left rest
  · exact bump_commute M p q _ _ s.writes

theorem different_cells_commute (M : Model N P) (d : Nat)
    (s : Config N P) (p q : P) (rest : List P) (different : M.cell p ≠ M.cell q) :
    Equivalent
      (process M d (process M d s p (q :: rest)) q (rest ++ emitted M p (read M d s p)))
      (process M d (process M d s q (p :: rest)) p (rest ++ emitted M q (read M d s q))) := by
  apply two_occurrences_commute
  · apply read_eq
    simp [process, bump, different]
  · apply read_eq
    simp [process, bump, Ne.symm different]

/-- At the current nominal count, allow k additional same-cell writes and
an error in [lo, hi]. The silence margin spends d*k; a write only helps FIRE. -/
def InterleavingRoom (score : Int) (lo hi : Int) (d k : Nat) : Prop :=
  (score < 0 ∧ score + (d : Int) * k + hi < 0) ∨
  (0 ≤ score ∧ 0 ≤ score + lo)

theorem interleaving_decision (score lo hi : Int) (d k added : Nat) (e : Int)
    (count : added ≤ k) (within : lo ≤ e ∧ e ≤ hi)
    (room : InterleavingRoom score lo hi d k) :
    decide (0 ≤ score + (d : Int) * added + e) = decide (0 ≤ score) := by
  have order : (added : Int) ≤ (k : Int) := by omega
  have inc := Int.mul_le_mul_of_nonneg_left order (show 0 ≤ (d : Int) by omega)
  have nonneg : 0 ≤ (d : Int) * (added : Int) := Int.mul_nonneg (by omega) (by omega)
  rcases room with ⟨silent, upper⟩ | ⟨fire, lower⟩
  · have guarded : ¬ 0 ≤ score + (d : Int) * added + e := by omega
    simp [guarded, silent]
  · have guarded : 0 ≤ score + (d : Int) * added + e := by omega
    simp [guarded, fire]

def cleanScore (M : Model N P) (d : Nat) (s : Config N P) (p : P) : Int :=
  score M d ⟨s.pending, s.writes, []⟩ p

theorem read_after_room (M : Model N P) (d : Nat)
    (s : Config N P) (p q : P) (rest : List P)
    (room : InterleavingRoom (cleanScore M d s p) 0 0 d 1) :
    read M d (process M d s q rest) p = read M d s p := by
  let added : Nat := if M.cell p = M.cell q ∧ read M d s q = false then 1 else 0
  have addedBound : added ≤ 1 := by unfold added; split <;> decide
  have scoreEq : cleanScore M d (process M d s q rest) p =
      cleanScore M d s p + (d : Int) * added := by
    change M.bias p + (d : Int) * ((s.writes (M.cell p) + added : Nat) : Int) +
        (M.drive p : Int) = _
    unfold cleanScore score
    rw [Int.natCast_add, Int.mul_add]
    dsimp only
    omega
  change decide (0 ≤ cleanScore M d (process M d s q rest) p + 0) =
    decide (0 ≤ cleanScore M d s p + 0)
  simpa only [scoreEq, Int.add_zero] using interleaving_decision _ _ _ d 1 added 0 addedBound (by decide) room

def Exclusive (M : Model N P) (s : Config N P) : Prop :=
  (s.pending.map M.cell).Nodup

/-- B only concerns distinct probe types on the same cell. Identical types
have the same immediate decision and their remainders agree up to permutation. -/
def PairMargins (M : Model N P) (d : Nat) (s : Config N P) : Prop :=
  ∀ p ∈ s.pending, ∀ q ∈ s.pending, p ≠ q → M.cell p = M.cell q →
    InterleavingRoom (cleanScore M d s p) 0 0 d 1

private theorem can_pick (s : Config N P) {p : P} {rest : List P}
    (h : s.pending.Perm (p :: rest)) : p ∈ s.pending :=
  h.mem_iff.mpr (by simp)

private theorem residual {p q : P} {a b : List P}
    (perm : (p :: a).Perm (q :: b)) (ne : p ≠ q) :
    ∃ rest, a.Perm (q :: rest) ∧ b.Perm (p :: rest) := by
  classical
  letI : BEq P := instBEqOfDecidableEq
  have mem : q ∈ p :: a := perm.mem_iff.mpr (by simp)
  have inside : q ∈ a := (List.mem_cons.mp mem).resolve_left (Ne.symm ne)
  have after := List.perm_cons_erase inside
  have both : (q :: p :: a.erase q).Perm (q :: b) :=
    ((List.Perm.swap p q _).trans (after.symm.cons p)).trans perm
  exact ⟨_, after, both.cons_inv.symm⟩

def Joinable (M : Model N P) (d : Nat) (a b : Config N P) : Prop :=
  ∃ u v, Path M d a u ∧ Path M d b v ∧ Equivalent u v

/-- Both sides of the local diamond take at most one additional step. -/
def ShortDiamond (M : Model N P) (d : Nat) (a b : Config N P) : Prop :=
  Equivalent a b ∨ ∃ u v, Move M d a u ∧ Move M d b v ∧ Equivalent u v

/-- A or B gives a local diamond modulo queue permutation. A may be
imposed as a reachable-state invariant; initial exclusivity alone is weaker. -/
theorem local_diamond (M : Model N P) (d : Nat) {s a b : Config N P}
    (hyp : Exclusive M s ∨ PairMargins M d s)
    (left : Move M d s a) (right : Move M d s b) : ShortDiamond M d a b := by
  cases left with
  | select p ps availableP =>
    cases right with
    | select q qs availableQ =>
      have heads := availableP.symm.trans availableQ
      by_cases same : p = q
      · subst q
        exact Or.inl (process_equivalent M d rfl p heads.cons_inv)
      · obtain ⟨rest, pTail, qTail⟩ := residual heads same
        have pStep : (process M d s p ps).pending.Perm
            (q :: (rest ++ emitted M p (read M d s p))) :=
          pTail.append_right _
        have qStep : (process M d s q qs).pending.Perm
            (p :: (rest ++ emitted M q (read M d s q))) :=
          qTail.append_right _
        refine Or.inr ⟨_, _, .select _ _ _ pStep, .select _ _ _ qStep, ?_⟩
        by_cases different : M.cell p = M.cell q
        · rcases hyp with exclusive | margins
          · have perm : (s.pending.map M.cell).Perm
                (M.cell p :: M.cell q :: rest.map M.cell) :=
              (availableP.trans (pTail.cons p)).map M.cell
            have nodup := perm.nodup_iff.mp exclusive
            rw [different] at nodup
            exact False.elim ((List.nodup_cons.mp nodup).1 (by simp))
          · exact two_occurrences_commute M d s p q rest
              (read_after_room M d s p q _ (margins p (can_pick s availableP) q
                (can_pick s availableQ) same different))
              (read_after_room M d s q p _ (margins q (can_pick s availableQ) p
                (can_pick s availableP) (Ne.symm same) different.symm))
        · exact different_cells_commute M d s p q rest different

theorem path_trans (M : Model N P) (d : Nat) {s a b : Config N P}
    (p : Path M d s a) (q : Path M d a b) : Path M d s b := by
  induction p with
  | nil => exact q
  | cons step _ ih => exact .cons step (ih q)

private theorem mass_perm (weight : P → Nat) {a b : List P} (p : a.Perm b) :
    mass weight a = mass weight b := by
  induction p with
  | nil => rfl
  | cons x _ ih => exact congrArg (weight x + ·) ih
  | swap x y rest => simp [mass, Nat.add_left_comm]
  | trans _ _ ab bc => exact ab.trans bc

theorem move_decreases (M : Model N P) (d eta : Nat) (w : P → Nat)
    (margin : ∀ p, mass w (M.route p) + eta ≤ w p)
    {s t : Config N P} (step : Move M d s t) :
    mass w t.pending + eta ≤ mass w s.pending := by
  cases step with
  | select p tail available =>
    rw [mass_perm w available]
    have bound := margin p
    change mass w (tail ++ emitted M p (read M d s p)) + eta ≤ w p + mass w tail
    rw [mass_append]
    cases read M d s p <;> simp [emitted, mass] at bound ⊢ <;> omega

/-- Ranked induction is Newman's lemma specialized to queue permutation.
The local condition is required at every reachable configuration. -/
theorem newman (Q W eta : Nat) {N : Nat} {P : Type} (M : Model N P) (d : Nat)
    (seed : List P) (cert : Certificate Q W eta M seed)
    (admissible : ∀ s, Path M d ⟨seed, fun _ => 0⟩ s → Exclusive M s ∨ PairMargins M d s)
    {a b : Config N P} (pa : Path M d ⟨seed, fun _ => 0⟩ a)
    (pb : Path M d ⟨seed, fun _ => 0⟩ b) : Joinable M d a b := by
  let root : Config N P := ⟨seed, fun _ => 0⟩
  have inductionClaim (rank : Nat) : ∀ s : Config N P,
      mass cert.weight s.pending = rank → Path M d root s →
      ∀ a b, Path M d s a → Path M d s b → Joinable M d a b := by
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro s rankEq reach a b pa pb
      cases pa with
      | nil => exact ⟨b, b, pb, .nil _, ⟨List.Perm.refl _, rfl⟩⟩
      | cons first restA =>
        rename_i left
        cases pb with
        | nil => exact ⟨a, a, .nil _, .cons first restA, ⟨List.Perm.refl _, rfl⟩⟩
        | cons second restB =>
          rename_i right
          have leftRank : mass cert.weight left.pending < rank := by
            have := move_decreases M d eta cert.weight cert.scalar first
            have := cert.eta_pos
            omega
          have rightRank : mass cert.weight right.pending < rank := by
            have := move_decreases M d eta cert.weight cert.scalar second
            have := cert.eta_pos
            omega
          have leftReach := path_trans M d reach (.cons first (.nil _))
          have rightReach := path_trans M d reach (.cons second (.nil _))
          have diamond : Joinable M d left right := by
            rcases local_diamond M d (admissible s reach) first second with same | ⟨u, v, lu, rv, uv⟩
            · exact ⟨left, right, .nil _, .nil _, same⟩
            · exact ⟨u, v, .cons lu (.nil _), .cons rv (.nil _), uv⟩
          obtain ⟨u, v, lu, rv, uv⟩ := diamond
          obtain ⟨a', u', aa', uu', sameA⟩ := ih _ leftRank _ rfl leftReach a u restA lu
          obtain ⟨v', vv', sameV⟩ := path_transport M d uv uu'
          have rightToV' := path_trans M d rv vv'
          obtain ⟨b', v'', bb', v'v'', sameB⟩ :=
            ih _ rightRank _ rfl rightReach b v' restB rightToV'
          have cross : Equivalent v' a' :=
            ⟨sameV.1.symm.trans sameA.1.symm, sameV.2.symm.trans sameA.2.symm⟩
          obtain ⟨last, a'last, sameLast⟩ := path_transport M d cross v'v''
          exact ⟨last, b', path_trans M d aa' a'last, bb',
            ⟨sameLast.1.symm.trans sameB.1.symm, sameLast.2.symm.trans sameB.2.symm⟩⟩
  exact inductionClaim _ root rfl (.nil _) a b pa pb

/-- Strip one step past a finite path using the strong local diamond.
This argument does not use a decreasing rank. -/
theorem strip_step (M : Model N P) (d : Nat) (root : Config N P)
    (admissible : ∀ s, Path M d root s → Exclusive M s ∨ PairMargins M d s)
    {s a b : Config N P} (reach : Path M d root s)
    (step : Move M d s a) (path : Path M d s b) :
    ∃ u v, Path M d a u ∧ (v = b ∨ Move M d b v) ∧ Equivalent u v := by
  induction path generalizing a with
  | nil => exact ⟨a, a, .nil _, Or.inr step, ⟨List.Perm.refl _, rfl⟩⟩
  | cons next tail ih =>
    rcases local_diamond M d (admissible _ reach) step next with same | ⟨u, v, au, tv, uv⟩
    · obtain ⟨last, path, eq⟩ := path_transport M d ⟨same.1.symm, same.2.symm⟩ tail
      exact ⟨last, _, path, Or.inl rfl, ⟨eq.1.symm, eq.2.symm⟩⟩
    · obtain ⟨last, finish, tailV, short, same⟩ := ih (path_trans M d reach (.cons next (.nil _))) tv
      obtain ⟨endA, pathA, matchA⟩ := path_transport M d ⟨uv.1.symm, uv.2.symm⟩ tailV
      exact ⟨endA, finish, .cons au pathA, short,
        ⟨matchA.1.symm.trans same.1, matchA.2.symm.trans same.2⟩⟩

/-- The stronger diamond also joins any two finite prefixes without a
termination premise. It gives no fairness or progress of infinite schedules. -/
theorem finite_prefix_confluence (M : Model N P) (d : Nat) (root : Config N P)
    (admissible : ∀ s, Path M d root s → Exclusive M s ∨ PairMargins M d s)
    {s a b : Config N P} (reach : Path M d root s)
    (pa : Path M d s a) (pb : Path M d s b) : Joinable M d a b := by
  induction pa generalizing b with
  | nil => exact ⟨b, b, pb, .nil _, ⟨List.Perm.refl _, rfl⟩⟩
  | cons step tail ih =>
    obtain ⟨u, v, toU, short, uv⟩ := strip_step M d root admissible reach step pb
    obtain ⟨a', u', aa', uu', au⟩ := ih (path_trans M d reach (.cons step (.nil _))) toU
    obtain ⟨v', vv', eq⟩ := path_transport M d uv uu'
    have bv : Path M d b v := by
      rcases short with rfl | move
      · exact .nil _
      · exact .cons move (.nil _)
    exact ⟨a', v', aa', path_trans M d bv vv', ⟨au.1.trans eq.1, au.2.trans eq.2⟩⟩

theorem path_from_empty (M : Model N P) (d : Nat) {s t : Config N P}
    (empty : s.pending = []) (path : Path M d s t) : t = s := by
  cases path with
  | nil => rfl
  | cons step _ =>
    cases step with
    | select p rest available =>
      rw [empty] at available
      exact False.elim (List.not_perm_nil_cons p rest available)

/-- Two finite prefixes that are write-free under every continuation have
the same memory, even when pending FIRE traffic can continue forever. -/
theorem write_closed_memory_unique (M : Model N P) (d : Nat) (root : Config N P)
    (admissible : ∀ s, Path M d root s → Exclusive M s ∨ PairMargins M d s)
    {a b : Config N P} (pa : Path M d root a) (pb : Path M d root b)
    (closedA : ∀ t, Path M d a t → t.writes = a.writes)
    (closedB : ∀ t, Path M d b t → t.writes = b.writes) :
    a.writes = b.writes := by
  obtain ⟨u, v, au, bv, eq⟩ := finite_prefix_confluence M d root admissible (.nil _) pa pb
  exact (closedA u au).symm.trans (eq.2.trans (closedB v bv))

/-- Comparing exhausted runs gives equality of every stored value. -/
theorem terminal_memory_unique (Q W eta d : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Certificate Q W eta M seed)
    (admissible : ∀ s, Path M d ⟨seed, fun _ => 0⟩ s → Exclusive M s ∨ PairMargins M d s)
    {a b : Config N P} (pa : Path M d ⟨seed, fun _ => 0⟩ a)
    (pb : Path M d ⟨seed, fun _ => 0⟩ b) (emptyA : a.pending = []) (emptyB : b.pending = [])
    (base : Fin N → Nat) :
    a.writes = b.writes ∧ (fun i => base i + d * a.writes i) =
      (fun i => base i + d * b.writes i) := by
  obtain ⟨u, v, au, bv, eq⟩ := newman Q W eta M d seed cert admissible pa pb
  rw [path_from_empty M d emptyA au, path_from_empty M d emptyB bv] at eq
  exact ⟨eq.2, by rw [eq.2]⟩

/-- Every reachable configuration can be drained under the scalar rank. -/
theorem reaches_empty (eta : Nat) (M : Model N P) (d : Nat) (w : P → Nat)
    (pos : 0 < eta) (margin : ∀ p, mass w (M.route p) + eta ≤ w p)
    (s : Config N P) : ∃ t, Path M d s t ∧ t.pending = [] := by
  have aux (rank : Nat) : ∀ s : Config N P, mass w s.pending = rank →
      ∃ t, Path M d s t ∧ t.pending = [] := by
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro s rankEq
      cases queue : s.pending with
      | nil => exact ⟨s, .nil _, queue⟩
      | cons p tail =>
        let u := process M d s p tail
        have next : Move M d s u := .select s p tail (queue ▸ List.Perm.refl _)
        have lower : mass w u.pending < rank := by
          have := move_decreases M d eta w margin next
          omega
        obtain ⟨t, path, empty⟩ := ih _ lower u rfl
        exact ⟨t, .cons next path, empty⟩
  exact aux _ s rfl

/-- A singleton seed remains exclusive if each FIRE emits at most one probe. -/
theorem singleton_exclusive (M : Model N P) (d : Nat)
    (capacity : ∀ p, (M.route p).length ≤ 1)
    {s t : Config N P} (path : Path M d s t) (initial : s.pending.length ≤ 1) :
    Exclusive M t := by
  have small : t.pending.length ≤ 1 := by
    induction path with
    | nil => exact initial
    | cons next _ ih =>
      apply ih
      cases next with
      | select p tail perm =>
        have ht : tail.length = 0 := by
          have sizes := perm.length_eq
          simp only [List.length_cons] at sizes
          omega
        have route := capacity p
        change (tail ++ emitted M p (read M d _ p)).length ≤ 1
        rw [List.length_append, ht, Nat.zero_add]
        cases read M d _ p <;> simp [emitted, route]
  unfold Exclusive
  cases q : t.pending with
  | nil => simp
  | cons p rest =>
    have empty : rest = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [q, List.length_cons] at small
      omega
    simp [empty]

/-- An actual step with a certified clean outcome projects to the same
zero-error order step. Margins can be checked for the chosen order. -/
theorem select_with_margin (M : Model N P) (d : Nat) (s : State N P)
    (before after : List P) (p : P) (queue : s.pending = before ++ p :: after)
    (lo hi e : Int) (within : lo ≤ e ∧ e ≤ hi)
    (room : RoutedCalendar.HasRoom (score M d s p) lo hi) :
    Move M d (project s)
      (project (step M d e { s with pending := p :: (before ++ after) })) := by
  have fire := fires_eq_of_margin M d s p e lo hi within room
  have changed : step M d e { s with pending := p :: (before ++ after) } =
      step M d 0 { s with pending := p :: (before ++ after) } := by
    have stable : fires M d { s with pending := p :: (before ++ after) } p e =
        fires M d { s with pending := p :: (before ++ after) } p 0 := fire
    simp [step, stable]
  rw [changed]
  exact select_projects M d (.process s before p after queue)

/-- Error may vary from step to step. The margin is checked at the memory
and port of the selected occurrence before that step. -/
inductive CertifiedTrace (M : Model N P) (d : Nat) :
    State N P → State N P → Prop where
  | nil (s : State N P) : CertifiedTrace M d s s
  | cons {s u : State N P} (before after : List P) (p : P)
      (queue : s.pending = before ++ p :: after) (lo hi e : Int)
      (within : lo ≤ e ∧ e ≤ hi) (room : RoutedCalendar.HasRoom (score M d s p) lo hi)
      (tail : CertifiedTrace M d
        (step M d e { s with pending := p :: (before ++ after) }) u) :
      CertifiedTrace M d s u

theorem certified_trace_projects (M : Model N P) (d : Nat) {s t : State N P}
    (trace : CertifiedTrace M d s t) : Path M d (project s) (project t) := by
  induction trace with
  | nil => exact .nil _
  | cons before after p queue lo hi e within room _ ih =>
    exact .cons (select_with_margin M d _ before after p queue lo hi e within room) ih

/-- All certified noisy orders that exhaust the queue agree on memory. -/
theorem certified_terminal_memory_unique (Q W eta d : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Certificate Q W eta M seed)
    (admissible : ∀ s, Path M d ⟨seed, fun _ => 0⟩ s → Exclusive M s ∨ PairMargins M d s)
    {a b : State N P} (pa : CertifiedTrace M d (start N seed) a)
    (pb : CertifiedTrace M d (start N seed) b) (ha : a.pending = []) (hb : b.pending = [])
    (base : Fin N → Nat) :
    a.writes = b.writes ∧ stored d base a = stored d base b :=
  terminal_memory_unique Q W eta d M seed cert admissible
    (certified_trace_projects M d pa) (certified_trace_projects M d pb) ha hb base

end NetworkStability.AutonomousFeedback.Schedule
