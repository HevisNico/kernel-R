import PortMemory

namespace NetworkStability.MarkFeedback

open AutonomousFeedback (mass mass_append)
open AutonomousFeedback.Schedule (Config Equivalent SafeMemory mass_permutation)
open AutonomousFeedback.Schedule.PortMemory (Address)

structure Model (N : Nat) (P : Type) where
  cell : P → Fin N
  secondPort : P → Bool
  bias : P → Int
  recoveryWeight : P → Int
  learn : P → Bool
  mark : P → Bool → Bool
  route : P → List P

def gain (M : Model N P) (p : P) : Fin (3 * N) :=
  (Address.mk (M.cell p) (if M.secondPort p then .port1 else .port0)).encode

def recovery (M : Model N P) (p : P) : Fin (3 * N) :=
  (Address.mk (M.cell p) .recovery).encode

def initial (N : Nat) (seed : List P) : Config (3 * N) P := ⟨seed, fun _ => 0⟩

/-- The two terms measure the gain dose and the signed influence of one
recovery dose on this probe. Counts use separate units per coordinate. -/
def score (M : Model N P) (d : Nat) (s : Config (3 * N) P) (p : P) : Int :=
  M.bias p + (d : Int) * s.writes (gain M p) + M.recoveryWeight p * s.writes (recovery M p)

def read (M : Model N P) (d : Nat) (s : Config (3 * N) P) (p : P) (e : Int) : Bool :=
  decide (0 ≤ score M d s p + e)

def emitted (M : Model N P) (p : P) (fire : Bool) : List P :=
  if fire then M.route p else []

/-- A silence can write the selected gain. Either branch can commit a
recovery dose, including a FIRE that also issues successors and a
protected native pulse that is silent and leaves the gain unchanged. -/
def footprint (M : Model N P) (p : P) (fire : Bool) (i : Fin (3 * N)) : Nat :=
  (if fire = false ∧ M.learn p = true ∧ i = gain M p then 1 else 0) +
    (if M.mark p fire = true ∧ i = recovery M p then 1 else 0)

def process (M : Model N P) (d : Nat) (s : Config (3 * N) P)
    (p : P) (rest : List P) (e : Int) : Config (3 * N) P :=
  let fire := read M d s p e
  ⟨rest ++ emitted M p fire, fun i => s.writes i + footprint M p fire i⟩

def fifoStep (M : Model N P) (d : Nat) (s : Config (3 * N) P) (e : Int) : Config (3 * N) P :=
  match s.pending with
  | [] => s
  | p :: rest => process M d s p rest e

def fifo (M : Model N P) (d : Nat) (error : Nat → Int) (s : Config (3 * N) P) :
    Nat → Config (3 * N) P
  | 0 => s
  | n + 1 => fifoStep M d (fifo M d error s n) (error n)

inductive Move (M : Model N P) (d : Nat) : Config (3 * N) P → Config (3 * N) P → Prop where
  | select (s : Config (3 * N) P) (p : P) (rest : List P) (available : s.pending.Perm (p :: rest)) :
      Move M d s (process M d s p rest 0)

inductive Path (M : Model N P) (d : Nat) : Config (3 * N) P → Config (3 * N) P → Prop where
  | nil (s : Config (3 * N) P) : Path M d s s
  | cons {s t u} : Move M d s t → Path M d t u → Path M d s u

theorem path_trans {M : Model N P} {d : Nat} {s t u : Config (3 * N) P}
    (a : Path M d s t) (b : Path M d t u) : Path M d s u := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

structure Reserve (Q : Nat) (M : Model N P) (seed : List P) where
  credit : Fin (3 * N) → P → Nat
  pays : ∀ p fire i, mass (credit i) (emitted M p fire) + footprint M p fire i ≤ credit i p
  seed_bound : ∀ i, mass (credit i) seed ≤ Q

structure Rank (W eta : Nat) (M : Model N P) (seed : List P) where
  weight : P → Nat
  positive : 0 < eta
  decreases : ∀ p, mass weight (M.route p) + eta ≤ weight p
  seed_bound : mass weight seed ≤ W * N

theorem process_reserve (M : Model N P) (d Q : Nat) {seed : List P}
    (cert : Reserve Q M seed) (s : Config (3 * N) P) (p : P) (tail : List P)
    (queue : s.pending.Perm (p :: tail)) (e : Int) (i : Fin (3 * N)) :
    (process M d s p tail e).writes i + mass (cert.credit i) (process M d s p tail e).pending ≤
      s.writes i + mass (cert.credit i) s.pending := by
  rw [mass_permutation _ queue]
  change s.writes i + footprint M p (read M d s p e) i +
    mass (cert.credit i) (tail ++ emitted M p (read M d s p e)) ≤
      s.writes i + (cert.credit i p + mass (cert.credit i) tail)
  rw [mass_append]
  have := cert.pays p (read M d s p e) i
  omega

theorem path_reserve {M : Model N P} {d Q : Nat} {seed : List P}
    (cert : Reserve Q M seed) {s t : Config (3 * N) P} (path : Path M d s t)
    (i : Fin (3 * N)) :
    t.writes i + mass (cert.credit i) t.pending ≤ s.writes i + mass (cert.credit i) s.pending := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons step _ ih =>
    cases step with
    | select p rest available => exact Nat.le_trans ih (process_reserve M d Q cert _ p rest available 0 i)

theorem fifo_reserve (M : Model N P) (d Q : Nat) {seed : List P}
    (cert : Reserve Q M seed) (error : Nat → Int) (s : Config (3 * N) P)
    (n : Nat) (i : Fin (3 * N)) :
    (fifo M d error s n).writes i + mass (cert.credit i) (fifo M d error s n).pending ≤
      s.writes i + mass (cert.credit i) s.pending := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    let u := fifo M d error s n
    change (fifoStep M d u (error n)).writes i +
      mass (cert.credit i) (fifoStep M d u (error n)).pending ≤ _
    change u.writes i + mass (cert.credit i) u.pending ≤ _ at ih
    cases queue : u.pending with
    | nil => simpa only [fifoStep, queue] using ih
    | cons p tail =>
      simp only [fifoStep, queue]
      exact Nat.le_trans (process_reserve M d Q cert u p tail (List.Perm.of_eq queue) _ i) ih

theorem safe_of_counts (Q d B rail : Nat) {N : Nat} {P : Type}
    (base : Fin (3 * N) → Nat) (initialBound : ∀ i, base i ≤ B) (room : B + d * Q < rail)
    (s : Config (3 * N) P) (counts : ∀ i, s.writes i ≤ Q) : SafeMemory Q d B rail base s := by
  refine ⟨RoutedCalendar.total_le Q _ counts, fun i => ⟨counts i, ?_, ?_, ?_⟩⟩
  · omega
  · exact Nat.add_le_add (initialBound i) (Nat.mul_le_mul_left d (counts i))
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add (initialBound i) (Nat.mul_le_mul_left d (counts i))) room

theorem cell_write_bound (Q : Nat) {N : Nat} {P : Type}
    (s : Config (3 * N) P) (counts : ∀ i, s.writes i ≤ Q) (i : Fin N) :
    s.writes (Address.mk i .port0).encode + s.writes (Address.mk i .port1).encode +
      s.writes (Address.mk i .recovery).encode ≤ 3 * Q := by
  have first := counts (Address.mk i .port0).encode
  have second := counts (Address.mk i .port1).encode
  have shared := counts (Address.mk i .recovery).encode
  omega

theorem process_rank (M : Model N P) (d W eta : Nat) {seed : List P}
    (rank : Rank W eta M seed) (s : Config (3 * N) P) (p : P) (tail : List P)
    (queue : s.pending.Perm (p :: tail)) (e : Int) :
    mass rank.weight (process M d s p tail e).pending + eta ≤ mass rank.weight s.pending := by
  rw [mass_permutation _ queue]
  change mass rank.weight (tail ++ emitted M p (read M d s p e)) + eta ≤
    rank.weight p + mass rank.weight tail
  rw [mass_append]
  have := rank.decreases p
  cases read M d s p e <;> simp [emitted, mass] at * <;> omega

theorem fifo_drains (W eta d : Nat) {N : Nat} {P : Type} (M : Model N P) (seed : List P)
    (rank : Rank W eta M seed) (error : Nat → Int) :
    (fifo M d error (initial N seed) (W * N)).pending = [] := by
  have budget (n : Nat) (active : (fifo M d error (initial N seed) n).pending ≠ []) :
      n + mass rank.weight (fifo M d error (initial N seed) n).pending ≤ W * N := by
    induction n with
    | zero => simpa [fifo, initial] using rank.seed_bound
    | succ n ih =>
      let s := fifo M d error (initial N seed) n
      cases queue : s.pending with
      | nil =>
        apply False.elim
        apply active
        change (fifoStep M d s (error n)).pending = []
        simp [fifoStep, queue]
      | cons p rest =>
        have prev := ih (by change s.pending ≠ []; simp [queue])
        change n + mass rank.weight s.pending ≤ W * N at prev
        have decrease := process_rank M d W eta rank s p rest (List.Perm.of_eq queue) (error n)
        have positive := rank.positive
        change n + 1 + mass rank.weight (fifoStep M d s (error n)).pending ≤ W * N
        simp only [fifoStep, queue]
        omega
  let s := fifo M d error (initial N seed) (W * N)
  cases queue : s.pending with
  | nil => rfl
  | cons p rest =>
    have h := budget (W * N) (by change s.pending ≠ []; simp [queue])
    change W * N + mass rank.weight s.pending ≤ W * N at h
    rw [queue] at h
    have paid := rank.decreases p
    have positive := rank.positive
    change W * N + (rank.weight p + mass rank.weight rest) ≤ W * N at h
    omega

theorem read_eq_of_room (score lo hi e : Int) (within : lo ≤ e ∧ e ≤ hi)
    (room : RoutedCalendar.HasRoom score lo hi) :
    decide (0 ≤ score + e) = decide (0 ≤ score + 0) := by
  rcases room with ⟨clean, upper⟩ | ⟨clean, lower⟩
  · have h : ¬ 0 ≤ score + e := by omega
    simp [h, clean]
  · have h : 0 ≤ score + e := by omega
    simp [h, clean]

def NominalMargins (M : Model N P) (d : Nat) (lo hi : Nat → Int)
    (s : Config (3 * N) P) (n : Nat) : Prop :=
  ∀ k < n, ∀ p rest, (fifo M d (fun _ => 0) s k).pending = p :: rest →
    RoutedCalendar.HasRoom (score M d (fifo M d (fun _ => 0) s k) p) (lo k) (hi k)

theorem fifo_eq_of_margins (M : Model N P) (d : Nat) (lo hi error : Nat → Int)
    (s : Config (3 * N) P) (n : Nat) (within : ∀ k, lo k ≤ error k ∧ error k ≤ hi k)
    (margins : NominalMargins M d lo hi s n) :
    fifo M d error s n = fifo M d (fun _ => 0) s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fifo, fifo, ih (fun k hk => margins k (by omega))]
    let u := fifo M d (fun _ => 0) s n
    change fifoStep M d u (error n) = fifoStep M d u 0
    cases queue : u.pending with
    | nil => simp [fifoStep, queue]
    | cons p rest =>
      have same := read_eq_of_room (score M d u p) _ _ _ (within n)
        (margins n (Nat.lt_succ_self _) p rest queue)
      change read M d u p (error n) = read M d u p 0 at same
      simp only [fifoStep, queue, process, same]

/-- The score displacement caused by an entire branch footprint. A signed
recovery coefficient can move either guard toward its threshold. -/
def displacement (M : Model N P) (d : Nat) (p q : P) (fire : Bool) : Int :=
  (d : Int) * footprint M q fire (gain M p) +
    M.recoveryWeight p * footprint M q fire (recovery M p)

theorem score_after (M : Model N P) (d : Nat) (s : Config (3 * N) P)
    (p q : P) (rest : List P) (e : Int) :
    score M d (process M d s q rest e) p =
      score M d s p + displacement M d p q (read M d s q e) := by
  unfold score displacement process
  dsimp only
  simp only [Int.natCast_add, Int.mul_add]
  omega

theorem different_cells_displacement (M : Model N P) (d : Nat) (p q : P)
    (different : M.cell p ≠ M.cell q) (fire : Bool) : displacement M d p q fire = 0 := by
  have apart (a b : AutonomousFeedback.Schedule.PortMemory.Coordinate) :
      (Address.mk (M.cell p) a).encode ≠ (Address.mk (M.cell q) b).encode :=
    fun eq => different (congrArg Address.cell
      (AutonomousFeedback.Schedule.PortMemory.address_encode_injective _ _ eq))
  cases fire <;> simp [displacement, footprint, gain, recovery, apart]

/-- For simultaneous distinct probe types, certify both possible footprints
of the other probe, including zero influence on disjoint cells. -/
def Separated (M : Model N P) (d : Nat) (s : Config (3 * N) P) : Prop :=
  ∀ p ∈ s.pending, ∀ q ∈ s.pending, p ≠ q → M.cell p = M.cell q →
    ∀ fire, RoutedCalendar.HasRoom (score M d s p)
      (displacement M d p q fire) (displacement M d p q fire)

/-- A single symmetric interleaving budget suffices when it bounds both
possible signed score shifts. The threshold convention is FIRE at zero. -/
theorem separated_of_uniform_room (M : Model N P) (d : Nat) (s : Config (3 * N) P)
    (bound : Int)
    (effect : ∀ p q fire, -bound ≤ displacement M d p q fire ∧ displacement M d p q fire ≤ bound)
    (margin : ∀ p ∈ s.pending, RoutedCalendar.HasRoom (score M d s p) (-bound) bound) :
    Separated M d s := by
  intro p mem q _ _ _ fire
  have ⟨lower, upper⟩ := effect p q fire
  rcases margin p mem with ⟨clean, silent⟩ | ⟨clean, fires⟩
  · exact Or.inl ⟨clean, by omega⟩
  · exact Or.inr ⟨clean, by omega⟩

def Exclusive (M : Model N P) (s : Config (3 * N) P) : Prop :=
  (s.pending.map M.cell).Nodup

theorem read_stable (M : Model N P) (d : Nat) (s : Config (3 * N) P)
    (hyp : Exclusive M s ∨ Separated M d s) {p q : P} {rest tail : List P}
    (perm : s.pending.Perm (p :: q :: rest)) (different : p ≠ q) :
    read M d (process M d s q tail 0) p 0 = read M d s p 0 := by
  unfold read
  rw [score_after, Int.add_zero]
  by_cases cell : M.cell p = M.cell q
  · rcases hyp with exclusive | separated
    · have nodup := (perm.map M.cell).nodup_iff.mp exclusive
      rw [List.map_cons, List.map_cons, cell] at nodup
      exact False.elim ((List.nodup_cons.mp nodup).1 (by simp))
    · have room := separated p (perm.mem_iff.mpr (by simp)) q
        (perm.mem_iff.mpr (by simp)) different cell (read M d s q 0)
      exact read_eq_of_room _ _ _ _ ⟨Int.le_refl _, Int.le_refl _⟩ room
  · rw [different_cells_displacement M d p q cell]

theorem process_equivalent (M : Model N P) (d : Nat) {s t : Config (3 * N) P}
    (same : s.writes = t.writes) (p : P) {a b : List P} (rest : a.Perm b) :
    Equivalent (process M d s p a 0) (process M d t p b 0) := by
  have fire : read M d s p 0 = read M d t p 0 := by simp [read, score, same]
  unfold Equivalent process
  dsimp only
  rw [fire, same]
  exact ⟨rest.append_right _, rfl⟩

theorem move_transport {M : Model N P} {d : Nat} {s t u : Config (3 * N) P}
    (eq : Equivalent s t) (step : Move M d s u) :
    ∃ v, Move M d t v ∧ Equivalent u v := by
  cases step with
  | select p rest available =>
    exact ⟨_, .select t p rest (eq.1.symm.trans available),
      process_equivalent M d eq.2 p (List.Perm.refl _)⟩

theorem path_transport {M : Model N P} {d : Nat} {s t u : Config (3 * N) P}
    (eq : Equivalent s t) (path : Path M d s u) :
    ∃ v, Path M d t v ∧ Equivalent u v := by
  induction path generalizing t with
  | nil => exact ⟨t, .nil _, eq⟩
  | cons step _ ih =>
    obtain ⟨v, move, same⟩ := move_transport eq step
    obtain ⟨last, tail, join⟩ := ih same
    exact ⟨last, .cons move tail, join⟩

theorem two_occurrences_commute (M : Model N P) (d : Nat) (s : Config (3 * N) P)
    (p q : P) (rest : List P)
    (pStable : read M d (process M d s q (p :: rest) 0) p 0 = read M d s p 0)
    (qStable : read M d (process M d s p (q :: rest) 0) q 0 = read M d s q 0) :
    Equivalent
      (process M d (process M d s p (q :: rest) 0) q (rest ++ emitted M p (read M d s p 0)) 0)
      (process M d (process M d s q (p :: rest) 0) p (rest ++ emitted M q (read M d s q 0)) 0) := by
  unfold Equivalent
  simp only [process] at pStable qStable ⊢
  rw [pStable, qStable]
  constructor
  · simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := emitted M p (read M d s p 0))
        (l₂ := emitted M q (read M d s q 0))).append_left rest
  · funext i
    omega

theorem different_cells_commute (M : Model N P) (d : Nat) (s : Config (3 * N) P)
    (p q : P) (rest : List P) (different : M.cell p ≠ M.cell q) :
    Equivalent
      (process M d (process M d s p (q :: rest) 0) q (rest ++ emitted M p (read M d s p 0)) 0)
      (process M d (process M d s q (p :: rest) 0) p (rest ++ emitted M q (read M d s q 0)) 0) := by
  apply two_occurrences_commute
  · simp only [read, score_after, different_cells_displacement M d p q different, Int.add_zero]
  · simp only [read, score_after, different_cells_displacement M d q p (Ne.symm different), Int.add_zero]

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

theorem local_diamond (M : Model N P) (d : Nat) {s a b : Config (3 * N) P}
    (hyp : Exclusive M s ∨ Separated M d s)
    (left : Move M d s a) (right : Move M d s b) :
    Equivalent a b ∨ ∃ u v, Move M d a u ∧ Move M d b v ∧ Equivalent u v := by
  cases left with
  | select p ps availableP =>
    cases right with
    | select q qs availableQ =>
      have heads := availableP.symm.trans availableQ
      by_cases same : p = q
      · subst q
        exact Or.inl (process_equivalent M d rfl p heads.cons_inv)
      · obtain ⟨rest, pTail, qTail⟩ := residual heads same
        have pq := availableP.trans (pTail.cons p)
        have qp := availableQ.trans (qTail.cons q)
        exact Or.inr ⟨_, _, .select _ _ _ (pTail.append_right _),
          .select _ _ _ (qTail.append_right _), two_occurrences_commute M d s p q rest
            (read_stable M d s hyp pq same) (read_stable M d s hyp qp (Ne.symm same))⟩


def Admissible (M : Model N P) (d : Nat) (root : Config (3 * N) P) : Prop :=
  ∀ s, Path M d root s → Exclusive M s ∨ Separated M d s

def Joinable (M : Model N P) (d : Nat) (a b : Config (3 * N) P) : Prop :=
  ∃ u v, Path M d a u ∧ Path M d b v ∧ Equivalent u v

/-- Newman's lemma modulo queue permutation, with the strict queue rank. -/
theorem newman (W eta : Nat) {N : Nat} {P : Type} (M : Model N P) (d : Nat)
    (seed : List P) (rank : Rank W eta M seed)
    (admissible : Admissible M d (initial N seed))
    {a b : Config (3 * N) P} (pa : Path M d (initial N seed) a)
    (pb : Path M d (initial N seed) b) : Joinable M d a b := by
  have lower {s t : Config (3 * N) P} (step : Move M d s t) :
      mass rank.weight t.pending < mass rank.weight s.pending := by
    cases step with
    | select p rest available =>
      have := process_rank M d W eta rank _ p rest available 0
      have := rank.positive
      omega
  have claim (n : Nat) : ∀ s : Config (3 * N) P,
      mass rank.weight s.pending = n → Path M d (initial N seed) s →
      ∀ a b, Path M d s a → Path M d s b → Joinable M d a b := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s size reach a b pa pb
      cases pa with
      | nil => exact ⟨b, b, pb, .nil _, ⟨List.Perm.refl _, rfl⟩⟩
      | cons first restA =>
        rename_i left
        cases pb with
        | nil => exact ⟨a, a, .nil _, .cons first restA, ⟨List.Perm.refl _, rfl⟩⟩
        | cons second restB =>
          rename_i right
          have leftRank := size ▸ lower first
          have rightRank := size ▸ lower second
          have leftReach := path_trans reach (.cons first (.nil _))
          have rightReach := path_trans reach (.cons second (.nil _))
          have diamond : Joinable M d left right := by
            rcases local_diamond M d (admissible s reach) first second with same | ⟨u, v, lu, rv, uv⟩
            · exact ⟨left, right, .nil _, .nil _, same⟩
            · exact ⟨u, v, .cons lu (.nil _), .cons rv (.nil _), uv⟩
          obtain ⟨u, v, lu, rv, uv⟩ := diamond
          obtain ⟨a', u', aa', uu', sameA⟩ := ih _ leftRank _ rfl leftReach a u restA lu
          obtain ⟨v', vv', sameV⟩ := path_transport uv uu'
          obtain ⟨b', v'', bb', v'v'', sameB⟩ :=
            ih _ rightRank _ rfl rightReach b v' restB (path_trans rv vv')
          have cross : Equivalent v' a' :=
            ⟨sameV.1.symm.trans sameA.1.symm, sameV.2.symm.trans sameA.2.symm⟩
          obtain ⟨last, a'last, sameLast⟩ := path_transport cross v'v''
          exact ⟨last, b', path_trans aa' a'last, bb',
            ⟨sameLast.1.symm.trans sameB.1.symm, sameLast.2.symm.trans sameB.2.symm⟩⟩
  exact claim _ _ rfl (.nil _) a b pa pb

theorem path_from_empty {M : Model N P} {d : Nat} {s t : Config (3 * N) P}
    (empty : s.pending = []) (path : Path M d s t) : t = s := by
  cases path with
  | nil => rfl
  | cons step _ =>
    cases step with
    | select p rest available =>
      rw [empty] at available
      exact False.elim (List.not_perm_nil_cons p rest available)

theorem terminal_unique (W eta d : Nat) {N : Nat} {P : Type} (M : Model N P)
    (seed : List P) (rank : Rank W eta M seed) (admissible : Admissible M d (initial N seed))
    {a b : Config (3 * N) P} (pa : Path M d (initial N seed) a) (pb : Path M d (initial N seed) b)
    (ea : a.pending = []) (eb : b.pending = []) : a.writes = b.writes := by
  obtain ⟨u, v, au, bv, eq⟩ := newman W eta M d seed rank admissible pa pb
  rw [path_from_empty ea au, path_from_empty eb bv] at eq
  exact eq.2

theorem move_writes_mono {M : Model N P} {d : Nat} {s t : Config (3 * N) P}
    (move : Move M d s t) (i : Fin (3 * N)) : s.writes i ≤ t.writes i := by
  cases move
  exact Nat.le_add_right _ _

theorem path_writes_mono {M : Model N P} {d : Nat} {s t : Config (3 * N) P}
    (path : Path M d s t) (i : Fin (3 * N)) : s.writes i ≤ t.writes i := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons move _ ih => exact Nat.le_trans (move_writes_mono move i) ih

theorem fifoStep_path (M : Model N P) (d : Nat) (s : Config (3 * N) P) :
    Path M d s (fifoStep M d s 0) := by
  cases queue : s.pending with
  | nil => simp only [fifoStep, queue]; exact .nil _
  | cons p rest =>
    simp only [fifoStep, queue]
    exact .cons (.select s p rest (List.Perm.of_eq queue)) (.nil _)

theorem fifo_prefix (M : Model N P) (d : Nat) (s : Config (3 * N) P) (n : Nat) :
    Path M d s (fifo M d (fun _ => 0) s n) := by
  induction n with
  | zero => exact .nil _
  | succ n ih => exact path_trans ih (fifoStep_path M d _)

theorem fifo_zero_add (M : Model N P) (d : Nat) (s : Config (3 * N) P) (n m : Nat) :
    fifo M d (fun _ => 0) s (n + m) =
      fifo M d (fun _ => 0) (fifo M d (fun _ => 0) s n) m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (fun t => fifoStep M d t 0) ih


/-- Residual paths carry an upper bound on their length. -/
inductive BudgetPath (M : Model N P) (d : Nat) : Nat → Config (3 * N) P → Config (3 * N) P → Prop where
  | nil (n : Nat) (s : Config (3 * N) P) : BudgetPath M d n s s
  | cons {n s t u} : Move M d s t → BudgetPath M d n t u → BudgetPath M d (n + 1) s u

private theorem budget_transport {M : Model N P} {d n : Nat} {s t u : Config (3 * N) P}
    (eq : Equivalent s t) (path : BudgetPath M d n s u) :
    ∃ v, BudgetPath M d n t v ∧ Equivalent u v := by
  induction path generalizing t with
  | nil n s => exact ⟨t, .nil n t, eq⟩
  | cons move _ ih =>
    obtain ⟨v, moved, same⟩ := move_transport eq move
    obtain ⟨last, tail, related⟩ := ih same
    exact ⟨last, .cons moved tail, related⟩

private theorem path_has_budget {M : Model N P} {d : Nat} {s t : Config (3 * N) P}
    (path : Path M d s t) : ∃ n, BudgetPath M d n s t := by
  induction path with
  | nil => exact ⟨0, .nil _ _⟩
  | cons move _ ih =>
    obtain ⟨n, budget⟩ := ih
    exact ⟨n + 1, .cons move budget⟩

private theorem budget_succ {M : Model N P} {d n : Nat} {s t : Config (3 * N) P}
    (path : BudgetPath M d n s t) : BudgetPath M d (n + 1) s t := by
  induction path with
  | nil => exact .nil _ _
  | cons move _ ih => exact .cons move ih

private theorem strip_budget (M : Model N P) (d : Nat) (root : Config (3 * N) P)
    (diamond : Admissible M d root) {s a b : Config (3 * N) P}
    (reach : Path M d root s) (step : Move M d s a) {n : Nat} (path : BudgetPath M d n s b) :
    ∃ u v, BudgetPath M d n a u ∧ (v = b ∨ Move M d b v) ∧ Equivalent u v := by
  induction path generalizing a with
  | nil n s => exact ⟨a, a, .nil n _, Or.inr step, ⟨List.Perm.refl _, rfl⟩⟩
  | cons next tail ih =>
    rcases local_diamond M d (diamond _ reach) step next with same | ⟨u', v', au, tv, related⟩
    · obtain ⟨last, moved, eq⟩ := budget_transport ⟨same.1.symm, same.2.symm⟩ tail
      exact ⟨last, _, budget_succ moved, Or.inl rfl, ⟨eq.1.symm, eq.2.symm⟩⟩
    · obtain ⟨last, finish, tailV, short, same⟩ := ih (path_trans reach (.cons next (.nil _))) tv
      obtain ⟨endA, pathA, matchA⟩ := budget_transport ⟨related.1.symm, related.2.symm⟩ tailV
      exact ⟨endA, finish, .cons au pathA, short,
        ⟨matchA.1.symm.trans same.1, matchA.2.symm.trans same.2⟩⟩

/-- FIFO catches the chosen occurrence (or an indistinguishable one) before
its suffix of original predecessors can grow. New descendants go to the tail. -/
private theorem catch_budget (M : Model N P) (d : Nat) (root : Config (3 * N) P)
    (diamond : Admissible M d root) (s : Config (3 * N) P) (reach : Path M d root s)
    (before : List P) (p : P) (after : List P) (queue : s.pending = before ++ p :: after)
    (n : Nat) (b : Config (3 * N) P)
    (tail : BudgetPath M d n (process M d s p (before ++ after) 0) b) :
    ∃ k u, BudgetPath M d n (fifo M d (fun _ => 0) s k) u ∧
      ∀ i, b.writes i ≤ u.writes i := by
  induction before generalizing s after b with
  | nil =>
    refine ⟨1, b, ?_, fun _ => Nat.le_refl _⟩
    change BudgetPath M d n (fifoStep M d s 0) b
    simpa only [fifoStep, queue, List.nil_append] using tail
  | cons q before ih =>
    let t := fifoStep M d s 0
    let rest := before ++ after
    let ep := emitted M p (read M d s p 0)
    let eq' := emitted M q (read M d s q 0)
    let a := process M d s p (q :: rest) 0
    let lifted := process M d t p (before ++ (after ++ eq')) 0
    have mainEq : t = process M d s q (before ++ p :: after) 0 := by
      simp only [t, fifoStep, queue, List.cons_append]
    have actual : Move M d s t := by
      rw [mainEq]
      exact .select _ _ _ (List.Perm.of_eq queue)
    by_cases same : p = q
    · subst q
      have related : Equivalent a t := by
        rw [mainEq]
        exact process_equivalent M d rfl p List.perm_middle.symm
      obtain ⟨u, path, eq⟩ := budget_transport related tail
      exact ⟨1, u, path, fun i => Nat.le_of_eq (congrFun eq.2 i)⟩
    · let aNext := process M d a q (rest ++ ep) 0
      let bNext := process M d (process M d s q (p :: rest) 0) p (rest ++ eq') 0
      have afterP : Move M d a aNext := .select _ _ _ (List.Perm.refl _)
      have tQueue : t.pending = before ++ p :: (after ++ eq') := by
        have eq := congrArg Config.pending mainEq
        change t.pending = (before ++ p :: after) ++ eq' at eq
        simpa only [List.append_assoc, List.cons_append] using eq
      have sPerm : s.pending.Perm (q :: p :: rest) := by
        rw [queue]
        exact List.perm_middle.cons q
      have joined : Equivalent aNext bNext :=
        two_occurrences_commute M d s p q rest
          (read_stable M d s (diamond _ reach) (sPerm.trans (List.Perm.swap _ _ _)) same)
          (read_stable M d s (diamond _ reach) sPerm (Ne.symm same))
      have liftedEq : Equivalent lifted bNext := by
        apply process_equivalent M d
        · rw [mainEq]
          exact (process_equivalent M d rfl q List.perm_middle).2
        · exact List.Perm.of_eq (List.append_assoc _ _ _).symm
      have reachA : Path M d root a := path_trans reach
        (.cons (.select _ _ _ (by rw [queue]; exact List.perm_middle)) (.nil _))
      obtain ⟨u, v, residual, short, uv⟩ := strip_budget M d root diamond reachA afterP tail
      obtain ⟨last, residual', ul⟩ := budget_transport
        ⟨joined.1.trans liftedEq.1.symm, joined.2.trans liftedEq.2.symm⟩ residual
      obtain ⟨k, finish, matched, counts⟩ :=
        ih t (path_trans reach (.cons actual (.nil _))) (after ++ eq') tQueue last residual'
      refine ⟨1 + k, finish, ?_, fun i => ?_⟩
      · rw [fifo_zero_add]
        exact matched
      · have lower : b.writes i ≤ v.writes i := by
          rcases short with rfl | mv
          · exact Nat.le_refl _
          · exact move_writes_mono mv i
        exact Nat.le_trans lower (Nat.le_trans (Nat.le_of_eq (congrFun (uv.2.symm.trans ul.2) i)) (counts i))

private theorem fifo_dominates (M : Model N P) (d : Nat) (root : Config (3 * N) P)
    (diamond : Admissible M d root) (s : Config (3 * N) P) (reach : Path M d root s)
    {n : Nat} {b : Config (3 * N) P} (path : BudgetPath M d n s b) :
    ∃ k, ∀ i, b.writes i ≤ (fifo M d (fun _ => 0) s k).writes i := by
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
        have same := process_equivalent M d (s := s) (t := s) rfl p
          (available.symm.trans split).cons_inv
        obtain ⟨end', toEnd, endEq⟩ := budget_transport same tail
        obtain ⟨k, u, rem, lower⟩ := catch_budget M d root diamond s reach before p after queue n end' toEnd
        obtain ⟨j, counts⟩ := ih _ (path_trans reach (fifo_prefix M d s k)) rem
        refine ⟨k + j, fun i => ?_⟩
        rw [fifo_zero_add]
        exact Nat.le_trans (Nat.le_of_eq (congrFun endEq.2 i)) (Nat.le_trans (lower i) (counts i))

theorem fifo_write_fair (M : Model N P) (d : Nat) (seed : List P)
    (diamond : Admissible M d (initial N seed)) (k : Nat) (t : Config (3 * N) P)
    (path : Path M d (fifo M d (fun _ => 0) (initial N seed) k) t) :
    ∃ j, k ≤ j ∧ ∀ i, t.writes i ≤ (fifo M d (fun _ => 0) (initial N seed) j).writes i := by
  obtain ⟨n, sized⟩ := path_has_budget path
  obtain ⟨j, writes⟩ := fifo_dominates M d _ diamond _ (fifo_prefix M d _ k) sized
  refine ⟨k + j, Nat.le_add_right _ _, ?_⟩
  rw [fifo_zero_add]
  exact writes


theorem noisy_fifo_write_fair (M : Model N P) (d : Nat) (seed : List P)
    (diamond : Admissible M d (initial N seed)) (lo hi error : Nat → Int)
    (within : ∀ n, lo n ≤ error n ∧ error n ≤ hi n)
    (margins : ∀ n, NominalMargins M d lo hi (initial N seed) n)
    (k : Nat) (t : Config (3 * N) P)
    (path : Path M d (fifo M d error (initial N seed) k) t) :
    ∃ j, k ≤ j ∧ ∀ i, t.writes i ≤ (fifo M d error (initial N seed) j).writes i := by
  have same n := fifo_eq_of_margins M d lo hi error (initial N seed) n within (margins n)
  rw [same k] at path
  obtain ⟨j, later, counts⟩ := fifo_write_fair M d seed diamond k t path
  rw [← same j] at counts
  exact ⟨j, later, counts⟩

/-- A noisy order is certified at each actual pre-read configuration. -/
inductive CertifiedPath (M : Model N P) (d : Nat) : Config (3 * N) P → Config (3 * N) P → Prop where
  | nil (s : Config (3 * N) P) : CertifiedPath M d s s
  | cons {s u : Config (3 * N) P} (p : P) (rest : List P) (available : s.pending.Perm (p :: rest))
      (lo hi e : Int) (within : lo ≤ e ∧ e ≤ hi)
      (room : RoutedCalendar.HasRoom (score M d s p) lo hi)
      (tail : CertifiedPath M d (process M d s p rest e) u) : CertifiedPath M d s u

theorem certified_projects {M : Model N P} {d : Nat} {s t : Config (3 * N) P}
    (path : CertifiedPath M d s t) : Path M d s t := by
  induction path with
  | nil => exact .nil _
  | @cons s u p rest available lo hi e within room tail ih =>
    have fire : read M d s p e = read M d s p 0 := read_eq_of_room _ _ _ _ within room
    have same : process M d s p rest e = process M d s p rest 0 := by simp only [process, fire]
    rw [same] at ih
    exact .cons (.select s p rest available) ih

def Stabilizes (state : Nat → Config (3 * N) P) (counts : Fin (3 * N) → Nat) : Prop :=
  ∃ cut, ∀ n, cut ≤ n → (state n).writes = counts

private theorem bounded_attains_max (f : Nat → Nat) (q : Nat) (bounded : ∀ n, f n ≤ q) :
    ∃ t, ∀ n, f n ≤ f t := by
  induction q with
  | zero => exact ⟨0, fun n => Nat.le_trans (bounded n) (Nat.zero_le _)⟩
  | succ q ih =>
    classical
    by_cases hit : ∃ n, f n = q + 1
    · obtain ⟨t, ht⟩ := hit
      exact ⟨t, fun n => ht ▸ bounded n⟩
    · apply ih
      intro n
      have below := bounded n
      have different : f n ≠ q + 1 := fun e => hit ⟨n, e⟩
      omega

theorem counts_stabilize (Q : Nat) {N : Nat} {P : Type}
    (state : Nat → Config (3 * N) P) (bounds : ∀ n i, (state n).writes i ≤ Q)
    (mono : ∀ n, ∀ i, (state n).writes i ≤ (state (n + 1)).writes i) :
    ∃ counts, Stabilizes state counts := by
  have growing (n m : Nat) (le : n ≤ m) (i : Fin (3 * N)) :
      (state n).writes i ≤ (state m).writes i := by
    induction le with
    | refl => exact Nat.le_refl _
    | @step m _ ih => exact Nat.le_trans ih (mono m i)
  have maxAt (i : Fin (3 * N)) : ∃ t, ∀ k, (state k).writes i ≤ (state t).writes i :=
    bounded_attains_max (fun n => (state n).writes i) Q (fun n => bounds n i)
  let cuts := fun i => Classical.choose (maxAt i)
  let cut := ((List.finRange (3 * N)).map cuts).sum
  have le_sum (xs : List (Fin (3 * N))) (i : Fin (3 * N)) (mem : i ∈ xs) :
      cuts i ≤ (xs.map cuts).sum := by
    induction xs with
    | nil => simp at mem
    | cons j rest ih =>
      rcases List.mem_cons.mp mem with eq | tail
      · subst j; simp
      · have h := ih tail
        simp only [List.map_cons, List.sum_cons]
        omega
  refine ⟨(state cut).writes, cut, fun n later => funext fun i => ?_⟩
  have leCut : cuts i ≤ cut := le_sum _ i (List.mem_finRange i)
  have atMax := Classical.choose_spec (maxAt i) n
  exact Nat.le_antisymm (Nat.le_trans atMax (growing _ _ leCut i)) (growing _ _ later i)

theorem fifo_safe (Q d B rail : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Reserve Q M seed)
    (base : Fin (3 * N) → Nat) (initialBound : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (error : Nat → Int) (n : Nat) : SafeMemory Q d B rail base (fifo M d error (initial N seed) n) := by
  apply safe_of_counts Q d B rail base initialBound headroom
  intro i
  have accounting := fifo_reserve M d Q cert error (initial N seed) n i
  have available := cert.seed_bound i
  change _ ≤ 0 + mass (cert.credit i) seed at accounting
  omega

theorem path_safe (Q d B rail : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Reserve Q M seed)
    (base : Fin (3 * N) → Nat) (initialBound : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (s : Config (3 * N) P) (path : Path M d (initial N seed) s) : SafeMemory Q d B rail base s := by
  apply safe_of_counts Q d B rail base initialBound headroom
  intro i
  have accounting := path_reserve cert path i
  have available := cert.seed_bound i
  change _ ≤ 0 + mass (cert.credit i) seed at accounting
  omega

theorem fifo_stabilizes (Q d : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Reserve Q M seed) (error : Nat → Int) :
    ∃ counts, Stabilizes (fifo M d error (initial N seed)) counts := by
  apply counts_stabilize Q
  · intro n i
    exact ((fifo_safe Q d 0 (d * Q + 1) M seed cert (fun _ => 0)
      (fun _ => by decide) (by omega) error n).2 i).1
  · intro n i
    let s := fifo M d error (initial N seed) n
    change s.writes i ≤ (fifoStep M d s (error n)).writes i
    cases queue : s.pending with
    | nil => simp [fifoStep, queue]
    | cons p tail => simp [fifoStep, queue, process]

/-- A fair stabilized FIFO cut bounds every finite reachable continuation.
The tail may continue to carry FIREs. -/
theorem fifo_limit_dominates (Q d : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Reserve Q M seed)
    (diamond : Admissible M d (initial N seed)) :
    ∃ counts, Stabilizes (fifo M d (fun _ => 0) (initial N seed)) counts ∧
      ∀ t, Path M d (initial N seed) t → ∀ i, t.writes i ≤ counts i := by
  obtain ⟨counts, cut, frozen⟩ := fifo_stabilizes Q d M seed cert (fun _ => 0)
  refine ⟨counts, ⟨cut, frozen⟩, fun t path i => ?_⟩
  obtain ⟨j, _, bound⟩ := fifo_write_fair M d seed diamond 0 t path
  have next := fifo_prefix M d (fifo M d (fun _ => 0) (initial N seed) j) cut
  have mono := path_writes_mono next i
  rw [← fifo_zero_add, frozen (j + cut) (by omega)] at mono
  exact Nat.le_trans (bound i) mono

/-- A sampled execution may process a finite batch at each sample. A
perpetual scheduler is fair for memory if it eventually matches every
write count achievable by a continuation from any sample. -/
def WriteFair (M : Model N P) (d : Nat) (state : Nat → Config (3 * N) P) : Prop :=
  ∀ k t, Path M d (state k) t → ∃ j, k ≤ j ∧ ∀ i, t.writes i ≤ (state j).writes i

theorem certified_execution_stabilizes (Q d : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Reserve Q M seed) (state : Nat → Config (3 * N) P)
    (starts : state 0 = initial N seed) (next : ∀ n, CertifiedPath M d (state n) (state (n + 1))) :
    ∃ counts, Stabilizes state counts := by
  have reach (n : Nat) : Path M d (initial N seed) (state n) := by
    induction n with
    | zero => rw [starts]; exact .nil _
    | succ n ih => exact path_trans ih (certified_projects (next n))
  apply counts_stabilize Q
  · intro n i
    have accounting := path_reserve cert (reach n) i
    have available := cert.seed_bound i
    change _ ≤ 0 + mass (cert.credit i) seed at accounting
    omega
  · exact fun n => path_writes_mono (certified_projects (next n))

theorem fair_limit_unique (Q d : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Reserve Q M seed)
    (diamond : Admissible M d (initial N seed)) (state : Nat → Config (3 * N) P)
    (starts : state 0 = initial N seed)
    (next : ∀ n, CertifiedPath M d (state n) (state (n + 1))) (fair : WriteFair M d state) :
    ∃ counts, Stabilizes state counts ∧
      Stabilizes (fifo M d (fun _ => 0) (initial N seed)) counts := by
  have reach (n : Nat) : Path M d (initial N seed) (state n) := by
    induction n with
    | zero => rw [starts]; exact .nil _
    | succ n ih => exact path_trans ih (certified_projects (next n))
  obtain ⟨limit, stable, maximal⟩ := fifo_limit_dominates Q d M seed cert diamond
  obtain ⟨cut, frozen⟩ := stable
  have service := fifo_prefix M d (initial N seed) cut
  rw [← starts] at service
  obtain ⟨j, _, catches⟩ := fair 0 _ service
  have after (n : Nat) (le : j ≤ n) (i : Fin (3 * N)) : (state j).writes i ≤ (state n).writes i := by
    induction le with
    | refl => exact Nat.le_refl _
    | @step m _ ih => exact Nat.le_trans ih (path_writes_mono (certified_projects (next m)) i)
  refine ⟨limit, ⟨j, fun n le => funext fun i => Nat.le_antisymm (maximal _ (reach n) i) ?_⟩,
    ⟨cut, frozen⟩⟩
  rw [starts, frozen cut (Nat.le_refl _)] at catches
  exact Nat.le_trans (catches i) (after n le i)

/-- Network memory with FIRE/MARK transactions. The scalar rank is only
needed for drainage and the Newman terminal result. -/
theorem network_memory (Q d B rail W eta : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Reserve Q M seed)
    (base : Fin (3 * N) → Nat) (initialBound : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (diamond : Admissible M d (initial N seed)) (lo hi : Nat → Int) :
    (∀ s, CertifiedPath M d (initial N seed) s → SafeMemory Q d B rail base s) ∧
    (∀ error n, SafeMemory Q d B rail base (fifo M d error (initial N seed) n)) ∧
    (∀ s, CertifiedPath M d (initial N seed) s → ∀ i : Fin N,
      s.writes (Address.mk i .port0).encode + s.writes (Address.mk i .port1).encode +
        s.writes (Address.mk i .recovery).encode ≤ 3 * Q) ∧
    (∀ error, ∃ counts, Stabilizes (fifo M d error (initial N seed)) counts) ∧
    (∀ error n, (∀ k, lo k ≤ error k ∧ error k ≤ hi k) → NominalMargins M d lo hi (initial N seed) n →
      fifo M d error (initial N seed) n = fifo M d (fun _ => 0) (initial N seed) n) ∧
    (∀ state : Nat → Config (3 * N) P, state 0 = initial N seed →
      (∀ n, CertifiedPath M d (state n) (state (n + 1))) → ∃ counts, Stabilizes state counts) ∧
    WriteFair M d (fifo M d (fun _ => 0) (initial N seed)) ∧
    (∀ state : Nat → Config (3 * N) P, state 0 = initial N seed →
      (∀ n, CertifiedPath M d (state n) (state (n + 1))) → WriteFair M d state →
      ∃ counts, Stabilizes state counts ∧ Stabilizes (fifo M d (fun _ => 0) (initial N seed)) counts) ∧
    (Rank W eta M seed →
      (∀ error, (fifo M d error (initial N seed) (W * N)).pending = []) ∧
      ∀ a b, CertifiedPath M d (initial N seed) a → CertifiedPath M d (initial N seed) b →
        a.pending = [] → b.pending = [] → a.writes = b.writes) := by
  exact ⟨fun s path => path_safe Q d B rail M seed cert base initialBound headroom s (certified_projects path),
    fifo_safe Q d B rail M seed cert base initialBound headroom,
    fun s path => cell_write_bound Q s (fun i =>
      ((path_safe Q d B rail M seed cert base initialBound headroom s (certified_projects path)).2 i).1),
    fifo_stabilizes Q d M seed cert,
    fun error n => fifo_eq_of_margins M d lo hi error (initial N seed) n, certified_execution_stabilizes Q d M seed cert,
    fifo_write_fair M d seed diamond,
    fair_limit_unique Q d M seed cert diamond,
    fun rank => ⟨fifo_drains W eta d M seed rank, fun _ _ pa pb =>
      terminal_unique W eta d M seed rank diamond (certified_projects pa) (certified_projects pb)⟩⟩

end NetworkStability.MarkFeedback
