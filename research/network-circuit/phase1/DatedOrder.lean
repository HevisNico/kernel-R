import CircuitNetwork

/-!
# The order of the dates gives the run of the queue

The guarded model of `AutonomousFeedback.lean` reads its queue from the head. A circuit network reads
its pulses in the order of their dates. This file proves that the two runs end in the same state, read
for read, when no two pulses that wait on one port have the same date.

The dated theorem of `../../network-stability/DatedNetwork.lean` compares runs that all respect the
dates. The queue run does not: it reads every source of A before the first source of B. Any single
order on dates for which both runs are earliest-date runs makes a source before its gate and a source
inside its gate tie on one port, and `TieRoom` then fails at the last silent read. The proof here
goes through a third description instead, which both runs satisfy.

1. **The port system.** Each port keeps the pulses that wait on it, in order of arrival. A move
   serves the first pulse of any port. Two moves on different ports commute exactly, because a read
   depends only on the writes of its own port: every complete run ends in the same state
   (`terminal_unique`), and with room for the error budgets a run with errors is a zero-error run
   (`noisy_exact`).
2. **The queue run is a run of the port system** (`queue_run`): the head of the queue is the first
   pulse of its port.
3. **The run in the order of the dates is a run of the port system** (`dated_reach`), if on each
   port the pulses wait in the order of their dates, without a tie. A routed pulse must then be dated
   after everything that waits on its port, which `Inv` keeps along the run.

`dated_run_eq_queue_run` puts the three together for any model; `circuit_dated_predicted` states it
for the circuit network.
-/

namespace NetworkStability.PortOrder

open AutonomousFeedback
open RoutedCalendar (HasRoom)
open CircuitNetwork (PortMargins)

/-! ## The port system -/

/-- The pulses that wait on each port in order of arrival, the writes of each port, and the reads
done on each port, latest first: the score and the decision. -/
structure PState (N : Nat) (P : Type) where
  queue : Fin N → List P
  writes : Fin N → Nat
  reads : Fin N → List (Int × Bool)

/-- What a read of `p` sends to port `k`. -/
def arrivals (M : Model N P) (p : P) (fire : Bool) (k : Fin N) : List P :=
  if fire then (M.route p).filter (fun q => M.cell q = k) else []

def portScore (M : Model N P) (d : Nat) (w : Fin N → Nat) (i : Fin N) (p : P) : Int :=
  M.bias p + (d : Int) * w i + (M.drive p : Int)

def apply (M : Model N P) (s : PState N P) (i : Fin N) (p : P) (rest : List P) (sc : Int)
    (fire : Bool) : PState N P where
  queue := fun k => (if k = i then rest else s.queue k) ++ arrivals M p fire k
  writes := fun k => s.writes k + if k = i ∧ fire = false then 1 else 0
  reads := fun k => if k = i then (sc, fire) :: s.reads k else s.reads k

/-- Serve the first pulse `p` of port `i` with read error `e`. -/
def serve (M : Model N P) (d : Nat) (s : PState N P) (i : Fin N) (p : P) (rest : List P)
    (e : Int) : PState N P :=
  apply M s i p rest (portScore M d s.writes i p) (decide (0 ≤ portScore M d s.writes i p + e))

inductive Move (M : Model N P) (d : Nat) (lo hi : Fin N → Int) : PState N P → PState N P → Prop
  | serve (s : PState N P) (i : Fin N) (p : P) (rest : List P) (e : Int) :
      s.queue i = p :: rest → lo i ≤ e → e ≤ hi i → Move M d lo hi s (serve M d s i p rest e)

inductive Reach (M : Model N P) (d : Nat) (lo hi : Fin N → Int) :
    Nat → PState N P → PState N P → Prop
  | nil (s : PState N P) : Reach M d lo hi 0 s s
  | cons {n : Nat} {s t u : PState N P} :
      Move M d lo hi s t → Reach M d lo hi n t u → Reach M d lo hi (n + 1) s u

/-- No error. -/
abbrev zero (N : Nat) : Fin N → Int := fun _ => 0

def Done (s : PState N P) : Prop := ∀ i, s.queue i = []

/-- Every waiting pulse is on its own port. -/
def Homed (M : Model N P) (s : PState N P) : Prop := ∀ i p, p ∈ s.queue i → M.cell p = i

/-- Reads of two different ports send their pulses to a port in an order that does not matter. -/
def RouteCommute (M : Model N P) : Prop :=
  ∀ p q k, M.cell p ≠ M.cell q →
    (M.route p).filter (fun r => M.cell r = k) ++ (M.route q).filter (fun r => M.cell r = k) =
      (M.route q).filter (fun r => M.cell r = k) ++ (M.route p).filter (fun r => M.cell r = k)

theorem arrivals_comm (M : Model N P) (comm : RouteCommute M) (p q : P) (apart : M.cell p ≠ M.cell q)
    (fp fq : Bool) (k : Fin N) :
    arrivals M p fp k ++ arrivals M q fq k = arrivals M q fq k ++ arrivals M p fp k := by
  cases fp <;> cases fq <;> simp [arrivals]
  exact comm p q k apart

theorem homed_move (M : Model N P) (d : Nat) (lo hi : Fin N → Int) {s t : PState N P}
    (homed : Homed M s) (move : Move M d lo hi s t) : Homed M t := by
  cases move with
  | serve i p rest e hq _ _ =>
    intro k x mem
    simp only [serve, apply] at mem
    rcases List.mem_append.mp mem with old | sent
    · by_cases ki : k = i
      · subst ki
        simp only [ite_true] at old
        exact homed k x (hq ▸ List.mem_cons_of_mem _ old)
      · simp only [ki, ite_false] at old
        exact homed k x old
    · simp only [arrivals] at sent
      split at sent
      · exact of_decide_eq_true (List.mem_filter.mp sent).2
      · cases sent

theorem apply_comm (M : Model N P) (comm : RouteCommute M) (s : PState N P) {i j : Fin N}
    (h : i ≠ j) (p q : P) (apart : M.cell p ≠ M.cell q) (rest rest' : List P) (sp sq : Int)
    (fp fq : Bool) :
    apply M (apply M s i p rest sp fp) j q (rest' ++ arrivals M p fp j) sq fq =
      apply M (apply M s j q rest' sq fq) i p (rest ++ arrivals M q fq i) sp fp := by
  have h' : j ≠ i := Ne.symm h
  simp only [apply, PState.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext k
    by_cases ki : k = i
    · subst ki
      simp only [h, ite_true, ite_false, List.append_assoc]
      rw [arrivals_comm M comm p q apart fp fq k]
    · by_cases kj : k = j
      · subst kj
        simp only [ki, ite_true, ite_false, List.append_assoc]
        rw [arrivals_comm M comm p q apart fp fq k]
      · simp only [ki, kj, ite_false, List.append_assoc]
        rw [arrivals_comm M comm p q apart fp fq k]
  · funext k
    by_cases ki : k = i <;> by_cases kj : k = j <;> simp [ki, kj] <;> omega
  · funext k
    by_cases ki : k = i
    · subst ki
      simp [h]
    · by_cases kj : k = j
      · subst kj
        simp [h']
      · simp [ki, kj]

theorem apply_writes_other (M : Model N P) (s : PState N P) {i j : Fin N} (h : j ≠ i) (p : P)
    (rest : List P) (sc : Int) (fire : Bool) : (apply M s i p rest sc fire).writes j = s.writes j := by
  simp [apply, h]

/-- Two zero-error moves from one state are the same move, or are followed by one move each to a
common state. -/
theorem diamond (M : Model N P) (d : Nat) (comm : RouteCommute M) {s a b : PState N P}
    (homed : Homed M s) (ha : Move M d (zero N) (zero N) s a) (hb : Move M d (zero N) (zero N) s b) :
    a = b ∨ ∃ u, Move M d (zero N) (zero N) a u ∧ Move M d (zero N) (zero N) b u := by
  cases ha with
  | serve i p rest e hq hlo hhi =>
    cases hb with
    | serve j q rest' e' hq' hlo' hhi' =>
      have e0 : e = 0 := by simp only [zero] at hlo hhi; omega
      have e0' : e' = 0 := by simp only [zero] at hlo' hhi'; omega
      subst e0 e0'
      by_cases h : i = j
      · subst h
        rw [hq] at hq'
        cases hq'
        exact Or.inl rfl
      · right
        have h' : j ≠ i := Ne.symm h
        have apart : M.cell p ≠ M.cell q := by
          rw [homed i p (hq ▸ List.mem_cons_self), homed j q (hq' ▸ List.mem_cons_self)]
          exact h
        let fp := decide (0 ≤ portScore M d s.writes i p + 0)
        let fq := decide (0 ≤ portScore M d s.writes j q + 0)
        have qa : (serve M d s i p rest 0).queue j = q :: (rest' ++ arrivals M p fp j) := by
          simp [serve, apply, h', hq', fp]
        have pb : (serve M d s j q rest' 0).queue i = p :: (rest ++ arrivals M q fq i) := by
          simp [serve, apply, h, hq, fq]
        have sa : portScore M d (serve M d s i p rest 0).writes j q = portScore M d s.writes j q := by
          simp [portScore, serve, apply_writes_other M s h']
        have sb : portScore M d (serve M d s j q rest' 0).writes i p = portScore M d s.writes i p := by
          simp [portScore, serve, apply_writes_other M s h]
        refine ⟨_, Move.serve _ j q _ 0 qa (by simp [zero]) (by simp [zero]), ?_⟩
        have eq : serve M d (serve M d s i p rest 0) j q (rest' ++ arrivals M p fp j) 0 =
            serve M d (serve M d s j q rest' 0) i p (rest ++ arrivals M q fq i) 0 := by
          show apply M (serve M d s i p rest 0) j q _ _ _ = apply M (serve M d s j q rest' 0) i p _ _ _
          rw [sa, sb]
          exact apply_comm M comm s h p q apart rest rest' _ _ fp fq
        rw [eq]
        exact Move.serve _ i p _ 0 pb (by simp [zero]) (by simp [zero])

theorem done_no_move (M : Model N P) (d : Nat) (lo hi : Fin N → Int) {s t : PState N P}
    (done : Done s) (move : Move M d lo hi s t) : False := by
  cases move with
  | serve i p rest e hq _ _ =>
    rw [done i] at hq
    cases hq

theorem done_reach (M : Model N P) (d : Nat) (lo hi : Fin N → Int) {n : Nat} {s t : PState N P}
    (done : Done s) (path : Reach M d lo hi n s t) : n = 0 ∧ t = s := by
  cases path with
  | nil => exact ⟨rfl, rfl⟩
  | cons move _ => exact (done_no_move M d lo hi done move).elim

/-- If a zero-error run of `n` reads empties every port, every zero-error run can be continued to the
same state, and takes `n` reads in all. -/
theorem complete (M : Model N P) (d : Nat) (comm : RouteCommute M) :
    ∀ n (s T : PState N P), Homed M s → Reach M d (zero N) (zero N) n s T → Done T →
      ∀ m t, Reach M d (zero N) (zero N) m s t → ∃ k, Reach M d (zero N) (zero N) k t T ∧ m + k = n := by
  intro n
  induction n with
  | zero =>
    intro s T _ path done m t other
    cases path
    obtain ⟨rfl, rfl⟩ := done_reach M d _ _ done other
    exact ⟨0, .nil _, rfl⟩
  | succ n ih =>
    intro s T homed path done m t other
    cases path with
    | cons sa rest =>
      cases other with
      | nil => exact ⟨n + 1, .cons sa rest, by omega⟩
      | @cons m' _ b _ sb tail =>
        rcases diamond M d comm homed sa sb with same | ⟨u, au, bu⟩
        · subst same
          obtain ⟨k, fin, len⟩ := ih _ T (homed_move M d _ _ homed sa) rest done m' t tail
          exact ⟨k, fin, by omega⟩
        · obtain ⟨k, fromU, len⟩ := ih _ T (homed_move M d _ _ homed sa) rest done 1 u (.cons au (.nil _))
          have size : n = k + 1 := by omega
          subst size
          obtain ⟨k', fin, len'⟩ := ih b T (homed_move M d _ _ homed sb) (.cons bu fromU) done m' t tail
          exact ⟨k', fin, by omega⟩

/-- Every complete zero-error run ends in the same state after the same number of reads. -/
theorem terminal_unique (M : Model N P) (d : Nat) (comm : RouteCommute M) {n m : Nat}
    {s T T' : PState N P} (homed : Homed M s) (path : Reach M d (zero N) (zero N) n s T) (done : Done T)
    (other : Reach M d (zero N) (zero N) m s T') (done' : Done T') : T' = T ∧ m = n := by
  obtain ⟨k, back, len⟩ := complete M d comm n s T homed path done m T' other
  obtain ⟨rfl, same⟩ := done_reach M d _ _ done' back
  exact ⟨same.symm, by omega⟩

/-! ## Errors inside the budgets -/

theorem move_reads (M : Model N P) (d : Nat) (lo hi : Fin N → Int) {s t : PState N P}
    (move : Move M d lo hi s t) (i : Fin N) (r : Int × Bool) (mem : r ∈ s.reads i) : r ∈ t.reads i := by
  cases move with
  | serve j p rest e _ _ _ =>
    simp only [serve, apply]
    by_cases h : i = j
    · simp only [h, ite_true]
      exact List.mem_cons_of_mem _ (h ▸ mem)
    · simp only [h, ite_false]
      exact mem

theorem reach_reads (M : Model N P) (d : Nat) (lo hi : Fin N → Int) {n : Nat} {s t : PState N P}
    (path : Reach M d lo hi n s t) (i : Fin N) (r : Int × Bool) (mem : r ∈ s.reads i) :
    r ∈ t.reads i := by
  induction path with
  | nil => exact mem
  | cons move _ ih => exact ih (move_reads M d lo hi move i r mem)

/-- Every read of the state has room for the budget of its port. -/
def Roomy (lo hi : Fin N → Int) (T : PState N P) : Prop :=
  ∀ i r, r ∈ T.reads i → HasRoom r.1 (lo i) (hi i)

theorem decide_eq_of_room {sc lo hi e : Int} (room : HasRoom sc lo hi) (h1 : lo ≤ e) (h2 : e ≤ hi) :
    decide (0 ≤ sc + e) = decide (0 ≤ sc + 0) := by
  rcases room with ⟨neg, top⟩ | ⟨pos, bot⟩
  · rw [decide_eq_false (by omega : ¬ 0 ≤ sc + e), decide_eq_false (by omega : ¬ 0 ≤ sc + 0)]
  · rw [decide_eq_true (by omega : 0 ≤ sc + e), decide_eq_true (by omega : 0 ≤ sc + 0)]

/-- If the reads of the complete zero-error run have room, a run with errors inside the budgets is a
zero-error run, read for read. -/
theorem noisy_exact (M : Model N P) (d : Nat) (comm : RouteCommute M) (lo hi : Fin N → Int)
    {T : PState N P} (done : Done T) (roomy : Roomy lo hi T) :
    ∀ m n (s t : PState N P), Homed M s → Reach M d (zero N) (zero N) n s T → Reach M d lo hi m s t →
      Reach M d (zero N) (zero N) m s t := by
  intro m
  induction m with
  | zero =>
    intro n s t _ _ path
    cases path
    exact .nil _
  | succ m ih =>
    intro n s t homed exact path
    cases path with
    | cons move tail =>
      cases move with
      | serve i p rest e hq hlo hhi =>
        have zmove : Move M d (zero N) (zero N) s (serve M d s i p rest 0) :=
          .serve s i p rest 0 hq (by simp [zero]) (by simp [zero])
        obtain ⟨k, fromA, _⟩ := complete M d comm n s T homed exact done 1 _ (.cons zmove (.nil _))
        have mem : (portScore M d s.writes i p, decide (0 ≤ portScore M d s.writes i p + 0)) ∈
            (serve M d s i p rest 0).reads i := by simp [serve, apply]
        have room := roomy i _ (reach_reads M d _ _ fromA i _ mem)
        have same : serve M d s i p rest e = serve M d s i p rest 0 := by
          simp only [serve]
          rw [decide_eq_of_room room hlo hhi]
        rw [same] at tail
        exact .cons zmove (ih k _ t (homed_move M d _ _ homed zmove) fromA tail)

/-! ## The queue run is a run of the port system -/

def view (M : Model N P) (s : State N P) (reads : Fin N → List (Int × Bool)) : PState N P :=
  ⟨fun i => s.pending.filter (fun q => M.cell q = i), s.writes, reads⟩

theorem view_homed (M : Model N P) (s : State N P) (reads : Fin N → List (Int × Bool)) :
    Homed M (view M s reads) :=
  fun _ _ mem => of_decide_eq_true (List.mem_filter.mp mem).2

/-- The reads of each port along the zero-error queue run, latest first, added to `r`: the score and
the decision. -/
def record (M : Model N P) (d : Nat) :
    Nat → State N P → (Fin N → List (Int × Bool)) → Fin N → List (Int × Bool)
  | 0, _, r => r
  | n + 1, s, r =>
    match s.pending with
    | [] => r
    | p :: _ => record M d n (step M d 0 s)
        (fun k => if k = M.cell p then (score M d s p, fires M d s p 0) :: r k else r k)

theorem view_step (M : Model N P) (d : Nat) (s : State N P) (p : P) (tail : List P)
    (h : s.pending = p :: tail) (r : Fin N → List (Int × Bool)) :
    view M (step M d 0 s)
        (fun k => if k = M.cell p then (score M d s p, fires M d s p 0) :: r k else r k) =
      serve M d (view M s r) (M.cell p) p (tail.filter (fun q => M.cell q = M.cell p)) 0 := by
  have sc : portScore M d s.writes (M.cell p) p = score M d s p := rfl
  have fr : decide (0 ≤ score M d s p + 0) = fires M d s p 0 := rfl
  simp only [view, serve, apply, step, h, sc, fr, PState.mk.injEq]
  refine ⟨?_, trivial, trivial⟩
  funext k
  rw [List.filter_append]
  by_cases hk : k = M.cell p
  · subst hk
    cases fires M d s p 0 <;> simp [arrivals]
  · have out : decide (M.cell p = k) = false := by simp [Ne.symm hk]
    cases fires M d s p 0 <;> simp [arrivals, hk, out]

/-- The zero-error queue run is a run of the port system, and its reads have room when the margins
of the model hold. -/
theorem queue_run (M : Model N P) (d : Nat) (lo hi : Fin N → Int) :
    ∀ n (s : State N P) (r : Fin N → List (Int × Bool)), PortMargins M d lo hi n s →
      (∃ m, Reach M d (zero N) (zero N) m (view M s r)
        (view M (run M d (fun _ => 0) n s) (record M d n s r))) ∧
      ∀ i x, x ∈ record M d n s r i → x ∈ r i ∨ HasRoom x.1 (lo i) (hi i) := by
  intro n
  induction n with
  | zero => exact fun s r _ => ⟨⟨0, .nil _⟩, fun _ _ mem => Or.inl mem⟩
  | succ n ih =>
    intro s r margins
    cases h : s.pending with
    | nil =>
      rw [run_empty M d _ _ s h]
      simp only [record, h]
      exact ⟨⟨0, .nil _⟩, fun _ _ mem => Or.inl mem⟩
    | cons p tail =>
      simp only [PortMargins, h] at margins
      obtain ⟨room, rest⟩ := margins
      obtain ⟨⟨m, path⟩, rooms⟩ := ih (step M d 0 s)
        (fun k => if k = M.cell p then (score M d s p, fires M d s p 0) :: r k else r k) rest
      have next : run M d (fun _ => 0) (n + 1) s = run M d (fun _ => 0) n (step M d 0 s) := rfl
      have recd : record M d (n + 1) s r = record M d n (step M d 0 s)
          (fun k => if k = M.cell p then (score M d s p, fires M d s p 0) :: r k else r k) := by
        simp only [record, h]
      rw [next, recd]
      refine ⟨⟨m + 1, .cons ?_ (view_step M d s p tail h r ▸ path)⟩, ?_⟩
      · exact .serve _ (M.cell p) p _ 0 (by simp [view, h]) (by simp [zero]) (by simp [zero])
      · intro i x mem
        rcases rooms i x mem with old | ok
        · by_cases hi' : i = M.cell p
          · subst hi'
            simp only [ite_true] at old
            rcases List.mem_cons.mp old with new | before
            · subst new
              exact Or.inr room
            · exact Or.inl before
          · simp only [hi', ite_false] at old
            exact Or.inl old
        · exact Or.inr ok

/-! ## The run in the order of the dates -/

/-- The state of a dated run: the pulses not yet served, in order of arrival, the writes and the
reads of each port. -/
structure DState (N : Nat) (O : Type) where
  pending : List O
  writes : Fin N → Nat
  reads : Fin N → List (Int × Bool)

def dserve (M : Model N O) (d : Nat) (s : DState N O) (pre : List O) (p : O) (post : List O)
    (e : Int) : DState N O :=
  let sc := portScore M d s.writes (M.cell p) p
  let fire := decide (0 ≤ sc + e)
  ⟨pre ++ post ++ (if fire then M.route p else []),
    fun k => s.writes k + if k = M.cell p ∧ fire = false then 1 else 0,
    fun k => if k = M.cell p then (sc, fire) :: s.reads k else s.reads k⟩

/-- Serve a pulse that no pending pulse precedes in date, with an error inside the budget of its
port. -/
inductive DatedMove (M : Model N O) (d : Nat) (lo hi : Fin N → Int) (date : O → Nat) :
    DState N O → DState N O → Prop
  | serve (s : DState N O) (pre : List O) (p : O) (post : List O) (e : Int) :
      s.pending = pre ++ p :: post → (∀ q ∈ s.pending, date p ≤ date q) →
      lo (M.cell p) ≤ e → e ≤ hi (M.cell p) → DatedMove M d lo hi date s (dserve M d s pre p post e)

inductive DatedReach (M : Model N O) (d : Nat) (lo hi : Fin N → Int) (date : O → Nat) :
    Nat → DState N O → DState N O → Prop
  | nil (s : DState N O) : DatedReach M d lo hi date 0 s s
  | cons {n : Nat} {s t u : DState N O} :
      DatedMove M d lo hi date s t → DatedReach M d lo hi date n t u →
      DatedReach M d lo hi date (n + 1) s u

/-- No same-date tie on a port: two pulses that wait on one port have different dates, and wait in
the order of their dates. -/
def PortSorted (M : Model N O) (date : O → Nat) (l : List O) : Prop :=
  l.Pairwise (fun q p => M.cell q = M.cell p → date q < date p)

/-- What a dated run keeps true of its pending pulses. `later`: a pulse that a pending pulse may
send is dated after everything that waits on its port. `mono`: on one port, pulses sent by a later
source are later. -/
structure Inv (M : Model N O) (date : O → Nat) (l : List O) : Prop where
  sorted : PortSorted M date l
  later : ∀ p ∈ l, ∀ r ∈ M.route p, ∀ q ∈ l, M.cell q = M.cell r → date q < date r
  mono : ∀ p ∈ l, ∀ p' ∈ l, ∀ r ∈ M.route p, ∀ r' ∈ M.route p', M.cell r = M.cell r' →
    date p < date p' → date r < date r'

/-- The shape of the routes: a read sends at most one pulse, a sent pulse sends nothing, and the
pulses of a port all come from one port. -/
structure Wiring (M : Model N O) : Prop where
  single : ∀ p, (M.route p).length ≤ 1
  leaf : ∀ p, ∀ r ∈ M.route p, M.route r = []
  source : ∀ p p', ∀ r ∈ M.route p, ∀ r' ∈ M.route p', M.cell r = M.cell r' → M.cell p = M.cell p'

def dview (M : Model N O) (s : DState N O) : PState N O :=
  ⟨fun i => s.pending.filter (fun q => M.cell q = i), s.writes, s.reads⟩

theorem dview_homed (M : Model N O) (s : DState N O) : Homed M (dview M s) :=
  fun _ _ mem => of_decide_eq_true (List.mem_filter.mp mem).2

/-- A dated move serves the first pulse of its port. -/
theorem dated_move (M : Model N O) (d : Nat) (lo hi : Fin N → Int) (date : O → Nat)
    {s t : DState N O} (sorted : PortSorted M date s.pending)
    (move : DatedMove M d lo hi date s t) : Move M d lo hi (dview M s) (dview M t) := by
  cases move with
  | serve pre p post e hp first hlo hhi =>
    have none : pre.filter (fun q => M.cell q = M.cell p) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq
      have cross := (List.pairwise_append.mp (hp ▸ sorted)).2.2 q hq p List.mem_cons_self
      have least := first q (hp ▸ List.mem_append_left _ hq)
      intro same
      have := cross (of_decide_eq_true same)
      omega
    have head : (dview M s).queue (M.cell p) = p :: post.filter (fun q => M.cell q = M.cell p) := by
      simp [dview, hp, List.filter_append, none]
    have eq : dview M (dserve M d s pre p post e) =
        serve M d (dview M s) (M.cell p) p (post.filter (fun q => M.cell q = M.cell p)) e := by
      simp only [dview, dserve, serve, apply, PState.mk.injEq]
      refine ⟨?_, rfl, rfl⟩
      funext k
      rw [List.filter_append, List.filter_append]
      by_cases fire : 0 ≤ portScore M d s.writes (M.cell p) p + e <;> by_cases hk : k = M.cell p
      · subst hk
        simp [arrivals, none, fire]
      · have out : decide (M.cell p = k) = false := by simp [Ne.symm hk]
        simp [arrivals, hk, hp, List.filter_append, out, fire]
      · subst hk
        simp [arrivals, none, fire]
      · have out : decide (M.cell p = k) = false := by simp [Ne.symm hk]
        simp [arrivals, hk, hp, List.filter_append, out, fire]
    rw [eq]
    exact .serve _ (M.cell p) p _ e head hlo hhi

theorem pairwise_short {R : O → O → Prop} (l : List O) (short : l.length ≤ 1) : l.Pairwise R := by
  match l, short with
  | [], _ => exact .nil
  | [_], _ => exact List.pairwise_singleton _ _
  | _ :: _ :: _, h => simp at h

/-- A dated move keeps the invariant. -/
theorem inv_move (M : Model N O) (d : Nat) (lo hi : Fin N → Int) (date : O → Nat)
    (wiring : Wiring M) {s t : DState N O} (inv : Inv M date s.pending)
    (move : DatedMove M d lo hi date s t) : Inv M date t.pending := by
  cases move with
  | serve pre p post e hp first hlo hhi =>
    have old := List.pairwise_append.mp (hp ▸ inv.sorted)
    have tailSorted := List.pairwise_cons.mp old.2.1
    have pmem : p ∈ s.pending := hp ▸ List.mem_append_right _ List.mem_cons_self
    have keep : ∀ x, x ∈ pre ++ post → x ∈ s.pending := by
      intro x hx
      rw [hp]
      rcases List.mem_append.mp hx with a | b
      · exact List.mem_append_left _ a
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ b)
    have sent : ∀ x, x ∈ (if decide (0 ≤ portScore M d s.writes (M.cell p) p + e) then M.route p else []) →
        x ∈ M.route p := by
      intro x hx
      split at hx
      · exact hx
      · cases hx
    have after : ∀ x, x ∈ pre ++ post → M.cell x = M.cell p → date p < date x := by
      intro x hx same
      rcases List.mem_append.mp hx with a | b
      · have before := old.2.2 x a p List.mem_cons_self same
        have least := first x (keep x hx)
        omega
      · exact tailSorted.1 x b same.symm
    have split : ∀ x, x ∈ (dserve M d s pre p post e).pending →
        x ∈ pre ++ post ∨ x ∈ M.route p := by
      intro x hx
      rcases List.mem_append.mp hx with a | b
      · exact Or.inl a
      · exact Or.inr (sent x b)
    refine ⟨?_, ?_, ?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨List.pairwise_append.mpr ⟨old.1, tailSorted.2, ?_⟩, ?_, ?_⟩
      · exact fun a ha b hb => old.2.2 a ha b (List.mem_cons_of_mem _ hb)
      · split
        · exact pairwise_short _ (wiring.single p)
        · exact .nil
      · exact fun a ha b hb same => inv.later p pmem b (sent b hb) a (keep a ha) same
    · intro x hx r hr q hq same
      rcases split x hx with xo | xr
      · rcases split q hq with qo | qr
        · exact inv.later x (keep x xo) r hr q (keep q qo) same
        · have ports := wiring.source p x q qr r hr same
          exact inv.mono p pmem x (keep x xo) q qr r hr same (after x xo ports.symm)
      · rw [wiring.leaf p x xr] at hr
        cases hr
    · intro x hx y hy r hr r' hr' same before
      rcases split x hx with xo | xr
      · rcases split y hy with yo | yr
        · exact inv.mono x (keep x xo) y (keep y yo) r hr r' hr' same before
        · rw [wiring.leaf p y yr] at hr'
          cases hr'
      · rw [wiring.leaf p x xr] at hr
        cases hr

/-- A dated run is a run of the port system. -/
theorem dated_reach (M : Model N O) (d : Nat) (lo hi : Fin N → Int) (date : O → Nat)
    (wiring : Wiring M) {m : Nat} {s t : DState N O} (inv : Inv M date s.pending)
    (path : DatedReach M d lo hi date m s t) : Reach M d lo hi m (dview M s) (dview M t) := by
  induction path with
  | nil => exact .nil _
  | cons move _ ih =>
    exact .cons (dated_move M d lo hi date inv.sorted move) (ih (inv_move M d lo hi date wiring inv move))

/-- **The order of the dates gives the run of the queue.** Take a model whose reads on different
ports commute and whose routes have the shape of `Wiring`, a seed that satisfies `Inv` (no same-date
tie on a port), and a zero-error queue run of `n` reads that ends with an empty queue and has room
for the budgets. Then every run that serves pulses in the order of their dates, with errors inside
the budgets, and ends with nothing pending, has the writes of the queue run and the same reads on
every port: same scores, same decisions, in the same order. -/
theorem dated_run_eq_queue_run (M : Model N O) (d : Nat) (lo hi : Fin N → Int) (date : O → Nat)
    (comm : RouteCommute M) (wiring : Wiring M) (seed : List O) (inv : Inv M date seed) (n : Nat)
    (margins : PortMargins M d lo hi n (start N seed))
    (empty : (run M d (fun _ => 0) n (start N seed)).pending = [])
    {m : Nat} {t : DState N O}
    (path : DatedReach M d lo hi date m ⟨seed, fun _ => 0, fun _ => []⟩ t) (done : t.pending = []) :
    t.writes = (run M d (fun _ => 0) n (start N seed)).writes ∧
      t.reads = record M d n (start N seed) (fun _ => []) := by
  obtain ⟨⟨k, queue⟩, rooms⟩ := queue_run M d lo hi n (start N seed) (fun _ => []) margins
  have finished : Done (view M (run M d (fun _ => 0) n (start N seed))
      (record M d n (start N seed) (fun _ => []))) := by
    intro i
    simp [view, empty]
  have roomy : Roomy lo hi (view M (run M d (fun _ => 0) n (start N seed))
      (record M d n (start N seed) (fun _ => []))) := by
    intro i x mem
    rcases rooms i x mem with none | ok
    · cases none
    · exact ok
  have ports := dated_reach M d lo hi date wiring inv path
  have exact := noisy_exact M d comm lo hi finished roomy m k _ _ (view_homed M _ _) queue ports
  have finished' : Done (dview M t) := by
    intro i
    simp [dview, done]
  have same := (terminal_unique M d comm (view_homed M _ _) queue finished exact finished').1
  exact ⟨congrArg PState.writes same, congrArg PState.reads same⟩

/-- Without errors every read has room. -/
theorem zero_margins (M : Model N P) (d : Nat) :
    ∀ n (s : State N P), PortMargins M d (zero N) (zero N) n s := by
  intro n
  induction n with
  | zero => exact fun _ => trivial
  | succ n ih =>
    intro s
    cases h : s.pending with
    | nil => simp [PortMargins, h]
    | cons p tail =>
      simp only [PortMargins, h]
      refine ⟨?_, ih _⟩
      simp only [HasRoom, zero]
      omega

/-! ## Forgetting the dates -/

/-- `f` forgets what the second model does not read. -/
structure Erases (f : O → P) (M' : Model N O) (M : Model N P) : Prop where
  cell : ∀ o, M'.cell o = M.cell (f o)
  bias : ∀ o, M'.bias o = M.bias (f o)
  drive : ∀ o, M'.drive o = M.drive (f o)
  route : ∀ o, (M'.route o).map f = M.route (f o)

/-- The queue runs of the two models are the same run. -/
theorem erase_run (f : O → P) (M' : Model N O) (M : Model N P) (er : Erases f M' M) (d : Nat)
    (lo hi : Fin N → Int) :
    ∀ n (s' : State N O) (s : State N P) (r : Fin N → List (Int × Bool)),
      s'.pending.map f = s.pending → s'.writes = s.writes →
      (run M' d (fun _ => 0) n s').pending.map f = (run M d (fun _ => 0) n s).pending ∧
      (run M' d (fun _ => 0) n s').writes = (run M d (fun _ => 0) n s).writes ∧
      record M' d n s' r = record M d n s r ∧
      (PortMargins M d lo hi n s → PortMargins M' d lo hi n s') := by
  intro n
  induction n with
  | zero => exact fun _ _ _ hp hw => ⟨hp, hw, rfl, fun _ => trivial⟩
  | succ n ih =>
    intro s' s r hp hw
    cases h' : s'.pending with
    | nil =>
      have hs : s.pending = [] := by rw [← hp, h']; rfl
      rw [run_empty M' d _ _ s' h', run_empty M d _ _ s hs]
      refine ⟨hp, hw, ?_, fun _ => ?_⟩
      · simp only [record, h', hs]
      · simp [PortMargins, h']
    | cons o tail =>
      have hs : s.pending = f o :: tail.map f := by rw [← hp, h']; rfl
      have sc : score M' d s' o = score M d s (f o) := by
        simp only [score, er.bias, er.drive, er.cell, hw]
      have fr : fires M' d s' o 0 = fires M d s (f o) 0 := by
        simp only [fires, sc]
      have np : (step M' d 0 s').pending.map f = (step M d 0 s).pending := by
        simp only [step, h', hs, fr, List.map_append]
        cases fires M d s (f o) 0 <;> simp [er.route]
      have nw : (step M' d 0 s').writes = (step M d 0 s).writes := by
        simp only [step, h', hs, fr, hw, er.cell]
      have nr : (fun k => if k = M'.cell o then (score M' d s' o, fires M' d s' o 0) :: r k else r k) =
          (fun k => if k = M.cell (f o) then (score M d s (f o), fires M d s (f o) 0) :: r k else r k) := by
        simp only [sc, fr, er.cell]
      obtain ⟨a, b, c, e⟩ := ih (step M' d 0 s') (step M d 0 s)
        (fun k => if k = M.cell (f o) then (score M d s (f o), fires M d s (f o) 0) :: r k else r k) np nw
      refine ⟨a, b, ?_, fun margins => ?_⟩
      · simp only [record, h', hs, nr]
        exact c
      · simp only [PortMargins, h', hs] at margins ⊢
        rw [sc, er.cell]
        exact ⟨margins.1, e margins.2⟩

/-! ## A dated run exists

The statements above are about every complete dated run. This section shows there is one, so that
they are not empty. -/

theorem exists_earliest (date : O → Nat) :
    ∀ l : List O, l ≠ [] → ∃ pre p post, l = pre ++ p :: post ∧ ∀ q ∈ l, date p ≤ date q := by
  intro l
  induction l with
  | nil => exact fun h => (h rfl).elim
  | cons x rest ih =>
    intro _
    cases rest with
    | nil => exact ⟨[], x, [], rfl, fun q hq => by simp at hq; subst hq; exact Nat.le_refl _⟩
    | cons y tail =>
      obtain ⟨pre, p, post, eq, least⟩ := ih (by simp)
      by_cases first : date x ≤ date p
      · refine ⟨[], x, y :: tail, rfl, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | later
        · exact Nat.le_refl _
        · exact Nat.le_trans first (least q later)
      · refine ⟨x :: pre, p, post, by rw [eq]; rfl, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | later
        · omega
        · exact least q later

theorem dated_snoc (M : Model N O) (d : Nat) (lo hi : Fin N → Int) (date : O → Nat) {m : Nat}
    {s t u : DState N O} (path : DatedReach M d lo hi date m s t)
    (move : DatedMove M d lo hi date t u) : DatedReach M d lo hi date (m + 1) s u := by
  induction path with
  | nil => exact .cons move (.nil _)
  | cons first _ ih => exact .cons first (ih move)

theorem pending_nil_of_done (M : Model N O) (s : DState N O) (done : Done (dview M s)) :
    s.pending = [] := by
  cases h : s.pending with
  | nil => rfl
  | cons p rest =>
    have empty := done (M.cell p)
    simp [dview, h] at empty

/-- Under the hypotheses of `dated_run_eq_queue_run`, a zero-error run in the order of the dates
exists and ends with nothing pending. -/
theorem dated_run_exists (M : Model N O) (d : Nat) (date : O → Nat) (comm : RouteCommute M)
    (wiring : Wiring M) (seed : List O) (inv : Inv M date seed) (n : Nat)
    (empty : (run M d (fun _ => 0) n (start N seed)).pending = []) :
    ∃ m t, DatedReach M d (zero N) (zero N) date m ⟨seed, fun _ => 0, fun _ => []⟩ t ∧
      t.pending = [] := by
  obtain ⟨⟨k, queue⟩, _⟩ := queue_run M d (zero N) (zero N) n (start N seed) (fun _ => [])
    (zero_margins M d n _)
  have finished : Done (view M (run M d (fun _ => 0) n (start N seed))
      (record M d n (start N seed) (fun _ => []))) := by
    intro i
    simp [view, empty]
  generalize view M (run M d (fun _ => 0) n (start N seed))
    (record M d n (start N seed) (fun _ => [])) = T at queue finished
  have go : ∀ j m (s : DState N O), Inv M date s.pending →
      DatedReach M d (zero N) (zero N) date m ⟨seed, fun _ => 0, fun _ => []⟩ s →
      Reach M d (zero N) (zero N) j (dview M s) T →
      ∃ m t, DatedReach M d (zero N) (zero N) date m ⟨seed, fun _ => 0, fun _ => []⟩ t ∧
        t.pending = [] := by
    intro j
    induction j with
    | zero =>
      intro m s _ path rest
      cases rest
      exact ⟨m, s, path, pending_nil_of_done M s finished⟩
    | succ j ih =>
      intro m s keep path rest
      by_cases none : s.pending = []
      · exact ⟨m, s, path, none⟩
      · obtain ⟨pre, p, post, eq, least⟩ := exists_earliest date s.pending none
        have move : DatedMove M d (zero N) (zero N) date s (dserve M d s pre p post 0) :=
          .serve s pre p post 0 eq least (by simp [zero]) (by simp [zero])
        have ported := dated_move M d (zero N) (zero N) date keep.sorted move
        obtain ⟨k', after, len⟩ := complete M d comm (j + 1) _ _ (dview_homed M s) rest finished 1 _
          (.cons ported (.nil _))
        have size : k' = j := by omega
        subst size
        exact ih (m + 1) _ (inv_move M d _ _ date wiring keep move) (dated_snoc M d _ _ date path move)
          after
  exact go k 0 _ inv (.nil _) queue

end NetworkStability.PortOrder

/-! ## The circuit network -/

namespace NetworkStability.CircuitNetwork

open AutonomousFeedback
open PortOrder

/-- A pulse with the date at which it starts. -/
abbrev Pulse := Probe × Nat

/-- The circuit network with dates. A source inside its gate that fires at date `t` sends a wire
pulse dated `wire t`: the date of its FIRE plus the delay of the edge. The model does not read the
dates. -/
def datedCircuit (gap : Fin 4 → Int) (wire : Nat → Nat) : Model 4 Pulse where
  cell := fun o => port o.1
  bias := fun o => - gap (port o.1)
  drive := fun _ => 0
  route := fun o => (route o.1).map (fun k => (k, wire o.2))

/-- The sources with their dates: those of A before its gate and inside it, then those of B. -/
def datedCalendar (ua ra ub rb : List Nat) : List Pulse :=
  ua.map (fun t => (Probe.sourceA false, t)) ++ ra.map (fun t => (Probe.sourceA true, t)) ++
    ub.map (fun t => (Probe.sourceB false, t)) ++ rb.map (fun t => (Probe.sourceB true, t))

theorem circuit_erases (gap : Fin 4 → Int) (wire : Nat → Nat) :
    Erases Prod.fst (datedCircuit gap wire) (circuit gap) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun o => by
    simp [datedCircuit, circuit, List.map_map, Function.comp_def]⟩

theorem map_const_replicate (l : List Nat) (c : Probe) :
    l.map (fun _ => c) = List.replicate l.length c := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [List.replicate_succ, ih]

theorem datedCalendar_erase (ua ra ub rb : List Nat) :
    (datedCalendar ua ra ub rb).map Prod.fst = calendar ua.length ra.length ub.length rb.length := by
  simp [datedCalendar, calendar, List.map_map, Function.comp_def, map_const_replicate]

theorem circuit_wiring (gap : Fin 4 → Int) (wire : Nat → Nat) : Wiring (datedCircuit gap wire) where
  single := by
    rintro ⟨k, t⟩
    cases k with
    | sourceA r => cases r <;> simp [datedCircuit, route]
    | sourceB r => cases r <;> simp [datedCircuit, route]
    | forward => simp [datedCircuit, route]
    | back => simp [datedCircuit, route]
  leaf := by
    rintro ⟨k, t⟩ r hr
    cases k with
    | sourceA b => cases b <;> simp [datedCircuit, route] at hr ⊢ <;> subst hr <;> rfl
    | sourceB b => cases b <;> simp [datedCircuit, route] at hr ⊢ <;> subst hr <;> rfl
    | forward => simp [datedCircuit, route] at hr
    | back => simp [datedCircuit, route] at hr
  source := by
    rintro ⟨k, t⟩ ⟨k', t'⟩ r hr r' hr' same
    cases k with
    | sourceA b =>
      cases b <;> simp [datedCircuit, route] at hr
      subst hr
      cases k' with
      | sourceA b' => rfl
      | sourceB b' =>
        cases b' <;> simp [datedCircuit, route] at hr'
        subst hr'
        simp (config := { decide := true }) [datedCircuit, port] at same
      | forward => simp [datedCircuit, route] at hr'
      | back => simp [datedCircuit, route] at hr'
    | sourceB b =>
      cases b <;> simp [datedCircuit, route] at hr
      subst hr
      cases k' with
      | sourceA b' =>
        cases b' <;> simp [datedCircuit, route] at hr'
        subst hr'
        simp (config := { decide := true }) [datedCircuit, port] at same
      | sourceB b' => rfl
      | forward => simp [datedCircuit, route] at hr'
      | back => simp [datedCircuit, route] at hr'
    | forward => simp [datedCircuit, route] at hr
    | back => simp [datedCircuit, route] at hr

theorem circuit_commute (gap : Fin 4 → Int) (wire : Nat → Nat) :
    RouteCommute (datedCircuit gap wire) := by
  rintro ⟨k, t⟩ ⟨k', t'⟩ i apart
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  cases k with
  | sourceA b =>
    cases b
    · simp [datedCircuit, route]
    · cases k' with
      | sourceA b' => cases b' <;> simp (config := { decide := true }) [datedCircuit, route, port] at apart ⊢
      | sourceB b' =>
        cases b'
        · simp [datedCircuit, route]
        · rcases cases with h | h | h | h <;> subst h <;>
            simp (config := { decide := true }) [datedCircuit, route, port]
      | forward => simp [datedCircuit, route]
      | back => simp [datedCircuit, route]
  | sourceB b =>
    cases b
    · simp [datedCircuit, route]
    · cases k' with
      | sourceA b' =>
        cases b'
        · simp [datedCircuit, route]
        · rcases cases with h | h | h | h <;> subst h <;>
            simp (config := { decide := true }) [datedCircuit, route, port]
      | sourceB b' => cases b' <;> simp (config := { decide := true }) [datedCircuit, route, port] at apart ⊢
      | forward => simp [datedCircuit, route]
      | back => simp [datedCircuit, route]
  | forward => simp [datedCircuit, route]
  | back => simp [datedCircuit, route]

/-- The seed has no same-date tie on a port when the dates of the sources of each cell increase, and
the wire dates increase with the dates of their sources. -/
theorem circuit_inv (gap : Fin 4 → Int) (wire : Nat → Nat) (strict : ∀ a b, a < b → wire a < wire b)
    (ua ra ub rb : List Nat) (sa : (ua ++ ra).Pairwise (· < ·)) (sb : (ub ++ rb).Pairwise (· < ·)) :
    Inv (datedCircuit gap wire) (fun o => o.2) (datedCalendar ua ra ub rb) where
  sorted := by
    obtain ⟨au, ar, aur⟩ := List.pairwise_append.mp sa
    obtain ⟨bu, br, bur⟩ := List.pairwise_append.mp sb
    show (ua.map (fun t => (Probe.sourceA false, t)) ++ ra.map (fun t => (Probe.sourceA true, t)) ++
      ub.map (fun t => (Probe.sourceB false, t)) ++ rb.map (fun t => (Probe.sourceB true, t))).Pairwise _
    rw [List.append_assoc]
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_append.mpr ⟨?_, ?_, ?_⟩, List.pairwise_append.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · refine List.pairwise_map.mpr (au.imp ?_)
      intro a b h _
      exact h
    · refine List.pairwise_map.mpr (ar.imp ?_)
      intro a b h _
      exact h
    · intro a ha b hb _
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      exact aur x hx y hy
    · refine List.pairwise_map.mpr (bu.imp ?_)
      intro a b h _
      exact h
    · refine List.pairwise_map.mpr (br.imp ?_)
      intro a b h _
      exact h
    · intro a ha b hb _
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      exact bur x hx y hy
    · intro a ha b hb same
      rcases List.mem_append.mp ha with h | h <;> rcases List.mem_append.mp hb with g | g <;>
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp h <;> obtain ⟨y, _, rfl⟩ := List.mem_map.mp g <;>
        simp (config := { decide := true }) [datedCircuit, port] at same
  later := by
    intro p _ r hr q hq same
    have source : port q.1 = sourceOfA ∨ port q.1 = sourceOfB := by
      simp only [datedCalendar, List.mem_append, List.mem_map] at hq
      rcases hq with ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> simp [port]
    have wire : port r.1 = forwardOnB ∨ port r.1 = returnOnA := by
      obtain ⟨k, t⟩ := p
      cases k with
      | sourceA b => cases b <;> simp [datedCircuit, route] at hr <;> subst hr <;> simp [port]
      | sourceB b => cases b <;> simp [datedCircuit, route] at hr <;> subst hr <;> simp [port]
      | forward => simp [datedCircuit, route] at hr
      | back => simp [datedCircuit, route] at hr
    have same' : port q.1 = port r.1 := same
    rcases source with h | h <;> rcases wire with g | g <;> rw [h, g] at same' <;>
      exact absurd same' (by decide)
  mono := by
    intro p _ p' _ r hr r' hr' _ before
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr'
    exact strict _ _ before

/-- The queue of the circuit model is empty after its `4 (a0 + 2 a1 + b0 + 2 b1)` reads. -/
theorem circuit_empties (gap : Fin 4 → Int) (a0 a1 b0 b1 d : Nat) :
    (run (circuit gap) d (fun _ => 0) ((a0 + 2 * a1 + b0 + 2 * b1) * 4)
      (start 4 (calendar a0 a1 b0 b1))).pending = [] := by
  have cert := certificate gap a0 a1 b0 b1
  exact terminal_by_budget (circuit gap) d 1 cert.weight cert.eta_pos cert.scalar _ _ _
    (by rw [Nat.one_mul]; exact cert.seed_weight)

/-- **The circuit network, read in the order of the dates.** The sources of each cell have increasing
dates, a wire pulse is dated by an increasing function of the date of its source, and every read of
the zero-error queue run has room for the error budget of its port (the hypothesis of
`circuit_predicted`, checked for each instance in `Instances.lean`). Then every run that serves the
pulses in the order of their dates, with errors inside the budgets, and ends with nothing pending,
has the writes of the zero-error queue run and the same reads on every port. -/
theorem circuit_dated_predicted (gap : Fin 4 → Int) (wire : Nat → Nat)
    (strict : ∀ a b, a < b → wire a < wire b) (ua ra ub rb : List Nat)
    (sa : (ua ++ ra).Pairwise (· < ·)) (sb : (ub ++ rb).Pairwise (· < ·)) (d : Nat)
    (lo hi : Fin 4 → Int)
    (margins : PortMargins (circuit gap) d lo hi
      ((ua.length + 2 * ra.length + ub.length + 2 * rb.length) * 4)
      (start 4 (calendar ua.length ra.length ub.length rb.length)))
    {m : Nat} {t : DState 4 Pulse}
    (path : DatedReach (datedCircuit gap wire) d lo hi (fun o => o.2) m
      ⟨datedCalendar ua ra ub rb, fun _ => 0, fun _ => []⟩ t)
    (done : t.pending = []) :
    let steps := (ua.length + 2 * ra.length + ub.length + 2 * rb.length) * 4
    let seed := start 4 (calendar ua.length ra.length ub.length rb.length)
    t.writes = (run (circuit gap) d (fun _ => 0) steps seed).writes ∧
      t.reads = record (circuit gap) d steps seed (fun _ => []) := by
  intro steps seed
  obtain ⟨pend, writes, reads, lift⟩ := erase_run Prod.fst (datedCircuit gap wire) (circuit gap)
    (circuit_erases gap wire) d lo hi steps (start 4 (datedCalendar ua ra ub rb)) seed (fun _ => [])
    (datedCalendar_erase ua ra ub rb) rfl
  have empty : (run (datedCircuit gap wire) d (fun _ => 0) steps
      (start 4 (datedCalendar ua ra ub rb))).pending = [] := by
    have gone := circuit_empties gap ua.length ra.length ub.length rb.length d
    rw [← pend] at gone
    exact List.map_eq_nil_iff.mp gone
  obtain ⟨w, r⟩ := dated_run_eq_queue_run (datedCircuit gap wire) d lo hi (fun o => o.2)
    (circuit_commute gap wire) (circuit_wiring gap wire) (datedCalendar ua ra ub rb)
    (circuit_inv gap wire strict ua ra ub rb sa sb) steps (lift margins) empty path done
  exact ⟨w.trans writes, r.trans reads⟩

/-- **No same-date tie: the run in the order of the dates equals the queue run.** The case without
errors, which needs no margin. -/
theorem circuit_dated_eq_queue (gap : Fin 4 → Int) (wire : Nat → Nat)
    (strict : ∀ a b, a < b → wire a < wire b) (ua ra ub rb : List Nat)
    (sa : (ua ++ ra).Pairwise (· < ·)) (sb : (ub ++ rb).Pairwise (· < ·)) (d : Nat)
    {m : Nat} {t : DState 4 Pulse}
    (path : DatedReach (datedCircuit gap wire) d (zero 4) (zero 4) (fun o => o.2) m
      ⟨datedCalendar ua ra ub rb, fun _ => 0, fun _ => []⟩ t)
    (done : t.pending = []) :
    let steps := (ua.length + 2 * ra.length + ub.length + 2 * rb.length) * 4
    let seed := start 4 (calendar ua.length ra.length ub.length rb.length)
    t.writes = (run (circuit gap) d (fun _ => 0) steps seed).writes ∧
      t.reads = record (circuit gap) d steps seed (fun _ => []) :=
  circuit_dated_predicted gap wire strict ua ra ub rb sa sb d (zero 4) (zero 4)
    (zero_margins (circuit gap) d _ _) path done

/-- A complete zero-error run of the circuit network in the order of the dates exists. -/
theorem circuit_dated_run_exists (gap : Fin 4 → Int) (wire : Nat → Nat)
    (strict : ∀ a b, a < b → wire a < wire b) (ua ra ub rb : List Nat)
    (sa : (ua ++ ra).Pairwise (· < ·)) (sb : (ub ++ rb).Pairwise (· < ·)) (d : Nat) :
    ∃ m t, DatedReach (datedCircuit gap wire) d (zero 4) (zero 4) (fun o => o.2) m
      ⟨datedCalendar ua ra ub rb, fun _ => 0, fun _ => []⟩ t ∧ t.pending = [] := by
  obtain ⟨pend, _⟩ := erase_run Prod.fst (datedCircuit gap wire) (circuit gap)
    (circuit_erases gap wire) d (zero 4) (zero 4)
    ((ua.length + 2 * ra.length + ub.length + 2 * rb.length) * 4)
    (start 4 (datedCalendar ua ra ub rb)) (start 4 (calendar ua.length ra.length ub.length rb.length))
    (fun _ => []) (datedCalendar_erase ua ra ub rb) rfl
  have gone := circuit_empties gap ua.length ra.length ub.length rb.length d
  rw [← pend] at gone
  exact dated_run_exists (datedCircuit gap wire) d (fun o => o.2) (circuit_commute gap wire)
    (circuit_wiring gap wire) (datedCalendar ua ra ub rb)
    (circuit_inv gap wire strict ua ra ub rb sa sb) _ (List.map_eq_nil_iff.mp gone)

end NetworkStability.CircuitNetwork
