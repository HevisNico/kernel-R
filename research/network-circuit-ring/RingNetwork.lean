import DatedOrder

/-!
# The periodic ring of circuit cells, for every N

An instance of the guarded model of `../network-stability/AutonomousFeedback.lean` for a ring of `N`
circuit cells with periodic launches, and what each port learns. Phase 0 of campaign 2, design only.

The ring has `N + 1` ports, in the order a pulse meets them: port 0 is the launch port of the root,
ports 1 to `N - 1` are the forward ports of the relays, port `N` is the return port of the root. A
pulse is named by the port it reads. A FIRE of port `k < N` sends one pulse to port `k + 1`; a FIRE
of port `N` sends nothing: the return port only acknowledges. The launches are a finite prefix of
the periodic calendar: `laps` pulses on port 0. The read law is that of `CircuitNetwork.lean`:

    score = - gap + d * (writes of that port),      FIRE iff 0 ≤ score + error.

Two results, both for every `N`, every gap and every number of laps.

1. **The certificate** (`certificate`, `ring_certified`, `ring_predicted`): the instance satisfies
   `AutonomousFeedback.certified_feedback`, as the two-cell network of campaign 1 does. No port has
   more than `laps` writes, the queue is empty after `laps * (N + 1)` reads whatever the errors, and
   with room on every read the run with errors is the zero-error run.

2. **What each port learns, port by port** (`ring_port_shaped`, `ring_words`). On the ring every
   pulse that waits on a port is the same probe, so the order in which the pulses are served does not
   matter, and no hypothesis on the dates is needed. Take any run that serves one pending pulse at a
   time, in any order, with each error inside the budget of the port read.
   - If the reads of port `k` have room (`Own`: `n` silent reads then a FIRE, each with room), port
     `k` makes at most `n` writes, its silent reads all come before its FIRE, and once it has fired
     it has exactly `n` writes, whatever the other ports do.
   - If the same holds for every port up to `k`, and the run ends with nothing pending, the word of
     port `k` is known exactly: `min n m` silent reads then `m - n` FIRE, where `m` is the number of
     pulses that the ports before it let through.

The order of the dates is one such order (`dated_any`), and so is the queue of the guarded model
(`queue_any`). What the model does not carry — the help of a recent pulse, the noise of the read,
the error of the measures — is in the error, bounded port by port.
-/

namespace NetworkStability.RingNetwork

open AutonomousFeedback
open RoutedCalendar (HasRoom)
open CircuitNetwork (PortMargins stepBound nominal_of_port)
open PortOrder (DState dserve DatedMove DatedReach portScore)

/-! ## The model and its certificate -/

/-- Port `k` sends to port `k + 1`; the return port sends nothing. -/
def next (N : Nat) (k : Fin (N + 1)) : List (Fin (N + 1)) :=
  if h : k.val < N then [⟨k.val + 1, Nat.succ_lt_succ h⟩] else []

/-- The ring as a guarded model: no drive term, one bias per port, a pulse named by its port. -/
def ring (N : Nat) (gap : Fin (N + 1) → Int) : Model (N + 1) (Fin (N + 1)) where
  cell := id
  bias := fun k => - gap k
  drive := fun _ => 0
  route := next N

/-- The launches of `laps` laps: pulses on the launch port. -/
def launches (N laps : Nat) : List (Fin (N + 1)) := List.replicate laps 0

/-- A pulse pays for itself and for every pulse it may cause down the chain. -/
def weight (N : Nat) (k : Fin (N + 1)) : Nat := N + 1 - k.val

/-- A pulse on port `k` may cause one write on each port from `k` on. -/
def reserve {N : Nat} (i k : Fin (N + 1)) : Nat := if k.val ≤ i.val then 1 else 0

theorem mass_replicate {P : Type} (w : P → Nat) (n : Nat) (p : P) :
    mass w (List.replicate n p) = n * w p := by
  induction n with
  | zero => simp [mass]
  | succ n ih =>
    simp only [mass, List.replicate_succ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.succ_mul, Nat.add_comm]

/-- At most `laps` writes on any port, and the queue is empty after `laps * (N + 1)` reads whatever
the errors. -/
def certificate (N : Nat) (gap : Fin (N + 1) → Int) (laps : Nat) :
    Certificate laps laps 1 (ring N gap) (launches N laps) where
  weight := weight N
  reserve := reserve
  eta_pos := Nat.one_pos
  scalar := by
    intro k
    have := k.isLt
    by_cases h : k.val < N
    · simp [ring, next, h, mass, weight]
      omega
    · simp [ring, next, h, mass, weight]
      omega
  local_route := by
    intro k i
    by_cases h : k.val < N
    · simp only [ring, next, h, mass, reserve, dite_true, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      split <;> split <;> omega
    · simp [ring, next, h, mass]
  local_write := by
    intro k
    simp [ring, reserve]
  seed_weight := by
    rw [launches, mass_replicate]
    simp [weight]
  seed_reserve := by
    intro i
    rw [launches, mass_replicate]
    simp [reserve]

/-- The network theorem for the ring, in its certified form. If the errors of the reads stay inside
`[lo, hi]` and every read of the zero-error run has room for them, the run with errors is the
zero-error run; the queue is empty at the end and stays so; and at every step, with or without room,
no port has more than `laps` writes and no stored value reaches the rail. -/
theorem ring_certified (N : Nat) (gap : Fin (N + 1) → Int) (laps d B rail : Nat)
    (base : Fin (N + 1) → Nat) (hbase : ∀ i, base i ≤ B) (headroom : B + d * laps < rail)
    (lo hi error : Nat → Int) (within : ∀ k, lo k ≤ error k ∧ error k ≤ hi k)
    (margins : NominalMargins (ring N gap) d lo hi (laps * (N + 1))
      (start (N + 1) (launches N laps))) :
    let terminal := run (ring N gap) d error (laps * (N + 1)) (start (N + 1) (launches N laps))
    terminal.pending = [] ∧
      terminal = run (ring N gap) d (fun _ => 0) (laps * (N + 1)) (start (N + 1) (launches N laps)) ∧
      (∀ n, run (ring N gap) d error n terminal = terminal) ∧
      ∀ n, let s := run (ring N gap) d error n (start (N + 1) (launches N laps))
        RoutedCalendar.total ⟨s.writes, []⟩ ≤ laps * (N + 1) ∧
        ∀ i, s.writes i ≤ laps ∧ base i ≤ base i + d * s.writes i ∧
          base i + d * s.writes i < rail :=
  certified_feedback laps d B rail laps 1 (ring N gap) (launches N laps) (certificate N gap laps)
    base hbase headroom lo hi error within margins

/-- The same with one budget per port, as the measures give them. -/
theorem ring_predicted (N : Nat) (gap : Fin (N + 1) → Int) (laps d B rail : Nat)
    (base : Fin (N + 1) → Nat) (hbase : ∀ i, base i ≤ B) (headroom : B + d * laps < rail)
    (lo hi : Fin (N + 1) → Int) (error : Nat → Int)
    (within : ∀ k, stepBound (ring N gap) d (start (N + 1) (launches N laps)) lo k ≤ error k ∧
      error k ≤ stepBound (ring N gap) d (start (N + 1) (launches N laps)) hi k)
    (margins : PortMargins (ring N gap) d lo hi (laps * (N + 1))
      (start (N + 1) (launches N laps))) :
    let terminal := run (ring N gap) d error (laps * (N + 1)) (start (N + 1) (launches N laps))
    terminal.pending = [] ∧
      terminal = run (ring N gap) d (fun _ => 0) (laps * (N + 1)) (start (N + 1) (launches N laps)) ∧
      (∀ n, run (ring N gap) d error n terminal = terminal) ∧
      ∀ n, let s := run (ring N gap) d error n (start (N + 1) (launches N laps))
        RoutedCalendar.total ⟨s.writes, []⟩ ≤ laps * (N + 1) ∧
        ∀ i, s.writes i ≤ laps ∧ base i ≤ base i + d * s.writes i ∧
          base i + d * s.writes i < rail :=
  ring_certified N gap laps d B rail base hbase headroom _ _ error within
    (nominal_of_port (ring N gap) d lo hi (start (N + 1) (launches N laps)) _ 0 (Or.inr rfl) margins)

/-! ## What each port learns, in any order of service -/

variable {N : Nat} {O : Type}

/-- The score of port `i` after `w` writes. -/
def scoreAt (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) (w : Nat) : Int :=
  - gap i + (d : Int) * w

/-- Port `i` needs `n` doses, and each of its reads has room for its budget: the `n` silent reads
stay silent under the largest error, the read after them is a FIRE under the smallest. -/
def Own (gap : Fin (N + 1) → Int) (d : Nat) (lo hi : Fin (N + 1) → Int) (i : Fin (N + 1))
    (n : Nat) : Prop :=
  (∀ w, w < n → scoreAt gap d i w < 0 ∧ scoreAt gap d i w + hi i < 0) ∧
    0 ≤ scoreAt gap d i n ∧ 0 ≤ scoreAt gap d i n + lo i

instance (gap : Fin (N + 1) → Int) (d : Nat) (lo hi : Fin (N + 1) → Int) (i : Fin (N + 1))
    (n : Nat) : Decidable (Own gap d lo hi i n) := by
  unfold Own
  exact inferInstance

/-- `w` silent reads of port `i`, latest first. -/
def silents (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) : Nat → List (Int × Bool)
  | 0 => []
  | w + 1 => (scoreAt gap d i w, false) :: silents gap d i w

/-- The reads of a port that needs `n` doses, after `w` silent reads then `f` FIRE, latest first. -/
def word (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) (n w f : Nat) : List (Int × Bool) :=
  List.replicate f (scoreAt gap d i n, true) ++ silents gap d i w

theorem silents_length (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) (w : Nat) :
    (silents gap d i w).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [silents, ih]

theorem silents_fired (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) (w : Nat) :
    (silents gap d i w).filter (fun r => r.2) = [] := by
  induction w with
  | zero => rfl
  | succ w ih => simp [silents, ih]

theorem word_length (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) (n w f : Nat) :
    (word gap d i n w f).length = f + w := by
  simp [word, silents_length]

theorem word_fired (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) (n w f : Nat) :
    ((word gap d i n w f).filter (fun r => r.2)).length = f := by
  simp [word, List.filter_append, silents_fired]

/-- A model that reads like the ring: the bias of a pulse is that of its port, and a pulse sends to
the ports that `next` names. The pulses may carry more than their port, a date for instance. -/
structure RingLike (N : Nat) (gap : Fin (N + 1) → Int) (M : Model (N + 1) O) : Prop where
  bias : ∀ o, M.bias o = - gap (M.cell o)
  drive : ∀ o, M.drive o = 0
  route : ∀ o, (M.route o).map M.cell = next N (M.cell o)

theorem ring_like (gap : Fin (N + 1) → Int) : RingLike N gap (ring N gap) where
  bias := fun _ => rfl
  drive := fun _ => rfl
  route := fun o => by simp [ring]

/-- Serve any pending pulse, with an error inside the budget of its port. -/
inductive AnyMove (M : Model (N + 1) O) (d : Nat) (lo hi : Fin (N + 1) → Int) :
    DState (N + 1) O → DState (N + 1) O → Prop
  | serve (s : DState (N + 1) O) (pre : List O) (p : O) (post : List O) (e : Int) :
      s.pending = pre ++ p :: post → lo (M.cell p) ≤ e → e ≤ hi (M.cell p) →
      AnyMove M d lo hi s (dserve M d s pre p post e)

inductive AnyReach (M : Model (N + 1) O) (d : Nat) (lo hi : Fin (N + 1) → Int) :
    DState (N + 1) O → DState (N + 1) O → Prop
  | nil (s : DState (N + 1) O) : AnyReach M d lo hi s s
  | cons {s t u : DState (N + 1) O} :
      AnyMove M d lo hi s t → AnyReach M d lo hi t u → AnyReach M d lo hi s u

/-- The reads of port `i` so far are silent reads then FIRE, with at most `n` writes, and `n` writes
exactly once it has fired. -/
def Shaped (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) (n : Nat)
    (s : DState (N + 1) O) : Prop :=
  ∃ f, s.reads i = word gap d i n (s.writes i) f ∧ s.writes i ≤ n ∧ (0 < f → s.writes i = n)

theorem dserve_writes (M : Model (N + 1) O) (d : Nat) (s : DState (N + 1) O) (pre : List O) (p : O)
    (post : List O) (e : Int) (k : Fin (N + 1)) :
    (dserve M d s pre p post e).writes k = s.writes k +
      if k = M.cell p ∧ decide (0 ≤ portScore M d s.writes (M.cell p) p + e) = false then 1 else 0 :=
  rfl

theorem dserve_reads (M : Model (N + 1) O) (d : Nat) (s : DState (N + 1) O) (pre : List O) (p : O)
    (post : List O) (e : Int) (k : Fin (N + 1)) :
    (dserve M d s pre p post e).reads k =
      if k = M.cell p then (portScore M d s.writes (M.cell p) p,
        decide (0 ≤ portScore M d s.writes (M.cell p) p + e)) :: s.reads k else s.reads k :=
  rfl

theorem dserve_pending (M : Model (N + 1) O) (d : Nat) (s : DState (N + 1) O) (pre : List O) (p : O)
    (post : List O) (e : Int) :
    (dserve M d s pre p post e).pending = pre ++ post ++
      (if decide (0 ≤ portScore M d s.writes (M.cell p) p + e) then M.route p else []) :=
  rfl

/-- A move keeps the shape of the reads of a port whose own reads have room, whichever port it
serves. -/
theorem shaped_move {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} (rl : RingLike N gap M)
    {d : Nat} {lo hi : Fin (N + 1) → Int} {i : Fin (N + 1)} {n : Nat} (own : Own gap d lo hi i n)
    {s t : DState (N + 1) O} (sh : Shaped gap d i n s) (move : AnyMove M d lo hi s t) :
    Shaped gap d i n t := by
  cases move with
  | serve pre p post e hp hlo hhi =>
    obtain ⟨f, hr, hw, hf⟩ := sh
    by_cases hc : i = M.cell p
    · subst hc
      have sc : portScore M d s.writes (M.cell p) p =
          scoreAt gap d (M.cell p) (s.writes (M.cell p)) := by
        simp [portScore, scoreAt, rl.bias, rl.drive]
      by_cases lt : s.writes (M.cell p) < n
      · have f0 : f = 0 := by
          cases f with
          | zero => rfl
          | succ f =>
            have := hf (Nat.succ_pos f)
            omega
        have room := own.1 _ lt
        have silent : decide (0 ≤ portScore M d s.writes (M.cell p) p + e) = false := by
          rw [sc]
          simp only [decide_eq_false_iff_not]
          omega
        refine ⟨0, ?_, ?_, ?_⟩
        · rw [dserve_reads, dserve_writes, silent]
          simp [hr, f0, word, silents, sc]
        · rw [dserve_writes]
          simp only [silent, and_self, ite_true]
          omega
        · intro h
          cases h
      · have eq : s.writes (M.cell p) = n := by omega
        have room := own.2.2
        have fire : decide (0 ≤ portScore M d s.writes (M.cell p) p + e) = true := by
          rw [sc, eq]
          simp only [decide_eq_true_eq]
          omega
        refine ⟨f + 1, ?_, ?_, ?_⟩
        · rw [dserve_reads, dserve_writes, fire]
          simp [hr, word, List.replicate_succ, sc, eq]
        · rw [dserve_writes]
          simp [fire, eq]
        · intro _
          rw [dserve_writes]
          simp [fire, eq]
    · refine ⟨f, ?_, ?_, ?_⟩
      · rw [dserve_reads, dserve_writes]
        simp [hc, hr]
      · rw [dserve_writes]
        simp [hc, hw]
      · intro pos
        rw [dserve_writes]
        simp [hc, hf pos]

theorem shaped_reach {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} (rl : RingLike N gap M)
    {d : Nat} {lo hi : Fin (N + 1) → Int} {i : Fin (N + 1)} {n : Nat} (own : Own gap d lo hi i n)
    {s t : DState (N + 1) O} (path : AnyReach M d lo hi s t) (sh : Shaped gap d i n s) :
    Shaped gap d i n t := by
  induction path with
  | nil => exact sh
  | cons move _ ih => exact ih (shaped_move rl own sh move)

/-! ### Counting the pulses -/

/-- The pulses of `l` that wait on port `k`. -/
def waiting (M : Model (N + 1) O) (l : List O) (k : Fin (N + 1)) : Nat :=
  (l.filter (fun q => M.cell q = k)).length

def served (s : DState (N + 1) O) (k : Fin (N + 1)) : Nat := (s.reads k).length

def fired (s : DState (N + 1) O) (k : Fin (N + 1)) : Nat := ((s.reads k).filter (fun r => r.2)).length

theorem waiting_append (M : Model (N + 1) O) (a b : List O) (k : Fin (N + 1)) :
    waiting M (a ++ b) k = waiting M a k + waiting M b k := by
  simp [waiting, List.filter_append]

theorem waiting_cons (M : Model (N + 1) O) (p : O) (l : List O) (k : Fin (N + 1)) :
    waiting M (p :: l) k = (if (M.cell p).val = k.val then 1 else 0) + waiting M l k := by
  by_cases h : M.cell p = k
  · simp [waiting, h]
    omega
  · have : ¬ (M.cell p).val = k.val := fun e => h (Fin.ext e)
    simp [waiting, h, this]

theorem waiting_map (M : Model (N + 1) O) (l : List O) (k : Fin (N + 1)) :
    waiting M l k = ((l.map M.cell).filter (fun c => c = k)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    unfold waiting at ih ⊢
    by_cases h : M.cell a = k <;> simp [h, ih]

theorem waiting_route {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} (rl : RingLike N gap M) (p : O)
    (k : Fin (N + 1)) :
    waiting M (M.route p) k = if (M.cell p).val < N ∧ k.val = (M.cell p).val + 1 then 1 else 0 := by
  rw [waiting_map, rl.route]
  unfold next
  by_cases h : (M.cell p).val < N
  · by_cases hk : k.val = (M.cell p).val + 1
    · have : (⟨(M.cell p).val + 1, Nat.succ_lt_succ h⟩ : Fin (N + 1)) = k := Fin.ext hk.symm
      simp [h, hk, this]
    · have : ¬ (⟨(M.cell p).val + 1, Nat.succ_lt_succ h⟩ : Fin (N + 1)) = k :=
        fun e => hk (congrArg Fin.val e).symm
      simp [h, hk, this]
  · simp [h]

/-- The pulses are conserved: the launch port receives the `laps` launches, and each other port
receives one pulse per FIRE of the port before it. -/
structure Counted (M : Model (N + 1) O) (laps : Nat) (s : DState (N + 1) O) : Prop where
  root : waiting M s.pending ⟨0, Nat.succ_pos N⟩ + served s ⟨0, Nat.succ_pos N⟩ = laps
  chain : ∀ (k : Fin (N + 1)) (h : k.val < N),
    waiting M s.pending ⟨k.val + 1, Nat.succ_lt_succ h⟩ + served s ⟨k.val + 1, Nat.succ_lt_succ h⟩ =
      fired s k

theorem served_dserve (M : Model (N + 1) O) (d : Nat) (s : DState (N + 1) O) (pre : List O) (p : O)
    (post : List O) (e : Int) (k : Fin (N + 1)) :
    served (dserve M d s pre p post e) k = served s k + if k.val = (M.cell p).val then 1 else 0 := by
  unfold served
  rw [dserve_reads]
  by_cases h : k = M.cell p
  · simp [h]
  · have : ¬ k.val = (M.cell p).val := fun e => h (Fin.ext e)
    simp [h, this]

theorem fired_dserve (M : Model (N + 1) O) (d : Nat) (s : DState (N + 1) O) (pre : List O) (p : O)
    (post : List O) (e : Int) (k : Fin (N + 1)) :
    fired (dserve M d s pre p post e) k = fired s k +
      if k.val = (M.cell p).val ∧ decide (0 ≤ portScore M d s.writes (M.cell p) p + e) = true
        then 1 else 0 := by
  unfold fired
  rw [dserve_reads]
  by_cases h : k = M.cell p
  · cases hb : decide (0 ≤ portScore M d s.writes (M.cell p) p + e) <;> simp [h]
  · have : ¬ k.val = (M.cell p).val := fun e => h (Fin.ext e)
    simp [h, this]

theorem waiting_dserve {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} (rl : RingLike N gap M)
    (d : Nat) (s : DState (N + 1) O) (pre : List O) (p : O) (post : List O) (e : Int)
    (hp : s.pending = pre ++ p :: post) (k : Fin (N + 1)) :
    waiting M (dserve M d s pre p post e).pending k + (if (M.cell p).val = k.val then 1 else 0) =
      waiting M s.pending k +
        if decide (0 ≤ portScore M d s.writes (M.cell p) p + e) = true ∧
          (M.cell p).val < N ∧ k.val = (M.cell p).val + 1 then 1 else 0 := by
  rw [dserve_pending, hp, waiting_append, waiting_append, waiting_append, waiting_cons]
  cases hb : decide (0 ≤ portScore M d s.writes (M.cell p) p + e)
  · simp [waiting]
    omega
  · simp only [ite_true, true_and, waiting_route rl]
    omega

theorem counted_move {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} (rl : RingLike N gap M)
    {d : Nat} {lo hi : Fin (N + 1) → Int} {laps : Nat} {s t : DState (N + 1) O}
    (cnt : Counted M laps s) (move : AnyMove M d lo hi s t) : Counted M laps t := by
  cases move with
  | serve pre p post e hp hlo hhi =>
    constructor
    · have w := waiting_dserve rl d s pre p post e hp ⟨0, Nat.succ_pos N⟩
      have r := served_dserve M d s pre p post e ⟨0, Nat.succ_pos N⟩
      have base := cnt.root
      simp only at w r
      split at w <;> split at w <;> split at r <;> omega
    · intro k h
      have w := waiting_dserve rl d s pre p post e hp ⟨k.val + 1, Nat.succ_lt_succ h⟩
      have r := served_dserve M d s pre p post e ⟨k.val + 1, Nat.succ_lt_succ h⟩
      have f := fired_dserve M d s pre p post e k
      have base := cnt.chain k h
      simp only at w r
      cases hb : decide (0 ≤ portScore M d s.writes (M.cell p) p + e) <;>
        simp only [hb, Bool.false_eq_true, false_and, and_false, true_and, and_true, ite_false] at w f <;>
        (repeat' split at w) <;> (repeat' split at r) <;> (repeat' split at f) <;> omega

theorem counted_reach {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} (rl : RingLike N gap M)
    {d : Nat} {lo hi : Fin (N + 1) → Int} {laps : Nat} {s t : DState (N + 1) O}
    (path : AnyReach M d lo hi s t) (cnt : Counted M laps s) : Counted M laps t := by
  induction path with
  | nil => exact cnt
  | cons move _ ih => exact ih (counted_move rl cnt move)

/-! ### The words -/

/-- The pulses that reach port `k`: every launch reaches the launch port, and a port lets through
what it receives beyond its need. -/
def arriving (need : Nat → Nat) (laps : Nat) : Nat → Nat
  | 0 => laps
  | k + 1 => arriving need laps k - need k

/-- The start of a run: the launches pending, no write, no read. -/
def opening (seed : List O) : DState (N + 1) O := ⟨seed, fun _ => 0, fun _ => []⟩

theorem shaped_opening (gap : Fin (N + 1) → Int) (d : Nat) (i : Fin (N + 1)) (n : Nat)
    (seed : List O) : Shaped gap d i n (opening seed) :=
  ⟨0, rfl, Nat.zero_le n, fun h => absurd h (Nat.lt_irrefl 0)⟩

theorem waiting_home (M : Model (N + 1) O) (seed : List O) (home : ∀ o ∈ seed, (M.cell o).val = 0)
    (k : Fin (N + 1)) : waiting M seed k = if k.val = 0 then seed.length else 0 := by
  induction seed with
  | nil => simp [waiting]
  | cons o l ih =>
    have h0 := home o List.mem_cons_self
    have rest := ih (fun q hq => home q (List.mem_cons_of_mem _ hq))
    rw [waiting_cons, rest, h0]
    by_cases hk : k.val = 0
    · simp [hk]
      omega
    · have : ¬ 0 = k.val := fun e => hk e.symm
      simp [hk, this]

theorem counted_opening (M : Model (N + 1) O) (seed : List O)
    (home : ∀ o ∈ seed, (M.cell o).val = 0) : Counted M seed.length (opening seed) where
  root := by
    show waiting M seed _ + 0 = seed.length
    rw [waiting_home M seed home]
    simp
  chain := by
    intro k h
    show waiting M seed _ + 0 = 0
    rw [waiting_home M seed home]
    simp

/-- At the end, every port up to `k` has read exactly the pulses that the ports before it let
through. -/
theorem served_arriving {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} {d laps : Nat}
    (need : Nat → Nat) (k : Fin (N + 1)) {t : DState (N + 1) O} (cnt : Counted M laps t)
    (done : t.pending = [])
    (shaped : ∀ j : Fin (N + 1), j.val ≤ k.val → Shaped gap d j (need j.val) t) :
    ∀ j (hj : j ≤ k.val), served t ⟨j, Nat.lt_of_le_of_lt hj k.isLt⟩ = arriving need laps j := by
  intro j
  induction j with
  | zero =>
    intro _
    have root := cnt.root
    rw [done] at root
    simpa [waiting, arriving] using root
  | succ j ih =>
    intro hj
    have hjk : j ≤ k.val := by omega
    have prev := ih hjk
    have hN : j < N := by
      have := k.isLt
      omega
    have link := cnt.chain ⟨j, Nat.lt_of_le_of_lt hjk k.isLt⟩ hN
    rw [done] at link
    obtain ⟨f, hr, hw, hf⟩ := shaped ⟨j, Nat.lt_of_le_of_lt hjk k.isLt⟩ hjk
    have hw' : t.writes ⟨j, Nat.lt_of_le_of_lt hjk k.isLt⟩ ≤ need j := hw
    have hf' : 0 < f → t.writes ⟨j, Nat.lt_of_le_of_lt hjk k.isLt⟩ = need j := hf
    have len : served t ⟨j, Nat.lt_of_le_of_lt hjk k.isLt⟩ =
        f + t.writes ⟨j, Nat.lt_of_le_of_lt hjk k.isLt⟩ := by
      unfold served
      rw [hr, word_length]
    have fr : fired t ⟨j, Nat.lt_of_le_of_lt hjk k.isLt⟩ = f := by
      unfold fired
      rw [hr, word_fired]
    simp only [waiting, List.filter_nil, List.length_nil, Nat.zero_add] at link
    simp only [arriving]
    rw [link, fr]
    cases f with
    | zero => omega
    | succ f =>
      have := hf' (Nat.succ_pos f)
      omega

/-- **Own room: the learned state of a port.** In any run from the launches, in any order of
service and with errors inside the budgets, a port whose own reads have room has read silent reads
then FIRE, has at most `n` writes, and has exactly `n` writes once it has fired, whatever the other
ports did. -/
theorem ring_port_shaped {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} (rl : RingLike N gap M)
    {d : Nat} {lo hi : Fin (N + 1) → Int} (seed : List O) (i : Fin (N + 1)) (n : Nat)
    (own : Own gap d lo hi i n) {t : DState (N + 1) O}
    (path : AnyReach M d lo hi (opening seed) t) :
    ∃ f, t.reads i = word gap d i n (t.writes i) f ∧ t.writes i ≤ n ∧ (0 < f → t.writes i = n) :=
  shaped_reach rl own path (shaped_opening gap d i n seed)

/-- **Room up to port `k`: the word of port `k`.** Take any run from the launches, in any order of
service and with errors inside the budgets, that ends with nothing pending. If every port up to `k`
has room for its own reads, port `k` has `min (need k) m` writes, and its reads are these silent
reads then `m - need k` FIRE, where `m = arriving need laps k` is the number of pulses that the ports
before it let through. Nothing is asked of the ports after `k`. -/
theorem ring_words {gap : Fin (N + 1) → Int} {M : Model (N + 1) O} (rl : RingLike N gap M)
    {d : Nat} {lo hi : Fin (N + 1) → Int} (need : Nat → Nat) (seed : List O)
    (home : ∀ o ∈ seed, (M.cell o).val = 0) (k : Fin (N + 1))
    (own : ∀ j : Fin (N + 1), j.val ≤ k.val → Own gap d lo hi j (need j.val))
    {t : DState (N + 1) O} (path : AnyReach M d lo hi (opening seed) t) (done : t.pending = []) :
    t.writes k = min (need k.val) (arriving need seed.length k.val) ∧
      t.reads k = word gap d k (need k.val) (min (need k.val) (arriving need seed.length k.val))
        (arriving need seed.length k.val - need k.val) := by
  have cnt := counted_reach rl path (counted_opening M seed home)
  have shaped : ∀ j : Fin (N + 1), j.val ≤ k.val → Shaped gap d j (need j.val) t :=
    fun j hj => shaped_reach rl (own j hj) path (shaped_opening gap d j (need j.val) seed)
  have total := served_arriving need k cnt done shaped k.val (Nat.le_refl _)
  obtain ⟨f, hr, hw, hf⟩ := shaped k (Nat.le_refl _)
  have len : served t k = f + t.writes k := by
    unfold served
    rw [hr, word_length]
  have total' : served t k = arriving need seed.length k.val := total
  have both : t.writes k = min (need k.val) (arriving need seed.length k.val) ∧
      f = arriving need seed.length k.val - need k.val := by
    cases f with
    | zero => omega
    | succ f =>
      have := hf (Nat.succ_pos f)
      omega
  exact ⟨both.1, by rw [hr, both.1, both.2]⟩

/-! ## The order of the dates, and the queue of the guarded model -/

/-- The ring with dated pulses: a FIRE of port `k` at date `t` sends a pulse dated `wire k t`. -/
def datedRing (N : Nat) (gap : Fin (N + 1) → Int) (wire : Nat → Nat → Nat) :
    Model (N + 1) (Fin (N + 1) × Nat) where
  cell := fun o => o.1
  bias := fun o => - gap o.1
  drive := fun _ => 0
  route := fun o => (next N o.1).map (fun k => (k, wire o.1.val o.2))

theorem dated_ring_like (gap : Fin (N + 1) → Int) (wire : Nat → Nat → Nat) :
    RingLike N gap (datedRing N gap wire) where
  bias := fun _ => rfl
  drive := fun _ => rfl
  route := fun o => by simp [datedRing, List.map_map, Function.comp_def]

/-- The launches at their dates. -/
def datedLaunches (N : Nat) (dates : List Nat) : List (Fin (N + 1) × Nat) :=
  dates.map (fun t => (⟨0, Nat.succ_pos N⟩, t))

theorem dated_any {M : Model (N + 1) O} {d : Nat} {lo hi : Fin (N + 1) → Int} {date : O → Nat}
    {s t : DState (N + 1) O} (move : DatedMove M d lo hi date s t) : AnyMove M d lo hi s t := by
  cases move with
  | serve pre p post e hp _ hlo hhi => exact .serve _ pre p post e hp hlo hhi

theorem dated_reach_any {M : Model (N + 1) O} {d : Nat} {lo hi : Fin (N + 1) → Int} {date : O → Nat}
    {m : Nat} {s t : DState (N + 1) O} (path : DatedReach M d lo hi date m s t) :
    AnyReach M d lo hi s t := by
  induction path with
  | nil => exact .nil _
  | cons move _ ih => exact .cons (dated_any move) ih

/-- **The ring in the order of the dates.** Every run that serves the pulses in the order of their
dates, with errors inside the budgets, and ends with nothing pending, gives port `k` its word, if
every port up to `k` has room. Two pulses with the same date may be served either way: no condition
on the dates or on the wires is needed. -/
theorem ring_dated_words (gap : Fin (N + 1) → Int) (wire : Nat → Nat → Nat) (d : Nat)
    (lo hi : Fin (N + 1) → Int) (need : Nat → Nat) (dates : List Nat) (k : Fin (N + 1))
    (own : ∀ j : Fin (N + 1), j.val ≤ k.val → Own gap d lo hi j (need j.val))
    {m : Nat} {t : DState (N + 1) (Fin (N + 1) × Nat)}
    (path : DatedReach (datedRing N gap wire) d lo hi (fun o => o.2) m
      (opening (datedLaunches N dates)) t) (done : t.pending = []) :
    t.writes k = min (need k.val) (arriving need dates.length k.val) ∧
      t.reads k = word gap d k (need k.val) (min (need k.val) (arriving need dates.length k.val))
        (arriving need dates.length k.val - need k.val) := by
  have home : ∀ o ∈ datedLaunches N dates, ((datedRing N gap wire).cell o).val = 0 := by
    intro o mem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp mem
    rfl
  have result := ring_words (dated_ring_like gap wire) need (datedLaunches N dates) home k own
    (dated_reach_any path) done
  simpa [datedLaunches] using result

/-- The zero-error queue run of the guarded model serves one pending pulse at a time. -/
theorem queue_any (M : Model (N + 1) O) (d : Nat) (lo hi : Fin (N + 1) → Int)
    (zero_in : ∀ i, lo i ≤ 0 ∧ 0 ≤ hi i) :
    ∀ n (s : State (N + 1) O) (r : Fin (N + 1) → List (Int × Bool)),
      AnyReach M d lo hi ⟨s.pending, s.writes, r⟩
        ⟨(run M d (fun _ => 0) n s).pending, (run M d (fun _ => 0) n s).writes,
          PortOrder.record M d n s r⟩ := by
  intro n
  induction n with
  | zero => exact fun s r => .nil _
  | succ n ih =>
    intro s r
    cases h : s.pending with
    | nil =>
      have stay : run M d (fun _ => 0) (n + 1) s = s := run_empty M d _ _ s h
      rw [stay, h]
      simp only [PortOrder.record, h]
      exact .nil _
    | cons p tail =>
      have move : AnyMove M d lo hi ⟨s.pending, s.writes, r⟩
          (dserve M d ⟨s.pending, s.writes, r⟩ [] p tail 0) :=
        .serve _ [] p tail 0 h (zero_in _).1 (zero_in _).2
      have rest := ih (step M d 0 s)
        (fun k => if k = M.cell p then (score M d s p, fires M d s p 0) :: r k else r k)
      have same : dserve M d ⟨s.pending, s.writes, r⟩ [] p tail 0 =
          ⟨(step M d 0 s).pending, (step M d 0 s).writes,
            fun k => if k = M.cell p then (score M d s p, fires M d s p 0) :: r k else r k⟩ := by
        simp [dserve, step, h, fires, score, portScore]
      have unfold_run : run M d (fun _ => 0) (n + 1) s = run M d (fun _ => 0) n (step M d 0 s) := rfl
      have unfold_record : PortOrder.record M d (n + 1) s r = PortOrder.record M d n (step M d 0 s)
          (fun k => if k = M.cell p then (score M d s p, fires M d s p 0) :: r k else r k) := by
        simp only [PortOrder.record, h]
      rw [unfold_run, unfold_record, ← h]
      rw [same] at move
      exact .cons move rest

/-- **The zero-error words, in closed form, for every N.** The queue run of the guarded model of the
ring, without error: if `need j` is the need of each port `j` up to `k`, port `k` ends with
`min (need k) m` writes and its reads are these silent reads then `m - need k` FIRE, with
`m = arriving need laps k`. -/
theorem ring_queue_words (gap : Fin (N + 1) → Int) (laps d : Nat) (need : Nat → Nat)
    (k : Fin (N + 1))
    (own : ∀ j : Fin (N + 1), j.val ≤ k.val →
      Own gap d (PortOrder.zero (N + 1)) (PortOrder.zero (N + 1)) j (need j.val)) :
    (run (ring N gap) d (fun _ => 0) (laps * (N + 1)) (start (N + 1) (launches N laps))).writes k =
        min (need k.val) (arriving need laps k.val) ∧
      PortOrder.record (ring N gap) d (laps * (N + 1)) (start (N + 1) (launches N laps))
          (fun _ => []) k =
        word gap d k (need k.val) (min (need k.val) (arriving need laps k.val))
          (arriving need laps k.val - need k.val) := by
  have cert := certificate N gap laps
  have empty : (run (ring N gap) d (fun _ => 0) (laps * (N + 1))
      (start (N + 1) (launches N laps))).pending = [] :=
    terminal_by_budget (ring N gap) d 1 cert.weight Nat.one_pos cert.scalar _ _ _
      (by rw [Nat.one_mul]; exact cert.seed_weight)
  have path := queue_any (ring N gap) d (PortOrder.zero (N + 1)) (PortOrder.zero (N + 1))
    (fun _ => ⟨Int.le_refl 0, Int.le_refl 0⟩) (laps * (N + 1)) (start (N + 1) (launches N laps))
    (fun _ => [])
  have home : ∀ o ∈ launches N laps, ((ring N gap).cell o).val = 0 := by
    intro o mem
    rw [List.eq_of_mem_replicate mem]
    rfl
  have result := ring_words (ring_like gap) need (launches N laps) home k own path empty
  simpa [launches] using result

/-! ## The nominal cell of phase 0

One dose is 100 000 units. The measured gap of each port of the nominal cell is 3.59378 doses, and
the error budget used in `CircuitNetwork.lean` is +0.26 and -0.23 dose. -/

def nominalGap (N : Nat) : Fin (N + 1) → Int := fun _ => 359378

/-- For every N, every port of the nominal ring needs four doses, with room. -/
theorem nominal_own (N : Nat) (k : Fin (N + 1)) :
    Own (nominalGap N) 100000 (fun _ => -23000) (fun _ => 26000) k 4 := by
  unfold Own scoreAt nominalGap
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    dsimp only
    omega
  · omega
  · dsimp only
    omega

/-- For every N and every number of laps: in any order of service, with errors inside the budget,
port `k` of the nominal ring ends with four writes if at least `4 * (k + 1)` laps are launched, and
has then fired `laps - 4 * (k + 1)` times: the ring is frozen from lap `4 * (N + 1)` on. -/
theorem nominal_ring (N : Nat) (wire : Nat → Nat → Nat) (dates : List Nat) (k : Fin (N + 1))
    (enough : 4 * (k.val + 1) ≤ dates.length) {m : Nat} {t : DState (N + 1) (Fin (N + 1) × Nat)}
    (path : DatedReach (datedRing N (nominalGap N) wire) 100000 (fun _ => -23000) (fun _ => 26000)
      (fun o => o.2) m (opening (datedLaunches N dates)) t) (done : t.pending = []) :
    t.writes k = 4 ∧ fired t k = dates.length - 4 * (k.val + 1) := by
  have result := ring_dated_words (nominalGap N) wire 100000 (fun _ => -23000) (fun _ => 26000)
    (fun _ => 4) dates k (fun j _ => nominal_own N j) path done
  have count : ∀ j, arriving (fun _ => 4) dates.length j = dates.length - 4 * j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [arriving, ih]
      omega
  rw [count] at result
  refine ⟨by rw [result.1]; omega, ?_⟩
  unfold fired
  rw [result.2, word_fired]
  omega

/-- The same instance through the certificate, for N = 3 and 26 laps, and N = 6 and 38 laps: every
read of the zero-error queue run has room for the budget, checked by the kernel. -/
example : PortMargins (ring 3 (nominalGap 3)) 100000 (fun _ => -23000) (fun _ => 26000) (26 * 4)
    (start 4 (launches 3 26)) := by decide +kernel

example : PortMargins (ring 6 (nominalGap 6)) 100000 (fun _ => -23000) (fun _ => 26000) (38 * 7)
    (start 7 (launches 6 38)) := by decide +kernel

/-- Every port ends with four writes and nothing is left to do. -/
example : (run (ring 3 (nominalGap 3)) 100000 (fun _ => 0) (26 * 4) (start 4 (launches 3 26))).pending = [] ∧
    ∀ i, (run (ring 3 (nominalGap 3)) 100000 (fun _ => 0) (26 * 4) (start 4 (launches 3 26))).writes i = 4 := by
  decide +kernel

/-- A larger positive error has no room at the fourth read of a port: 0.59378 dose is all there is. -/
example : ¬ Own (nominalGap 3) 100000 (fun _ => -23000) (fun _ => 60000) 0 4 := by decide +kernel

/-- A port that would need a different number of doses is not `Own` with four. -/
example : ¬ Own (fun _ : Fin 4 => 459378) 100000 (fun _ => -23000) (fun _ => 26000) 0 4 := by
  decide +kernel

end NetworkStability.RingNetwork
