import ScheduleConfluence

namespace NetworkStability.AutonomousFeedback.Schedule

/-- A sampled scheduler run admits finite batches of certified steps,
including idle samples. Each processed probe carries its own read margin. -/
structure Execution (M : Model N P) (d : Nat) (seed : List P) where
  state : Nat → State N P
  initial : state 0 = start N seed
  next : ∀ n, CertifiedTrace M d (state n) (state (n + 1))

def seedConfig (N : Nat) (seed : List P) : Config N P := ⟨seed, fun _ => 0⟩

/-- Continuation fairness for memory: every write count attainable by a
finite legal continuation of a prefix is eventually matched or exceeded.
This is an explicit scheduler assumption, stronger than token service. -/
def WriteFair {M : Model N P} {d : Nat} {seed : List P} (r : Execution M d seed) : Prop :=
  ∀ k t, Path M d (project (r.state k)) t →
    ∀ i, ∃ j, k ≤ j ∧ t.writes i ≤ (r.state j).writes i

def Stable {M : Model N P} {d : Nat} {seed : List P} (r : Execution M d seed)
    (counts : Fin N → Nat) : Prop :=
  ∃ cut, ∀ n, cut ≤ n → (r.state n).writes = counts

theorem reaches {M : Model N P} {d : Nat} {seed : List P} (r : Execution M d seed) (n : Nat) :
    Path M d (seedConfig N seed) (project (r.state n)) := by
  induction n with
  | zero => rw [r.initial]; exact .nil _
  | succ n ih => exact path_trans M d ih (certified_trace_projects M d (r.next n))

theorem move_writes_mono {s t : Config N P} (mv : Move M d s t) (i : Fin N) :
    s.writes i ≤ t.writes i := by
  cases mv
  exact Nat.le_add_right _ _

theorem path_writes_mono {s t : Config N P} (path : Path M d s t) (i : Fin N) :
    s.writes i ≤ t.writes i := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons mv _ ih => exact Nat.le_trans (move_writes_mono mv i) ih

theorem mass_permutation (weight : P → Nat) {a b : List P} (same : a.Perm b) :
    mass weight a = mass weight b := by
  induction same with
  | nil => rfl
  | cons x _ ih => exact congrArg (weight x + ·) ih
  | swap x y rest => simp [mass, Nat.add_left_comm]
  | trans _ _ ab bc => exact ab.trans bc

theorem move_reserve {M : Model N P} {d : Nat} {seed : List P}
    (cert : LocalReserve Q M seed) {s t : Config N P} (mv : Move M d s t) (i : Fin N) :
    t.writes i + mass (cert.reserve i) t.pending ≤
      s.writes i + mass (cert.reserve i) s.pending := by
  cases mv with
  | select p tail available =>
    have transport := mass_permutation (cert.reserve i) available
    have h := step_local M d cert.reserve cert.route cert.write 0
      (⟨p :: tail, s.writes, []⟩ : State N P) i
    change (process M d s p tail).writes i + mass (cert.reserve i) (process M d s p tail).pending ≤
      s.writes i + mass (cert.reserve i) s.pending
    rw [transport]
    exact h

theorem path_reserve {M : Model N P} {d : Nat} {seed : List P}
    (cert : LocalReserve Q M seed) {s t : Config N P} (path : Path M d s t) (i : Fin N) :
    t.writes i + mass (cert.reserve i) t.pending ≤
      s.writes i + mass (cert.reserve i) s.pending := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons mv _ ih => exact Nat.le_trans ih (move_reserve cert mv i)

theorem reachable_bound (Q d : Nat) {N : Nat} {P : Type} {M : Model N P}
    {seed : List P} (cert : LocalReserve Q M seed) {s : Config N P}
    (path : Path M d (seedConfig N seed) s) (i : Fin N) : s.writes i ≤ Q := by
  have accounting := path_reserve cert path i
  have initial := cert.initial i
  change _ ≤ 0 + mass (cert.reserve i) seed at accounting
  omega

private theorem finite_max (f : Nat → Nat) (bound : Nat) (h : ∀ n, f n ≤ bound) :
    ∃ n, ∀ m, f m ≤ f n := by
  induction bound with
  | zero => exact ⟨0, fun k => Nat.le_trans (h k) (Nat.zero_le _)⟩
  | succ bound ih =>
    classical
    by_cases hit : ∃ n, f n = bound + 1
    · obtain ⟨n, eq⟩ := hit
      exact ⟨n, fun m => eq ▸ h m⟩
    · exact ih (fun n => by
        have unequal : f n ≠ bound + 1 := fun eq => hit ⟨n, eq⟩
        have := h n
        omega)

theorem execution_stabilizes (Q d : Nat) {N : Nat} {P : Type} {M : Model N P}
    {seed : List P} (cert : LocalReserve Q M seed) (r : Execution M d seed) :
    ∃ counts, Stable r counts := by
  have mono (n m : Nat) (h : n ≤ m) (i : Fin N) : (r.state n).writes i ≤ (r.state m).writes i := by
    induction h with
    | refl => exact Nat.le_refl _
    | @step m _ ih =>
      exact Nat.le_trans ih (path_writes_mono (certified_trace_projects M d (r.next m)) i)
  have maxAt (i : Fin N) : ∃ t, ∀ k, (r.state k).writes i ≤ (r.state t).writes i :=
    finite_max (fun n => (r.state n).writes i) Q
      (fun n => reachable_bound Q d cert (reaches r n) i)
  let cuts := fun i => Classical.choose (maxAt i)
  let cut := ((List.finRange N).map cuts).sum
  have le_sum (xs : List (Fin N)) (i : Fin N) (mem : i ∈ xs) :
      cuts i ≤ (xs.map cuts).sum := by
    induction xs with
    | nil => simp at mem
    | cons j rest ih =>
      rcases List.mem_cons.mp mem with eq | tail
      · subst j
        simp
      · have h := ih tail
        simp only [List.map_cons, List.sum_cons]
        omega
  refine ⟨(r.state cut).writes, cut, fun n later => funext fun i => ?_⟩
  have leCut : cuts i ≤ cut := le_sum _ i (List.mem_finRange i)
  have atMax := Classical.choose_spec (maxAt i) n
  exact Nat.le_antisymm (Nat.le_trans atMax (mono _ _ leCut i)) (mono _ _ later i)

theorem fair_cut_closed {M : Model N P} {d : Nat} {seed : List P}
    (r : Execution M d seed) (fair : WriteFair r) (counts : Fin N → Nat) (cut : Nat)
    (frozen : ∀ n, cut ≤ n → (r.state n).writes = counts) :
    ∀ t, Path M d (project (r.state cut)) t → t.writes = counts := by
  intro t path
  funext i
  obtain ⟨j, after, catches⟩ := fair cut t path i
  have lower := path_writes_mono path i
  change (r.state cut).writes i ≤ _ at lower
  rw [frozen cut (Nat.le_refl _)] at lower
  rw [frozen j after] at catches
  exact Nat.le_antisymm catches lower

theorem fair_limit_unique (M : Model N P) (d : Nat) (seed : List P)
    (diamond : ∀ s, Path M d (seedConfig N seed) s → Exclusive M s ∨ PairMargins M d s)
    (a b : Execution M d seed) (fa : WriteFair a) (fb : WriteFair b)
    {x y : Fin N → Nat} (sx : Stable a x) (sy : Stable b y) : x = y := by
  obtain ⟨u, hu⟩ := sx
  obtain ⟨v, hv⟩ := sy
  have same := write_closed_memory_unique M d (seedConfig N seed) diamond (reaches a u) (reaches b v)
    (fun t p => (fair_cut_closed a fa x u hu t p).trans (hu u (Nat.le_refl _)).symm)
    (fun t p => (fair_cut_closed b fb y v hv t p).trans (hv v (Nat.le_refl _)).symm)
  exact (hu u (Nat.le_refl _)).symm.trans (same.trans (hv v (Nat.le_refl _)))

end NetworkStability.AutonomousFeedback.Schedule
