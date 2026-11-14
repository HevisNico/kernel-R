import AutonomousFeedback

namespace NetworkStability.AutonomousFeedback

open SelfCertifyingLearning

/-- The local part of the feedback certificate. FIRE and silence spend the
reserve in mutually exclusive ways. No scalar potential is required. -/
structure LocalReserve (Q : Nat) {N : Nat} {P : Type} (M : Model N P) (seed : List P) where
  reserve : Fin N → P → Nat
  route : ∀ p i, mass (reserve i) (M.route p) ≤ reserve i p
  write : ∀ p, 1 ≤ reserve (M.cell p) p
  initial : ∀ i, mass (reserve i) seed ≤ Q

def writeTotal (s : State N P) : Nat := RoutedCalendar.total ⟨s.writes, []⟩

def stored (d : Nat) (base : Fin N → Nat) (s : State N P) (i : Fin N) : Nat :=
  base i + d * s.writes i

theorem step_writes_mono (M : Model N P) (d : Nat) (e : Int) (s : State N P) (i : Fin N) :
    s.writes i ≤ (step M d e s).writes i := by
  cases queue : s.pending with
  | nil => simp [step, queue]
  | cons p tail => simp [step, queue]

theorem run_writes_mono (M : Model N P) (d : Nat) (error : Nat → Int)
    (n : Nat) (s : State N P) (i : Fin N) :
    s.writes i ≤ (run M d error n s).writes i := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.le_trans (step_writes_mono M d _ s i) (ih _)

theorem run_add (M : Model N P) (d : Nat) (error : Nat → Int)
    (n m : Nat) (s : State N P) :
    run M d error (n + m) s = run M d error m (run M d error n s) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => rw [Nat.succ_add, run, run, ih]

theorem reserve_prefix (Q d B rail : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : LocalReserve Q M seed)
    (base : Fin N → Nat) (hbase : ∀ i, base i ≤ B) (railRoom : B + d * Q < rail)
    (error : Nat → Int) (n : Nat) :
    let s := run M d error n (start N seed)
    writeTotal s ≤ Q * N ∧ ∀ i, s.writes i ≤ Q ∧ base i ≤ stored d base s i ∧
      stored d base s i ≤ B + d * Q ∧ stored d base s i < rail := by
  dsimp only
  have counts (i : Fin N) : (run M d error n (start N seed)).writes i ≤ Q := by
    have bound := local_run M d cert.reserve cert.route cert.write error n (start N seed) i
    change _ ≤ 0 + mass (cert.reserve i) seed at bound
    rw [Nat.zero_add] at bound
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans bound (cert.initial i))
  refine ⟨RoutedCalendar.total_le Q _ counts, fun i => ⟨counts i, ?_, ?_, ?_⟩⟩
  · unfold stored
    omega
  · exact Nat.add_le_add (hbase i) (Nat.mul_le_mul_left d (counts i))
  · have dose := Nat.mul_le_mul_left d (counts i)
    have initial := hbase i
    unfold stored
    omega

private theorem weighted_count_order {I : Type} (xs : List I) (a b : I → Nat)
    (mono : ∀ i ∈ xs, a i ≤ b i) :
    weighted (fun _ => 1) a xs ≤ weighted (fun _ => 1) b xs ∧
      (weighted (fun _ => 1) a xs = weighted (fun _ => 1) b xs →
        ∀ i ∈ xs, a i = b i) := by
  induction xs with
  | nil => simp [weighted]
  | cons j tail ih =>
    have head := mono j (by simp)
    obtain ⟨rest, eqRest⟩ := ih (fun i hi => mono i (by simp [hi]))
    simp only [weighted, Nat.one_mul]
    refine ⟨Nat.add_le_add head rest, fun same i mem => ?_⟩
    rcases List.mem_cons.mp mem with eq | inTail
    · subst i
      omega
    · exact eqRest (by omega) i inTail

private theorem attains_maximum (f : Nat → Nat) (bound : Nat) (bounded : ∀ k, f k ≤ bound) :
    ∃ t, ∀ k, f k ≤ f t := by
  induction bound with
  | zero => exact ⟨0, fun k => Nat.le_trans (bounded k) (Nat.zero_le _)⟩
  | succ bound ih =>
    classical
    by_cases hit : ∃ t, f t = bound + 1
    · obtain ⟨t, ht⟩ := hit
      exact ⟨t, fun k => by rw [ht]; exact bounded k⟩
    · apply ih
      intro k
      have below := bounded k
      have different : f k ≠ bound + 1 := fun eq => hit ⟨k, eq⟩
      omega

/-- For each error trace, one finite cut freezes all cells simultaneously.
The cut need not be bounded in terms of the write budget. -/
theorem memory_stabilizes (Q d B rail : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : LocalReserve Q M seed)
    (base : Fin N → Nat) (hbase : ∀ i, base i ≤ B) (railRoom : B + d * Q < rail)
    (error : Nat → Int) :
    ∃ t, ∀ k,
      let atCut := run M d error t (start N seed)
      let later := run M d error (t + k) (start N seed)
      later.writes = atCut.writes ∧ stored d base later = stored d base atCut := by
  let history := fun k => run M d error k (start N seed)
  obtain ⟨t, max⟩ := attains_maximum (fun k => writeTotal (history k)) (Q * N)
    (fun k => (reserve_prefix Q d B rail M seed cert base hbase railRoom error k).1)
  refine ⟨t, fun k => ?_⟩
  have growing (i : Fin N) : (history t).writes i ≤ (history (t + k)).writes i := by
    dsimp [history]
    rw [run_add]
    exact run_writes_mono M d error k _ i
  have ordered := weighted_count_order (List.finRange N) (history t).writes (history (t + k)).writes
    (fun i _ => growing i)
  have same := Nat.le_antisymm ordered.1 (max (t + k))
  have counts : (history (t + k)).writes = (history t).writes :=
    funext fun i => (ordered.2 same i (List.mem_finRange i)).symm
  exact ⟨counts, by unfold stored; rw [counts]⟩

/-- Every declared FIRE descendant has a strictly smaller probe-type rank
under milestone 5's certificate, even when the cell graph has cycles. -/
theorem strict_probe_rank (Q W eta : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (cert : Certificate Q W eta M seed)
    (p q : P) (child : q ∈ M.route p) : cert.weight q < cert.weight p := by
  have leMass (queue : List P) (mem : q ∈ queue) : cert.weight q ≤ mass cert.weight queue := by
    induction queue with
    | nil => simp at mem
    | cons a tail ih =>
      rcases List.mem_cons.mp mem with eq | ht
      · subst a
        simp [mass]
      · have := ih ht
        change cert.weight q ≤ cert.weight a + mass cert.weight tail
        omega
  have := cert.scalar p
  have := leMass _ child
  have := cert.eta_pos
  omega

end NetworkStability.AutonomousFeedback
