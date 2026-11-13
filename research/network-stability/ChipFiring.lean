import SelfCertifyingLearning.Composition

namespace NetworkStability.ChipFiring

open SelfCertifyingLearning

/-- The index list contains each cell once. The threshold and work bound
are external scalars, common to every network size. -/
structure Model (N : Nat) where
  spill : Fin N → Fin N → Nat
  initial : Fin N → Nat

structure State (N : Nat) where
  work : Fin N → Nat
  writes : Fin N → Nat

def tally {N : Nat} (x : Fin N → Nat) : Nat :=
  weighted (fun _ => 1) x (List.finRange N)

def start (M : Model N) : State N := ⟨M.initial, fun _ => 0⟩

def fire (M : Model N) (d : Nat) (s : State N) (i : Fin N) : State N :=
  ⟨fun j => s.work j - (if j = i then d else 0) + M.spill j i,
   fun j => s.writes j + (if j = i then 1 else 0)⟩

/-- Enabling is monotone in incoming work. -/
def Terminal (d : Nat) (s : State N) : Prop := ∀ i, s.work i < d

inductive Reach (M : Model N) (d : Nat) : Nat → State N → Prop where
  | start : Reach M d 0 (start M)
  | fire {n s} (pre : Reach M d n s) (i) (enabled : d ≤ s.work i) :
      Reach M d (n + 1) (fire M d s i)

private theorem weighted_zero {I : Type} (xs : List I) (w : I → Nat) :
    weighted w (fun _ => 0) xs = 0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [weighted, ih]

private theorem weighted_le {I : Type} (xs : List I) (w a b : I → Nat)
    (h : ∀ i ∈ xs, a i ≤ b i) : weighted w a xs ≤ weighted w b xs := by
  have zero := weighted_zero xs w
  simpa only [zero, Nat.add_zero] using
    (weighted_balance xs w b a (fun _ => 0) (fun _ => 0) (by simpa using h))

private theorem weighted_constant {I : Type} (xs : List I) (w : I → Nat) (q : Nat) :
    weighted w (fun _ => q) xs = weighted (fun _ => 1) w xs * q := by
  induction xs with
  | nil => simp [weighted]
  | cons i xs ih => simp [weighted, ih, Nat.add_mul]

private theorem weighted_bump {I : Type} [DecidableEq I] (xs : List I)
    (w x : I → Nat) (i : I) (nodup : xs.Nodup) :
    weighted w (fun j => x j + if j = i then 1 else 0) xs =
      weighted w x xs + if i ∈ xs then w i else 0 := by
  induction xs with
  | nil => simp [weighted]
  | cons j xs ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp nodup
    by_cases eq : j = i
    · subst j
      simp [weighted, ih tail, absent, Nat.mul_add, Nat.add_assoc, Nat.add_comm]
    · simp [weighted, ih tail, eq, Ne.symm eq, Nat.add_assoc]

private theorem weighted_impulse {I : Type} [DecidableEq I] (xs : List I)
    (w : I → Nat) (i : I) (d : Nat) (nodup : xs.Nodup) :
    weighted w (fun j => if j = i then d else 0) xs =
      if i ∈ xs then w i * d else 0 := by
  induction xs with
  | nil => simp [weighted]
  | cons j xs ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp nodup
    by_cases eq : j = i
    · subst j
      simp [weighted, ih tail, absent]
    · simp [weighted, ih tail, eq, Ne.symm eq]

theorem balance {M : Model N} {d n s} (r : Reach M d n s) (j : Fin N) :
    s.work j + d * s.writes j = M.initial j + weighted (M.spill j) s.writes (List.finRange N) := by
  induction r with
  | start => simp [start, weighted_zero]
  | @fire n s pre i enabled ih =>
    have bump := weighted_bump (List.finRange N) (M.spill j) s.writes i (List.nodup_finRange N)
    simp only [List.mem_finRange, ite_true] at bump
    change s.work j - (if j = i then d else 0) + M.spill j i +
        d * (s.writes j + (if j = i then 1 else 0)) =
      M.initial j + weighted (M.spill j) (fun k => s.writes k + if k = i then 1 else 0) (List.finRange N)
    rw [bump]
    by_cases eq : j = i
    · subst j
      simp only [ite_true, Nat.mul_add, Nat.mul_one]
      have := Nat.sub_add_cancel enabled
      omega
    · simp only [eq, ite_false, Nat.sub_zero, Nat.add_zero]
      omega

theorem count_eq {M : Model N} {d n s} (r : Reach M d n s) : tally s.writes = n := by
  induction r with
  | start => exact weighted_zero _ _
  | @fire n s pre i enabled ih =>
    unfold tally at *
    change weighted (fun _ => 1) (fun j => s.writes j + if j = i then 1 else 0) _ = _
    rw [weighted_bump _ _ _ _ (List.nodup_finRange N)]
    simpa only [List.mem_finRange, ite_true] using congrArg (· + 1) ih

theorem decrease {M : Model N} {d eta : Nat} (w : Fin N → Nat)
    (margin : ∀ i, eta + weighted w (fun j => M.spill j i) (List.finRange N) ≤ w i * d)
    (s : State N) (i : Fin N) (enabled : d ≤ s.work i) :
    weighted w (fire M d s i).work (List.finRange N) + eta ≤
      weighted w s.work (List.finRange N) := by
  have retirement :
      weighted w (fun j => if j = i then d else 0) (List.finRange N) = w i * d := by
    simpa only [List.mem_finRange, ite_true] using
      weighted_impulse (List.finRange N) w i d (List.nodup_finRange N)
  exact coupled_decrease _ _ _ _ _ _ _ (by
    intro j _
    change s.work j - (if j = i then d else 0) + M.spill j i +
      (if j = i then d else 0) ≤ s.work j + M.spill j i
    by_cases h : j = i
    · subst j
      simp only [ite_true]
      omega
    · simp [h]) (by simpa [retirement] using margin i)

private theorem sum_ones (N : Nat) :
    weighted (fun _ => 1) (fun _ => 1) (List.finRange N) = N := by
  have aux {I : Type} (xs : List I) : weighted (fun _ => 1) (fun _ => 1) xs = xs.length := by
    induction xs with
    | nil => rfl
    | cons _ _ ih => simp [weighted, ih, Nat.add_comm]
  simp [aux]

/-- A column certificate gives a write bound with uniform Q, W and eta0. -/
theorem weighted_budget (Q d W eta0 : Nat) {N : Nat} {M : Model N}
    {n : Nat} {s : State N} (w : Fin N → Nat)
    (hW : ∀ i, 1 ≤ w i ∧ w i ≤ W)
    (initial : ∀ i, M.initial i ≤ Q)
    (margin : ∀ i, eta0 + weighted w (fun j => M.spill j i) (List.finRange N) ≤ w i * d)
    (r : Reach M d n s) :
    weighted w s.work (List.finRange N) + eta0 * n ≤ W * Q * N := by
  induction r with
  | start =>
    simp only [Nat.mul_zero, Nat.add_zero, start]
    calc
      weighted w M.initial (List.finRange N) ≤ weighted w (fun _ => Q) (List.finRange N) :=
        weighted_le _ _ _ _ (fun i _ => initial i)
      _ = tally w * Q := weighted_constant _ _ _
      _ ≤ (N * W) * Q := by
        apply Nat.mul_le_mul_right
        calc
          tally w ≤ weighted (fun _ => 1) (fun _ => W) (List.finRange N) :=
            weighted_le _ _ _ _ (fun i _ => (hW i).2)
          _ = N * W := by rw [weighted_constant, sum_ones]
      _ = W * Q * N := by simp [Nat.mul_comm, Nat.mul_left_comm]
  | @fire n s pre i enabled ih =>
    have step := decrease w margin s i enabled
    rw [Nat.mul_succ]
    omega

private theorem supply_bound {M : Model N} {d Q : Nat} {s : State N}
    (hd : 0 < d) (rows : ∀ i, tally (M.spill i) < d)
    (initial : ∀ i, M.initial i ≤ Q) (counts : ∀ i, s.writes i ≤ Q) (i : Fin N) :
    M.initial i + weighted (M.spill i) s.writes (List.finRange N) ≤ d * Q := by
  have hw := weighted_le (List.finRange N) (M.spill i) s.writes (fun _ => Q) (fun j _ => counts j)
  rw [weighted_constant] at hw
  change _ ≤ tally (M.spill i) * Q at hw
  have hm := Nat.mul_le_mul_right Q (show tally (M.spill i) ≤ d - 1 by
    have := rows i
    omega)
  have he : (d - 1) * Q + Q = d * Q := by
    calc
      (d - 1) * Q + Q = (d - 1) * Q + 1 * Q := by rw [Nat.one_mul]
      _ = d * Q := by rw [← Nat.add_mul, Nat.sub_add_cancel hd]
  have := initial i
  omega

private theorem write_bound {M : Model N} {d Q n : Nat} {s : State N} (r : Reach M d n s)
    (hd : 0 < d) (rows : ∀ i, tally (M.spill i) < d)
    (initial : ∀ i, M.initial i ≤ Q) : ∀ i, s.writes i ≤ Q := by
  induction r with
  | start => intro i; exact Nat.zero_le _
  | @fire n s pre i enabled ih =>
    intro j
    by_cases eq : j = i
    · subst j
      have hbal := balance pre i
      have hs := supply_bound hd rows initial ih i
      have hb : d * (s.writes i + 1) ≤ d * Q := by rw [Nat.mul_succ]; omega
      simpa [fire] using Nat.le_of_mul_le_mul_left hb hd
    · simpa [fire, eq] using ih j

/-- The least-action comparison bounds any legal prefix by any reachable
terminal write vector. It uses nonnegative spill and monotone enabling. -/
theorem least_action {M : Model N} {d n m : Nat} {s t : State N}
    (r : Reach M d n s) (target : Reach M d m t) (done : Terminal d t) :
    ∀ i, s.writes i ≤ t.writes i := by
  induction r with
  | start => intro i; exact Nat.zero_le _
  | @fire n s pre i enabled ih =>
    intro j
    by_cases eq : j = i
    · subst j
      have strict : s.writes i < t.writes i := by
        apply Nat.lt_of_le_of_ne (ih i)
        intro same
        have h₁ := balance pre i
        have h₂ := balance target i
        have mono := weighted_le (List.finRange N) (M.spill i) s.writes t.writes (fun j _ => ih j)
        have := done i
        rw [same] at h₁
        omega
      simpa [fire] using Nat.succ_le_of_lt strict
    · simpa [fire, eq] using ih j

theorem terminal_unique {M : Model N} {d n m : Nat} {s t : State N}
    (rs : Reach M d n s) (rt : Reach M d m t) (hs : Terminal d s) (ht : Terminal d t) :
    s = t := by
  have eq : s.writes = t.writes := funext fun i =>
    Nat.le_antisymm (least_action rs rt ht i) (least_action rt rs hs i)
  have work : s.work = t.work := funext fun i => by
    have h₁ := balance rs i
    have h₂ := balance rt i
    rw [eq] at h₁
    omega
  cases s
  cases t
  simp_all

def next (d : Nat) (s : State N) : Option (Fin N) :=
  (List.finRange N).find? (fun i => decide (d ≤ s.work i))

def compute (M : Model N) (d : Nat) : Nat → State N → State N
  | 0, s => s
  | fuel + 1, s =>
    match next d s with
    | none => s
    | some i => compute M d fuel (fire M d s i)

private theorem next_none {d : Nat} {s : State N} (h : next d s = none) : Terminal d s := by
  intro i
  have hs := List.find?_eq_none.mp h i (List.mem_finRange i)
  simpa using hs

private theorem compute_spec {M : Model N} {d n : Nat} {s : State N}
    (fuel : Nat) (r : Reach M d n s) :
    (∃ m, Reach M d m (compute M d fuel s) ∧ Terminal d (compute M d fuel s)) ∨
      Reach M d (n + fuel) (compute M d fuel s) := by
  induction fuel generalizing n s with
  | zero => exact Or.inr r
  | succ fuel ih =>
    cases h : next d s with
    | none => exact Or.inl ⟨n, by simpa [compute, h], by simpa [compute, h] using next_none h⟩
    | some i =>
      have enabled : d ≤ s.work i := of_decide_eq_true (List.find?_some (p := fun j => decide (d ≤ s.work j)) h)
      rcases ih (r.fire i enabled) with ⟨m, hm, ht⟩ | hfull
      · exact Or.inl ⟨m, by simpa [compute, h] using hm, by simpa [compute, h] using ht⟩
      · refine Or.inr ?_
        rw [compute, h, show n + (fuel + 1) = n + 1 + fuel by omega]
        exact hfull

/-- Q and d are fixed before quantifying over N. Unit weights and unit
decrease give the Q*N bound. Every finite terminal schedule has the same
outcome; the prefix bound excludes an infinite legal write schedule. -/
theorem stabilize (Q d : Nat) {N : Nat} (M : Model N)
    (hd : 0 < d)
    (rows : ∀ i, tally (M.spill i) < d)
    (columns : ∀ i, tally (fun j => M.spill j i) < d)
    (initial : ∀ i, M.initial i ≤ Q) :
    (∀ n s, Reach M d n s →
      n ≤ Q * N ∧ ∀ i, s.writes i ≤ Q ∧ s.work i ≤ d * Q) ∧
    (∃ n, Reach M d n (compute M d (Q * N) (start M)) ∧
      Terminal d (compute M d (Q * N) (start M)) ∧
      ∀ m t, Reach M d m t → Terminal d t → t = compute M d (Q * N) (start M)) := by
  have budget {n s} (r : Reach M d n s) :=
    weighted_budget Q d 1 1 (fun _ => 1) (fun _ => by simp)
      initial (fun i => by
        change 1 + tally (fun j => M.spill j i) ≤ 1 * d
        simpa [Nat.add_comm] using Nat.succ_le_of_lt (columns i)) r
  constructor
  · intro n s r
    have hb := budget r
    simp only [Nat.one_mul] at hb
    have counts := write_bound r hd rows initial
    refine ⟨by omega, fun i => ⟨counts i, ?_⟩⟩
    have hbal := balance r i
    have hs := supply_bound hd rows initial counts i
    omega
  · let t := compute M d (Q * N) (start M)
    have existence : ∃ n, Reach M d n t ∧ Terminal d t := by
      rcases compute_spec (Q * N) (Reach.start (M := M) (d := d)) with done | full
      · exact done
      · refine ⟨_, full, ?_⟩
        intro i
        apply Nat.lt_of_not_ge
        intro enabled
        have over := budget (full.fire i enabled)
        simp only [Nat.one_mul, Nat.zero_add] at over
        omega
    obtain ⟨n, hn, ht⟩ := existence
    exact ⟨n, hn, ht, fun _ _ r done => terminal_unique r hn done ht⟩

/-- Stored memory in dose units, with B and Q independent of network size. -/
theorem memory_bound (B Q d : Nat) {N : Nat} {M : Model N}
    (hd : 0 < d) (rows : ∀ i, tally (M.spill i) < d)
    (initial : ∀ i, M.initial i ≤ Q)
    (base : Fin N → Nat) (hbase : ∀ i, base i ≤ B)
    {n : Nat} {s : State N} (r : Reach M d n s) (i : Fin N) :
    base i ≤ base i + s.writes i ∧ base i + s.writes i ≤ B + Q := by
  have hw := write_bound r hd rows initial i
  have hb := hbase i
  omega

end NetworkStability.ChipFiring
