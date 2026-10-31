import KernelR.HybridAuxEvents

/-! Uniform budgets for actual physical jumps. Arbitrary subdivision of a flow
does not create a physical event and is deliberately not counted here. -/
namespace KernelR.Hybrid

def mainRank : MainMode → ℕ
  | .ready => 0 | .fast => 2 | .slow => 1

def Jump.mainCount {n route s u} (j : @Jump n route s u) (i : Fin n) : ℕ :=
  match j with
  | .fire _ k _ _ | .fastEnd _ k _ _ | .reopen _ k _ _ => if k = i then 1 else 0
  | _ => 0

def Jump.arrivalCount {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port) : ℕ :=
  match j with
  | .arrive _ d _ _ _ _ _ => if d.cell = i ∧ d.port = p then 1 else 0
  | _ => 0

def Jump.rawEndCount {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port) : ℕ :=
  match j with
  | .rawEnd _ k q _ _ _ => if k = i ∧ q = p then 1 else 0
  | _ => 0

def Move.mainCount {n θ route s u} : @Move n θ route s u → Fin n → ℕ
  | .flow _ => fun _ => 0
  | .jump j => j.mainCount

def Move.arrivalCount {n θ route s u} : @Move n θ route s u → Fin n → Port → ℕ
  | .flow _ => fun _ _ => 0
  | .jump j => j.arrivalCount

def Move.rawEndCount {n θ route s u} : @Move n θ route s u → Fin n → Port → ℕ
  | .flow _ => fun _ _ => 0
  | .jump j => j.rawEndCount

def Move.jumpCount {n θ route s u} : @Move n θ route s u → ℕ
  | .flow _ => 0
  | .jump _ => 1

def Execution.mainCount {n θ route s u} : @Execution n θ route s u → Fin n → ℕ
  | .nil _ => fun _ => 0
  | .cons step rest => fun i => step.mainCount i + rest.mainCount i

def Execution.arrivalCount {n θ route s u} : @Execution n θ route s u → Fin n → Port → ℕ
  | .nil _ => fun _ _ => 0
  | .cons step rest => fun i p => step.arrivalCount i p + rest.arrivalCount i p

def Execution.rawEndCount {n θ route s u} : @Execution n θ route s u → Fin n → Port → ℕ
  | .nil _ => fun _ _ => 0
  | .cons step rest => fun i p => step.rawEndCount i p + rest.rawEndCount i p

def Execution.jumpCount {n θ route s u} : @Execution n θ route s u → ℕ
  | .nil _ => 0
  | .cons step rest => step.jumpCount + rest.jumpCount

theorem Jump.main_rank_balance {n} {θ : Fin n → Parameters} {route s u}
    (j : @Jump n route s u) (i : Fin n) :
    j.mainCount i + mainRank (u.main i) =
      3 * (Move.jump (θ := θ) j).fireCount i + mainRank (s.main i) := by
  cases j with
  | fire k mode guard | fastEnd k mode guard | reopen k mode guard =>
    by_cases hk : i = k
    · subst i
      simp [Jump.mainCount, Move.fireCount, Move.ledger, Jump.ledger, Ledger.zero,
        setMain, mode, mainRank]
    · simp [Jump.mainCount, Move.fireCount, Move.ledger, Jump.ledger, Ledger.zero,
        setMain, hk, Ne.symm hk]
  | _ => simp [Jump.mainCount, Move.fireCount, Move.ledger, Jump.ledger, Ledger.zero,
      setAux, setRaw]

theorem Move.main_rank_balance {n θ route s u} (m : @Move n θ route s u) (i : Fin n) :
    m.mainCount i + mainRank (u.main i) = 3 * m.fireCount i + mainRank (s.main i) := by
  cases m with
  | flow f => simp [Move.mainCount, Move.fireCount, Move.ledger, Flow.ledger, f.main_fixed]
  | jump j => exact j.main_rank_balance i

theorem Execution.main_rank_balance {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) :
    e.mainCount i + mainRank (u.main i) = 3 * (e.signal i).count + mainRank (s.main i) := by
  induction e with
  | nil => simp [mainCount, signal, emissionTimes, ledger, Ledger.zero]
  | cons step rest ih =>
    have h := step.main_rank_balance i
    rw [signal_count_cons]
    simp only [mainCount]
    omega

theorem Execution.main_count_bound {n θ ε route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) :
    (e.mainCount i : ℝ) ≤ 3 * u.time + 3 := by
  have h := e.main_rank_balance i
  have hr : mainRank (s.main i) = 0 := by simp [mainRank, (hs.2.2 i).1]
  have hc : e.mainCount i ≤ 3 * (e.signal i).count := by omega
  have hcast := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcast
  linarith [e.fire_count_bound hs hb i]

def rawActive {n} (s : Snapshot n) (i : Fin n) (p : Port) : ℕ :=
  match s.raw i p with | none => 0 | some _ => 1

/-- Raw ends consume an actual active current; arrivals create one. -/
theorem Jump.raw_balance {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port) :
    j.rawEndCount i p + rawActive u i p = j.arrivalCount i p + rawActive s i p := by
  cases j with
  | arrive d before after queue due free =>
    by_cases hi : i = d.cell <;> by_cases hp : p = d.port
    all_goals first
      | (subst i; subst p; simp [Jump.rawEndCount, Jump.arrivalCount, rawActive, setRaw, free])
      | simp [Jump.rawEndCount, Jump.arrivalCount, rawActive, setRaw, hi, hp, eq_comm]
  | rawEnd k q origin active due =>
    by_cases hi : i = k <;> by_cases hp : p = q
    all_goals first
      | (subst i; subst p; simp [Jump.rawEndCount, Jump.arrivalCount, rawActive, setRaw, active])
      | simp [Jump.rawEndCount, Jump.arrivalCount, rawActive, setRaw, hi, hp, eq_comm]
  | _ => simp [Jump.rawEndCount, Jump.arrivalCount, rawActive, setMain, setAux]

theorem Move.raw_balance {n θ route s u} (m : @Move n θ route s u) (i : Fin n) (p : Port) :
    m.rawEndCount i p + rawActive u i p = m.arrivalCount i p + rawActive s i p := by
  cases m with
  | flow f => simp [Move.rawEndCount, Move.arrivalCount, rawActive, f.raw_fixed]
  | jump j => exact j.raw_balance i p

theorem Execution.raw_balance {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) :
    e.rawEndCount i p + rawActive u i p = e.arrivalCount i p + rawActive s i p := by
  induction e with
  | nil => simp [rawEndCount, arrivalCount]
  | cons step rest ih =>
    have h := step.raw_balance i p
    simp only [rawEndCount, arrivalCount]
    omega

theorem Move.arrival_count_sum {n θ route s u} (m : @Move n θ route s u) :
    (∑ i, ∑ p, m.arrivalCount i p) = m.ledger.delivered := by
  cases m with
  | flow f => simp [Move.arrivalCount, Move.ledger, Flow.ledger]
  | jump j => cases j <;> simp [Move.arrivalCount, Jump.arrivalCount, Move.ledger,
      Jump.ledger, Ledger.zero, ite_and, eq_comm]

theorem Execution.arrival_count_sum {n θ route s u} (e : @Execution n θ route s u) :
    (∑ i, ∑ p, e.arrivalCount i p) = e.ledger.delivered := by
  induction e with
  | nil => simp [arrivalCount, ledger, Ledger.zero]
  | cons step rest ih =>
    simp only [arrivalCount, Finset.sum_add_distrib, ledger, Ledger.add]
    rw [step.arrival_count_sum, ih]

theorem Execution.raw_end_count_bound {n θ route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) : (∑ i, ∑ p, e.rawEndCount i p) ≤ e.ledger.delivered := by
  rw [← e.arrival_count_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro p _
  have h := e.raw_balance i p
  have hz : rawActive s i p = 0 := by simp [rawActive, hs.2.1 i p]
  omega

/-- Every permitted physical jump occurs exactly once in this partition. -/
theorem Move.jump_count_partition {n θ route s u} (m : @Move n θ route s u) :
    m.jumpCount = (∑ i, m.mainCount i) + (∑ i, ∑ p, m.auxCount i p) +
      m.ledger.delivered + ∑ i, ∑ p, m.rawEndCount i p := by
  cases m with
  | flow f => simp [Move.jumpCount, Move.mainCount, Move.auxCount, Move.rawEndCount,
      Move.ledger, Flow.ledger]
  | jump j => cases j <;> simp [Move.jumpCount, Move.mainCount, Move.auxCount, Move.rawEndCount,
      Jump.mainCount, Jump.auxCount, Jump.rawEndCount, Move.ledger, Jump.ledger, Ledger.zero,
      ite_and]

theorem Execution.jump_count_partition {n θ route s u} (e : @Execution n θ route s u) :
    e.jumpCount = (∑ i, e.mainCount i) + (∑ i, ∑ p, e.auxCount i p) +
      e.ledger.delivered + ∑ i, ∑ p, e.rawEndCount i p := by
  induction e with
  | nil => simp [jumpCount, mainCount, auxCount, rawEndCount, ledger, Ledger.zero]
  | cons step rest ih =>
    simp only [jumpCount, mainCount, auxCount, rawEndCount, ledger, Ledger.add,
      Finset.sum_add_distrib]
    rw [step.jump_count_partition, ih]
    omega

def FanoutBound {n} (route : Router n) (F : ℕ) : Prop :=
  ∀ i t, (route i t).length ≤ F

theorem Move.issued_bound {n θ route s u F} (m : @Move n θ route s u)
    (hr : FanoutBound route F) : m.ledger.issued ≤ F * m.ledger.emissions.length := by
  cases m with
  | flow f => simp [Move.ledger, Flow.ledger]
  | jump j =>
    cases j <;> simp [Move.ledger, Jump.ledger, Ledger.zero]
    exact hr _ _

theorem Execution.issued_bound {n θ route s u F} (e : @Execution n θ route s u)
    (hr : FanoutBound route F) : e.ledger.issued ≤ F * e.ledger.emissions.length := by
  induction e with
  | nil => simp [ledger, Ledger.zero]
  | cons step rest ih =>
    simpa [ledger, Ledger.add, List.length_append, Nat.mul_add]
      using Nat.add_le_add (step.issued_bound hr) ih

theorem emission_length_eq_sum {n} (events : List (Fin n × ℝ)) :
    events.length = ∑ i, (events.filter (fun ev => ev.1 = i)).length := by
  induction events with
  | nil => simp
  | cons event rest ih =>
    have h (i : Fin n) : ((event :: rest).filter (fun ev => ev.1 = i)).length =
        (if event.1 = i then 1 else 0) + (rest.filter (fun ev => ev.1 = i)).length := by
      by_cases hi : event.1 = i <;> simp [hi, Nat.add_comm]
    simp_rw [h]
    rw [Finset.sum_add_distrib, ← ih]
    simp [eq_comm, Nat.add_comm]

theorem Execution.total_fire_count_bound {n θ ε route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) :
    (e.ledger.emissions.length : ℝ) ≤ (n : ℝ) * (u.time + 1) := by
  rw [emission_length_eq_sum]
  push_cast
  calc
    _ = ∑ i, ((e.signal i).count : ℝ) := by simp [signal, emissionTimes]
    _ ≤ ∑ _i : Fin n, (u.time + 1) := Finset.sum_le_sum (fun i _ => e.fire_count_bound hs hb i)
    _ = _ := by simp [mul_add]

/-- Uniform finite-prefix budget for all nine jump constructors. The source
queue is counted explicitly and each routed fanout is bounded by F. This is an
event-count result, not a construction of a continuation or a complete run. -/
theorem Execution.jump_count_bound {n θ ε route s u F} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (hr : FanoutBound route F) :
    (e.jumpCount : ℝ) ≤ (n : ℝ) * (27 * u.time + 33) +
      2 * ((s.pending.length : ℝ) + (F : ℝ) * (n : ℝ) * (u.time + 1)) := by
  have hm : (∑ i, (e.mainCount i : ℝ)) ≤ (n : ℝ) * (3 * u.time + 3) := by
    calc
      _ ≤ ∑ _i : Fin n, (3 * u.time + 3) :=
        Finset.sum_le_sum (fun i _ => e.main_count_bound hs hb i)
      _ = _ := by simp [mul_add]
  have ha : (∑ i, ∑ p, (e.auxCount i p : ℝ)) ≤ (n : ℝ) * (3 * (8 * u.time + 10)) := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _p : Port, (8 * u.time + 10) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun p _ => e.aux_count_bound hs hb i p))
      _ = _ := by simp [Port, mul_add]
  have hend := (Nat.cast_le (α := ℝ)).mpr (e.raw_end_count_bound hs)
  push_cast at hend
  have hqueue : e.ledger.delivered ≤ s.pending.length + e.ledger.issued := by
    have h := e.queue_balance
    omega
  have hqueueR := (Nat.cast_le (α := ℝ)).mpr hqueue
  have hissueR := (Nat.cast_le (α := ℝ)).mpr (e.issued_bound hr)
  push_cast at hqueueR hissueR
  have htotal := mul_le_mul_of_nonneg_left (e.total_fire_count_bound hs hb)
    (Nat.cast_nonneg F : (0 : ℝ) ≤ F)
  have hdel : (e.ledger.delivered : ℝ) ≤ (s.pending.length : ℝ) +
      (F : ℝ) * (n : ℝ) * (u.time + 1) := by nlinarith
  rw [e.jump_count_partition]
  push_cast
  nlinarith

/-- The same bound applies to every finite prefix ending by the same horizon,
so the number of physical events cannot grow unboundedly at bounded times. -/
theorem Execution.jump_count_through {n θ ε route s u F} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (hr : FanoutBound route F)
    (T : ℝ) (ht : u.time ≤ T) :
    (e.jumpCount : ℝ) ≤ (n : ℝ) * (27 * T + 33) +
      2 * ((s.pending.length : ℝ) + (F : ℝ) * (n : ℝ) * (T + 1)) := by
  apply (e.jump_count_bound hs hb hr).trans
  gcongr

/-- One natural budget bounds every finite admissible prefix from the same
birth state at a bounded horizon. No execution-existence premise is hidden in
this statement, and arbitrary flow subdivisions are not physical events. -/
theorem finite_prefix_event_budget {n θ ε route s F} (hs : @BirthState n s)
    (hb : PhysicalBox θ ε) (hr : FanoutBound route F) (T : ℝ) :
    ∃ B : ℕ, ∀ (u : Snapshot n) (e : Execution θ route s u), u.time ≤ T → e.jumpCount ≤ B := by
  obtain ⟨B, hB⟩ := exists_nat_ge ((n : ℝ) * (27 * T + 33) +
    2 * ((s.pending.length : ℝ) + (F : ℝ) * (n : ℝ) * (T + 1)))
  exact ⟨B, fun _ e ht => (Nat.cast_le (α := ℝ)).mp ((e.jump_count_through hs hb hr T ht).trans hB)⟩

end KernelR.Hybrid
