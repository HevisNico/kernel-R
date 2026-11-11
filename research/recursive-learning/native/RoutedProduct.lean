import FamilyProduct

/-! Networks of cells joined by wires. Each cell has a one-cell execution
in which the pulses it will receive from other cells are already in its
queue. The executions are woven into one execution of the routed
network, in which a pulse exists only after the FIRE that sends it. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- The network state made of `n` one-cell states, with its own queue. -/
def Snapshot.familyWith {n : ℕ} (T : ℝ) (s : Fin n → Snapshot 1) (P : List (Delivery n)) :
    Snapshot n :=
  { Snapshot.family T s with pending := P }

theorem familyWith_update_eq {n : ℕ} {T : ℝ} {s : Fin n → Snapshot 1} {i : Fin n}
    {v : Snapshot 1} {w : Snapshot n} {P : List (Delivery n)} (time : w.time = T)
    (x : ∀ j c, w.x j c = (s j).x 0 c) (vx : v.x = (s i).x)
    (main : ∀ j, j ≠ i → w.main j = (s j).main 0) (mainI : w.main i = v.main 0)
    (aux : ∀ j, j ≠ i → ∀ p, w.aux j p = (s j).aux 0 p) (auxI : ∀ p, w.aux i p = v.aux 0 p)
    (raw : ∀ j, j ≠ i → ∀ p, w.raw j p = (s j).raw 0 p) (rawI : ∀ p, w.raw i p = v.raw 0 p)
    (pending : w.pending = P) : w = Snapshot.familyWith T (Function.update s i v) P := by
  cases w
  simp only [Snapshot.familyWith, Snapshot.family, Snapshot.mk.injEq]
  refine ⟨time, ?_, ?_, ?_, ?_, pending⟩
  · funext j c
    by_cases h : j = i
    · subst j; rw [Function.update_self, vx]; exact x i c
    · rw [Function.update_of_ne h]; exact x j c
  · funext j
    by_cases h : j = i
    · subst j; rw [Function.update_self]; exact mainI
    · rw [Function.update_of_ne h]; exact main j h
  · funext j p
    by_cases h : j = i
    · subst j; rw [Function.update_self]; exact auxI p
    · rw [Function.update_of_ne h]; exact aux j h p
  · funext j p
    by_cases h : j = i
    · subst j; rw [Function.update_self]; exact rawI p
    · rw [Function.update_of_ne h]; exact raw j h p

/-- The synchronized flows of the cells form a flow of the network, for
any queue with no delivery due before the end. -/
noncomputable def familyFlowWith {n : ℕ} {θ : Fin n → Fin 1 → Parameters} {T T' : ℝ}
    {s u : Fin n → Snapshot 1} (f : ∀ i, ParameterFlow (θ i) (s i) (u i)) (lt : T < T')
    (start : ∀ i, (s i).time = T) (finish : ∀ i, (u i).time = T') (P : List (Delivery n))
    (urgent : ∀ d ∈ P, T' ≤ d.due) :
    ParameterFlow (familyParameters θ) (Snapshot.familyWith T s P)
      (Snapshot.familyWith T' u P) where
  positive := lt
  path := (familyFlow f lt start finish).path
  initial := (familyFlow f lt start finish).initial
  final := (familyFlow f lt start finish).final
  main_fixed := (familyFlow f lt start finish).main_fixed
  aux_fixed := (familyFlow f lt start finish).aux_fixed
  raw_fixed := (familyFlow f lt start finish).raw_fixed
  queue_fixed := rfl
  continuous := (familyFlow f lt start finish).continuous
  integrable := (familyFlow f lt start finish).integrable
  mark_integrable := (familyFlow f lt start finish).mark_integrable
  integral_eq := (familyFlow f lt start finish).integral_eq
  guards := (familyFlow f lt start finish).guards
  raw_support := (familyFlow f lt start finish).raw_support
  pending_urgent := urgent

/-- A jump of one cell is a jump of the routed network. A FIRE adds the
deliveries of its wires to the queue. An arrival takes its delivery from
the queue, where it must be present. The last clause relates the queues
before and after as multisets. -/
theorem routed_jump {n : ℕ} {θ : Fin n → Fin 1 → Parameters} (route : Router n) {T : ℝ}
    {s : Fin n → Snapshot 1} (i : Fin n) {v : Snapshot 1}
    (j : ParameterJump (θ i) (fun _ _ => []) (s i) v) (hs : (s i).time = T)
    (P : List (Delivery n))
    (available : ∀ e ∈ (s i).pending, e.due = T → Delivery.inCell i e ∈ P) :
    ∃ (P' : List (Delivery n)) (k : ParameterJump (familyParameters θ) route
        (Snapshot.familyWith T s P) (Snapshot.familyWith T (Function.update s i v) P')),
      k.emissions = j.emissions.map (fun e => (i, e.2)) ∧
      ((familyQueue (Function.update s i v) : Multiset (Delivery n)) + (P : Multiset (Delivery n)) +
        ((j.emissions.flatMap (fun e => route i e.2) : List (Delivery n)) : Multiset (Delivery n)) =
        (familyQueue s : Multiset (Delivery n)) + (P' : Multiset (Delivery n))) := by
  generalize hsi : s i = a at j
  cases j with
  | fire i₀ mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.fire (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) i mode guard)
      (familyWith_update_eq (P := P ++ route i T) (v := { (setMain (s i) 0 .fast) with
          pending := (s i).pending ++ (fun (_ : Fin 1) (_ : ℝ) => ([] : List (Delivery 1))) 0 (s i).time })
        rfl (fun _ _ => rfl) rfl
        (fun j hj => by simp [setMain, Snapshot.familyWith, Snapshot.family, hj])
        (by simp [setMain, Snapshot.familyWith, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) rfl)
    refine ⟨P ++ route i T, k, hk.trans ?_, ?_⟩
    · show [(i, T)] = [(i, (s i).time)]
      rw [hs]
    · rw [familyQueue_keep s i _ (by simp)]
      show (familyQueue s : Multiset (Delivery n)) + (P : Multiset (Delivery n)) +
        ((route i (s i).time ++ [] : List (Delivery n)) : Multiset (Delivery n)) = _
      rw [hs, List.append_nil, ← Multiset.coe_add, add_assoc]
  | fastEnd i₀ mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.fastEnd (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) i mode guard)
      (familyWith_update_eq (P := P) (v := setMain (s i) 0 .slow) rfl (fun _ _ => rfl) rfl
        (fun j hj => by simp [setMain, Snapshot.familyWith, Snapshot.family, hj])
        (by simp [setMain, Snapshot.familyWith, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) rfl)
    exact ⟨P, k, hk, by rw [familyQueue_keep s i (setMain (s i) 0 .slow) rfl]; simp [ParameterJump.emissions]⟩
  | reopen i₀ mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.reopen (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) i mode guard)
      (familyWith_update_eq (P := P) (v := setMain (s i) 0 .ready) rfl (fun _ _ => rfl) rfl
        (fun j hj => by simp [setMain, Snapshot.familyWith, Snapshot.family, hj])
        (by simp [setMain, Snapshot.familyWith, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) rfl)
    exact ⟨P, k, hk, by rw [familyQueue_keep s i (setMain (s i) 0 .ready) rfl]; simp [ParameterJump.emissions]⟩
  | mark i₀ p mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.mark (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) i p mode guard)
      (familyWith_update_eq (P := P) (v := setAux (s i) 0 p .mark) rfl (fun _ _ => rfl) rfl
        (fun _ _ => rfl) rfl
        (fun j hj q => by simp [setAux, Snapshot.familyWith, Snapshot.family, hj])
        (fun q => by simp [setAux, Snapshot.familyWith, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) rfl)
    exact ⟨P, k, hk, by rw [familyQueue_keep s i (setAux (s i) 0 p .mark) rfl]; simp [ParameterJump.emissions]⟩
  | silent i₀ p mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.silent (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) i p mode guard)
      (familyWith_update_eq (P := P) (v := setAux (s i) 0 p .silent) rfl (fun _ _ => rfl) rfl
        (fun _ _ => rfl) rfl
        (fun j hj q => by simp [setAux, Snapshot.familyWith, Snapshot.family, hj])
        (fun q => by simp [setAux, Snapshot.familyWith, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) rfl)
    exact ⟨P, k, hk, by rw [familyQueue_keep s i (setAux (s i) 0 p .silent) rfl]; simp [ParameterJump.emissions]⟩
  | error i₀ p mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.error (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) i p mode guard)
      (familyWith_update_eq (P := P) (v := setAux (s i) 0 p .error) rfl (fun _ _ => rfl) rfl
        (fun _ _ => rfl) rfl
        (fun j hj q => by simp [setAux, Snapshot.familyWith, Snapshot.family, hj])
        (fun q => by simp [setAux, Snapshot.familyWith, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) rfl)
    exact ⟨P, k, hk, by rw [familyQueue_keep s i (setAux (s i) 0 p .error) rfl]; simp [ParameterJump.emissions]⟩
  | auxReady i₀ p mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.auxReady (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) i p mode guard)
      (familyWith_update_eq (P := P) (v := setAux (s i) 0 p .ready) rfl (fun _ _ => rfl) rfl
        (fun _ _ => rfl) rfl
        (fun j hj q => by simp [setAux, Snapshot.familyWith, Snapshot.family, hj])
        (fun q => by simp [setAux, Snapshot.familyWith, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) rfl)
    exact ⟨P, k, hk, by rw [familyQueue_keep s i (setAux (s i) 0 p .ready) rfl]; simp [ParameterJump.emissions]⟩
  | arrive d before after queue due free =>
    subst hsi
    have hc : d.cell = 0 := Subsingleton.elim _ _
    have present : Delivery.inCell i d ∈ P :=
      available d (by rw [queue]; simp) (due.trans hs)
    obtain ⟨B, A, split⟩ := List.append_of_mem present
    obtain ⟨L, R, parts⟩ := familyQueue_split s i
    have original := parts (s i)
    rw [Function.update_eq_self] at original
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.arrive (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) (Delivery.inCell i d) B A split (due.trans hs)
        (by
          show (s i).raw 0 d.port = none
          rw [← hc]
          exact free))
      (familyWith_update_eq (P := B ++ A) (v := { (setRaw (s i) d.cell d.port (some (s i).time)) with
          pending := before ++ after }) rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl
        (fun _ _ _ => rfl) (fun _ => rfl)
        (fun j hj q => by simp [setRaw, Snapshot.familyWith, Snapshot.family, Delivery.inCell, hj])
        (fun q => by simp [setRaw, Snapshot.familyWith, Snapshot.family, Delivery.inCell, hc, hs])
        rfl)
    refine ⟨B ++ A, k, hk, ?_⟩
    rw [parts, original, queue, split]
    simp only [ParameterJump.emissions, List.flatMap_nil, List.map_append, List.map_cons,
      Multiset.coe_nil, add_zero, ← Multiset.coe_add, ← Multiset.cons_coe,
      ← Multiset.singleton_add]
    abel
  | rawEnd i₀ p origin active due =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.rawEnd (θ := familyParameters θ) (route := route)
        (Snapshot.familyWith T s P) i p origin active (hs.symm.trans due))
      (familyWith_update_eq (P := P) (v := setRaw (s i) 0 p none) rfl (fun _ _ => rfl) rfl
        (fun _ _ => rfl) rfl (fun _ _ _ => rfl) (fun _ => rfl)
        (fun j hj q => by simp [setRaw, Snapshot.familyWith, Snapshot.family, hj])
        (fun q => by simp [setRaw, Snapshot.familyWith, Snapshot.family]) rfl)
    exact ⟨P, k, hk, by rw [familyQueue_keep s i (setRaw (s i) 0 p none) rfl]; simp [ParameterJump.emissions]⟩

/-! ### Weaving with wires -/

/-- The deliveries that the remaining FIRE dates will send. -/
def promised {n : ℕ} (route : Router n) (dates : Fin n → List ℝ) : Multiset (Delivery n) :=
  ∑ i, (((dates i).flatMap (route i) : List (Delivery n)) : Multiset (Delivery n))

theorem promised_step {n : ℕ} (route : Router n) (dates : Fin n → List ℝ) (i : Fin n)
    (now rest : List ℝ) (h : dates i = now ++ rest) :
    promised route dates = ((now.flatMap (route i) : List (Delivery n)) : Multiset (Delivery n)) +
      promised route (Function.update dates i rest) := by
  unfold promised
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase (a := i) _ (fun j =>
      (((Function.update dates i rest j).flatMap (route j) : List (Delivery n)) :
        Multiset (Delivery n))) (Finset.mem_univ i),
    Function.update_self, h, List.flatMap_append, ← Multiset.coe_add, add_assoc]
  congr 2
  exact Finset.sum_congr rfl (fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])

theorem mem_promised {n : ℕ} {route : Router n} {dates : Fin n → List ℝ} {d : Delivery n}
    (h : d ∈ promised route dates) : ∃ i, ∃ t ∈ dates i, d ∈ route i t := by
  obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp h
  obtain ⟨t, ht, hd⟩ := List.mem_flatMap.mp (Multiset.mem_coe.mp hi)
  exact ⟨i, t, ht, hd⟩

theorem Reach.dates_ge {θ : Fin 1 → Parameters} {s u : Snapshot 1} {dates : List ℝ} {count : ℕ}
    (h : Reach θ s u dates count) : ∀ t ∈ dates, s.time ≤ t := by
  obtain ⟨e, he, _⟩ := h
  intro t ht
  rw [← he] at ht
  obtain ⟨event, mem, rfl⟩ := List.mem_map.mp ht
  exact e.emission_time_lower event (List.mem_filter.mp mem).1

/-- One-cell runs woven into a run of the routed network. In its own
run, each cell already holds in its queue the pulses that other cells
will send it. In the network a pulse enters the queue at the FIRE that
sends it. The hypotheses are a strictly positive delay on every wire and
the balance of the queues: the queues of the cells are the queue of the
network plus what the remaining FIRE dates will send. Each cell keeps
its FIRE dates. -/
theorem routed_execution {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters}
    (route : Router n) (causal : ∀ i t d, d ∈ route i t → t < d.due) :
    ∀ (k : ℕ) (T T' : ℝ) (s u : Fin n → Snapshot 1) (dates : Fin n → List ℝ)
      (count : Fin n → ℕ) (P : List (Delivery n)), ∑ i, count i = k →
      (∀ i, Reach (θ i) (s i) (u i) (dates i) (count i)) →
      (∀ i, (s i).time = T) → (∀ i, (u i).time = T') →
      (familyQueue s : Multiset (Delivery n)) = (P : Multiset (Delivery n)) + promised route dates →
      ∃ (P' : List (Delivery n)) (E : ParameterExecution (familyParameters θ) route
          (Snapshot.familyWith T s P) (Snapshot.familyWith T' u P')),
        (∀ i, E.emissionTimes i = dates i) ∧
        (P' : Multiset (Delivery n)) = (familyQueue u : Multiset (Delivery n)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T T' s u dates count P total reach start finish balance
    classical
    by_cases jumping : ∃ (i : Fin n) (v : Snapshot 1)
        (j : ParameterJump (θ i) (fun _ _ => []) (s i) v) (rest : List ℝ) (c : ℕ),
        Reach (θ i) v (u i) rest c ∧ count i = c + 1 ∧
          dates i = j.emissions.map Prod.snd ++ rest
    · obtain ⟨i, v, j, rest, c, hr, hc, hd⟩ := jumping
      have available : ∀ e ∈ (s i).pending, e.due = T → Delivery.inCell i e ∈ P := by
        intro e he due
        have mem : Delivery.inCell i e ∈ (familyQueue s : Multiset (Delivery n)) :=
          Multiset.mem_coe.mpr (List.mem_flatMap.mpr
            ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨e, he, rfl⟩⟩)
        rw [balance] at mem
        rcases Multiset.mem_add.mp mem with h | h
        · exact Multiset.mem_coe.mp h
        · exfalso
          obtain ⟨i', t, ht, sent⟩ := mem_promised h
          have late := causal i' t _ sent
          have early := (reach i').dates_ge t ht
          rw [start i'] at early
          have same : (Delivery.inCell i e).due = T := due
          linarith
      obtain ⟨P₁, kJ, hk, account⟩ := routed_jump route i j (start i) P available
      have future := promised_step route dates i (j.emissions.map Prod.snd) rest hd
      have sent : ((j.emissions.flatMap (fun e => route i e.2) : List (Delivery n)) :
          Multiset (Delivery n)) =
          (((j.emissions.map Prod.snd).flatMap (route i) : List (Delivery n)) :
            Multiset (Delivery n)) := by
        rw [List.flatMap_map]
      have balance' : (familyQueue (Function.update s i v) : Multiset (Delivery n)) =
          (P₁ : Multiset (Delivery n)) + promised route (Function.update dates i rest) := by
        rw [sent] at account
        rw [balance, future] at account
        have h : (familyQueue (Function.update s i v) : Multiset (Delivery n)) +
            ((P : Multiset (Delivery n)) +
              (((j.emissions.map Prod.snd).flatMap (route i) : List (Delivery n)) :
                Multiset (Delivery n))) =
            ((P₁ : Multiset (Delivery n)) + promised route (Function.update dates i rest)) +
            ((P : Multiset (Delivery n)) +
              (((j.emissions.map Prod.snd).flatMap (route i) : List (Delivery n)) :
                Multiset (Delivery n))) := by
          rw [← add_assoc, account]
          abel
        exact add_right_cancel h
      have reach' : ∀ j', Reach (θ j') (Function.update s i v j') (u j')
          (Function.update dates i rest j') (Function.update count i c j') := by
        intro j'
        by_cases h : j' = i
        · subst j'
          simp only [Function.update_self]
          exact hr
        · simp only [Function.update_of_ne h]
          exact reach j'
      have start' : ∀ j', (Function.update s i v j').time = T := by
        intro j'
        by_cases h : j' = i
        · subst j'
          rw [Function.update_self, j.time_unchanged]
          exact start i
        · rw [Function.update_of_ne h]
          exact start j'
      have less : ∑ j', Function.update count i c j' < k := by
        rw [← total]
        apply Finset.sum_lt_sum
        · intro j' _
          by_cases h : j' = i
          · subst j'; rw [Function.update_self]; omega
          · rw [Function.update_of_ne h]
        · exact ⟨i, Finset.mem_univ i, by rw [Function.update_self]; omega⟩
      obtain ⟨P', E', hE', final⟩ := ih _ less T T' _ u _ _ P₁ rfl reach' start' finish balance'
      refine ⟨P', .cons (.jump kJ) E', fun i' => ?_, final⟩
      have tail := hE' i'
      unfold ParameterExecution.emissionTimes at tail ⊢
      simp only [ParameterExecution.emissions_cons, ParameterMove.emissions, List.filter_append,
        List.map_append]
      rw [tail, hk, lifted_times]
      by_cases h : i' = i
      · subst i'
        simp only [ite_true, Function.update_self]
        exact hd.symm
      · simp only [h, ite_false, List.nil_append, Function.update_of_ne h]
    · have head (i : Fin n) : (s i = u i ∧ dates i = [] ∧ count i = 0) ∨
          ∃ (v : Snapshot 1) (_ : ParameterFlow (θ i) (s i) v) (c : ℕ),
            Reach (θ i) v (u i) (dates i) c ∧ count i = c + 1 := by
        rcases (reach i).cases with h | ⟨v, j, rest, c, hr, hc, hd⟩ | h
        · exact Or.inl h
        · exact absurd ⟨i, v, j, rest, c, hr, hc, hd⟩ jumping
        · exact Or.inr h
      by_cases flowing : ∃ i, ∃ (v : Snapshot 1) (_ : ParameterFlow (θ i) (s i) v) (c : ℕ),
          Reach (θ i) v (u i) (dates i) c ∧ count i = c + 1
      · obtain ⟨i₀, v₀, f₀, c₀, hr₀, _⟩ := flowing
        have lt : T < T' := by
          have h₁ := f₀.positive
          have h₂ := hr₀.time_le
          rw [start i₀] at h₁
          rw [finish i₀] at h₂
          linarith
        have flows : ∀ i, ∃ (v : Snapshot 1) (_ : ParameterFlow (θ i) (s i) v) (c : ℕ),
            Reach (θ i) v (u i) (dates i) c ∧ count i = c + 1 := by
          intro i
          rcases head i with ⟨same, _, _⟩ | h
          · exfalso
            have h := congrArg Snapshot.time same
            rw [start i, finish i] at h
            linarith
          · exact h
        choose v f c hr hc using flows
        obtain ⟨m, -, least⟩ := Finset.exists_min_image Finset.univ (fun i => (v i).time)
          ⟨⟨0, pos⟩, Finset.mem_univ _⟩
        have after (i : Fin n) : (s i).time < (v m).time := by
          have h := (f m).positive
          rw [start m] at h
          rw [start i]
          exact h
        have before (i : Fin n) : (v m).time ≤ (v i).time := least i (Finset.mem_univ i)
        have urgent : ∀ d ∈ P, (v m).time ≤ d.due := by
          intro d hd
          have mem : d ∈ (familyQueue s : Multiset (Delivery n)) := by
            rw [balance]
            exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr hd))
          obtain ⟨i, e, he, rfl⟩ := mem_familyQueue (Multiset.mem_coe.mp mem)
          exact (flowPrefix (f i) (after i) (before i)).pending_urgent e he
        let F := familyFlowWith (fun i => flowPrefix (f i) (after i) (before i))
          (by have h := after m; rw [start m] at h; exact h) start (fun _ => rfl) P urgent
        have reach' : ∀ i, Reach (θ i) ((f i).at (v m).time) (u i) (dates i)
            (if (v i).time = (v m).time then c i else c i + 1) := by
          intro i
          by_cases same : (v i).time = (v m).time
          · simp only [same, ite_true]
            rw [← same, (f i).at_final]
            exact hr i
          · simp only [same, ite_false]
            exact Reach.flow ((f i).suffix (after i).le
              (lt_of_le_of_ne (before i) (fun h => same h.symm))) (hr i)
        have less : ∑ i, (if (v i).time = (v m).time then c i else c i + 1) < k := by
          rw [← total]
          apply Finset.sum_lt_sum
          · intro i _
            rw [hc i]
            split <;> omega
          · exact ⟨m, Finset.mem_univ m, by rw [hc m]; simp⟩
        have sameQueue : familyQueue (fun i => (f i).at (v m).time) = familyQueue s := rfl
        obtain ⟨P', E', hE', final⟩ := ih _ less (v m).time T' _ u dates _ P rfl reach'
          (fun _ => rfl) finish (by rw [sameQueue]; exact balance)
        refine ⟨P', .cons (.flow F) E', fun i' => ?_, final⟩
        rw [← hE' i']
        simp [ParameterExecution.emissionTimes, ParameterMove.emissions]
      · have still (i : Fin n) : s i = u i ∧ dates i = [] := by
          rcases head i with ⟨same, empty, _⟩ | h
          · exact ⟨same, empty⟩
          · exact absurd ⟨i, h⟩ flowing
        have same : s = u := funext fun i => (still i).1
        have date : T = T' := by
          have h := congrArg Snapshot.time (still ⟨0, pos⟩).1
          rw [start, finish] at h
          exact h
        have none : dates = fun _ => [] := funext fun i => (still i).2
        subst same
        subst date
        subst none
        refine ⟨P, .nil _, fun i => rfl, ?_⟩
        rw [balance]
        simp [promised]

end RecursiveLearning.Native
