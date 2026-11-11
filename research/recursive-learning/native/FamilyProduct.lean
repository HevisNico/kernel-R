import TrainedCoincidence

/-! Networks of any number of independent cells. Each cell has its own
parameters and its own one-cell execution. The executions are woven into
one execution of the n-cell network, with each cell's FIRE dates kept. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- The parameters of a network of independent cells. -/
def familyParameters {n : ℕ} (θ : Fin n → Fin 1 → Parameters) : Fin n → Parameters :=
  fun i => θ i 0

/-- A delivery of cell `i`, seen in the network. -/
def Delivery.inCell {n : ℕ} (i : Fin n) (d : Delivery 1) : Delivery n := ⟨i, d.port, d.due⟩

/-- The queue of the network: the queues of the cells, in cell order. -/
def familyQueue {n : ℕ} (s : Fin n → Snapshot 1) : List (Delivery n) :=
  (List.finRange n).flatMap (fun i => (s i).pending.map (Delivery.inCell i))

/-- The network state made of `n` one-cell states at the date `T`. -/
def Snapshot.family {n : ℕ} (T : ℝ) (s : Fin n → Snapshot 1) : Snapshot n where
  time := T
  x := fun i c => (s i).x 0 c
  main := fun i => (s i).main 0
  aux := fun i => (s i).aux 0
  raw := fun i => (s i).raw 0
  pending := familyQueue s

theorem mem_familyQueue {n : ℕ} {s : Fin n → Snapshot 1} {d : Delivery n}
    (h : d ∈ familyQueue s) : ∃ i, ∃ e ∈ (s i).pending, d = Delivery.inCell i e := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
  exact ⟨i, e, he, rfl⟩

/-- The queue of the network around the queue of one cell. -/
theorem familyQueue_split {n : ℕ} (s : Fin n → Snapshot 1) (i : Fin n) :
    ∃ L R : List (Delivery n), ∀ v : Snapshot 1,
      familyQueue (Function.update s i v) = L ++ v.pending.map (Delivery.inCell i) ++ R := by
  obtain ⟨l₁, l₂, split⟩ := List.append_of_mem (List.mem_finRange i)
  have nodup : (l₁ ++ i :: l₂).Nodup := split ▸ List.nodup_finRange n
  have out₁ : ∀ j ∈ l₁, j ≠ i := by
    intro j hj h
    subst h
    exact (List.nodup_append.mp nodup).2.2 j hj j (List.mem_cons_self) rfl
  have out₂ : ∀ j ∈ l₂, j ≠ i := by
    intro j hj h
    subst h
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1 hj
  refine ⟨l₁.flatMap (fun j => (s j).pending.map (Delivery.inCell j)),
    l₂.flatMap (fun j => (s j).pending.map (Delivery.inCell j)), fun v => ?_⟩
  unfold familyQueue
  rw [split, List.flatMap_append, List.flatMap_cons, Function.update_self]
  have same₁ : l₁.flatMap (fun j => (Function.update s i v j).pending.map (Delivery.inCell j)) =
      l₁.flatMap (fun j => (s j).pending.map (Delivery.inCell j)) :=
    List.flatMap_congr (fun j hj => by rw [Function.update_of_ne (out₁ j hj)])
  have same₂ : l₂.flatMap (fun j => (Function.update s i v j).pending.map (Delivery.inCell j)) =
      l₂.flatMap (fun j => (s j).pending.map (Delivery.inCell j)) :=
    List.flatMap_congr (fun j hj => by rw [Function.update_of_ne (out₂ j hj)])
  rw [same₁, same₂, List.append_assoc]

theorem familyQueue_keep {n : ℕ} (s : Fin n → Snapshot 1) (i : Fin n) (v : Snapshot 1)
    (h : v.pending = (s i).pending) : familyQueue (Function.update s i v) = familyQueue s := by
  obtain ⟨L, R, split⟩ := familyQueue_split s i
  have original := split (s i)
  rw [Function.update_eq_self] at original
  rw [split v, h, original]

theorem Snapshot.family_congr {n : ℕ} {T : ℝ} {s : Fin n → Snapshot 1} {w : Snapshot n}
    (time : w.time = T) (x : ∀ j c, w.x j c = (s j).x 0 c) (main : ∀ j, w.main j = (s j).main 0)
    (aux : ∀ j p, w.aux j p = (s j).aux 0 p) (raw : ∀ j p, w.raw j p = (s j).raw 0 p)
    (pending : w.pending = familyQueue s) : w = Snapshot.family T s := by
  cases w
  simp only [Snapshot.family, Snapshot.mk.injEq]
  exact ⟨time, funext fun j => funext fun c => x j c, funext main,
    funext fun j => funext fun p => aux j p, funext fun j => funext fun p => raw j p, pending⟩

/-- The field of the network at cell `i` is the field of that cell. -/
theorem family_field {n : ℕ} (θ : Fin n → Fin 1 → Parameters) (T : ℝ) (s : Fin n → Snapshot 1)
    (X : Fin n → Values 1) (t : ℝ) (i : Fin n) (c : Coord) :
    field (familyParameters θ) (Snapshot.family T s) (fun j c => X j 0 c) t i c =
      field (θ i) (s i) (X i) t 0 c := by
  cases c <;> rfl

/-- The synchronized flows of the cells form a flow of the network. -/
noncomputable def familyFlow {n : ℕ} {θ : Fin n → Fin 1 → Parameters} {T T' : ℝ}
    {s u : Fin n → Snapshot 1} (f : ∀ i, ParameterFlow (θ i) (s i) (u i)) (lt : T < T')
    (start : ∀ i, (s i).time = T) (finish : ∀ i, (u i).time = T') :
    ParameterFlow (familyParameters θ) (Snapshot.family T s) (Snapshot.family T' u) where
  positive := lt
  path := fun t i c => (f i).path t 0 c
  initial := by
    funext i c
    show (f i).path T 0 c = (s i).x 0 c
    rw [← start i, (f i).initial]
  final := by
    funext i c
    show (f i).path T' 0 c = (u i).x 0 c
    rw [← finish i, (f i).final]
  main_fixed := by
    funext i
    exact congrFun (f i).main_fixed 0
  aux_fixed := by
    funext i
    exact congrFun (f i).aux_fixed 0
  raw_fixed := by
    funext i
    exact congrFun (f i).raw_fixed 0
  queue_fixed := by
    show familyQueue u = familyQueue s
    unfold familyQueue
    exact List.flatMap_congr (fun i _ => by rw [(f i).queue_fixed])
  continuous := by
    intro i c
    have h := (f i).continuous 0 c
    rw [start i, finish i] at h
    exact h
  integrable := by
    intro i c
    have h := (f i).integrable 0 c
    rw [start i, finish i] at h
    exact h
  mark_integrable := by
    intro i p
    have h := (f i).mark_integrable 0 p
    rw [start i, finish i] at h
    exact h
  integral_eq := by
    intro t ht i c
    have h := (f i).integral_eq t (by rw [start i, finish i]; exact ht) 0 c
    rw [start i] at h
    exact h
  guards := by
    intro t ht
    have local_ (i : Fin n) := (f i).guards t (by rw [start i, finish i]; exact ht)
    exact ⟨fun i => (local_ i).1 0, fun i p => (local_ i).2 0 p⟩
  raw_support := by
    intro i p origin h
    have r := (f i).raw_support 0 p origin h
    rw [start i, finish i] at r
    exact r
  pending_urgent := by
    intro d hd
    obtain ⟨i, e, he, rfl⟩ := mem_familyQueue hd
    have r := (f i).pending_urgent e he
    rw [finish i] at r
    exact r

theorem family_update_eq {n : ℕ} {T : ℝ} {s : Fin n → Snapshot 1} {i : Fin n} {v : Snapshot 1}
    {w : Snapshot n} (time : w.time = T)
    (x : ∀ j c, w.x j c = (s j).x 0 c) (vx : v.x = (s i).x)
    (main : ∀ j, j ≠ i → w.main j = (s j).main 0) (mainI : w.main i = v.main 0)
    (aux : ∀ j, j ≠ i → ∀ p, w.aux j p = (s j).aux 0 p) (auxI : ∀ p, w.aux i p = v.aux 0 p)
    (raw : ∀ j, j ≠ i → ∀ p, w.raw j p = (s j).raw 0 p) (rawI : ∀ p, w.raw i p = v.raw 0 p)
    (pending : w.pending = familyQueue (Function.update s i v)) :
    w = Snapshot.family T (Function.update s i v) := by
  apply Snapshot.family_congr time _ _ _ _ pending
  · intro j c
    by_cases h : j = i
    · subst j; rw [Function.update_self, vx]; exact x i c
    · rw [Function.update_of_ne h]; exact x j c
  · intro j
    by_cases h : j = i
    · subst j; rw [Function.update_self]; exact mainI
    · rw [Function.update_of_ne h]; exact main j h
  · intro j p
    by_cases h : j = i
    · subst j; rw [Function.update_self]; exact auxI p
    · rw [Function.update_of_ne h]; exact aux j h p
  · intro j p
    by_cases h : j = i
    · subst j; rw [Function.update_self]; exact rawI p
    · rw [Function.update_of_ne h]; exact raw j h p

theorem jump_to {n : ℕ} {θ : Fin n → Parameters} {route : Router n} {a w b : Snapshot n}
    (k : ParameterJump θ route a w) (h : w = b) :
    ∃ k' : ParameterJump θ route a b, k'.emissions = k.emissions := by
  subst h
  exact ⟨k, rfl⟩

/-- A jump of one cell is a jump of the network. -/
theorem family_jump {n : ℕ} {θ : Fin n → Fin 1 → Parameters} {T : ℝ} {s : Fin n → Snapshot 1}
    (i : Fin n) {v : Snapshot 1} (j : ParameterJump (θ i) (fun _ _ => []) (s i) v)
    (hs : (s i).time = T) :
    ∃ k : ParameterJump (familyParameters θ) (fun _ _ => []) (Snapshot.family T s)
        (Snapshot.family T (Function.update s i v)),
      k.emissions = j.emissions.map (fun e => (i, e.2)) := by
  generalize hsi : s i = a at j
  cases j with
  | fire i₀ mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.fire (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) i mode guard)
      (family_update_eq (v := { (setMain (s i) 0 .fast) with
          pending := (s i).pending ++ (fun (_ : Fin 1) (_ : ℝ) => ([] : List (Delivery 1))) 0 (s i).time }) rfl (fun _ _ => rfl) rfl
        (fun j hj => by simp [setMain, Snapshot.family, hj]) (by simp [setMain, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
        (by
          show familyQueue s ++ [] = _
          rw [familyQueue_keep s i _ (by simp), List.append_nil]))
    refine ⟨k, hk.trans ?_⟩
    show [(i, T)] = [(i, (s i).time)]
    rw [hs]
  | fastEnd i₀ mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.fastEnd (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) i mode guard)
      (family_update_eq (v := setMain (s i) 0 .slow) rfl (fun _ _ => rfl) rfl
        (fun j hj => by simp [setMain, Snapshot.family, hj]) (by simp [setMain, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
        (familyQueue_keep s i (setMain (s i) 0 .slow) rfl).symm)
    exact ⟨k, hk⟩
  | reopen i₀ mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.reopen (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) i mode guard)
      (family_update_eq (v := setMain (s i) 0 .ready) rfl (fun _ _ => rfl) rfl
        (fun j hj => by simp [setMain, Snapshot.family, hj]) (by simp [setMain, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
        (familyQueue_keep s i (setMain (s i) 0 .ready) rfl).symm)
    exact ⟨k, hk⟩
  | mark i₀ p mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.mark (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) i p mode guard)
      (family_update_eq (v := setAux (s i) 0 p .mark) rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl
        (fun j hj q => by simp [setAux, Snapshot.family, hj])
        (fun q => by simp [setAux, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (familyQueue_keep s i (setAux (s i) 0 p .mark) rfl).symm)
    exact ⟨k, hk⟩
  | silent i₀ p mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.silent (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) i p mode guard)
      (family_update_eq (v := setAux (s i) 0 p .silent) rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl
        (fun j hj q => by simp [setAux, Snapshot.family, hj])
        (fun q => by simp [setAux, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (familyQueue_keep s i (setAux (s i) 0 p .silent) rfl).symm)
    exact ⟨k, hk⟩
  | error i₀ p mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.error (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) i p mode guard)
      (family_update_eq (v := setAux (s i) 0 p .error) rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl
        (fun j hj q => by simp [setAux, Snapshot.family, hj])
        (fun q => by simp [setAux, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (familyQueue_keep s i (setAux (s i) 0 p .error) rfl).symm)
    exact ⟨k, hk⟩
  | auxReady i₀ p mode guard =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.auxReady (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) i p mode guard)
      (family_update_eq (v := setAux (s i) 0 p .ready) rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl
        (fun j hj q => by simp [setAux, Snapshot.family, hj])
        (fun q => by simp [setAux, Snapshot.family])
        (fun _ _ _ => rfl) (fun _ => rfl) (familyQueue_keep s i (setAux (s i) 0 p .ready) rfl).symm)
    exact ⟨k, hk⟩
  | arrive d before after queue due free =>
    subst hsi
    have hc : d.cell = 0 := Subsingleton.elim _ _
    obtain ⟨L, R, split⟩ := familyQueue_split s i
    have original := split (s i)
    rw [Function.update_eq_self] at original
    have joint : (Snapshot.family T s).pending =
        (L ++ before.map (Delivery.inCell i)) ++ Delivery.inCell i d ::
          (after.map (Delivery.inCell i) ++ R) := by
      show familyQueue s = _
      rw [original, queue]
      simp
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.arrive (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) (Delivery.inCell i d) (L ++ before.map (Delivery.inCell i))
        (after.map (Delivery.inCell i) ++ R) joint (due.trans hs)
        (by
          show (s i).raw 0 d.port = none
          rw [← hc]
          exact free))
      (family_update_eq (v := { (setRaw (s i) d.cell d.port (some (s i).time)) with
          pending := before ++ after }) rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl
        (fun _ _ _ => rfl) (fun _ => rfl)
        (fun j hj q => by simp [setRaw, Snapshot.family, Delivery.inCell, hj])
        (fun q => by simp [setRaw, Snapshot.family, Delivery.inCell, hc, hs])
        (by
          rw [split]
          simp))
    exact ⟨k, hk⟩
  | rawEnd i₀ p origin active due =>
    subst hsi
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := jump_to
      (ParameterJump.rawEnd (θ := familyParameters θ) (route := fun _ _ => [])
        (Snapshot.family T s) i p origin active (hs.symm.trans due))
      (family_update_eq (v := setRaw (s i) 0 p none) rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl
        (fun _ _ _ => rfl) (fun _ => rfl)
        (fun j hj q => by simp [setRaw, Snapshot.family, hj])
        (fun q => by simp [setRaw, Snapshot.family])
        (familyQueue_keep s i (setRaw (s i) 0 p none) rfl).symm)
    exact ⟨k, hk⟩

/-! ### Weaving the executions of the cells -/

/-- The part of a flow up to an intermediate date. -/
noncomputable def flowPrefix {n θ s u} (f : @ParameterFlow n θ s u) {t : ℝ}
    (hstart : s.time < t) (hend : t ≤ u.time) : ParameterFlow θ s (f.at t) where
  positive := hstart
  path := f.path
  initial := f.initial
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun i c => (f.continuous i c).mono (Icc_subset_Icc le_rfl hend)
  integrable := fun i c => (f.integrable i c).mono_set (by
    dsimp only [ParameterFlow.at]
    rw [uIcc_of_le hstart.le, uIcc_of_le f.positive.le]
    exact Icc_subset_Icc le_rfl hend)
  mark_integrable := fun i p => (f.mark_integrable i p).mono_set (by
    dsimp only [ParameterFlow.at]
    rw [uIcc_of_le hstart.le, uIcc_of_le f.positive.le]
    exact Icc_subset_Icc le_rfl hend)
  integral_eq := fun v hv i c => f.integral_eq v ⟨hv.1, hv.2.trans hend⟩ i c
  guards := fun v hv => f.guards v ⟨hv.1, hv.2.trans_le hend⟩
  raw_support := fun i p origin hraw =>
    ⟨(f.raw_support i p origin hraw).1, hend.trans (f.raw_support i p origin hraw).2⟩
  pending_urgent := fun d hd => hend.trans (f.pending_urgent d hd)

/-- A one-cell run with its FIRE dates and its number of moves. -/
def Reach (θ : Fin 1 → Parameters) (s u : Snapshot 1) (dates : List ℝ) (count : ℕ) : Prop :=
  ∃ e : ParameterExecution θ (fun _ _ => []) s u, e.emissionTimes 0 = dates ∧ e.moveCount = count

theorem Reach.time_le {θ : Fin 1 → Parameters} {s u : Snapshot 1} {dates : List ℝ} {count : ℕ}
    (h : Reach θ s u dates count) : s.time ≤ u.time := by
  obtain ⟨e, _, _⟩ := h
  exact e.time_monotone

theorem Reach.flow {θ : Fin 1 → Parameters} {s v u : Snapshot 1} {dates : List ℝ} {count : ℕ}
    (f : ParameterFlow θ s v) (h : Reach θ v u dates count) : Reach θ s u dates (count + 1) := by
  obtain ⟨e, he, hc⟩ := h
  refine ⟨.cons (.flow f) e, ?_, by simp [hc]⟩
  rw [← he]
  simp [ParameterExecution.emissionTimes, ParameterMove.emissions]

theorem single_cell_times (l : List (Fin 1 × ℝ)) :
    (l.filter (fun e => e.1 = 0)).map Prod.snd = l.map Prod.snd := by
  congr 1
  exact List.filter_eq_self.mpr (fun e _ => by simp [Subsingleton.elim e.1 0])

/-- The first move of a one-cell run. -/
theorem Reach.cases {θ : Fin 1 → Parameters} {s u : Snapshot 1} {dates : List ℝ} {count : ℕ}
    (h : Reach θ s u dates count) :
    (s = u ∧ dates = [] ∧ count = 0) ∨
    (∃ (v : Snapshot 1) (j : ParameterJump θ (fun _ _ => []) s v) (rest : List ℝ) (c : ℕ),
      Reach θ v u rest c ∧ count = c + 1 ∧ dates = j.emissions.map Prod.snd ++ rest) ∨
    (∃ (v : Snapshot 1) (_ : ParameterFlow θ s v) (c : ℕ),
      Reach θ v u dates c ∧ count = c + 1) := by
  obtain ⟨e, he, hc⟩ := h
  cases e with
  | nil =>
    refine Or.inl ⟨rfl, ?_, ?_⟩
    · rw [← he]; rfl
    · rw [← hc]; rfl
  | cons m rest =>
    cases m with
    | flow f =>
      refine Or.inr (Or.inr ⟨_, f, rest.moveCount, ⟨rest, ?_, rfl⟩, ?_⟩)
      · rw [← he]
        simp [ParameterExecution.emissionTimes, ParameterMove.emissions]
      · rw [← hc]; rfl
    | jump j =>
      refine Or.inr (Or.inl ⟨_, j, rest.emissionTimes 0, rest.moveCount, ⟨rest, rfl, rfl⟩, ?_, ?_⟩)
      · rw [← hc]; rfl
      · rw [← he]
        simp only [ParameterExecution.emissionTimes, ParameterExecution.emissions_cons,
          ParameterMove.emissions, List.filter_append, List.map_append, single_cell_times]

theorem lifted_times {n : ℕ} (l : List (Fin 1 × ℝ)) (i i' : Fin n) :
    ((l.map (fun e => (i, e.2))).filter (fun e => e.1 = i')).map Prod.snd =
      if i' = i then l.map Prod.snd else [] := by
  induction l with
  | nil => simp
  | cons e rest ih =>
    by_cases h : i' = i
    · subst h
      simp only [ite_true] at ih ⊢
      simp [ih]
    · have h' : i ≠ i' := fun e => h e.symm
      simp only [h, ite_false] at ih ⊢
      simp [h', ih]

/-- Independent one-cell runs with the same start and end dates form one
run of the network. Each cell keeps its FIRE dates. -/
theorem family_execution {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters} :
    ∀ (k : ℕ) (T T' : ℝ) (s u : Fin n → Snapshot 1) (dates : Fin n → List ℝ)
      (count : Fin n → ℕ), ∑ i, count i = k →
      (∀ i, Reach (θ i) (s i) (u i) (dates i) (count i)) →
      (∀ i, (s i).time = T) → (∀ i, (u i).time = T') →
      ∃ E : ParameterExecution (familyParameters θ) (fun _ _ => [])
          (Snapshot.family T s) (Snapshot.family T' u),
        ∀ i, E.emissionTimes i = dates i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T T' s u dates count total reach start finish
    classical
    by_cases jumping : ∃ (i : Fin n) (v : Snapshot 1)
        (j : ParameterJump (θ i) (fun _ _ => []) (s i) v) (rest : List ℝ) (c : ℕ),
        Reach (θ i) v (u i) rest c ∧ count i = c + 1 ∧
          dates i = j.emissions.map Prod.snd ++ rest
    · obtain ⟨i, v, j, rest, c, hr, hc, hd⟩ := jumping
      obtain ⟨kJ, hk⟩ := family_jump i j (start i)
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
      obtain ⟨E', hE'⟩ := ih _ less T T' _ u _ _ rfl reach' start' finish
      refine ⟨.cons (.jump kJ) E', fun i' => ?_⟩
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
        let F := familyFlow (fun i => flowPrefix (f i) (after i) (before i))
          (by have h := after m; rw [start m] at h; exact h) start (fun _ => rfl)
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
        obtain ⟨E', hE'⟩ := ih _ less (v m).time T' _ u dates _ rfl reach' (fun _ => rfl) finish
        refine ⟨.cons (.flow F) E', fun i' => ?_⟩
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
        subst same
        subst date
        exact ⟨.nil _, fun i => by rw [(still i).2]; rfl⟩

/-! ### Networks of trained cells -/

/-- A network of rested cells with empty queues has no move left. -/
theorem family_complete {n : ℕ} {θ : Fin n → Fin 1 → Parameters} {T : ℝ}
    {u : Fin n → Snapshot 1} {level : Fin n → ℝ} {s : Snapshot n}
    (cell : ∀ i, CellConfig (θ i) (level i)) (fire : ∀ i, 19 / 20 ≤ level i)
    (rested : ∀ i, RestState (θ i) (u i)) (empty : ∀ i, (u i).pending = [])
    (E : ParameterExecution (familyParameters θ) (fun _ _ => []) s (Snapshot.family T u)) :
    ParameterCompleteThrough E T := by
  have guards (i : Fin n) : ThresholdGuards (fun j => (θ i j).thresholds) (u i) (u i).x :=
    cell_guards_rest (cell i) (rested i).main
      (by linarith [(rested i).charge.2, fire i]) (rested i).aux
      (fun q => lt_of_le_of_lt ((rested i).sensors q).2 (by norm_num))
  have none : ∀ d ∈ (Snapshot.family T u).pending, T < d.due := by
    intro d hd
    obtain ⟨i, e, he, _⟩ := mem_familyQueue hd
    rw [empty i] at he
    cases he
  refine ⟨rfl, ?_, none⟩
  apply (Snapshot.family T u).no_parameter_jump
  · exact ⟨fun i => (guards i).1 0, fun i p => (guards i).2 0 p⟩
  · exact none
  · intro i p o h
    have h' : (u i).raw 0 p = some o := h
    rw [(rested i).raw p] at h'
    cases h'

/-- The complete local run of one trained cell, ending at rest. -/
theorem TrainedCell.run_rest {θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle read₁ read₂ rest
    r₁ r₂}
    (cell : TrainedCell θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle read₁ read₂ rest r₁ r₂) :
    ∃ (u : Snapshot 1) (tf : ℝ) (training : List ℝ) (count : ℕ),
      read₁ + 239 / 1000 < tf ∧ tf ≤ read₂ + 32 / 125 ∧
      Reach θ s u (training ++ [tf]) count ∧ RestState θ u ∧ u.time = rest ∧ u.pending = [] := by
  obtain ⟨u, tf, training, after, before, ⟨e, times⟩, rested, date, pend, _, _, _⟩ :=
    trained_read_exists cell.box cell.distinct cell.config₁ cell.config₂ cell.fire cell.entry₁
      cell.exit₁ cell.entry₂ cell.exit₂ cell.dose₁ cell.dose₂ cell.state cell.recovery cell.queue
      cell.spaced₁ cell.spaced₂ cell.order cell.wait cell.below₁ cell.below₂ r₁ r₂ cell.reach₁
      cell.reach₂ cell.enough₁ cell.enough₂
  exact ⟨u, tf, training, e.moveCount, after, before, ⟨e, times, rfl⟩, rested, date, pend⟩

/-- A network of any number of trained cells. Each cell has its own
parameters in the fabrication box, its own start gains, its own FIRE
level, its own pulse trains and its own read dates. In every complete run
of the network, the last FIRE of each cell is its read FIRE. It comes
later than 0.239 units after the cell's first read pulse and no later
than 0.256 units after its second. For any two cells read with an offset
of −0.3, 0 or +0.3 units, the two dates are closer than 3/20 exactly when
the offset is zero. -/
theorem trained_network {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters} {ε T rest : ℝ}
    {s : Fin n → Snapshot 1} {p₁ p₂ : Fin n → Port} {u₁ l₁ u₂ l₂ level : Fin n → ℝ}
    {dates₁ dates₂ : Fin n → List ℝ} {middle read₁ read₂ : Fin n → ℝ} {r₁ r₂ : Fin n → ℕ}
    (cells : ∀ i, TrainedCell (θ i) ε (s i) (p₁ i) (p₂ i) (u₁ i) (l₁ i) (u₂ i) (l₂ i) (level i)
      (dates₁ i) (dates₂ i) (middle i) (read₁ i) (read₂ i) rest (r₁ i) (r₂ i))
    (start : ∀ i, (s i).time = T) :
    ∃ (tf : Fin n → ℝ) (training : Fin n → List ℝ),
      (∀ i, read₁ i + 239 / 1000 < tf i ∧ tf i ≤ read₂ i + 32 / 125) ∧
      (∀ i j offset, read₂ i ≤ read₁ i + 1 / 10 → read₂ j ≤ read₁ j + 1 / 10 →
        read₁ j = read₁ i + offset → (offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10) →
        (|tf j - tf i| < 3 / 20 ↔ offset = 0)) ∧
      (∃ (u : Snapshot n) (ref : ParameterExecution (familyParameters θ) (fun _ _ => [])
        (Snapshot.family T s) u), ParameterCompleteThrough ref rest) ∧
      ∀ {u : Snapshot n} (ex : ParameterExecution (familyParameters θ) (fun _ _ => [])
        (Snapshot.family T s) u), ParameterCompleteThrough ex rest →
        ∀ i, ex.emissionTimes i = training i ++ [tf i] := by
  choose u tf training count after before reach rested date pend using
    fun i => (cells i).run_rest
  obtain ⟨E, times⟩ := family_execution pos _ T rest s u (fun i => training i ++ [tf i]) count
    rfl reach start date
  have complete := family_complete (fun i => (cells i).config₁.cell) (fun i => (cells i).fire.1)
    rested pend E
  have box : PhysicalBox (familyParameters θ) ε :=
    ⟨(cells ⟨0, pos⟩).box.1, fun i p => (cells i).box.2 0 p⟩
  have b (i : Fin n) := cell_threshold_bounds (cells i).config₁.cell (cells i).fire
  have bounds : ParameterThresholdBounds (familyParameters θ) :=
    ⟨fun i => (b i).fire 0, fun i => (b i).fastEnd 0, fun i => (b i).fastBelowFire 0,
      fun i => (b i).reopen 0, fun i p => (b i).mark 0 p, fun i p => (b i).silent 0 p,
      fun i p => (b i).error 0 p, fun i p => (b i).auxReady 0 p⟩
  have inv (i : Fin n) := (cells i).state.physical
  have birth : ParameterPhysicalInvariant (familyParameters θ) (Snapshot.family T s) :=
    ⟨fun i => (inv i).charge 0, fun i p => (inv i).sensor 0 p, fun i p => (inv i).gain 0 p,
      fun i => (inv i).recovery 0, fun i => (inv i).reserve 0⟩
  refine ⟨tf, training, fun i => ⟨after i, before i⟩, ?_, ⟨_, E, complete⟩, ?_⟩
  · intro i j offset staggerI staggerJ schedule offsets
    exact trained_dates_decide (after i) (before i) (after j) (before j)
      ⟨(cells i).order.1, staggerI⟩ ⟨(cells j).order.1, staggerJ⟩ schedule offsets
  · intro w ex done i
    rw [ex.emissionTimes_unique E box bounds birth done complete i, times i]

/-- The hypotheses hold for a network of `n` copies of the explicit cell.
In every complete run, every cell fires its read at a date in its window
and any two cells are accepted together. -/
theorem trained_network_witness (n : ℕ) (pos : 0 < n) :
    ∃ (tf : Fin n → ℝ) (training : Fin n → List ℝ),
      (∃ (u : Snapshot n) (ref : ParameterExecution
        (familyParameters (fun (_ : Fin n) (_ : Fin 1) => witnessParameters)) (fun _ _ => [])
        (Snapshot.family 0 (fun _ => witnessStart)) u), ParameterCompleteThrough ref 990) ∧
      ∀ {u : Snapshot n} (ex : ParameterExecution
        (familyParameters (fun (_ : Fin n) (_ : Fin 1) => witnessParameters)) (fun _ _ => [])
        (Snapshot.family 0 (fun _ => witnessStart)) u), ParameterCompleteThrough ex 990 →
        (∀ i, ex.emissionTimes i = training i ++ [tf i]) ∧
        ∀ i j, |tf j - tf i| < 3 / 20 := by
  obtain ⟨tf, training, _, decide, ref, all⟩ :=
    trained_network pos (θ := fun _ _ => witnessParameters) (s := fun _ => witnessStart)
      (fun _ => trainedCell_witness) (fun _ => rfl)
  refine ⟨tf, training, ref, fun ex done => ⟨all ex done, fun i j => ?_⟩⟩
  exact (decide i j 0 (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl rfl))).mpr rfl

end RecursiveLearning.Native
