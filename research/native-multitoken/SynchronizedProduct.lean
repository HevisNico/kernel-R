import NativeStrongStep
import KernelR.HybridNeutralExecutionProduct
import KernelR.HybridWeakInputCycleExistence

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid NativeStrong Set MeasureTheory
open scoped BigOperators

/-- Assemble the cell coordinates at a shared date. The global queue is
separate from the empty local routers used to construct pulse legs. -/
noncomputable def assemble (t : ℝ) (states : Fin N → Snapshot 1)
    (queue : List (Delivery N)) : Snapshot N :=
  ⟨t, fun i => (states i).x 0, fun i => (states i).main 0,
    fun i => (states i).aux 0, fun i => (states i).raw 0, queue⟩

theorem assemble_field (θ : Fin N → Parameters) (t : ℝ)
    (states : Fin N → Snapshot 1) (q : List (Delivery N)) (path : ℝ → Values N)
    (v : ℝ) (i : Fin N) (c : Coord) :
    field θ (assemble t states q) (path v) v i c =
      field (fun _ => θ i) (states i) (fun _ => path v i) v 0 c := by
  cases c <;> rfl

noncomputable def parallelFlow {θ : Fin N → Parameters} {t u : ℝ}
    {a b : Fin N → Snapshot 1} (start : ∀ i, (a i).time = t)
    (finish : ∀ i, (b i).time = u) (positive : t < u)
    (f : ∀ i, Flow (fun _ => θ i) (a i) (b i))
    (q : List (Delivery N)) (urgent : ∀ d ∈ q, u ≤ d.due) :
    Flow θ (assemble t a q) (assemble u b q) where
  positive := positive
  path v i := (f i).path v 0
  initial := funext fun i => by simpa [assemble, start i] using congrFun (f i).initial 0
  final := funext fun i => by simpa [assemble, finish i] using congrFun (f i).final 0
  main_fixed := funext fun i => congrFun (f i).main_fixed 0
  aux_fixed := funext fun i => congrFun (f i).aux_fixed 0
  raw_fixed := funext fun i => congrFun (f i).raw_fixed 0
  queue_fixed := rfl
  continuous i c := by simpa [assemble, start i, finish i] using (f i).continuous 0 c
  integrable i c := by
    change IntervalIntegrable (fun v => field θ (assemble t a q)
      (fun j => (f j).path v 0) v i c) volume t u
    rw [funext (fun v => assemble_field θ t a q (fun w j => (f j).path w 0) v i c)]
    have same (v : ℝ) : (fun _ : Fin 1 => (f i).path v 0) = (f i).path v :=
      funext fun j => congrArg ((f i).path v) (Subsingleton.elim 0 j)
    simpa only [same, start i, finish i] using (f i).integrable 0 c
  mark_integrable i p := by
    simpa [assemble, markAct, start i, finish i] using (f i).mark_integrable 0 p
  integral_eq v hv i c := by
    have inside : v ∈ Icc (a i).time (b i).time := by simpa [assemble, start i, finish i] using hv
    change (f i).path v 0 c = (a i).x 0 c +
      ∫ w in t..v, field θ (assemble t a q) (fun j => (f j).path w 0) w i c
    rw [funext (fun w => assemble_field θ t a q (fun z j => (f j).path z 0) w i c)]
    have same (w : ℝ) : (fun _ : Fin 1 => (f i).path w 0) = (f i).path w :=
      funext fun j => congrArg ((f i).path w) (Subsingleton.elim 0 j)
    simpa only [same, start i] using (f i).integral_eq v inside 0 c
  guards v hv := by
    have localGuard (i : Fin N) := (f i).guards v
      (show v ∈ Ico (a i).time (b i).time by simpa [assemble, start i, finish i] using hv)
    exact ⟨fun i => (localGuard i).1 0, fun i p => (localGuard i).2 0 p⟩
  raw_support i p origin h := by
    simpa [assemble, start i, finish i] using (f i).raw_support 0 p origin h
  pending_urgent := urgent

private theorem snapshot_eq {a b : Snapshot N} (ht : a.time = b.time)
    (hx : a.x = b.x) (hm : a.main = b.main) (ha : a.aux = b.aux)
    (hr : a.raw = b.raw) (hq : a.pending = b.pending) : a = b := by
  cases a
  cases b
  cases ht
  cases hx
  cases hm
  cases ha
  cases hr
  cases hq
  rfl

private theorem assemble_main (t : ℝ) (a : Fin N → Snapshot 1) (q : List (Delivery N))
    (i : Fin N) (mode : MainMode) :
    assemble t (Function.update a i (setMain (a i) 0 mode)) q =
      setMain (assemble t a q) i mode := by
  refine snapshot_eq rfl ?_ ?_ ?_ ?_ rfl <;> funext j <;>
    by_cases h : j = i <;> simp [assemble, setMain, h]

private theorem assemble_aux (t : ℝ) (a : Fin N → Snapshot 1) (q : List (Delivery N))
    (i : Fin N) (port : Port) (mode : AuxMode) :
    assemble t (Function.update a i (setAux (a i) 0 port mode)) q =
      setAux (assemble t a q) i port mode := by
  refine snapshot_eq rfl ?_ ?_ ?_ ?_ rfl <;> funext j <;>
    by_cases h : j = i <;> simp [assemble, setAux, h]

private theorem assemble_raw (t : ℝ) (a : Fin N → Snapshot 1) (q : List (Delivery N))
    (i : Fin N) (port : Port) (origin : Option ℝ) :
    assemble t (Function.update a i (setRaw (a i) 0 port origin)) q =
      setRaw (assemble t a q) i port origin := by
  refine snapshot_eq rfl ?_ ?_ ?_ ?_ rfl <;> funext j <;>
    by_cases h : j = i <;> simp [assemble, setRaw, h]

theorem cast_jump {route : Router N} {s a b : Snapshot N}
    (j : Jump route s a) (target : a = b) :
    ∃ k : Jump route s b, k.ledger = j.ledger ∧ k.deliveries = j.deliveries := by
  subst b
  exact ⟨j, rfl, rfl⟩

theorem parallelJump {route : Router N} {t : ℝ} {states : Fin N → Snapshot 1}
    (i : Fin N) {v : Snapshot 1} (clock : (states i).time = t)
    (q : List (Delivery N)) (j : Jump (EmptyRouter 1) (states i) v)
    (silentQueue : j.deliveries = []) :
    ∃ k : Jump route (assemble t states q)
      (assemble t (Function.update states i v) (q ++ issuedBy route i j.ledger.emissions)),
      k.ledger.emissions = j.ledger.emissions.map (emissionAt i) ∧
      k.deliveries = [] := by
  cases j with
  | arrive d before after queue due free => simp [Jump.deliveries] at silentQueue
  | fire cell mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.fire (route := route) (assemble t states q) i mode guard
    have target : { setMain (assemble t states q) i .fast with pending := q ++ route i t } =
        assemble t (Function.update states i
          { setMain (states i) 0 .fast with pending := (states i).pending ++ [] })
          (q ++ issuedBy route i (Jump.fire (route := EmptyRouter 1) (states i) 0 mode guard).ledger.emissions) := by
      simp only [List.append_nil, issuedBy, Jump.ledger, List.flatMap_cons, List.flatMap_nil, clock]
      refine snapshot_eq rfl ?_ ?_ ?_ ?_ rfl <;> funext j <;>
        by_cases h : j = i <;> simp [assemble, setMain, h]
    obtain ⟨lifted, ledger, delivered⟩ := cast_jump k target
    exact ⟨lifted, by rw [ledger]; simp [k, Jump.ledger, emissionAt, assemble, clock], delivered⟩
  | fastEnd cell mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.fastEnd (route := route) (assemble t states q) i mode guard
    change ∃ lifted : Jump route (assemble t states q)
        (assemble t (Function.update states i (setMain (states i) 0 .slow)) (q ++ [])),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = []
    obtain ⟨lifted, ledger, delivered⟩ := cast_jump k (assemble_main t states q i _).symm
    rw [List.append_nil]
    exact ⟨lifted, ledger ▸ rfl, delivered⟩
  | reopen cell mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.reopen (route := route) (assemble t states q) i mode guard
    change ∃ lifted : Jump route (assemble t states q)
        (assemble t (Function.update states i (setMain (states i) 0 .ready)) (q ++ [])),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = []
    obtain ⟨lifted, ledger, delivered⟩ := cast_jump k (assemble_main t states q i _).symm
    rw [List.append_nil]
    exact ⟨lifted, ledger ▸ rfl, delivered⟩
  | mark cell port mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.mark (route := route) (assemble t states q) i port mode guard
    change ∃ lifted : Jump route (assemble t states q)
        (assemble t (Function.update states i (setAux (states i) 0 port .mark)) (q ++ [])),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = []
    obtain ⟨lifted, ledger, delivered⟩ := cast_jump k (assemble_aux t states q i port _).symm
    rw [List.append_nil]
    exact ⟨lifted, ledger ▸ rfl, delivered⟩
  | silent cell port mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.silent (route := route) (assemble t states q) i port mode guard
    change ∃ lifted : Jump route (assemble t states q)
        (assemble t (Function.update states i (setAux (states i) 0 port .silent)) (q ++ [])),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = []
    obtain ⟨lifted, ledger, delivered⟩ := cast_jump k (assemble_aux t states q i port _).symm
    rw [List.append_nil]
    exact ⟨lifted, ledger ▸ rfl, delivered⟩
  | error cell port mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.error (route := route) (assemble t states q) i port mode guard
    change ∃ lifted : Jump route (assemble t states q)
        (assemble t (Function.update states i (setAux (states i) 0 port .error)) (q ++ [])),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = []
    obtain ⟨lifted, ledger, delivered⟩ := cast_jump k (assemble_aux t states q i port _).symm
    rw [List.append_nil]
    exact ⟨lifted, ledger ▸ rfl, delivered⟩
  | auxReady cell port mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.auxReady (route := route) (assemble t states q) i port mode guard
    change ∃ lifted : Jump route (assemble t states q)
        (assemble t (Function.update states i (setAux (states i) 0 port .ready)) (q ++ [])),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = []
    obtain ⟨lifted, ledger, delivered⟩ := cast_jump k (assemble_aux t states q i port _).symm
    rw [List.append_nil]
    exact ⟨lifted, ledger ▸ rfl, delivered⟩
  | rawEnd cell port origin active due =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.rawEnd (route := route) (assemble t states q) i port origin active
      (by simpa [assemble, clock] using due)
    change ∃ lifted : Jump route (assemble t states q)
        (assemble t (Function.update states i (setRaw (states i) 0 port none)) (q ++ [])),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = []
    obtain ⟨lifted, ledger, delivered⟩ := cast_jump k (assemble_raw t states q i port _).symm
    rw [List.append_nil]
    exact ⟨lifted, ledger ▸ rfl, delivered⟩


/-- Lift one scheduled local admission, consuming precisely its occurrence in
the global queue and retaining both surrounding sublists. -/
theorem parallel_arrival {route : Router N} {t : ℝ}
    {states : Fin N → Snapshot 1} (i : Fin N) {v : Snapshot 1}
    (clock : (states i).time = t) (q : List (Delivery N))
    (j : Jump (EmptyRouter 1) (states i) v) (receipt : Delivery 1)
    (delivered : j.deliveries = [receipt])
    (before after : List (Delivery N))
    (queue : q = before ++ ⟨i, receipt.port, receipt.due⟩ :: after) :
    ∃ k : Jump route (assemble t states q)
      (assemble t (Function.update states i v) (before ++ after)),
      k.ledger.emissions = [] ∧ k.deliveries = [⟨i, receipt.port, receipt.due⟩] := by
  cases j with
  | arrive d l r _ due free =>
    have same : d = receipt := List.cons.inj delivered |>.1
    subst receipt
    let k := Jump.arrive (route := route) (assemble t states q)
      ⟨i, d.port, d.due⟩ before after queue (due.trans clock)
      (by
        change (states i).raw 0 d.port = none
        have cell : d.cell = 0 := Subsingleton.elim _ _
        simpa only [cell] using free)
    have target : { (setRaw (assemble t states q) i d.port (some t)) with
        pending := before ++ after } = assemble t (Function.update states i
        { (setRaw (states i) d.cell d.port (some (states i).time)) with pending := l ++ r })
        (before ++ after) := by
      have cell : d.cell = 0 := Subsingleton.elim _ _
      refine snapshot_eq ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · funext c; by_cases eq : c = i <;> simp [assemble, setRaw, eq]
      · funext c; by_cases eq : c = i <;> simp [assemble, setRaw, eq]
      · funext c; by_cases eq : c = i <;> simp [assemble, setRaw, eq]
      · funext c
        by_cases eq : c = i <;> simp [assemble, setRaw, eq, cell, clock]
      · rfl
    obtain ⟨lifted, ledger, intake⟩ := cast_jump k target
    exact ⟨lifted, (congrArg Ledger.emissions ledger).trans rfl, intake.trans rfl⟩
  | _ => simp [Jump.deliveries] at delivered

/-- The state and remaining execution of a cell at a product cut. -/
structure Cursor (θ : Parameters) (finish : Snapshot 1) where
  start : Snapshot 1
  run : Execution (fun _ => θ) (EmptyRouter 1) start finish

def startsWithJump {θ : Parameters} {finish : Snapshot 1}
    (c : Cursor θ finish) : Prop :=
  ∃ (v : Snapshot 1) (j : Jump (EmptyRouter 1) c.start v)
    (rest : Execution (fun _ => θ) (EmptyRouter 1) v finish), c.run = .cons (.jump j) rest

/-- The first move when the remaining local execution starts with a flow. -/
structure FlowHead (θ : Parameters) (finish : Snapshot 1) (c : Cursor θ finish) where
  endState : Snapshot 1
  flow : Flow (fun _ => θ) c.start endState
  tail : Execution (fun _ => θ) (EmptyRouter 1) endState finish
  unfoldRun : c.run = .cons (.flow flow) tail

/-- The projection of a global flow traverses the head of a local leg,
either to the end of that head or to an interior cut along its path. -/
inductive FollowsFlow {θ : Parameters} {finish : Snapshot 1}
    {c : Cursor θ finish} (h : FlowHead θ finish c) :
    (next : Cursor θ finish) → (ℝ → Values 1) → Prop where
  | full : FollowsFlow h ⟨h.endState, h.tail⟩ h.flow.path
  | cut {t : ℝ} (after : c.start.time < t) (before : t < h.endState.time) :
      FollowsFlow h ⟨h.flow.at t, .cons (.flow (h.flow.suffix after.le before)) h.tail⟩ h.flow.path

/-- The global execution follows the supplied local legs. A jump advances
one cell and leaves the other cursors intact. A flow advances every cell
along the original path to the next cut. -/
inductive Weaves {θ : Fin N → Parameters} {route : Router N} {b : Fin N → Snapshot 1}
    {T : ℝ} {out : List (Delivery N)} :
    (c : ∀ i, Cursor (θ i) (b i)) → {date : ℝ} → {q : List (Delivery N)} →
      Execution θ route (assemble date (fun i => (c i).start) q) (assemble T b out) → Prop where
  | done : Weaves (fun i => ⟨b i, .nil (b i)⟩) (.nil (assemble T b out))
  | jump {c : ∀ i, Cursor (θ i) (b i)} {date q}
      (i : Fin N) {v : Snapshot 1} (j : Jump (EmptyRouter 1) (c i).start v)
      (rest : Execution (fun _ => θ i) (EmptyRouter 1) v (b i))
      (head : (c i).run = .cons (.jump j) rest)
      {lifted : Jump route (assemble date (fun k => (c k).start) q)
        (assemble date (fun k => (Function.update c i ⟨v, rest⟩ k).start)
          (q ++ issuedBy route i j.ledger.emissions))}
      (fires : lifted.ledger.emissions = j.ledger.emissions.map (emissionAt i))
      {tail} (follow : Weaves (Function.update c i ⟨v, rest⟩) tail) :
      Weaves c (.cons (.jump lifted) tail)
  | flow {c next : ∀ i, Cursor (θ i) (b i)} {date cut q}
      {f : Flow θ (assemble date (fun i => (c i).start) q)
        (assemble cut (fun i => (next i).start) q)}
      (paths : ∀ i, ∃ h : FlowHead (θ i) (b i) (c i),
        FollowsFlow h (next i) (fun t _ => f.path t i))
      {tail} (follow : Weaves next tail) : Weaves c (.cons (.flow f) tail)

theorem cursor_done {θ : Parameters} {finish : Snapshot 1} (c : Cursor θ finish)
    (clock : c.start.time = finish.time) (noJump : ¬ startsWithJump c) :
    c = ⟨finish, .nil finish⟩ := by
  obtain ⟨_, e⟩ := c
  cases e with
  | nil => rfl
  | @cons _ v _ step tail =>
    cases step with
    | jump j => exact (noJump ⟨v, j, tail, rfl⟩).elim
    | flow f =>
      simp only at clock
      exact False.elim (by linarith [f.positive, tail.time_monotone])

theorem cursor_flow {θ : Parameters} {finish : Snapshot 1} (c : Cursor θ finish)
    (clock : c.start.time < finish.time) (noJump : ¬ startsWithJump c) :
    Nonempty (FlowHead θ finish c) := by
  obtain ⟨_, e⟩ := c
  cases e with
  | nil => exact (lt_irrefl _ clock).elim
  | @cons _ v _ step tail =>
    cases step with
    | jump j => exact (noJump ⟨v, j, tail, rfl⟩).elim
    | flow f => exact ⟨⟨v, f, tail, rfl⟩⟩

structure Advance (θ : Parameters) (finish : Snapshot 1) (c : Cursor θ finish) (t : ℝ) where
  next : Cursor θ finish
  clock : next.start.time = t
  flow : Flow (fun _ => θ) c.start next.start
  count : next.run.moveCount ≤ c.run.moveCount
  fires : next.run.ledger.emissions = c.run.ledger.emissions
  arrivals : next.run.deliveries = c.run.deliveries
  marks : ∀ p, flow.ledger.mark 0 p + next.run.ledger.mark 0 p = c.run.ledger.mark 0 p

theorem advance_exists {θ : Parameters} {finish : Snapshot 1} {c : Cursor θ finish}
    (h : FlowHead θ finish c) {t : ℝ} (after : c.start.time < t)
    (before : t ≤ h.endState.time) :
    ∃ a : Advance θ finish c t, FollowsFlow h a.next a.flow.path ∧
      (t = h.endState.time → a.next.run.moveCount < c.run.moveCount) := by
  by_cases atEnd : t = h.endState.time
  · subst t
    have smaller : h.tail.moveCount < c.run.moveCount := by
      rw [h.unfoldRun]
      exact Nat.lt_succ_self _
    refine ⟨⟨⟨h.endState, h.tail⟩, rfl, h.flow, smaller.le, ?_, ?_, ?_⟩,
      .full, fun _ => smaller⟩
    · rw [h.unfoldRun]
      rfl
    · rw [h.unfoldRun]
      rfl
    · intro p
      rw [h.unfoldRun]
      rfl
  · have strict := lt_of_le_of_ne before atEnd
    let leftFlow := h.flow.prefix after before
    let rightFlow := h.flow.suffix after.le strict
    refine ⟨⟨⟨h.flow.at t, .cons (.flow rightFlow) h.tail⟩, rfl, leftFlow, ?_, ?_, ?_, ?_⟩,
      .cut after strict, fun eq => (atEnd eq).elim⟩
    · rw [h.unfoldRun]
      rfl
    · rw [h.unfoldRun]
      rfl
    · rw [h.unfoldRun]
      rfl
    · intro p
      rw [h.unfoldRun]
      have split := intervalIntegral.integral_add_adjacent_intervals
        (leftFlow.mark_integrable 0 p) (rightFlow.mark_integrable 0 p)
      change (∫ v in c.start.time..t, markAct (fun _ => θ) c.start (h.flow.path v) 0 p) +
          (∫ v in t..h.endState.time, markAct (fun _ => θ) c.start (h.flow.path v) 0 p) = _ at split
      change leftFlow.ledger.mark 0 p + (rightFlow.ledger.mark 0 p + h.tail.ledger.mark 0 p) =
        h.flow.ledger.mark 0 p + h.tail.ledger.mark 0 p
      rw [← add_assoc]
      exact congrArg (· + h.tail.ledger.mark 0 p) split

private theorem filter_emissions_cons {N : Nat} (i j : Fin N) (events : List (Fin 1 × ℝ))
    (later : List (Fin N × ℝ)) :
    (((events.map (emissionAt i) ++ later).filter fun e => e.1 = j).map Prod.snd) =
      (if i = j then events.map Prod.snd else []) ++
        ((later.filter fun e => e.1 = j).map Prod.snd) := by
  classical
  by_cases h : i = j
  · simp [List.filter_map, Function.comp_def, emissionAt, h]
  · simp [List.filter_map, Function.comp_def, emissionAt, h]

/-- A finite synchronized product for arbitrary arrival-free local legs on
a shared closed interval. An inactive cell may supply a quiet leg. The
router may issue any list of tokens, due at or after the closing cut. -/
theorem synchronized_execution {θ : Fin N → Parameters} {route : Router N} {t T : ℝ}
    (a b : Fin N → Snapshot 1) (legs : ∀ i, Execution (fun _ => θ i) (EmptyRouter 1) (a i) (b i))
    (start : ∀ i, (a i).time = t) (finish : ∀ i, (b i).time = T) (interval : t ≤ T)
    (noArrival : ∀ i, (legs i).deliveries = []) (queue : List (Delivery N))
    (future : ∀ token ∈ queue, T ≤ token.due)
    (routerFuture : ∀ i e, e ∈ (legs i).ledger.emissions → ∀ token ∈ route i e.2, T ≤ token.due) :
    ∃ (out : List (Delivery N)) (run : Execution θ route (assemble t a queue) (assemble T b out)),
      run.deliveries = [] ∧ out = queue ++ run.ledger.emissions.flatMap (fun e => route e.1 e.2) ∧
      (∀ i, run.emissionTimes i = ((legs i).ledger.emissions.map Prod.snd)) ∧
      (∀ i p, run.ledger.mark i p = (legs i).ledger.mark 0 p) ∧
      Weaves (fun i => ⟨a i, legs i⟩) run := by
  classical
  let cursors : ∀ i, Cursor (θ i) (b i) := fun i => ⟨a i, legs i⟩
  suffices loop : ∀ n (c : ∀ i, Cursor (θ i) (b i)) (date : ℝ) (q : List (Delivery N)),
    (∑ i, (c i).run.moveCount) = n → date ≤ T →
    (∀ i, (c i).start.time = date) → (∀ i, (c i).run.deliveries = []) →
    (∀ d ∈ q, T ≤ d.due) →
    (∀ i e, e ∈ (c i).run.ledger.emissions → ∀ token ∈ route i e.2, T ≤ token.due) →
    ∃ (out : List (Delivery N)) (run : Execution θ route (assemble date (fun i => (c i).start) q) (assemble T b out)),
      run.deliveries = [] ∧ out = q ++ run.ledger.emissions.flatMap (fun e => route e.1 e.2) ∧
      (∀ i, run.emissionTimes i = ((c i).run.ledger.emissions.map Prod.snd)) ∧
      (∀ i p, run.ledger.mark i p = (c i).run.ledger.mark 0 p) ∧ Weaves c run from
    loop _ cursors t queue rfl interval start noArrival future routerFuture
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c date q size dateLe clocks deliveries urgent routing
    let current := fun i => (c i).start
    by_cases jump : ∃ i, startsWithJump (c i)
    · obtain ⟨i, v, j, rest, head⟩ := jump
      have noIntake : j.deliveries = [] ∧ rest.deliveries = [] := by
        have h := deliveries i
        rw [head] at h
        exact List.append_eq_nil_iff.mp h
      let next := Function.update c i ⟨v, rest⟩
      have nextAt : next i = ⟨v, rest⟩ := Function.update_self _ _ _
      have others (k : Fin N) (h : k ≠ i) : next k = c k := Function.update_of_ne h _ _
      have starts : (fun k => (next k).start) = Function.update current i v := by
        funext k
        by_cases h : k = i
        · subst k; simp [nextAt]
        · simp [others k h, current, h]
      let issued := issuedBy route i j.ledger.emissions
      obtain ⟨localLift, localFires, localArrived⟩ :=
        parallelJump (route := route) (states := current) i (clocks i) q j noIntake.1
      obtain ⟨lifted, liftLedger, liftDeliveries⟩ :=
        cast_jump localLift (congrArg (fun states => assemble date states (q ++ issued)) starts.symm)
      have fires := (congrArg Ledger.emissions liftLedger).trans localFires
      have arrived := liftDeliveries.trans localArrived
      have countAt : (next i).run.moveCount = rest.moveCount :=
        congrArg (fun d => d.run.moveCount) nextAt
      have countOther (k : Fin N) (h : k ≠ i) :
          (next k).run.moveCount = (c k).run.moveCount :=
        congrArg (fun d => d.run.moveCount) (others k h)
      have deliveriesAt : (next i).run.deliveries = rest.deliveries :=
        congrArg (fun d => d.run.deliveries) nextAt
      have firesAt : (next i).run.ledger.emissions = rest.ledger.emissions :=
        congrArg (fun d => d.run.ledger.emissions) nextAt
      have firesOther (k : Fin N) (h : k ≠ i) :
          (next k).run.ledger.emissions = (c k).run.ledger.emissions :=
        congrArg (fun d => d.run.ledger.emissions) (others k h)
      have smaller : (∑ k, (next k).run.moveCount) < n := by
        rw [← size]
        apply Finset.sum_lt_sum
        · intro k _
          by_cases h : k = i
          · subst k; rw [countAt, head]; exact Nat.le_succ _
          · exact (countOther k h).le
        · exact ⟨i, Finset.mem_univ _, by rw [countAt, head]; exact Nat.lt_succ_self _⟩
      have nextClock (k : Fin N) : (next k).start.time = date := by
        by_cases h : k = i
        · subst k; simpa [nextAt, j.time_unchanged] using clocks i
        · simpa [others k h] using clocks k
      have nextDelivery (k : Fin N) : (next k).run.deliveries = [] := by
        by_cases h : k = i
        · subst k; exact deliveriesAt.trans noIntake.2
        · exact (congrArg (fun d => d.run.deliveries) (others k h)).trans (deliveries k)
      have issuedFuture (token : Delivery N) (mem : token ∈ q ++ issued) : T ≤ token.due := by
        rcases List.mem_append.mp mem with old | new
        · exact urgent token old
        · obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp new
          apply routing i e _ token ht
          rw [head]
          exact List.mem_append_left _ he
      have nextRoute (k : Fin N) (e : Fin 1 × ℝ) (he : e ∈ (next k).run.ledger.emissions) :
          ∀ token ∈ route k e.2, T ≤ token.due := by
        apply routing k e
        by_cases h : k = i
        · subst k; rw [head]
          exact List.mem_append_right _ (firesAt ▸ he)
        · exact firesOther k h ▸ he
      obtain ⟨out, tail, hd, hq, hf, hm, hw⟩ :=
        ih _ smaller next date (q ++ issued) rfl dateLe nextClock nextDelivery issuedFuture nextRoute
      refine ⟨out, .cons (.jump lifted) tail, ?_, ?_, ?_, ?_, .jump i j rest head fires hw⟩
      · simp [Execution.deliveries, Move.deliveries, arrived, hd]
      · change out = q ++ (lifted.ledger.emissions ++ tail.ledger.emissions).flatMap
          (fun e => route e.1 e.2)
        refine hq.trans ?_
        rw [List.flatMap_append, ← List.append_assoc, fires, List.flatMap_map]
        rfl
      · intro k
        change (((lifted.ledger.emissions ++ tail.ledger.emissions).filter
          fun e => e.1 = k).map Prod.snd) = _
        rw [fires, filter_emissions_cons]
        change _ ++ tail.emissionTimes k = _
        rw [hf k]
        by_cases h : i = k
        · subst k; simp [firesAt, head, Execution.ledger, Move.ledger, Ledger.add]
        · simp [h, firesOther k (Ne.symm h)]
      · intro k port
        change lifted.ledger.mark k port + tail.ledger.mark k port = _
        rw [Jump.mark_zero, zero_add, hm]
        by_cases h : k = i
        · subst k
          have dose := congrArg (fun d => d.run.ledger.mark 0 port) nextAt
          simpa [head, Execution.ledger, Move.ledger, Ledger.add, Jump.mark_zero] using dose
        · exact congrArg (fun d => d.run.ledger.mark 0 port) (others k h)
    · by_cases terminal : date = T
      · have done (i : Fin N) : c i = ⟨b i, .nil (b i)⟩ :=
          cursor_done (c i) ((clocks i).trans (terminal.trans (finish i).symm))
            (fun h => jump ⟨i, h⟩)
        have allDone : c = fun i => ⟨b i, .nil (b i)⟩ := funext done
        subst date
        subst c
        exact ⟨q, .nil _, rfl, by simp [Execution.ledger, Ledger.zero],
          by simp [Execution.emissionTimes, Execution.ledger, Ledger.zero],
          by simp [Execution.ledger, Ledger.zero], .done⟩
      · have beforeEnd : date < T := lt_of_le_of_ne dateLe terminal
        have available (i : Fin N) : Nonempty (FlowHead (θ i) (b i) (c i)) :=
          cursor_flow (c i) (by rw [clocks i, finish i]; exact beforeEnd) (fun h => jump ⟨i, h⟩)
        by_cases cells : Nonempty (Fin N)
        · let _ : Nonempty (Fin N) := cells
          let head (i : Fin N) := Classical.choice (available i)
          obtain ⟨first, earliest⟩ := Finite.exists_min (fun i => (head i).endState.time)
          let cut := (head first).endState.time
          have advance : date < cut := by
            have h := (head first).flow.positive
            rwa [clocks first] at h
          have cutLe : cut ≤ T := by
            have h := (head first).tail.time_monotone
            rwa [finish first] at h
          have steps (i : Fin N) := advance_exists (head i)
            (show (c i).start.time < cut by rw [clocks i]; exact advance) (earliest i)
          let step (i : Fin N) := Classical.choose (steps i)
          let next := fun i => (step i).next
          have smaller : (∑ i, (next i).run.moveCount) < n := by
            rw [← size]
            exact Finset.sum_lt_sum (fun i _ => (step i).count)
              ⟨first, Finset.mem_univ _, (Classical.choose_spec (steps first)).2 rfl⟩
          let flow := parallelFlow clocks (fun i => (step i).clock) advance
            (fun i => (step i).flow) q (fun d hd => cutLe.trans (urgent d hd))
          obtain ⟨out, tail, hd, hq, hf, hm, hw⟩ := ih _ smaller next cut q rfl cutLe
            (fun i => (step i).clock) (fun i => (step i).arrivals.trans (deliveries i))
            urgent (fun i e h => routing i e (by
              change e ∈ (step i).next.run.ledger.emissions at h
              rwa [(step i).fires] at h))
          refine ⟨out, .cons (.flow flow) tail, hd, hq, ?_, ?_, .flow ?_ hw⟩
          · intro i
            change tail.emissionTimes i = _
            rw [hf i, (step i).fires]
          · intro i p
            change flow.ledger.mark i p + tail.ledger.mark i p = _
            rw [hm i]
            have markEq : flow.ledger.mark i p = (step i).flow.ledger.mark 0 p := by
              change (∫ v in date..cut, markAct θ (assemble date current q)
                (fun j => (step j).flow.path v 0) i p) = _
              simp only [Flow.ledger, markAct, assemble, current, clocks i, (step i).clock]
              rfl
            rw [markEq]
            exact (step i).marks p
          · intro i
            refine ⟨head i, ?_⟩
            have same : (fun v (_ : Fin 1) => flow.path v i) = (step i).flow.path :=
              funext fun v => funext fun k =>
                congrArg ((step i).flow.path v) (Subsingleton.elim 0 k)
            rw [same]
            exact (Classical.choose_spec (steps i)).1
        · have empty (i : Fin N) : False := cells ⟨i⟩
          let allFlows (i : Fin N) : Flow (fun _ => θ i) (c i).start (b i) := (empty i).elim
          let flow := parallelFlow clocks finish beforeEnd allFlows q urgent
          let run : Execution θ route _ _ := .cons (.flow flow) (.nil _)
          exact ⟨q, run, rfl, by simp [run, Execution.ledger, Move.ledger, Flow.ledger, Ledger.add,
            Ledger.zero], fun i => (empty i).elim, fun i => (empty i).elim,
            .flow (fun i => (empty i).elim) .done⟩


private theorem issued_count {θ : Fin N → Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) :
    run.ledger.issued = (run.ledger.emissions.flatMap (fun e => route e.1 e.2)).length := by
  induction run with
  | nil => rfl
  | cons step tail ih =>
    have head : step.ledger.issued =
        (step.ledger.emissions.flatMap (fun e => route e.1 e.2)).length := by
      cases step with
      | flow => rfl
      | jump j => cases j <;> simp [Move.ledger, Jump.ledger, Ledger.zero]
    simpa only [Execution.ledger, Ledger.add, List.flatMap_append, List.length_append] using
      congrArg₂ (· + ·) head ih

private theorem delivered_count {θ : Fin N → Parameters} {route : Router N}
    {s u : Snapshot N} (run : Execution θ route s u) :
    run.ledger.delivered = run.deliveries.length := by
  induction run with
  | nil => rfl
  | cons step tail ih =>
    have head : step.ledger.delivered = step.deliveries.length := by
      cases step with
      | flow => rfl
      | jump j => cases j <;> rfl
    exact (congrArg₂ (· + ·) head ih).trans List.length_append.symm

/-- The same synchronization exposes every physical ledger coordinate.
FIREs retain the exact ordered word within each cell and the native queue
retains the exact order in which this execution issues routed children. -/
theorem synchronized_ledger {θ : Fin N → Parameters} {route : Router N} {t T : ℝ}
    (a b : Fin N → Snapshot 1) (legs : ∀ i, Execution (fun _ => θ i) (EmptyRouter 1) (a i) (b i))
    (start : ∀ i, (a i).time = t) (finish : ∀ i, (b i).time = T) (interval : t ≤ T)
    (noArrival : ∀ i, (legs i).deliveries = []) (queue : List (Delivery N))
    (future : ∀ token ∈ queue, T ≤ token.due)
    (routerFuture : ∀ i e, e ∈ (legs i).ledger.emissions → ∀ token ∈ route i e.2, T ≤ token.due) :
    ∃ (out : List (Delivery N)) (run : Execution θ route (assemble t a queue) (assemble T b out)),
      run.deliveries = [] ∧ out = queue ++ run.ledger.emissions.flatMap (fun e => route e.1 e.2) ∧
      (∀ i, run.emissionTimes i = (legs i).ledger.emissions.map Prod.snd) ∧
      run.ledger.issued = (run.ledger.emissions.flatMap (fun e => route e.1 e.2)).length ∧
      run.ledger.delivered = 0 ∧
      (∀ i port, run.ledger.error i port = (legs i).ledger.error 0 port ∧
        run.ledger.mark i port = (legs i).ledger.mark 0 port) ∧
      (∀ i, run.ledger.recovery i = (legs i).ledger.recovery 0) ∧
      Weaves (fun i => ⟨a i, legs i⟩) run := by
  obtain ⟨out, run, arrivals, pending, fires, marks, follows⟩ :=
    synchronized_execution (route := route) a b legs start finish interval noArrival queue future routerFuture
  refine ⟨out, run, arrivals, pending, fires, issued_count run,
    by rw [delivered_count, arrivals]; rfl, ?_, ?_, follows⟩
  · intro i port
    have product := run.gain_balance i port
    have localBalance := (legs i).gain_balance 0 port
    change (b i).x 0 (.z port) = (a i).x 0 (.z port) + run.ledger.error i port at product
    exact ⟨by linarith, marks i port⟩
  · intro i
    have product := run.recovery_balance i
    have localBalance := (legs i).recovery_balance 0
    change (b i).x 0 .b = (a i).x 0 .b + run.ledger.recovery i at product
    linarith

/-- A weak training wave immediately after the same-date RAW admissions.
Other pending work can have arbitrary destinations beyond the closing cut. -/
theorem weak_training_wave {θ : Fin N → Parameters} {route : Router N} {ε : ℝ}
    (box : PhysicalBox θ ε) (s : Snapshot N) (port : Fin N → Port)
    (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (ready : ∀ i, ReadyCoordinates s i)
    (active : ∀ i, s.raw i (port i) = some s.time)
    (inactive : ∀ i p, p ≠ port i → s.raw i p = none)
    (weak : ∀ i, Real.exp (s.x i (.z (port i))) ≤ 7 / 6)
    (headroom : ∀ i, s.x i (.z (port i)) ≤ Real.log (6 / 5) + 1 / 1000)
    (later : ∀ token ∈ s.pending, s.time + 15 / 2 < token.due) :
    ∃ (u : Snapshot N) (run : Execution θ route s u),
      CompleteThrough run (s.time + 15 / 2) ∧ u.pending = s.pending ∧
      run.deliveries = [] ∧ run.ledger.emissions = [] ∧
      (∀ i, ReadyCoordinates u i ∧ (∀ p, u.raw i p = none) ∧
        run.ledger.recovery i = 0 ∧
        ∀ p, run.ledger.mark i p = 0 ∧
          run.ledger.error i p = if p = port i then 3 / 5 else 0) := by
  classical
  have localLeg (i : Fin N) :
      Nonempty (WeakInputCycle (fun _ => θ i) (EmptyRouter 1) (localView s i) 0 (port i)) := by
    refine weak_input_cycle_exists (localView s i) ⟨box.1, fun _ p => box.2 i p⟩
      ?_ ?_ 0 (port i) ?_ (weak i) (headroom i) (active i) ?_ ?_
    · exact ⟨fun _ => physical.region i, fun _ p => physical.gain_cap i p,
        fun _ => physical.recovery_cap i, fun _ => physical.reserve i⟩
    · intro _ p origin h
      exact valid i p origin h
    · intro j
      have eq : j = 0 := Subsingleton.elim _ _
      subst j
      exact ⟨(ready i).ready, (ready i).charge, (ready i).auxiliary⟩
    · intro j p h
      exact inactive i p (h.resolve_left (fun ne => ne (Subsingleton.elim j 0)))
    · simp [localView]
  let leg (i : Fin N) := Classical.choice (localLeg i)
  let T := s.time + 15 / 2
  obtain ⟨out, run, arrivals, pending, fires, _, _, doses, recovery, _⟩ :=
    synchronized_ledger (route := route) (localView s) (fun i => (leg i).final)
      (fun i => (leg i).execution) (fun _ => rfl) (fun i => (leg i).date)
      (by linarith) (fun i => (leg i).deliveries) s.pending
      (fun token mem => (later token mem).le)
      (fun i e mem => by rw [(leg i).emissions] at mem; cases mem)
  have noFire : run.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event mem
    have em := fires event.1
    rw [(leg event.1).emissions] at em
    have selected : event ∈ run.ledger.emissions.filter (fun e => e.1 = event.1) :=
      List.mem_filter.mpr ⟨mem, by simp⟩
    have date := List.mem_map_of_mem selected (f := Prod.snd)
    change event.2 ∈ run.emissionTimes event.1 at date
    rw [em] at date
    exact List.not_mem_nil date
  let u := assemble T (fun i => (leg i).final) out
  have hstart : assemble s.time (localView s) s.pending = s := by
    cases s
    rfl
  have pendingExact : u.pending = s.pending := by
    change out = s.pending
    simpa [noFire] using pending
  have settled (i : Fin N) : ReadyCoordinates u i :=
    ⟨(leg i).pulse.coordinates.ready, (leg i).pulse.coordinates.charge,
      (leg i).pulse.coordinates.auxiliary⟩
  have raw (i : Fin N) (p : Port) : u.raw i p = none := (leg i).pulse.raw_finished p
  have guards : BeforeGuards u u.x := by
    constructor
    · intro i
      rw [(settled i).ready]
      have h := (settled i).charge.2
      linarith
    · intro i p
      obtain ⟨mode, band⟩ := (settled i).auxiliary p
      rw [mode]
      linarith [band.2]
  have quiet : ∀ v, IsEmpty (Jump route u v) := guards.no_jump
    (fun i p origin h => by rw [raw i p] at h; cases h)
    (fun token mem => later token (pendingExact ▸ mem))
  let answer := run.cast_source hstart.symm
  have ledger : answer.ledger = run.ledger := run.cast_source_ledger hstart.symm
  refine ⟨u, answer, ⟨rfl, quiet, fun token mem => later token (pendingExact ▸ mem)⟩,
    pendingExact, (run.cast_source_deliveries hstart.symm).trans arrivals, ?_, ?_⟩
  · rw [ledger, noFire]
  · intro i
    refine ⟨settled i, raw i, ?_, ?_⟩
    · rw [ledger, recovery i]
      have balance := (leg i).execution.recovery_balance 0
      rw [(leg i).pulse.recovery_preserved] at balance
      linarith
    · intro p
      rw [ledger]
      refine ⟨(doses i p).2.trans ((leg i).pulse.mark_zero p), ?_⟩
      rw [(doses i p).1]
      by_cases selected : p = port i
      · subst p
        simpa using (leg i).pulse.error_dose
      · simpa [selected] using (leg i).pulse.error_other p selected


def waveTokens (t : ℝ) (port : Fin N → Port) (cells : List (Fin N)) :
    List (Delivery N) := cells.map fun i => ⟨i, port i, t⟩

def admittedWave (s : Snapshot N) (port : Fin N → Port) (cells : List (Fin N))
    (later : List (Delivery N)) : Snapshot N :=
  { s with
    pending := later
    raw := fun i p => if i ∈ cells ∧ p = port i then some s.time else s.raw i p }

theorem admit_wave {θ : Fin N → Parameters} {route : Router N} (s : Snapshot N)
    (port : Fin N → Port) (cells : List (Fin N)) (unique : cells.Nodup)
    (later : List (Delivery N)) (queue : s.pending = waveTokens s.time port cells ++ later)
    (free : ∀ i ∈ cells, s.raw i (port i) = none) :
    ∃ run : Execution θ route s (admittedWave s port cells later),
      run.deliveries = waveTokens s.time port cells ∧ run.ledger.emissions = [] := by
  induction cells generalizing s with
  | nil =>
    have same : admittedWave s port [] later = s := by
      apply snapshot_eq
      · rfl
      · rfl
      · rfl
      · rfl
      · simp [admittedWave]
      · exact queue.symm
    rw [same]
    exact ⟨.nil s, rfl, rfl⟩
  | cons i cells ih =>
    obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
    let token : Delivery N := ⟨i, port i, s.time⟩
    let next := { setRaw s i (port i) (some s.time) with
      pending := waveTokens s.time port cells ++ later }
    let jump : Jump route s next :=
      .arrive s token [] (waveTokens s.time port cells ++ later) queue rfl (free i (by simp))
    have stillFree (j : Fin N) (mem : j ∈ cells) : next.raw j (port j) = none := by
      have ne : j ≠ i := fun same => fresh (same ▸ mem)
      simpa [next, setRaw, ne] using free j (List.mem_cons_of_mem i mem)
    obtain ⟨tail, delivered, fires⟩ := ih next tailUnique rfl stillFree
    have finish : admittedWave s port (i :: cells) later = admittedWave next port cells later := by
      refine snapshot_eq rfl rfl rfl rfl ?_ rfl
      funext j p
      by_cases eq : j = i
      · subst j; by_cases same : p = port i <;> simp [admittedWave, next, setRaw, fresh, same]
      · simp [admittedWave, next, setRaw, eq]
    rw [finish]
    refine ⟨.cons (.jump jump) tail, ?_, fires⟩
    change [token] ++ tail.deliveries = _
    rw [delivered]
    rfl

/-- Consume one actual token on every cell at the common wave date, then
settle the overlapping weak legs while retaining the exact later queue. -/
theorem weak_training_transaction {θ : Fin N → Parameters} {route : Router N} {ε : ℝ}
    (box : PhysicalBox θ ε) (s : Snapshot N) (port : Fin N → Port)
    (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (ready : ∀ i, ReadyCoordinates s i) (raw : ∀ i p, s.raw i p = none)
    (weak : ∀ i, Real.exp (s.x i (.z (port i))) ≤ 7 / 6)
    (headroom : ∀ i, s.x i (.z (port i)) ≤ Real.log (6 / 5) + 1 / 1000)
    (later : List (Delivery N))
    (queue : s.pending = (List.finRange N).map (fun i => ⟨i, port i, s.time⟩) ++ later)
    (future : ∀ token ∈ later, s.time + 15 / 2 < token.due) :
    ∃ (u : Snapshot N) (run : Execution θ route s u),
      CompleteThrough run (s.time + 15 / 2) ∧ u.pending = later ∧
      run.deliveries = (List.finRange N).map (fun i => ⟨i, port i, s.time⟩) ∧
      run.ledger.emissions = [] ∧
      (∀ i, ReadyCoordinates u i ∧ (∀ p, u.raw i p = none) ∧
        run.ledger.recovery i = 0 ∧
        ∀ p, run.ledger.mark i p = 0 ∧
          run.ledger.error i p = if p = port i then 3 / 5 else 0) := by
  obtain ⟨intake, delivered, noFire⟩ := admit_wave (θ := θ) (route := route) s port
    (List.finRange N) (List.nodup_finRange N) later queue (fun i _ => raw i (port i))
  let a := admittedWave s port (List.finRange N) later
  obtain ⟨u, body, complete, pending, noArrivals, noEmissions, doses⟩ :=
    weak_training_wave (route := route) box a port (intake.physical_invariant box physical)
      (intake.raw_valid valid)
      (fun i => ⟨(ready i).ready, (ready i).charge, (ready i).auxiliary⟩)
      (fun i => by simp [a, admittedWave])
      (fun i p ne => by simp [a, admittedWave, ne, raw])
      weak headroom future
  let run := intake.append body
  refine ⟨u, run, complete, pending, ?_, ?_, ?_⟩
  · rw [Execution.deliveries_append, noArrivals, List.append_nil, delivered]
    rfl
  · rw [Execution.emissions_append, noFire, noEmissions]
    rfl
  · intro i
    obtain ⟨rest, inactive, recovery, marks⟩ := doses i
    refine ⟨rest, inactive, ?_, fun p => ⟨?_, ?_⟩⟩
    · have total := run.recovery_balance i
      have leg := body.recovery_balance i
      change u.x i .b = s.x i .b + body.ledger.recovery i at leg
      rw [recovery] at leg
      linarith
    · rw [Execution.mark_append, (marks p).1, add_zero]
      -- The intake contains only arrivals, which contribute no MARK.
      have zero {v w : Snapshot N} (e : Execution θ route v w) (short : v.time = w.time) :
          e.ledger.mark i p = 0 := by
        induction e with
        | nil => rfl
        | cons step rest ih =>
          cases step with
          | flow f => exact False.elim (by linarith [f.positive, rest.time_monotone])
          | jump j =>
            change j.ledger.mark i p + rest.ledger.mark i p = 0
            rw [j.mark_zero, ih (j.time_unchanged.trans short), zero_add]
      exact zero intake rfl
    · have total := run.gain_balance i p
      have leg := body.gain_balance i p
      change u.x i (.z p) = s.x i (.z p) + body.ledger.error i p at leg
      rw [(marks p).2] at leg
      linarith

end NetworkStability.NativeMultiToken
