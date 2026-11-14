import KernelR.HybridShortLearnedCycle
import KernelR.HybridQuietSourceArrival
import KernelR.HybridQuietExecutionProduct

namespace NetworkStability.NativeStrong

open KernelR.Hybrid

abbrev EmptyRouter (N : Nat) : Router N := fun _ _ => []

/-- The isolated construction begins just after intake, with the delivered
pulse active and the local queue empty. Its recovery and gain ledger is zero. -/
structure LocalLeg (θ : Fin 1 → Parameters) (s : Snapshot 1) (port : Port) where
  cycle : ShortLearnedCycle θ s port
  final : Snapshot 1
  execution : Execution θ (EmptyRouter 1) s final
  date : final.time = s.time + 15 / 2
  ready : PreparedSection final 0
  raw : ∀ q, final.raw 0 q = none
  pending : final.pending = []
  gains : ∀ q, final.x 0 (.z q) = s.x 0 (.z q)
  recovery : final.x 0 .b = s.x 0 .b
  charge : final.x 0 .q = 1 / 10
  emissions : execution.ledger.emissions = [(0, cycle.fire.final.time)]
  deliveries : execution.deliveries = []

theorem local_leg_exists {θ ε} (box : PhysicalBox θ ε) (s : Snapshot 1) (port : Port)
    (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (prepared : PreparedSection s 0)
    (gain : 9 / 5 ≤ Real.exp (s.x 0 (.z port)) ∧ Real.exp (s.x 0 (.z port)) ≤ 2)
    (active : s.raw 0 port = some s.time) (other : ∀ q, q ≠ port → s.raw 0 q = none)
    (empty : s.pending = []) : Nonempty (LocalLeg θ s port) := by
  obtain ⟨cycle⟩ := short_learned_cycle_exists box s port physical valid prepared
    ⟨gain.1, by linarith [gain.2]⟩ active other
    (by intro token seen; simp [empty] at seen)
  let T := s.time + 15 / 2
  have later : cycle.returned.final.time < T := by
    rw [cycle.date]
    dsimp [T]
    linarith
  let flow : Flow θ cycle.returned.final (quietAt cycle.returned.final T) := quietFlow cycle.returned.final later
    (fun i => (cycle.ready i).ready) (fun i q => ((cycle.ready i).auxiliary q).1) cycle.raw_none
    (fun i => by have h := (cycle.ready i).charge.2; linarith)
    (fun i q => by have h := ((cycle.ready i).auxiliary q).2.2; linarith)
    (by intro token seen; change token ∈ cycle.returned.final.pending at seen
        simp [cycle.pending, empty] at seen)
  let idle : Execution θ (EmptyRouter 1) cycle.returned.final (quietAt cycle.returned.final T) :=
    .cons (.flow flow) (.nil _)
  have idleReady := quietAt_ready_coordinates cycle.returned.final 0 (cycle.ready 0) later.le
  refine ⟨{
    cycle := cycle
    final := quietAt cycle.returned.final T
    execution := cycle.execution.append idle
    date := rfl
    ready := ⟨idleReady.ready, idleReady.charge, (cycle.prepared 0).recovery, idleReady.auxiliary⟩
    raw := cycle.raw_none 0
    pending := cycle.pending.trans empty
    gains := cycle.gains 0
    recovery := cycle.recovery 0
    charge := ?_
    emissions := ?_
    deliveries := ?_
  }⟩
  · change relax (1 / 2) (1 / 10) (cycle.returned.final.x 0 .q) cycle.returned.final.time T = _
    rw [cycle.charge]
    simp [relax]
  · rw [Execution.emissions_append, cycle.emissions]
    rfl
  · rw [Execution.deliveries_append, cycle.deliveries]
    rfl

/-- A cell's local analysis state with no queued source. The operational
queue is held separately and is changed only by native jumps. -/
noncomputable def localView (s : Snapshot N) (i : Fin N) : Snapshot 1 :=
  ⟨s.time, fun _ => s.x i, fun _ => s.main i, fun _ => s.aux i, fun _ => s.raw i, []⟩

/-- The selected cell follows the local leg. Other cells follow the
source-free equations on this interval, with their own initial coordinates. -/
noncomputable def splice (s : Snapshot N) (i : Fin N) (a : Snapshot 1)
    (queue : List (Delivery N)) : Snapshot N where
  time := a.time
  x := Function.update (quietValues s a.time) i (a.x 0)
  main := Function.update s.main i (a.main 0)
  aux := Function.update s.aux i (a.aux 0)
  raw := Function.update s.raw i (a.raw 0)
  pending := queue

private theorem splice_start (s : Snapshot N) (i : Fin N) :
    splice s i (localView s i) s.pending = s := by
  have h := quietValues_initial s
  cases s
  simp [splice, localView, h]

/-- These conditions concern only the spectators during this one leg.
They can have different gains, energy and charge, and later queued work. -/
structure Spectators (s : Snapshot N) (i : Fin N) : Prop where
  ready : ∀ j, j ≠ i → ReadyCoordinates s j
  raw : ∀ j, j ≠ i → ∀ p, s.raw j p = none

private theorem splice_field_selected (s : Snapshot N) (i : Fin N) (a : Snapshot 1)
    (q : List (Delivery N)) (θ : Fin N → Parameters) (x : Values N) (y : Values 1)
    (same : x i = y 0) (t : ℝ) (c : Coord) :
    field θ (splice s i a q) x t i c = field (fun _ => θ i) a y t 0 c := by
  have hx : ∀ c, x i c = y 0 c := congrFun same
  cases c <;>
    simp [field, work, drive, current, errorAct, markAct, splice, hx, auxDrain]

private theorem splice_field_other (s : Snapshot N) (i j : Fin N) (different : j ≠ i)
    (a : Snapshot 1) (q : List (Delivery N)) (θ : Fin N → Parameters) (x y : Values N)
    (same : x j = y j) (t : ℝ) (c : Coord) :
    field θ (splice s i a q) x t j c = field θ s y t j c := by
  have hx : ∀ c, x j c = y j c := congrFun same
  cases c <;>
    simp [field, work, drive, current, errorAct, markAct, splice, hx, auxDrain, different]

open Set MeasureTheory in
/-- Synchronize each local positive flow with the spectator flows over the
same time interval. The supplied queue is the operational queue. -/
noncomputable def spliceFlow {θ : Fin N → Parameters} {a b : Snapshot 1}
    (s : Snapshot N) (i : Fin N) (spectators : Spectators s i)
    (f : Flow (fun _ => θ i) a b) (started : s.time ≤ a.time)
    (q : List (Delivery N)) (urgent : ∀ token ∈ q, b.time ≤ token.due) :
    Flow θ (splice s i a q) (splice s i b q) := by
  let dummy : Snapshot N :=
    { s with
      main := Function.update s.main i .ready
      aux := Function.update s.aux i (fun _ => .ready)
      raw := Function.update s.raw i (fun _ => none)
      x := Function.update s.x i (fun _ => 0)
      pending := [] }
  have quietMode : ∀ j, dummy.main j = .ready := by
    intro j
    by_cases h : j = i
    · subst j; simp [dummy]
    · simpa [dummy, h] using (spectators.ready j h).ready
  have quietAux : ∀ j p, dummy.aux j p = .ready := by
    intro j p
    by_cases h : j = i
    · subst j; simp [dummy]
    · simpa [dummy, h] using ((spectators.ready j h).auxiliary p).1
  have quietRaw : ∀ j p, dummy.raw j p = none := by
    intro j p
    by_cases h : j = i
    · subst j; simp [dummy]
    · simpa [dummy, h] using spectators.raw j h p
  have quietBounds (j : Fin N) (hj : j ≠ i) :
      ReadyCoordinates (quietAt dummy a.time) j := by
    apply quietAt_ready_coordinates dummy j _ started
    have h := spectators.ready j hj
    exact ⟨by simpa [dummy, hj] using h.ready,
      by simpa [dummy, hj] using h.charge,
      fun p => by simpa [dummy, hj] using h.auxiliary p⟩
  have qBound (j : Fin N) : (quietAt dummy a.time).x j .q < 1 := by
    by_cases h : j = i
    · subst j
      exact relax_lt (by norm_num) started (by simp [dummy]) (by norm_num)
    · have hq := (quietBounds j h).charge.2
      linarith
  have auxBound (j : Fin N) (p : Port) : (quietAt dummy a.time).x j (.m p) < 1 := by
    by_cases h : j = i
    · subst j
      exact relax_lt (by norm_num) started (by simp [dummy]) (by norm_num)
    · have hm := ((quietBounds j h).auxiliary p).2.2
      linarith
  let quiet : Flow θ (quietAt dummy a.time) (quietAt dummy b.time) :=
    (quietAt_quietAt dummy a.time b.time) ▸
      quietFlow (quietAt dummy a.time) f.positive quietMode quietAux quietRaw qBound auxBound
        (by simp [quietAt, dummy])
  let path : ℝ → Values N := fun t => Function.update (quiet.path t) i (f.path t 0)
  have selected (t : ℝ) : path t i = f.path t 0 := by simp [path]
  have other (t : ℝ) (j : Fin N) (h : j ≠ i) : path t j = quiet.path t j := by simp [path, h]
  have sameValues (t : ℝ) (j : Fin N) (h : j ≠ i) :
      quietValues s t j = quietValues dummy t j := by
    funext c
    cases c <;> simp [quietValues, dummy, h]
  have otherField (t : ℝ) (j : Fin N) (h : j ≠ i) (c : Coord) :
      field θ (splice s i a q) (path t) t j c =
        field θ (quietAt dummy a.time) (quiet.path t) t j c := by
    rw [splice_field_other s i j h a q θ _ _ (other t j h)]
    cases c <;>
      simp [field, work, drive, current, errorAct, markAct, quietAt, dummy, h]
  have selectedField (t : ℝ) (c : Coord) :
      field θ (splice s i a q) (path t) t i c =
        field (fun _ => θ i) a (f.path t) t 0 c :=
    splice_field_selected s i a q θ _ _ (selected t) t c
  refine {
    positive := f.positive
    path := path
    initial := ?_
    final := ?_
    main_fixed := by simp [splice, f.main_fixed]
    aux_fixed := by simp [splice, f.aux_fixed]
    raw_fixed := by simp [splice, f.raw_fixed]
    queue_fixed := rfl
    continuous := ?_
    integrable := ?_
    mark_integrable := ?_
    integral_eq := ?_
    guards := ?_
    raw_support := ?_
    pending_urgent := urgent
  }
  · funext j c
    by_cases h : j = i
    · subst j; simpa [splice, path] using congrFun (congrFun f.initial 0) c
    · simpa [splice, path, h, quietAt, sameValues _ _ h] using congrFun (congrFun quiet.initial j) c
  · funext j c
    by_cases h : j = i
    · subst j; simpa [splice, path] using congrFun (congrFun f.final 0) c
    · simpa [splice, path, h, quietAt, sameValues _ _ h] using congrFun (congrFun quiet.final j) c
  · intro j c
    change ContinuousOn (fun t => path t j c) (Icc a.time b.time)
    by_cases h : j = i
    · subst j; simpa only [selected] using f.continuous 0 c
    · simpa only [other _ j h, quietAt] using quiet.continuous j c
  · intro j c
    change IntervalIntegrable (fun t => field θ (splice s i a q) (path t) t j c) volume a.time b.time
    by_cases h : j = i
    · subst j; simpa only [selectedField] using f.integrable 0 c
    · simpa only [otherField _ j h c, quietAt] using quiet.integrable j c
  · intro j p
    by_cases h : j = i
    · subst j; simpa [markAct, splice, path] using f.mark_integrable 0 p
    · simpa [markAct, splice, path, h, quietAt, dummy] using quiet.mark_integrable j p
  · intro t ht j c
    change path t j c = (splice s i a q).x j c +
      ∫ v in a.time..t, field θ (splice s i a q) (path v) v j c
    by_cases h : j = i
    · subst j
      rw [selected]
      rw [funext (fun v => selectedField v c)]
      simpa only [splice, Function.update_self] using f.integral_eq t ht 0 c
    · rw [other _ j h]
      rw [funext (fun v => otherField v j h c)]
      have values := congrFun (sameValues a.time j h) c
      simpa [splice, h, quietAt, values] using quiet.integral_eq t ht j c
  · intro j p origin active
    by_cases h : j = i
    · subst j
      exact f.raw_support 0 p origin (by simpa [splice] using active)
    · simp [splice, h, spectators.raw j h p] at active
  · intro t ht
    constructor
    · intro j
      by_cases h : j = i
      · subst j; simpa [splice, path] using (f.guards t ht).1 0
      · simpa [splice, path, h, quietAt, dummy] using (quiet.guards t ht).1 j
    · intro j p
      by_cases h : j = i
      · subst j; simpa [splice, path] using (f.guards t ht).2 0 p
      · simpa [splice, path, h, quietAt, dummy] using (quiet.guards t ht).2 j p

@[simp] private theorem splice_main (s : Snapshot N) (i : Fin N) (a : Snapshot 1)
    (q : List (Delivery N)) (mode : MainMode) :
    splice s i (setMain a 0 mode) q = setMain (splice s i a q) i mode := by
  simp [splice, setMain, Function.update_idem]

@[simp] private theorem splice_aux (s : Snapshot N) (i : Fin N) (a : Snapshot 1)
    (q : List (Delivery N)) (p : Port) (mode : AuxMode) :
    splice s i (setAux a 0 p mode) q = setAux (splice s i a q) i p mode := by
  simp [splice, setAux, Function.update_idem]

@[simp] private theorem splice_raw (s : Snapshot N) (i : Fin N) (a : Snapshot 1)
    (q : List (Delivery N)) (p : Port) (origin : Option ℝ) :
    splice s i (setRaw a 0 p origin) q = setRaw (splice s i a q) i p origin := by
  simp [splice, setRaw, Function.update_idem]

def emissionAt (i : Fin N) (e : Fin 1 × ℝ) : Fin N × ℝ := (i, e.2)

def issuedBy (route : Router N) (i : Fin N) (events : List (Fin 1 × ℝ)) :
    List (Delivery N) :=
  events.flatMap (fun e => route i e.2)

private theorem castJumpTarget {route : Router N} {s u v : Snapshot N}
    (j : Jump route s u) (eq : u = v) :
    ∃ k : Jump route s v, k.ledger = j.ledger ∧ k.deliveries = j.deliveries := by
  subst v
  exact ⟨j, rfl, rfl⟩

/-- Transport a local leg without arrivals. At FIRE the native queue receives
exactly the actual router's output. All other jumps retain the current queue. -/
private theorem splice_jump {route : Router N} {a b : Snapshot 1}
    (s : Snapshot N) (i : Fin N) (q : List (Delivery N))
    (j : Jump (EmptyRouter 1) a b) (noArrival : j.deliveries = []) :
    ∃ k : Jump route (splice s i a q)
      (splice s i b (q ++ issuedBy route i j.ledger.emissions)),
      k.ledger.emissions = j.ledger.emissions.map (emissionAt i) ∧ k.deliveries = [] := by
  cases j with
  | arrive token before after queue due free => simp [Jump.deliveries] at noArrival
  | fire cell mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.fire (route := route) (splice s i a q) i
      (by simpa [splice] using mode) (by simpa [splice] using guard)
    have same :
        splice s i
          { setMain a 0 .fast with pending := a.pending ++ EmptyRouter 1 0 a.time }
          (q ++ issuedBy route i (Jump.fire (route := EmptyRouter 1) a 0 mode guard).ledger.emissions) =
        { setMain (splice s i a q) i .fast with pending := q ++ route i a.time } := by
      simp [splice, setMain, Function.update_idem, issuedBy, Jump.ledger]
    obtain ⟨lifted, ledger, deliveries⟩ := castJumpTarget k same.symm
    exact ⟨lifted, ledger ▸ rfl, deliveries⟩
  | fastEnd cell mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.fastEnd (route := route) (splice s i a q) i (by simpa [splice] using mode) (by simpa [splice] using guard)
    have target : (setMain (splice s i a q) i .slow) = splice s i (setMain a 0 .slow)
        (q ++ issuedBy route i (Jump.fastEnd (route := EmptyRouter 1) a 0 mode guard).ledger.emissions) := by
      simp [splice_main, issuedBy, Jump.ledger, Ledger.zero]
    obtain ⟨lifted, ledger, delivered⟩ := castJumpTarget k target
    refine ⟨lifted, ?_, ?_⟩
    · rw [ledger]
      rfl
    · rw [delivered]
      rfl
  | reopen cell mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.reopen (route := route) (splice s i a q) i (by simpa [splice] using mode) (by simpa [splice] using guard)
    have target : (setMain (splice s i a q) i .ready) = splice s i (setMain a 0 .ready)
        (q ++ issuedBy route i (Jump.reopen (route := EmptyRouter 1) a 0 mode guard).ledger.emissions) := by
      simp [splice_main, issuedBy, Jump.ledger, Ledger.zero]
    obtain ⟨lifted, ledger, delivered⟩ := castJumpTarget k target
    refine ⟨lifted, ?_, ?_⟩
    · rw [ledger]
      rfl
    · rw [delivered]
      rfl
  | mark cell port mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.mark (route := route) (splice s i a q) i port (by simpa [splice] using mode) (by simpa [splice] using guard)
    have target : (setAux (splice s i a q) i port .mark) = splice s i (setAux a 0 port .mark)
        (q ++ issuedBy route i (Jump.mark (route := EmptyRouter 1) a 0 port mode guard).ledger.emissions) := by
      simp [splice_aux, issuedBy, Jump.ledger, Ledger.zero]
    obtain ⟨lifted, ledger, delivered⟩ := castJumpTarget k target
    refine ⟨lifted, ?_, ?_⟩
    · rw [ledger]
      rfl
    · rw [delivered]
      rfl
  | silent cell port mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.silent (route := route) (splice s i a q) i port (by simpa [splice] using mode) (by simpa [splice] using guard)
    have target : (setAux (splice s i a q) i port .silent) = splice s i (setAux a 0 port .silent)
        (q ++ issuedBy route i (Jump.silent (route := EmptyRouter 1) a 0 port mode guard).ledger.emissions) := by
      simp [splice_aux, issuedBy, Jump.ledger, Ledger.zero]
    obtain ⟨lifted, ledger, delivered⟩ := castJumpTarget k target
    refine ⟨lifted, ?_, ?_⟩
    · rw [ledger]
      rfl
    · rw [delivered]
      rfl
  | error cell port mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.error (route := route) (splice s i a q) i port (by simpa [splice] using mode) (by simpa [splice] using guard)
    have target : (setAux (splice s i a q) i port .error) = splice s i (setAux a 0 port .error)
        (q ++ issuedBy route i (Jump.error (route := EmptyRouter 1) a 0 port mode guard).ledger.emissions) := by
      simp [splice_aux, issuedBy, Jump.ledger, Ledger.zero]
    obtain ⟨lifted, ledger, delivered⟩ := castJumpTarget k target
    refine ⟨lifted, ?_, ?_⟩
    · rw [ledger]
      rfl
    · rw [delivered]
      rfl
  | auxReady cell port mode guard =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.auxReady (route := route) (splice s i a q) i port (by simpa [splice] using mode) (by simpa [splice] using guard)
    have target : (setAux (splice s i a q) i port .ready) = splice s i (setAux a 0 port .ready)
        (q ++ issuedBy route i (Jump.auxReady (route := EmptyRouter 1) a 0 port mode guard).ledger.emissions) := by
      simp [splice_aux, issuedBy, Jump.ledger, Ledger.zero]
    obtain ⟨lifted, ledger, delivered⟩ := castJumpTarget k target
    refine ⟨lifted, ?_, ?_⟩
    · rw [ledger]
      rfl
    · rw [delivered]
      rfl
  | rawEnd cell port origin active due =>
    have h : cell = 0 := Subsingleton.elim _ _
    subst cell
    let k := Jump.rawEnd (route := route) (splice s i a q) i port origin (by simpa [splice] using active) due
    have target : (setRaw (splice s i a q) i port none) = splice s i (setRaw a 0 port none)
        (q ++ issuedBy route i (Jump.rawEnd (route := EmptyRouter 1) a 0 port origin active due).ledger.emissions) := by
      simp [splice_raw, issuedBy, Jump.ledger, Ledger.zero]
    obtain ⟨lifted, ledger, delivered⟩ := castJumpTarget k target
    refine ⟨lifted, ?_, ?_⟩
    · rw [ledger]
      rfl
    · rw [delivered]
      rfl

theorem splice_execution {θ : Fin N → Parameters} {route : Router N} {a b : Snapshot 1}
    (s : Snapshot N) (i : Fin N) (spectators : Spectators s i)
    (e : Execution (fun _ => θ i) (EmptyRouter 1) a b) (start : s.time ≤ a.time)
    (noArrival : e.deliveries = []) (q : List (Delivery N))
    (future : ∀ t ∈ q ++ issuedBy route i e.ledger.emissions, b.time ≤ t.due) :
    ∃ lifted : Execution θ route (splice s i a q)
      (splice s i b (q ++ issuedBy route i e.ledger.emissions)),
      lifted.ledger.emissions = e.ledger.emissions.map (emissionAt i) ∧ lifted.deliveries = [] := by
  induction e generalizing q with
  | nil state =>
    have same : q ++ issuedBy route i (Execution.nil (θ := fun _ => θ i)
        (route := EmptyRouter 1) state).ledger.emissions = q := by
      change q ++ [] = q
      exact List.append_nil q
    rw [same]
    exact ⟨.nil _, rfl, rfl⟩
  | @cons a m b step rest ih =>
    have hd := List.append_eq_nil_iff.mp noArrival
    cases step with
    | flow f =>
      have later := start.trans f.positive.le
      obtain ⟨tail, he, hv⟩ := ih later hd.2 q future
      let flow := spliceFlow s i spectators f start q
        (fun t ht => rest.time_monotone.trans (future t (List.mem_append_left _ ht)))
      exact ⟨.cons (.flow flow) tail, he, hv⟩
    | jump j =>
      obtain ⟨jump, he, hv⟩ := splice_jump (route := route) s i q j hd.1
      let next := q ++ issuedBy route i j.ledger.emissions
      have same : next ++ issuedBy route i rest.ledger.emissions =
          q ++ issuedBy route i (Execution.cons (.jump j) rest).ledger.emissions := by
        simp only [next, issuedBy, Execution.ledger, Move.ledger, Ledger.add,
          List.flatMap_append, List.append_assoc]
      obtain ⟨tail, htail, hdel⟩ := ih (start.trans_eq j.time_unchanged.symm) hd.2 next
        (fun t ht => future t (same ▸ ht))
      have events : (Execution.cons (.jump jump) tail).ledger.emissions =
          (Execution.cons (.jump j) rest).ledger.emissions.map (emissionAt i) := by
        simp only [Execution.ledger, Move.ledger, Ledger.add, he, htail, List.map_append]
      have deliveries : (Execution.cons (.jump jump) tail).deliveries = [] := by
        simp only [Execution.deliveries, Move.deliveries, hv, hdel, List.append_nil]
      rw [← same]
      exact ⟨.cons (.jump jump) tail, events, deliveries⟩

private theorem mark_nonnegative {θ : Fin N → Parameters} {route : Router N}
    {s u : Snapshot N} (e : Execution θ route s u) (box : PhysicalBox θ ε) (i : Fin N) (p : Port) :
    0 ≤ e.ledger.mark i p := by
  induction e with
  | nil => exact le_rfl
  | cons step rest ih =>
    change 0 ≤ step.ledger.mark i p + rest.ledger.mark i p
    cases step with
    | jump j => simpa only [Move.ledger, j.mark_zero, zero_add] using ih
    | flow f =>
      exact add_nonneg (intervalIntegral.integral_nonneg f.positive.le
        (fun t ht => f.mark_act_nonnegative box i p ht)) ih

private theorem ledger_delivered {θ : Fin N → Parameters} {route : Router N} {s u : Snapshot N}
    (e : Execution θ route s u) : e.ledger.delivered = e.deliveries.length := by
  induction e with
  | nil => rfl
  | cons step rest ih =>
    have count : step.ledger.delivered = step.deliveries.length := by
      cases step with
      | flow => rfl
      | jump j => cases j <;> rfl
    exact (congrArg₂ (· + ·) count ih).trans List.length_append.symm

/-- A settled strong leg in the actual product. Queued deliveries can remain
pending during the leg as long as their dates are strictly beyond its cut. -/
structure StrongStep {N : Nat} (θ : Fin N → Parameters) (route : Router N)
    (s : Snapshot N) (i : Fin N) (port : Port) where
  leg : LocalLeg (fun _ => θ i) (localView s i) port
  final : Snapshot N
  execution : Execution θ route s final
  fireTime : ℝ
  fireTime_eq : fireTime = leg.cycle.fire.final.time
  root : readyPulse (s.x i .q) (Real.exp (s.x i (.z port))) s.time fireTime = 1
  fireBounds : s.time + 3 / 10 < fireTime ∧ fireTime < s.time + 9 / 10
  child : Delivery N
  routeAtFire : route i fireTime = [child]
  childFuture : s.time + 15 / 2 < child.due
  date : final.time = s.time + 15 / 2
  pending : final.pending = s.pending ++ [child]
  emissions : execution.ledger.emissions = [(i, fireTime)]
  deliveries : execution.deliveries = []
  issued : execution.ledger.issued = 1
  delivered : execution.ledger.delivered = 0
  error : ∀ j q, execution.ledger.error j q = 0
  mark : ∀ j q, execution.ledger.mark j q = 0
  recovery : ∀ j, execution.ledger.recovery j = 0
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recoveryPreserved : ∀ j, final.x j .b = s.x j .b
  selectedReady : PreparedSection final i
  selectedCharge : final.x i .q = 1 / 10
  spectatorFinal : ∀ j, j ≠ i → final.x j = quietValues s final.time j
  spectatorReady : ∀ j, j ≠ i → ReadyCoordinates final j
  inactive : ∀ j q, final.raw j q = none
  physical : PhysicalInvariant θ final
  rawValid : RawValid final

theorem strong_step_exists {N : Nat} {θ : Fin N → Parameters} {route : Router N}
    (box : PhysicalBox θ ε) (s : Snapshot N) (i : Fin N) (port : Port)
    (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (prepared : PreparedSection s i)
    (gain : 9 / 5 ≤ Real.exp (s.x i (.z port)) ∧ Real.exp (s.x i (.z port)) ≤ 2)
    (active : s.raw i port = some s.time) (other : ∀ q, q ≠ port → s.raw i q = none)
    (spectators : Spectators s i)
    (future : ∀ token ∈ s.pending, s.time + 15 / 2 < token.due)
    (outgoing : ∀ time, s.time + 3 / 10 < time → time < s.time + 9 / 10 →
      ∃ token, route i time = [token] ∧ s.time + 15 / 2 < token.due) :
    Nonempty (StrongStep θ route s i port) := by
  let single : Fin 1 → Parameters := fun _ => θ i
  have box₁ : PhysicalBox single ε := ⟨box.1, fun _ q => box.2 i q⟩
  have physical₁ : PhysicalInvariant single (localView s i) :=
    ⟨fun _ => physical.region i, fun _ q => physical.gain_cap i q,
      fun _ => physical.recovery_cap i, fun _ => physical.reserve i⟩
  have valid₁ : RawValid (localView s i) := fun _ q origin h => valid i q origin h
  obtain ⟨leg⟩ := local_leg_exists box₁ (localView s i) port physical₁ valid₁
    (show PreparedSection (localView s i) 0 from ⟨prepared.ready, prepared.charge,
      prepared.recovery, prepared.auxiliary⟩) gain active other rfl
  let fire := leg.cycle.fire.final.time
  have clock : s.time + 3 / 10 < fire ∧ fire < s.time + 9 / 10 := by
    have h := leg.cycle.fire_bounds
    change s.time + 2 / 5 < fire ∧ fire < s.time + 7 / 10 at h
    constructor <;> linarith [h.1, h.2]
  obtain ⟨child, routed, childFuture⟩ := outgoing fire clock.1 clock.2
  have issued : issuedBy route i leg.execution.ledger.emissions = [child] := by
    simp only [leg.emissions, issuedBy, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact routed
  have allFuture : ∀ t ∈ s.pending ++ issuedBy route i leg.execution.ledger.emissions,
      leg.final.time ≤ t.due := by
    rw [issued, leg.date]
    intro token h
    rcases List.mem_append.mp h with h | h
    · exact (future token h).le
    · exact (List.mem_singleton.mp h ▸ childFuture).le
  obtain ⟨lifted, emits, noDelivery⟩ := splice_execution s i spectators leg.execution le_rfl
    leg.deliveries s.pending allFuture
  let final := splice s i leg.final (s.pending ++ issuedBy route i leg.execution.ledger.emissions)
  let e : Execution θ route s final := lifted.cast_source (splice_start s i).symm
  have finalTime : final.time = s.time + 15 / 2 := leg.date
  have pending : final.pending = s.pending ++ [child] := by simp only [final, splice, issued]
  have emits' : e.ledger.emissions = [(i, fire)] := by
    rw [Execution.cast_source_ledger, emits, leg.emissions]
    rfl
  have delivered : e.deliveries = [] := by
    rw [Execution.cast_source_deliveries, noDelivery]
  have delCount : e.ledger.delivered = 0 := by rw [ledger_delivered, delivered]; rfl
  have issuedCount : e.ledger.issued = 1 := by
    have balance := e.queue_balance
    rw [pending, List.length_append, delCount] at balance
    simp only [List.length_cons, List.length_nil] at balance
    omega
  have spectatorValues (j : Fin N) (different : j ≠ i) :
      final.x j = quietValues s final.time j := by simp [final, splice, different]
  have gainFinal (j : Fin N) (q : Port) : final.x j (.z q) = s.x j (.z q) := by
    by_cases h : j = i
    · subst j; simpa [final, splice, localView] using leg.gains q
    · rw [spectatorValues j h]; rfl
  have recoveryFinal (j : Fin N) : final.x j .b = s.x j .b := by
    by_cases h : j = i
    · subst j; simpa [final, splice, localView] using leg.recovery
    · rw [spectatorValues j h]; rfl
  have errorZero (j : Fin N) (q : Port) : e.ledger.error j q = 0 := by
    have balance := e.gain_balance j q
    rw [gainFinal] at balance
    linarith
  have recoveryZero (j : Fin N) : e.ledger.recovery j = 0 := by
    have balance := e.recovery_balance j
    rw [recoveryFinal] at balance
    linarith
  have markZero (j : Fin N) (q : Port) : e.ledger.mark j q = 0 := by
    have sumZero : (∑ p : Port, e.ledger.mark j p) = 0 := by
      rw [← e.recovery_sum_marks, recoveryZero]
    have bound := Finset.single_le_sum
      (s := Finset.univ) (f := fun p : Port => e.ledger.mark j p)
      (fun p _ => mark_nonnegative e box j p) (Finset.mem_univ q)
    rw [sumZero] at bound
    exact le_antisymm bound (mark_nonnegative e box j q)
  have root : readyPulse (s.x i .q) (Real.exp (s.x i (.z port))) s.time fire = 1 := by
    change readyPulse ((localView s i).x 0 .q) (Real.exp ((localView s i).x 0 (.z port)))
      (localView s i).time leg.cycle.fire.final.time = 1
    rw [leg.cycle.fire.date]
    exact leg.cycle.fire.response_root
  refine ⟨{
    leg := leg, final := final, execution := e, fireTime := fire, fireTime_eq := rfl
    root := root, fireBounds := clock, child := child, routeAtFire := routed, childFuture := childFuture
    date := finalTime, pending := pending, emissions := emits', deliveries := delivered
    issued := issuedCount, delivered := delCount, error := errorZero, mark := markZero
    recovery := recoveryZero, gains := gainFinal, recoveryPreserved := recoveryFinal
    selectedReady := ?_, selectedCharge := by simpa [final, splice] using leg.charge
    spectatorFinal := spectatorValues, spectatorReady := ?_, inactive := ?_
    physical := e.physical_invariant box physical, rawValid := e.raw_valid valid
  }⟩
  · exact ⟨by simpa [final, splice] using leg.ready.ready,
      by simpa [final, splice] using leg.ready.charge,
      by simpa [final, splice] using leg.ready.recovery,
      fun q => by simpa [final, splice] using leg.ready.auxiliary q⟩
  · intro j h
    have time : s.time ≤ final.time := by rw [finalTime]; linarith
    have ready := quietAt_ready_coordinates s j (spectators.ready j h) time
    exact ⟨by simpa [final, splice, quietAt, h] using ready.ready,
      by simpa [final, splice, quietAt, h] using ready.charge,
      fun q => by simpa [final, splice, quietAt, h] using ready.auxiliary q⟩
  · intro j q
    by_cases h : j = i
    · subst j; simpa [final, splice] using leg.raw q
    · simpa [final, splice, h] using spectators.raw j h q

/-- Consume a real earliest source and then settle its strong transaction.
All other pending occurrences are carried into the leg as future work. -/
theorem strong_transaction_exists {θ : Fin N → Parameters} {route : Router N}
    (box : PhysicalBox θ ε) (s : Snapshot N) (token : Delivery N) (later : List (Delivery N))
    (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (selected : PreparedSection s token.cell)
    (gain : 9 / 5 ≤ Real.exp (s.x token.cell (.z token.port)) ∧
      Real.exp (s.x token.cell (.z token.port)) ≤ 2)
    (spectators : Spectators s token.cell)
    (raw : ∀ q, s.raw token.cell q = none)
    (date : s.time < token.due) (queue : s.pending = token :: later)
    (future : ∀ pending ∈ later, token.due + 15 / 2 < pending.due)
    (outgoing : ∀ time, token.due + 3 / 10 < time → time < token.due + 9 / 10 →
      ∃ child, route token.cell time = [child] ∧ token.due + 15 / 2 < child.due) :
    ∃ arrival : QuietSourceArrival θ route s token later,
      ∃ pulse : StrongStep θ route arrival.final token.cell token.port,
        pulse.final.time = token.due + 15 / 2 ∧
        (arrival.execution.append pulse.execution).deliveries = [token] ∧
        (arrival.execution.append pulse.execution).ledger.emissions = [(token.cell, pulse.fireTime)] ∧
        pulse.final.pending = later ++ [pulse.child] := by
  have allReady (j : Fin N) : ReadyCoordinates s j := by
    by_cases h : j = token.cell
    · subst j; exact selected.ready_coordinates
    · exact spectators.ready j h
  have allRaw (j : Fin N) (q : Port) : s.raw j q = none := by
    by_cases h : j = token.cell
    · subst j; exact raw q
    · exact spectators.raw j h q
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := route) box s token later physical valid allReady allRaw date queue
    (fun pending seen => by have h := future pending seen; linarith)
  have ready : PreparedSection arrival.final token.cell :=
    ⟨(arrival.ready _).ready, (arrival.ready _).charge,
      by rw [arrival.recovery_preserved]; exact selected.recovery, (arrival.ready _).auxiliary⟩
  have gain' : 9 / 5 ≤ Real.exp (arrival.final.x token.cell (.z token.port)) ∧
      Real.exp (arrival.final.x token.cell (.z token.port)) ≤ 2 := by
    rw [arrival.gain_preserved]
    exact gain
  have quiet : Spectators arrival.final token.cell :=
    ⟨fun j _ => arrival.ready j, fun j h q => arrival.raw_other j q (Or.inl h)⟩
  obtain ⟨pulse⟩ := strong_step_exists (route := route) box arrival.final token.cell token.port arrival.physical
    arrival.raw_valid ready gain' arrival.raw_active
    (fun q h => arrival.raw_other _ _ (Or.inr h)) quiet
    (by rw [arrival.date, arrival.pending]; exact future)
    (by rw [arrival.date]; exact outgoing)
  refine ⟨arrival, pulse, ?_, ?_, ?_, ?_⟩
  · rw [pulse.date, arrival.date]
  · rw [Execution.deliveries_append, arrival.deliveries, pulse.deliveries, List.append_nil]
  · rw [Execution.emissions_append, arrival.emissions, pulse.emissions, List.nil_append]
  · rw [pulse.pending, arrival.pending]

end NetworkStability.NativeStrong
