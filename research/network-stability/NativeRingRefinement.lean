import NativeRingTarget
import NativeWeakStep

namespace NetworkStability.NativeRing

open KernelR.Hybrid
open PhaseAdmission
open NativeStrong
open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

variable {N : Nat} {size : 2 ≤ N}

private def stage : Input N → Nat
  | .inl i => i.val
  | .inr _ => N

private theorem stage_succ (i : Fin N) : stage (successor i) = i.val + 1 := by
  unfold successor
  split
  · rfl
  · change N = i.val + 1
    have hi := i.isLt
    omega

private def keyAddress (size : 2 ≤ N) (key : Input N) : Address N :=
  ⟨inputCell size key, match key with | .inl _ => .port0 | .inr _ => .port1⟩

private theorem gain_eq (p : Parameters N) (s : Probe N) :
    MarkFeedback.gain (calendar p size).model s = (keyAddress size s.input).encode := by
  rcases s with ⟨date, i | ⟨⟩⟩ <;> rfl

private theorem route_fwd (p : Parameters N) (x : Probe N) (i : Fin N)
    (h : x.input = .inl i) :
    (calendar p size).route x = [⟨x.due + latency p i + p.delay i, successor i⟩] := by
  simp [calendar, h]

private theorem route_return (p : Parameters N) (x : Probe N) (h : x.input = .inr ()) :
    (calendar p size).route x = [] := by
  simp [calendar, h]

private noncomputable def credit (size : 2 ≤ N) (i : Fin (3 * N)) (x : Probe N) : Nat := by
  classical
  exact if ∃ k : Input N, stage x.input ≤ stage k ∧ i = (keyAddress size k).encode then 1 else 0

private theorem footprint_eq (p : Parameters N) (x : Probe N) (fire : Bool) (i : Fin (3 * N)) :
    MarkFeedback.footprint (calendar p size).model x fire i =
      if fire = false ∧ i = (keyAddress size x.input).encode then 1 else 0 := by
  unfold MarkFeedback.footprint
  rw [gain_eq (size := size)]
  simp [Calendar.model, calendar]

private noncomputable def reserve (p : Parameters N) :
    MarkFeedback.Reserve Q (calendar p size).model (seed size) where
  credit := credit size
  pays := by
    classical
    intro x fire i
    rw [footprint_eq (size := size)]
    cases fire
    · by_cases coord : i = (keyAddress size x.input).encode
      · have owns : ∃ k : Input N, stage x.input ≤ stage k ∧ i = (keyAddress size k).encode :=
          ⟨x.input, le_rfl, coord⟩
        rw [credit, ite_eq_left owns]
        simp [MarkFeedback.emitted, AutonomousFeedback.mass, coord]
      · simp [MarkFeedback.emitted, AutonomousFeedback.mass, coord]
    · simp only [Bool.true_eq_false, false_and, ite_false]
      change AutonomousFeedback.mass (credit size i) ((calendar p size).route x) ≤ credit size i x
      rcases h : x.input with j | ⟨⟩
      · rw [route_fwd (size := size) p x j h]
        simp only [AutonomousFeedback.mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        unfold credit
        split
        · rename_i seen
          obtain ⟨k, lower, addr⟩ := seen
          have bound : stage x.input ≤ stage k := by
            change stage (successor j) ≤ stage k at lower
            rw [stage_succ] at lower
            rw [h]
            change j.val ≤ stage k
            exact (Nat.le_succ j.val).trans lower
          simp [show ∃ k : Input N, stage x.input ≤ stage k ∧ i = (keyAddress size k).encode from ⟨k, bound, addr⟩]
        · exact Nat.zero_le _
      · rw [route_return (size := size) p x h]
        exact Nat.zero_le _
  seed_bound := by
    classical
    intro i
    change credit size i ⟨1, .inl (root size)⟩ + 0 ≤ 1
    unfold credit
    split <;> omega

private theorem rank_stage (x : Probe N) : occurrenceRank x = N + 1 - stage x.input := by
  rcases x with ⟨t, j | ⟨⟩⟩
  · rfl
  · simp [occurrenceRank, stage]

private def rank (p : Parameters N) :
    MarkFeedback.Rank W eta₀ (calendar p size).model (seed size) where
  weight := occurrenceRank
  positive := by decide
  decreases := by
    intro x
    change AutonomousFeedback.mass occurrenceRank ((calendar p size).route x) + 1 ≤ occurrenceRank x
    rcases h : x.input with j | ⟨⟩
    · rw [route_fwd (size := size) p x j h, rank_stage x]
      simp only [AutonomousFeedback.mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, rank_stage]
      rw [stage_succ, h]
      change N + 1 - (j.val + 1) + 1 ≤ N + 1 - j.val
      have hj := j.isLt
      omega
    · rw [route_return (size := size) p x h, rank_stage, h]
      simp [stage, AutonomousFeedback.mass]
  seed_bound := by
    change (N + 1 - 0) + 0 ≤ 2 * N
    omega

private theorem route_length (p : Parameters N) (x : Probe N) : ((calendar p size).route x).length ≤ 1 := by
  rcases h : x.input with j | ⟨⟩
  · rw [route_fwd (size := size) p x j h]
    exact le_rfl
  · rw [route_return (size := size) p x h]
    exact Nat.zero_le _

private theorem selected_rest {p : Probe N} {rest : List (Probe N)} {s : State N}
    (small : s.pending.length ≤ 1) (chosen : s.pending.Perm (p :: rest)) : rest = [] := by
  have h := chosen.length_eq
  simp only [List.length_cons] at h
  exact List.length_eq_zero_iff.mp (by omega)

private theorem small_after (p : Parameters N) (s : State N) (x : Probe N) (error : Int) :
    (MarkFeedback.process (calendar p size).model d s x [] error).pending.length ≤ 1 := by
  change (if MarkFeedback.read (calendar p size).model d s x error then (calendar p size).route x else []).length ≤ 1
  split
  · exact route_length (size := size) p x
  · simp

private theorem ties (p : Parameters N) :
    TieAdmissible (calendar p size) d (MarkFeedback.initial N (seed size)) := by
  have small (s : State N) (path : DatedPath (calendar p size) d (MarkFeedback.initial N (seed size)) s) :
      s.pending.length ≤ 1 := by
    induction path with
    | refl => exact le_rfl
    | tail path move ih =>
      obtain ⟨x, rest, chosen, _, rfl⟩ := move
      obtain rfl := selected_rest ih chosen
      exact small_after (size := size) p _ x 0
  intro s path x y eligibleX eligibleY different _
  have bound := small s path
  cases h : s.pending with
  | nil => exact (List.not_mem_nil (h ▸ eligibleX.1)).elim
  | cons z zs =>
    have empty : zs = [] := by
      rw [h, List.length_cons] at bound
      exact List.length_eq_zero_iff.mp (by omega)
    subst zs
    exact (different ((List.mem_singleton.mp (h ▸ eligibleX.1)).trans
      (List.mem_singleton.mp (h ▸ eligibleY.1)).symm)).elim

private theorem compare_traces (p : Parameters N) {s a b : State N} {xs ys}
    (hx : Trace (calendar p size) d (· ≤ ·) s xs a)
    (hy : Trace (calendar p size) d (· ≤ ·) s ys b)
    (small : s.pending.length ≤ 1) (done : b.pending = []) :
    ∃ suffix, Trace (calendar p size) d (· ≤ ·) a suffix b ∧ xs ++ suffix = ys := by
  induction hx generalizing b ys with
  | nil => exact ⟨ys, hy, rfl⟩
  | @cons s a x rest chosen earliest lo hi error within room word tail ih =>
    obtain rfl := selected_rest small chosen
    cases hy with
    | nil =>
      rw [done] at chosen
      simp at chosen
    | @cons _ _ y rest' chosen' _ lo' hi' error' within' room' word' tail' =>
      obtain rfl := selected_rest small chosen'
      have eq : x = y := by simpa using chosen.symm.trans chosen'
      subst y
      have same :
          MarkFeedback.read (calendar p size).model d s x error =
            MarkFeedback.read (calendar p size).model d s x error' :=
        (MarkFeedback.read_eq_of_room _ lo hi error within room).trans
          (MarkFeedback.read_eq_of_room _ lo' hi' error' within' room').symm
      have stateEq :
          MarkFeedback.process (calendar p size).model d s x [] error' =
            MarkFeedback.process (calendar p size).model d s x [] error := by
        simp only [MarkFeedback.process, same]
      obtain ⟨suffix, trace, eq⟩ := ih (stateEq ▸ tail') (small_after (size := size) p s x error) done
      exact ⟨suffix, trace, by rw [List.cons_append, eq, same]⟩

private theorem latency_exact (p : Parameters N) (i : Fin N) (strong : StrongAmplitude (p.forwardAmplitude i))
    {date fire : ℝ} (window : date + 3 / 10 < fire ∧ fire < date + 9 / 10)
    (root : readyPulse (1 / 10) (p.forwardAmplitude i) date fire = 1) :
    date + latency p i = fire := by
  let t := fire - date
  have eq : date + t = fire := by dsimp [t]; ring
  have low : (9 / 5 : ℝ) ≤ (p.forwardAmplitude i : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).2 strong.1
  have small : t ∈ Set.Icc (0 : ℝ) (9 / 10) := ⟨by dsimp [t]; linarith [window.1],
    by dsimp [t]; linarith [window.2]⟩
  have tRoot : readyPulse (1 / 10) (p.forwardAmplitude i) 0 t = 1 := by
    rw [← eq] at root
    simpa only [readyPulse, add_sub_cancel_left, sub_zero] using root
  have singleton : {v : ℝ | 0 ≤ v ∧ v ≤ 9 / 10 ∧
      readyPulse (1 / 10) (p.forwardAmplitude i) 0 v = 1} = {t} := by
    ext v
    constructor
    · rintro ⟨lo, hi, cross⟩
      exact Set.mem_singleton_iff.mpr (readyPulse_root_unique (by norm_num) low
        (by simpa using And.intro lo hi) (by simpa using small) cross tRoot)
    · rintro (rfl : v = t)
      exact ⟨small.1, small.2, tRoot⟩
  rw [latency, ite_eq_left strong, singleton, csInf_singleton]
  exact eq

private theorem latency_window (p : Parameters N) (i : Fin N)
    (strong : StrongAmplitude (p.forwardAmplitude i)) :
    (3 / 10 : ℝ) < latency p i ∧ latency p i < 9 / 10 := by
  have hg : (9 / 5 : ℝ) ≤ (p.forwardAmplitude i : ℝ) ∧ (p.forwardAmplitude i : ℝ) ≤ 2 :=
    ⟨by simpa using (Rat.cast_le (K := ℝ)).2 strong.1, by simpa using (Rat.cast_le (K := ℝ)).2 strong.2⟩
  obtain ⟨t, lo, hi, root, _⟩ := readyPulse_first_learned_crossing (start := 0)
    (initial := 1 / 10) (by norm_num) hg
  have eq := latency_exact p i strong (date := 0) (fire := 0 + t) (by simpa using And.intro lo hi) root
  simpa [show latency p i = t by simpa using eq] using And.intro lo hi

private theorem delay_window {p : Parameters N} (valid : p.Valid) (i : Fin N) :
    (8 : ℝ) ≤ p.delay i ∧ (p.delay i : ℝ) ≤ 9 :=
  ⟨by simpa using (Rat.cast_le (K := ℝ)).2 (valid.2.2 i).1.1,
    by simpa using (Rat.cast_le (K := ℝ)).2 (valid.2.2 i).1.2⟩

private theorem causal (p : Parameters N) (valid : p.Valid) : Causal (calendar p size) := by
  intro x y seen
  have positive (i : Fin N) : 0 < latency p i := by
    by_cases strong : StrongAmplitude (p.forwardAmplitude i)
    · have h := (latency_window p i strong).1
      linarith
    · rw [latency, ite_eq_right strong]
      norm_num
  rcases key : x.input with i | ⟨⟩
  · rw [route_fwd (size := size) p x i key] at seen
    obtain rfl := List.mem_singleton.mp seen
    change x.due ≤ x.due + latency p i + (p.delay i : ℝ)
    linarith [(delay_window valid i).1, positive i]
  · rw [route_return (size := size) p x key] at seen
    exact (List.not_mem_nil seen).elim

private theorem disjoint_amplitude {a : ℚ} (weak : WeakAmplitude a) (strong : StrongAmplitude a) : False := by
  linarith [weak.2, strong.1]

private theorem forward_class {p : Parameters N} (valid : p.Valid) (i : Fin N) :
    WeakAmplitude (p.forwardAmplitude i) ∨ StrongAmplitude (p.forwardAmplitude i) := by
  have h := (valid.2.2 i).2
  split at h
  · exact Or.inr h
  · exact h

private theorem baseAmplitude (p : Parameters N) (valid : p.Valid) (i : Fin N) (q : Port) :
    0 < (p.amplitude size i q : ℝ) ∧ (p.amplitude size i q : ℝ) ≤ 2 := by
  have bounded {a : ℚ} (h : WeakAmplitude a ∨ StrongAmplitude a) :
      0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 := by
    have low : 0 < a := by
      rcases h with w | s
      · linarith [w.1]
      · linarith [s.1]
    have high : a ≤ 2 := by
      rcases h with w | s
      · linarith [w.2]
      · exact s.2
    exact ⟨by exact_mod_cast low, by exact_mod_cast high⟩
  unfold Parameters.amplitude
  split
  · exact bounded (forward_class valid i)
  · split
    · exact bounded (Or.inl valid.2.1)
    · norm_num

private theorem box : PhysicalBox (nativeParameters N) (1 / 10) :=
  ⟨KernelR.FutureControls.parameters_box.1, fun _ => KernelR.FutureControls.parameters_box.2 0⟩

private theorem basePhysical (p : Parameters N) (valid : p.Valid) : PhysicalInvariant (nativeParameters N) (prepared p size) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    norm_num [prepared, UpperRegion, auxUpper]
  · intro i q
    change Real.log (p.amplitude size i q) ≤ Real.log 4
    have bounded := baseAmplitude (size := size) p valid i q
    exact Real.log_le_log bounded.1 (bounded.2.trans (by norm_num))
  · intro i
    norm_num [prepared]
  · intro i
    norm_num [prepared]

private def zeroState (x : Probe N) : State N := ⟨[x], fun _ => 0⟩

private def endState (k : Input N) : State N :=
  ⟨[], fun i => if i = (keyAddress size k).encode then 1 else 0⟩

private def birthProbe (size : 2 ≤ N) : Probe N := ⟨1, .inl (root size)⟩

set_option maxHeartbeats 1000000 in
private theorem one_row (p : Parameters N) (x : Probe N) (tx : Row N)
    (key : tx.probe = x) (interval : tx.lo = -1 ∧ tx.hi = 1)
    (decision : MarkFeedback.read (calendar p size).model d (zeroState x) x 0 = tx.decision)
    (room : RoutedCalendar.HasRoom (MarkFeedback.score (calendar p size).model d (zeroState x) x) (-1) 1)
    (children : MarkFeedback.emitted (calendar p size).model x tx.decision = tx.children)
    (next : State N) (queue : next.pending = tx.children)
    (writes : ∀ i, next.writes i = MarkFeedback.footprint (calendar p size).model x tx.decision i) :
    TransactionReplay (calendar p size) d (· ≤ ·) (zeroState x) [tx] next := by
  apply TransactionReplay.cons (rest := [])
  · rw [key]; exact .refl _
  · simp [Earliest]
  · rw [interval.1, interval.2]; decide
  · simpa only [key, interval.1, interval.2] using room
  · simpa only [key] using decision
  · simpa only [key] using children
  · exact queue
  · intro i
    simpa only [key, zeroState, Nat.zero_add] using writes i
  · exact .nil _

private theorem root_score (p : Parameters N) (x : Probe N) :
    MarkFeedback.score (calendar p size).model d (zeroState x) x =
      (calendar p size).bias x.input .ready := by
  simp [MarkFeedback.score, Calendar.model, calendar, zeroState]

private theorem quietAdmission {p : Parameters N} {s : Snapshot N} {token : Delivery N} {later}
    (a : QuietSourceArrival (nativeParameters N) (router p size) s token later)
    (start : s.main token.cell = .ready) :
    NativeReciprocal.nativeAdmissions a.execution = [⟨token, .ready⟩] := by
  have mapped := NativeReciprocal.admissions_deliveries a.execution
  rw [a.deliveries] at mapped
  generalize h : NativeReciprocal.nativeAdmissions a.execution = admissions at mapped ⊢
  cases admissions with
  | nil => simp at mapped
  | cons first rest =>
    have empty : rest = [] := by simpa using congrArg List.length mapped
    subst rest
    have tokenEq : first.token = token := by simpa using mapped
    have member : first ∈ NativeReciprocal.nativeAdmissions a.execution := by rw [h]; simp
    obtain ⟨v, w, before, jump, after, split, _, mode, _⟩ :=
      NativeReciprocal.admission_cut a.execution first member
    have firstReady : v.main first.token.cell = .ready :=
      before.allStates_final (before.ready_states_of_no_emissions first.token.cell
        (by rw [tokenEq]; exact start)
        (by
          have whole := a.emissions
          rw [split, Execution.emissions_append] at whole
          simp [Execution.emissionTimes, (List.append_eq_nil_iff.mp whole).1]))
    cases first
    simp_all

private theorem initialMatch (p : Parameters N) :
    Matches p size (prepared p size) (zeroState (birthProbe size)) := by
  refine ⟨.refl _, fun i => ⟨rfl, rfl, fun c => ?_⟩⟩
  rw [show (zeroState (birthProbe size)).writes (Address.mk i c).encode = 0 from rfl]
  simp

private theorem replaceMemory {p : Parameters N} {s u : Snapshot N} {a b : State N}
    (h : Matches p size s a) (queue : u.pending = b.pending.map (toDelivery size))
    (writes : b.writes = a.writes)
    (gain : ∀ i q, u.x i (.z q) = s.x i (.z q))
    (recovery : ∀ i, u.x i .b = s.x i .b) : Matches p size u b := by
  refine ⟨.of_eq queue, fun i => ⟨(gain i 1).trans (h.2 i).1, ?_, ?_⟩⟩
  · rw [writes]; exact (h.2 i).2.1
  · intro c
    rw [writes, ← (h.2 i).2.2 c]
    cases c with
    | port0 => exact gain i 0
    | port1 => exact gain i 2
    | recovery => exact recovery i

private theorem stoppedMatch (p : Parameters N) (x : Probe N) (s u : Snapshot N)
    (h : Matches p size s (zeroState x))
    (queue : u.pending = [])
    (gain : ∀ j q, u.x j (.z q) = s.x j (.z q) +
      if j = inputCell size x.input ∧ q = inputPort x.input then 3 / 5 else 0)
    (rec : ∀ i, u.x i .b = s.x i .b) : Matches p size u (endState (size := size) x.input) := by
  refine ⟨.of_eq queue, ?_⟩
  intro i
  have base (c : Coordinate) : s.x i (nativeCoordinate c) = (prepared p size).x i (nativeCoordinate c) := by
    simpa [zeroState] using (h.2 i).2.2 c
  have port : inputPort x.input = 0 ∨ inputPort x.input = 2 := by
    rcases h : x.input with j | ⟨⟩ <;> simp [inputPort]
  have same (c : Coordinate) :
      (Address.mk i c).encode = (keyAddress size x.input).encode ↔
        i = inputCell size x.input ∧ nativeCoordinate c = .z (inputPort x.input) := by
    constructor
    · intro eq
      have addr := AutonomousFeedback.Schedule.PortMemory.address_encode_injective _ _ eq
      refine ⟨congrArg Address.cell addr, ?_⟩
      have coord := congrArg Address.coordinate addr
      rcases key : x.input with j | ⟨⟩ <;> cases c <;>
        simp_all [keyAddress, inputPort, nativeCoordinate]
    · rintro ⟨cell, coord⟩
      rw [cell]
      rcases key : x.input with j | ⟨⟩ <;> cases c <;>
        simp_all [keyAddress, inputPort, nativeCoordinate]
  refine ⟨?_, ?_, ?_⟩
  · have notPort : (1 : Port) ≠ inputPort x.input := by
      rcases port with h | h <;> rw [h] <;> decide
    simp [gain, notPort, (h.2 i).1]
  · have none : ¬ (Address.mk i .recovery).encode = (keyAddress size x.input).encode := by
      rw [same]
      simp [nativeCoordinate]
    simp [endState, none]
  · intro c
    rw [← base c]
    cases c with
    | port0 =>
      change u.x i (.z 0) = s.x i (.z 0) + (3 / 5) * _
      rw [gain]
      simp only [endState, same, nativeCoordinate, Coord.z.injEq]
      split <;> simp
    | port1 =>
      change u.x i (.z 2) = s.x i (.z 2) + (3 / 5) * _
      rw [gain]
      simp only [endState, same, nativeCoordinate, Coord.z.injEq]
      split <;> simp
    | recovery =>
      simp [rec, endState, same, nativeCoordinate]

private theorem finish (p : Parameters N) (s : Snapshot N) (x : Input N)
    (time : s.time < horizon N) (ready : ∀ i, PreparedSection s i)
    (raw : ∀ i q, s.raw i q = none) (queue : s.pending = [])
    (memoryMatch : Matches p size s (endState (size := size) x)) :
    ∃ (u : Snapshot N) (e : Execution (nativeParameters N) (router p size) s u),
      CompleteThrough e (horizon N) ∧ NativeRows p size e (endState (size := size) x) [] (endState (size := size) x) ∧
      e.deliveries = [] ∧ e.ledger.emissions = [] ∧ u.pending = [] ∧ Matches p size u (endState (size := size) x) := by
  let T := horizon N
  have future : ∀ token ∈ s.pending, T < token.due := by simp [queue]
  let flow : Flow (nativeParameters N) s (quietAt s T) := quietFlow s time
    (fun i => (ready i).ready) (fun i q => ((ready i).auxiliary q).1) raw
    (fun i => by have h := (ready i).charge.2; linarith)
    (fun i q => by have h := ((ready i).auxiliary q).2.2; linarith)
    (fun tok mem => (future tok mem).le)
  let e : Execution (nativeParameters N) (router p size) s (quietAt s T) := .cons (.flow flow) (.nil _)
  have safe : CompleteThrough e T := by
    refine ⟨rfl, ?_, future⟩
    intro v
    apply ready_no_jump (quietAt s T) (fun i => (ready i).ready) (fun i q => ((ready i).auxiliary q).1) raw
    · intro i
      exact relax_lt (by norm_num) time.le (by have h := (ready i).charge.2; linarith) (by norm_num)
    · intro i q
      exact relax_lt (by norm_num) time.le (by have h := ((ready i).auxiliary q).2.2; linarith) (by norm_num)
    · exact future
  have endpoint : Matches p size (quietAt s T) (endState (size := size) x) :=
    replaceMemory (size := size) memoryMatch queue rfl (fun _ _ => rfl) (fun _ => rfl)
  exact ⟨_, e, safe, .done e _ rfl rfl memoryMatch endpoint, rfl, rfl, queue, endpoint⟩

private theorem native_strong_route (p : Parameters N) (i : Fin N) (date fire : ℝ)
    (window : date + 3 / 10 < fire ∧ fire < date + 9 / 10)
    (gate : i = root size → date = 1) :
    router p size i fire =
      [toDelivery size ⟨fire + p.delay i, successor i⟩] := by
  have openGate : ¬ (i = root size ∧ ¬ (1 ≤ fire ∧ fire < 2)) := by
    rintro ⟨h, blocked⟩
    have actual : date = 1 := gate h
    exact blocked ⟨by linarith [window.1], by linarith [window.2]⟩
  unfold router
  rw [ite_eq_right openGate]

set_option maxHeartbeats 1000000 in
private theorem strong_row (p : Parameters N) (x : Probe N) (i : Fin N)
    (key : x.input = .inl i) (gate : i = root size → x.due = 1)
    (strong : StrongAmplitude (p.forwardAmplitude i)) (validP : p.Valid)
    (s : Snapshot N) (preparedAll : ∀ j, PreparedSection s j)
    (physical : PhysicalInvariant (nativeParameters N) s) (valid : RawValid s)
    (raw : ∀ j q, s.raw j q = none) (resting : s.x i .q = 1 / 10)
    (gain : s.x i (.z 0) = Real.log (p.forwardAmplitude i))
    (time : s.time < x.due) (queue : s.pending = [toDelivery size x])
    (matched : Matches p size s (zeroState x)) :
    ∃ (child : Probe N) (tx : Row N) (end' : Snapshot N)
      (intake : QuietSourceArrival (nativeParameters N) (router p size) s (toDelivery size x) [])
      (pulse : Execution (nativeParameters N) (router p size) intake.final end'),
      child.input = successor i ∧ child.due = x.due + latency p i + p.delay i ∧
      end'.time = x.due + 15 / 2 ∧
      end'.pending = [toDelivery size child] ∧
      (∀ j, PreparedSection end' j) ∧ (∀ j q, end'.raw j q = none) ∧
      (∀ j, end'.x j .b = s.x j .b) ∧
      (∀ j q, end'.x j (.z q) = s.x j (.z q)) ∧
      (∀ j, s.x j .q = 1 / 10 → end'.x j .q = 1 / 10) ∧
      PhysicalInvariant (nativeParameters N) end' ∧ RawValid end' ∧
      tx.probe = x ∧
      (intake.execution.append pulse).deliveries = [toDelivery size x] ∧
      (intake.execution.append pulse).ledger.emissions = Transaction.fires (inputCell size) [tx] ∧
      Matches p size end' (zeroState child) ∧
      TransactionReplay (calendar p size) d (· ≤ ·) (zeroState x) [tx] (zeroState child) ∧
      ∀ {u} (suffix : Execution (nativeParameters N) (router p size) end' u) rows out,
        NativeRows p size suffix (zeroState child) rows out →
        NativeRows p size (intake.execution.append (pulse.append suffix))
          (zeroState x) (tx :: rows) out := by
  have hg : (9 / 5 : ℝ) ≤ (p.forwardAmplitude i : ℝ) ∧ (p.forwardAmplitude i : ℝ) ≤ 2 :=
    ⟨by simpa using (Rat.cast_le (K := ℝ)).2 strong.1, by simpa using (Rat.cast_le (K := ℝ)).2 strong.2⟩
  have render : (toDelivery size x).cell = i ∧ (toDelivery size x).port = 0 := by
    simp [toDelivery, key, inputCell, inputPort]
  have strongGain : 9 / 5 ≤ Real.exp (s.x (toDelivery size x).cell (.z (toDelivery size x).port)) ∧
      Real.exp (s.x (toDelivery size x).cell (.z (toDelivery size x).port)) ≤ 2 := by
    rw [render.1, render.2, gain, Real.exp_log (by linarith [hg.1])]
    exact hg
  obtain ⟨intake, pulse, settled, delivered, fired, queued⟩ :=
    strong_transaction_exists (route := router p size) box s (toDelivery size x) []
      physical valid (preparedAll _) strongGain
      ⟨fun j _ => (preparedAll j).ready_coordinates, fun j _ => raw j⟩ (raw _) time queue
      (by simp) (by
        intro fire lo hi
        rw [render.1]
        exact ⟨toDelivery size ⟨fire + p.delay i, successor i⟩,
          native_strong_route (size := size) p i x.due fire ⟨lo, hi⟩ gate,
          by
            change x.due + 3 / 10 < fire at lo
            change x.due + 15 / 2 < fire + p.delay i
            linarith [(delay_window validP i).1]⟩)
  let child : Probe N := ⟨pulse.fireTime + p.delay i, successor i⟩
  let tx : Row N := ⟨x, some pulse.fireTime, [child], -1, 1⟩
  have window : x.due + 3 / 10 < pulse.fireTime ∧ pulse.fireTime < x.due + 9 / 10 := by
    simpa only [intake.date, toDelivery] using pulse.fireBounds
  have actualGain : intake.final.x i (.z 0) = Real.log (p.forwardAmplitude i) :=
    (intake.gain_preserved i 0).trans gain
  have actualCharge : intake.final.x i .q = 1 / 10 := by
    rw [show intake.final.x i .q = quietValues s (toDelivery size x).due i .q from congrFun (congrFun intake.values i) .q]
    simp [quietValues, relax, resting]
  let fire := pulse.fireTime
  have root' : readyPulse (1 / 10) (p.forwardAmplitude i) x.due fire = 1 := by
    have h : readyPulse (intake.final.x (toDelivery size x).cell .q)
        (Real.exp (intake.final.x (toDelivery size x).cell (.z (toDelivery size x).port)))
        intake.final.time fire = 1 := pulse.root
    rw [render.1, render.2, actualGain, actualCharge, Real.exp_log (by linarith [hg.1]), intake.date] at h
    exact h
  have fireDate := latency_exact p i strong window root'
  have childNative : pulse.child = toDelivery size child := by
    have same := pulse.routeAtFire
    have same' : router p size (toDelivery size x).cell fire = [pulse.child] := same
    let nativeChild := pulse.child
    change router p size (toDelivery size x).cell fire = [nativeChild] at same'
    rw [render.1, native_strong_route (size := size) p i x.due fire window gate] at same'
    exact (List.cons.inj same').1.symm
  have nextQ : pulse.final.pending = [toDelivery size child] := by simpa [childNative] using queued
  have gains (j : Fin N) (q : Port) : pulse.final.x j (.z q) = s.x j (.z q) :=
    (pulse.gains j q).trans (intake.gain_preserved j q)
  have recovery (j : Fin N) : pulse.final.x j .b = s.x j .b :=
    (pulse.recoveryPreserved j).trans (intake.recovery_preserved j)
  have match' := replaceMemory (size := size) matched (b := zeroState child) nextQ rfl gains recovery
  have ready (j : Fin N) : PreparedSection pulse.final j := by
    by_cases h : j = (toDelivery size x).cell
    · subst j; exact pulse.selectedReady
    · have r := pulse.spectatorReady j h
      exact ⟨r.ready, r.charge, by rw [recovery]; exact (preparedAll j).recovery, r.auxiliary⟩
  have qRest (j : Fin N) (h : s.x j .q = 1 / 10) : pulse.final.x j .q = 1 / 10 := by
    by_cases eq : j = (toDelivery size x).cell
    · subst j; exact pulse.selectedCharge
    · rw [show pulse.final.x j .q = quietValues intake.final pulse.final.time j .q from
        congrFun (pulse.spectatorFinal j eq) .q]
      have rest : intake.final.x j .q = 1 / 10 := by
        rw [show intake.final.x j .q = quietValues s (toDelivery size x).due j .q from
          congrFun (congrFun intake.values j) .q]
        simp [quietValues, relax, h]
      simp [quietValues, relax, rest]
  have score : MarkFeedback.score (calendar p size).model d (zeroState x) x = 2 := by
    rw [root_score (size := size)]
    simp [calendar, key, show StrongAmplitude (p.forwardAmplitude i) from strong]
  have routes : (calendar p size).route x = [child] := by
    simp [calendar, key, child, fireDate]
  have replay : TransactionReplay (calendar p size) d (· ≤ ·) (zeroState x) [tx] (zeroState child) :=
    one_row (size := size) p x tx rfl ⟨rfl, rfl⟩ (by simp [MarkFeedback.read, score, tx, Transaction.decision])
      (by rw [score]; norm_num [RoutedCalendar.HasRoom])
      (by simpa [MarkFeedback.emitted, Calendar.model, tx, Transaction.decision] using routes)
      _ rfl (fun j => by simp [zeroState, footprint_eq (size := size), tx, Transaction.decision])
  refine ⟨child, tx, pulse.final, intake, pulse.execution, rfl, ?_, settled, nextQ,
    ready, pulse.inactive, recovery, gains, qRest, pulse.physical, pulse.rawValid, rfl,
    delivered, ?_, match', replay, ?_⟩
  · change pulse.fireTime + p.delay i = x.due + latency p i + p.delay i
    rw [fireDate]
  · exact fired
  · intro u suffix rows out tail
    exact .step intake.execution pulse.execution suffix
      (quietAdmission (size := size) intake (preparedAll _).ready) intake.date
      (by simpa only [intake.date, toDelivery, tx] using intake.raw_active)
      intake.emissions pulse.deliveries pulse.emissions
      (by
        have route := (native_strong_route (size := size) p i x.due pulse.fireTime window gate).symm
        simpa [tx, child, key, inputCell] using route)
      (by simpa [tx] using window)
      settled ready pulse.inactive ⟨rfl, rfl⟩ matched match' replay tail

set_option maxHeartbeats 1000000 in
private theorem weak_row (p : Parameters N) (x : Probe N)
    (weak : ∀ i, x.input = .inl i → WeakAmplitude (p.forwardAmplitude i))
    (s : Snapshot N) (preparedAll : ∀ j, PreparedSection s j)
    (physical : PhysicalInvariant (nativeParameters N) s) (valid : RawValid s)
    (raw : ∀ j q, s.raw j q = none)
    (gain : Real.exp (s.x (inputCell size x.input) (.z (inputPort x.input))) ≤ 1)
    (time : s.time < x.due) (queue : s.pending = [toDelivery size x])
    (date : x.due + 15 / 2 < horizon N)
    (matched : Matches p size s (zeroState x)) :
    ∃ (u : Snapshot N)
      (run : Execution (nativeParameters N) (router p size) s u),
      CompleteThrough run (horizon N) ∧
      NativeRows p size run (zeroState x) [⟨x, none, [], -1, 1⟩] (endState (size := size) x.input) ∧
      TransactionReplay (calendar p size) d (· ≤ ·)
        (zeroState x) [⟨x, none, [], -1, 1⟩] (endState (size := size) x.input) ∧
      run.deliveries = [toDelivery size x] ∧ run.ledger.emissions = [] ∧
      u.pending = [] ∧ Matches p size u (endState (size := size) x.input) := by
  let token := toDelivery size x
  let tx : Row N := ⟨x, none, [], -1, 1⟩
  obtain ⟨intake⟩ := quiet_source_arrival_exists (route := router p size) box s token []
    physical valid (fun i => (preparedAll i).ready_coordinates) raw time queue (by simp)
  have prep (j : Fin N) : PreparedSection intake.final j :=
    ⟨(intake.ready j).ready, (intake.ready j).charge,
      by rw [intake.recovery_preserved]; exact (preparedAll j).recovery, (intake.ready j).auxiliary⟩
  have actual : Real.exp (intake.final.x token.cell (.z token.port)) ≤ 1 := by
    rw [intake.gain_preserved]
    exact gain
  obtain ⟨settled, pulse, clock, stillPending, noDelivery, noFire, gains, rec, ready, inactive⟩ :=
    weak_step_exists (route := router p size) box intake.final token.cell token.port intake.physical
      intake.raw_valid (prep _) actual intake.raw_active (fun q ne => intake.raw_other _ _ (Or.inr ne))
      ⟨fun j _ => intake.ready j, fun j ne q => intake.raw_other j q (Or.inl ne)⟩
      (by rw [intake.pending]; simp)
  have done : settled.pending = [] := stillPending.trans intake.pending
  have clock' : settled.time = x.due + 15 / 2 := clock.trans (congrArg (· + 15 / 2) intake.date)
  have afterGain (j : Fin N) (q : Port) : settled.x j (.z q) = s.x j (.z q) +
      if j = inputCell size x.input ∧ q = inputPort x.input then 3 / 5 else 0 := by
    rw [gains, intake.gain_preserved]
    rfl
  have afterRec (j : Fin N) : settled.x j .b = s.x j .b :=
    (rec j).trans (intake.recovery_preserved j)
  have matched' := stoppedMatch (size := size) p x s settled matched done afterGain afterRec
  have score : MarkFeedback.score (calendar p size).model d (zeroState x) x = -2 := by
    rw [root_score (size := size)]
    rcases key : x.input with j | ⟨⟩
    · have notStrong : ¬ StrongAmplitude (p.forwardAmplitude j) :=
        fun strong => disjoint_amplitude (weak j key) strong
      simp [calendar, notStrong]
    · simp [calendar]
  have replay : TransactionReplay (calendar p size) d (· ≤ ·) (zeroState x) [tx] (endState (size := size) x.input) :=
    one_row (size := size) p x tx rfl ⟨rfl, rfl⟩ (by simp [MarkFeedback.read, score, tx, Transaction.decision])
      (by rw [score]; norm_num [RoutedCalendar.HasRoom]) rfl _ rfl (fun i => by simp [endState, footprint_eq (size := size), tx, Transaction.decision])
  obtain ⟨u, idle, complete, tail, idleDelivery, idleFire, empty, endpoint⟩ :=
    finish (size := size) p settled x.input (clock'.trans_lt date) (fun j => ready j (prep j)) inactive done matched'
  let run := intake.execution.append (pulse.append idle)
  have native : NativeRows p size run (zeroState x) [tx] (endState (size := size) x.input) :=
    .step intake.execution pulse idle (quietAdmission (size := size) intake (preparedAll _).ready) intake.date
      (by simpa only [intake.date, toDelivery, tx, token] using intake.raw_active) intake.emissions noDelivery
      noFire rfl (by simp [tx]) clock' (fun j => ready j (prep j)) inactive
      ⟨rfl, rfl⟩ matched matched' replay tail
  exact ⟨u, run, complete, native, replay,
    by simp [run, Execution.deliveries_append, intake.deliveries, noDelivery, idleDelivery, token],
    by simp [run, Execution.emissions_append, intake.emissions, noFire, idleFire], empty, endpoint⟩

private def PartialHistory (size : 2 ≤ N) (p : Parameters N) (s : Snapshot N) (start : State N) (k : Input N) : Prop :=
  ∃ (u : Snapshot N) (run : Execution (nativeParameters N) (router p size) s u)
    (rows : List (Row N)),
    CompleteThrough run (horizon N) ∧ NativeRows p size run start rows (endState (size := size) k) ∧
    TransactionReplay (calendar p size) d (· ≤ ·) start rows (endState (size := size) k) ∧
    rows.map (fun tx => toDelivery size tx.probe) = run.deliveries ∧
    Transaction.fires (inputCell size) rows = run.ledger.emissions ∧
    u.pending = [] ∧ Matches p size u (endState (size := size) k)

private theorem weak_history (p : Parameters N) (x : Probe N)
    (weak : ∀ i, x.input = .inl i → WeakAmplitude (p.forwardAmplitude i))
    (s : Snapshot N) (ready : ∀ j, PreparedSection s j)
    (physical : PhysicalInvariant (nativeParameters N) s) (valid : RawValid s)
    (raw : ∀ j q, s.raw j q = none)
    (gain : Real.exp (s.x (inputCell size x.input) (.z (inputPort x.input))) ≤ 1)
    (time : s.time < x.due) (queue : s.pending = [toDelivery size x])
    (endTime : x.due + 15 / 2 < horizon N)
    (matched : Matches p size s (zeroState x)) :
    PartialHistory size p s (zeroState x) x.input := by
  obtain ⟨u, run, complete, native, replay, delivered, emits, empty, endpoint⟩ :=
    weak_row (size := size) p x weak s ready physical valid raw gain time queue endTime matched
  exact ⟨u, run, [_], complete, native, replay, delivered.symm, emits.symm, empty, endpoint⟩

private theorem prepend_history {p : Parameters N} {s v u : Snapshot N} {x y : Probe N}
    (tx : Row N) (head : Execution (nativeParameters N) (router p size) s v)
    (pulse : Execution (nativeParameters N) (router p size) v u)
    (probe : tx.probe = x)
    (delivered : (head.append pulse).deliveries = [toDelivery size x])
    (emits : (head.append pulse).ledger.emissions = Transaction.fires (inputCell size) [tx])
    (replay : TransactionReplay (calendar p size) d (· ≤ ·) (zeroState x) [tx] (zeroState y))
    (prepend : ∀ {last} (e : Execution (nativeParameters N) (router p size) u last) rows out,
      NativeRows p size e (zeroState y) rows out →
      NativeRows p size (head.append (pulse.append e)) (zeroState x) (tx :: rows) out)
    {k : Input N} (tail : PartialHistory size p u (zeroState y) k) :
    PartialHistory size p s (zeroState x) k := by
  obtain ⟨last, e, rows, complete, native, replayTail, deliveries, fires, empty, endpoint⟩ := tail
  let joined := head.append (pulse.append e)
  refine ⟨last, joined, tx :: rows, complete, prepend e rows _ native,
    replay.append replayTail, ?_, ?_, empty, endpoint⟩
  · have split : joined.deliveries = (head.append pulse).deliveries ++ e.deliveries := by
      rw [show joined = (head.append pulse).append e by rw [Execution.append_assoc]]
      exact Execution.deliveries_append _ _
    rw [split, delivered, ← deliveries, List.map_cons, probe]
    rfl
  · have split : joined.ledger.emissions = (head.append pulse).ledger.emissions ++ e.ledger.emissions := by
      rw [show joined = (head.append pulse).append e by rw [Execution.append_assoc]]
      exact Execution.emissions_append _ _
    rw [split, emits, ← fires]
    simpa only [Transaction.fires, List.singleton_append] using
      (List.filterMap_append (l := [tx]) (l' := rows) (f := fun tx : Row N =>
        tx.fireDate.map (fun t => (inputCell size tx.probe.input, t))))

set_option maxHeartbeats 2500000 in

/-- At a settled cut, the only pending delivery is the next admission.
Every cell is READY with closed raw ports and the prepared charge. At this
point no weak probe has run, so the memory has zero accrued doses. -/
private structure SingleToken (p : Parameters N) (size : 2 ≤ N)
    (s : Snapshot N) (x : Probe N) : Prop where
  ready : ∀ j, PreparedSection s j
  physical : PhysicalInvariant (nativeParameters N) s
  valid : RawValid s
  raw : ∀ j q, s.raw j q = none
  charge : ∀ j, s.x j .q = 1 / 10
  time : s.time < x.due
  queue : s.pending = [toDelivery size x]
  memory : Matches p size s (zeroState x)
  lower : 1 + 8 * (stage x.input : ℝ) ≤ x.due
  upper : x.due ≤ 1 + (99 / 10) * (stage x.input : ℝ)
  passed : ∀ j : Fin N, j.val < stage x.input → StrongAmplitude (p.forwardAmplitude j)

private theorem result_at_weak (p : Parameters N) (i : Fin N)
    (weak : WeakAmplitude (p.forwardAmplitude i))
    (passed : ∀ j : Fin N, j.val < i.val → StrongAmplitude (p.forwardAmplitude j)) :
    resultInput p = .inl i := by
  have found : (List.finRange N).find? (fun j => decide (WeakAmplitude (p.forwardAmplitude j))) = some i := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨decide_eq_true weak, i.val, by simp, ?_, ?_⟩
    · simp
    · intro j hj
      have hN : j < N := hj.trans i.isLt
      have strong := passed ⟨j, hN⟩ hj
      simpa using (show ¬ WeakAmplitude (p.forwardAmplitude ⟨j, hN⟩) from
        fun w => disjoint_amplitude w strong)
  simp [resultInput, found]

private theorem result_at_return (p : Parameters N)
    (passed : ∀ j : Fin N, StrongAmplitude (p.forwardAmplitude j)) :
    resultInput p = .inr () := by
  have found : (List.finRange N).find? (fun j => decide (WeakAmplitude (p.forwardAmplitude j))) = none := by
    apply List.find?_eq_none.mpr
    intro i _
    simp [show ¬ WeakAmplitude (p.forwardAmplitude i) from fun w => disjoint_amplitude w (passed i)]
  simp [resultInput, found]

private theorem stage_le (k : Input N) : stage k ≤ N := by
  rcases k with i | ⟨⟩
  · exact i.isLt.le
  · exact le_rfl

private theorem weak_amplitude_le_one (p : Parameters N) (valid : p.Valid)
    (k : Input N) (weak : ∀ i, k = .inl i → WeakAmplitude (p.forwardAmplitude i)) :
    (p.amplitude size (inputCell size k) (inputPort k) : ℝ) ≤ 1 := by
  rcases k with i | ⟨⟩
  · simpa [Parameters.amplitude, inputCell, inputPort] using (Rat.cast_le (K := ℝ)).2 (weak i rfl).2
  · have different : (2 : Port) ≠ 0 := by decide
    simpa [Parameters.amplitude, inputCell, inputPort, different] using (Rat.cast_le (K := ℝ)).2 valid.2.1.2

private theorem prepared_gain (p : Parameters N) (s : Snapshot N) (x : Probe N)
    (matched : Matches p size s (zeroState x)) :
    s.x (inputCell size x.input) (.z (inputPort x.input)) =
      Real.log (p.amplitude size (inputCell size x.input) (inputPort x.input)) := by
  rcases key : x.input with i | ⟨⟩
  · simpa [key, inputCell, inputPort, nativeCoordinate, prepared, zeroState] using (matched.2 i).2.2 .port0
  · simpa [key, inputCell, inputPort, nativeCoordinate, prepared, zeroState] using (matched.2 (root size)).2.2 .port1

private theorem SingleToken.silent {p : Parameters N} {s : Snapshot N} {x : Probe N}
    (h : SingleToken p size s x) (valid : p.Valid)
    (weak : ∀ i, x.input = .inl i → WeakAmplitude (p.forwardAmplitude i)) :
    PartialHistory size p s (zeroState x) x.input := by
  have stages : (stage x.input : ℝ) ≤ N := by exact_mod_cast stage_le x.input
  have endTime : x.due + 15 / 2 < horizon N := by
    unfold horizon
    linarith [h.upper, stages]
  have gain : Real.exp (s.x (inputCell size x.input) (.z (inputPort x.input))) ≤ 1 := by
    rw [prepared_gain (size := size) p s x h.memory, Real.exp_log (baseAmplitude (size := size) p valid _ _).1]
    exact weak_amplitude_le_one (size := size) p valid x.input weak
  exact weak_history (size := size) p x weak s h.ready h.physical h.valid h.raw gain h.time h.queue endTime h.memory

set_option maxHeartbeats 1000000 in
private theorem SingleToken.continue {p : Parameters N} {s : Snapshot N} {x : Probe N}
    (h : SingleToken p size s x) (valid : p.Valid) (i : Fin N) (key : x.input = .inl i)
    (strong : StrongAmplitude (p.forwardAmplitude i)) :
    ∃ (next : Snapshot N) (child : Probe N), stage child.input = stage x.input + 1 ∧
      SingleToken p size next child ∧
      (PartialHistory size p next (zeroState child) (resultInput p) →
        PartialHistory size p s (zeroState x) (resultInput p)) := by
  have gate : i = root size → x.due = 1 := by
    intro eq
    have lo := h.lower
    have hi := h.upper
    rw [key, eq] at lo hi
    norm_num [stage, root] at lo hi
    exact le_antisymm hi lo
  have gain : s.x i (.z 0) = Real.log (p.forwardAmplitude i) := by
    simpa [key, inputCell, inputPort, Parameters.amplitude] using prepared_gain (size := size) p s x h.memory
  obtain ⟨child, tx, cut, intake, pulse, childKey, due, clock, queue, ready, raw, _, _,
    qRest, physical, rawValid, probe, delivered, emits, memoryMatch, replay, prepend⟩ :=
    strong_row (size := size) p x i key gate strong valid s h.ready h.physical h.valid h.raw (h.charge i)
      gain h.time h.queue h.memory
  have stageChild : stage child.input = stage x.input + 1 := by
    rw [childKey, stage_succ, key]
    rfl
  have lag := latency_window p i strong
  have delay := delay_window valid i
  have time : cut.time < child.due := by
    rw [clock, due]
    linarith [lag.1, delay.1]
  have lower : 1 + 8 * (stage child.input : ℝ) ≤ child.due := by
    rw [stageChild, Nat.cast_add, Nat.cast_one, due]
    linarith [h.lower, lag.1, delay.1]
  have upper : child.due ≤ 1 + (99 / 10) * (stage child.input : ℝ) := by
    rw [stageChild, Nat.cast_add, Nat.cast_one, due]
    linarith [h.upper, lag.2, delay.2]
  have passed (j : Fin N) (before : j.val < stage child.input) :
      StrongAmplitude (p.forwardAmplitude j) := by
    rw [stageChild, key] at before
    change j.val < i.val + 1 at before
    by_cases eq : j.val = i.val
    · have cell : j = i := Fin.ext eq
      simpa only [cell] using strong
    · exact h.passed j (by rw [key]; change j.val < i.val; omega)
  exact ⟨cut, child, stageChild,
    ⟨ready, physical, rawValid, raw, fun j => qRest j (h.charge j), time, queue,
      memoryMatch, lower, upper, passed⟩,
    prepend_history (size := size) tx intake.execution pulse probe delivered emits replay prepend⟩

/-- The next forward index is strictly larger, and the return port has index N. -/
private theorem history_from (p : Parameters N) (valid : p.Valid) (s : Snapshot N) (x : Probe N)
    (h : SingleToken p size s x) :
    PartialHistory size p s (zeroState x) (resultInput p) := by
  suffices all : ∀ (remaining : Nat) (s : Snapshot N) (x : Probe N),
      N - stage x.input = remaining → SingleToken p size s x →
        PartialHistory size p s (zeroState x) (resultInput p) by
    exact all _ s x rfl h
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro s x measure h
    rcases key : x.input with i | ⟨⟩
    · obtain weak | strong := forward_class valid i
      · rw [result_at_weak p i weak (by simpa only [key, stage] using h.passed), ← key]
        exact h.silent (size := size) valid (by
          intro j hj
          rw [key] at hj
          cases hj
          exact weak)
      · obtain ⟨next, child, stageChild, nextToken, prepend⟩ := h.continue (size := size) valid i key strong
        have decreases : N - stage child.input < remaining := by
          rw [← measure, stageChild, key]
          change N - (i.val + 1) < N - i.val
          have hi := i.isLt
          omega
        exact prepend (ih _ decreases next child rfl nextToken)
    · rw [result_at_return p (fun j => h.passed j (by simp [key, stage])), ← key]
      exact h.silent (size := size) valid (by
        intro i hi
        rw [key] at hi
        contradiction)

private theorem histories (p : Parameters N) (valid : p.Valid) :
    PartialHistory size p (prepared p size) (zeroState (birthProbe size)) (resultInput p) := by
  apply history_from (size := size) p valid
  refine ⟨?_, basePhysical (size := size) p valid, ?_, fun _ _ => rfl, fun _ => rfl, ?_, rfl,
    initialMatch (size := size) p, ?_, ?_, ?_⟩
  · intro j
    refine ⟨rfl, by norm_num [prepared], by norm_num [prepared], fun q => ?_⟩
    exact ⟨rfl, by norm_num [prepared, RestBand]⟩
  · intro i q t h
    cases h
  · norm_num [prepared, birthProbe]
  · norm_num [birthProbe, stage, root]
  · norm_num [birthProbe, stage, root]
  · intro j h
    simp [birthProbe, stage, root] at h

private theorem flow_gain_le_end {θ : Fin N → KernelR.Hybrid.Parameters} {s u : Snapshot N}
    (f : Flow θ s u) (hb : PhysicalBox θ ε) (i : Fin N) (p : Port) (t : ℝ)
    (ht : t ∈ Set.Icc s.time u.time) : f.path t i (.z p) ≤ u.x i (.z p) := by
  by_cases endDate : t = u.time
  · rw [endDate, f.final]
  · let rest := f.suffix ht.1 (lt_of_le_of_ne ht.2 endDate)
    have h := rest.gain_nondecreasing hb i p u.time ⟨ht.2, le_rfl⟩
    exact h.trans_eq (congrFun (congrFun f.final i) (.z p))

private theorem flow_recovery_le_end {θ : Fin N → KernelR.Hybrid.Parameters} {s u : Snapshot N}
    (f : Flow θ s u) (hb : PhysicalBox θ ε) (i : Fin N) (t : ℝ)
    (ht : t ∈ Set.Icc s.time u.time) : f.path t i .b ≤ u.x i .b := by
  by_cases endDate : t = u.time
  · rw [endDate, f.final]
  · let rest := f.suffix ht.1 (lt_of_le_of_ne ht.2 endDate)
    have h := rest.recovery_nondecreasing hb i u.time ⟨ht.2, le_rfl⟩
    exact h.trans_eq (congrFun (congrFun f.final i) .b)

private theorem runRails {s u : Snapshot N} {r : Router N}
    (e : Execution (nativeParameters N) r s u) (rail : BelowRail u.x) :
    e.AllStates (fun state => BelowRail state.x) ∧
      e.AllFlows (fun {s u} f => ∀ t ∈ Set.Icc s.time u.time, BelowRail (f.path t)) := by
  induction e with
  | nil => exact ⟨rail, trivial⟩
  | @cons s mid u step tail ih =>
    have atStart : BelowRail s.x := by
      exact ⟨fun i p => (Execution.cons step tail).gain_nondecreasing box i p |>.trans_lt (rail.1 i p),
        fun i => (Execution.cons step tail).recovery_nondecreasing box i |>.trans_lt (rail.2 i)⟩
    have tailRails := ih rail
    refine ⟨⟨atStart, tailRails.1⟩, ?_⟩
    cases step with
    | jump => exact tailRails.2
    | flow f =>
      refine ⟨fun t ht => ⟨fun i p => ?_, fun i => ?_⟩, tailRails.2⟩
      · exact ((flow_gain_le_end f box i p t ht).trans (tail.gain_nondecreasing box i p)).trans_lt (rail.1 i p)
      · exact ((flow_recovery_le_end f box i t ht).trans (tail.recovery_nondecreasing box i)).trans_lt (rail.2 i)


private theorem result_weak (p : Parameters N) (i : Fin N)
    (key : resultInput p = .inl i) : WeakAmplitude (p.forwardAmplitude i) := by
  unfold resultInput at key
  split at key
  · rename_i j found
    cases key
    exact of_decide_eq_true (List.find?_eq_some_iff_getElem.mp found).1
  · contradiction

private theorem endRail (p : Parameters N) (valid : p.Valid) (last : Snapshot N)
    (memoryMatch : Matches p size last (endState (size := size) (resultInput p))) :
    BelowRail last.x := by
  have doseRoom : (3 / 5 : ℝ) < Real.log 4 := by linarith [KernelR.log_four_bounds.1]
  have trainedRoom : Real.log (2 : ℝ) < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have baseRoom (i : Fin N) (q : Port) :
      (prepared p size).x i (.z q) < Real.log 4 :=
    (Real.log_le_log (baseAmplitude (size := size) p valid i q).1 (baseAmplitude (size := size) p valid i q).2).trans_lt trainedRoom
  constructor
  · intro i q
    change last.x i (.z q) < Real.log 4
    fin_cases q
    · change last.x i (nativeCoordinate .port0) < Real.log 4
      rw [(memoryMatch.2 i).2.2 .port0]
      change (prepared p size).x i (.z 0) + 3 / 5 *
        (if (Address.mk i .port0).encode = (keyAddress size (resultInput p)).encode then 1 else 0 : Nat) < _
      split
      · rename_i address
        have matchAddr := AutonomousFeedback.Schedule.PortMemory.address_encode_injective _ _ address
        have key : resultInput p = .inl i := by
          rcases h : resultInput p with j | ⟨⟩
          · have sameCell : i = j := by
              simpa only [h, keyAddress, inputCell] using congrArg Address.cell matchAddr
            rw [sameCell]
          · have eq := congrArg Address.coordinate matchAddr
            simp [h, keyAddress] at eq
        have amp := result_weak p i key
        have low : Real.log (p.forwardAmplitude i) ≤ 0 := Real.log_nonpos
          (by simpa [Parameters.amplitude] using (baseAmplitude (size := size) p valid i 0).1.le)
          (by exact_mod_cast amp.2)
        norm_num [prepared, Parameters.amplitude]
        linarith
      · simpa using baseRoom i 0
    · exact ((memoryMatch.2 i).1).trans_lt (baseRoom i 1)
    · change last.x i (nativeCoordinate .port1) < Real.log 4
      rw [(memoryMatch.2 i).2.2 .port1]
      change (prepared p size).x i (.z 2) + 3 / 5 *
        (if (Address.mk i .port1).encode = (keyAddress size (resultInput p)).encode then 1 else 0 : Nat) < _
      split
      · rename_i address
        have matchAddr := AutonomousFeedback.Schedule.PortMemory.address_encode_injective _ _ address
        have rootCell : i = root size := by
          rcases h : resultInput p with j | ⟨⟩
          · have eq := congrArg Address.coordinate matchAddr
            simp [h, keyAddress] at eq
          · simpa only [h, keyAddress, inputCell] using congrArg Address.cell matchAddr
        subst i
        have different : (2 : Port) ≠ 0 := by decide
        have low : Real.log p.returnAmplitude ≤ 0 := Real.log_nonpos
          (by simpa [Parameters.amplitude, different] using (baseAmplitude (size := size) p valid (root size) 2).1.le)
          (by exact_mod_cast valid.2.1.2)
        norm_num [prepared, Parameters.amplitude, different]
        linarith
      · simpa using baseRoom i 2
  · intro i
    have h := (memoryMatch.2 i).2.2 .recovery
    rw [(memoryMatch.2 i).2.1] at h
    norm_num [nativeCoordinate, prepared] at h
    linarith

set_option maxHeartbeats 1000000 in
private theorem refines (p : Parameters N) (valid : p.Valid) : Refines p size := by
  let C := calendar p size
  let start := MarkFeedback.initial N (seed size)
  obtain ⟨u, run, rows, complete, native, replay, deliveries, fires, empty, matched⟩ := histories (size := size) p valid
  have replay' : TransactionReplay C d (· ≤ ·) start rows (endState (size := size) (resultInput p)) := replay
  have sizeRank : AutonomousFeedback.mass (rank (size := size) p).weight start.pending = N + 1 := rfl
  have rowBound : rows.length ≤ N + 1 := by
    have bound := replay'.trace.rank_bound (rank (size := size) p)
    rw [sizeRank, Transaction.word, List.length_map] at bound
    omega
  have safe : SafeMemory Q d B rail (fun _ => 0) (endState (size := size) (resultInput p)) := by
    have h := dated_network_memory Q d B rail W eta₀ C (seed size) (reserve (size := size) p)
      (fun _ => 0) (fun _ => le_rfl) (by decide) (causal (size := size) p valid) (ties (size := size) p)
    exact (h.1 _ (MarkFeedback.certified_projects replay'.trace.certified)).1
  obtain ⟨snapshots, flows⟩ := runRails run (endRail (size := size) p valid u matched)
  refine ⟨⟨reserve (size := size) p⟩, ⟨rank (size := size) p, rfl⟩, causal (size := size) p valid, ties (size := size) p,
    u, run, rows, endState (size := size) (resultInput p), complete, native, replay',
    deliveries, fires, empty, rfl, rowBound, matched, snapshots, flows, safe, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro other word trace
    obtain ⟨suffix, tail, split⟩ := compare_traces (size := size) p trace replay'.trace (by change 1 ≤ 1; decide) rfl
    have length : word.length ≤ N + 1 := by
      have count := congrArg List.length split
      rw [List.length_append, Transaction.word, List.length_map] at count
      omega
    refine ⟨⟨suffix, split⟩, length, ?_, ⟨suffix, tail, split⟩⟩
    intro empty
    cases tail with
    | nil => exact ⟨by simpa using split, rfl⟩
    | cons x rest chosen => rw [empty] at chosen; simp at chosen
  · intro other comparison done
    exact run.observational_unique comparison box (basePhysical (size := size) p valid) complete done

/-- Every checked native ring realizes the frozen dated refinement. -/
theorem native_ring_refinement : NativeRingRefinement := by
  intro N p valid size
  exact refines (size := size) p valid

end NetworkStability.NativeRing
