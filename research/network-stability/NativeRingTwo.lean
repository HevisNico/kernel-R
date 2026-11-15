import NativeRingExamples
import NativeWeakStep

namespace NetworkStability.NativeRing

open KernelR.Hybrid
open PhaseAdmission
open NativeStrong
open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

private theorem two : 2 ≤ 2 := le_rfl

private abbrev aKey : Input 2 := .inl 0
private abbrev bKey : Input 2 := .inl 1
private abbrev rKey : Input 2 := .inr ()

private def keyAddress (key : Input 2) : Address 2 :=
  ⟨inputCell two key, match key with | .inl _ => .port0 | .inr _ => .port1⟩

private theorem gain_eq (p : Parameters 2) (s : Probe 2) :
    MarkFeedback.gain (calendar p two).model s = (keyAddress s.input).encode := by
  rcases s with ⟨date, i | ⟨⟩⟩ <;> rfl

private theorem key_split (key : Input 2) : key = aKey ∨ key = bKey ∨ key = rKey := by
  rcases key with i | ⟨⟩
  · fin_cases i <;> simp
  · simp

private theorem route_shape (p : Parameters 2) (x : Probe 2) :
    (x.input = aKey ∧ (calendar p two).route x =
      [⟨x.due + latency p 0 + p.delay 0, bKey⟩]) ∨
    (x.input = bKey ∧ (calendar p two).route x =
      [⟨x.due + latency p 1 + p.delay 1, rKey⟩]) ∨
    (x.input = rKey ∧ (calendar p two).route x = []) := by
  obtain h | h | h := key_split x.input
  · exact Or.inl ⟨h, by simp [calendar, h, successor]⟩
  · exact Or.inr (Or.inl ⟨h, by simp [calendar, h, successor]⟩)
  · exact Or.inr (Or.inr ⟨h, by simp [calendar, h]⟩)

private def credit (i : Fin 6) (x : Probe 2) : Nat :=
  if i = (keyAddress rKey).encode ∨
    (x.input ≠ rKey ∧ i = (keyAddress bKey).encode) ∨
    (x.input = aKey ∧ i = (keyAddress aKey).encode) then 1 else 0

private theorem footprint_eq (p : Parameters 2) (x : Probe 2) (fire : Bool) (i : Fin 6) :
    MarkFeedback.footprint (calendar p two).model x fire i =
      if fire = false ∧ i = (keyAddress x.input).encode then 1 else 0 := by
  unfold MarkFeedback.footprint
  rw [gain_eq]
  simp [Calendar.model, calendar]

private def reserve (p : Parameters 2) :
    MarkFeedback.Reserve Q (calendar p two).model (seed two) where
  credit := credit
  pays := by
    intro x fire i
    rcases x with ⟨date, key⟩
    obtain h | h | h := key_split key
    all_goals
      subst key
      cases fire <;> fin_cases i <;>
        simp [MarkFeedback.emitted, MarkFeedback.footprint, MarkFeedback.gain, MarkFeedback.recovery,
          Calendar.model, calendar, credit, keyAddress, inputCell, root, successor, Address.encode,
          Coordinate.index, AutonomousFeedback.mass]
  seed_bound := by
    intro i
    change credit i ⟨1, aKey⟩ + 0 ≤ 1
    unfold credit
    split <;> omega

private def rank (p : Parameters 2) :
    MarkFeedback.Rank W eta₀ (calendar p two).model (seed two) where
  weight := occurrenceRank
  positive := by decide
  decreases := by
    intro x
    obtain ⟨key, routes⟩ | ⟨key, routes⟩ | ⟨key, routes⟩ := route_shape p x
    all_goals
      change AutonomousFeedback.mass occurrenceRank ((calendar p two).route x) + eta₀ ≤ occurrenceRank x
      rw [routes]
      simp [AutonomousFeedback.mass, occurrenceRank, key, eta₀]
  seed_bound := by
    norm_num [seed, AutonomousFeedback.mass, occurrenceRank, root]

private theorem route_length (p : Parameters 2) (x : Probe 2) : ((calendar p two).route x).length ≤ 1 := by
  obtain ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ := route_shape p x <;> simp [h]

private theorem selected_rest {p : Probe 2} {rest : List (Probe 2)} {s : State 2}
    (small : s.pending.length ≤ 1) (chosen : s.pending.Perm (p :: rest)) : rest = [] := by
  have h := chosen.length_eq
  simp only [List.length_cons] at h
  exact List.length_eq_zero_iff.mp (by omega)

private theorem small_after (p : Parameters 2) (s : State 2) (x : Probe 2) (error : Int) :
    (MarkFeedback.process (calendar p two).model d s x [] error).pending.length ≤ 1 := by
  change (if MarkFeedback.read (calendar p two).model d s x error then (calendar p two).route x else []).length ≤ 1
  split
  · exact route_length p x
  · simp

private theorem ties (p : Parameters 2) :
    TieAdmissible (calendar p two) d (MarkFeedback.initial 2 (seed two)) := by
  have small (s : State 2) (path : DatedPath (calendar p two) d (MarkFeedback.initial 2 (seed two)) s) :
      s.pending.length ≤ 1 := by
    induction path with
    | refl => decide +kernel
    | tail path move ih =>
      obtain ⟨x, rest, chosen, _, rfl⟩ := move
      obtain rfl := selected_rest ih chosen
      exact small_after p _ x 0
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

private theorem compare_traces (p : Parameters 2) {s a b : State 2} {xs ys}
    (hx : Trace (calendar p two) d (· ≤ ·) s xs a)
    (hy : Trace (calendar p two) d (· ≤ ·) s ys b)
    (small : s.pending.length ≤ 1) (done : b.pending = []) :
    ∃ suffix, Trace (calendar p two) d (· ≤ ·) a suffix b ∧ xs ++ suffix = ys := by
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
          MarkFeedback.read (calendar p two).model d s x error =
            MarkFeedback.read (calendar p two).model d s x error' :=
        (MarkFeedback.read_eq_of_room _ lo hi error within room).trans
          (MarkFeedback.read_eq_of_room _ lo' hi' error' within' room').symm
      have stateEq :
          MarkFeedback.process (calendar p two).model d s x [] error' =
            MarkFeedback.process (calendar p two).model d s x [] error := by
        simp only [MarkFeedback.process, same]
      obtain ⟨suffix, trace, eq⟩ := ih (stateEq ▸ tail') (small_after p s x error) done
      exact ⟨suffix, trace, by rw [List.cons_append, eq, same]⟩

private theorem latency_exact (p : Parameters 2) (i : Fin 2) (strong : StrongAmplitude (p.forwardAmplitude i))
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

private theorem latency_window (p : Parameters 2) (i : Fin 2)
    (strong : StrongAmplitude (p.forwardAmplitude i)) :
    (3 / 10 : ℝ) < latency p i ∧ latency p i < 9 / 10 := by
  have hg : (9 / 5 : ℝ) ≤ (p.forwardAmplitude i : ℝ) ∧ (p.forwardAmplitude i : ℝ) ≤ 2 :=
    ⟨by simpa using (Rat.cast_le (K := ℝ)).2 strong.1, by simpa using (Rat.cast_le (K := ℝ)).2 strong.2⟩
  obtain ⟨t, lo, hi, root, _⟩ := readyPulse_first_learned_crossing (start := 0)
    (initial := 1 / 10) (by norm_num) hg
  have eq := latency_exact p i strong (date := 0) (fire := 0 + t) (by simpa using And.intro lo hi) root
  simpa [show latency p i = t by simpa using eq] using And.intro lo hi

private theorem causal (p : Parameters 2) (delay : ∀ i, p.delay i = 8) : Causal (calendar p two) := by
  intro x y seen
  have positive (i : Fin 2) : 0 < latency p i := by
    by_cases strong : StrongAmplitude (p.forwardAmplitude i)
    · have h := (latency_window p i strong).1
      linarith
    · rw [latency, ite_eq_right strong]
      norm_num
  obtain ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ := route_shape p x <;> rw [h] at seen
  · obtain rfl := List.mem_singleton.mp seen
    change x.due ≤ x.due + latency p 0 + (p.delay 0 : ℝ)
    rw [delay]; norm_num
    linarith [positive 0]
  · obtain rfl := List.mem_singleton.mp seen
    change x.due ≤ x.due + latency p 1 + (p.delay 1 : ℝ)
    rw [delay]; norm_num
    linarith [positive 1]
  · exact (List.not_mem_nil seen).elim

private def parameters (stops : Bool) : Parameters 2 :=
  if stops then stoppingParameters 2 else allStrongParameters 2

private theorem delay_eq (stops : Bool) (i : Fin 2) : (parameters stops).delay i = 8 := by
  cases stops <;> rfl

private theorem launch_strong (stops : Bool) : StrongAmplitude ((parameters stops).forwardAmplitude 0) := by
  cases stops <;> norm_num [parameters, allStrongParameters, stoppingParameters, StrongAmplitude]

private theorem relay_strong : StrongAmplitude ((parameters false).forwardAmplitude 1) := by
  norm_num [parameters, StrongAmplitude, allStrongParameters]

private theorem box : PhysicalBox (nativeParameters 2) (1 / 10) :=
  ⟨KernelR.FutureControls.parameters_box.1, fun _ => KernelR.FutureControls.parameters_box.2 0⟩

private theorem baseAmplitude (stops : Bool) (i : Fin 2) (q : Port) :
    0 < ((parameters stops).amplitude two i q : ℝ) ∧ ((parameters stops).amplitude two i q : ℝ) ≤ 2 := by
  cases stops <;> fin_cases i <;> fin_cases q <;>
    norm_num [Parameters.amplitude, parameters, allStrongParameters, stoppingParameters, root]

private theorem basePhysical (stops : Bool) : PhysicalInvariant (nativeParameters 2) (prepared (parameters stops) two) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    norm_num [prepared, UpperRegion, auxUpper]
  · intro i q
    change Real.log ((parameters stops).amplitude two i q) ≤ Real.log 4
    exact Real.log_le_log (baseAmplitude stops i q).1 ((baseAmplitude stops i q).2.trans (by norm_num))
  · intro i
    norm_num [prepared]
  · intro i
    norm_num [prepared]

private def zeroState (x : Probe 2) : State 2 := ⟨[x], fun _ => 0⟩

private def endState (k : Input 2) : State 2 :=
  ⟨[], fun i => if i = (keyAddress k).encode then 1 else 0⟩

private def birthProbe : Probe 2 := ⟨1, aKey⟩

set_option maxHeartbeats 1000000 in
private theorem one_row (p : Parameters 2) (x : Probe 2) (tx : Row 2)
    (key : tx.probe = x) (interval : tx.lo = -1 ∧ tx.hi = 1)
    (decision : MarkFeedback.read (calendar p two).model d (zeroState x) x 0 = tx.decision)
    (room : RoutedCalendar.HasRoom (MarkFeedback.score (calendar p two).model d (zeroState x) x) (-1) 1)
    (children : MarkFeedback.emitted (calendar p two).model x tx.decision = tx.children)
    (next : State 2) (queue : next.pending = tx.children)
    (writes : ∀ i, next.writes i = MarkFeedback.footprint (calendar p two).model x tx.decision i) :
    TransactionReplay (calendar p two) d (· ≤ ·) (zeroState x) [tx] next := by
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

private theorem root_score (p : Parameters 2) (x : Probe 2) :
    MarkFeedback.score (calendar p two).model d (zeroState x) x =
      (calendar p two).bias x.input .ready := by
  simp [MarkFeedback.score, Calendar.model, calendar, zeroState]

private theorem quietAdmission {p : Parameters 2} {s : Snapshot 2} {token : Delivery 2} {later}
    (a : QuietSourceArrival (nativeParameters 2) (router p two) s token later)
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

private theorem initialMatch (stops : Bool) :
    Matches (parameters stops) two (prepared (parameters stops) two) (zeroState birthProbe) := by
  refine ⟨.refl _, fun i => ⟨rfl, rfl, fun c => ?_⟩⟩
  rw [show (zeroState birthProbe).writes (Address.mk i c).encode = 0 from rfl]
  simp

private theorem replaceMemory {p : Parameters 2} {s u : Snapshot 2} {a b : State 2}
    (h : Matches p two s a) (queue : u.pending = b.pending.map (toDelivery two))
    (writes : b.writes = a.writes)
    (gain : ∀ i q, u.x i (.z q) = s.x i (.z q))
    (recovery : ∀ i, u.x i .b = s.x i .b) : Matches p two u b := by
  refine ⟨.of_eq queue, fun i => ⟨(gain i 1).trans (h.2 i).1, ?_, ?_⟩⟩
  · rw [writes]; exact (h.2 i).2.1
  · intro c
    rw [writes, ← (h.2 i).2.2 c]
    cases c with
    | port0 => exact gain i 0
    | port1 => exact gain i 2
    | recovery => exact recovery i

private theorem stoppedMatch (p : Parameters 2) (x : Probe 2) (s u : Snapshot 2)
    (key : x.input = bKey ∨ x.input = rKey) (h : Matches p two s (zeroState x))
    (queue : u.pending = [])
    (gain : ∀ j q, u.x j (.z q) = s.x j (.z q) +
      if j = inputCell two x.input ∧ q = inputPort x.input then 3 / 5 else 0)
    (rec : ∀ i, u.x i .b = s.x i .b) : Matches p two u (endState x.input) := by
  refine ⟨.of_eq queue, ?_⟩
  intro i
  have base (c : Coordinate) : s.x i (nativeCoordinate c) = (prepared p two).x i (nativeCoordinate c) := by
    simpa [zeroState] using (h.2 i).2.2 c
  have port : inputPort x.input = 0 ∨ inputPort x.input = 2 := by
    obtain b | r := key
    · exact Or.inl (by rw [b]; rfl)
    · exact Or.inr (by rw [r]; rfl)
  have same (c : Coordinate) :
      (Address.mk i c).encode = (keyAddress x.input).encode ↔
        i = inputCell two x.input ∧ nativeCoordinate c = .z (inputPort x.input) := by
    obtain b | r := key
    · rw [b]
      cases c <;> fin_cases i <;> decide +kernel
    · rw [r]
      cases c <;> fin_cases i <;> decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · have notPort : (1 : Port) ≠ inputPort x.input := by
      rcases port with h | h <;> rw [h] <;> decide
    simp [gain, notPort, (h.2 i).1]
  · have none : ¬ (Address.mk i .recovery).encode = (keyAddress x.input).encode := by
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

private theorem finish (p : Parameters 2) (s : Snapshot 2) (x : Input 2)
    (time : s.time < horizon 2) (ready : ∀ i, PreparedSection s i)
    (raw : ∀ i q, s.raw i q = none) (queue : s.pending = [])
    (memoryMatch : Matches p two s (endState x)) :
    ∃ (u : Snapshot 2) (e : Execution (nativeParameters 2) (router p two) s u),
      CompleteThrough e (horizon 2) ∧ NativeRows p two e (endState x) [] (endState x) ∧
      e.deliveries = [] ∧ e.ledger.emissions = [] ∧ u.pending = [] ∧ Matches p two u (endState x) := by
  let T := horizon 2
  have future : ∀ token ∈ s.pending, T < token.due := by simp [queue]
  let flow : Flow (nativeParameters 2) s (quietAt s T) := quietFlow s time
    (fun i => (ready i).ready) (fun i q => ((ready i).auxiliary q).1) raw
    (fun i => by have h := (ready i).charge.2; linarith)
    (fun i q => by have h := ((ready i).auxiliary q).2.2; linarith)
    (fun tok mem => (future tok mem).le)
  let e : Execution (nativeParameters 2) (router p two) s (quietAt s T) := .cons (.flow flow) (.nil _)
  have safe : CompleteThrough e T := by
    refine ⟨rfl, ?_, future⟩
    intro v
    apply ready_no_jump (quietAt s T) (fun i => (ready i).ready) (fun i q => ((ready i).auxiliary q).1) raw
    · intro i
      exact relax_lt (by norm_num) time.le (by have h := (ready i).charge.2; linarith) (by norm_num)
    · intro i q
      exact relax_lt (by norm_num) time.le (by have h := ((ready i).auxiliary q).2.2; linarith) (by norm_num)
    · exact future
  have endpoint : Matches p two (quietAt s T) (endState x) :=
    replaceMemory memoryMatch queue rfl (fun _ _ => rfl) (fun _ => rfl)
  exact ⟨_, e, safe, .done e _ rfl rfl memoryMatch endpoint, rfl, rfl, queue, endpoint⟩

private theorem native_strong_route (stops : Bool) (i : Fin 2) (date fire : ℝ)
    (window : date + 3 / 10 < fire ∧ fire < date + 9 / 10)
    (gate : i = 0 → date = 1) :
    router (parameters stops) two i fire =
      [toDelivery two ⟨fire + 8, successor i⟩] := by
  have openGate : ¬ (i = root two ∧ ¬ (1 ≤ fire ∧ fire < 2)) := by
    rintro ⟨h, blocked⟩
    have actual : date = 1 := gate h
    exact blocked ⟨by linarith [window.1], by linarith [window.2]⟩
  unfold router
  rw [ite_eq_right openGate]
  simp [delay_eq]

private theorem strong_row (stops : Bool) (x : Probe 2) (i : Fin 2)
    (key : x.input = .inl i) (gate : i = 0 → x.due = 1)
    (strong : StrongAmplitude ((parameters stops).forwardAmplitude i))
    (s : Snapshot 2) (preparedAll : ∀ j, PreparedSection s j)
    (physical : PhysicalInvariant (nativeParameters 2) s) (valid : RawValid s)
    (raw : ∀ j q, s.raw j q = none) (resting : s.x i .q = 1 / 10)
    (gain : s.x i (.z 0) = Real.log ((parameters stops).forwardAmplitude i))
    (time : s.time < x.due) (queue : s.pending = [toDelivery two x])
    (matched : Matches (parameters stops) two s (zeroState x)) :
    ∃ (child : Probe 2) (tx : Row 2) (end' : Snapshot 2)
      (intake : QuietSourceArrival (nativeParameters 2) (router (parameters stops) two) s (toDelivery two x) [])
      (pulse : Execution (nativeParameters 2) (router (parameters stops) two) intake.final end'),
      child.input = successor i ∧ child.due = x.due + latency (parameters stops) i + 8 ∧
      end'.time = x.due + 15 / 2 ∧
      end'.pending = [toDelivery two child] ∧
      (∀ j, PreparedSection end' j) ∧ (∀ j q, end'.raw j q = none) ∧
      (∀ j, end'.x j .b = s.x j .b) ∧
      (∀ j q, end'.x j (.z q) = s.x j (.z q)) ∧
      (∀ j, s.x j .q = 1 / 10 → end'.x j .q = 1 / 10) ∧
      PhysicalInvariant (nativeParameters 2) end' ∧ RawValid end' ∧
      tx.probe = x ∧
      (intake.execution.append pulse).deliveries = [toDelivery two x] ∧
      (intake.execution.append pulse).ledger.emissions = Transaction.fires (inputCell two) [tx] ∧
      Matches (parameters stops) two end' (zeroState child) ∧
      TransactionReplay (calendar (parameters stops) two) d (· ≤ ·) (zeroState x) [tx] (zeroState child) ∧
      ∀ {u} (suffix : Execution (nativeParameters 2) (router (parameters stops) two) end' u) rows out,
        NativeRows (parameters stops) two suffix (zeroState child) rows out →
        NativeRows (parameters stops) two (intake.execution.append (pulse.append suffix))
          (zeroState x) (tx :: rows) out := by
  let p := parameters stops
  have hg : (9 / 5 : ℝ) ≤ (p.forwardAmplitude i : ℝ) ∧ (p.forwardAmplitude i : ℝ) ≤ 2 :=
    ⟨by simpa using (Rat.cast_le (K := ℝ)).2 strong.1, by simpa using (Rat.cast_le (K := ℝ)).2 strong.2⟩
  have render : (toDelivery two x).cell = i ∧ (toDelivery two x).port = 0 := by
    simp [toDelivery, key, inputCell, inputPort]
  have strongGain : 9 / 5 ≤ Real.exp (s.x (toDelivery two x).cell (.z (toDelivery two x).port)) ∧
      Real.exp (s.x (toDelivery two x).cell (.z (toDelivery two x).port)) ≤ 2 := by
    rw [render.1, render.2, gain, Real.exp_log (by linarith [hg.1])]
    exact hg
  obtain ⟨intake, pulse, settled, delivered, fired, queued⟩ :=
    strong_transaction_exists (route := router p two) box s (toDelivery two x) []
      physical valid (preparedAll _) strongGain
      ⟨fun j _ => (preparedAll j).ready_coordinates, fun j _ => raw j⟩ (raw _) time queue
      (by simp) (by
        intro fire lo hi
        rw [render.1]
        exact ⟨toDelivery two ⟨fire + 8, successor i⟩,
          native_strong_route stops i x.due fire ⟨lo, hi⟩ gate,
          by
            change x.due + 3 / 10 < fire at lo
            change x.due + 15 / 2 < fire + 8
            linarith⟩)
  let child : Probe 2 := ⟨pulse.fireTime + 8, successor i⟩
  let tx : Row 2 := ⟨x, some pulse.fireTime, [child], -1, 1⟩
  have window : x.due + 3 / 10 < pulse.fireTime ∧ pulse.fireTime < x.due + 9 / 10 := by
    simpa only [intake.date, toDelivery] using pulse.fireBounds
  have actualGain : intake.final.x i (.z 0) = Real.log (p.forwardAmplitude i) :=
    (intake.gain_preserved i 0).trans gain
  have actualCharge : intake.final.x i .q = 1 / 10 := by
    rw [show intake.final.x i .q = quietValues s (toDelivery two x).due i .q from congrFun (congrFun intake.values i) .q]
    simp [quietValues, relax, resting]
  let fire := pulse.fireTime
  have root' : readyPulse (1 / 10) (p.forwardAmplitude i) x.due fire = 1 := by
    have h : readyPulse (intake.final.x (toDelivery two x).cell .q)
        (Real.exp (intake.final.x (toDelivery two x).cell (.z (toDelivery two x).port)))
        intake.final.time fire = 1 := pulse.root
    rw [render.1, render.2, actualGain, actualCharge, Real.exp_log (by linarith [hg.1]), intake.date] at h
    exact h
  have fireDate := latency_exact p i strong window root'
  have childNative : pulse.child = toDelivery two child := by
    have same := pulse.routeAtFire
    have same' : router p two (toDelivery two x).cell fire = [pulse.child] := same
    let nativeChild := pulse.child
    change router p two (toDelivery two x).cell fire = [nativeChild] at same'
    rw [render.1, native_strong_route stops i x.due fire window gate] at same'
    exact (List.cons.inj same').1.symm
  have nextQ : pulse.final.pending = [toDelivery two child] := by simpa [childNative] using queued
  have gains (j : Fin 2) (q : Port) : pulse.final.x j (.z q) = s.x j (.z q) :=
    (pulse.gains j q).trans (intake.gain_preserved j q)
  have recovery (j : Fin 2) : pulse.final.x j .b = s.x j .b :=
    (pulse.recoveryPreserved j).trans (intake.recovery_preserved j)
  have match' := replaceMemory matched (b := zeroState child) nextQ rfl gains recovery
  have ready (j : Fin 2) : PreparedSection pulse.final j := by
    by_cases h : j = (toDelivery two x).cell
    · subst j; exact pulse.selectedReady
    · have r := pulse.spectatorReady j h
      exact ⟨r.ready, r.charge, by rw [recovery]; exact (preparedAll j).recovery, r.auxiliary⟩
  have qRest (j : Fin 2) (h : s.x j .q = 1 / 10) : pulse.final.x j .q = 1 / 10 := by
    by_cases eq : j = (toDelivery two x).cell
    · subst j; exact pulse.selectedCharge
    · rw [show pulse.final.x j .q = quietValues intake.final pulse.final.time j .q from
        congrFun (pulse.spectatorFinal j eq) .q]
      have rest : intake.final.x j .q = 1 / 10 := by
        rw [show intake.final.x j .q = quietValues s (toDelivery two x).due j .q from
          congrFun (congrFun intake.values j) .q]
        simp [quietValues, relax, h]
      simp [quietValues, relax, rest]
  have score : MarkFeedback.score (calendar p two).model d (zeroState x) x = 2 := by
    rw [root_score]
    simp [calendar, key, show StrongAmplitude (p.forwardAmplitude i) from strong]
  have routes : (calendar p two).route x = [child] := by
    simp [calendar, key, child, fireDate, show p.delay i = 8 from delay_eq stops i]
  have replay : TransactionReplay (calendar p two) d (· ≤ ·) (zeroState x) [tx] (zeroState child) :=
    one_row p x tx rfl ⟨rfl, rfl⟩ (by simp [MarkFeedback.read, score, tx, Transaction.decision])
      (by rw [score]; norm_num [RoutedCalendar.HasRoom])
      (by simpa [MarkFeedback.emitted, Calendar.model, tx, Transaction.decision] using routes)
      _ rfl (fun j => by simp [zeroState, footprint_eq, tx, Transaction.decision])
  refine ⟨child, tx, pulse.final, intake, pulse.execution, rfl, ?_, settled, nextQ,
    ready, pulse.inactive, recovery, gains, qRest, pulse.physical, pulse.rawValid, rfl,
    delivered, ?_, match', replay, ?_⟩
  · change pulse.fireTime + 8 = x.due + latency p i + 8
    rw [fireDate]
  · exact fired
  · intro u suffix rows out tail
    exact .step intake.execution pulse.execution suffix
      (quietAdmission intake (preparedAll _).ready) intake.date
      (by simpa only [intake.date, toDelivery, tx] using intake.raw_active)
      intake.emissions pulse.deliveries pulse.emissions
      (by
        have route := (native_strong_route stops i x.due pulse.fireTime window gate).symm
        simpa [tx, child, key, inputCell] using route)
      (by simpa [tx] using window)
      settled ready pulse.inactive ⟨rfl, rfl⟩ matched match' replay tail

private theorem weak_row (stops : Bool) (x : Probe 2)
    (key : x.input = bKey ∨ x.input = rKey)
    (weak : x.input = bKey → stops = true)
    (s : Snapshot 2) (preparedAll : ∀ j, PreparedSection s j)
    (physical : PhysicalInvariant (nativeParameters 2) s) (valid : RawValid s)
    (raw : ∀ j q, s.raw j q = none)
    (gain : s.x (inputCell two x.input) (.z (inputPort x.input)) = 0)
    (time : s.time < x.due) (queue : s.pending = [toDelivery two x])
    (date : x.due + 15 / 2 < horizon 2)
    (matched : Matches (parameters stops) two s (zeroState x)) :
    ∃ (u : Snapshot 2)
      (run : Execution (nativeParameters 2) (router (parameters stops) two) s u),
      CompleteThrough run (horizon 2) ∧
      NativeRows (parameters stops) two run (zeroState x) [⟨x, none, [], -1, 1⟩] (endState x.input) ∧
      TransactionReplay (calendar (parameters stops) two) d (· ≤ ·)
        (zeroState x) [⟨x, none, [], -1, 1⟩] (endState x.input) ∧
      run.deliveries = [toDelivery two x] ∧ run.ledger.emissions = [] ∧
      u.pending = [] ∧ Matches (parameters stops) two u (endState x.input) := by
  let p := parameters stops
  let token := toDelivery two x
  let tx : Row 2 := ⟨x, none, [], -1, 1⟩
  obtain ⟨intake⟩ := quiet_source_arrival_exists (route := router p two) box s token []
    physical valid (fun i => (preparedAll i).ready_coordinates) raw time queue (by simp)
  have prep (j : Fin 2) : PreparedSection intake.final j :=
    ⟨(intake.ready j).ready, (intake.ready j).charge,
      by rw [intake.recovery_preserved]; exact (preparedAll j).recovery, (intake.ready j).auxiliary⟩
  have actual : Real.exp (intake.final.x token.cell (.z token.port)) ≤ 1 := by
    rw [intake.gain_preserved]
    change Real.exp (s.x (inputCell two x.input) (.z (inputPort x.input))) ≤ 1
    rw [gain, Real.exp_zero]
  obtain ⟨settled, pulse, clock, stillPending, noDelivery, noFire, gains, rec, ready, inactive⟩ :=
    weak_step_exists (route := router p two) box intake.final token.cell token.port intake.physical
      intake.raw_valid (prep _) actual intake.raw_active (fun q ne => intake.raw_other _ _ (Or.inr ne))
      ⟨fun j _ => intake.ready j, fun j ne q => intake.raw_other j q (Or.inl ne)⟩
      (by rw [intake.pending]; simp)
  have done : settled.pending = [] := stillPending.trans intake.pending
  have clock' : settled.time = x.due + 15 / 2 := clock.trans (congrArg (· + 15 / 2) intake.date)
  have afterGain (j : Fin 2) (q : Port) : settled.x j (.z q) = s.x j (.z q) +
      if j = inputCell two x.input ∧ q = inputPort x.input then 3 / 5 else 0 := by
    rw [gains, intake.gain_preserved]
    rfl
  have afterRec (j : Fin 2) : settled.x j .b = s.x j .b :=
    (rec j).trans (intake.recovery_preserved j)
  have matched' := stoppedMatch p x s settled key matched done afterGain afterRec
  have score : MarkFeedback.score (calendar p two).model d (zeroState x) x = -2 := by
    rw [root_score]
    obtain h | h := key
    · have branch := weak h
      subst stops
      norm_num [p, calendar, h, parameters, stoppingParameters, StrongAmplitude]
    · simp [calendar, h]
  have replay : TransactionReplay (calendar p two) d (· ≤ ·) (zeroState x) [tx] (endState x.input) :=
    one_row p x tx rfl ⟨rfl, rfl⟩ (by simp [MarkFeedback.read, score, tx, Transaction.decision])
      (by rw [score]; norm_num [RoutedCalendar.HasRoom]) rfl _ rfl (fun i => by simp [endState, footprint_eq, tx, Transaction.decision])
  obtain ⟨u, idle, complete, tail, idleDelivery, idleFire, empty, endpoint⟩ :=
    finish p settled x.input (clock'.trans_lt date) (fun j => ready j (prep j)) inactive done matched'
  let run := intake.execution.append (pulse.append idle)
  have native : NativeRows p two run (zeroState x) [tx] (endState x.input) :=
    .step intake.execution pulse idle (quietAdmission intake (preparedAll _).ready) intake.date
      (by simpa only [intake.date, toDelivery, tx, token] using intake.raw_active) intake.emissions noDelivery
      noFire rfl (by simp [tx]) clock' (fun j => ready j (prep j)) inactive
      ⟨rfl, rfl⟩ matched matched' replay tail
  exact ⟨u, run, complete, native, replay,
    by simp [run, Execution.deliveries_append, intake.deliveries, noDelivery, idleDelivery, token],
    by simp [run, Execution.emissions_append, intake.emissions, noFire, idleFire], empty, endpoint⟩

private def PartialHistory (p : Parameters 2) (s : Snapshot 2) (start : State 2) (k : Input 2) : Prop :=
  ∃ (u : Snapshot 2) (run : Execution (nativeParameters 2) (router p two) s u)
    (rows : List (Row 2)),
    CompleteThrough run (horizon 2) ∧ NativeRows p two run start rows (endState k) ∧
    TransactionReplay (calendar p two) d (· ≤ ·) start rows (endState k) ∧
    rows.map (fun tx => toDelivery two tx.probe) = run.deliveries ∧
    Transaction.fires (inputCell two) rows = run.ledger.emissions ∧
    u.pending = [] ∧ Matches p two u (endState k)

private theorem weak_history (stops : Bool) (x : Probe 2)
    (key : x.input = bKey ∨ x.input = rKey) (weak : x.input = bKey → stops = true)
    (s : Snapshot 2) (ready : ∀ j, PreparedSection s j)
    (physical : PhysicalInvariant (nativeParameters 2) s) (valid : RawValid s)
    (raw : ∀ j q, s.raw j q = none)
    (gain : s.x (inputCell two x.input) (.z (inputPort x.input)) = 0)
    (time : s.time < x.due) (queue : s.pending = [toDelivery two x])
    (endTime : x.due + 15 / 2 < horizon 2)
    (matched : Matches (parameters stops) two s (zeroState x)) :
    PartialHistory (parameters stops) s (zeroState x) x.input := by
  obtain ⟨u, run, complete, native, replay, delivered, emits, empty, endpoint⟩ :=
    weak_row stops x key weak s ready physical valid raw gain time queue endTime matched
  exact ⟨u, run, [_], complete, native, replay, delivered.symm, emits.symm, empty, endpoint⟩

private theorem prepend_history {p : Parameters 2} {s v u : Snapshot 2} {x y : Probe 2}
    (tx : Row 2) (head : Execution (nativeParameters 2) (router p two) s v)
    (pulse : Execution (nativeParameters 2) (router p two) v u)
    (probe : tx.probe = x)
    (delivered : (head.append pulse).deliveries = [toDelivery two x])
    (emits : (head.append pulse).ledger.emissions = Transaction.fires (inputCell two) [tx])
    (replay : TransactionReplay (calendar p two) d (· ≤ ·) (zeroState x) [tx] (zeroState y))
    (prepend : ∀ {last} (e : Execution (nativeParameters 2) (router p two) u last) rows out,
      NativeRows p two e (zeroState y) rows out →
      NativeRows p two (head.append (pulse.append e)) (zeroState x) (tx :: rows) out)
    {k : Input 2} (tail : PartialHistory p u (zeroState y) k) :
    PartialHistory p s (zeroState x) k := by
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
      (List.filterMap_append (l := [tx]) (l' := rows) (f := fun tx : Row 2 =>
        tx.fireDate.map (fun t => (inputCell two tx.probe.input, t))))

set_option maxHeartbeats 2500000 in
private theorem histories (stops : Bool) :
    PartialHistory (parameters stops) (prepared (parameters stops) two)
      (zeroState birthProbe) (if stops then bKey else rKey) := by
  let p := parameters stops
  let s := prepared p two
  have startReady (j : Fin 2) : PreparedSection s j := by
    refine ⟨rfl, by norm_num [s, prepared], by norm_num [s, prepared], fun q => ?_⟩
    exact ⟨rfl, by norm_num [s, prepared, RestBand]⟩
  have startValid : RawValid s := by intro i q t h; cases h
  have startGain : s.x 0 (.z 0) = Real.log (p.forwardAmplitude 0) := rfl
  have startRest : ∀ j, s.x j .q = 1 / 10 := fun _ => rfl
  obtain ⟨child, tx, cut, intake, pulse, childKey, due, clock, queue, ready, raw, recovery,
      gains, qRest, physical, valid, probe, delivered, emits, memoryMatch, replay, prepend⟩ :=
    strong_row stops birthProbe 0 rfl (fun _ => rfl) (launch_strong stops) s startReady
      (basePhysical stops) startValid (fun _ _ => rfl) (startRest 0) startGain
      (by norm_num [s, prepared, birthProbe]) rfl (initialMatch stops)
  have childPort : child.input = bKey := childKey
  have bounds := latency_window p 0 (launch_strong stops)
  have childDate : 9 < child.due ∧ child.due < 10 := by
    rw [due]
    change 9 < 1 + latency p 0 + 8 ∧ 1 + latency p 0 + 8 < 10
    constructor <;> linarith [bounds.1, bounds.2]
  have cutTime : cut.time < child.due := by
    rw [clock]
    change 1 + 15 / 2 < child.due
    linarith [childDate.1]
  apply prepend_history tx intake.execution pulse probe delivered emits replay prepend
  cases stops with
  | true =>
    have startWeak : cut.x (inputCell two child.input) (.z (inputPort child.input)) = 0 := by
      rw [gains, childPort]
      norm_num [s, p, prepared, Parameters.amplitude, parameters, stoppingParameters,
        allStrongParameters, inputCell, inputPort]
    have tail := weak_history true child (Or.inl childPort) (fun _ => rfl) cut
      ready physical valid raw startWeak cutTime queue
      (by change child.due + 15 / 2 < 10 * ((2 : ℝ) + 1); linarith [childDate.2]) memoryMatch
    rwa [childPort] at tail
  | false =>
    have startStrong : cut.x 1 (.z 0) = Real.log ((parameters false).forwardAmplitude 1) :=
      (gains 1 0).trans rfl
    obtain ⟨ret, relayTx, relayCut, relayIntake, relayPulse, retKey, retDue, relayClock,
      relayQueue, relayReady, relayRaw, _, relayGains, _, relayPhysical, relayValid,
      relayProbe, relayDelivery, relayFires, relayMatches, relayReplay, relayPrepend⟩ :=
      strong_row false child 1 childPort (fun h => (by decide : (1 : Fin 2) ≠ 0) h |>.elim) relay_strong cut ready physical valid raw
        (qRest 1 (startRest 1)) startStrong cutTime queue memoryMatch
    have retPort : ret.input = rKey := retKey
    have retBounds := latency_window (parameters false) 1 relay_strong
    have returnTime : relayCut.time < ret.due := by
      rw [relayClock, retDue]
      linarith [retBounds.1]
    have endTime : ret.due + 15 / 2 < horizon 2 := by
      rw [retDue]
      change child.due + latency (parameters false) 1 + 8 + 15 / 2 < 10 * ((2 : ℝ) + 1)
      linarith [childDate.2, retBounds.2]
    have returnGain : relayCut.x (inputCell two ret.input) (.z (inputPort ret.input)) = 0 := by
      rw [retPort, relayGains, gains]
      norm_num [s, p, prepared, Parameters.amplitude, parameters, allStrongParameters,
        inputCell, inputPort, root]
    have tail := weak_history false ret (Or.inr retPort) (by rw [retPort]; simp) relayCut
      relayReady relayPhysical relayValid relayRaw returnGain returnTime relayQueue endTime relayMatches
    have stitched := prepend_history relayTx relayIntake.execution relayPulse relayProbe relayDelivery
      relayFires relayReplay relayPrepend tail
    rwa [retPort] at stitched

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

private theorem runRails {s u : Snapshot 2} {r : Router 2}
    (e : Execution (nativeParameters 2) r s u) (rail : BelowRail u.x) :
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

private theorem endRail (stops : Bool) (last : Snapshot 2)
    (memoryMatch : Matches (parameters stops) two last (endState (if stops then bKey else rKey))) :
    BelowRail last.x := by
  constructor
  · intro i p
    change last.x i (.z p) < Real.log 4
    have doseRoom : (3 / 5 : ℝ) < Real.log 4 := by linarith [KernelR.log_four_bounds.1]
    have trainedRoom : Real.log (2 : ℝ) < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have unused := (memoryMatch.2 i).1
    have forward := (memoryMatch.2 i).2.2 .port0
    have ret := (memoryMatch.2 i).2.2 .port1
    cases stops <;> fin_cases i <;> fin_cases p <;>
      norm_num [nativeCoordinate, prepared, Parameters.amplitude, parameters, allStrongParameters,
        stoppingParameters, root, unitDose, endState, keyAddress, inputCell, Address.encode, Coordinate.index]
        at unused forward ret ⊢ <;>
      first
      | linarith
      | have h : Real.log (37 / 20 : ℝ) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
        linarith
  · intro i
    have h := (memoryMatch.2 i).2.2 .recovery
    rw [(memoryMatch.2 i).2.1] at h
    norm_num [nativeCoordinate, prepared] at h
    linarith

private theorem result_eq (stops : Bool) : resultInput (parameters stops) = if stops then bKey else rKey := by
  cases stops <;> decide +kernel

private theorem refines_two (stops : Bool) : Refines (parameters stops) two := by
  let p := parameters stops
  let C := calendar p two
  let start := MarkFeedback.initial 2 (seed two)
  obtain ⟨u, run, rows, complete, native, replay, deliveries, fires, empty, matched⟩ := histories stops
  have replay' : TransactionReplay C d (· ≤ ·) start rows (endState (if stops then bKey else rKey)) := replay
  have sizeRank : AutonomousFeedback.mass (rank p).weight start.pending = 3 := rfl
  have rowBound : rows.length ≤ 3 := by
    have bound := replay'.trace.rank_bound (rank p)
    rw [sizeRank, Transaction.word, List.length_map] at bound
    omega
  have safe : SafeMemory Q d B rail (fun _ => 0) (endState (if stops then bKey else rKey)) := by
    have h := dated_network_memory Q d B rail W eta₀ C (seed two) (reserve p)
      (fun _ => 0) (fun _ => le_rfl) (by decide) (causal p (delay_eq stops)) (ties p)
    exact (h.1 _ (MarkFeedback.certified_projects replay'.trace.certified)).1
  obtain ⟨snapshots, flows⟩ := runRails run (endRail stops u matched)
  refine ⟨⟨reserve p⟩, ⟨rank p, rfl⟩, causal p (delay_eq stops), ties p,
    u, run, rows, endState (if stops then bKey else rKey), complete, native, replay',
    deliveries, fires, empty, rfl, rowBound, matched, snapshots, flows, safe, ?_, ?_, ?_⟩
  · intro i
    simp only [endState, resultAddress, result_eq, keyAddress]
    cases stops <;> rfl
  · intro other word trace
    obtain ⟨suffix, tail, split⟩ := compare_traces p trace replay'.trace (by change 1 ≤ 1; decide) rfl
    have length : word.length ≤ 3 := by
      have count := congrArg List.length split
      rw [List.length_append, Transaction.word, List.length_map] at count
      omega
    refine ⟨⟨suffix, split⟩, length, ?_, ⟨suffix, tail, split⟩⟩
    intro empty
    cases tail with
    | nil => exact ⟨by simpa using split, rfl⟩
    | cons x rest chosen => rw [empty] at chosen; simp at chosen
  · intro other comparison done
    exact run.observational_unique comparison box (basePhysical stops) complete done

/-- The launch and relay transmit, then the native return port records one dose. -/
theorem all_strong_two_refines : Refines (allStrongParameters 2) (by decide) :=
  refines_two false

/-- The weak relay learns once and the return port is never admitted. -/
theorem stopping_two_refines : Refines (stoppingParameters 2) (by decide) :=
  refines_two true

end NetworkStability.NativeRing
