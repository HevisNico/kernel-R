import NativeRefinement
import PhaseAdmission

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid
open PhaseAdmission (Phase)
open AutonomousFeedback.Schedule (Config SafeMemory)

structure Admission (N : Nat) where
  token : Delivery N
  mode : MainMode

/-- The mode comes from the source of the actual arrival jump. It is
insensitive to subdivision of flows into smaller steps. -/
def jumpAdmissions {n route s u} (j : @Jump n route s u) : List (Admission n) := by
  cases j
  case arrive token _ _ _ _ _ => exact [⟨token, s.main token.cell⟩]
  all_goals exact []

def moveAdmissions {n θ route s u} (m : @KernelR.Hybrid.Move n θ route s u) :
    List (Admission n) :=
  match m with
  | .flow _ => []
  | .jump j => jumpAdmissions j

def nativeAdmissions {n θ route s u} (run : @Execution n θ route s u) :
    List (Admission n) :=
  match run with
  | .nil _ => []
  | .cons step rest => moveAdmissions step ++ nativeAdmissions rest

theorem admissions_deliveries {n θ route s u} (run : @Execution n θ route s u) :
    (nativeAdmissions run).map Admission.token = run.deliveries := by
  induction run with
  | nil => rfl
  | cons step rest ih =>
    simp only [nativeAdmissions, Execution.deliveries, List.map_append, ih]
    cases step with
    | flow f => rfl
    | jump j => cases j <;> rfl

/-- Membership retains an exact split at the corresponding arrival jump.
The snapshot supplies the native mode at this particular queue occurrence. -/
theorem admission_cut {n θ route s u} (run : @Execution n θ route s u)
    (a : Admission n) (mem : a ∈ nativeAdmissions run) :
    ∃ (v w : Snapshot n) (head : Execution θ route s v) (arrival : Jump route v w)
      (tail : Execution θ route w u),
      run = head.append (.cons (.jump arrival) tail) ∧
      arrival.deliveries = [a.token] ∧ v.main a.token.cell = a.mode ∧ v.time = a.token.due := by
  induction run with
  | nil => simp [nativeAdmissions] at mem
  | @cons s v u move rest ih =>
    rcases List.mem_append.mp mem with first | later
    · cases move with
      | flow f => simp [moveAdmissions] at first
      | jump j =>
        cases j with
        | arrive token before after queued due free =>
          have eq : a = ⟨token, s.main token.cell⟩ := List.mem_singleton.mp first
          subst a
          exact ⟨s, _, .nil _, .arrive s token before after queued due free, rest,
            rfl, rfl, rfl, due.symm⟩
        | _ => simp [moveAdmissions, jumpAdmissions] at first
    · obtain ⟨b, c, head, arrival, tail, shape, paid, phase, date⟩ := ih later
      exact ⟨b, c, .cons move head, arrival, tail, by rw [shape]; rfl, paid, phase, date⟩

theorem admissions_raw_separated {n θ route s u} (run : @Execution n θ route s u) :
    (nativeAdmissions run).Pairwise (fun a b =>
      a.token.cell = b.token.cell → a.token.port = b.token.port → a.token.due + 1 ≤ b.token.due) := by
  have gap : ((nativeAdmissions run).map Admission.token).Pairwise
      (fun a b => a.cell = b.cell → a.port = b.port → a.due + 1 ≤ b.due) := by
    rw [admissions_deliveries]
    exact actual_raw_windows_disjoint run
  exact List.pairwise_map.mp gap

/-- All admitted occurrences in the two-cell witness retain their true
dates and modes, including occurrences on either side of the birth cut. -/
theorem nominal_admission_words (epoch : NominalEpoch) :
    (nativeAdmissions epoch.staged.before).map Admission.token = epoch.staged.before.deliveries ∧
    (nativeAdmissions epoch.staged.after).map Admission.token = epoch.staged.after.deliveries ∧
    (nativeAdmissions epoch.staged.after).Pairwise
      (fun a b => a.token.cell = b.token.cell → a.token.port = b.token.port →
        a.token.due + 1 ≤ b.token.due) := by
  exact ⟨admissions_deliveries _, admissions_deliveries _, admissions_raw_separated _⟩

/-- The observed finite calendar keys phases by the full physical address
and the due date. An unobserved key has no assigned native mode. -/
noncomputable def recordedMode (admissions : List (Admission n)) (token : Delivery n) :
    Option MainMode := by
  classical
  exact (admissions.find? (fun a => decide (a.token = token))).map Admission.mode

private theorem recordedMode_of_unique (admissions : List (Admission n)) (a : Admission n)
    (mem : a ∈ admissions)
    (unique : ∀ b ∈ admissions, b.token = a.token → b.mode = a.mode) :
    recordedMode admissions a.token = some a.mode := by
  classical
  induction admissions with
  | nil => simp at mem
  | cons b rest ih =>
    by_cases same : b.token = a.token
    · simp [recordedMode, same, unique b (by simp) same]
    · have later : a ∈ rest := by
        rcases List.mem_cons.mp mem with eq | inTail
        · exact (same (congrArg Admission.token eq.symm)).elim
        · exact inTail
      simpa [recordedMode, same] using
        ih later (fun c hc eq => unique c (List.mem_cons_of_mem _ hc) eq)

/-- Same-port raw separation implies there is at most one occurrence at
each (cell, port, due date), so calendar lookup returns its actual mode. -/
theorem recordedMode_recovers_admission {n θ route s u} (run : @Execution n θ route s u)
    (a : Admission n) (mem : a ∈ nativeAdmissions run) :
    recordedMode (nativeAdmissions run) a.token = some a.mode := by
  apply recordedMode_of_unique _ a mem
  have separated := admissions_raw_separated run
  have distinct : ((nativeAdmissions run).map Admission.token).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    apply List.pairwise_map.mpr
    refine separated.imp ?_
    intro x y gap same
    have h := gap (congrArg Delivery.cell same) (congrArg Delivery.port same)
    rw [same] at h
    linarith
  intro b hb same
  have injection : List.Pairwise (fun x y : Admission n => x.token ≠ y.token) (nativeAdmissions run) :=
    List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp distinct)
  have mode_unique (xs : List (Admission n))
      (distinct : xs.Pairwise (fun x y => x.token ≠ y.token))
      (ha : a ∈ xs) (hb : b ∈ xs) : b = a := by
    induction xs with
    | nil => simp at ha
    | cons x rest ih =>
      obtain ⟨head, restDistinct⟩ := List.pairwise_cons.mp distinct
      rcases List.mem_cons.mp ha with rfl | ma
      · rcases List.mem_cons.mp hb with rfl | mb
        · rfl
        · exact (head b mb same.symm).elim
      · rcases List.mem_cons.mp hb with rfl | mb
        · exact (head a ma same).elim
        · exact ih restDistinct ma mb
  exact congrArg Admission.mode (mode_unique _ injection mem hb)

/-- A motion-free delivery jump preserves the mode, so the occupancy check
uses the same phase whether the observation is made just before or after
the jump. -/
theorem admission_mode_after {n θ route s u} (run : @Execution n θ route s u)
    (a : Admission n) (mem : a ∈ nativeAdmissions run) :
    ∃ v : Snapshot n, v.main a.token.cell = a.mode ∧ v.time = a.token.due ∧
      v.raw a.token.cell a.token.port = some a.token.due := by
  obtain ⟨_, v, _, jump, _, _, issued, mode, _⟩ := admission_cut run a mem
  have present : a.token ∈ jump.deliveries := by rw [issued]; simp
  obtain ⟨_, _, _, due, _, shape⟩ := jump.delivery_snapshot a.token present
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [shape]
    exact mode
  · rw [shape]
    exact due.symm
  · rw [shape, due]
    simp [setRaw]


open PhaseAdmission (Calendar Occurrence Trace)

private noncomputable def forwardCalendar (cut : ℝ) : Calendar 2 ℝ Unit where
  cell := fun _ => 1
  secondPort := fun _ => false
  phase := fun _ due => if due < cut then .ready else .slow
  bias := fun _ phase => if phase = .ready then 2 else -2
  recoveryWeight := fun _ _ => 0
  learn := fun _ _ => false
  mark := fun _ phase fire => phase == .slow && !fire
  route := fun _ => []

private theorem forward_score (cut : ℝ) (s : Config 6 (Occurrence ℝ Unit))
    (p : Occurrence ℝ Unit) :
    MarkFeedback.score (forwardCalendar cut).model 0 s p = if p.due < cut then 2 else -2 := by
  classical
  unfold MarkFeedback.score
  by_cases h : p.due < cut <;> simp [PhaseAdmission.Calendar.model, forwardCalendar, h]

private theorem forward_footprint (cut : ℝ) (p : Occurrence ℝ Unit) (fire : Bool) (i : Fin 6) :
    MarkFeedback.footprint (forwardCalendar cut).model p fire i ≤ 1 := by
  unfold MarkFeedback.footprint
  simp only [PhaseAdmission.Calendar.model, forwardCalendar, Bool.false_eq_true, and_false, false_and,
    ite_false, Nat.zero_add]
  split <;> split <;> decide

private theorem forward_admissible (cut : ℝ) (seed : List (Occurrence ℝ Unit)) :
    MarkFeedback.Admissible (forwardCalendar cut).model 0 (MarkFeedback.initial 2 seed) := by
  intro s _
  right
  intro p _ q _ _ _ fire
  have displacement : MarkFeedback.displacement (forwardCalendar cut).model 0 p q fire = 0 := by
    simp [MarkFeedback.displacement, PhaseAdmission.Calendar.model, forwardCalendar]
  rw [displacement]
  unfold RoutedCalendar.HasRoom
  omega

/-- The phase of each of the two actual B receipts is attached to its date
before any reordering of the guarded system. The branch and endpoint
comparison uses the native cuts, including the SLOW MARK completion. -/
theorem ProtectedReceipt.dated_pair {last : Snapshot 2} {staged : NominalStaged last}
    (w : ProtectedReceipt staged) :
    ∃ C : Calendar 2 ℝ Unit, ∃ a b : Occurrence ℝ Unit, ∃ out : Config 6 (Occurrence ℝ Unit),
      a.due = w.readySource.time ∧ b.due = w.receipt.time ∧
      C.phase a.input a.due = .ready ∧ C.phase b.input b.due = .slow ∧
      Trace C 0 (· ≤ ·) (MarkFeedback.initial 2 [a, b]) [(a, true), (b, false)] out ∧
      out.pending = [] ∧
      (∀ s word, Trace C 0 (· ≤ ·) (MarkFeedback.initial 2 [a, b]) word s →
        SafeMemory 2 0 0 1 (fun _ => 0) s) ∧
      (∀ s word, Trace C 0 (· ≤ ·) (MarkFeedback.initial 2 [a, b]) word s →
        s.pending = [] → s.writes = out.writes) ∧
      w.trigger.ledger.emissions = [(1, w.fromFire.time)] ∧ w.finish.emissionTimes 1 = [] ∧
      (w.completed.x 1 (.z 1) = w.readySource.x 1 (.z 1) +
        unitDose .port0 * (out.writes (MarkFeedback.gain C.model a) : ℝ)) ∧
      (w.completed.x 1 .b = w.readySource.x 1 .b +
        unitDose .recovery * (out.writes (MarkFeedback.recovery C.model a) : ℝ)) := by
  classical
  let C := forwardCalendar w.receipt.time
  let a : Occurrence ℝ Unit := ⟨w.readySource.time, ()⟩
  let b : Occurrence ℝ Unit := ⟨w.receipt.time, ()⟩
  let seed := [a, b]
  let s := MarkFeedback.initial 2 seed
  let mid := MarkFeedback.process C.model 0 s a [b] 0
  let out := MarkFeedback.process C.model 0 mid b [] 0
  have gap : a.due < b.due := w.fires_after_arrival.trans w.receipt_after_fire
  have sa : ∀ v, MarkFeedback.score C.model 0 v a = 2 := by
    intro v
    rw [forward_score, ite_eq_left gap]
  have sb : ∀ v, MarkFeedback.score C.model 0 v b = -2 := by
    intro v
    rw [forward_score, ite_eq_right (lt_irrefl b.due)]
  have ra : MarkFeedback.read C.model 0 s a 0 = true := by simp [MarkFeedback.read, sa]
  have rb : MarkFeedback.read C.model 0 mid b 0 = false := by simp [MarkFeedback.read, sb]
  have dateA : PhaseAdmission.Earliest (· ≤ ·) a [b] := by
    intro p hp
    cases List.mem_singleton.mp hp
    exact gap.le
  have roomA : RoutedCalendar.HasRoom (MarkFeedback.score C.model 0 s a) (-1) 1 := by
    rw [sa]
    right
    decide
  have roomB : RoutedCalendar.HasRoom (MarkFeedback.score C.model 0 mid b) (-1) 1 := by
    rw [sb]
    left
    decide
  have midPending : mid.pending = [b] := by
    simp [mid, MarkFeedback.process, MarkFeedback.emitted, C, forwardCalendar,
      PhaseAdmission.Calendar.model]
  have trace : Trace C 0 (· ≤ ·) s [(a, true), (b, false)] out := by
    simpa only [ra, rb] using
      (Trace.cons a [b] (List.Perm.refl _) dateA (-1) 1 0 (by decide) roomA
        (Trace.cons b [] (List.Perm.of_eq midPending) (by simp [PhaseAdmission.Earliest])
          (-1) 1 0 (by decide) roomB (.nil out)))
  have exhausted : out.pending = [] := by
    simp [out, MarkFeedback.process, MarkFeedback.emitted, rb]
  have cert : MarkFeedback.Reserve 2 C.model seed := by
    refine ⟨fun _ _ => 1, ?_, ?_⟩
    · intro p fire i
      have noRoute : MarkFeedback.emitted C.model p fire = [] := by cases fire <;> rfl
      rw [noRoute]
      simpa [AutonomousFeedback.mass] using forward_footprint _ p fire i
    · intro i
      change 2 ≤ 2
      decide
  have rank : MarkFeedback.Rank 1 1 C.model seed := by
    refine ⟨fun _ => 1, by decide, fun _ => Nat.le_refl 1, Nat.le_refl 2⟩
  obtain ⟨safe, _, _, _, _, _, _, _, terminal⟩ :=
    PhaseAdmission.network_memory 2 0 0 1 1 1 C seed cert (fun _ => 0)
      (fun _ => by decide) (by decide) (forward_admissible _ _) (· ≤ ·) (fun _ => -1) (fun _ => 1)
  refine ⟨C, a, b, out, rfl, rfl, ?_, ?_, trace, exhausted, safe, ?_, w.fire_word, w.silence, ?_, ?_⟩
  · exact ite_eq_left gap
  · simp [C, forwardCalendar, b]
  · intro endState word h done
    exact (terminal rank).2 _ _ _ _ h trace done exhausted
  · have zero : out.writes (MarkFeedback.gain C.model a) = 0 := by
      unfold out
      simp only [MarkFeedback.process, rb]
      unfold mid
      simp only [MarkFeedback.process, ra]
      simp [s, MarkFeedback.initial, MarkFeedback.footprint, MarkFeedback.gain, MarkFeedback.recovery,
        PhaseAdmission.Calendar.model, C, forwardCalendar,
        AutonomousFeedback.Schedule.PortMemory.Address.encode,
        AutonomousFeedback.Schedule.PortMemory.Coordinate.index]
    rw [zero, Nat.cast_zero, mul_zero, add_zero]
    exact (w.gain_preserved 1).trans w.same_gain
  · have one : out.writes (MarkFeedback.recovery C.model a) = 1 := by
      unfold out
      simp only [MarkFeedback.process, rb]
      unfold mid
      simp only [MarkFeedback.process, ra]
      simp [s, MarkFeedback.initial, MarkFeedback.footprint, MarkFeedback.recovery,
        PhaseAdmission.Calendar.model, C, forwardCalendar, b]
    rw [one, Nat.cast_one, mul_one, w.mark_gain, w.same_recovery]
    rfl

end NetworkStability.NativeReciprocal
