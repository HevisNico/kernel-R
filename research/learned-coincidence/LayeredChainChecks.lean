import LayeredChain
import LayeredTrainingChainTarget

/-! Boolean checkers, with soundness, for the trace premises of the chain: the schedule,
the latencies and the external window. A witness or a generated gate reduces them with
`decide +kernel`. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)

def checkScheduled (s : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Bool
  | .input, _ => true
  | .layer (L := L) lower _ _, r =>
    checkScheduled s lower r.1 && (List.finRange N).all fun i => decide ((r.2.1 i).start = s (L + 1))

def checkLatencies (lmin lmax : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Bool
  | .input, _ => true
  | .layer (L := L) lower _ _, r =>
    checkLatencies lmin lmax lower r.1 && (List.finRange N).all fun i =>
      (r.2.1 i).emissions.all fun t =>
        decide ((r.2.1 i).start + lmin (L + 1) ≤ t ∧ t ≤ (r.2.1 i).start + lmax (L + 1))

def checkExternalWindow (s0 w : Rat) (c : Cascade M L N) (r : ReadTrace c) : Bool :=
  (List.finRange M).all fun j =>
    match inputTrace c r j with
    | none => true
    | some t => decide (s0 ≤ t ∧ t ≤ s0 + w)

def checkPulseWindows (s e f : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Bool
  | .input, r => (List.finRange M).all fun j =>
    match r j with
    | none => true
    | some t => decide (s 0 + e 0 ≤ t ∧ t ≤ s 0 + f 0)
  | .layer (L := L) lower _ _, r =>
    checkPulseWindows s e f lower r.1 && (List.finRange N).all fun i =>
      match (r.2.1 i).emissions.head? with
      | none => true
      | some t => decide (s (L + 1) + e (L + 1) ≤ t ∧ t ≤ s (L + 1) + f (L + 1))

/-- The lessons of one cell: active groups and rounds through `maxWrites`. -/
def lessonsOf (d : Node M N) (P : Fin 2 → Nat → Bool) : Bool :=
  (List.finRange 2).all fun g => !decide (g.val < d.cell.gate.groups) ||
    (List.range (d.cell.maxWrites + 1)).all fun r => P g r

def checkTrainingChainDates (σ : LessonClock) (e f : Nat → Rat) : (c : Cascade M L N) → Bool
  | .input => true
  | .layer (L := L) lower timing nodes =>
    checkTrainingChainDates σ e f lower && (List.finRange N).all fun i =>
      lessonsOf (nodes i) fun g r =>
        let s := σ (L + 1) i.val g.val r
        checkChainDates s e f lower && (List.finRange 2).all fun a =>
          match (nodes i).source a with
          | none => true
          | some _ =>
            decide (s (L + 1) ≤ s L + e L + (nodes i).delay a) &&
            decide (s L + f L + (nodes i).delay a ≤ s (L + 1) + timing.skew)

def checkTrainingScheduled (σ : LessonClock) : (c : Cascade M L N) → TrainingTrace c → Bool
  | .input, _ => true
  | .layer (L := L) lower _ nodes, train =>
    checkTrainingScheduled σ lower train.1 && (List.finRange N).all fun i =>
      lessonsOf (nodes i) fun g r =>
        checkScheduled (σ (L + 1) i.val g.val r) lower (train.2.1 i g r) &&
        decide ((train.2.2 i g r).start = σ (L + 1) i.val g.val r (L + 1))

def checkTrainingPulses (σ : LessonClock) (e f : Nat → Rat) : (c : Cascade M L N) → TrainingTrace c → Bool
  | .input, _ => true
  | .layer (L := L) lower _ nodes, train =>
    checkTrainingPulses σ e f lower train.1 && (List.finRange N).all fun i =>
      lessonsOf (nodes i) fun g r => checkPulseWindows (σ (L + 1) i.val g.val r) e f lower (train.2.1 i g r)

private theorem all_fin {n : Nat} {P : Fin n → Bool} :
    (List.finRange n).all P = true ↔ ∀ i, P i = true := by
  simp [List.all_eq_true]

theorem scheduled_checker_sound {s : Nat → Rat} {c : Cascade M L N} {r : ReadTrace c}
    (h : checkScheduled s c r = true) : Scheduled s c r := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    simp only [checkScheduled, Bool.and_eq_true] at h
    exact ⟨ih h.1, fun i => of_decide_eq_true (all_fin.mp h.2 i)⟩

theorem latencies_checker_sound {lmin lmax : Nat → Rat} {c : Cascade M L N} {r : ReadTrace c}
    (h : checkLatencies lmin lmax c r = true) : Latencies lmin lmax c r := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    simp only [checkLatencies, Bool.and_eq_true] at h
    exact ⟨ih h.1, fun i t mem => of_decide_eq_true (List.all_eq_true.mp (all_fin.mp h.2 i) t mem)⟩

theorem external_window_checker_sound {s0 w : Rat} {c : Cascade M L N} {r : ReadTrace c}
    (h : checkExternalWindow s0 w c r = true) : ExternalWindow s0 w c r := by
  intro j t arrived
  have port := all_fin.mp h j
  rw [arrived] at port
  exact of_decide_eq_true port

private theorem lessons_sound {d : Node M N} {P : Fin 2 → Nat → Bool} (h : lessonsOf d P = true) :
    ∀ g : Fin 2, g.val < d.cell.gate.groups → ∀ r, r ≤ d.cell.maxWrites → P g r = true := by
  intro g active r bound
  have group := all_fin.mp h g
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at group
  rcases group with off | rounds
  · exact absurd active off
  · exact List.all_eq_true.mp rounds r (List.mem_range.mpr (by omega))

theorem pulse_windows_checker_sound {s e f : Nat → Rat} {c : Cascade M L N} {r : ReadTrace c}
    (h : checkPulseWindows s e f c r = true) : PulseWindows s e f c r := by
  induction c with
  | input =>
    intro j t arrived
    have port := all_fin.mp h j
    simp only [arrived] at port
    exact of_decide_eq_true port
  | @layer L N B lower timing nodes ih =>
    simp only [checkPulseWindows, Bool.and_eq_true] at h
    refine ⟨ih h.1, fun i t first => ?_⟩
    have cell := all_fin.mp h.2 i
    simp only [first] at cell
    exact of_decide_eq_true cell

theorem training_chain_dates_checker_sound {σ : LessonClock} {e f : Nat → Rat} {c : Cascade M L N}
    (h : checkTrainingChainDates σ e f c = true) : TrainingChainDates σ e f c := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    simp only [checkTrainingChainDates, Bool.and_eq_true] at h
    refine ⟨ih h.1, fun i g active r bound => ?_⟩
    have lesson := lessons_sound (all_fin.mp h.2 i) g active r bound
    simp only [Bool.and_eq_true] at lesson
    refine ⟨chain_dates_checker_sound _ _ _ _ _ _ _ lesson.1, fun a src source => ?_⟩
    have port := all_fin.mp lesson.2 a
    rw [source] at port
    simp only [Bool.and_eq_true, decide_eq_true_eq] at port
    exact port

theorem training_scheduled_checker_sound {σ : LessonClock} {c : Cascade M L N} {train : TrainingTrace c}
    (h : checkTrainingScheduled σ c train = true) : TrainingScheduled σ c train := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    simp only [checkTrainingScheduled, Bool.and_eq_true] at h
    refine ⟨ih h.1, fun i g active r bound => ?_⟩
    have lesson := lessons_sound (all_fin.mp h.2 i) g active r bound
    simp only [Bool.and_eq_true] at lesson
    exact ⟨scheduled_checker_sound lesson.1, of_decide_eq_true lesson.2⟩

theorem training_pulses_checker_sound {σ : LessonClock} {e f : Nat → Rat} {c : Cascade M L N}
    {train : TrainingTrace c} (h : checkTrainingPulses σ e f c train = true) :
    TrainingPulses σ e f c train := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    simp only [checkTrainingPulses, Bool.and_eq_true] at h
    exact ⟨ih h.1, fun i g active r bound =>
      pulse_windows_checker_sound (lessons_sound (all_fin.mp h.2 i) g active r bound)⟩

end LearnedCoincidence.Layered
