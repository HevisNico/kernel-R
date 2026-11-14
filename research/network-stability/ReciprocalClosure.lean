import NativeAdmissions
import DatedReplay

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid
open AutonomousFeedback.Schedule (Config)
open PhaseAdmission (Calendar Occurrence Trace)

abbrev ReciprocalInput := Fin 2 × Port
abbrev ReciprocalProbe := Occurrence ℝ ReciprocalInput

/-- A's first four external probes have the same physical input. -/
def birthTrainingProbe (date : ℝ) : ReciprocalProbe := ⟨date, 0, 0⟩

/-- The first four A sources, including the first strong one, are already
queued at birth. This computes the actual source date from the source train. -/
theorem first_strong_birth_token_queued :
    (⟨0, 0, 24⟩ : Delivery 1) ∈ nominalStart.pending := by
  change (⟨0, 0, 24⟩ : Delivery 1) ∈ sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16
  apply List.mem_append_left
  apply List.mem_ofFn.mpr
  refine ⟨⟨3, by decide⟩, ?_⟩
  norm_num

/-- The actual native first strong source is READY, fires once, preserves
all memory on its firing segment, and leaves the subsequent queue intact. -/
theorem birth_first_strong_native_certificate :
    ∃ witness : BirthFirstFire KernelR.FutureControls.parameters (fun _ _ => []) nominalStart,
      witness.weak.final.time = 24 ∧ witness.weak.final.main 0 = .ready ∧
      witness.weak.final.raw 0 0 = some 24 ∧
      witness.weak.execution.ledger.emissions = [] ∧ witness.weak.final.x 0 (.z 0) =
        nominalStart.x 0 (.z 0) + 9 / 5 ∧
      witness.fire.execution.ledger.emissions = [(0, witness.final.time)] ∧
      witness.final.pending = witness.weak.final.pending ∧
      (∀ port, witness.final.x 0 (.z port) = witness.weak.final.x 0 (.z port)) ∧
      witness.final.x 0 .b = witness.weak.final.x 0 .b := by
  obtain ⟨witness⟩ := birth_protocol_first_fire_exists
    (born := nominalStart) (route := fun _ _ => []) Newborn.nominal_birth_state nominal_box.extend_old
    (fun _ => rfl) (show nominalStart.pending = _ from rfl)
  exact ⟨witness, witness.weak.date, (witness.weak.ready 0).ready,
    by rw [witness.weak.raw_active, witness.weak.date],
    witness.weak.emissions, witness.weak.gain_target, witness.fire.emissions,
    witness.fire.pending.trans (List.append_nil _), witness.fire.gain_preserved 0,
    witness.fire.recovery_preserved 0⟩

private theorem keep_first_strong {C : Calendar 2 ℝ ReciprocalInput} {d : Nat}
    {root s : Config 6 ReciprocalProbe} (diamond : MarkFeedback.Admissible C.model d root)
    (reach : MarkFeedback.Path C.model d root s)
    {p : ReciprocalProbe} {rest : List ReciprocalProbe} {lo hi error : Int}
    (selected : s.pending.Perm (p :: rest))
    (within : lo ≤ error ∧ error ≤ hi)
    (margin : RoutedCalendar.HasRoom (MarkFeedback.score C.model d s p) lo hi)
    (different : birthTrainingProbe 24 ≠ p)
    (pending : birthTrainingProbe 24 ∈ s.pending) :
    let next := MarkFeedback.process C.model d s p rest error
    MarkFeedback.Path C.model d root next ∧ birthTrainingProbe 24 ∈ next.pending ∧
      MarkFeedback.read C.model d next (birthTrainingProbe 24) 0 =
        MarkFeedback.read C.model d s (birthTrainingProbe 24) 0 := by
  classical
  let strong := birthTrainingProbe 24
  have clean : MarkFeedback.read C.model d s p error = MarkFeedback.read C.model d s p 0 :=
    MarkFeedback.read_eq_of_room _ _ _ _ within margin
  have same : MarkFeedback.process C.model d s p rest error =
      MarkFeedback.process C.model d s p rest 0 := by simp only [MarkFeedback.process, clean]
  dsimp only
  rw [same]
  have inside : strong ∈ rest :=
    (List.mem_cons.mp (selected.mem_iff.mp pending)).resolve_left different
  have arranged : s.pending.Perm (strong :: p :: rest.erase strong) :=
    (selected.trans ((List.perm_cons_erase inside).cons p)).trans (List.Perm.swap _ _ _)
  exact ⟨MarkFeedback.path_trans reach (.cons (.select _ _ _ selected) (.nil _)),
    List.mem_append_left _ inside, MarkFeedback.read_stable C.model d s (diamond s reach) arranged different⟩

private theorem zero_room (score : Int) : RoutedCalendar.HasRoom score 0 0 := by
  unfold RoutedCalendar.HasRoom
  omega

/-- A whole reachable MARK diamond is incompatible with the earliest
native training prefix when every queued physical source is already in
the guarded queue. The first strong source is READY, like the first weak
source. The global diamond forces its read to stay silent through the
three training writes, even though the native source at 24 fires. -/
theorem birth_training_prefix_no_global_diamond
    (C : Calendar 2 ℝ ReciprocalInput) (d : Nat) (seed : List ReciprocalProbe)
    (queued : birthTrainingProbe 24 ∈ seed)
    (firstReady : C.phase (0, 0) 0 = .ready) (strongReady : C.phase (0, 0) 24 = .ready)
    (diamond : MarkFeedback.Admissible C.model d (MarkFeedback.initial 2 seed))
    {last : Config 6 ReciprocalProbe}
    {word : List (ReciprocalProbe × Bool)} (remaining : List (ReciprocalProbe × Bool))
    (trace : Trace C d (· ≤ ·) (MarkFeedback.initial 2 seed) word last) :
    word ≠
      [(birthTrainingProbe 0, false), (birthTrainingProbe 8, false), (birthTrainingProbe 16, false),
        (birthTrainingProbe 24, true)] ++ remaining := by
  let root := MarkFeedback.initial 2 seed
  let strong := birthTrainingProbe 24
  have firstLaw : SameReadLaw C.model (birthTrainingProbe 0) strong := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact congrArg (C.bias (0, 0)) (firstReady.trans strongReady.symm)
    · exact congrArg (C.recoveryWeight (0, 0)) (firstReady.trans strongReady.symm)
  have different (t : ℝ) (ne : 24 ≠ t) : strong ≠ birthTrainingProbe t :=
    fun h => ne (congrArg Occurrence.due h)
  have nominal := trace.zero_error_replay
  clear trace
  intro recorded
  cases nominal with
  | nil => simp at recorded
  | @cons s u p0 rest0 selected0 earliest0 w0 tail0 =>
    have split0 := List.cons.inj recorded
    obtain ⟨pair0, word0⟩ := split0
    obtain ⟨input0, decision0⟩ := Prod.mk.inj pair0
    subst p0
    have strongSilent : MarkFeedback.read C.model d root strong 0 = false :=
      (same_read_law_same_decision C.model d root root _ _ firstLaw rfl rfl).symm.trans decision0
    obtain ⟨reach0, pending0, same0⟩ :=
      keep_first_strong diamond (.nil _) selected0 ⟨le_rfl, le_rfl⟩ (zero_room _)
        (different 0 (by norm_num)) queued
    clear recorded
    cases tail0 with
    | nil => simp at word0
    | @cons s u p8 rest8 selected8 earliest8 w8 tail8 =>
      obtain ⟨pair8, word8⟩ := List.cons.inj word0
      obtain ⟨input8, _⟩ := Prod.mk.inj pair8
      subst p8
      obtain ⟨reach8, pending8, same8⟩ :=
        keep_first_strong diamond reach0 selected8 ⟨le_rfl, le_rfl⟩ (zero_room _)
          (different 8 (by norm_num)) pending0
      clear word0
      cases tail8 with
      | nil => simp at word8
      | @cons s u p16 rest16 selected16 earliest16 w16 tail16 =>
        obtain ⟨pair16, word16⟩ := List.cons.inj word8
        obtain ⟨input16, _⟩ := Prod.mk.inj pair16
        subst p16
        obtain ⟨_, _, same16⟩ :=
          keep_first_strong diamond reach8 selected16 ⟨le_rfl, le_rfl⟩ (zero_room _)
            (different 16 (by norm_num)) pending8
        clear word8
        cases tail16 with
        | nil => simp at word16
        | @cons s u p24 rest24 selected24 earliest24 w24 tail24 =>
          obtain ⟨pair24, _⟩ := List.cons.inj word16
          obtain ⟨input24, decision24⟩ := Prod.mk.inj pair24
          subst p24
          exact Bool.noConfusion (decision24.symm.trans
            (same16.trans (same8.trans (same0.trans strongSilent))))

end NetworkStability.NativeReciprocal
