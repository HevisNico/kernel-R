import LayeredChain
import LayeredTrainingChainTarget

/-! The training lessons' arrival windows from the lesson clock. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)

/-- One addressed read: the routed lower pulses and the addressed cell's inequalities give
its arrival window. -/
theorem routed_window {s e f : Nat → Rat} {lower : Cascade M L N} {d : Node M N}
    {timing : SlotTiming} {replay : ReadTrace lower} {read : ReadObservation 2}
    (route : Routed d (pulseDates lower replay) read) (start : read.start = s (L + 1))
    (pulses : PulseWindows s e f lower replay)
    (dates : ∀ a src, d.source a = some src →
      s (L + 1) ≤ s L + e L + d.delay a ∧ s L + f L + d.delay a ≤ s (L + 1) + timing.skew) :
    InWindow timing read := by
  intro j t arrived
  rw [route j] at arrived
  rw [start]
  cases source : d.source j with
  | none => simp [source] at arrived
  | some src =>
    rw [source] at arrived
    cases pulse : pulseDates lower replay src with
    | none => simp [pulse] at arrived
    | some u =>
      simp only [Option.bind_some, pulse, Option.map_some, Option.some.injEq] at arrived
      subst arrived
      obtain ⟨lo, hi⟩ := top_pulse pulses src u pulse
      obtain ⟨early, late⟩ := dates j src source
      constructor <;> grind

/-- Forgetting the windows of a training calibration. -/
theorem training_reads_of_calibration {c : Cascade M L N} {train : TrainingTrace c}
    (calibrated : TrainingCalibration c train) : TrainingReads c train := by
  induction c with
  | input => trivial
  | layer lower timing nodes ih =>
    refine ⟨ih calibrated.1, fun i g active r bound => ?_⟩
    obtain ⟨replay, route, slot⟩ := calibrated.2 i g active r bound
    obtain ⟨stimulus, reads, _⟩ := (read_calibration_iff lower train.1 _ _).mp replay
    exact ⟨stimulus, reads, route, (additive_slot_iff.mp slot).1⟩

theorem training_calibration_chained : TrainingCalibrationChained := by
  intro M L N c train σ e f dates reads scheduled pulses
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    refine ⟨ih train.1 dates.1 reads.1 scheduled.1 pulses.1, fun i g active r bound => ?_⟩
    obtain ⟨stimulus, replayReads, route, slot⟩ := reads.2 i g active r bound
    obtain ⟨replayScheduled, start⟩ := scheduled.2 i g active r bound
    have replayPulses := pulses.2 i g active r bound
    obtain ⟨replayDates, cellDates⟩ := dates.2 i g active r bound
    have windows := chain_windows replayDates replayReads replayScheduled replayPulses
    refine ⟨(read_calibration_iff lower train.1 _ _).mpr ⟨stimulus, replayReads, windows⟩, route, ?_⟩
    exact additive_slot_iff.mpr ⟨slot, routed_window route start replayPulses cellDates⟩

/-- Both chains together. No arrival window is assumed, in training or at test. Training
is gated by the lesson clock, and the test read at `x` by the latency chain. -/
theorem layered_recognition_fully_chained {c : Cascade M L N} (valid : c.Valid)
    {train : TrainingTrace c} {σ : LessonClock} {e f : Nat → Rat}
    (lessonDates : TrainingChainDates σ e f c) (lessonReads : TrainingReads c train)
    (lessonScheduled : TrainingScheduled σ c train) (lessonPulses : TrainingPulses σ e f c train)
    {s lmin lmax : Nat → Rat} {w : Rat}
    (dates : ChainDates s (latencyLow lmin) (latencyHigh w lmax) c)
    {x : Pattern M} {test : ReadTrace c}
    (inputs : (fun j => (inputTrace c test j).isSome) = x) (reads : LayerReads c train test)
    (scheduled : Scheduled s c test) (external : ExternalWindow (s 0) w c test)
    (latency : Latencies lmin lmax c test) :
    c.Trained train ∧ ArrivalWindows c test ∧ observed c test = c.predict x := by
  have training := training_calibration_chained M L N c train σ e f lessonDates lessonReads
    lessonScheduled lessonPulses
  obtain ⟨windows, decisions, _⟩ := layered_recognition_from_latency M L N c valid train training
    s lmin lmax w dates x test inputs reads scheduled external latency
  exact ⟨layered_trained valid training, windows, decisions⟩

end LearnedCoincidence.Layered
