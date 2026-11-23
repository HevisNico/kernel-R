import LayeredInverterTarget
import LayeredChain
import LayeredMonotoneCharacterization
import Inverters
import TwoRails

/-! Inverters in front of the layered cascade. The front end lemmas of `Inverters.lean`
give the external mask (the rails of `y`) and the external window. The per-pattern layered
theorem, or its latency chain, gives the rest. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF (InverterTiming InverterRead FrontEnd frontArrival rails front_end_input
  front_end_window)

/-- The front end seen as one read on the `2 M` lines. -/
private def frontRead (t : InverterTiming) (start : Rat) (external : Fin M → Option Rat)
    (inv : Fin M → ReadObservation 1) : ReadObservation (M + M) :=
  ⟨start + t.emitEarly, frontArrival t.emitEarly external inv, [], 0⟩

private theorem front_read {t : InverterTiming} {start : Rat} {external : Fin M → Option Rat}
    {inv : Fin M → ReadObservation 1}
    (cells : ∀ j, (inv j).start = start ∧ (inv j).arrival 0 = external j ∧ InverterRead t (inv j)) :
    FrontEnd t start external inv (frontRead t start external inv) :=
  ⟨cells, rfl, rfl⟩

/-- The front end puts the rails of `y` on the external lines. -/
theorem layered_front_mask {t : InverterTiming} {start : Rat} {external : Fin M → Option Rat}
    {inv : Fin M → ReadObservation 1} {c : Cascade (M + M) L N} {test : ReadTrace c}
    {y : Pattern M} (realised : ∀ j, (external j).isSome = y j)
    (front : LayeredFront t start external inv c test) :
    (fun j => (inputTrace c test j).isSome) = rails y := by
  have mask := front_end_input (front_read front.1)
  rw [show rails y = rails (fun j => (external j).isSome) from congrArg rails (funext realised).symm]
  rw [← mask, front.2]
  rfl

/-- The front end is the external window `[start + emitEarly, start + emitEarly + w]`. -/
theorem layered_front_window {t : InverterTiming} {start : Rat} {external : Fin M → Option Rat}
    {inv : Fin M → ReadObservation 1} {c : Cascade (M + M) L N} {test : ReadTrace c} {w : Rat}
    (front : LayeredFront t start external inv c test)
    (windowFits : t.window ≤ w) (spreadFits : t.emitLate - t.emitEarly ≤ w) :
    ExternalWindow (start + t.emitEarly) w c test := by
  intro j v arrived
  rw [front.2] at arrived
  exact front_end_window (front_read front.1) windowFits spreadFits j v arrived

theorem layered_inverters_compute : LayeredInvertersCompute := by
  intro M L N c valid train training t start external inv y test realised front reads windows
  exact (layered_recognition_at (M + M) L N c valid train training (rails y) test
    ((read_calibration_iff c train _ test).mpr
      ⟨layered_front_mask realised front, reads, windows⟩)).2

theorem layered_inverters_chained : LayeredInvertersChained := by
  intro M L N c valid train training t start external inv y test s lmin lmax w first windowFits
    spreadFits dates realised front reads scheduled latency
  have external := layered_front_window front windowFits spreadFits
  rw [← first] at external
  obtain ⟨arrivals, decisions, _⟩ := layered_recognition_from_latency (M + M) L N c valid train
    training s lmin lmax w dates (rails y) test (layered_front_mask realised front) reads scheduled
    external latency
  exact ⟨arrivals, decisions⟩

/-- Every Boolean function: a two-rail cascade gives a monotone function of the lines
(`every_function_on_two_rails`, `monotone_characterization`). A layered cascade realises
it (`layered_monotone_characterization`). -/
theorem every_function_layered_with_inverters : EveryFunctionLayeredWithInverters := by
  intro M f
  obtain ⟨A, B, p, k, pValid, onRails⟩ := MonotoneDNF.every_function_on_two_rails M f
  have monotone : MonotoneDNF.MonotoneFunction (MonotoneDNF.output p k) :=
    (MonotoneDNF.monotone_characterization (M + M) _).mpr ⟨A, B, p, k, pValid, fun _ => rfl⟩
  obtain ⟨L, N, c, i, valid, same⟩ := (layered_monotone_characterization (M + M) _).mp monotone
  refine ⟨L, N, c, i, valid, ?_⟩
  intro train training t start external inv y test realised front reads windows
  rw [layered_inverters_compute M L N c valid train training t start external inv y test realised
    front reads windows, same, onRails]

end LearnedCoincidence.Layered
