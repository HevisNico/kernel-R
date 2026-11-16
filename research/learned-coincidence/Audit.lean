import Recognition
import MonotoneCharacterization
import MonotonePremiseCompleteness
import MonotonePremiseExamples
import LayeredMonotoneExample

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`Target, `Recognition, `TwoLayerTarget, `MonotoneTarget, `MonotoneSupport,
    `MonotoneRecognition, `MonotoneCharacterization,
    `MonotoneOneSidedTarget, `MonotoneOneSidedRecognition,
    `MonotonePremiseTargets, `MonotonePremiseCompletenessTargets, `MonotonePremiseSoundness,
    `MonotonePremiseCompleteness, `MonotonePremiseExamples,
    `LayeredMonotoneTarget, `LayeredMonotoneRecognition, `LayeredMonotoneCharacterization,
    `LayeredMonotoneExample]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected learned-coincidence axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
  let required := #[
    (``LearnedCoincidence.learned_coincidence_recognition, ``LearnedCoincidence.LearnedCoincidenceRecognition),
    (``LearnedCoincidence.MonotoneDNF.monotone_characterization, ``LearnedCoincidence.MonotoneDNF.MonotoneCharacterization),
    (``LearnedCoincidence.MonotoneDNF.two_layer_monotone_recognition, ``LearnedCoincidence.MonotoneDNF.TwoLayerMonotoneRecognition),
    (``LearnedCoincidence.MonotoneDNF.two_layer_monotone_recognition_one_sided,
      ``LearnedCoincidence.MonotoneDNF.TwoLayerMonotoneRecognitionOneSided),
    (``LearnedCoincidence.MonotoneDNF.cascade_valid_checker_sound,
      ``LearnedCoincidence.MonotoneDNF.CascadeValidCheckerSound),
    (``LearnedCoincidence.MonotoneDNF.training_separation_checker_sound,
      ``LearnedCoincidence.MonotoneDNF.TrainingSeparationCheckerSound),
    (``LearnedCoincidence.MonotoneDNF.cascade_calibration_one_sided_checker_sound,
      ``LearnedCoincidence.MonotoneDNF.CascadeCalibrationOneSidedCheckerSound),
    (``LearnedCoincidence.MonotoneDNF.cascade_valid_checker_complete,
      ``LearnedCoincidence.MonotoneDNF.CascadeValidCheckerComplete),
    (``LearnedCoincidence.MonotoneDNF.training_separation_checker_complete,
      ``LearnedCoincidence.MonotoneDNF.TrainingSeparationCheckerComplete),
    (``LearnedCoincidence.MonotoneDNF.cascade_calibration_one_sided_checker_complete,
      ``LearnedCoincidence.MonotoneDNF.CascadeCalibrationOneSidedCheckerComplete),
    (``LearnedCoincidence.Layered.layered_monotone_recognition_one_sided,
      ``LearnedCoincidence.Layered.LayeredMonotoneRecognitionOneSided),
    (``LearnedCoincidence.Layered.layered_monotone_characterization,
      ``LearnedCoincidence.Layered.LayeredMonotoneCharacterization)]
  for (theoremName, target) in required do
    let some info := env.find? theoremName | throwError "Missing theorem {theoremName}"
    unless info.isTheorem && info.type.isConstOf target do
      throwError "Expected theorem {theoremName} with type {target}"
  logInfo m!"Learned coincidence audit passed."
