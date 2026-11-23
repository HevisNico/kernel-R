import InverterScheduleWitness
import Lean.Util.CollectAxioms

/-! Audit of training on a fixed inverter schedule: no project axiom, only `propext`,
`Classical.choice` and `Quot.sound`, and the frozen target has its exact type.

What the existential form of `InverterTrainingCalibration` constrains: the dates of
the training reads (`front_end_complement_late`: a complement pulse strictly after
the read start; `directly_driven_not_front_end`: a read with a complement pulse at
its start is produced by no front end). What it does not: its witnesses may be
chosen after the fact. `ScheduledInverterTraining` takes the schedule as a given
parameter; as logic, `∀ s, P s → C` is equivalent to `(∃ s, P s) → C`, so the
change is one of interface (a schedule fixed before the run and checked), not of
logical strength. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`InverterSchedule, `InverterScheduleWitness]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected inverter-schedule axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  let some info := env.find? ``LearnedCoincidence.MonotoneDNF.every_function_trained_on_schedule
    | throwError "every_function_trained_on_schedule is missing"
  unless info.type == mkConst ``LearnedCoincidence.MonotoneDNF.EveryFunctionTrainedOnSchedule do
    throwError "every_function_trained_on_schedule does not have the type EveryFunctionTrainedOnSchedule"
  logInfo m!"Inverter schedule audit passed: {checked} declarations."

#print axioms LearnedCoincidence.MonotoneDNF.front_end_complement_late
#print axioms LearnedCoincidence.MonotoneDNF.directly_driven_not_front_end
#print axioms LearnedCoincidence.MonotoneDNF.scheduled_training_calibration
#print axioms LearnedCoincidence.MonotoneDNF.scheduled_inverters_compute
#print axioms LearnedCoincidence.MonotoneDNF.every_function_trained_on_schedule
#print axioms LearnedCoincidence.MonotoneDNF.InverterScheduleWitness.premises_hold
#print axioms LearnedCoincidence.MonotoneDNF.InverterScheduleWitness.answers_not
