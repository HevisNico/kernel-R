import ReusableController
open ReusableController ReusableController.Adaptive ReusableController.Adaptive.Examples

#eval [false, true].map fun p =>
  let s := result p
  (p, s.lesson.preparation, s.lesson.practice, s.attempts, s.trialPulses,
    s.preparationBlocked, s.practiceBlocked, trueCost p, report p, charge p)

#eval (completed.memory.incumbent, completed.memory.trials, completed.memory.adoptions,
  completed.memory.spent, completed.memory.live.work 1,
  completed.memory.spent + completed.memory.live.work 1)

#eval (selected.spent + 6 * trueCost selected.incumbent, 6 * trueCost menu.seed,
  selected.spent + 7 * trueCost selected.incumbent, 7 * trueCost menu.seed)
