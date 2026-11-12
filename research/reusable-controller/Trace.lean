import ReusableController
open ReusableController ReusableController.Examples

#eval (List.range 7).map fun n =>
  let s := run need n start
  (n, s.lesson.preparation, s.lesson.practice, s.halted,
   s.attempts, s.accepted, s.trialPulses, s.work 1)
