import PhysicalEvaluator
open ReusableController.PhysicalEvaluator ReusableController.PhysicalEvaluator.RecordedData

#eval (firstFire t6004p1Readings, firstFire t6004p2Readings,
  firstFire t6007p1Readings, firstFire t6007p2Readings)
#eval (Replay.cost false, Replay.cost true, Replay.completed.memory.incumbent,
  Replay.completed.memory.spent, Replay.completed.memory.live.trialPulses,
  Replay.completed.memory.live.attempts, Replay.recordedTrainPulses)
#eval (21 + 741 + 36 * 359, 36 * 380, 21 + 741 + 37 * 359, 37 * 380)
